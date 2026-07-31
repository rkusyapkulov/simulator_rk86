#define _CRT_SECURE_NO_WARNINGS
#define UNICODE
#define _UNICODE
#include <windows.h>
#include <mmsystem.h>
#include <fstream>
#include <string>
#include <vector>
#include <cstdlib>
#include <cwchar>
#include <cmath>
#include <commdlg.h> // Обязательно проверьте наличие этого инклуда вверху файла

#pragma comment(lib, "winmm.lib")

// Размеры экрана Радио-86РК
const int SCREEN_COLS = 64;
const int SCREEN_ROWS = 25;
const int CHAR_HEIGHT = 8;
const int CHAR_WIDTH = 6;

#define IDM_FILE_OPEN  0x0010  // Изменено: строго меньше 0xF000 для системного меню!
#define IDM_FILE_EXIT  0x0020

#define BIOS_START_ADDRESS 0xF800  // 0xE000 for "peace.dos"
#define BIOS_SIZE 2048 // 8192 for "peace.dos"
#define BIOS_NAME L"bios.bin" // "peace.dos" for peace.dos

// --- ГЛОБАЛЬНЫЕ БУФЕРЫ ПАМЯТИ ---
BYTE system_ram[65536];    // Полное адресное пространство 64 Кб
BYTE font_rom[2048];       // ПЗУ Знакогенератора (2 Кб)
BYTE rom_disk_storage[32768]; // Буфер для хранения файла "rom.bin"
BYTE key_matrix_state[8];  // Состояние шин клавиатуры (Индекс = Столбец PA, Биты = Строки PB)
bool emulator_running = true;

// Состояния модификаторов (true = нажато/заземлено, false = разомкнуто)
bool rk_cc_pressed = false;       // CC (Shift) -> Подключена к PC5
bool rk_us_pressed = false;       // УС (Ctrl)  -> Подключена к PC6
bool rk_rus_lat_pressed = false;  // РУС/ЛАТ    -> Подключена к PC7

// --- ЭМУЛЯЦИЯ БИПЕРА INTE ---
bool rk_inte_speaker_state = false; // Текущее состояние динамика от INTE

HWND hRegListBox = NULL;   // Дескриптор окна вывода регистров

// --- ПАРАМЕТРЫ ЗВУКОВОГО ПОТОКА КР580ВИ53 ---
const int AUDIO_SAMPLE_RATE = 22050;
HWAVEOUT hWaveOut = NULL;
WAVEHDR waveHeader[2];
short* audioBuffers[2] = { NULL, NULL };
const int AUDIO_BUF_SIZE = 1024;

// --- ДОБАВИТЬ: Кольцевой буфер синхронизации INTE ---
const int INTE_RING_BUF_SIZE = 16384;
short inte_ring_buffer[INTE_RING_BUF_SIZE] = { 0 };
volatile int inte_ring_write_ptr = 0;
volatile int inte_ring_read_ptr = 0;

#pragma pack(push, 1)
struct CPU8080 {
	BYTE A, B, C, D, E, H, L;
	WORD PC, SP;
	bool S, Z, AC, P, CY;
	bool EI;
	bool halted; // флаг останова процессора
	int cycles_until_interrupt = 35600; // 1780000 Гц / 50 Гц = 35600 тактов на кадр
	bool int_pending = false;           // Флаг того, что прерывание пришло от дисплея

	// Порты КР580ВВ55 (ППА)
	BYTE ppi_pa, ppi_pb, ppi_pc, ppi_ctrl;
	BYTE ppi1_pa, ppi1_pb, ppi1_pc, ppi1_ctrl; // 0A000h (Пользователь №1)

	// Состояние КР580ВТ57 (ПДП) — исправленные каналы
	WORD dma_ch_addr[4];
	WORD dma_ch_count[4];
	BYTE dma_status;
	BYTE dma_command;
	bool dma_flip_flop;

	// Состояние КР580ВГ75 (Видеоконтроллер)
	BYTE vgh75_status;
	BYTE vgh75_command;
	BYTE vgh75_param_count;
	BYTE vgh75_config[4];
	bool vgh75_vblank_state;

	// Состояние КР580ВИ53 (Таймер/Звук)
	struct PITChannel {
		WORD count;
		WORD latch;
		BYTE mode;
		BYTE bcd;
		BYTE access_phase;
		bool latched;
		double phase;
	} pit_channels[3];
	BYTE pit_control;

	void Reset() {
		PC = BIOS_START_ADDRESS; // Старт строго с начального адреса ПЗУ BIOS
		SP = 0x0000;
		A = B = C = D = E = H = L = 0;
		S = Z = AC = P = CY = false;
		EI = false;
		halted = false; // <-- ДОБАВИТЬ: сброс флага при перезагрузке
		ppi_pa = ppi_pb = ppi_pc = 0xFF; ppi_ctrl = 0x9B;
		ppi1_pa = ppi1_pb = ppi1_pc = 0xFF; ppi1_ctrl = 0x9B;

		// Настройка дефолтных значений ПДП
		for (int i = 0; i < 4; i++) { dma_ch_addr[i] = 0; dma_ch_count[i] = 0; }
		dma_ch_addr[2] = 0x76D0; // Канал 2 по умолчанию отвечает за экран РК
		dma_command = 0; dma_status = 0; dma_flip_flop = false;

		// Настройка видеоконтроллера
		vgh75_status = 0x00; vgh75_command = 0x00; vgh75_param_count = 0; vgh75_vblank_state = false;
		for (int i = 0; i < 4; i++) vgh75_config[i] = 0;

		rk_inte_speaker_state = false;
		// Настройка таймера ВИ53
		pit_control = 0x00;
		for (int i = 0; i < 3; i++) {
			pit_channels[i].count = 0; pit_channels[i].latch = 0; pit_channels[i].mode = 0;
			pit_channels[i].bcd = 0; pit_channels[i].access_phase = 0; pit_channels[i].latched = false;
			pit_channels[i].phase = 0.0;
		}
	}

	void SetFlagsZSP(BYTE res) {
		Z = (res == 0);
		S = ((res & 0x80) != 0);
		BYTE Ty = res;
		Ty ^= Ty >> 4; Ty ^= Ty >> 2; Ty ^= Ty >> 1;
		P = !(Ty & 1);
	}

	void SetFlagsINR(BYTE old_val, BYTE new_val) {
		AC = ((old_val & 0x0F) + 1 > 0x0F);
		SetFlagsZSP(new_val);
	}

	void SetFlagsDCR(BYTE old_val, BYTE new_val) {
		AC = ((old_val & 0x0F) == 0);
		SetFlagsZSP(new_val);
	}

	void SetFlagsAdd(BYTE r1, BYTE r2, int res) {
		CY = (res > 0xFF);
		AC = (((r1 & 0xF) + (r2 & 0xF)) > 0xF);
		SetFlagsZSP((BYTE)res);
	}

	void SetFlagsSub(BYTE r1, BYTE r2, int res) {
		CY = (res < 0);
		AC = (((r1 & 0xF) - (r2 & 0xF)) < 0);
		SetFlagsZSP((BYTE)res);
	}

	WORD GetHL() const { return (H << 8) | L; }
	void SetHL(WORD val) { H = val >> 8; L = val & 0xFF; }
	WORD GetBC() const { return (B << 8) | C; }
	void SetBC(WORD val) { B = val >> 8; C = val & 0xFF; }
	WORD GetDE() const { return (D << 8) | E; }
	void SetDE(WORD val) { D = val >> 8; E = val & 0xFF; }

	BYTE GetReg(int r) {
		switch (r) {
		case 0: return B; case 1: return C; case 2: return D; case 3: return E;
		case 4: return H; case 5: return L; case 6: return Read(GetHL()); default: return A;
		}
	}

	void SetReg(int r, BYTE val) {
		switch (r) {
		case 0: B = val; break; case 1: C = val; break; case 2: D = val; break; case 3: E = val; break;
		case 4: H = val; break; case 5: L = val; break; case 6: Write(GetHL(), val); break; default: A = val; break;
		}
	}

	BYTE Read(WORD addr) {
		if (addr >= BIOS_START_ADDRESS) return system_ram[addr]; // Чтение BIOS ПЗУ

		// Опрос КР580ВВ55 (ППА клавиатуры) (8000h - 9FFFh)
		if (addr >= 0x8000 && addr <= 0x8003) {
			WORD reg = addr & 3;
			if (reg == 0) return ppi_pa;
			if (reg == 1) {
				BYTE result_pb = 0xFF;
				for (int col = 0; col < 8; col++) {
					if ((ppi_pa & (1 << col)) == 0) {
						result_pb &= key_matrix_state[col];
					}
				}
				return result_pb;
			}
			if (reg == 2) { // Порт С (Линии модификаторов)
				BYTE result_pc = ppi_pc;
				result_pc |= 0xE0; // Высокий уровень подтяжки по умолчанию
				if (rk_cc_pressed)      result_pc &= ~(1 << 5); // CC -> PC5
				if (rk_us_pressed)      result_pc &= ~(1 << 6); // УС -> PC6
				if (rk_rus_lat_pressed) result_pc &= ~(1 << 7); // РУС/ЛАТ -> PC7
				return result_pc;
			}
			return ppi_ctrl;
		}

		// К580ВВ55 №2: Интерфейс ROM-диска программы (0xF500 - 0xF503)
		if (addr >= 0xA000 && addr <= 0xA003) {
			WORD reg = addr & 3;
			if (reg == 0) {
				WORD rom_address = (ppi1_pc << 8) | ppi1_pb;
				return rom_disk_storage[rom_address];
			}
			if (reg == 1) return ppi1_pb;
			if (reg == 2) return ppi1_pc;
			return ppi1_ctrl;
		}

		// Опрос внешнего музыкального таймера КР580ВИ53 (9000h - 9003h)
		if (addr >= 0x9000 && addr <= 0x9003) {
			WORD reg = addr & 3;
			if (reg < 3) {
				PITChannel& ch = pit_channels[reg];
				BYTE val = 0;
				WORD src = ch.latched ? ch.latch : ch.count;
				if (ch.access_phase == 0) {
					val = src & 0xFF;
					ch.access_phase = 1;
				}
				else {
					val = (src >> 8) & 0xFF;
					ch.access_phase = 0;
					ch.latched = false;
				}
				return val;
			}
			return 0xFF;
		}

		// Опрос КР580ВГ75 (C000h - DFFFh) с симуляцией VRTC/VBlank
		if (addr >= 0xC000 && addr <= 0xDFFF) {
			if ((addr & 1) == 1) {
				BYTE current_status = vgh75_status;
				vgh75_status &= ~0x20; // Сброс флага конца кадра при чтении
				return current_status;
			}
			return 0x00;
		}

		// Опрос КР580ВТ57 (ПДП) (E000h - F7FFh)
		if (addr >= 0xE000 && addr <= 0xF7FF) {
			WORD reg = addr & 0x000F;
			if (reg <= 7) {
				int channel = reg >> 1;
				bool is_count = (reg & 1) != 0;
				WORD val = is_count ? dma_ch_count[channel] : dma_ch_addr[channel];
				BYTE res_byte = 0;
				if (!dma_flip_flop) {
					res_byte = val & 0xFF;
					dma_flip_flop = true;
				}
				else {
					res_byte = (val >> 8) & 0xFF;
					dma_flip_flop = false;
				}
				return res_byte;
			}
			if (reg == 8) {
				BYTE status = dma_status;
				dma_status &= 0xF0;
				return status;
			}
			return 0x00;
		}

		// Если не попали ни в одно устройство, читаем RAM строго до 0x7FFF
		if (addr <= 0x7FFF) return system_ram[addr];
		return 0xFF; // Высокоимпедансная пустая шина
	}

	void Write(WORD addr, BYTE val) {
		if (addr <= 0x7FFF) {
			system_ram[addr] = val;
		}

		if (addr >= 0x8000 && addr <= 0x9FFF) {
			WORD reg = addr & 3;
			if (reg == 0) ppi_pa = val;
			else if (reg == 1) ppi_pb = val;
			else if (reg == 2) ppi_pc = val;
			else {
				ppi_ctrl = val;
				if ((val & 0x80) == 0) {
					int bit_to_change = (val >> 1) & 7;
					if (val & 1) ppi_pc |= (1 << bit_to_change);
					else ppi_pc &= ~(1 << bit_to_change);
				}
			}
		}

		// Микросхема PPI 1 (Вторая плата)
		if (addr >= 0xA000 && addr <= 0xA003) {
			WORD reg = addr & 3;
			if (reg == 0) ppi1_pa = val;
			else if (reg == 1) ppi1_pb = val;
			else if (reg == 2) ppi1_pc = val;
			else ppi1_ctrl = val;
			return;
		}

		// --- Write to КР580ВИ53 (Timer) at 9000h - 9003h ---
		if (addr >= 0x9000 && addr <= 0x9003) {
			WORD reg = addr & 3;
			if (reg < 3) { // Write to counters 0, 1, 2
				PITChannel& ch = pit_channels[reg];
				if (ch.access_phase == 0) {
					ch.count = (ch.count & 0xFF00) | val;
					ch.access_phase = 1;
				}
				else {
					ch.count = (ch.count & 0x00FF) | (val << 8);
					ch.access_phase = 0;
				}
			}
			else { // Write to Control Word Register
				pit_control = val;
				int sel_ch = (val >> 6) & 3;
				if (sel_ch < 3) {
					PITChannel& ch = pit_channels[sel_ch];
					ch.mode = (val >> 1) & 7;
					ch.bcd = val & 1;

					int rw_mode = (val >> 4) & 3;
					if (rw_mode == 0) { // Counter Latch command
						ch.latch = ch.count;
						ch.latched = true;
					}
					else {
						ch.access_phase = 0; // Reset phase for new data bytes
					}
				}
			}
		}

		// --- Write to КР580ВГ75 (CRT Controller) at C000h - DFFFh ---
		if (addr >= 0xC000 && addr <= 0xDFFF) {
			WORD reg = addr & 1;
			if (reg == 1) { // Command Port
				vgh75_command = val;
				vgh75_param_count = 0; // Reset parameter index phase
				if ((val & 0xFC) == 0x00) {
					vgh75_status &= ~0x20; // Clear internal error/vblank flags
				}
			}
			else if (reg == 0) { // Parameter Data Port
				if (vgh75_param_count < 4) {
					vgh75_config[vgh75_param_count++] = val;
					if (vgh75_param_count == 4) {
						vgh75_status |= 0x00; // Setup completed successfully
					}
				}
			}
		}

		// --- Write to КР580ВТ57 (DMA Controller) at E000h - F7FFh ---
		if (addr >= 0xE000) {
			WORD reg = addr & 0x000F;

			if (reg <= 7) { // Write channel address or word count registers
				int channel = reg >> 1;
				bool is_count = (reg & 1) != 0;

				if (!dma_flip_flop) {
					if (is_count) dma_ch_count[channel] = (dma_ch_count[channel] & 0xFF00) | val;
					else          dma_ch_addr[channel] = (dma_ch_addr[channel] & 0xFF00) | val;
					dma_flip_flop = true;
				}
				else {
					if (is_count) dma_ch_count[channel] = (dma_ch_count[channel] & 0x00FF) | ((val & 0x3F) << 8);
					else          dma_ch_addr[channel] = (dma_ch_addr[channel] & 0x00FF) | (val << 8);
					dma_flip_flop = false;
				}
			}
			else if (reg == 8) { // Write DMA command register
				dma_command = val;
				dma_flip_flop = false; // Any command register write resets the flip-flop byte tracker
			}
		}
	}

	int Step() {
		// Таблица базовых тактов для всех 256 инструкций Intel 8080
		static const int lut_cycles[256] = {
			4, 10, 7,  5,  5,  5,  7,  4,  4, 10, 7,  5,  5,  5,  7,  4,  // 00-0F
			4, 10, 7,  5,  5,  5,  7,  4,  4, 10, 7,  5,  5,  5,  7,  4,  // 10-1F
			4, 10, 16, 5,  5,  5,  7,  4,  4, 10, 16, 5,  5,  5,  7,  4,  // 20-2F
			4, 10, 13, 5,  10, 10, 10, 4,  4, 10, 13, 5,  5,  5,  7,  4,  // 30-3F
			5, 5,  5,  5,  5,  5,  7,  5,  5, 5,  5,  5,  5,  5,  7,  5,  // 40-4F
			5, 5,  5,  5,  5,  5,  7,  5,  5, 5,  5,  5,  5,  5,  7,  5,  // 50-5F
			5, 5,  5,  5,  5,  5,  7,  5,  5, 5,  5,  5,  5,  5,  7,  5,  // 60-6F
			7, 7,  7,  7,  7,  7,  7,  7,  5, 5,  5,  5,  5,  5,  7,  5,  // 70-7F
			4, 4,  4,  4,  4,  4,  7,  4,  4, 4,  4,  4,  4,  4,  7,  4,  // 80-8F
			4, 4,  4,  4,  4,  4,  7,  4,  4, 4,  4,  4,  4,  4,  7,  4,  // 90-9F
			4, 4,  4,  4,  4,  4,  7,  4,  4, 4,  4,  4,  4,  4,  7,  4,  // A0-AF
			4, 4,  4,  4,  4,  4,  7,  4,  4, 4,  4,  4,  4,  4,  7,  4,  // B0-BF
			5, 10, 10, 10, 11, 11, 7,  11, 5, 10, 10, 10, 11, 17, 7,  11, // C0-CF
			5, 10, 10, 10, 11, 11, 7,  11, 5, 10, 10, 10, 11, 17, 7,  11, // D0-DF
			5, 10, 10, 10, 11, 11, 7,  11, 5, 10, 10, 10, 11, 17, 7,  11, // E0-EF
			5, 10, 10, 10, 11, 11, 7,  11, 5, 10, 10, 10, 11, 17, 7,  11  // F0-FF
		};

		// 1. Проверяем аппаратное прерывание перед декодированием инструкции
		if (int_pending) {
			int_pending = false;
			halted = false; // Прерывание кадра ВСЕГДА пробуждает процессор из состояния HLT
		}

		// 2. Если процессор в состоянии HLT
		if (halted) {
			return 4; // Будем возвращать по 4 такта
		}

		BYTE op = Read(PC++);
		int cycles = lut_cycles[op];

		// Группа команд MOV r1, r2 (исключая MOV M, M, которая является HLT 0x76)
		if ((op & 0xC0) == 0x40 && op != 0x76) {
			SetReg((op >> 3) & 7, GetReg(op & 7));
			return cycles;
		}

		switch (op) {
			// NOP инструкции
		case 0x00: case 0x08: case 0x10: case 0x18: case 0x20: case 0x28:
		case 0x30: case 0x38: return cycles;

			// Останавливаем процессор до аппаратного прерывания
		case 0x76: halted = true; return cycles;

			// MVI r, imm
		case 0x06: B = Read(PC++); return cycles;
		case 0x0E: C = Read(PC++); return cycles;
		case 0x16: D = Read(PC++); return cycles;
		case 0x1E: E = Read(PC++); return cycles;
		case 0x26: H = Read(PC++); return cycles;
		case 0x2E: L = Read(PC++); return cycles;
		case 0x36: Write(GetHL(), Read(PC++)); return cycles;
		case 0x3E: A = Read(PC++); return cycles;

			// LXI rp, imm
		case 0x01: { WORD l = Read(PC++); WORD h = Read(PC++); SetBC((h << 8) | l); return cycles; }
		case 0x11: { WORD l = Read(PC++); WORD h = Read(PC++); SetDE((h << 8) | l); return cycles; }
		case 0x21: { WORD l = Read(PC++); WORD h = Read(PC++); SetHL((h << 8) | l); return cycles; }
		case 0x31: { WORD l = Read(PC++); WORD h = Read(PC++); SP = (h << 8) | l; return cycles; }

				 // ADD r
		case 0x80: case 0x81: case 0x82: case 0x83: case 0x84: case 0x85:
		case 0x86: case 0x87: { BYTE src = GetReg(op & 7); int r = A + src; SetFlagsAdd(A, src, r); A = (BYTE)r; return cycles; }

				 // ADC r
		case 0x88: case 0x89: case 0x8A: case 0x8B: case 0x8C: case 0x8D:
		case 0x8E: case 0x8F: { BYTE src = GetReg(op & 7); int r = A + src + (CY ? 1 : 0); SetFlagsAdd(A, src, r); A = (BYTE)r; return cycles; }

				 // SUB r
		case 0x90: case 0x91: case 0x92: case 0x93: case 0x94: case 0x95:
		case 0x96: case 0x97: { BYTE src = GetReg(op & 7); int r = A - src; SetFlagsSub(A, src, r); A = (BYTE)r; return cycles; }

				 // SBB r
		case 0x98: case 0x99: case 0x9A: case 0x9B: case 0x9C: case 0x9D:
		case 0x9E: case 0x9F: { BYTE src = GetReg(op & 7); int r = A - src - (CY ? 1 : 0); SetFlagsSub(A, src, r); A = (BYTE)r; return cycles; }

				 // ANA r
		case 0xA0: case 0xA1: case 0xA2: case 0xA3: case 0xA4: case 0xA5:
		case 0xA6: case 0xA7: { A &= GetReg(op & 7); CY = false; AC = true; SetFlagsZSP(A); return cycles; }

				 // XRA r
		case 0xA8: case 0xA9: case 0xAA: case 0xAB: case 0xAC: case 0xAD:
		case 0xAE: case 0xAF: { A ^= GetReg(op & 7); CY = false; AC = false; SetFlagsZSP(A); return cycles; }

				 // ORA r
		case 0xB0: case 0xB1: case 0xB2: case 0xB3: case 0xB4: case 0xB5:
		case 0xB6: case 0xB7: { A |= GetReg(op & 7); CY = false; AC = false; SetFlagsZSP(A); return cycles; }

				 // CMP r
		case 0xB8: case 0xB9: case 0xBA: case 0xBB: case 0xBC: case 0xBD:
		case 0xBE: case 0xBF: { BYTE src = GetReg(op & 7); int r = A - src; SetFlagsSub(A, src, r); return cycles; }

				 // Операции с непосредственным значением (Иммедиат)
		case 0xC6: { BYTE imm = Read(PC++); int r = A + imm; SetFlagsAdd(A, imm, r); A = (BYTE)r; return cycles; }
		case 0xCE: { BYTE imm = Read(PC++); int r = A + imm + (CY ? 1 : 0); SetFlagsAdd(A, imm, r); A = (BYTE)r; return cycles; }
		case 0xD6: { BYTE imm = Read(PC++); int r = A - imm; SetFlagsSub(A, imm, r); A = (BYTE)r; return cycles; }
		case 0xDE: { BYTE imm = Read(PC++); int r = A - imm - (CY ? 1 : 0); SetFlagsSub(A, imm, r); A = (BYTE)r; return cycles; }
		case 0xE6: { A &= Read(PC++); CY = false; AC = true; SetFlagsZSP(A); return cycles; }
		case 0xEE: { A ^= Read(PC++); CY = false; AC = false; SetFlagsZSP(A); return cycles; }
		case 0xF6: { A |= Read(PC++); CY = false; AC = false; SetFlagsZSP(A); return cycles; }
		case 0xFE: { BYTE imm = Read(PC++); int r = A - imm; SetFlagsSub(A, imm, r); return cycles; }

				 // Безусловные JMP / CALL / RET
		case 0xC3: { WORD l = Read(PC++); WORD h = Read(PC++); PC = (h << 8) | l; return cycles; }
		case 0xCD: { WORD l = Read(PC++); WORD h = Read(PC++); Write(--SP, PC >> 8); Write(--SP, PC & 0xFF); PC = (h << 8) | l; return cycles; }
		case 0xC9: { WORD l = Read(SP++); WORD h = Read(SP++); PC = (h << 8) | l; return cycles; }

				 // Возвраты по условию (При переходе тратится 11 тактов вместо 5 базовых)
		case 0xC0: if (!Z) { WORD l = Read(SP++); WORD h = Read(SP++); PC = (h << 8) | l; cycles = 11; } return cycles;
		case 0xC8: if (Z) { WORD l = Read(SP++); WORD h = Read(SP++); PC = (h << 8) | l; cycles = 11; } return cycles;
		case 0xD0: if (!CY) { WORD l = Read(SP++); WORD h = Read(SP++); PC = (h << 8) | l; cycles = 11; } return cycles;
		case 0xD8: if (CY) { WORD l = Read(SP++); WORD h = Read(SP++); PC = (h << 8) | l; cycles = 11; } return cycles;
		case 0xE0: if (!P) { WORD l = Read(SP++); WORD h = Read(SP++); PC = (h << 8) | l; cycles = 11; } return cycles;
		case 0xE8: if (P) { WORD l = Read(SP++); WORD h = Read(SP++); PC = (h << 8) | l; cycles = 11; } return cycles;
		case 0xF0: if (!S) { WORD l = Read(SP++); WORD h = Read(SP++); PC = (h << 8) | l; cycles = 11; } return cycles;
		case 0xF8: if (S) { WORD l = Read(SP++); WORD h = Read(SP++); PC = (h << 8) | l; cycles = 11; } return cycles;

			// Переходы по условию (Всегда занимают 10 тактов в 8080)
		case 0xC2: { WORD l = Read(PC++); WORD h = Read(PC++); if (!Z) { PC = (h << 8) | l; } return cycles; }
		case 0xCA: { WORD l = Read(PC++); WORD h = Read(PC++); if (Z) { PC = (h << 8) | l; } return cycles; }
		case 0xD2: { WORD l = Read(PC++); WORD h = Read(PC++); if (!CY) { PC = (h << 8) | l; } return cycles; }
		case 0xDA: { WORD l = Read(PC++); WORD h = Read(PC++); if (CY) { PC = (h << 8) | l; } return cycles; }
		case 0xE2: { WORD l = Read(PC++); WORD h = Read(PC++); if (!P) { PC = (h << 8) | l; } return cycles; }
		case 0xEA: { WORD l = Read(PC++); WORD h = Read(PC++); if (P) { PC = (h << 8) | l; } return cycles; }
		case 0xF2: { WORD l = Read(PC++); WORD h = Read(PC++); if (!S) { PC = (h << 8) | l; } return cycles; }
		case 0xFA: { WORD l = Read(PC++); WORD h = Read(PC++); if (S) { PC = (h << 8) | l; } return cycles; }

				 // Вызовы по условию (При вызове тратится 17 тактов вместо 11 базовых)
		case 0xC4: { WORD l = Read(PC++); WORD h = Read(PC++); if (!Z) { Write(--SP, PC >> 8); Write(--SP, PC & 0xFF); PC = (h << 8) | l; cycles = 17; } return cycles; }
		case 0xCC: { WORD l = Read(PC++); WORD h = Read(PC++); if (Z) { Write(--SP, PC >> 8); Write(--SP, PC & 0xFF); PC = (h << 8) | l; cycles = 17; } return cycles; }
		case 0xD4: { WORD l = Read(PC++); WORD h = Read(PC++); if (!CY) { Write(--SP, PC >> 8); Write(--SP, PC & 0xFF); PC = (h << 8) | l; cycles = 17; } return cycles; }
		case 0xDC: { WORD l = Read(PC++); WORD h = Read(PC++); if (CY) { Write(--SP, PC >> 8); Write(--SP, PC & 0xFF); PC = (h << 8) | l; cycles = 17; } return cycles; }
		case 0xE4: { WORD l = Read(PC++); WORD h = Read(PC++); if (!P) { Write(--SP, PC >> 8); Write(--SP, PC & 0xFF); PC = (h << 8) | l; cycles = 17; } return cycles; }
		case 0xEC: { WORD l = Read(PC++); WORD h = Read(PC++); if (P) { Write(--SP, PC >> 8); Write(--SP, PC & 0xFF); PC = (h << 8) | l; cycles = 17; } return cycles; }
		case 0xF4: { WORD l = Read(PC++); WORD h = Read(PC++); if (!S) { Write(--SP, PC >> 8); Write(--SP, PC & 0xFF); PC = (h << 8) | l; cycles = 17; } return cycles; }
		case 0xFC: { WORD l = Read(PC++); WORD h = Read(PC++); if (S) { Write(--SP, PC >> 8); Write(--SP, PC & 0xFF); PC = (h << 8) | l; cycles = 17; } return cycles; }

				 // INX / DCX
		case 0x03: SetBC(GetBC() + 1); return cycles;
		case 0x13: SetDE(GetDE() + 1); return cycles;
		case 0x23: SetHL(GetHL() + 1); return cycles;
		case 0x33: SP++; return cycles;
		case 0x0B: SetBC(GetBC() - 1); return cycles;
		case 0x1B: SetDE(GetDE() - 1); return cycles;
		case 0x2B: SetHL(GetHL() - 1); return cycles;
		case 0x3B: SP--; return cycles;

			// INR / DCR
		case 0x04: { BYTE old = B; B++; SetFlagsINR(old, B); return cycles; }
		case 0x05: { BYTE old = B; B--; SetFlagsDCR(old, B); return cycles; }
		case 0x0C: { BYTE old = C; C++; SetFlagsINR(old, C); return cycles; }
		case 0x0D: { BYTE old = C; C--; SetFlagsDCR(old, C); return cycles; }
		case 0x14: { BYTE old = D; D++; SetFlagsINR(old, D); return cycles; }
		case 0x15: { BYTE old = D; D--; SetFlagsDCR(old, D); return cycles; }
		case 0x1C: { BYTE old = E; E++; SetFlagsINR(old, E); return cycles; }
		case 0x1D: { BYTE old = E; E--; SetFlagsDCR(old, E); return cycles; }
		case 0x24: { BYTE old = H; H++; SetFlagsINR(old, H); return cycles; }
		case 0x25: { BYTE old = H; H--; SetFlagsDCR(old, H); return cycles; }
		case 0x2C: { BYTE old = L; L++; SetFlagsINR(old, L); return cycles; }
		case 0x2D: { BYTE old = L; L--; SetFlagsDCR(old, L); return cycles; }
		case 0x34: { BYTE old = Read(GetHL()); BYTE v = old + 1; Write(GetHL(), v); SetFlagsINR(old, v); return cycles; }
		case 0x35: { BYTE old = Read(GetHL()); BYTE v = old - 1; Write(GetHL(), v); SetFlagsDCR(old, v); return cycles; }
		case 0x3C: { BYTE old = A; A++; SetFlagsINR(old, A); return cycles; }
		case 0x3D: { BYTE old = A; A--; SetFlagsDCR(old, A); return cycles; }

				 // DAD rp
		case 0x09: { unsigned int r = (unsigned int)GetHL() + (unsigned int)GetBC(); CY = (r > 0xFFFF); SetHL((WORD)(r & 0xFFFF)); return cycles; }
		case 0x19: { unsigned int r = (unsigned int)GetHL() + (unsigned int)GetDE(); CY = (r > 0xFFFF); SetHL((WORD)(r & 0xFFFF)); return cycles; }
		case 0x29: { unsigned int r = (unsigned int)GetHL() + (unsigned int)GetHL(); CY = (r > 0xFFFF); SetHL((WORD)(r & 0xFFFF)); return cycles; }
		case 0x39: { unsigned int r = (unsigned int)GetHL() + (unsigned int)SP;    CY = (r > 0xFFFF); SetHL((WORD)(r & 0xFFFF)); return cycles; }

				 // PUSH / POP
		case 0xC5: Write(--SP, B); Write(--SP, C); return cycles;
		case 0xD5: Write(--SP, D); Write(--SP, E); return cycles;
		case 0xE5: Write(--SP, H); Write(--SP, L); return cycles;
		case 0xF5: { BYTE psw = (S << 7) | (Z << 6) | (0 << 5) | (AC << 4) | (0 << 3) | (P << 2) | (2) | (CY ? 1 : 0); Write(--SP, A); Write(--SP, psw); return cycles; }
		case 0xC1: C = Read(SP++); B = Read(SP++); return cycles;
		case 0xD1: E = Read(SP++); D = Read(SP++); return cycles;
		case 0xE1: L = Read(SP++); H = Read(SP++); return cycles;
		case 0xF1: { BYTE psw = Read(SP++); A = Read(SP++); S = (psw & 0x80) != 0; Z = (psw & 0x40) != 0; AC = (psw & 0x10) != 0; P = (psw & 0x04) != 0; CY = (psw & 0x01) != 0; return cycles; }

				 // Прямая адресация (STA, LDA, SHLD, LHLD)
		case 0x32: { WORD l = Read(PC++); WORD h = Read(PC++); Write((h << 8) | l, A); return cycles; }
		case 0x3A: { WORD l = Read(PC++); WORD h = Read(PC++); A = Read((h << 8) | l); return cycles; }
		case 0x22: { WORD l = Read(PC++); WORD h = Read(PC++); WORD a = (h << 8) | l; Write(a, L); Write(a + 1, H); return cycles; }
		case 0x2A: { WORD l = Read(PC++); WORD h = Read(PC++); WORD a = (h << 8) | l; L = Read(a); H = Read(a + 1); return cycles; }

				 // Косвенная адресация
		case 0x02: Write(GetBC(), A); return cycles;
		case 0x12: Write(GetDE(), A); return cycles;
		case 0x0A: A = Read(GetBC()); return cycles;
		case 0x1A: A = Read(GetDE()); return cycles;

			// Циклические сдвиги аккумулятора
		case 0x07: { CY = (A & 0x80) != 0; A = (BYTE)(((A << 1) | (CY ? 1 : 0)) & 0xFF); return cycles; }
		case 0x0F: { CY = (A & 1) != 0; A = (BYTE)(((A >> 1) | (CY ? 0x80 : 0)) & 0xFF); return cycles; }
		case 0x17: { bool old_cy = CY; CY = (A & 0x80) != 0; A = (BYTE)(((A << 1) | (old_cy ? 1 : 0)) & 0xFF); return cycles; }
		case 0x1F: { bool old_cy = CY; CY = (A & 1) != 0; A = (BYTE)(((A >> 1) | (old_cy ? 0x80 : 0)) & 0xFF); return cycles; }

				 // RST 0 - RST 7
		case 0xC7: case 0xCF: case 0xD7: case 0xDF: case 0xE7: case 0xEF: case 0xF7: case 0xFF:
			Write(--SP, PC >> 8); Write(--SP, PC & 0xFF); PC = (op & 0x38); return cycles;

			// OUT port
		case 0xD3: {
			BYTE port = Read(PC++);
			WORD target_addr = (port << 8) | port; // Аппаратное дублирование байта порта
			Write(target_addr, A);                 // Перенаправляем запись в память (в область портов)
			return cycles;
		}

				 // IN port
		case 0xDB: {
			BYTE port = Read(PC++);
			WORD target_addr = (port << 8) | port; // Аппаратное дублирование байта порта
			A = Read(target_addr);                 // Читаем из памяти как из порта
			return cycles;
		}

				 // Десятичная коррекция аккумулятора (DAA)
		case 0x27: {
			BYTE corr = 0; bool new_cy = CY;
			if ((A & 0x0F) > 9 || AC) corr |= 0x06;
			if (A > 0x99 || CY) { corr |= 0x60; new_cy = true; }
			int res = A + corr; AC = ((A & 0x0F) + (corr & 0x0F)) > 0x0F;
			A = (BYTE)res; CY = new_cy; SetFlagsZSP(A); return cycles;
		}

				 // Специальные команды
		case 0x2F: A = (BYTE)(~A & 0xFF); return cycles;
		case 0x37: CY = true; return cycles;
		case 0x3F: CY = !CY; return cycles;
		case 0xEB: { BYTE t = D; D = H; H = t; t = E; E = L; L = t; return cycles; }
		case 0xE3: { BYTE l = Read(SP); BYTE h = Read(SP + 1); Write(SP, L); Write(SP + 1, H); L = l; H = h; return cycles; }
		case 0xF9: SP = GetHL(); return cycles;
		case 0xE9: PC = GetHL(); return cycles;

		case 0xFB: EI = true; rk_inte_speaker_state = true; return cycles;  // EI включает INTE
		case 0xF3: EI = false; rk_inte_speaker_state = false; return cycles; // DI выключает INTE
		}
		return cycles;
	}
};
#pragma pack(pop)

CPU8080 cpu;
HWND button_matrix;

// --- ЗАГРУЗКА И КОРРЕКТИРОВКА РОМОВ ---
bool LoadRawBinaryFile(const wchar_t* filepath, BYTE* target_dest, size_t max_bytes) {
	std::ifstream file(filepath, std::ios::binary);
	if (!file.is_open()) return false;
	file.read(reinterpret_cast<char*>(target_dest), max_bytes);
	file.close();
	return true;
}

void LoadRoms() {
	cpu.Reset();
	if (!LoadRawBinaryFile(BIOS_NAME, &system_ram[BIOS_START_ADDRESS], BIOS_SIZE)) {
		MessageBoxW(NULL, L"Критическая ошибка: Не удалось открыть bios.bin!", L"Ошибка", MB_OK | MB_ICONERROR);
	}
	if (!LoadRawBinaryFile(L"font.bin", font_rom, 2048)) {
		MessageBoxW(NULL, L"Критическая ошибка: Не удалось открыть font.bin!", L"Ошибка", MB_OK | MB_ICONERROR);
	}
	// ДОБАВЛЕНО: Загрузка РОМ-диска 64 Кб для Порта Пользователя №1
	memset(rom_disk_storage, 0xFF, sizeof(rom_disk_storage)); // Инициализация чистой памяти
	if (!LoadRawBinaryFile(L"rom_disk.bin", rom_disk_storage, 32768)) {
		MessageBoxW(NULL, L"Не удалось открыть файл РОМ-диска rom_disk.bin!\nБудет смонтирован пустой диск.", L"Информация", MB_OK | MB_ICONINFORMATION);
	}
	for (int i = 0; i < 8; i++) key_matrix_state[i] = 0xFF;
}

void UpdateRegisterDisplay() {
	SendMessageW(hRegListBox, LB_RESETCONTENT, 0, 0);
	wchar_t buf[64];
	swprintf(buf, 64, L" PC: %04Xh SP: %04Xh", cpu.PC, cpu.SP); SendMessageW(hRegListBox, LB_ADDSTRING, 0, (LPARAM)buf);
	buf[0] = L'\0';
	swprintf(buf, 64, L" REG A: %02Xh PSW: %02Xh", cpu.A, (cpu.S << 7) | (cpu.Z << 6) | (cpu.AC << 4) | (cpu.P << 2) | 1 | cpu.CY); SendMessageW(hRegListBox, LB_ADDSTRING, 0, (LPARAM)buf);
	buf[0] = L'\0';
	swprintf(buf, 64, L" REG B: %02Xh REG C: %02Xh", cpu.B, cpu.C); SendMessageW(hRegListBox, LB_ADDSTRING, 0, (LPARAM)buf);
	buf[0] = L'\0';
	swprintf(buf, 64, L" REG D: %02Xh REG E: %02Xh", cpu.D, cpu.E); SendMessageW(hRegListBox, LB_ADDSTRING, 0, (LPARAM)buf);
	buf[0] = L'\0';
	swprintf(buf, 64, L" REG H: %02Xh REG L: %02Xh", cpu.H, cpu.L); SendMessageW(hRegListBox, LB_ADDSTRING, 0, (LPARAM)buf);
	buf[0] = L'\0';
	swprintf(buf, 64, L" Флаги: S:%d Z:%d AC:%d P:%d CY:%d", cpu.S, cpu.Z, cpu.AC, cpu.P, cpu.CY); SendMessageW(hRegListBox, LB_ADDSTRING, 0, (LPARAM)buf);
	buf[0] = L'\0';
	swprintf(buf, 64, L" DMA (ВТ57): %04Xh", cpu.dma_ch_addr[2]); SendMessageW(hRegListBox, LB_ADDSTRING, 0, (LPARAM)buf);
}

// =========================================================================
//   ФУНКЦИЯ ПРЕЦИЗИОННОГО ВЫВОДА ЭКРАНА С УЧЕТОМ СИНХРОБАЙТОВ ВГ75
//   СОХРАНЯЕТ ОРИГИНАЛЬНЫЙ ЦИКЛ (ЧЕРНЫЙ ФОН, БЕЛЫЙ ШРИФТ)
// =========================================================================
void RenderScreen(HDC hdc, int xOffset, int yOffset) {
	WORD screen_ram_start = cpu.dma_ch_addr[2];
	if (screen_ram_start == 0 || screen_ram_start > 0x7FFF) screen_ram_start = 0x76D0;

	const int RK_STRIDE = 78;
	const int RK_START_ROW = 3;
	const int RK_START_COL = 8;
	const int tex_width = SCREEN_COLS * CHAR_WIDTH;
	const int tex_height = SCREEN_ROWS * CHAR_HEIGHT;

	static DWORD pixel_buffer[384 * 200];
	for (int i = 0; i < 384 * 200; i++) pixel_buffer[i] = 0x00000000;

	for (int row = 0; row < SCREEN_ROWS; row++) {
		int visible_col = 0;
		for (int col = RK_START_COL; col < RK_STRIDE; col++) {
			if (visible_col >= SCREEN_COLS) break;
			WORD char_addr = screen_ram_start + (RK_START_ROW + row) * RK_STRIDE + col;
			BYTE code = system_ram[char_addr & 0xFFFF];

			if (code >= 0xF0) break;

			// ПРАВИЛЬНАЯ ФИЛЬТРАЦИЯ АТРИБУТОВ ВГ75 ДЛЯ ИНВЕРТИРОВАННОГО ШРИФТА:
			// Вместо continue (который сдвигал строки) или 0x20 (который рисовал белые квадраты),
			// мы используем логический флаг пустого символа, чтобы прорисовать пустой черный блок.
			bool is_attribute = (code >= 0x80 && code <= 0x9F);

			for (int line = 0; line < CHAR_HEIGHT; line++) {
				// Если это служебный атрибут ВГ75, подставляем пустую инвертированную строку (0xFF),
				// чтобы при проверке "== 0" этот пиксель пропустился и остался черным.
				BYTE font_byte = is_attribute ? 0xFF : font_rom[(code << 3) + line];

				int pixel_y = (tex_height - 1) - (row * CHAR_HEIGHT + line);
				for (int bit = 0; bit < CHAR_WIDTH; bit++) {
					if ((font_byte & (0x20 >> bit)) == 0) {
						int pixel_x = visible_col * CHAR_WIDTH + bit;
						if (pixel_x < tex_width && pixel_y >= 0 && pixel_y < tex_height) {
							pixel_buffer[pixel_y * tex_width + pixel_x] = 0x00FFFFFF;
						}
					}
				}
			}
			visible_col++;
		}
	}

	BITMAPINFO bmi = { 0 };
	bmi.bmiHeader.biSize = sizeof(BITMAPINFOHEADER);
	bmi.bmiHeader.biWidth = tex_width;
	bmi.bmiHeader.biHeight = tex_height;
	bmi.bmiHeader.biPlanes = 1;
	bmi.bmiHeader.biBitCount = 32;
	bmi.bmiHeader.biCompression = BI_RGB;

	StretchDIBits(hdc, xOffset, yOffset, tex_width * 2, tex_height * 2, 0, 0, tex_width, tex_height, pixel_buffer, &bmi, DIB_RGB_COLORS, SRCCOPY);
}


#ifndef BS_NOFOCUS
#define BS_NOFOCUS 0x00008000L
#endif

// =========================================================================
// ФУНКЦИЯ ДИНАМИЧЕСКОЙ ГЕНЕРАЦИИ ИНТЕРФЕЙСА КЛАВИАТУРЫ
// =========================================================================
void CreateKeyboardUI(HWND hwndParent, HINSTANCE hInst) {
	const int BTN_W = 40; const int BTN_H = 40; const int START_X = 20; const int START_Y = 440; const int GAP = 4;

	// Возвращаем полный массив надписей, где элемент "СБ" заменен на пустую заглушку
	static const wchar_t* main_labels[] = {
		L";\n+", L"1\n!", L"2\n\"", L"3\n#", L"4\n$", L"5\n%", L"6\n&", L"7\n'", L"8\n(", L"9\n)", L"0", L"-\n=", L"ТАБ", L"ПС", L"", // Индекс 14: Бывшая кнопка "СБ" (теперь пустая заглушка)
		L"Й\nJ", L"Ц\nC", L"У\nU", L"К\nK", L"Е\nE", L"Н\nN", L"Г\nG", L"Ш\n[", L"Щ\n]", L"З\nZ", L"Х\nH", L":\n*", L"ВК", L"", L"",
		L"УС", L"Ф\nF", L"Ы\nY", L"В\nW", L"А\nA", L"П\nP", L"Р\nR", L"О\nO", L"Л\nL", L"Д\nD", L"Ж\n\\V", L"Э\n\\", L".\n>", L"ЗБ", L"",
		L"СС", L"Я\nQ", L"Ч\n^", L"С\nS", L"М\nM", L"И\nI", L"Т\nT", L"Ь\nX", L"Б\nB", L"Ю\n@", L",\n<", L"/\n?", L"РУС\nЛАТ", L"[ _ ]", L"[ _ ]"
	};
	static const wchar_t* side_labels[] = { L" ", L"F1", L"СТР", L"←", L"↑", L"→", L"F2", L"F3", L"F4", L"↓", L"AP2", L"" };

	for (int idx = 0; idx < 60; idx++) {
		int r = idx / 15; int c = idx % 15; int current_id = 1000 + idx;

		// КРИТИЧЕСКОЕ ИСПРАВЛЕНИЕ: Просто пропускаем физическое создание кнопки "СБ"
		if (idx == 14) continue;

		if ((r == 1 && c >= 13) || (r == 2 && c == 14)) continue;
		int x = START_X + c * (BTN_W + GAP); int y = START_Y + r * (BTN_H + GAP);

		if (r == 3 && c == 13) {
			CreateWindowExW(0, L"BUTTON", main_labels[idx],
				WS_CHILD | WS_VISIBLE | BS_PUSHBUTTON | BS_MULTILINE | BS_FLAT | BS_NOFOCUS,
				x, y, (BTN_W * 2) + GAP, BTN_H, hwndParent, (HMENU)(INT_PTR)current_id, hInst, NULL);
			continue;
		}
		if (r == 3 && c == 14) continue;

		CreateWindowExW(0, L"BUTTON", main_labels[idx],
			WS_CHILD | WS_VISIBLE | BS_PUSHBUTTON | BS_MULTILINE | BS_FLAT | BS_NOFOCUS,
			x, y, BTN_W, BTN_H, hwndParent, (HMENU)(INT_PTR)current_id, hInst, NULL);
	}

	int SIDE_START_X = START_X + 15 * (BTN_W + GAP) + 15;
	for (int side_idx = 0; side_idx < 12; side_idx++) {
		int r = side_idx / 3; int c = side_idx % 3; int current_id = 1060 + side_idx;
		if (r == 3 && c == 2) continue;
		int x = SIDE_START_X + c * (BTN_W + GAP); int y = START_Y + r * (BTN_H + GAP);
		CreateWindowExW(0, L"BUTTON", side_labels[side_idx],
			WS_CHILD | WS_VISIBLE | BS_PUSHBUTTON | BS_MULTILINE | BS_FLAT | BS_NOFOCUS,
			x, y, BTN_W, BTN_H, hwndParent, (HMENU)(INT_PTR)current_id, hInst, NULL);
	}
}

static const int rk_hardware_map[] = {
	// РЯД 1: Индекс 14 (кнопка СБ) занулен и безопасен
	3 * 8 + 3, 2 * 8 + 1, 2 * 8 + 2, 2 * 8 + 3, 2 * 8 + 4, 2 * 8 + 5, 2 * 8 + 6, 2 * 8 + 7, 3 * 8 + 0, 3 * 8 + 1, 2 * 8 + 0, 3 * 8 + 5, 1 * 8 + 0, 1 * 8 + 1, 0,
	// РЯД 2
	5 * 8 + 2, 4 * 8 + 3, 6 * 8 + 5, 5 * 8 + 3, 4 * 8 + 5, 5 * 8 + 6, 4 * 8 + 7, 7 * 8 + 3, 7 * 8 + 5, 7 * 8 + 2, 5 * 8 + 0, 3 * 8 + 2, 1 * 8 + 2, 0, 0,
	// РЯД 3
	0,         4 * 8 + 6, 7 * 8 + 1, 6 * 8 + 7, 4 * 8 + 1, 6 * 8 + 0, 6 * 8 + 2, 5 * 8 + 7, 5 * 8 + 4, 4 * 8 + 4, 6 * 8 + 6, 7 * 8 + 4, 3 * 8 + 6, 1 * 8 + 3, 0,
	// РЯД 4: Кнопка РУС/ЛАТ находится строго под своим исходным ID (1000 + 57)
	0,         6 * 8 + 1, 7 * 8 + 6, 6 * 8 + 3, 5 * 8 + 5, 5 * 8 + 1, 6 * 8 + 4, 7 * 8 + 0, 4 * 8 + 2, 4 * 8 + 0, 3 * 8 + 4, 3 * 8 + 7, 0,         7 * 8 + 7, 7 * 8 + 7,
	// ДОПОЛНИТЕЛЬНЫЙ БЛОК СПРАВА
	0 * 8 + 0, 0 * 8 + 3, 0 * 8 + 1, 1 * 8 + 4, 1 * 8 + 5, 1 * 8 + 6, 0 * 8 + 4, 0 * 8 + 5, 0 * 8 + 6, 1 * 8 + 7, 0 * 8 + 2, 0
};

/*
bool MapVirtualKeyToRK(UINT vkCode, int& out_row, int& out_col) {
	int target_idx = -1;
	switch (vkCode) {
		case 0xC0: target_idx = 0; break;
		case '1': target_idx = 1; break; case '2': target_idx = 2; break; case '3': target_idx = 3; break;
		case '4': target_idx = 4; break; case '5': target_idx = 5; break; case '6': target_idx = 6; break;
		case '7': target_idx = 7; break; case '8': target_idx = 8; break; case '9': target_idx = 9; break;
		case '0': target_idx = 10; break; case 0xBB: target_idx = 11; break;
		case 'Q': target_idx = 15; break; case 'W': target_idx = 16; break; case 'E': target_idx = 17; break;
		case 'R': target_idx = 18; break; case 'T': target_idx = 19; break; case 'Y': target_idx = 20; break;
		case 'U': target_idx = 21; break; case 'I': target_idx = 22; break; case 'O': target_idx = 23; break;
		case 'P': target_idx = 24; break; case 0xDB: target_idx = 25; break; case 0xDD: target_idx = 26; break;
		case VK_RETURN: target_idx = 27; break;
		case 'A': target_idx = 31; break; case 'S': target_idx = 32; break; case 'D': target_idx = 33; break;
		case 'F': target_idx = 34; break; case 'G': target_idx = 35; break; case 'H': target_idx = 36; break;
		case 'J': target_idx = 37; break; case 'K': target_idx = 38; break; case 'L': target_idx = 39; break;
		case 0xBA: target_idx = 40; break; case 0xDE: target_idx = 41; break; case 0xBF: target_idx = 42; break;
		case VK_BACK: target_idx = 43; break;
		case 'Z': target_idx = 46; break; case 'X': target_idx = 47; break; case 'C': target_idx = 48; break;
		case 'V': target_idx = 49; break; case 'B': target_idx = 50; break; case 'N': target_idx = 51; break;
		case 'M': target_idx = 52; break; case 0xBC: target_idx = 53; break; case 0xBE: target_idx = 54; break;
		case VK_SPACE: target_idx = 58; break;
		case VK_LEFT: target_idx = 63; break; case VK_UP: target_idx = 64; break; case VK_RIGHT: target_idx = 65; break;
		case VK_DOWN: target_idx = 69; break;  case VK_HOME: target_idx = 60; break;
	}
	if (target_idx != -1) {
		int hw_code = rk_hardware_map[target_idx];
		out_row = hw_code / 8; out_col = hw_code % 8;
		return true;
	}
	return false;
}
*/

bool MapVirtualKeyToRK(UINT vkCode, int& out_row, int& out_col) {
	int target_idx = -1;
	switch (vkCode) {
		// --- ЦИФРОВОЙ РЯД ПК ---
	case 0xC0: target_idx = 0;  break; // Клавиша ` / Ё  -> мапим на [;] (Index 0)
	case '1':  target_idx = 1;  break;
	case '2':  target_idx = 2;  break;
	case '3':  target_idx = 3;  break;
	case '4':  target_idx = 4;  break;
	case '5':  target_idx = 5;  break;
	case '6':  target_idx = 6;  break;
	case '7':  target_idx = 7;  break;
	case '8':  target_idx = 8;  break;
	case '9':  target_idx = 9;  break;
	case '0':  target_idx = 10; break;
	case 0xBD: target_idx = 11; break; // Клавиша минус [-] -> мапим на [-] (Index 11)

		// --- БУКВЕННЫЕ КЛАВИШИ: СИМВОЛЬНОЕ СООТВЕТСТВИЕ QWERTY ---
		// Ищем в main_labels, на какой кнопке РК находится нужная латинская буква
	case 'Q': target_idx = 46; break; // Нажимаем ПК 'Q' -> РК выдает 'Q' (Кнопка Я/Q, Index 46)
	case 'W': target_idx = 33; break; // Нажимаем ПК 'W' -> РК выдает 'W' (Кнопка В/W, Index 33)
	case 'E': target_idx = 19; break; // Нажимаем ПК 'E' -> РК выдает 'E' (Кнопка Е/E, Index 19)
	case 'R': target_idx = 36; break; // Нажимаем ПК 'R' -> РК выдает 'R' (Кнопка Р/R, Index 36)
	case 'T': target_idx = 51; break; // Нажимаем ПК 'T' -> РК выдает 'T' (Кнопка Т/T, Index 51)
	case 'Y': target_idx = 32; break; // Нажимаем ПК 'Y' -> РК выдает 'Y' (Кнопка Ы/Y, Index 32)
	case 'U': target_idx = 17; break; // Нажимаем ПК 'U' -> РК выдает 'U' (Кнопка У/U, Index 17)
	case 'I': target_idx = 50; break; // Нажимаем ПК 'I' -> РК выдает 'I' (Кнопка И/I, Index 50)
	case 'O': target_idx = 37; break; // Нажимаем ПК 'O' -> РК выдает 'O' (Кнопка О/O, Index 37)
	case 'P': target_idx = 35; break; // Нажимаем ПК 'P' -> РК выдает 'P' (Кнопка П/P, Index 35)

	case 'A': target_idx = 34; break; // Нажимаем ПК 'A' -> РК выдает 'A' (Кнопка А/A, Index 34)
	case 'S': target_idx = 48; break; // Нажимаем ПК 'S' -> РК выдает 'S' (Кнопка С/S, Index 48)
	case 'D': target_idx = 39; break; // Нажимаем ПК 'D' -> РК выдает 'D' (Кнопка Д/D, Index 39)
	case 'F': target_idx = 31; break; // Нажимаем ПК 'F' -> РК выдает 'F' (Кнопка Ф/F, Index 31)
	case 'G': target_idx = 21; break; // Нажимаем ПК 'G' -> РК выдает 'G' (Кнопка Г/G, Index 21)
	case 'H': target_idx = 25; break; // Нажимаем ПК 'H' -> РК выдает 'H' (Кнопка Х/H, Index 25)
	case 'J': target_idx = 15; break; // Нажимаем ПК 'J' -> РК выдает 'J' (Кнопка Й/J, Index 15)
	case 'K': target_idx = 18; break; // Нажимаем ПК 'K' -> РК выдает 'K' (Кнопка К/K, Index 18)
	case 'L': target_idx = 38; break; // Нажимаем ПК 'L' -> РК выдает 'L' (Кнопка Л/L, Index 38)

	case 'Z': target_idx = 24; break; // Нажимаем ПК 'Z' -> РК выдает 'Z' (Кнопка З/Z, Index 24)
	case 'X': target_idx = 52; break; // Нажимаем ПК 'X' -> РК выдает 'X' (Кнопка Ь/X, Index 52)
	case 'C': target_idx = 16; break; // Нажимаем ПК 'C' -> РК выдает 'C' (Кнопка Ц/C, Index 16)
	case 'V': target_idx = 40; break; // Нажимаем ПК 'V' -> РК выдает 'V' (Кнопка Ж/\V, Index 40)
	case 'B': target_idx = 53; break; // Нажимаем ПК 'B' -> РК выдает 'B' (Кнопка Б/B, Index 53)
	case 'N': target_idx = 20; break; // Нажимаем ПК 'N' -> РК выдает 'N' (Кнопка Н/N, Index 20)
	case 'M': target_idx = 49; break; // Нажимаем ПК 'M' -> РК выдает 'M' (Кнопка М/M, Index 49)

		// --- ПУНКТУАЦИЯ И СПЕЦСИМВОЛЫ ---
	case 0xDB: target_idx = 22; break; // Клавиша [ { -> мапим на Ш / [ (Index 22)
	case 0xDD: target_idx = 23; break; // Клавиша ] } -> мапим на Щ / ] (Index 23)
	case 0xBA: target_idx = 26; break; // Клавиша ; : -> мапим на : / * (Index 26)
	case 0xDE: target_idx = 41; break; // Клавиша ' " -> мапим на Э / \ (Index 41)
	case 0xBC: target_idx = 55; break; // Клавиша , < -> мапим на РК-шную запятую (Index 55)
	case 0xBE: target_idx = 42; break; // Клавиша . > -> мапим на . / > (Index 42)
	case 0xBF: target_idx = 56; break; // Клавиша / ? -> мапим на РК-шный слэш (Index 56)

	case VK_RETURN: target_idx = 27; break; // ВК (Enter)
	case VK_BACK:   target_idx = 43; break; // ЗБ (Backspace)
	case VK_SPACE:  target_idx = 58; break; // ПРОБЕЛ

		// --- УПРАВЛЯЮЩИЙ БЛОК ПК И СТРЕЛКИ ---
	case VK_F1:    target_idx = 61; break; // Кнопка F1
	case VK_F2:    target_idx = 66; break; // Кнопка F2
	case VK_F3:    target_idx = 67; break; // Кнопка F3
	case VK_F4:    target_idx = 68; break; // Кнопка F4
	case VK_LEFT:  target_idx = 63; break;
	case VK_UP:    target_idx = 64; break;
	case VK_RIGHT: target_idx = 65; break;
	case VK_DOWN:  target_idx = 69; break;
	case VK_HOME:  target_idx = 60; break; // "в угол"
	}

	if (target_idx != -1) {
		int hw_code = rk_hardware_map[target_idx];
		out_row = hw_code / 8; out_col = hw_code % 8;
		return true;
	}
	return false;
}

void LoadRKFile(HWND hwnd) {
	OPENFILENAMEW ofn;
	wchar_t szFile[260] = { 0 };

	ZeroMemory(&ofn, sizeof(ofn));
	ofn.lStructSize = sizeof(ofn);
	ofn.hwndOwner = hwnd;
	ofn.lpstrFile = szFile;
	ofn.nMaxFile = sizeof(szFile);
	ofn.lpstrFilter = L"Файлы Радио-86РК (*.rk;*.rk86)\0*.rk;*.rk86\0Все файлы (*.*)\0*.*\0";
	ofn.nFilterIndex = 1;
	ofn.lpstrFileTitle = NULL;
	ofn.nMaxFileTitle = 0;
	ofn.lpstrInitialDir = NULL;
	ofn.Flags = OFN_PATHMUSTEXIST | OFN_FILEMUSTEXIST;

	if (GetOpenFileNameW(&ofn) == TRUE) {
		std::ifstream file(ofn.lpstrFile, std::ios::binary);
		if (!file.is_open()) {
			MessageBoxW(hwnd, L"Не удалось открыть файл!", L"Ошибка", MB_OK | MB_ICONERROR);
			return;
		}

		// Читаем начальный адрес (2 байта, Big Endian в формате .RK)
		BYTE start_h = file.get();
		BYTE start_l = file.get();
		WORD start_addr = (start_h << 8) | start_l;

		// Читаем конечный адрес (2 байта, Big Endian)
		BYTE end_h = file.get();
		BYTE end_l = file.get();
		WORD end_addr = (end_h << 8) | end_l;

		if (file.eof() || start_addr > end_addr || end_addr > 0x7FFF) {
			MessageBoxW(hwnd, L"Неверный формат или поврежденный .RK файл!\nЗагрузка выше 7FFFh запрещена.", L"Ошибка", MB_OK | MB_ICONERROR);
			file.close();
			return;
		}

		// Вычисляем размер блока данных
		size_t data_size = end_addr - start_addr + 1;

		// Считываем бинарные данные напрямую в эмулируемое системное ОЗУ
		file.read(reinterpret_cast<char*>(&system_ram[start_addr]), data_size);
		file.close();

		// Аппаратный запуск: перенаправляем указатель инструкций (PC) на старт программы
		cpu.PC = start_addr;

		// Обновляем окна отладчика и сбрасываем залипшие клавиши
		for (int i = 0; i < 8; i++) key_matrix_state[i] = 0xFF;
		UpdateRegisterDisplay();
		InvalidateRect(hwnd, NULL, FALSE);

		wchar_t success_msg[128];
		swprintf(success_msg, 128, L"Файл успешно загружен!\nАдреса: %04Xh - %04Xh\nПереход на %04Xh выполнен.", start_addr, end_addr, start_addr);
		MessageBoxW(hwnd, success_msg, L"Успех", MB_OK | MB_ICONINFORMATION);
	}
}

int static_virtual_key_duration = 0; // Наш счетчик автоотжатия кнопок мыши
const int HARDWARE_MAP_SIZE = sizeof(rk_hardware_map) / sizeof(rk_hardware_map[0]);

// =========================================================================
// ОКОННАЯ ПРОЦЕДУРА С ПОТОКОВОЙ СИНХРОНИЗАЦИЕЙ (БЕЗ ТАЙМЕРОВ)
// =========================================================================
LRESULT CALLBACK WndProc(HWND hwnd, UINT msg, WPARAM wp, LPARAM lp) {
	static HINSTANCE hInst;
	switch (msg) {
	case WM_CREATE: {
		LPCREATESTRUCTW pcs = (LPCREATESTRUCTW)lp;
		hInst = pcs->hInstance;

		// --- ATTACHING OPTIONS DIRECTLY TO WINDOWS SYSTEM MENU ---
		HMENU hSysMenu = GetSystemMenu(hwnd, FALSE);
		if (hSysMenu) {
			AppendMenuW(hSysMenu, MF_SEPARATOR, 0, NULL);
			AppendMenuW(hSysMenu, MF_STRING, IDM_FILE_OPEN, L"Открыть .RK файл...");
		}

		CreateKeyboardUI(hwnd, hInst);
		int RIGHT_PANEL_X = 810;
		CreateWindowExW(0, L"BUTTON", L"СБРОС (RESET)", WS_CHILD | WS_VISIBLE | BS_PUSHBUTTON, RIGHT_PANEL_X, 20, 240, 40, hwnd, (HMENU)2000, hInst, NULL);
		hRegListBox = CreateWindowExW(WS_EX_CLIENTEDGE, L"LISTBOX", NULL, WS_CHILD | WS_VISIBLE | WS_VSCROLL, RIGHT_PANEL_X, 75, 240, 245, hwnd, (HMENU)2001, NULL, NULL);

		cpu.Reset();
		UpdateRegisterDisplay();
		return 0;
	}
	case WM_SYSCOMMAND: {
		// Применяем побитовую маску 0xFFF0, как требует документация Microsoft Win32
		if ((wp & 0xFFF0) == IDM_FILE_OPEN) {
			LoadRKFile(hwnd); // Вызываем окно выбора и инжекции файла
			return 0;
		}
		// Все остальные команды (сворачивание, перетаскивание, закрытие) отдаем ОС
		return DefWindowProcW(hwnd, msg, wp, lp);
	}
	case WM_COMMAND: {
		int btn_id = LOWORD(wp);

		// 1. Обработка кнопки СБРОС (RESET)
		if (btn_id == 2000) {
			cpu.Reset();
			for (int i = 0; i < 8; i++) key_matrix_state[i] = 0xFF;
			UpdateRegisterDisplay();
			InvalidateRect(hwnd, NULL, FALSE);
			return 0;
		}

		// 2. Обработка виртуальных клавиш клавиатуры (ID от 1000 до 1071)
		int btn_idx = btn_id - 1000;
		if (btn_idx >= 0 && btn_idx < HARDWARE_MAP_SIZE) {
			UINT target_vk = 0;

			// Находим соответствующий Virtual Key (VK) для этой кнопки
			for (int vk_test = 0; vk_test < 256; vk_test++) {
				int r = -1, c = -1;
				if (MapVirtualKeyToRK(vk_test, r, c)) {
					int hw_code = rk_hardware_map[btn_idx];
					if ((hw_code / 8 == r) && (hw_code % 8 == c)) {
						target_vk = vk_test;
						break;
					}
				}
			}

			// Ручной маппинг системных модификаторов
			if (btn_idx == 57) target_vk = VK_CAPITAL;      // РУС/ЛАТ
			else if (btn_idx == 45) target_vk = VK_SHIFT;   // СС
			else if (btn_idx == 30) target_vk = VK_CONTROL; // УС

			// Если кнопка валидна — зажимаем её в матрице НАПРЯМУЮ
			if (target_vk != 0) {
				// Выделяем 4 кадра удержания (~80 мс), чтобы процессор точно успел считать её
				static_virtual_key_duration = 4;

				if (target_vk == VK_CAPITAL) { rk_rus_lat_pressed = true; }
				else if (target_vk == VK_SHIFT) { rk_cc_pressed = true; }
				else if (target_vk == VK_CONTROL) { rk_us_pressed = true; }
				else {
					int r = -1, c = -1;
					if (MapVirtualKeyToRK(target_vk, r, c)) {
						if (r >= 0 && r < 8) {
							key_matrix_state[r] &= ~(1 << c); // Замыкаем контакт напрямую
						}
					}
				}
			}

			// Возвращаем фокус на главное окно, чтобы продолжала работать физическая клавиатура
			SetFocus(hwnd);
			return 0;
		}
		break;
	}
	case WM_PAINT: {
		PAINTSTRUCT ps; HDC hdc = BeginPaint(hwnd, &ps);
		RenderScreen(hdc, 20, 20);
		EndPaint(hwnd, &ps);
		break;
	}
	case WM_DESTROY:
		PostQuitMessage(0);
		break;
	default:
		return DefWindowProcW(hwnd, msg, wp, lp);
	}
	return 0;
}

// Генерирование звука через КР580ВИ53 на основе накопленной фазы частоты
void FillAudioBuffer(short* buffer, int samplesCount) {
	const double PIT_CLOCK_HZ = 1780000.0;
	const double TICKS_PER_SAMPLE = PIT_CLOCK_HZ / (double)AUDIO_SAMPLE_RATE;
	static double ticks_accumulator = 0.0;

	for (int i = 0; i < samplesCount; i++) {
		ticks_accumulator += TICKS_PER_SAMPLE;
		int ticks_to_consume = (int)ticks_accumulator;
		ticks_accumulator -= ticks_to_consume;

		if (ticks_to_consume <= 0) {
			buffer[i] = (i > 0) ? buffer[i - 1] : 0;
			continue;
		}

		int active_channels = 0;
		int mixed_signal = 0;

		// 1. Эмуляция каналов КР580ВИ53 (остается оригинальной)
		for (int ch = 0; ch < 3; ch++) {
			CPU8080::PITChannel& channel = cpu.pit_channels[ch];
			WORD divisor = channel.count;
			BYTE mode = channel.mode & 7;

			if (divisor > 3 && (mode == 2 || mode == 3)) {
				if (channel.phase <= 0.0 || channel.phase > (double)divisor) {
					channel.phase = (double)(divisor / 2);
				}
				channel.phase -= (double)ticks_to_consume;
				if (channel.phase <= 0.0) {
					channel.phase += (double)(divisor / 2);
					channel.latched = !channel.latched;
				}
				mixed_signal += channel.latched ? 1 : -1;
				active_channels++;
			}
		}

		// 2. Извлечение СИНХРОННОГО сигнала INTE из кольцевого буфера
		int inte_signal = 0;
		if (inte_ring_read_ptr != inte_ring_write_ptr) {
			inte_signal = inte_ring_buffer[inte_ring_read_ptr];
			inte_ring_read_ptr = (inte_ring_read_ptr + 1) % INTE_RING_BUF_SIZE;
		}
		else {
			// Если буфер пуст, берем последнее состояние (стабилизация)
			inte_signal = rk_inte_speaker_state ? 4000 : -4000;
		}

		// 3. Микширование сигналов
		if (active_channels > 0) {
			// Нормализуем меандр ВИ53 к значениям громкости и прибавляем сигнал INTE
			int vi53_signal = mixed_signal * 5000 / active_channels;
			buffer[i] = (short)((vi53_signal + inte_signal) / 2);
		}
		else {
			// Работает только чистый бипер INTE
			buffer[i] = (short)inte_signal;
		}
	}
}

void CALLBACK WaveOutCallback(HWAVEOUT hwo, UINT uMsg, DWORD_PTR dwInstance, DWORD_PTR dwParam1, DWORD_PTR dwParam2) {
	if (uMsg == WOM_DONE) {
		WAVEHDR* pHdr = (WAVEHDR*)dwParam1;
		FillAudioBuffer((short*)pHdr->lpData, AUDIO_BUF_SIZE);
		waveOutWrite(hwo, pHdr, sizeof(WAVEHDR));
	}
}

static double audio_ticks_accumulator = 0.0;
const double PIT_CLOCK_HZ = 1780000.0;
const double TICKS_PER_SAMPLE = PIT_CLOCK_HZ / (double)AUDIO_SAMPLE_RATE;

int WINAPI WinMain(HINSTANCE hInst, HINSTANCE, LPSTR, int nCmdShow) {
	LoadRoms();
	WNDCLASSW wc = { 0 };
	wc.lpfnWndProc = WndProc;
	wc.hInstance = hInst;
	wc.hCursor = LoadCursor(NULL, IDC_ARROW);
	wc.hbrBackground = (HBRUSH)(COLOR_BTNFACE + 1);
	wc.lpszClassName = L"Radio86RK_Emulator_Unicode";
	RegisterClassW(&wc);

	HWND hwnd = CreateWindowExW(0, L"Radio86RK_Emulator_Unicode", L"Радио-86РК Симулятор",
		WS_OVERLAPPEDWINDOW & ~WS_THICKFRAME & ~WS_MAXIMIZEBOX, CW_USEDEFAULT,
		CW_USEDEFAULT, 1080, 670, NULL, NULL, hInst, NULL);
	ShowWindow(hwnd, nCmdShow);
	UpdateWindow(hwnd);

	WAVEFORMATEX wfx = { 0 };
	wfx.wFormatTag = WAVE_FORMAT_PCM; wfx.nChannels = 1; wfx.nSamplesPerSec = AUDIO_SAMPLE_RATE; wfx.wBitsPerSample = 16;
	wfx.nBlockAlign = (wfx.nChannels * wfx.wBitsPerSample) / 8;
	wfx.nAvgBytesPerSec = wfx.nSamplesPerSec * wfx.nBlockAlign;
	if (waveOutOpen(&hWaveOut, WAVE_MAPPER, &wfx, (DWORD_PTR)WaveOutCallback, 0, CALLBACK_FUNCTION) == MMSYSERR_NOERROR) {
		for (int i = 0; i < 2; i++) {
			audioBuffers[i] = new short[AUDIO_BUF_SIZE];
			memset(audioBuffers[i], 0, AUDIO_BUF_SIZE * sizeof(short));
			waveHeader[i].lpData = (LPSTR)audioBuffers[i];
			waveHeader[i].dwBufferLength = AUDIO_BUF_SIZE * sizeof(short);
			waveHeader[i].dwFlags = 0;
			waveOutPrepareHeader(hWaveOut, &waveHeader[i], sizeof(WAVEHDR));
			waveOutWrite(hWaveOut, &waveHeader[i], sizeof(WAVEHDR));
		}
	}


	MSG msg;
	LARGE_INTEGER frequency;
	LARGE_INTEGER last_hardware_time;
	double internal_cycles_debt = 0.0;

	QueryPerformanceFrequency(&frequency);
	QueryPerformanceCounter(&last_hardware_time);

	const double SYSTEM_CLOCK_HZ = 1780000.0; // Частота ядра Радио-86РК (1.78 МГц)
	double time_since_last_interrupt = 0.0;

	while (emulator_running) {
		// Ожидание системных событий во избежание 100% загрузки процессора ПК
		MsgWaitForMultipleObjectsEx(0, NULL, 1, QS_ALLINPUT, MWMO_INPUTAVAILABLE);

		while (PeekMessageW(&msg, NULL, 0, 0, PM_REMOVE)) {
			if (msg.message == WM_QUIT) {
				emulator_running = false;
				break;
			}

			// --- НАЖАТИЕ КЛАВИШ (WM_KEYDOWN) ---
			if (msg.message == WM_KEYDOWN) {
				if (!(msg.lParam & (1 << 30))) { // Защита от автоповтора Windows
					UINT vk = (UINT)msg.wParam;
					if (vk == VK_CAPITAL) { rk_rus_lat_pressed = true; }
					else if (vk == VK_SHIFT) { rk_cc_pressed = true; }
					else if (vk == VK_CONTROL) { rk_us_pressed = true; }
					else {
						int target_row = -1, target_col = -1;
						if (MapVirtualKeyToRK(vk, target_row, target_col)) {
							key_matrix_state[target_row] &= ~(1 << target_col);
						}
					}
				}
			}

			// --- ОТПУСКАНИЕ КЛАВИШ (WM_KEYUP) ---
			else if (msg.message == WM_KEYUP) {
				UINT vk = (UINT)msg.wParam;
				if (vk == VK_CAPITAL) { rk_rus_lat_pressed = false; }
				else if (vk == VK_SHIFT) { rk_cc_pressed = false; }
				else if (vk == VK_CONTROL) { rk_us_pressed = false; }
				else {
					int target_row = -1, target_col = -1;
					if (MapVirtualKeyToRK(vk, target_row, target_col)) {
						key_matrix_state[target_row] |= (1 << target_col); // Размыкаем контакт
					}
				}
			}

			TranslateMessage(&msg);
			DispatchMessageW(&msg);
		}

		if (!emulator_running) break;

		// --- ДИСПЕТЧЕР И ТАКТОВАЯ СИНХРОНИЗАЦИЯ ЯДРА ---
		LARGE_INTEGER current_hardware_time;
		QueryPerformanceCounter(&current_hardware_time);
		double elapsed_seconds = (double)(current_hardware_time.QuadPart - last_hardware_time.QuadPart) / frequency.QuadPart;

		if (elapsed_seconds > 0.1) elapsed_seconds = 0.1; // Защита от лагов Windows

		if (elapsed_seconds > 0.0) {
			last_hardware_time = current_hardware_time;
			internal_cycles_debt += elapsed_seconds * SYSTEM_CLOCK_HZ; // Накапливаем такты ПК

			int cycles_to_execute = (int)internal_cycles_debt;
			if (cycles_to_execute > 0) {
				while (cycles_to_execute > 0) {
					int elapsed_ticks = cpu.Step();

					cycles_to_execute -= elapsed_ticks;
					internal_cycles_debt -= elapsed_ticks;

					// Накапливаем процессорные такты для генерации звука
					audio_ticks_accumulator += elapsed_ticks;
					while (audio_ticks_accumulator >= TICKS_PER_SAMPLE) {
						audio_ticks_accumulator -= TICKS_PER_SAMPLE;

						// Генерируем сэмпл на основе ТЕКУЩЕГО состояния флага прямо сейчас
						short sample = rk_inte_speaker_state ? 4000 : -4000;

						// Записываем в кольцевой буфер
						int next_write = (inte_ring_write_ptr + 1) % INTE_RING_BUF_SIZE;
						// Защита от переполнения буфера
						if (next_write != inte_ring_read_ptr) {
							inte_ring_buffer[inte_ring_write_ptr] = sample;
							inte_ring_write_ptr = next_write;
						}
					}

					// Отсчитываем такты до кадрового прерывания 50 Гц
					cpu.cycles_until_interrupt -= elapsed_ticks;
					if (cpu.cycles_until_interrupt <= 0) {
						cpu.int_pending = true; // Выставляем запрос на прерывание для процессора
						cpu.cycles_until_interrupt += 35600; // На запуск следующего кадра

						// Синхронное переключение флага VBlank видеоконтроллера ВГ75
						cpu.vgh75_vblank_state = !cpu.vgh75_vblank_state;
						if (cpu.vgh75_vblank_state) {
							cpu.vgh75_status |= 0x20;        // Конец кадра (VRTC)
						}
						else {
							cpu.vgh75_status &= ~0x20;
						}

						// Автоматическое плавное отжатие экранных кнопок GUI (раз в 20 мс)
						if (static_virtual_key_duration > 0) {
							static_virtual_key_duration--;
							if (static_virtual_key_duration == 0) {
								rk_rus_lat_pressed = false;
								rk_cc_pressed = false;
								rk_us_pressed = false;
								for (int i = 0; i < 8; i++) key_matrix_state[i] = 0xFF;
							}
						}

						// Обновляем графику и окна отладки строго 1 раз по завершении кадра
						UpdateRegisterDisplay();
						InvalidateRect(hwnd, NULL, FALSE);
					}
				}
			}
		}

		if (internal_cycles_debt <= 0.0) {
			Sleep(1); // Освобождаем CPU ПК
		}
	}

	// --- Безопасная очистка аудиодескрипторов перед выходом ---
	if (hWaveOut) {
		for (int i = 0; i < 2; i++) {
			waveOutUnprepareHeader(hWaveOut, &waveHeader[i], sizeof(WAVEHDR));
			delete[] audioBuffers[i];
		}
		waveOutClose(hWaveOut);
	}
	return (int)msg.wParam;
}

