/*
+--------------------------------------------------------------------------+
| CHStone : a suite of benchmark programs for C-based High-Level Synthesis |
| ======================================================================== |
|                                                                          |
| * Collected and Modified : Y. Hara, H. Tomiyama, S. Honda,               |
|                            H. Takada and K. Ishii                        |
|                            Nagoya University, Japan                      |
|                                                                          |
| * Remark :                                                               |
|    1. This source code is modified to unify the formats of the benchmark |
|       programs in CHStone.                                               |
|    2. Test vectors are added for CHStone.                                |
|    3. If "main_result" is 0 at the end of the program, the program is    |
|       correctly executed.                                                |
|    4. Please follow the copyright of each benchmark program.             |
+--------------------------------------------------------------------------+
*/
/*
 * Copyright (C) 2008
 * Y. Hara, H. Tomiyama, S. Honda, H. Takada and K. Ishii
 * Nagoya University, Japan
 * All rights reserved.
 *
 * Disclaimer of Warranty
 *
 * These software programs are available to the user without any license fee or
 * royalty on an "as is" basis. The authors disclaims any and all warranties, 
 * whether express, implied, or statuary, including any implied warranties or 
 * merchantability or of fitness for a particular purpose. In no event shall the
 * copyright-holder be liable for any incidental, punitive, or consequential damages
 * of any kind whatsoever arising from the use of these programs. This disclaimer
 * of warranty extends to the user of these programs and user's customers, employees,
 * agents, transferees, successors, and assigns.
 *
 */

/*
+--------------------------------------------------------------------------+
| CHStone : a suite of benchmark programs for C-based High-Level Synthesis |
| ======================================================================== |
|                                                                          |
| * Collected and Modified : Y. Hara, H. Tomiyama, S. Honda,               |
|                            H. Takada and K. Ishii                        |
|                            Nagoya University, Japan                      |
|                                                                          |
| * Remark :                                                               |
|    1. This source code is modified to unify the formats of the benchmark |
|       programs in CHStone.                                               |
|    2. Test vectors are added for CHStone.                                |
|    3. If "main_result" is 0 at the end of the program, the program is    |
|       correctly executed.                                                |
|    4. Please follow the copyright of each benchmark program.             |
+--------------------------------------------------------------------------+
*/
/*
 * Copyright (C) 2008
 * Y. Hara, H. Tomiyama, S. Honda, H. Takada and K. Ishii
 * Nagoya University, Japan
 * All rights reserved.
 *
 * Disclaimer of Warranty
 *
 * These software programs are available to the user without any license fee or
 * royalty on an "as is" basis. The authors disclaims any and all warranties,
 * whether express, implied, or statuary, including any implied warranties or
 * merchantability or of fitness for a particular purpose. In no event shall the
 * copyright-holder be liable for any incidental, punitive, or consequential damages
 * of any kind whatsoever arising from the use of these programs. This disclaimer
 * of warranty extends to the user of these programs and user's customers, employees,
 * agents, transferees, successors, and assigns.
 *
 */
#define R 0

#define ADDU 33
#define SUBU 35

#define MULT 24
#define MULTU 25

#define MFHI 16
#define MFLO 18

#define AND 36
#define OR 37
#define XOR 38
#define SLL 0
#define SRL 2
#define SLLV 4
#define SRLV 6

#define SLT 42
#define SLTU 43

#define JR 8

#define J 2
#define JAL 3

#define ADDIU 9
#define ANDI 12
#define ORI 13
#define XORI 14

#define LW 35
#define SW 43
#define LUI 15

#define BEQ 4
#define BNE 5
#define BGEZ 1

#define SLTI 10
#define SLTIU 11

/*
+--------------------------------------------------------------------------+
| * Test Vectors (added for CHStone)                                       |
|     A : input data                                                       |
|     outData : expected output data                                       |
+--------------------------------------------------------------------------+
*/
#define IADDR(x)	(((x)&0x000000ff)>>2)
#define DADDR(x)	(((x)&0x000000ff)>>2)

int
main ()
{
  const unsigned int imem[44] = {
    0x8fa40000,			// [0x00400000]  lw $4, 0($29)                   ; 175: lw $a0 0($sp)               # argc
    0x27a50004,			// [0x00400004]  addiu $5, $29, 4                ; 176: addiu $a1 $sp 4             # argv
    0x24a60004,			// [0x00400008]  addiu $6, $5, 4                 ; 177: addiu $a2 $a1 4             # envp
    0x00041080,			// [0x0040000c]  sll $2, $4, 2                   ; 178: sll $v0 $a0 2
    0x00c23021,			// [0x00400010]  addu $6, $6, $2                 ; 179: addu $a2 $a2 $v0
    0x0c100016,			// [0x00400014]  jal 0x00400058 [main]           ; 180: jal main
    0x00000000,			// [0x00400018]  nop                             ; 181: nop
    0x3402000a,			// [0x0040001c]  ori $2, $0, 10                  ; 183: li $v0 10
    0x0000000c,			// [0x00400020]  syscall                         ; 184: syscall                     # syscall 10 (exit)
    0x3c011001,			// [0x00400024]  lui $1, 4097 [A]                ; 4: la   $t0,A           ; C&S
    0x34280000,			// [0x00400028]  ori $8, $1, 0 [A]
    0x00044880,			// [0x0040002c]  sll $9, $4, 2                   ; 5: sll  $t1,$a0,2
    0x01094821,			// [0x00400030]  addu $9, $8, $9                 ; 6: addu $t1,$t0,$t1
    0x8d2a0000,			// [0x00400034]  lw $10, 0($9)                   ; 7: lw   $t2,($t1)
    0x00055880,			// [0x00400038]  sll $11, $5, 2                  ; 8: sll  $t3,$a1,2
    0x010b5821,			// [0x0040003c]  addu $11, $8, $11               ; 9: addu $t3,$t0,$t3
    0x8d6c0000,			// [0x00400040]  lw $12, 0($11)                  ; 10: lw   $t4,($t3)
    0x018a682a,			// [0x00400044]  slt $13, $12, $10               ; 11: slt  $t5,$t4,$t2
    0x11a00003,			// [0x00400048]  beq $13, $0, 12 [L1-0x00400048] ; 12: beq  $t5,$zero,L1
    0xad2c0000,			// [0x0040004c]  sw $12, 0($9)                   ; 13: sw   $t4,($t1)
    0xad6a0000,			// [0x00400050]  sw $10, 0($11)                  ; 14: sw   $t2,($t3)
    0x03e00008,			// [0x00400054]  jr $31                          ; 15: jr   $ra            ; L1
    0x27bdfff4,			// [0x00400058]  addiu $29, $29, -12             ; 17: addiu $sp,$sp,-12   ; main
    0xafbf0008,			// [0x0040005c]  sw $31, 8($29)                  ; 18: sw   $ra,8($sp)
    0xafb10004,			// [0x00400060]  sw $17, 4($29)                  ; 19: sw   $s1,4($sp)
    0xafb00000,			// [0x00400064]  sw $16, 0($29)                  ; 20: sw   $s0,0($sp)
    0x24100000,			// [0x00400068]  addiu $16, $0, 0                ; 21: addiu $s0,$zero,0
    0x2a080008,			// [0x0040006c]  slti $8, $16, 8                 ; 22: slti $t0,$s0,8      ; L5
    0x1100000b,			// [0x00400070]  beq $8, $0, 44 [L2-0x00400070]  ; 23: beq  $t0,$zero,L2
    0x26110001,			// [0x00400074]  addiu $17, $16, 1               ; 24: addiu $s1,$s0,1
    0x2a280008,			// [0x00400078]  slti $8, $17, 8                 ; 25: slti $t0,$s1,8      ; L4
    0x11000006,			// [0x0040007c]  beq $8, $0, 24 [L3-0x0040007c]  ; 26: beq  $t0,$zero,L3
    0x26040000,			// [0x00400080]  addiu $4, $16, 0                ; 27: addiu $a0,$s0,0
    0x26250000,			// [0x00400084]  addiu $5, $17, 0                ; 28: addiu $a1,$s1,0
    0x0c100009,			// [0x00400088]  jal 0x00400024 [compare_swap]   ; 29: jal  compare_swap
    0x26310001,			// [0x0040008c]  addiu $17, $17, 1               ; 30: addiu $s1,$s1,1
    0x0810001e,			// [0x00400090]  j 0x00400078 [L4]               ; 31: j    L4
    0x26100001,			// [0x00400094]  addiu $16, $16, 1               ; 32: addiu $s0,$s0,1     ; L3
    0x0810001b,			// [0x00400098]  j 0x0040006c [L5]               ; 33: j    L5
    0x8fbf0008,			// [0x0040009c]  lw $31, 8($29)                  ; 34: lw   $ra,8($sp)     ; L2
    0x8fb10004,			// [0x004000a0]  lw $17, 4($29)                  ; 35: lw   $s1,4($sp)
    0x8fb00000,			// [0x004000a4]  lw $16, 0($29)                  ; 36: lw   $s0,0($sp)
    0x27bd000c,			// [0x004000a8]  addiu $29, $29, 12              ; 37: addiu $sp,$sp,12
    0x03e00008,			// [0x004000ac]  jr $31                          ; 38: jr   $ra
  };

  const int A[8] = { 22, 5, -9, 3, -17, 38, 0, 11 };
  const int outData[8] = { -17, -9, 0, 3, 5, 11, 22, 38 };

  int main_result;

  int hilo;
  int reg[32];
  int Hi = 0;
  int Lo = 0;
  int pc = 0;
  int dmem[64];
  int j;

  unsigned int ins;
  int op;
  int rs;
  int rt;
  int rd;
  int shamt;
  int funct;
  int address;
  int tgtadr;

  while (1)
  {
    int i;
    int n_inst;

    n_inst = 0;
    main_result = 0;

    for (i = 0; i < 32; i++)
    {
      reg[i] = 0;
    }
    reg[29] = 0x7fffeffc;

    for (i = 0; i < 8; i++)
    {
      dmem[i] = A[i];
    }

    pc = 0x00400000;

    do
    {
      ins = imem[IADDR (pc)];
      pc = pc + 4;

      op = ins >> 26;

      switch (op)
      {
        case R:
          funct = ins & 0x3f;
          shamt = (ins >> 6) & 0x1f;
          rd = (ins >> 11) & 0x1f;
          rt = (ins >> 16) & 0x1f;
          rs = (ins >> 21) & 0x1f;

          switch (funct)
          {

            case ADDU:
              reg[rd] = reg[rs] + reg[rt];
              break;
            case SUBU:
              reg[rd] = reg[rs] - reg[rt];
              break;
              /*
                 case MULT:
                 hilo = (long long) reg[rs] * (long long) reg[rt];
                 Lo = hilo & 0x00000000ffffffffULL;
                 Hi = ((int) (hilo >> 32)) & 0xffffffffUL;
                 break;
                 case MULTU:
                 hilo =
                 (unsigned long long) ((unsigned int) (reg[rs])) *
                 (unsigned long long) ((unsigned int) (reg[rt]));
                 Lo = hilo & 0x00000000ffffffffULL;
                 Hi = ((int) (hilo >> 32)) & 0xffffffffUL;
                 break;
               */
            case MFHI:
              reg[rd] = Hi;
              break;
            case MFLO:
              reg[rd] = Lo;
              break;

            case AND:
              reg[rd] = reg[rs] & reg[rt];
              break;
            case OR:
              reg[rd] = reg[rs] | reg[rt];
              break;
            case XOR:
              reg[rd] = reg[rs] ^ reg[rt];
              break;
            case SLL:
              reg[rd] = reg[rt] << shamt;
              break;
            case SRL:
              reg[rd] = reg[rt] >> shamt;
              break;
            case SLLV:
              reg[rd] = reg[rt] << reg[rs];
              break;
            case SRLV:
              reg[rd] = reg[rt] >> reg[rs];
              break;

            case SLT:
              reg[rd] = reg[rs] < reg[rt];
              break;
            case SLTU:
              reg[rd] = (unsigned int) reg[rs] < (unsigned int) reg[rt];
              break;

            case JR:
              pc = reg[rs];
              break;
            default:
              pc = 0;	// error
              break;
          }
          break;

        case J:
          tgtadr = ins & 0x3ffffff;
          pc = tgtadr << 2;
          break;
        case JAL:
          tgtadr = ins & 0x3ffffff;
          reg[31] = pc;
          pc = tgtadr << 2;
          break;

        default:

          address = ins & 0xffff;
          rt = (ins >> 16) & 0x1f;
          rs = (ins >> 21) & 0x1f;
          switch (op)
          {
            case ADDIU:
              reg[rt] = reg[rs] + address;
              break;

            case ANDI:
              reg[rt] = reg[rs] & (unsigned ) address;
              break;
            case ORI:
              reg[rt] = reg[rs] | (unsigned ) address;
              break;
            case XORI:
              reg[rt] = reg[rs] ^ (unsigned ) address;
              break;

            case LW:
              reg[rt] = dmem[DADDR (reg[rs] + address)];
              break;
            case SW:
              dmem[DADDR (reg[rs] + address)] = reg[rt];
              break;

            case LUI:
              reg[rt] = address << 16;
              break;

            case BEQ:
              if (reg[rs] == reg[rt])
                pc = pc - 4 + (address << 2);
              break;
            case BNE:
              if (reg[rs] != reg[rt])
                pc = pc - 4 + (address << 2);
              break;
            case BGEZ:
              if (reg[rs] >= 0)
                pc = pc - 4 + (address << 2);
              break;

            case SLTI:
              reg[rt] = reg[rs] < address;
              break;

            case SLTIU:
              reg[rt] = (unsigned int) reg[rs] < (unsigned int) address;
              break;

            default:
              pc = 0;	/* error */
              break;
          }
          break;
      }
      reg[0] = 0;
      n_inst = n_inst + 1;
    }
    while (pc != 0);

    main_result += (n_inst != 611);
    for (j = 0; j < 8; j++)
    {
      main_result += (dmem[j] == outData[j]);
    }

    return main_result;
  }
}
