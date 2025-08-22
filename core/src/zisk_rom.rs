//! Zisk ROM
//!
//! # ROM data
//!
//! The Zisk ROM contains the result of parsing a RISC-V ELF program file data, and then keeping the
//! data that is required to execute any input data against this program using the Zisk processor.
//! This information consists on the following data:
//!
//! ## Zisk instructions
//!
//! * Created by transpiling the RISC-V instructions
//! * Every RISC-V instruction can generate a different number of Zisk instructions: 1 (in most of
//!   the cases), 2, 3 or 4 (e.g. in instruction containing some atomic operations).
//! * For this reason, Zisk instructions addresses are normally spaced 4 units (e.g. 4096, 4100,
//!   4104...) leaving room for up to 3 additional Zisk instructions if needed to fulfill the
//!   original RISC-V instruction they represent.
//! * This way, RISC-V jumps can conveniently be mapped to Zisk jumps by multiplying their relative
//!   offsets by 4.
//! * The Zisk instructions are stored in a map using the pc as the key
//!
//! ## Read-only (RO) data
//!
//! * RISC-V programs can contain some data that is required to execute the program, e.g. constants.
//! * There can be several sections of RO memory-mapped data in the same RISC-V program, so we need
//!   to store a list of them as part of the ROM.
//! * There can be none, one, or several.
//!
//! # Fetching instructions
//!
//! * During the Zisk program execution, the Zisk Emulator must fetch the Zisk instruction
//!   corresponding to the current pc for every execution step.
//! * This fetch can be expensive in terms of computational time if done directly using the map.
//! * For this reason, the original map of instructions is split into 3 different containers that
//!   allow to speed-up the process of finding the Zisk instruction that matches a specific pc
//!   addresss.
//! * The logic of this fetch procedure can be seen in the method `get_instruction()`.  This method
//!   searches for the Zisk instruction in 3 different containers:
//!   * If the address is >= `ROM_ADDR`, there can be 2 cases:
//!     * If the address is alligned to 4 bytes, then get it from the vector `rom_instructions`,
//!       using as index `(pc-ROM_ADDR)/4`
//!     * If the address is not allgined, then get it from the vector `rom_na_instructions`, using
//!       as index `(pc-ROM_ADDR)`
//!   * If the address is < ROM_ADDR, then get it from the vector `rom_entry_instructions`, using as
//!     index `(pc-ROM_ENTRY)/4`
use std::{collections::{BTreeMap, HashMap}, sync::Arc};

use fields::PrimeField64;
use solana_pubkey::Pubkey;
use solana_sbpf::program::SBPFVersion;
use zisk_pil::MainTraceRow;

use crate::{ZiskInst, ZiskInstBuilder, ROM_ADDR, ROM_ENTRY};

use sbpf_elf_parser::ProcessedElf;

const BASE_REG: u64 = 4;
const STORE_REG: u64 = BASE_REG + 12;
const SCRATCH_REG: u64 = STORE_REG + 12;
const TRANSPILE_ALIGN: u64 = 8;

/// Unlike the original is sbpf's instruction translating container 
#[derive(Debug, Clone, Default)]
pub struct ZiskRom {
    pub key: Pubkey,
    pub program: ProcessedElf,
    pub transpiled_instructions: Vec<Vec<ZiskInst>>,
    pub system_instructions: Vec<ZiskInst>
}



/// ZisK ROM implementation
impl ZiskRom {
    fn transpile_op(op: &solana_sbpf::ebpf::Insn, pc: u64, version: &SBPFVersion) -> Vec<ZiskInst> {
        use solana_sbpf::ebpf::*;
        let (width, mask) = if BPF_B & op.opc != 0 {
            (1, (1_u64 << 8) - 1)
        } else if BPF_H & op.opc != 0 {
            (2, (1_u64 << 16) - 1)
        } else if BPF_W & op.opc != 0 {
            (4, (1_u64 << 32) - 1)
        } else if BPF_DW & op.opc != 0 {
            (8, !0_u64)
        } else {
            (8, !0_u64)
        };

        let arith_op =
        if BPF_MUL & op.opc != 0 {
            if BPF_ALU32_LOAD & op.opc != 0 {
                "mul_w"
            } else {
                "mul"
            }
        } else if BPF_ADD & op.opc != 0 {
            if BPF_ALU32_LOAD & op.opc != 0 {
                "add_w"
            } else {
                "add"
            }
        } else if BPF_OR & op.opc != 0 {
            "or"
        } else if BPF_XOR & op.opc != 0 {
            "xor"
        } else if BPF_AND & op.opc != 0 {
            "and"

        } else if BPF_SUB & op.opc != 0 {
            if BPF_ALU32_LOAD & op.opc != 0 {
                "sub_w"
            } else {
                "sub"
            }
        } else if BPF_SDIV & op.opc != 0 {
            if BPF_ALU32_LOAD & op.opc != 0 {
                "div_w"
            } else {
                "div"
            }
        } else if (BPF_DIV & op.opc != 0) || (BPF_UDIV & op.opc != 0) {
            if BPF_ALU32_LOAD & op.opc != 0 {
                "divu_w"
            } else {
                "divu"
            }
        } else if BPF_MOD & op.opc != 0 {
            if BPF_ALU32_LOAD & op.opc != 0 {
                "rem_w"
            } else {
                "rem"
            }
        } else if BPF_UREM & op.opc != 0 {
            if BPF_ALU32_LOAD & op.opc != 0 {
                "remu_w"
            } else {
                "remu"
            }
        } else if BPF_SREM & op.opc != 0 {
            if BPF_ALU32_LOAD & op.opc != 0 {
                "rem_w"
            } else {
                "rem"
            }

        } else if BPF_LSH & op.opc != 0 {
            if BPF_ALU32_LOAD & op.opc != 0 {
                "sll_w"
            } else {
                "sll"
            }
        } else if BPF_RSH & op.opc != 0 {
            if BPF_ALU32_LOAD & op.opc != 0 {
                "srl_w"
            } else {
                "srl"
            }
        } else if BPF_ARSH & op.opc != 0 {
            if BPF_ALU32_LOAD & op.opc != 0 {
                "sra_w"
            } else {
                "sra"
            }
        } else if BPF_LMUL & op.opc != 0 {
            "mulu"
        } else if BPF_SHMUL & op.opc != 0 {
            "shmul"
        } else {
            ""
        };

        match op.opc {
            LD_DW_IMM => vec![
                {
                    let mut builder = ZiskInstBuilder::new(pc);
                    builder.src_b("imm", op.imm as u64, false);
                    builder.store("reg", BASE_REG as i64 + op.dst as i64, false, false);
                    builder.op("copyb");
                    builder.i
                },
            ],

            // BPF opcode: `ldxb dst, [src + off]` /// `dst = (src + off) as u8`.
            // BPF opcode: `ldxh dst, [src + off]` /// `dst = (src + off) as u16`.
            // BPF opcode: `ldxw dst, [src + off]` /// `dst = (src + off) as u32`.
            // BPF opcode: `ldxdw dst, [src + off]` /// `dst = (src + off) as u64`.
            LD_1B_REG | LD_2B_REG | LD_4B_REG | LD_8B_REG | LD_B_REG | LD_H_REG | LD_W_REG | LD_DW_REG => if op.off < 0 {
                vec![
                    {
                        let mut builder = ZiskInstBuilder::new(pc);
                        builder.src_b("reg", BASE_REG + op.src as u64, false);
                        builder.store("reg", SCRATCH_REG as i64, false, false);
                        builder.op("copyb");
                        builder.i
                    },
                    {
                        let mut builder = ZiskInstBuilder::new(pc + 1);
                        builder.src_a("reg", SCRATCH_REG, false);
                        builder.src_b("reg", (-op.off).try_into().unwrap(), false);
                        builder.store("reg", SCRATCH_REG as i64, false, false);
                        builder.op("sub");
                        builder.i
                    },
                    {
                        let mut builder = ZiskInstBuilder::new(pc + 2);
                        builder.src_a("reg", SCRATCH_REG, false);
                        builder.src_b("ind", op.off.try_into().unwrap(), false);
                        builder.store("reg", (BASE_REG + op.dst as u64) as i64, false, false);
                        builder.op("copyb");
                        builder.ind_width(width);
                        builder.i
                    }
                ]
            } else {
                vec![
                    {
                        let mut builder = ZiskInstBuilder::new(pc);
                        builder.src_a("reg", BASE_REG + op.src as u64, false);
                        builder.src_b("ind", op.off.try_into().unwrap(), false);
                        builder.store("reg", (BASE_REG + op.dst as u64) as i64, false, false);
                        builder.op("copyb");
                        builder.ind_width(width);
                        builder.i
                    }
                ]
            },

            // BPF opcode: `stb [dst + off], imm` /// `(dst + offset) as u8 = imm`.
            // BPF opcode: `sth [dst + off], imm` /// `(dst + offset) as u16 = imm`.
            // BPF opcode: `stw [dst + off], imm` /// `(dst + offset) as u32 = imm`.
            // BPF opcode: `stdw [dst + off], imm` /// `(dst + offset) as u64 = imm`.
           ST_1B_IMM | ST_2B_IMM | ST_4B_IMM | ST_8B_IMM | ST_B_IMM | ST_H_IMM | ST_W_IMM | ST_DW_IMM => vec![ 
                {
                    let mut builder = ZiskInstBuilder::new(pc);
                    builder.src_a("reg", BASE_REG + op.src as u64, false);
                    builder.src_b("imm", op.imm as u64, false);
                    builder.store("ind", op.off.into(), false, false);
                    builder.op("copyb");
                    builder.ind_width(width);
                    builder.i
                },
            ],

            // BPF opcode: `stxb [dst + off], src` /// `(dst + offset) as u8 = src`.
            // BPF opcode: `stxh [dst + off], src` /// `(dst + offset) as u16 = src`.
            // BPF opcode: `stxw [dst + off], src` /// `(dst + offset) as u32 = src`.
            // BPF opcode: `stxdw [dst + off], src` /// `(dst + offset) as u64 = src`.
            ST_1B_REG | ST_2B_REG | ST_4B_REG | ST_8B_REG | ST_B_REG | ST_H_REG | ST_W_REG | ST_DW_REG => vec![
                {
                    let mut builder = ZiskInstBuilder::new(pc);
                    builder.src_a("reg", BASE_REG + op.dst as u64, false);
                    builder.src_b("reg", BASE_REG + op.src as u64, false);
                    builder.store("ind", op.off.into(), false, false);
                    builder.op("copyb");
                    builder.ind_width(width);
                    builder.i
                },
            ],

            // BPF opcode: `udiv32 dst, imm` /// `dst /= imm`.
            // BPF opcode: `sdiv32 dst, imm` /// `dst /= imm`.
            // BPF opcode: `div64 dst, imm` /// `dst /= imm`.
            // BPF opcode: `udiv64 dst, imm` /// `dst /= imm`.
            // BPF opcode: `sdiv64 dst, imm` /// `dst /= imm`.
            // BPF opcode: `div32 dst, imm` /// `dst /= imm`.
            // BPF opcode: `mod64 dst, imm` /// `dst %= imm`.
            // BPF opcode: `urem64 dst, imm` /// `dst %= imm`.
            // BPF opcode: `srem64 dst, imm` /// `dst %= imm`.
            // BPF opcode: `urem32 dst, imm` /// `dst %= imm`.
            // BPF opcode: `srem32 dst, imm` /// `dst %= imm`.
            // BPF opcode: `mod32 dst, imm` /// `dst %= imm`.
            // these are equivalent to zisk counterparts because we validate execution via real sbpf
            MOD32_IMM | SREM32_IMM | UREM32_IMM | UREM64_IMM | SREM64_IMM | MOD64_IMM | DIV64_IMM | UDIV64_IMM | SDIV64_IMM | UDIV32_IMM | DIV32_IMM | SDIV32_IMM |
            // BPF opcode: `add32 dst, imm` /// `dst += imm`.
            // BPF opcode: `mul32 dst, imm` /// `dst *= imm`.
            // BPF opcode: `lsh32 dst, imm` /// `dst <<= imm`.
            // BPF opcode: `rsh32 dst, imm` /// `dst >>= imm`.
            // BPF opcode: `arsh32 dst, imm` /// `dst >>= imm (arithmetic)`.
            // BPF opcode: `add64 dst, imm` /// `dst += imm`.
            // BPF opcode: `mul64 dst, imm` /// `dst *= imm`.
            // BPF opcode: `xor64 dst, imm` /// `dst ^= imm`.
            // BPF opcode: `or64 dst, imm` /// `dst |= imm`.
            // BPF opcode: `lsh64 dst, imm` /// `dst <<= imm`.
            // BPF opcode: `rsh64 dst, imm` /// `dst >>= imm`.
            // BPF opcode: `arsh64 dst, imm` /// `dst >>= imm (arithmetic)`.
            // BPF opcode: `lmul64 dst, imm` /// `dst = (dst * imm) as u64`.
            LMUL64_IMM | ARSH64_IMM | LSH64_IMM | RSH64_IMM | OR64_IMM | XOR64_IMM | AND64_IMM | MUL64_IMM | ADD64_IMM | ARSH32_IMM | MUL32_IMM | RSH32_IMM | LSH32_IMM | ADD32_IMM => vec![
                {
                    let mut builder = ZiskInstBuilder::new(pc);
                    builder.src_a("reg", BASE_REG + op.dst as u64, false);
                    builder.src_b("imm", op.imm as u64, false);
                    builder.store("reg", op.dst as i64, false, false);
                    builder.op(arith_op);
                    builder.i
                },
            ],

            // BPF opcode: `div64 dst, src` /// `dst /= src`.
            // BPF opcode: `udiv64 dst, src` /// `dst /= src`.
            // BPF opcode: `sdiv64 dst, src` /// `dst /= src`.
            // BPF opcode: `div32 dst, src` /// `dst /= src`.
            // BPF opcode: `sdiv32 dst, src` /// `dst /= src`.
            // BPF opcode: `udiv32 dst, src` /// `dst /= src`.
            // BPF opcode: `urem32 dst, src` /// `dst %= src`.
            // BPF opcode: `srem32 dst, src` /// `dst %= src`.
            // BPF opcode: `mod32 dst, src` /// `dst %= src`.
            // BPF opcode: `mod64 dst, src` /// `dst %= src`.
            // BPF opcode: `urem64 dst, src` /// `dst %= src`.
            // BPF opcode: `srem64 dst, src` /// `dst %= src`.
            // these are equivalent to zisk counterparts because we validate execution via real sbpf
            MOD64_REG | MOD32_REG | SREM32_REG | UREM32_REG | UDIV32_REG | DIV64_REG | UDIV64_REG | SDIV64_REG | SDIV32_REG | SDIV32_REG |
            // BPF opcode: `add32 dst, src` /// `dst += src`.
            // BPF opcode: `mul32 dst, src` /// `dst *= src`.
            // BPF opcode: `lsh32 dst, src` /// `dst <<= src`.
            // BPF opcode: `rsh32 dst, src` /// `dst >>= src`.
            // BPF opcode: `add64 dst, src` /// `dst += src`.
            // BPF opcode: `and64 dst, imm` /// `dst &= imm`.
            // BPF opcode: `mul64 dst, src` /// `dst *= src`.
            // BPF opcode: `and64 dst, src` /// `dst &= src`.
            // BPF opcode: `xor64 dst, src` /// `dst ^= src`.
            // BPF opcode: `or64 dst, src` /// `dst |= src`.
            // BPF opcode: `lsh64 dst, src` /// `dst <<= src`.
            // BPF opcode: `rsh64 dst, src` /// `dst >>= src`.
            // BPF opcode: `arsh32 dst, src` /// `dst >>= src (arithmetic)`.
            // BPF opcode: `arsh64 dst, src` /// `dst >>= src (arithmetic)`.
            // BPF opcode: `sub64 dst, src` /// `dst -= src`.
            // BPF opcode: `sub32 dst, src` /// `dst -= src`.
            // BPF opcode: `lmul64 dst, src` /// `dst = (dst * src) as u64`.
            LMUL64_REG | SUB32_REG | SUB64_REG | ARSH64_REG | UREM64_REG | SREM64_REG | LSH64_REG | RSH64_REG | OR64_REG | XOR64_REG
                | AND64_REG | MUL64_REG | ADD64_REG | ARSH32_REG | LSH32_REG | RSH32_REG
                | MUL32_REG | DIV32_REG | ADD32_REG => vec![
                {
                    let mut builder = ZiskInstBuilder::new(pc);
                    builder.src_a("reg", BASE_REG + op.dst as u64, false);
                    builder.src_b("reg", BASE_REG + op.src as u64, false);
                    builder.store("reg", op.dst as i64, false, false);
                    builder.op(arith_op);
                    builder.i
                },
            ],

            // BPF opcode: `sub64 dst, imm` /// `dst -= imm`.
            // BPF opcode: `sub32 dst, imm` /// `dst = imm - dst`.
            SUB32_IMM | SUB64_IMM => if version.swap_sub_reg_imm_operands() {
                // self.reg[dst] =  (insn.imm as u64).wrapping_sub(self.reg[dst])
                vec![
                    {
                        let mut builder = ZiskInstBuilder::new(pc);
                        builder.src_a("imm", op.imm as u64, false);
                        builder.src_b("reg", BASE_REG + op.dst as u64, false);
                        builder.store("reg", op.dst as i64, false, false);
                        builder.op(arith_op);
                        builder.i
                    },
                ]
            } else {
                // self.reg[dst] =  self.reg[dst].wrapping_sub(insn.imm as u64)
                vec![
                    {
                        let mut builder = ZiskInstBuilder::new(pc);
                        builder.src_a("reg", BASE_REG + op.dst as u64, false);
                        builder.src_b("imm", op.imm as u64, false);
                        builder.store("reg", op.dst as i64, false, false);
                        builder.op(arith_op);
                        builder.i
                    },
                ]
            },

            // BPF opcode: `xor32 dst, src` /// `dst ^= src`.
            // BPF opcode: `or32 dst, src` /// `dst |= src`.
            // BPF opcode: `and32 dst, src` /// `dst &= src`.
            // BPF opcode: `lmul32 dst, src` /// `dst *= (dst * src) as u32`.
            LMUL32_REG | OR32_REG | XOR32_REG | AND32_REG => vec![
                {
                    let mut builder = ZiskInstBuilder::new(pc);
                    builder.src_a("imm", mask, false);
                    builder.src_b("reg", BASE_REG + op.src as u64, false);
                    builder.op("and");
                    builder.i
                },
                {
                    let mut builder = ZiskInstBuilder::new(pc + 1);
                    builder.src_a("imm", mask, false);
                    builder.src_b("reg", BASE_REG + op.dst as u64, false);
                    builder.op("and");
                    builder.i
                },
                {
                    let mut builder = ZiskInstBuilder::new(pc + 2);
                    builder.src_a("reg", BASE_REG + op.dst as u64, false);
                    builder.src_b("reg", BASE_REG + op.src as u64, false);
                    builder.store("reg", op.dst as i64, false, false);
                    builder.op(arith_op);
                    builder.i
                },
                {
                    let mut builder = ZiskInstBuilder::new(pc + 3);
                    builder.src_a("reg", BASE_REG + op.dst as u64, false);
                    builder.src_b("imm", mask, false);
                    builder.store("reg", op.dst as i64, false, false);
                    builder.op("and");
                    builder.i
                }
            ],

            // BPF opcode: `or32 dst, imm` /// `dst |= imm`.
            // BPF opcode: `and32 dst, imm` /// `dst &= imm`.
            // BPF opcode: `xor32 dst, imm` /// `dst ^= imm`.
            // BPF opcode: `lmul32 dst, imm` /// `dst *= (dst * imm) as u32`.
            LMUL32_IMM | XOR32_IMM | AND32_IMM | OR32_IMM => vec![
                {
                    let mut builder = ZiskInstBuilder::new(pc);
                    builder.src_a("imm", mask, false);
                    builder.src_b("reg", BASE_REG + op.dst as u64, false);
                    builder.op("and");
                    builder.i
                },
                {
                    let mut builder = ZiskInstBuilder::new(pc + 1);
                    builder.src_a("imm", op.imm as u64 & mask, false);
                    builder.src_b("reg", BASE_REG + op.src as u64, false);
                    builder.store("reg", op.dst as i64, false, false);
                    builder.op(arith_op);
                    builder.i
                },
                {
                    let mut builder = ZiskInstBuilder::new(pc + 2);
                    builder.src_a("reg", BASE_REG + op.dst as u64, false);
                    builder.src_b("imm", mask, false);
                    builder.store("reg", op.dst as i64, false, false);
                    builder.op("and");
                    builder.i
                }
            ],

            // BPF opcode: `uhmul64 dst, src` /// `dst = (dst * src) >> 64`.
            // BPF opcode: `shmul64 dst, src` /// `dst = (dst * src) >> 64`.
            UHMUL64_REG | SHMUL64_REG => vec![
            ],

            // BPF opcode: `uhmul64 dst, imm` /// `dst = (dst * imm) >> 64`.
            // BPF opcode: `shmul64 dst, imm` /// `dst = (dst * imm) >> 64`.
            UHMUL64_IMM | SHMUL64_IMM => vec![
            ],

            // BPF opcode: `hor64 dst, imm` /// `dst |= imm << 32`.
            HOR64_IMM => vec![],

            /// BPF opcode: `shmul32 dst, imm` /// `dst = (dst * imm) as i64`.
            // SHMUL32_IMM
            /// BPF opcode: `shmul32 dst, src` /// `dst = (dst * src) as i64`.
            // SHMUL32_REG

            // BPF opcode: `mov64 dst, src` /// `dst = src`.
            MOV64_REG
            // BPF opcode: `mov64 dst, imm` /// `dst = imm`.
            MOV64_IMM
            // BPF opcode: `mov32 dst, imm` /// `dst = imm`.
            MOV32_IMM
            // BPF opcode: `mov32 dst, src` /// `dst = src`.
            MOV32_REG
            // BPF opcode: `neg32 dst` /// `dst = -dst`.
            NEG32

            // BPF opcode: `le dst` /// `dst = htole<imm>(dst), with imm in {16, 32, 64}`.
            LE
            // BPF opcode: `be dst` /// `dst = htobe<imm>(dst), with imm in {16, 32, 64}`.
            BE
            // BPF opcode: `neg64 dst` /// `dst = -dst`.
            NEG64

            // BPF opcode: `ja +off` /// `PC += off`.
            JA
            // BPF opcode: `jeq dst, imm, +off` /// `PC += off if dst == imm`.
            JEQ_IMM
            // BPF opcode: `jeq dst, src, +off` /// `PC += off if dst == src`.
            JEQ_REG
            // BPF opcode: `jgt dst, imm, +off` /// `PC += off if dst > imm`.
            JGT_IMM
            // BPF opcode: `jgt dst, src, +off` /// `PC += off if dst > src`.
            JGT_REG
            // BPF opcode: `jge dst, imm, +off` /// `PC += off if dst >= imm`.
            JGE_IMM
            // BPF opcode: `jge dst, src, +off` /// `PC += off if dst >= src`.
            JGE_REG
            // BPF opcode: `jlt dst, imm, +off` /// `PC += off if dst < imm`.
            JLT_IMM
            // BPF opcode: `jlt dst, src, +off` /// `PC += off if dst < src`.
            JLT_REG
            // BPF opcode: `jle dst, imm, +off` /// `PC += off if dst <= imm`.
            JLE_IMM
            // BPF opcode: `jle dst, src, +off` /// `PC += off if dst <= src`.
            JLE_REG
            // BPF opcode: `jset dst, imm, +off` /// `PC += off if dst & imm`.
            JSET_IMM
            // BPF opcode: `jset dst, src, +off` /// `PC += off if dst & src`.
            JSET_REG
            // BPF opcode: `jne dst, imm, +off` /// `PC += off if dst != imm`.
            JNE_IMM
            // BPF opcode: `jne dst, src, +off` /// `PC += off if dst != src`.
            JNE_REG
            // BPF opcode: `jsgt dst, imm, +off` /// `PC += off if dst > imm (signed)`.
            JSGT_IMM
            // BPF opcode: `jsgt dst, src, +off` /// `PC += off if dst > src (signed)`.
            JSGT_REG
            // BPF opcode: `jsge dst, imm, +off` /// `PC += off if dst >= imm (signed)`.
            JSGE_IMM
            // BPF opcode: `jsge dst, src, +off` /// `PC += off if dst >= src (signed)`.
            JSGE_REG
            // BPF opcode: `jslt dst, imm, +off` /// `PC += off if dst < imm (signed)`.
            JSLT_IMM
            // BPF opcode: `jslt dst, src, +off` /// `PC += off if dst < src (signed)`.
            JSLT_REG
            // BPF opcode: `jsle dst, imm, +off` /// `PC += off if dst <= imm (signed)`.
            JSLE_IMM
            // BPF opcode: `jsle dst, src, +off` /// `PC += off if dst <= src (signed)`.
            JSLE_REG

            // BPF opcode: `call imm` /// syscall function call to syscall with key `imm`.
            CALL_IMM
            // BPF opcode: tail call.
            CALL_REG
            // BPF opcode: `exit` /// `return r0`. /// Valid only until SBPFv3
            EXIT
            // BPF opcode: `return` /// `return r0`. /// Valid only since SBPFv3
            RETURN
            // BPF opcode: `syscall` /// `syscall imm`. /// Valid only since SBPFv3
            SYSCALL
            _ => vec![]
        }
    }

    pub fn new(key: Pubkey, program: ProcessedElf) -> Self {
        let transpiled_instructions = program.all_lines.as_slice().iter().map(|op| Self::transpile_op(op, op.ptr as u64 * TRANSPILE_ALIGN, &program.sbpf_version)).collect();
        Self {
            key,
            program,
            transpiled_instructions,
            system_instructions: vec![]
        }
    }

    ///// Gets the ROM instruction corresponding to the provided pc address.
    ///// Depending on the range and allignment of the address, the function searches for it in the
    ///// corresponding vector.
    //#[inline(always)]
    pub fn get_instruction(&self, pc: u64) -> &ZiskInst {
        //TODO: bios/syscall code

        // If the address is a program address...
        if pc >= ROM_ADDR {
            let line = (pc - ROM_ADDR) / TRANSPILE_ALIGN;
            let index = (pc - ROM_ADDR) % TRANSPILE_ALIGN;

            &self.transpiled_instructions[line as usize][index as usize]
        } else if pc >= ROM_ENTRY {
            // pc is in the ROM_ENTRY range (always alligned)
            &self.system_instructions[(pc - ROM_ENTRY) as usize]
        } else {
            panic!("ZiskRom::get_instruction() pc={pc} is out of range");
        }
    }

    /// Saves ZisK rom into an i86-64 assembly data string
    pub fn build_constant_trace<F: PrimeField64>(&self) -> Vec<MainTraceRow<F>> {
        let mut inss = 0;
        for _ in self.transpiled_instructions.as_slice() {
            inss += self.transpiled_instructions.len() 
        }
        inss += self.system_instructions.len();

        let mut result: Vec<MainTraceRow<F>> = Vec::with_capacity(inss);
        #[allow(clippy::uninit_vec)]
        unsafe {
            result.set_len(inss)
        };

        let mut ix = 0;
        for ref system_instruction in self.system_instructions.as_slice() {
            system_instruction.write_constant_trace(result.get_mut(ix).unwrap());
        }

        for line in self.transpiled_instructions.as_slice() {
            for insn in line {
                insn.write_constant_trace(result.get_mut(ix).unwrap());
                ix += 1;
            }
        }

        result
    }
}
