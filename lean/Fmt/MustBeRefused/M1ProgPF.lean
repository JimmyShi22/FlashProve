-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/MustBeRefused/M1ProgPF.lean: 9 false proofs of the first toy (a product test), each with its
expected refusal.

Every proof in this list is false and must be refused. A verifier that accepts one is broken. They
are test data of a toy: made-up data only, no model and no weights. Each was made by the toy's own
prover, in the programs (the C++ implementation that comes with this Lean code), with one block
cheating in the named way and all others going on honestly. These files are test fixtures: proofs
that every verifier must refuse. Test data: every file here is false, or breaks a rule of the
protocol, and must be refused.

The first toy is a test protocol for the claim that three rows a, b, c of one oracle message have
a_i b_i = c_i for every i (the heads of Fmt/M1Types.lean and Fmt/M1Psc.lean). A block is one step of
that protocol. The head of Fmt/M1Dec.lean names blocks of this toy: PSC is the sum-check, CS the
code switch, BASE the last block. FOLD is a sum-check that folds a linear claim (Fmt/M1Fold.lean).
In SEND the verifier samples a sent oracle message at a drawn point, and the prover answers with one
element (Fmt/M1Send.lean). ENGINE, in the names cheat-ENGINE_FAR_WORD-0, cheat-ENGINE_FAR_WORD-1 and
cheat-ENGINE_FAR_WORD-2, is none of the blocks that the head of Fmt/M1Dec.lean names, and this head
does not say what it is.

Sources. Made by a program from the files as they came. No Mathlib is imported. "cheat-X" is
FALSE-PROOFS-every-verifier-must-refuse/product/full/product.cheat-X.proof of the programs' archive
of files (sha256 f97d6774317660e9033841ab36ce4e63e376ebeb25542cf6f1f92e8f61644aa1; the archive is
not in this repository): the run at full parameters (the toy at its real target). The false proofs'
parameters are those of the honest run (Fmt/M1ProgPFFiles.lean).

1. What the file contains.
   The bytes are in Fmt/MustBeRefused/M1ProgPFa.lean to M1ProgPFi.lean, one proof to a file; this
   file imports them.
   mustBeRefused          Name, bytes, and the expected refusal: the part of the check at which the
                          proof was expected to fail, by the programs' own list of expectations,
                          written before the proof was made. The parts are: 1 the form of the file,
                          2 the proof of work, 3 the Merkle openings, 4 the last block's linear
                          check, 5 the last block's checks at the opened positions. This list has
                          only 4 and 5.

2. What is checked when the file compiles. Every size; for every file the format's hash under the
   number 168, against a value that the format page's own reference program (format_rules.py)
   computed from the archive's file, at a moment when that file's sha256 agreed with the archive's
   list of sums.

3. Theorems. No theorem in this file. A test (#guard) is an evaluation made while the file compiles;
   the compile fails if the result moves; it leaves no theorem.

4. What is not claimed. Nothing is said here about what any verifier in Lean answers on them; see
   Fmt/M1FullProgPFc.lean, Fmt/M1FullProgPFd.lean, Run/PlanQSFProgPFe.lean to
   Run/PlanQSFProgPFh.lean, Run/M1EngineOneF*.lean and Run/M1EngineTypedF*.lean.

Notation: `HF`: a hash (Fmt/Rules5Fast.lean); its arguments, in order: number, tree, index, start,
bytes; `zero32`: 32 zero bytes; `hex`: bytes as a string of base 16 (both: Fmt/Rules1.lean).

Terms: lean/GLOSSARY.md.
-/
import Fmt.MustBeRefused.M1ProgPFa
import Fmt.MustBeRefused.M1ProgPFb
import Fmt.MustBeRefused.M1ProgPFc
import Fmt.MustBeRefused.M1ProgPFd
import Fmt.MustBeRefused.M1ProgPFe
import Fmt.MustBeRefused.M1ProgPFf
import Fmt.MustBeRefused.M1ProgPFg
import Fmt.MustBeRefused.M1ProgPFh
import Fmt.MustBeRefused.M1ProgPFi

namespace Fmt
namespace M1
namespace ProgPF

/-- Every one must be refused; the expected part beside it. -/
def mustBeRefused : List (String × ByteArray × Nat) :=
  [("cheat-BASE_WRONG_WORD", f_cheat_BASE_WRONG_WORD, 5),
    ("cheat-CS_OTHER_MESSAGE-0", f_cheat_CS_OTHER_MESSAGE_0, 4),
    ("cheat-CS_OTHER_MESSAGE-1", f_cheat_CS_OTHER_MESSAGE_1, 4),
    ("cheat-ENGINE_FAR_WORD-0", f_cheat_ENGINE_FAR_WORD_0, 4),
    ("cheat-ENGINE_FAR_WORD-1", f_cheat_ENGINE_FAR_WORD_1, 4),
    ("cheat-ENGINE_FAR_WORD-2", f_cheat_ENGINE_FAR_WORD_2, 5),
    ("cheat-FOLD_OTHER_ROWS", f_cheat_FOLD_OTHER_ROWS, 4),
    ("cheat-PSC_FALSE_TARGET", f_cheat_PSC_FALSE_TARGET, 4),
    ("cheat-SEND_WRONG_ANSWER", f_cheat_SEND_WRONG_ANSWER, 4)]

#guard mustBeRefused.map (fun x => x.2.1.size) = [160904, 161888, 160664, 161664, 162400, 160232, 159888, 160128, 160992]
#guard mustBeRefused.map (fun x => hex (HF 168 0 0 zero32 x.2.1)) = [
  "dcebd040d0cc8bc1fc9adee7932841f7d2782a78f6e8c98aa236f4cb61fdf361",
  "f3564211d44b38a8d04573f33b258d144df29ee69c7c92c4f42ff6cb40d51a43",
  "d8b744a9e96df481aab58f560de62ed9a1857c3e2164f5cb9fac6f3025ec94ef",
  "d185900dea06b9bfcb95178c64e1986ef762d5b71e571631938bc889a6a097c7",
  "80322f5aa100a4b59e2aab3ead83fce5c550ea60db007d3d8d155b598f8f4569",
  "ad34136ffe5b824ef10b55cebafdaa680ba9ed4189994e3a02b39ca04bab9373",
  "fc40f2b1fa9cde110e22b83cc0bc9b483283ee2ad31381d6ee43cdbe52c51938",
  "a6a5886f925714bac00bba6ea72d8d2db33ba5438e93b8706987eaa2274cc045",
  "378f73a856f8ecdea3c6811c23605f115fe867858c0385d97bfb5c7d81adea19"]

end ProgPF
end M1
end Fmt
