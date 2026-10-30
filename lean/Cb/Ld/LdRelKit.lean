-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdRelKit.lean: a round in which a native word of a code (`Cb.LdCode` of Cb/Ld/LdRel.lean) is
sent as an oracle.

Definitions only; common to the blocks beyond unique decoding.

Main names:
  `C.sendRound Plain Chal d`: the prover sends a native word of C as an oracle (a position is a
    native position, a symbol the native symbol there) and a plain part; the verifier answers with
    an element of Chal. Every round has a fixed message of the right format: what is sent where
    there is no honest message, and after a rejection of an earlier part, when the later rounds are
    still played (the fields `dOrc`, `dPlain` of `Round`, Iop/Shape.lean). Here d is the fixed plain
    part (`dPlain`), and the fixed oracle (`dOrc`) is the zero word.
  `C.sendPoint`: the oracle of such a round is a string (`Round.IsPoint`, Iop/Shape.lean) that is
    read symbol by symbol.
A verifier reads such an oracle through the transformation of C: for the long position x it reads
the native positions `C.src x`.

Limits: nothing is proved here.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdRel

set_option autoImplicit false

namespace Cb
open Iop

namespace LdCode
variable {E P : Type} [Zero E] (C : LdCode E P)

/-- A native word sent as an oracle, with a plain part. -/
@[reducible] def sendRound (Plain Chal : Type) [Fintype Chal] [Nonempty Chal] (dPlain : Plain) :
    Round where
  Orc := C.Word
  Pos := C.NP
  Sym := fun p => C.NS p → E
  rd := fun o p => o p
  Plain := Plain
  Chal := Chal
  dOrc := fun _ _ => 0
  dPlain := dPlain

/-- Its oracle is a string. -/
def sendPoint (Plain Chal : Type) [Fintype Chal] [Nonempty Chal] (dPlain : Plain) :
    (C.sendRound Plain Chal dPlain).IsPoint where
  finPos := C.finNP
  decPos := C.decNP
  ofSyms := fun f => f
  rd_ofSyms := fun _ _ => rfl
  ofSyms_rd := fun _ => rfl
  zero := fun _ _ => 0

end LdCode
end Cb
