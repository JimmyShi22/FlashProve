-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/CarryAnyW.lean: the code switch: THE READING LAW OF THE SENTENCE «carry»,
closed (`carryAtZ`: CarryClosed.lean), IN ITS LAST LETTER: the sentence does not read the witness
at all: what it says (`carryAtZ_iff`) names the typed entry, the way in, the state and the strings
alone. So it rides over every change of the witness, whatever that change leaves alone.

Main names:
  `carryAtZ_anyW`: at two witnesses, of whatever two types, the sentence is one.
  `carryAtZ_reads`: the form in which a table of riders asks it: under ANY premise on the two
    witnesses (a letter `_h : Q`, not read) the sentence goes from the one to the other.
Limits. It says nothing on the strings or the state: these the sentence does read. Nothing on
soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.CarryClosed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller

/-- **The sentence does not read the witness.** -/
theorem carryAtZ_anyW {P W W' : Type} (Z : ProofFile.Pub) (lay : ByteArray) (m : ℕ)
    (a : P × VerifiableInference.Desc.First.S) (y : Strs) (w : W) (w' : W') :
    carryAtZ Z lay m a y w ↔ carryAtZ Z lay m a y w' :=
  (carryAtZ_iff Z lay m a y w).trans (carryAtZ_iff Z lay m a y w').symm

/-- **Its reading law**, under whatever premise Q on the two witnesses a table asks. -/
theorem carryAtZ_reads {P W : Type} {Q : Prop} (Z : ProofFile.Pub) (lay : ByteArray) (m : ℕ)
    (a : P × VerifiableInference.Desc.First.S) (y : Strs) (w w' : W) (_h : Q) :
    carryAtZ Z lay m a y w → carryAtZ Z lay m a y w' :=
  (carryAtZ_anyW Z lay m a y w w').1

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.carryAtZ_anyW
#print axioms VerifiableInference.Desc.First.K2Caller.carryAtZ_reads
