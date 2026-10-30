-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Meant.lean: the three free linear claims of the closed parameters
(Att/K05Closed.lean: Lin's LM, LD,
LE) at their meant value: the library's LMat, LDat, LEat (Cb/Pv/Att/End/Hid.lean: the hidden value
of each scalar that one
claim ties to a table is its rule value; for the third also the join on the hidden values).

Main names:
  `meantLin`: the two readings of a given Lin, with the three claims set so. LMat, LDat, LEat read
    none of the three
    letters themselves, so there is no circle. `meantQ`: the join's letters at these parameters.
  `meant_LM`, `meant_LD`, `meant_LE`: the last three fields of the library's Fits (End/Cl.lean) hold
    there, by unfolding.

The letters hang on the ledger's number of slots and on the slots' numbers: the places of the
scalars' mask entries.
The lookup's letters in the join stay a letter.
Nothing is claimed on soundness, completeness or hiding.

-/
import Cb.Pv.Att.End.Hid
import Johnson.Desc.First.Att.K05Closed

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Cb.Pv.Att
open Cb.Pv.Att.End (JoinLay LMat LDat LEat)

variable {K : Type} [Field K] [Fintype K] {M0 X Mg : Type}

/-- The three free linear claims at their meant value. -/
noncomputable def meantLin (P0 : OwnPar K M0 X) (Λ0 : Lin P0 Mg) (ns : ℕ) (N : Nums)
    (Q : JoinLay (closedOf P0 Λ0 ns N)) : Lin P0 Mg where
  maskOf := Λ0.maskOf
  restOf := Λ0.restOf
  LM := LMat (closedOf P0 Λ0 ns N)
  LD := LDat (closedOf P0 Λ0 ns N)
  LE := LEat (closedOf P0 Λ0 ns N) Q

/-- The join's letters, at the parameters with the meant claims. -/
def meantQ (P0 : OwnPar K M0 X) (Λ0 : Lin P0 Mg) (ns : ℕ) (N : Nums) (Q : JoinLay (closedOf P0 Λ0 ns N)) :
    JoinLay (closedOf P0 (meantLin P0 Λ0 ns N Q) ns N) := ⟨Q.scl, Q.q, Q.ce⟩

theorem meant_LM (P0 : OwnPar K M0 X) (Λ0 : Lin P0 Mg) (ns : ℕ) (N : Nums) (Q : JoinLay (closedOf P0 Λ0 ns N)) :
    ∀ x r m, (closedOf P0 (meantLin P0 Λ0 ns N Q) ns N).LM x r m ↔
      LMat (closedOf P0 (meantLin P0 Λ0 ns N Q) ns N) x r m := fun _ _ _ => Iff.rfl

theorem meant_LD (P0 : OwnPar K M0 X) (Λ0 : Lin P0 Mg) (ns : ℕ) (N : Nums) (Q : JoinLay (closedOf P0 Λ0 ns N)) :
    ∀ x r m, (closedOf P0 (meantLin P0 Λ0 ns N Q) ns N).LD x r m ↔
      LDat (closedOf P0 (meantLin P0 Λ0 ns N Q) ns N) x r m := fun _ _ _ => Iff.rfl

theorem meant_LE (P0 : OwnPar K M0 X) (Λ0 : Lin P0 Mg) (ns : ℕ) (N : Nums) (Q : JoinLay (closedOf P0 Λ0 ns N)) :
    ∀ x r m, (closedOf P0 (meantLin P0 Λ0 ns N Q) ns N).LE x r m ↔
      LEat (closedOf P0 (meantLin P0 Λ0 ns N Q) ns N) (meantQ P0 Λ0 ns N Q) x r m := fun _ _ _ => Iff.rfl

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.meant_LM
#print axioms VerifiableInference.Desc.First.Att.P.meant_LE
