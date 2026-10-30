--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/CodesOneAtOpen.lean: where the proof file's description is made and passes its
tests on the plan, the codes that the first chain's parameter bytes hold, as read back, are the
codes that the planner sized. Statements and proofs; no definition.

Why. Two names stand for the proof's codes. `Z.first.codes` is read back from the first chain's
parameter bytes (`Params.First.read`, OnBytes/Params/Chains.lean). The planner keeps what it sized
in `Z.p.chains.made.sized.proof.codes`. The first chain's laws speak of the first name, the shared
chain's laws of the second. A law that joins the two chains needs that they are equal.

How. The description's own text compares them. The numbers of every code switch are made by
`P1K2.prepOf` (Johnson/Desc/ProofFile/Lot/K2OfPlan.lean), which returns nothing unless `P1K2.tied`
says yes, and `tied` tests `z.codes = first.codes` at `z := Z.p.chains.made.sized.proof`. Where
`prepOf` returns nothing, the block that stands first behind the links fails its test on the plan
(`IM.k2_finish_of`, Johnson/IMR/K2Seat.lean). So a description that passes its tests on the plan has
passed `tied`. No spelled bytes are read back here, so no bound on a word or on a size is asked.

Main statements, at every function `o` for the format's second hash function and at all three public files:
  `ties_of_prep`: what a value of `prepOf` says: three of the five equations of `tied`.
  `prep_of_open`: from an opening of the description's maker (`IM.Open`) and `F.planOk = true`:
    `prepOf` returns a value at the maker's own letters.
  `codes_one_open`: so `Z.first.codes = Z.p.chains.made.sized.proof.codes`.
  `shape_one_open`: `Z.first.shape = Z.p.chains.made.sized.proof.request`.
  `start_codes_open`: `Z.s₀.st.codes = Z.p.chains.made.sized.proof.codes`.

Limits. That a description passes its tests on the plan is a premise. Nothing on the shape of the
test on the table (`Z.first.lin`): `tied` does not compare it. Nothing says which codes these are.
Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.IMR.K2Seat
import Johnson.IMR.PlanAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.CodesOne

open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)

/-- What a value of `P1K2.prepOf` says: the planner's sized request shape and codes are those of the
first chain's parameters in `G`, and the first state's codes are the planner's. -/
theorem ties_of_prep {Z : ProofFile.Pub} {G : ProofFile.Ground} {Pp : P1K2.Prep}
    (h : P1K2.prepOf Z G = some Pp) :
    Z.p.chains.made.sized.proof.request = G.first.shape ∧
      Z.p.chains.made.sized.proof.codes = G.first.codes ∧
      Z.s₀.st.codes = Z.p.chains.made.sized.proof.codes := by
  unfold P1K2.prepOf P1K2.prepareAt at h
  simp only [bind, Option.bind, pure] at h
  split at h
  · cases h
  · rename_i ht
    unfold P1K2.tied at ht
    simp only [Bool.not_eq_true, Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq] at ht
    exact ⟨ht.1.1.1.1, ht.1.1.1.2, ht.1.1.2⟩

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- Where the description passes its tests on the plan, the numbers of the code switches are made:
otherwise the block that stands first behind the links would fail its own test. -/
theorem prep_of_open (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true) :
    ∃ Pp, P1K2.prepOf Z Bs.G₀ = some Pp := by
  obtain ⟨b, x, e1, -, -, hla, hx⟩ := IM.k2_finish_of O
  have hb : b.planOk = true := IM.plan_back O hp e1
  rw [IM.alone_planOk hla] at hb
  have hxp : x.planOk = true := (IM.retype_planOk x hb).1
  rcases hx with ⟨h0, -⟩ | ⟨Pp, -, hP, -, -⟩
  · rw [h0] at hxp
    cases hxp
  · exact ⟨Pp, hP⟩

/-- **The codes as read back from the first chain's parameter bytes are the codes as sized.** -/
theorem codes_one_open (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true) :
    Z.first.codes = Z.p.chains.made.sized.proof.codes := by
  obtain ⟨Pp, hP⟩ := prep_of_open O hp
  rw [← O.first]
  exact (ties_of_prep hP).2.1.symm

/-- The same for the request's shape. -/
theorem shape_one_open (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true) :
    Z.first.shape = Z.p.chains.made.sized.proof.request := by
  obtain ⟨Pp, hP⟩ := prep_of_open O hp
  rw [← O.first]
  exact (ties_of_prep hP).1.symm

/-- The codes in the state before the first segment are the codes as sized. -/
theorem start_codes_open (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true) :
    Z.s₀.st.codes = Z.p.chains.made.sized.proof.codes := by
  obtain ⟨Pp, hP⟩ := prep_of_open O hp
  exact (ties_of_prep hP).2.2

end

end Desc.CodesOne

#print axioms Desc.CodesOne.ties_of_prep
#print axioms Desc.CodesOne.prep_of_open
#print axioms Desc.CodesOne.codes_one_open
#print axioms Desc.CodesOne.shape_one_open
#print axioms Desc.CodesOne.start_codes_open
