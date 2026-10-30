-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/KeepsFromStep.lean: kind K13, the members' batching: THE KIND's
CLAUSE `K13KeepsAll` (Johnson/Desc/K13/Honest/KeepsAllM3.lean) FROM THE WHOLE MEMBER's ACCEPTING
STEP (`StepYes`, Johnson/Top/H0/Walk/Reach.lean), with nothing asked of the state in front.
Statements with their proofs. General in the list of sub-protocols; the form at the library's own
list is KeepsFromStepAt.lean of this folder.

`atM3_keepsAll` starts from a return of the kind's own sub-protocol `atM3 P`, at a state without a
mark of failure. A member of a chain is that sub-protocol as the chain's makers have wrapped it. Two
things are asked of the member: it returns only where `atM3 P` does, with the same state
(`MemberIs.back`, ShapeAtM3.lean of this folder); and the state that it returns bears no mark
(`MemberClean`). The kind's step leaves the mark as it was: so the state in front bore none.
Main names:
  `MemberClean`: A PREMISE's FORM: what the member returns bears no mark of failure.
  `k13_keeps_stepYes`: **the clause from the member's accepting step.**
  `memberClean_open`: `MemberClean` at the IOP's own member at the kind's place.

What is not claimed. That the member's step accepts anywhere. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K13.ShapeAtM3
import Johnson.Desc.K13.Honest.KeepsAllM3
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13 (Where whereOf)
open VerifiableInference.Desc.K13.Honest (K13KeepsAll atM3_keepsAll)

variable {Cl : Type}

/-- **What the member number b returns bears no mark of failure.** A premise's form. -/
def MemberClean (bs : List (Block S Cl)) (b : Nat) : Prop :=
  ∀ blk, bs[b]? = some blk → ∀ s rs gs t', blk.decide s rs gs = .ok t' → t'.failed = none

/-- **The kind's clause from the whole member's accepting step.** -/
theorem k13_keeps_stepYes {bs : List (Block S Cl)} {b : Nat} {P : Where} {Cl' : Type}
    (hM : MemberIs bs b P Cl') (hC : MemberClean bs b) (ft : Nat) :
    ∀ blk, bs[b]? = some blk → ∀ s s', Johnson.Desc.First.Walk.Tied.StepYes ft blk s s' →
      K13KeepsAll P s s' := by
  intro blk hb s s' ⟨R, c, _, hst⟩
  obtain ⟨-, gs, hd⟩ := VerifiableInference.Desc.K1.step_ok ft blk s s' R c _ hst
  have ha := hM.back blk hb s _ gs s' hd
  have h0 : s.failed = none :=
    (VerifiableInference.Desc.K13.Law.atM3_failed ha).symm.trans (hC blk hb s _ gs s' hd)
  exact atM3_keepsAll h0 ha

section
open ProofFile.Honest.AtPlace (k13_m3_decides)

variable {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription Inst} {Zp : Pub} {Bs : PureBase}
  {base : List (Block S ProofFile.Cl)} {c₁ : Chain S ProofFile.Cl} {A : SharedSeat} {B : SecondSeat}

/-- `MemberClean` at the IOP's own member: where the member number b of the first chain's flat list
stands at the kind's place. -/
theorem memberClean_open (O : IM.Open o pol lay KL F Zp Bs base c₁ A B) {b : Nat}
    (hp : ∀ blk, c₁.blocksInOrder[b]? = some blk → blk.place = ⟨1, none, 3, .K13⟩) :
    MemberClean c₁.blocksInOrder b :=
  fun blk hb s rs gs t' h =>
    ((k13_m3_decides O (List.mem_of_getElem? hb) (hp blk hb) s t' rs gs).1 h).2.1

end

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_keeps_stepYes
#print axioms ProofFile.Honest.K13.memberClean_open
