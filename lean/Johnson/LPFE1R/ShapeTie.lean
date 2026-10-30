-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/ShapeTie.lean:
WHERE THE PROOF FILE's DESCRIPTION IS MADE AND PASSES ITS TESTS ON THE PLAN, THE REQUEST's SHAPE IN
THE PLANNER's SIZES IS THE SHAPE THAT IS READ BACK FROM THE FIRST CHAIN's PARAMETER BYTES: the one
premise hS of Johnson/Desc/First/Link/Law/EndsOfMade.lean's ends_of_made; AND SO THE TWO MEMBERSHIPS
OF endsThere. AT EVERY o, AT EVERY THREE PUBLIC FILES: NO SCOPE, NO WRITTEN VALUE, NO PIN.
Theorems on public data.

WHY IT HOLDS. The kind K2's lot makes its numbers only where `P1K2.tied` accepts
(Johnson/Desc/ProofFile/Lot/K2OfPlan.lean: prepareAt), and "z.request = first.shape" is tied's first
conjunct. Where it rejects, the lot lays a mute sub-protocol whose test on the plan says no
(Lot/K2.lean: pureMute). The first sub-protocol behind the links is K2's lot's, alone, AT EVERY
DESCRIPTION THAT IS MADE (IM.k2_finish_of: no premise on scope); the
description's planOk gives that sub-protocol's own (IM.plan_back) and so the lot's own
  (alone_planOk · retype_planOk): so it is no mute. lettersBy_first, blankBy_first   the lots'
  letters bear the public part's own first chain's parameters. tied_of_plan     IM.Open … F Z Bs
  base c A B · F.planOk = true ⊢ P1K2.tied … = true. shape_tie        … ⊢
  Z.made.p.chains.made.sized.proof.request = Z.first.shape. ends_of_plan     … ⊢ the two
  memberships (ends_of_made's conclusion), at every dl.

Limits. That a description is made and passes planOk is the caller's (LaidAt holds both:
its fields opened and planOk). The one line at `P5J.LaidAt` is not here: it is `At.ends_at`,
Johnson/LPFE1R/EndsAt.lean, which imports this file. Nothing on soundness or on hiding.

-/
import Johnson.IMR.K2Seat
import Johnson.IMR.PlanAt
import Johnson.Desc.First.Link.Law.EndsOfMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)
open P5T (planSeats numbersOf)

theorem lettersBy_first {mk : ProofFile.LinksBy} {Z : ProofFile.Pub} {s : S} {G : ProofFile.Ground}
    (h : ProofFile.lettersBy mk Z s = .ok G) : G.first = Z.first := by
  unfold ProofFile.lettersBy at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | contradiction | (cases h; rfl)

theorem blankBy_first {mk : ProofFile.LinksBy} {Z : ProofFile.Pub} {G : ProofFile.Ground}
    (h : ProofFile.blankBy mk Z = some G) : G.first = Z.first := by
  unfold ProofFile.blankBy at h
  dsimp only at h
  cases e : ProofFile.lettersBy mk Z (Z.s₀.withReq (Array.replicate Z.p.X.T 0 ++ #[0, 1])) with
  | error w =>
    rw [e] at h
    cases h
  | ok G' =>
    rw [e] at h
    obtain rfl : G' = G := Option.some.inj h
    exact lettersBy_first e

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- K2's lot's ties accept. -/
theorem tied_of_plan (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true) :
    P1K2.tied Z.p.chains.made.sized.proof Bs.G₀.first Z.s₀.st.codes Z.s₀.check.frame.shape
      Z.P.samples = true := by
  obtain ⟨b, x, hb, _, _, hla, harm⟩ := IM.k2_finish_of O
  have hbp : b.planOk = true := IM.plan_back O hp hb
  rw [IM.alone_planOk hla] at hbp
  have hx : x.planOk = true := (IM.retype_planOk x hbp).1
  rcases harm with ⟨h0, -⟩ | ⟨P, n, hP, -, -⟩
  · rw [h0] at hx
    cases hx
  · unfold P1K2.prepOf P1K2.prepareAt at hP
    by_cases ht : P1K2.tied Z.p.chains.made.sized.proof Bs.G₀.first Z.s₀.st.codes
        Z.s₀.check.frame.shape Z.P.samples = true
    · exact ht
    · simp [ht] at hP

/-- **The sizes' request's shape is the shape that is read back.** -/
theorem shape_tie (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true) :
    Z.made.p.chains.made.sized.proof.request = Z.first.shape := by
  have ht := tied_of_plan O hp
  unfold P1K2.tied at ht
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
  have e := ht.1.1.1.1
  rw [blankBy_first O.blank] at e
  exact e

/-- **The two memberships, wherever the description is made and passes its tests on the plan.**
-/
theorem ends_of_plan (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true)
    (dl : List Fmt.DeclaredRound) :
    ((((planSeats Z dl).filter (·.smpd)).map (·.seat)).contains (numbersOf (planSeats Z dl)).index
      && (((planSeats Z dl).filter (·.smpd)).map (·.seat)).contains
        (numbersOf (planSeats Z dl)).w) = true :=
  ends_of_made (show ProofFile.pureRoad.pub o pol lay KL = .ok Z from O.pub) (shape_tie O hp) dl

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.tied_of_plan
#print axioms VerifiableInference.Desc.LinkJoin.shape_tie
#print axioms VerifiableInference.Desc.LinkJoin.ends_of_plan
