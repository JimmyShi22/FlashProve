-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/WrittenInScope.lean: the equations on the public part under which the laws on the
sub-protocols K13 and K14 are stated (`Written Z x`, Johnson/Goal/Numbers/WrittenAtZ.lean), at the
public part Z that the IOP as written in Lean for the proof file computes (`pureRoad.pub`,
Johnson/Desc/ProofFile/OnlineDescriptionPublicPart.lean), at all public files in the goals' scope, with no equation
left as a premise. And what these laws then say at that Z.

The premises that are left. The scope. That the public part is computed. That two tests at the run
say yes: the planner's sizes of a proof file, and five fields of the first chain's parameters as
read back, are the written ones (`sizedPinnedAt`, `firstPinnedAt`,
Johnson/Desc/Ok/PlanWritten/SizedTest.lean). That the verifier's value for the proof file is laid
(`proofDataAndDecisionOfPublicFiles`, Johnson/Desc/Laid/ProofFull.lean). That `realSized` returns x with the written codes: a
closed fact with a witness (`k14_real`). The statements that end in `_of_before` take besides: that
the list of messages in front of the shared point is not empty; `before_in_scope`
(Johnson/Desc/K14/Law/BeforeInScope.lean) pays that from the last premise, and the statements that
end in `_in_scope` are without it.

How: `written_of_pins'` (Johnson/Desc/K14/Law/StartWritten.lean) is called. Its premises, and who
pays each:
  the public part is `pubBy`'s: by the text of `pureRoad`.
  `AtFull`: `atFull_of_publicO` (Johnson/Desc/K12/Law/Sizes/PublicOAtScope.lean), from the scope,
    `pub_public` (Johnson/Desc/ProofFile/Law/MakerPublic.lean), `pub_configure`
    (Johnson/Desc/ProofFile/Law/PlainMade.lean) and `shapesWith_sub`
    (OnBytes/Model/LinkRoundsList.lean) behind `plainShapes_with`.
  the first and the second chain's entries are the written lists': `plans_written`
    (Johnson/Goal/Numbers/PlanWrittenPlans.lean).
  the rows left to the test on the table, the shape of that test, the slots: `first_in_scope` (the
    slots have a second payer, not called here: `chainsOf_proof_binding`,
    Johnson/Goal/Numbers/DepthAtThe.lean); the codes and the shape in the planner's sizes:
    `sized_in_scope` (Johnson/Goal/Numbers/KeyInScope.lean), with `codes_written`
    (Johnson/Desc/Ok/PlanWritten/SizedTestLaws.lean) and `real_shape`
    (Johnson/Goal/Numbers/RealShape.lean).

Statements.
  `plainShapes_with`: what the maker of the shapes in that IOP returns is what `shapesWith` returns
    at some links, layout and identifiers.
  `atFull_in_scope`: `AtFull` of what the planner configured in Z.
  `written_of_before`, **`written_in_scope`**: `Written Z x`.
  `k13_of_before`, `k14_of_before`, `k14_seat_of_before`, and `k13_in_scope`, `k14_in_scope`,
    `k14_seat_in_scope`: so `k13_at_Z`, `k14_at_Z` and `k14_at_seat` (WrittenAtZ.lean) at that Z.
  `first_codes_in_scope`, `first_shape_in_scope`: the first chain's codes as read back are
    `codesFull2`, and its shape of a request is `ReqLit.shapeFull` (Johnson/Desc/ReqLit/Full.lean).
    No evaluation is made here.

Is it empty? Each statement has a member only where the public part is computed, both tests say yes
and the value is laid: that is shown at the stored full-size files (AtFullSide: `theLive_zFull`,
`written_zFull`), not here; at other public files it is the reference run's to show.
Limits. That a verifier asks the two tests is not said here. Nothing on soundness.
-/
import Johnson.Desc.K14.Law.StartWritten
import Johnson.Desc.K14.Law.BeforeInScope
import Johnson.Goal.Numbers.RealShape
import Johnson.Goal.Numbers.KeyInScope
import Johnson.Goal.Numbers.PlanWrittenPlans
import Johnson.Desc.ProofFile.Law.PlainMade
import Johnson.Desc.K12.Law.Sizes.PublicOAtScope
import OnBytes.Model.LinkRoundsList

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Model.Verify Johnson.G
open VerifiableInference.PlanWritten (proofSizedFull sizedPinnedAt firstPinnedAt sized_in_scope
  first_in_scope codes_written plans_written)
open VerifiableInference.Desc.K1 (realSized)
open VerifiableInference.Desc.K13.Law (K13Cond K13Called K13AtCap)
open H2K.Sizes (AtFull atFull_of_publicO)
open LPFD.Full (proofDataAndDecisionOfPublicFiles RunPF)

/-- What the maker of the shapes returns is what `shapesWith` returns at some arguments. -/
theorem plainShapes_with {X : Public} {lay : Option ByteArray}
    {ls : Array Stages.LinkH × Shapes} (h : ProofFile.Plain.shapesOf X lay = .ok ls) :
    ∃ rl layout ids, shapesWith X rl layout ids = .ok ls.2 := by
  unfold ProofFile.Plain.shapesOf at h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨⟨links', declared⟩, _, h⟩ := exc_bind h
  dsimp only at h
  split at h
  · obtain ⟨file, _, h⟩ := exc_bind h
    split at h
    · obtain ⟨⟨reqLinks, layout⟩, _, h⟩ := exc_bind h
      dsimp only at h
      obtain ⟨s, hs, h⟩ := exc_bind h
      have e : (links', s) = ls := Except.ok.inj h
      rw [← e]
      exact ⟨_, _, _, hs⟩
    · obtain ⟨_, e, _⟩ := exc_bind h
      cases e
  · obtain ⟨_, e, _⟩ := exc_bind h
    cases e

section
variable {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub}

/-- **In scope what the planner configured is as at the full size.** -/
theorem atFull_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z) : AtFull Z.p.chains.made := by
  obtain ⟨ls, hs, hm, _, _⟩ := ProofFile.Law.pub_configure h
  obtain ⟨rl, layout, ids, hw⟩ := plainShapes_with hs
  exact atFull_of_publicO hW (ProofFile.Law.pub_public h) hm (shapesWith_sub hw)

variable {D : OnBytes.Maker.WholeD} {r : RunPF} {x : LinSized}

/-- **The equations on the public part, in scope.** -/
theorem written_of_before (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hs : sizedPinnedAt Z.p.X.P Z.p.chains.made = true)
    (hf : firstPinnedAt Z.p.X.P Z.first = true)
    (hl : proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) (hx : realSized = some (x, codesFull2))
    (before : ∀ N, H2U.placesOfMade Z.made = .ok N → Desc.K14.beforePointOf N ≠ []) :
    Written Z x := by
  obtain ⟨Z', hZ', p1, p2, _⟩ := plans_written hW hl
  obtain rfl : Z' = Z := Except.ok.inj (hZ'.symm.trans h)
  obtain ⟨_, f2, _, f4, f5⟩ := first_in_scope hW h hf
  have hz := sized_in_scope hW h hs
  refine written_of_pins' (made := ProofFile.PlainG.madeOf o) (st := ProofFile.plainStarts) h
    (atFull_in_scope hW h) p1 p2 hx f4 (f2.trans (real_shape hx).symm) ?_ ?_ ?_ before
  · rw [f5]
    decide
  · rw [hz]
    exact codes_written
  · rw [hz]
    exact (real_shape hx).symm

/-- **K13's law at that public part.** -/
theorem k13_of_before (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hs : sizedPinnedAt Z.p.X.P Z.p.chains.made = true)
    (hf : firstPinnedAt Z.p.X.P Z.first = true)
    (hl : proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) (hx : realSized = some (x, codesFull2))
    (before : ∀ N, H2U.placesOfMade Z.made = .ok N → Desc.K14.beforePointOf N ≠ []) :
    K13Cond (VerifiableInference.Desc.K13.whereOf Z) codesFull2 dryProofFull.1 48270
        (VerifiableInference.Desc.K1.sentOf 2 0)[81]? ∧
      K13Called (VerifiableInference.Desc.K13.whereOf Z) dryProofFull.1 48270 ∧
      K13AtCap (VerifiableInference.Desc.K13.whereOf Z) dryProofFull.1 48270 :=
  k13_at_Z hx (written_of_before hW h hs hf hl hx before)

/-- **K14's law at the parameters that the shared chain's maker takes off the planner's chains.** -/
theorem k14_of_before (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hs : sizedPinnedAt Z.p.X.P Z.p.chains.made = true)
    (hf : firstPinnedAt Z.p.X.P Z.first = true)
    (hl : proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) (hx : realSized = some (x, codesFull2))
    (before : ∀ N, H2U.placesOfMade Z.made = .ok N → Desc.K14.beforePointOf N ≠ [])
    (bp : List (Nat × Nat)) (hbp : bp ≠ []) : K14At (p14Of Z.p.chains bp) :=
  k14_at_Z hx (written_of_before hW h hs hf hl hx before) bp hbp

/-- **At the seat's own chain.** -/
theorem k14_seat_of_before (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hs : sizedPinnedAt Z.p.X.P Z.p.chains.made = true)
    (hf : firstPinnedAt Z.p.X.P Z.first = true)
    (hl : proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) (hx : realSized = some (x, codesFull2))
    (before : ∀ N, H2U.placesOfMade Z.made = .ok N → Desc.K14.beforePointOf N ≠ [])
    {s : ProofFile.SharedSeat} (hseat : Desc.K14.sharedSeatAt Z = some s) :
    ∃ N, H2U.placesOfMade Z.made = .ok N ∧
      K14At (p14Of Z.p.chains (Desc.K14.beforePointOf N)) :=
  k14_at_seat hx (written_of_before hW h hs hf hl hx before) hseat

/-- **THE EQUATIONS ON THE PUBLIC PART, IN SCOPE, WITH NO EQUATION LEFT.** -/
theorem written_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hs : sizedPinnedAt Z.p.X.P Z.p.chains.made = true)
    (hf : firstPinnedAt Z.p.X.P Z.first = true)
    (hl : proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) (hx : realSized = some (x, codesFull2)) :
    Written Z x :=
  written_of_before hW h hs hf hl hx (before_in_scope h hl)

/-- **K13's law in scope.** -/
theorem k13_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hs : sizedPinnedAt Z.p.X.P Z.p.chains.made = true)
    (hf : firstPinnedAt Z.p.X.P Z.first = true)
    (hl : proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) (hx : realSized = some (x, codesFull2)) :
    K13Cond (VerifiableInference.Desc.K13.whereOf Z) codesFull2 dryProofFull.1 48270
        (VerifiableInference.Desc.K1.sentOf 2 0)[81]? ∧
      K13Called (VerifiableInference.Desc.K13.whereOf Z) dryProofFull.1 48270 ∧
      K13AtCap (VerifiableInference.Desc.K13.whereOf Z) dryProofFull.1 48270 :=
  k13_of_before hW h hs hf hl hx (before_in_scope h hl)

/-- **K14's law in scope**, at any list of messages in front of the shared point that is not empty.
-/
theorem k14_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hs : sizedPinnedAt Z.p.X.P Z.p.chains.made = true)
    (hf : firstPinnedAt Z.p.X.P Z.first = true)
    (hl : proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) (hx : realSized = some (x, codesFull2))
    (bp : List (Nat × Nat)) (hbp : bp ≠ []) : K14At (p14Of Z.p.chains bp) :=
  k14_of_before hW h hs hf hl hx (before_in_scope h hl) bp hbp

/-- **K14's law in scope, at the seat's own chain.** -/
theorem k14_seat_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hs : sizedPinnedAt Z.p.X.P Z.p.chains.made = true)
    (hf : firstPinnedAt Z.p.X.P Z.first = true)
    (hl : proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) (hx : realSized = some (x, codesFull2))
    {s : ProofFile.SharedSeat} (hseat : Desc.K14.sharedSeatAt Z = some s) :
    ∃ N, H2U.placesOfMade Z.made = .ok N ∧
      K14At (p14Of Z.p.chains (Desc.K14.beforePointOf N)) :=
  k14_seat_of_before hW h hs hf hl hx (before_in_scope h hl) hseat

/-- The first chain's codes, as read back, are the written codes. -/
theorem first_codes_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hf : firstPinnedAt Z.p.X.P Z.first = true) : Z.first.codes = codesFull2 :=
  (first_in_scope hW h hf).1.trans codes_written

/-- The first chain's shape of a request, as read back, is the written shape. -/
theorem first_shape_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hf : firstPinnedAt Z.p.X.P Z.first = true) :
    Z.first.shape = VerifiableInference.Desc.ReqLit.shapeFull :=
  (first_in_scope hW h hf).2.2.1.trans request_written

end

end Desc.K14.Law

#print axioms Desc.K14.Law.plainShapes_with
#print axioms Desc.K14.Law.atFull_in_scope
#print axioms Desc.K14.Law.written_of_before
#print axioms Desc.K14.Law.k13_of_before
#print axioms Desc.K14.Law.k14_of_before
#print axioms Desc.K14.Law.k14_seat_of_before
#print axioms Desc.K14.Law.written_in_scope
#print axioms Desc.K14.Law.k13_in_scope
#print axioms Desc.K14.Law.k14_in_scope
#print axioms Desc.K14.Law.k14_seat_in_scope
#print axioms Desc.K14.Law.first_codes_in_scope
#print axioms Desc.K14.Law.first_shape_in_scope
