-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/KeyPlansAtPure.lean: in the public part that the proof file's description
computes (`pureRoad.pub`, Johnson/Desc/ProofFile/OnlineDescriptionPublicPart.lean), at the parameter file of the goals'
scope, the planner's record holds the three written priced plans of a key file
(Johnson/G/PricedKeyLit.lean): all 18950 rounds. For every function in the second hash function's
place; the description's constant stands in the digest's place; no hash is named.

How. Where that public part is computed, its planner's record is what one call of `configure`
returns (`pub_configure`, Johnson/Desc/ProofFile/Law/PlainMade.lean), and its public record is what
`publicOfO o` returns (`pub_public`, Johnson/Desc/ProofFile/Law/MakerPublic.lean), so that the steps
of that text hold of it (`PublicSteps`, Johnson/Desc/Ok/PlanWritten/PublicAtSteps.lean). At the
parameter file with any values of the eight free numbers the scan's lines are the written lines and
the layout of the committed matrix is that of the ten written sizes: by the lemmas on the scan of
Johnson/Goal/PlanValues/ScopeAtPlan.lean, along the proof of `key_at_policy` there. So the sizing of
a key returns the typed sizes (`keySized_returns`, Johnson/Goal/PlanValues/KeySizedReturns.lean),
and `keyPlans_of_configure` (Johnson/Goal/Numbers/KeyPlansOfConfigure.lean) applies.

Statements and proofs.
  `args_of_steps`: where the steps hold of X at the parameter file with free numbers v and any scale
    file: X's lines are `recordLines`, and the layout of the committed matrix in X is what `wsLayOf`
    returns at the ten written sizes.
  `plainShapes_ranges`: what the description's own maker of the shapes returns has, as what the key
    file's proof of the ranges looks up, what follows from that layout.
  `keyPlans_at_policy`: so at `VerifierAndGoals.policyFile v`, any layout file, any scale file, any o: the key
    file's plans in the public part's planner's record are the three written ones.
  `keyPlans_at_pure`: the same at all public files in the goals' scope. `keyPriced_at_pure`: so
    `PricedRounds writtenKFull` holds of them, and `Desc.keyOk` says yes of that record.
No evaluation is made here.

What of OnBytes/Model/ is used: `Verify.Public`, `Verify.polLayout`, `Verify.weightShape`,
`Verify.shapesWith`, `wsLayOf`, and what ScopeAtPlan.lean uses.

Limits. One way: from a public part that is computed; that it is computed at any files is not said.
Nothing on the proof file's or the entry file's plans. Nothing says that an error bounds a count.
Nothing on soundness.
-/
import Johnson.Goal.Numbers.KeyPlansOfConfigure
import Johnson.Desc.ProofFile.Law.PlainMade
import Johnson.Desc.Ok.PlanWritten.PublicAtSteps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Number.ByRuns
open VerifiableInference VerifiableInference.Number VerifiableInference.PlanWritten
open OnBytes OnBytes.Model OnBytes.Model.Verify OnBytes.Flat.Held Lk6.AtPlan Johnson.G
open OnBytes.Params (exc_bind recordLines)

/-- At the parameter file with free numbers v: the lines, and the layout of the committed matrix. -/
theorem args_of_steps {v : VerifierAndGoals.FreeLines} {KL : ByteArray} {X : Public}
    (C : PublicSteps (VerifierAndGoals.policyFile v) KL X) :
    X.P.frame = recordLines ∧
      wsLayOf wsFull true recordLines.blockLog = .ok X.layers.wsLay := by
  have hy := C.layout
  have hw := C.wsLay
  have hS := polLayout_scan hy
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, bD⟩ := scan_sizes hS
  have hf := scan_frame hS
  obtain ⟨c1, c2, c3⟩ := layout_sizes (polLayout_layout hy)
  have hq : X.layers.y.dq = 5120 := by
    rw [c2]
    show X.P.h.H * X.P.h.dh = 5120
    rw [b3, b5]
  have hkv : X.layers.y.dkv = 1024 := by
    rw [c3]
    show X.P.h.Gk * X.P.h.dh = 1024
    rw [b4, b5]
  have h3 : X.layers.y.h.p3 = true := by
    rw [c1]
    show (X.P.h.prof == 3 || (X.P.h.prof == 4 && decide (0 < X.P.h.NE))) = true
    rw [b0, b8]
    rfl
  have hws : weightShape X.P X.layers.y = wsFull := by
    unfold weightShape wsFull
    simp only [bD, b1, b2, b5, hkv, hq, b6, b7, b8, b9]
  have hlk : X.P.lkW = recordLines.blockLog := by
    show X.P.frame.blockLog = _
    rw [hf]
  rw [hws, h3, hlk] at hw
  exact ⟨hf, hw⟩

/-- What the key file's proof of the ranges looks up, in the shapes of the description's own maker.
-/
theorem plainShapes_ranges {X : Public} {lay : Option ByteArray}
    {ls : Array Stages.LinkH × Params.Shapes} (h : ProofFile.Plain.shapesOf X lay = .ok ls) :
    Plan.shapeOfLayout X.layers.wsLay X.layers.wsLay.lk = some ls.2.ranges := by
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
      exact shapesWith_ranges hs
    · obtain ⟨_, e, _⟩ := exc_bind h
      cases e
  · obtain ⟨_, e, _⟩ := exc_bind h
    cases e

/-- **At the parameter file with any values of the eight free numbers.** -/
theorem keyPlans_at_policy {o : ProofFile.SecondHashFunctionArgument} {v : VerifierAndGoals.FreeLines} {lay KL : ByteArray}
    {Z : ProofFile.Pub} (h : ProofFile.pureRoad.pub o (VerifierAndGoals.policyFile v) lay KL = .ok Z) :
    Z.p.chains.made.key = [keyThree.A.plan, keyThree.B.plan, keyThree.C.plan] := by
  obtain ⟨ls, hs, hm, _, _⟩ := ProofFile.Law.pub_configure h
  obtain ⟨hf, hw⟩ := args_of_steps (publicSteps_of_O (ProofFile.Law.pub_public h))
  rw [hf] at hm
  exact keyPlans_of_configure hm (keySized_returns hw (plainShapes_ranges hs))

/-- **At all public files in the goals' scope.** -/
theorem keyPlans_at_pure {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} (hW : VerifierAndGoals.InScope W = true)
    {Z : ProofFile.Pub} (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z) :
    Z.p.chains.made.key = [keyThree.A.plan, keyThree.B.plan, keyThree.C.plan] := by
  obtain ⟨v, hv⟩ := inScope_policy hW
  rw [hv] at h
  exact keyPlans_at_policy h

/-- So the prices hold of them, and the key file's own public test says yes. -/
theorem keyPriced_at_pure {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} (hW : VerifierAndGoals.InScope W = true)
    {Z : ProofFile.Pub} (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z) :
    (∃ K₁ K₂ K₃, Z.p.chains.made.key = [K₁, K₂, K₃] ∧ PricedRounds writtenKFull K₁ K₂ K₃) ∧
      Desc.keyOk Z.p.chains.made = true :=
  ⟨⟨_, _, _, keyPlans_at_pure hW h, keyPricedFull⟩,
    keyOk_of_lit key_lit_ok _ (keyPlans_at_pure hW h)⟩

end VerifiableInference.Number.ByRuns

#print axioms VerifiableInference.Number.ByRuns.args_of_steps
#print axioms VerifiableInference.Number.ByRuns.plainShapes_ranges
#print axioms VerifiableInference.Number.ByRuns.keyPlans_at_policy
#print axioms VerifiableInference.Number.ByRuns.keyPlans_at_pure
#print axioms VerifiableInference.Number.ByRuns.keyPriced_at_pure
