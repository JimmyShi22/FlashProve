-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/WorthAtMerge.lean: at the merge of the claims on the committed table (kind
K11): the two items "worth" that are open on both sides of the merge go back over its accepting
step: a clause of the merge's fifth tie. One small lemma, one theorem: a joining.

What is said.
  `pieceAt_head`: where the head's segment has the number 24, the lookup on the digits stands at
    piece 8 of that segment.
  `worth_at_merge`: at the composed meaning over its base `mgAll D mgBase`: from the table's
    condition at 346, no mark and the merge's accepting step: each item of `worthAtMerge` (worth 24
    8 "planes", worth 24 8 "keys") that holds behind the step holds in front: `t5_cut_low`'s premise
    hW (RidesJoinLow.lean).

By what. `worth_planes_step`, `worth_keys_step` (Johnson/Desc/First/Look/K3WorthStep.lean) at
`k3At_mgAll` (Johnson/Desc/Sound/MgAt/K3At.lean): the items go back over any
step that leaves what the lookup has heard and leads to a later ledger. That the merge's step is
such a step: `ledger_at_front`, `sized_of_ledgerB`, `merge_forks`
(KeepAtMerge.lean).

The premises that read no state. hH: the head's segment has the number 24. hx: the public parameters
give segment 24 a lookup on the digits (`digAt`).

Limits. Where no ledger is open behind, or the item behind does not hold, it says nothing. No state
is shown at which the item holds. Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.KeepAtMerge
import Johnson.Top.H0.MergeLaw.RidesJoinLow
import Johnson.Desc.First.Look.K3WorthStep
import Johnson.Desc.Sound.MgAt.K3At
import Johnson.Desc.Sound.MgBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes.Slice
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S Numbers flatPlacesOf)
open VerifiableInference.Desc.First.Look (digAt)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR X)

/-- Where the head's segment has the number 24, the lookup on the digits stands at its piece 8. -/
theorem pieceAt_head (hH : VerifiableInference.OnPublicFiles.headLink X = 24) :
    VerifiableInference.Desc.K3.pieceAt X 24 true = 8 := by
  have e : (if X.p4 then 2 else 1) * X.NGr = 24 := hH
  unfold VerifiableInference.Desc.K3.pieceAt VerifiableInference.Desc.K3.isHead
  rw [e]
  rfl

/-- **The two items "worth" that are open on both sides of the merge go back over its accepting
step.** -/
theorem worth_at_merge (hH : VerifiableInference.OnPublicFiles.headLink X = 24)
    {x : VerifiableInference.Desc.First.Look.Place} {tl : OnBytes.Model.HTailF2}
    (hx : digAt X 24 = some (x, tl)) (Pm : HeadMergeP) (Nn : Numbers) {Fr : Frame} (z : P)
    (a b : S × Fr.E.Str) (w : Wit (CellsQ rows cols) Tok MsgT) {rs : List Fmt.RoundView}
    (hon : onQ Nn (mgAll D mgBase) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a)
    (hf : a.1.failed = none) (hy : headMergeDecide Pm a.1 rs = .ok b.1) :
    ∀ j ∈ worthAtMerge, meansQ Nn (mgAll D mgBase) (fun s => (z, s)) j b w →
      meansQ Nn (mgAll D mgBase) (fun s => (z, s)) j a w := by
  obtain ⟨hled, -⟩ := ledger_at_front D mgBase rfl Nn z a hon hf
  obtain ⟨F, hF, -⟩ := sized_of_ledgerB hled
  obtain ⟨_, x1, -, -, -, hG, hL, htl, -⟩ := merge_forks Pm hy hF
  have hp := pieceAt_head (X := X) hH
  have hh : (VerifiableInference.Desc.K3.seatDigits (fun _ => ())).heard b.1 =
      (VerifiableInference.Desc.K3.seatDigits (fun _ => ())).heard a.1 := by
    show b.1.tl?.bind (·.heard) = a.1.tl?.bind (·.heard)
    rw [htl]
  intro j hj H
  unfold worthAtMerge at hj
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
  rcases hj with rfl | rfl
  · have h1 := VerifiableInference.OnPublicFiles.worth_planes_step
      (VerifiableInference.OnPublicFiles.k3At_mgAll D mgBase) (fun _ => ()) 24 hx z z a.1 b.1
      (strsOf Fr a.2) (strsOf Fr b.2) w hh hF hG ⟨hL.next, hL.ns, hL.keep⟩ (by rw [hp]; exact H)
    rw [hp] at h1
    exact h1
  · have h1 := VerifiableInference.OnPublicFiles.worth_keys_step
      (VerifiableInference.OnPublicFiles.k3At_mgAll D mgBase) (fun _ => ()) 24 hx z z a.1 b.1
      (strsOf Fr a.2) (strsOf Fr b.2) w hh hF hG ⟨hL.next, hL.ns, hL.keep⟩ (by rw [hp]; exact H)
    rw [hp] at h1
    exact h1

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.pieceAt_head
#print axioms VerifiableInference.Desc.First.MergeLaw.worth_at_merge
