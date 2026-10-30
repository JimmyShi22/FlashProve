-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
LPFK9R/HandsAtLink.lean: `IM.Hands` (IMR/HandsDef.lean: what
one block of the first chain owes to «the half of the table's promise that reads the verifier's
state is handed on») AT FOUR OF A LINK's LAST BLOCKS: the batching, the frame's block behind it, the
one equation, the shutting: 100 of the first chain's 358 blocks at the full size. Theorems: the
library's Link/Law files laid into that structure's six fields.

What is said.
  `keeps4_of_rb`: `Rb` gives `IM.Keeps4`. `hands_of_rb`: `IM.Hands` at a block with a quiet row each
    of whose yeses stands in `Rb` and leaves no count of rows waiting where none may wait.
    `hands_batch`, `hands_behind`, `hands_shut`: **`IM.Hands` at the batching's block and at the
    frame's block behind it (from `TwoBlocks`), and at a block each of whose yeses is the
    shutting's.** `hands_eq`: **`IM.Hands` at a block each of whose yeses is the one equation's**:
    its row is not quiet: the five fields by EqHands.lean. What is asked of the table and of the
    written list comes of ONE Bool's yes (`linkFit`, LinkPlacesFit.lean).

Limits. A FORM WITH ITS DEBTS COUNTED. PREMISES THAT STAY: the sixth field (`more`: the further
Bools E (k + 1) behind the block) at all four; the plan's counts of trees and messages the same at
the two places; at the one equation: the plan lays the class «equation» at the end of what is open,
one row; no other open segment has the segment's group; AND hg: THE GROUP THAT THE LINK's CONTEXT
NAMES IS THE PLAN's GROUP OF THE SEGMENT, drawn from X k s (it is for E k to hold it); `TwoBlocks`
(the sort's Take; the lookup's one sentence; the batching's block is a draw with the gatherer behind
it). The blocks are the link's own, or letters under the kind's text: `IM.Hands.under` carries them
to the seated blocks. Nothing on soundness.

-/
import Johnson.IMR.HandsDef
import Johnson.Desc.First.Link.Law.LinkAtSort
import Johnson.Desc.First.Link.Law.EqHands
import Johnson.Desc.First.Link.Law.LinkPlacesFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFK9.HandsAt
open VerifiableInference.Desc
open VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.K9 (atS Where shut)
open VerifiableInference.Desc.First (S ModelPart Item RowClass Numbers start rowOf openSets stepOpen
  quietRow shapeAt mayWait rowSegs rowsDue)

theorem keeps4_of_rb {s s' : S} (R : Rb s s') : IM.Keeps4 s s' :=
  ⟨R.rq.groups, R.rq.place, R.rq.trees, R.rq.oracles⟩

variable {N : Numbers} {links : List ModelPart} {ps : List Place} {E : ℕ → S → Bool} {ft k : ℕ}

/-- **Hands at a block with a quiet row each of whose yeses stands in Rb.** -/
theorem hands_of_rb {b : Block S ProofFile.Cl} {p p' : Place} (hp : ps[k]? = some p)
    (hp' : ps[k + 1]? = some p') (hq : quietRow (rowOf links p) = true) (hn : NextIn links p p')
    (hT : N.treesAt ps[k + 1]? = N.treesAt ps[k]?) (hM : N.msgsAt ps[k + 1]? = N.msgsAt ps[k]?)
    (hR : ∀ s s', IM.Yes ft b s s' → Rb s s' ∧
      (shapeAt links (some p) s = true → s'.noneWaits = true ∨ mayWait links p' = true))
    (more : ∀ s s', IM.Yes ft b s s' → s.failed = none → s'.failed = none →
      IM.XK N links ps E k s = true → E (k + 1) s' = true) : IM.Hands N links ps E ft k b :=
  IM.hands_quiet hp hq hT hM (fun s s' hy _ _ => keeps4_of_rb (hR s s' hy).1)
    (fun s s' hy h => by rw [(hR s s' hy).1.failed]; exact h)
    (fun s s' hy _ _ hx => by
      obtain ⟨R, hw⟩ := hR s s' hy
      have hs := (IM.xk_parts hx).1
      rw [hp] at hs
      rw [hp']
      exact shape_step links p p' s s' hs R.stand hn.stand hn.link (hw hs) R.num) more

/-- **THE BATCHING's BLOCK.** -/
theorem hands_batch (hfit : linkFit links ps = true) {m : ℕ} {p p' : Place}
    (hp : ps[k]? = some p) (hp' : ps[k + 1]? = some p') (hl : p.link = some m)
    (hpc : p.piece = hearN links m + 1)
    (hT : N.treesAt ps[k + 1]? = N.treesAt ps[k]?) (hM : N.msgsAt ps[k + 1]? = N.msgsAt ps[k]?)
    (L : Link S ProofFile.Cl) (pp : Where) (T : TwoBlocks L pp)
    (more : ∀ s s', IM.Yes ft L.batchB s s' → s.failed = none → s'.failed = none →
      IM.XK N links ps E k s = true → E (k + 1) s' = true) :
    IM.Hands N links ps E ft k L.batchB := by
  obtain ⟨⟨n1, n2⟩, hq, hw⟩ := fit_batch links ps hfit k m p p' hp hp' hl hpc
  exact hands_of_rb hp hp' hq ⟨n1, n2⟩ hT hM
    (fun s s' ⟨rs, cols, n, h⟩ => ⟨(T.1 ft s rs cols s' n h).1, fun _ => Or.inr hw⟩) more

/-- **THE FRAME's BLOCK BEHIND THE BATCHING.** -/
theorem hands_behind (hfit : linkFit links ps = true) {m : ℕ} {p p' : Place}
    (hp : ps[k]? = some p) (hp' : ps[k + 1]? = some p') (hl : p.link = some m)
    (hpc : p.piece = hearN links m + 2)
    (hT : N.treesAt ps[k + 1]? = N.treesAt ps[k]?) (hM : N.msgsAt ps[k + 1]? = N.msgsAt ps[k]?)
    (L : Link S ProofFile.Cl) (pp : Where) (T : TwoBlocks L pp)
    (more : ∀ s s', IM.Yes ft L.behindB s s' → s.failed = none → s'.failed = none →
      IM.XK N links ps E k s = true → E (k + 1) s' = true) :
    IM.Hands N links ps E ft k L.behindB := by
  obtain ⟨⟨n1, n2⟩, hq, hw⟩ := fit_behind links ps hfit k m p p' hp hp' hl hpc
  exact hands_of_rb hp hp' hq ⟨n1, n2⟩ hT hM
    (fun s s' ⟨rs, cols, n, h⟩ => ⟨(T.2 ft s rs cols s' n h).1, fun _ => Or.inr hw⟩) more

/-- **THE SHUTTING.** -/
theorem hands_shut (hfit : linkFit links ps = true) {m : ℕ} {p p' : Place}
    (hp : ps[k]? = some p) (hp' : ps[k + 1]? = some p') (hl : p.link = some m)
    (hpc : p.piece = hearN links m + 5)
    (hT : N.treesAt ps[k + 1]? = N.treesAt ps[k]?) (hM : N.msgsAt ps[k + 1]? = N.msgsAt ps[k]?)
    (pw : Where) (piece : ℕ) (b₅ : Block S ProofFile.Cl)
    (hb₅ : ∀ ft s rs cols x, b₅.step ft s rs cols = .ok x →
      (shut (Cl := ProofFile.Cl) pw piece).step ft s rs cols = .ok x)
    (more : ∀ s s', IM.Yes ft b₅ s s' → s.failed = none → s'.failed = none →
      IM.XK N links ps E k s = true → E (k + 1) s' = true) :
    IM.Hands N links ps E ft k b₅ := by
  obtain ⟨⟨n1, n2⟩, hq, hnw⟩ := fit_shut links ps hfit k m p p' hp hp' hl hpc
  refine hands_of_rb hp hp' hq ⟨n1, n2⟩ hT hM (fun s s' ⟨rs, cols, n, h⟩ => ?_) more
  obtain ⟨R, e⟩ := rb_shutB pw piece b₅ hb₅ ft s rs cols s' n h
  refine ⟨R, fun hs => Or.inl ?_⟩
  have hs' : (First.standOf s == First.standAt links p && (s.noneWaits || mayWait links p) &&
      s.link?.all fun L => p.link == some L.link) = true := hs
  have h2 := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 hs').1).2
  rw [hnw, Bool.or_false] at h2
  unfold S.noneWaits at h2 ⊢
  rw [e]
  exact h2

/-- **THE ONE EQUATION's BLOCK.** -/
theorem hands_eq (hfit : linkFit links ps = true) {m : ℕ} {p p' : Place}
    (hp : ps[k]? = some p) (hp' : ps[k + 1]? = some p') (hl : p.link = some m)
    (hpc : p.piece = hearN links m + 3)
    (hT : N.treesAt ps[k + 1]? = N.treesAt ps[k]?) (hM : N.msgsAt ps[k + 1]? = N.msgsAt ps[k]?)
    (hat : N.rowsAt m .equation = (rowsDue N (IM.openAt links ps k) m, 1))
    (inj : ∀ m' ∈ rowSegs (IM.openAt links ps k), m' ≠ m → N.groupAt m' ≠ N.groupAt m)
    (pw : Where) (b₃ : Block S ProofFile.Cl)
    (hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
      (K9.oneEquation (Cl := ProofFile.Cl) atS pw).step ft s rs cols = .ok x)
    (hg : ∀ s a, IM.XK N links ps E k s = true → atS.get? s = some a →
      N.groupAt m = a.L.check.group)
    (more : ∀ s s', IM.Yes ft b₃ s s' → s.failed = none → s'.failed = none →
      IM.XK N links ps E k s = true → E (k + 1) s' = true) :
    IM.Hands N links ps E ft k b₃ := by
  obtain ⟨⟨n1, n2⟩, hins, houts, fresh, seg⟩ := fit_eq links ps hfit k m p p' hp hp' hl hpc
  have hO : IM.openAt links ps (k + 1) = stepOpen (IM.openAt links ps k) (rowOf links p) :=
    First.openSets_succ links ps (start links) k p hp
  refine ⟨fun s s' ⟨rs, cols, n, h⟩ hm => ?_, fun s s' ⟨rs, cols, n, h⟩ _ _ hx => ?_,
    fun s s' ⟨rs, cols, n, h⟩ _ _ hx => ?_, fun s s' ⟨rs, cols, n, h⟩ _ _ hx => ?_,
    fun s s' ⟨rs, cols, n, h⟩ _ _ hx => ?_, more⟩
  · obtain ⟨a, row, G0, _, _, El⟩ := eq_lays pw b₃ hb₃ ft s rs cols s' n h
    rw [El.failed]
    exact hm
  · obtain ⟨a, row, G0, _, _, El⟩ := eq_lays pw b₃ hb₃ ft s rs cols s' n h
    have hs := (IM.xk_parts hx).1
    rw [hp] at hs
    rw [hp']
    exact eq_shape links p p' ⟨n1, n2⟩ s s' _ row El hs
  · obtain ⟨a, row, G0, ha, hG, El⟩ := eq_lays pw b₃ hb₃ ft s rs cols s' n h
    rw [hO]
    exact eq_rows N _ _ m hins houts fresh seg hat inj s s' _ row G0 El hG (hg s a hx ha)
      (IM.xk_parts hx).2.1
  · obtain ⟨a, row, G0, _, _, El⟩ := eq_lays pw b₃ hb₃ ft s rs cols s' n h
    rw [hO]
    exact eq_members N _ _ m hins houts fresh seg s s' _ row El (IM.xk_parts hx).2.2.1
  · obtain ⟨a, row, G0, _, _, El⟩ := eq_lays pw b₃ hb₃ ft s rs cols s' n h
    exact eq_book N _ _ hT hM s s' _ row El (IM.xk_parts hx).2.2.2.1

end LPFK9.HandsAt

#print axioms LPFK9.HandsAt.hands_batch
#print axioms LPFK9.HandsAt.hands_behind
#print axioms LPFK9.HandsAt.hands_eq
#print axioms LPFK9.HandsAt.hands_shut
