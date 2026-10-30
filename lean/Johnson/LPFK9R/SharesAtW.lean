-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
LPFK9R/SharesAtW.lean: OUR SHARES OF THE JOIN OF «the half of the
table's promise that reads the verifier's state is handed on», AT THE JOIN's OWN WRITTEN LIST AND
NUMBERS (IMR/WrittenList.lean: `linksW`, `placesW`, `nAt`; IMR/TableW.lean: `number_at`):
the fields «batch», «behind» and «close» (at its first and third member) in their own letters.
Theorems, and three evaluations by the kernel.

What is said.
  `linkFit_W`, `listFit_W`: the two Bools on the table and the written list (LinkPlacesFit.lean,
    EqNumbersOf.lean) say yes at `linksW`, `placesW`. `hearN_W`: at each of the 25 segments the
    number of hearing sub-protocols is `nAt`. `place_W`: the places at the numbers 14 l + nAt l + 2
    + i and the next. `batch_W`, `behind_W`, `close0_W`, `close2_W`: **`IM.Hands N linksW placesW E
    ft (14 * l + nAt l + 2 | 3 | 4 | 6) …` at the link's own batching, at every block without a
    round whose decision is the link's runs behind the batching, and at the closing's first and
    third member, retyped.**

Limits. A FORM WITH ITS DEBTS COUNTED. PREMISES THAT STAY: the sixth field (`more`) at all four; the
plan's counts of trees and messages the same at the two places; `TwoBlocks` at the link (the sort's
Take; the lookup's one sentence; the batching is a draw with the link's own gatherer behind it); at
the one equation: the table's own test on the plan's numbers (`rowsAtFit N 25`) and hg: the group
that the link's context names is the plan's group of the segment. Nothing on soundness.

-/
import Johnson.LPFK9R.SharesAtLink
import Johnson.IMR.TableW
import Johnson.Desc.First.Link.Law.EqNumbersOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFK9.HandsAt
open VerifiableInference.Desc
open VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.K9 (atS Where shut)
open VerifiableInference.Desc.First (S Numbers rowsAtFit)
open IM (linksW placesW nAt)

set_option maxRecDepth 1000000 in
/-- The Bool on the table and the written list, at the join's own list. -/
theorem linkFit_W : linkFit linksW placesW = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem listFit_W : listFit linksW placesW = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- At each of the 25 segments the number of hearing sub-protocols is nAt. -/
theorem hearN_all : (List.range 25).all (fun l => hearN linksW l == nAt l) = true := by
  decide +kernel

theorem hearN_W {l : ℕ} (hl : l < 25) : hearN linksW l = nAt l := by
  have h := List.all_eq_true.1 hearN_all l (List.mem_range.2 hl)
  simpa using h

theorem nAt_le (l : ℕ) : nAt l ≤ 9 := by
  unfold nAt
  split <;> omega

/-- The places at a number of a link's last sub-protocols, and at the next. -/
theorem place_W {l i : ℕ} (hl : l < 25) (hi : i + 1 < 6) :
    ∃ p p', placesW[14 * l + nAt l + 2 + i]? = some p ∧
      placesW[14 * l + nAt l + 2 + i + 1]? = some p' ∧ p.link = some l ∧
      p.piece = hearN linksW l + 1 + i := by
  obtain ⟨p, h1, _, h2, h3⟩ := IM.number_at (l := l) (j := nAt l + 1 + i) hl (by omega)
  obtain ⟨p', h1', _, _, _⟩ := IM.number_at (l := l) (j := nAt l + 1 + i + 1) hl (by omega)
  refine ⟨p, p', ?_, ?_, h2, by rw [h3, hearN_W hl]⟩
  · rw [← h1]
    congr 1
    omega
  · rw [← h1']
    congr 1
    omega

variable {N : Numbers} {E : ℕ → S → Bool} {ft : ℕ}

/-- **THE FIELD «batch».** -/
theorem batch_W {l : ℕ} (hl : l < 25) (Lk : Link S ProofFile.Cl) (pp : Where) (T : TwoBlocks Lk pp)
    (hT : N.treesAt placesW[14 * l + nAt l + 2 + 1]? = N.treesAt placesW[14 * l + nAt l + 2]?)
    (hM : N.msgsAt placesW[14 * l + nAt l + 2 + 1]? = N.msgsAt placesW[14 * l + nAt l + 2]?)
    (more : ∀ s s', IM.Yes ft Lk.batchB s s' → s.failed = none → s'.failed = none →
      IM.XK N linksW placesW E (14 * l + nAt l + 2) s = true →
      E (14 * l + nAt l + 2 + 1) s' = true) :
    IM.Hands N linksW placesW E ft (14 * l + nAt l + 2)
      (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) := by
  obtain ⟨p, p', h1, h2, h3, h4⟩ := place_W (l := l) (i := 0) hl (by omega)
  exact hands_batch linkFit_W h1 h2 h3 h4 hT hM Lk pp T more

/-- **THE FIELD «behind».** -/
theorem behind_W {l : ℕ} (hl : l < 25) (Lk : Link S ProofFile.Cl) (pp : Where) (T : TwoBlocks Lk pp)
    (hT : N.treesAt placesW[14 * l + nAt l + 3 + 1]? = N.treesAt placesW[14 * l + nAt l + 3]?)
    (hM : N.msgsAt placesW[14 * l + nAt l + 3 + 1]? = N.msgsAt placesW[14 * l + nAt l + 3]?)
    (more : ∀ s s', IM.Yes ft Lk.behindB s s' → s.failed = none → s'.failed = none →
      IM.XK N linksW placesW E (14 * l + nAt l + 3) s = true →
      E (14 * l + nAt l + 3 + 1) s' = true)
    (b : Block S ProofFile.Cl) (hr : b.rounds = [])
    (hd : ∀ s rs gs, b.decide s rs gs = Lk.runBehind s) :
    IM.Hands N linksW placesW E ft (14 * l + nAt l + 3) b := by
  obtain ⟨p, p', h1, h2, h3, h4⟩ := place_W (l := l) (i := 1) hl (by omega)
  exact share_behind linkFit_W h1 h2 h3 h4 hT hM Lk pp T more b hr hd

/-- **THE FIELD «close» AT j = 0: THE ONE EQUATION.** -/
theorem close0_W {l : ℕ} (hl : l < 25) (hN : rowsAtFit N 25 = true) (pw : Where)
    (Q : First.Close.Par)
    (hT : N.treesAt placesW[14 * l + nAt l + 4 + 0 + 1]? =
      N.treesAt placesW[14 * l + nAt l + 4 + 0]?)
    (hM : N.msgsAt placesW[14 * l + nAt l + 4 + 0 + 1]? =
      N.msgsAt placesW[14 * l + nAt l + 4 + 0]?)
    (hg : ∀ s a, IM.XK N linksW placesW E (14 * l + nAt l + 4 + 0) s = true →
      atS.get? s = some a → N.groupAt l = a.L.check.group)
    (more : ∀ s s', IM.Yes ft (K9.oneEquation (Cl := ProofFile.Cl) atS pw) s s' → s.failed = none →
      s'.failed = none → IM.XK N linksW placesW E (14 * l + nAt l + 4 + 0) s = true →
      E (14 * l + nAt l + 4 + 0 + 1) s' = true)
    (x : Block S Unit) (hx : (K9.closeOf pw Q : List (Block S Unit))[0]? = some x) :
    IM.Hands N linksW placesW E ft (14 * l + nAt l + 4 + 0) (x.retype : Block S ProofFile.Cl) := by
  obtain ⟨p, p', h1, h2, h3, h4⟩ := place_W (l := l) (i := 2) hl (by omega)
  obtain ⟨hat, inj⟩ := numbers_of_fit N linksW placesW hN listFit_W _ l p h1 h3 h4 hl
  exact share_close0 linkFit_W h1 h2 h3 h4 hT hM hat inj pw Q hg more x hx

/-- **THE FIELD «close» AT j = 2: THE SHUTTING.** -/
theorem close2_W {l : ℕ} (hl : l < 25) (pw : Where) (Q : First.Close.Par)
    (hT : N.treesAt placesW[14 * l + nAt l + 4 + 2 + 1]? =
      N.treesAt placesW[14 * l + nAt l + 4 + 2]?)
    (hM : N.msgsAt placesW[14 * l + nAt l + 4 + 2 + 1]? =
      N.msgsAt placesW[14 * l + nAt l + 4 + 2]?)
    (more : ∀ s s', IM.Yes ft (shut (Cl := ProofFile.Cl) pw (Q.piece + 1)) s s' → s.failed = none →
      s'.failed = none → IM.XK N linksW placesW E (14 * l + nAt l + 4 + 2) s = true →
      E (14 * l + nAt l + 4 + 2 + 1) s' = true)
    (x : Block S Unit) (hx : (K9.closeOf pw Q : List (Block S Unit))[2]? = some x) :
    IM.Hands N linksW placesW E ft (14 * l + nAt l + 4 + 2) (x.retype : Block S ProofFile.Cl) := by
  obtain ⟨p, p', h1, h2, h3, h4⟩ := place_W (l := l) (i := 4) hl (by omega)
  exact share_close2 linkFit_W h1 h2 h3 h4 hT hM pw Q more x hx

end LPFK9.HandsAt

#print axioms LPFK9.HandsAt.linkFit_W
#print axioms LPFK9.HandsAt.listFit_W
#print axioms LPFK9.HandsAt.batch_W
#print axioms LPFK9.HandsAt.behind_W
#print axioms LPFK9.HandsAt.close0_W
#print axioms LPFK9.HandsAt.close2_W
