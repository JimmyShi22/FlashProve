-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/SeamL.lean: THE COUNT AT THE SEAM between this folder's
stretches and the code switch's, at the job of the first chain's proximity test (`jobL`,
AtProof/JobL.lean). This folder's `Stretch` (K12/Coins.lean) is read by number and has lost its
count; the code switch's (`K2.Stretch`, K2/Part.lean) bears it. `carryRows` gives the count back by
`asK2`, at a count that it takes off the sender's public data. This file shows that, at every c :
CsAll l of a list l that begins with the members' counts, that count is the entry's own in l, and
that the lists which the test's two parts state as carried are such lists. Two definitions; nine
theorems.

  `carried_asK2`, `carried_beyond`   the code switch's reader of a lent list
                 (`K2.Stretch.carried`) and this folder's (`stretches`): one, by `asK2` at the
                 list's own count; beyond the list
  `Begins`, `begins_runs`, `begins_first`   a list begins with the members' counts; what the test's
                 two parts state as carried does
  `carryBy`, `carryRows_by_carried`   `carryRows`' text at `K2.Stretch.carried`;
                 `carryRows` at `stretches l c` is it
  `mem_rest`, `mem_first_L`   what the two parts' readers hand the job as `mem`
  `seam_first`, `seam_rest`   the two joined, at `jobL`, part by part

By what. Induction on the list; `asK2_stretchOf` (JobL.lean) at its head.

Limits.
- On counts alone. Whose random values a book lends under an entry (its owner, its start) is the
  book's: nothing here.
- `Begins` asks the counts in their order, not the names.
- That the two parts' moves are made of these two readers is `first_moves` and `rest_moves`
  (K12/HalfSteps.lean). That a move hands the job's `rows₀` and `trees₀` the reader's field `mem` is
  the text of `moveAt` and `TestJob.first` (K12/Parts.lean, Test.lean): by reading; no count is
  touched there. That the frame lends a part just the list that it states is the type of the frame's
  `lendPart` (Honest/Frame.lean): not restated here.
- Nothing on completeness, soundness or hiding.
Terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.JobL
import Johnson.Desc.ProofFile.Honest.K12.HalfSteps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc.K2.Honest (mainRows zeroG)
open VerifiableInference.Desc.K12 (P12 T12)

variable {W₀ Rc Xi Tr X : Type}

/-! ## 1 The two readers of a lent list are one -/

/-- **The code switch's reader of a lent list and this folder's, bridged by `asK2` at the list's own
count, are one**: where the list has an entry number n. General in the list: no job, no book. -/
theorem carried_asK2 : ∀ (l : List (String × Due)) (c : CsAll l) (n : ℕ) (x : String × Due),
    l[n]? = some x → K2.Stretch.carried l c n = .ok (asK2 x.2 (stretches l c n))
  | [], _, _, _, h => by simp at h
  | d :: l, c, 0, x, h => by
    have e : d = x := by simpa using h
    subst e
    simp only [K2.Stretch.carried, stretches, asK2_stretchOf]
  | d :: l, c, n + 1, x, h => by
    simp only [K2.Stretch.carried, stretches]
    exact carried_asK2 l _ n x (by simpa using h)

/-- Beyond the list the code switch's reader refuses, and this folder's yields the stretch of zeros.
-/
theorem carried_beyond : ∀ (l : List (String × Due)) (c : CsAll l) (n : ℕ), l[n]? = none →
    K2.Stretch.carried l c n = .error "a stretch is asked beyond the list" ∧
      stretches l c n = Stretch.zero
  | [], _, _, _ => ⟨rfl, rfl⟩
  | d :: l, c, 0, h => by simp at h
  | d :: l, c, n + 1, h => by
    simp only [K2.Stretch.carried, stretches]
    exact carried_beyond l _ n (by simpa using h)

/-! ## 2 At the job -/

/-- **A list of named counts begins with the members' counts**, in their order. -/
def Begins (ms : List (Addr × ℕ × Due)) (l : List (String × Due)) : Prop :=
  ∀ (n : ℕ) (m : Addr × ℕ × Due), ms[n]? = some m → ∃ s, l[n]? = some (s, m.2.2)

/-- What either part of the test states as carried begins so: the first part's list is the case
l₂ = [] up to `List.append_nil`; the second's has the fresh table's run behind. -/
theorem begins_runs {W X : Type} (J : TestJob W X) (dest : Addr) (l₂ : List (String × Due)) :
    Begins J.members (memberRuns J dest ++ l₂) := by
  intro n m h
  refine ⟨carriedName m.1 m.2.1 dest, ?_⟩
  have hn : n < J.members.length := (List.getElem?_eq_some_iff.1 h).1
  rw [List.getElem?_append_left (by simpa [memberRuns] using hn)]
  simp [memberRuns, h]

theorem begins_first {W X : Type} (J : TestJob W X) (dest : Addr) :
    Begins J.members (memberRuns J dest) := by
  have h := begins_runs J dest []
  rwa [List.append_nil] at h

/-- `carryRows`' text with THE CODE SWITCH's OWN READER of a lent list l in the place of `asK2` over
this folder's: the closing is handed `K2.Stretch.carried l c n` below the sender's own number of
carried messages, `messageRows` the entry behind them. No count is named: each stands in the type of
c. -/
def carryBy (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers) (closing : K2.Closing)
    (p : K2.SwitchPlace) (w : Local W₀ Rc Xi Tr) (heard : List Fmt.Drawn)
    (l : List (String × Due)) (c : CsAll l) : Except String Johnson.Prover.Send.Rows :=
  (closing p (D w.x) (readers w) heard fun n =>
    if n < p.front.length then K2.Stretch.carried l c n
    else .error "a stretch is asked beyond the list").bind fun Wl =>
  (K2.Stretch.carried l c p.front.length).bind fun k =>
    K2.messageRows K2.freshTable p.sizes.codes (shapeL p) none
      (mainRows p.sizes Wl (fun _ _ _ => zeroG) 0) k

/-- **THE COUNT AT THE SEAM.** At a lent list l that begins with the job's members' counts,
`carryRows` at this folder's reader of l is `carryBy` at l. So each count that `asK2` lays is the
count of that entry of l: it stands in the type of c. -/
theorem carryRows_by_carried (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : K2.Closing) (p : K2.SwitchPlace) (w : Local W₀ Rc Xi Tr) (heard : List Fmt.Drawn)
    (l : List (String × Due)) (hb : Begins (membersL p) l) (c : CsAll l) :
    carryRows D readers closing p w heard (stretches l c) =
      carryBy D readers closing p w heard l c := by
  have h0 : K2.Stretch.carried l c p.front.length =
      .ok (asK2 (K2.messageDue p.sizes.codes (shapeL p) none) (stretches l c p.front.length)) := by
    obtain ⟨s, hs⟩ := hb p.front.length
      (⟨p.place, 0⟩, 0, K2.messageDue p.sizes.codes (shapeL p) none) (by simp [membersL])
    exact carried_asK2 l c _ _ hs
  unfold carryRows carryBy
  rw [h0]
  congr 1
  congr 1
  funext n
  by_cases hn : n < p.front.length
  · obtain ⟨s, hs⟩ := hb n p.front[n] (by simp [membersL, List.getElem?_append_left hn])
    rw [if_pos hn, carried_asK2 l c n _ hs, List.getElem?_eq_getElem hn]
  · rw [if_neg hn, List.getElem?_eq_none (by omega)]

/-! ## 3 What the test's two parts hand the job -/

/-- The second part's reader (`restCoins`, K12/Parts.lean) hands the job this folder's reader of the
part's own carried list, at what the part was lent. -/
theorem mem_rest {W X : Type} (J : TestJob W X)
    (c : Handed ⟨0, dueRest J.p.nums.stages⟩ [] (memberRuns J ⟨J.p.place, 1⟩ ++ [freshRun J])) :
    (restCoins J c).mem = stretches _ c.2.2 := rfl

section
variable {V : Type} (q : P12) (door : Local W₀ Rc Xi Tr → Front X → T12) (D : RowDataOf Xi)
  (readers : Local W₀ Rc Xi Tr → Readers) (closing : K2.Closing) (p : K2.SwitchPlace)

local notation "JL" => jobL q door D readers closing p

/-- The first part's reader (`firstRd`, K12/HalfSteps.lean) at this job likewise. -/
theorem mem_first_L (c : Handed ⟨0, 0⟩ [spentRun JL] (memberRuns JL ⟨q.place, 0⟩)) :
    (firstRd (V := V) JL c).mem = stretches _ c.2.2 := rfl

/-- **The seam at the first part**: `carryRows`, which `rowsL` and `treesL` call, at the first
part's reader and at any challenges heard, is `carryBy` at the list that the part states as carried
and at what it was lent under it. -/
theorem seam_first (w : Local W₀ Rc Xi Tr) (heard : List Fmt.Drawn)
    (c : Handed ⟨0, 0⟩ [spentRun JL] (memberRuns JL ⟨q.place, 0⟩)) :
    carryRows D readers closing p w heard (firstRd (V := V) JL c).mem =
      carryBy D readers closing p w heard (memberRuns JL ⟨q.place, 0⟩) c.2.2 :=
  carryRows_by_carried D readers closing p w heard _ (begins_first JL _) c.2.2

/-- **The seam at the second part.** -/
theorem seam_rest (w : Local W₀ Rc Xi Tr) (heard : List Fmt.Drawn)
    (c : Handed ⟨0, dueRest q.nums.stages⟩ [] (memberRuns JL ⟨q.place, 1⟩ ++ [freshRun JL])) :
    carryRows D readers closing p w heard (restCoins JL c).mem =
      carryBy D readers closing p w heard (memberRuns JL ⟨q.place, 1⟩ ++ [freshRun JL]) c.2.2 :=
  carryRows_by_carried D readers closing p w heard _ (begins_runs JL _ _) c.2.2

end

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.carried_asK2
#print axioms ProofFile.Honest.K12.AtProof.carried_beyond
#print axioms ProofFile.Honest.K12.AtProof.Begins
#print axioms ProofFile.Honest.K12.AtProof.begins_runs
#print axioms ProofFile.Honest.K12.AtProof.begins_first
#print axioms ProofFile.Honest.K12.AtProof.carryBy
#print axioms ProofFile.Honest.K12.AtProof.carryRows_by_carried
#print axioms ProofFile.Honest.K12.AtProof.mem_rest
#print axioms ProofFile.Honest.K12.AtProof.mem_first_L
#print axioms ProofFile.Honest.K12.AtProof.seam_first
#print axioms ProofFile.Honest.K12.AtProof.seam_rest
