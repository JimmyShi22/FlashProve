-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameCarryFenceEnds.lean: THE FENCE `CarryFence` AT THE STATE THAT THE WAY IN
`doorZ Z m` RETURNS, WHEREVER THE SWITCH STANDS: the premise hF of `carry_goesBack_door` | `_head` |
`_finish` | `_sameZ` (FrameCarryEnds.lean), to the letter, from the same four facts on the state in
front that `fence_of_in_link` | `fence_of_in_data` (FrameCarryFence.lean,
FrameCarryKey.lean) take where the switch stands at a link. Statements and proofs.

What is said.
  `DoorReads p s s'`: s' has s's book and number of roots, and the carried rows of the switch's
front
    at s' ARE those of the frame of s's LIVE copy of the calls' state (`s.live.frame.rows`: the
    letters of the field rowsSent of `FoldFacts`).
  `finishFront_rows`: the finish's front's maker leaves the frame's carried rows.
  `headFrontQ_reads`, `finishFrontQ_reads`: what the head's and the finish's fronts return of a
    state u: u's book and number of roots; the front's rows are u's walk's copy's.
  `doorReads_link`, `doorReads_head`, `doorReads_finish`: **so at each of the three sorts of
place.**
  `fence_of_reads`: the fence at s' from the four facts on s, `DoorReads` and the fact on the keys.
  `fence_of_in_door`: **hF, GENERAL IN In, AT ALL THREE SORTS**; `fence_of_in_doorData`: with the
fact
    on the keys paid by `key_below` (the proof file's rounds have data; base ≤ D.t₁).

Limits. At `.head`: the state in front does not stand at the head's link (from In): at an unopened
head's link the way in hands the state back, whose front's frame is the head's own copy a.fr: of its
rows nothing is said here. The four facts are premises, had from what is known in front. No
soundness statement.

-/
import Johnson.Top.H0.Walk.FrameCarryEnds
import Johnson.Top.H0.Walk.FrameCarryKey

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 frontAt par9 headFrontQ finishFrontQ headFrontOf
  finFrontOf)
open VerifiableInference.Desc.First.K2Caller
open _root_.Tw.K2 (firstFront finishFront Front)

/-- What the way in's answer s' reads of s. -/
structure DoorReads (p : P2) (s s' : S) : Prop where
  book : s'.book = s.book
  roots : s'.roots = s.roots
  rows : ∀ fx, frontAt p s' = some fx → fx.f.rows = s.live.frame.rows

/-- The finish's front's maker leaves the frame's carried rows. -/
theorem finishFront_rows {St : Statement} {f : ReqFrame} {x : Front}
    (h : finishFront St f = .ok x) : x.f.rows = f.rows := by
  unfold finishFront at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · obtain rfl := Except.ok.inj h
        rfl

/-- **What the head's front returns.** -/
theorem headFrontQ_reads {p : P2} (hp : p.stands = .head) (tl : HTailF2) {u s' : S}
    (h : headFrontQ tl u = .ok s') :
    s'.book = u.book ∧ s'.roots = u.roots ∧
      ∀ fx, frontAt p s' = some fx → fx.f.rows = u.check.frame.rows := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := u
  unfold headFrontQ at h
  cases here with
  | between =>
    simp only [S.atBetween, Bool.not_true, Bool.false_eq_true, if_false] at h
    by_cases hd : firstDue check = true
    · simp only [hd, Bool.not_true, Bool.false_eq_true, if_false] at h
      cases hx : firstFront st check.frame with
      | error e =>
        rw [hx] at h
        cases h
      | ok x =>
        rw [hx] at h
        cases hm : failed with
        | some mk =>
          simp [Except.bind, S.enterHead?, S.enterHead, S.atBetween, S.unmarked, hm] at h
        | none =>
          simp only [Except.bind, S.enterHead?, S.enterHead, S.atBetween, S.unmarked, hm,
            if_true] at h
          obtain rfl := Except.ok.inj h
          refine ⟨rfl, rfl, fun fx hfx => ?_⟩
          unfold frontAt at hfx
          simp only [hp] at hfx
          obtain ⟨G, _, rfl⟩ := Option.map_eq_some_iff.1 hfx
          show x.f.rows = check.frame.rows
          exact firstFront_rows hx
    · simp [hd] at h
  | _ => simp [S.atBetween] at h

/-- **What the finish's front returns.** -/
theorem finishFrontQ_reads {p : P2} (hp : p.stands = .finish) {u s' : S}
    (h : finishFrontQ u = .ok s') :
    s'.book = u.book ∧ s'.roots = u.roots ∧
      ∀ fx, frontAt p s' = some fx → fx.f.rows = u.check.frame.rows := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := u
  unfold finishFrontQ at h
  cases here with
  | between =>
    simp only [S.atBetween, Bool.not_true, Bool.false_eq_true, if_false] at h
    by_cases hd : finishDue check = true
    · simp only [hd, Bool.not_true, Bool.false_eq_true, if_false] at h
      cases hG : check.frame.groups[check.frame.link]? with
      | none =>
        rw [hG] at h
        cases hx : finishFront st check.frame <;> simp [hx] at h
      | some G =>
        cases hx : finishFront st check.frame with
        | error e =>
          rw [hG, hx] at h
          cases h
        | ok x =>
          rw [hG, hx] at h
          cases hm : failed with
          | some mk =>
            simp [Except.bind, S.enterFin?, S.enterFin, S.atBetween, S.unmarked, hm] at h
          | none =>
            simp only [Except.bind, S.enterFin?, S.enterFin, S.atBetween, S.unmarked, hm,
              if_true] at h
            obtain rfl := Except.ok.inj h
            refine ⟨rfl, rfl, fun fx hfx => ?_⟩
            unfold frontAt at hfx
            simp only [hp, Option.map_some, Option.some.injEq] at hfx
            subst hfx
            show x.f.rows = check.frame.rows
            exact finishFront_rows hx
    · simp [hd] at h
  | _ => simp [S.atBetween] at h

/-- At a link. -/
theorem doorReads_link {Z : ProofFile.Pub} {m : ℕ} (hp : (ProofFile.pAtK2 Z m).stands = .link) {s s' : S}
    (h : doorZ Z m s = some s') : DoorReads (ProofFile.pAtK2 Z m) s s' := by
  unfold doorZ at h
  rw [hp] at h
  obtain rfl : rest s = s' := Option.some.inj h
  refine ⟨rest_book s, rest_roots s, fun fx hfx => ?_⟩
  unfold frontAt at hfx
  rw [hp] at hfx
  dsimp only at hfx
  rw [firstFront_rows (toOption_some hfx), rest_frame]

/-- At the head's link's switch. -/
theorem doorReads_head {Z : ProofFile.Pub} {m : ℕ} (hp : (ProofFile.pAtK2 Z m).stands = .head) {s s' : S}
    (hs : ∀ a, s.here ≠ .head a) (h : doorZ Z m s = some s') :
    DoorReads (ProofFile.pAtK2 Z m) s s' := by
  rw [doorZ_head hp hs] at h
  obtain ⟨h1, h2, h3⟩ := headFrontQ_reads hp {} (toOption_some h)
  exact ⟨h1.trans (rest_book s), h2.trans (rest_roots s),
    fun fx hfx => (h3 fx hfx).trans (congrArg (·.rows) (rest_frame s))⟩

/-- At the finish's switch. -/
theorem doorReads_finish {Z : ProofFile.Pub} {m : ℕ} (hp : (ProofFile.pAtK2 Z m).stands = .finish) {s s' : S}
    (h : doorZ Z m s = some s') : DoorReads (ProofFile.pAtK2 Z m) s s' := by
  rw [doorZ_finish hp] at h
  obtain ⟨h1, h2, h3⟩ := finishFrontQ_reads hp (toOption_some h)
  exact ⟨h1.trans (rest_book s), h2.trans (rest_roots s),
    fun fx hfx => (h3 fx hfx).trans (congrArg (·.rows) (rest_frame s))⟩

/-- **The fence at s', from four facts on s.** -/
theorem fence_of_reads (Z : ProofFile.Pub) (m base : ℕ) {s s' : S}
    (hD : DoorReads (ProofFile.pAtK2 Z m) s s')
    (h1 : VerifiableInference.Desc.K12.Door.atFirstBook (par9 (ProofFile.pAtK2 Z m)).firstTree s = true)
    (h2 : VerifiableInference.Desc.K12.Door.atFirstFits s = true)
    (h3 : ∀ o ∈ singleRowsOracles s.live.frame.rows, o < s.book.place.size)
    (h4 : s.book.trees.size ≤ base)
    (hKey : ∀ k L, k < base →
      (ProofFile.allAt Z).find? (fun L => ProofFile.keyAt Z L.no == k) = some L → L.no < base) :
    CarryFence Z m base s' := by
  refine carryFence_of Z m base s' ?_ ?_ ?_ ?_ hKey
  · unfold VerifiableInference.Desc.K12.Door.atFirstBook at h1 ⊢
    rw [hD.book, hD.roots]
    exact h1
  · unfold VerifiableInference.Desc.K12.Door.atFirstFits at h2 ⊢
    rw [hD.book]
    exact h2
  · intro fx hfx o ho
    rw [hD.rows fx hfx] at ho
    rw [hD.book]
    exact h3 o ho
  · rw [hD.book]
    exact h4

/-- **THE PREMISE hF OF THE RULES OF FrameCarryEnds.lean, TO THE LETTER: GENERAL IN In, WHEREVER THE
SWITCH STANDS.** -/
theorem fence_of_in_door {P : Type} (Z : ProofFile.Pub) (m base : ℕ) (In : P × S → Strs → Prop)
    (hIn : ∀ p s y, In (p, s) y →
      VerifiableInference.Desc.K12.Door.atFirstBook (par9 (ProofFile.pAtK2 Z m)).firstTree s = true ∧
      VerifiableInference.Desc.K12.Door.atFirstFits s = true ∧
      (∀ o ∈ singleRowsOracles s.live.frame.rows, o < s.book.place.size) ∧
      s.book.trees.size ≤ base)
    (hH : (ProofFile.pAtK2 Z m).stands = .head → ∀ p s y, In (p, s) y → ∀ a, s.here ≠ .head a)
    (hKey : ∀ k L, k < base →
      (ProofFile.allAt Z).find? (fun L => ProofFile.keyAt Z L.no == k) = some L → L.no < base) :
    ∀ p s y s', In (p, s) y → doorZ Z m s = some s' → CarryFence Z m base s' := by
  intro p s y s' hI hd
  obtain ⟨h1, h2, h3, h4⟩ := hIn p s y hI
  have hD : DoorReads (ProofFile.pAtK2 Z m) s s' := by
    cases hs : (ProofFile.pAtK2 Z m).stands with
    | link => exact doorReads_link hs hd
    | head => exact doorReads_head hs (hH hs p s y hI) hd
    | finish => exact doorReads_finish hs hd
  exact fence_of_reads Z m base hD h1 h2 h3 h4 hKey

/-- **The same, the fact on the keys paid by the file's data.** -/
theorem fence_of_in_doorData {P : Type} (Z : ProofFile.Pub) (D : WholeD) (hW : ProofFile.wholeAt Z = some D)
    (m base : ℕ) (hb : base ≤ D.t₁) (In : P × S → Strs → Prop)
    (hIn : ∀ p s y, In (p, s) y →
      VerifiableInference.Desc.K12.Door.atFirstBook (par9 (ProofFile.pAtK2 Z m)).firstTree s = true ∧
      VerifiableInference.Desc.K12.Door.atFirstFits s = true ∧
      (∀ o ∈ singleRowsOracles s.live.frame.rows, o < s.book.place.size) ∧
      s.book.trees.size ≤ base)
    (hH : (ProofFile.pAtK2 Z m).stands = .head → ∀ p s y, In (p, s) y → ∀ a, s.here ≠ .head a) :
    ∀ p s y s', In (p, s) y → doorZ Z m s = some s' → CarryFence Z m base s' :=
  fence_of_in_door Z m base In hIn hH (key_below Z D hW base hb)

end Johnson.Desc.First.Walk.Tied

#print axioms Johnson.Desc.First.Walk.Tied.headFrontQ_reads
#print axioms Johnson.Desc.First.Walk.Tied.finishFrontQ_reads
#print axioms Johnson.Desc.First.Walk.Tied.doorReads_link
#print axioms Johnson.Desc.First.Walk.Tied.doorReads_head
#print axioms Johnson.Desc.First.Walk.Tied.doorReads_finish
#print axioms Johnson.Desc.First.Walk.Tied.fence_of_reads
#print axioms Johnson.Desc.First.Walk.Tied.fence_of_in_door
#print axioms Johnson.Desc.First.Walk.Tied.fence_of_in_doorData
