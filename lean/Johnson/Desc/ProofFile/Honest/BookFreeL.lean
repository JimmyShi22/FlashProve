-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookFreeL.lean: A TEST OF ONE PASS BESIDE THE BOOK's MAKER's TEST OVER
ALL PAIRS, wantsFree (Honest/BookEntries.lean): wantsFreeL: every stretch lies within its message's
free entries, and, in the list's own order, each stretch that has an entry begins at or behind the
first number that is still free under its message's key; AND WHERE wantsFreeL ACCEPTS A LIST,
wantsFree ACCEPTS IT (wantsFreeL_sound), general in the list. Written by the authors of the honest
side of the linear claim's shared rounds (K14), in the frame's folder, not by the frame's authors;
the makers are theirs. Five definitions with code; tests at that file's synthetic lists; statements
with their proofs.

  MsgAt.key       a key of numbers in the message's stead: its sender's address, and where its
                  entries begin among that part's coins. Equal messages have equal keys; no string
                  is compared. Two messages with one key are held as one: that makes the test
                  stricter
  freeMarkAt, moveMark   the marks: for each key met so far the first number that is still free; the
                  latest key stands first; an elder pair with the same key, deeper in the list, is
                  never read
  wantsFreeFrom, wantsFreeL   the pass. A stretch of count 0 asks for no mark and moves none
  freeMarkAt_move   the mark behind a move: under the moved key the new number; under every other
                  key as before
  wantsFreeFrom_sound   where the pass from the marks T accepts: every stretch lies within its
                  message's free entries; each that has an entry begins at or behind T's mark of its
                  key; and the stretches stand pairwise in front of each other (InFront₀,
                  Honest/BookFreeOf.lean)
  wantsFreeL_sound   **wantsFreeL ws = true → wantsFree ws = true**: ONE DIRECTION: the converse
                  fails at the last test's list (a test, by evaluation: no theorem here says so)

STRICTER THAN wantsFree: it rejects a list whose stretches of one message that have an entry do not
stand in rising order (the last test below), and a list in which two messages have one key and their
stretches do not rise together. Stretches of count 0 may stand anywhere.
The lines that begin with `#guard` are tests, checked by evaluation: Lean's evaluator runs each of
them when the file is compiled, and the build fails if one is false. The kernel does not check them,
and they prove nothing.
force (Johnson/G/Eager.lean) hands a number on after it is evaluated; it turns no value (force_eq).
Kin. inTimeL beside BookPlan.inTime (Johnson/AtFull/ProofPlan/OneWalk.lean): a second text of a
test, made so that Lean's kernel can be asked it at a long list; there the two are equal; here not.
risingPlaces (Johnson/Desc/BookPlan.lean): a test of one pass at one key.
What is not claimed. That wantsFreeL accepts any maker's list. What it costs Lean's kernel at any
length. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.BookFreeOf
import Johnson.G.Eager

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

/-- A key of an oracle message as an owner: its sender's address, and where its entries begin among
that part's coins. Equal messages have equal keys; no string is compared. -/
def MsgAt.key (m : MsgAt) : Addr × Due := (m.owner, m.base)

/-- The mark under a key: the first number that is still free: of the first pair with that key; 0
where there is none. -/
def freeMarkAt : List ((Addr × Due) × Nat) → Addr × Due → Nat
  | [], _ => 0
  | x :: T, k => if x.1 = k then x.2 else freeMarkAt T k

/-- The mark under the key k moves to e: laid at the head; a pair at the head with that key goes. -/
def moveMark (T : List ((Addr × Due) × Nat)) (k : Addr × Due) (e : Nat) :
    List ((Addr × Due) × Nat) :=
  match T with
  | x :: T' => if x.1 = k then (k, e) :: T' else (k, e) :: x :: T'
  | [] => [(k, e)]

/-- One pass in the list's own order. T: the marks so far, the latest first. -/
def wantsFreeFrom : List ((Addr × Due) × Nat) → List Want → Bool
  | _, [] => true
  | T, w :: ws =>
    Johnson.G.force (w.number + w.count) fun e =>
      decide (e ≤ w.msg.free) &&
        (if w.count = 0 then wantsFreeFrom T ws
         else decide (freeMarkAt T w.msg.key ≤ w.number) &&
           wantsFreeFrom (moveMark T w.msg.key e) ws)

/-- **The test of one pass**: every stretch lies within its message's free entries, and, in the
list's own order, each stretch that has an entry begins at or behind the mark of its message's key.
STRICTER THAN wantsFree: it rejects a list whose stretches of one message that have an entry do not
stand in rising order, and a list in which two messages have one key and their stretches do not rise
together. -/
def wantsFreeL (ws : List Want) : Bool := wantsFreeFrom [] ws

/-! ## The law -/

/-- The mark behind a move: under the moved key the new number; under every other key as before. -/
theorem freeMarkAt_move (T : List ((Addr × Due) × Nat)) (k : Addr × Due) (e : Nat)
    (k' : Addr × Due) : freeMarkAt (moveMark T k e) k' = if k = k' then e else freeMarkAt T k' := by
  cases T with
  | nil => simp [moveMark, freeMarkAt]
  | cons x T' =>
    by_cases hx : x.1 = k
    · have e1 : moveMark (x :: T') k e = (k, e) :: T' := by simp [moveMark, hx]
      rw [e1]
      by_cases hk : k = k'
      · simp [freeMarkAt, hk]
      · have hx' : ¬ x.1 = k' := by rw [hx]; exact hk
        simp [freeMarkAt, hk, hx']
    · have e1 : moveMark (x :: T') k e = (k, e) :: x :: T' := by simp [moveMark, hx]
      rw [e1]
      by_cases hk : k = k'
      · simp [freeMarkAt, hk]
      · simp [freeMarkAt, hk]

/-- **Where the pass from the marks T accepts**: every stretch lies within its message's free
entries; each that has an entry begins at or behind T's mark of its key; the stretches stand
pairwise in front of each other. -/
theorem wantsFreeFrom_sound : ∀ (ws : List Want) (T : List ((Addr × Due) × Nat)),
    wantsFreeFrom T ws = true →
      (∀ w ∈ ws, w.number + w.count ≤ w.msg.free) ∧
      (∀ w ∈ ws, w.count ≠ 0 → freeMarkAt T w.msg.key ≤ w.number) ∧ ws.Pairwise InFront₀
  | [], _, _ => ⟨fun _ h => (nomatch h), fun _ h => (nomatch h), List.Pairwise.nil⟩
  | w :: ws, T, h => by
    unfold wantsFreeFrom at h
    rw [Johnson.G.force_eq, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have h1' : w.number + w.count ≤ w.msg.free := of_decide_eq_true h1
    by_cases hc : w.count = 0
    · rw [if_pos hc] at h2
      obtain ⟨a, b, c⟩ := wantsFreeFrom_sound ws T h2
      refine ⟨fun v hv => ?_, fun v hv hv0 => ?_, List.pairwise_cons.2 ⟨fun _ _ _ => Or.inl hc, c⟩⟩
      · rcases List.mem_cons.1 hv with rfl | hv
        · exact h1'
        · exact a v hv
      · rcases List.mem_cons.1 hv with rfl | hv
        · exact absurd hc hv0
        · exact b v hv hv0
    · rw [if_neg hc, Bool.and_eq_true] at h2
      obtain ⟨h3, h4⟩ := h2
      have h3' : freeMarkAt T w.msg.key ≤ w.number := of_decide_eq_true h3
      obtain ⟨a, b, c⟩ := wantsFreeFrom_sound ws _ h4
      refine ⟨fun v hv => ?_, fun v hv hv0 => ?_, List.pairwise_cons.2 ⟨fun v hv hm => ?_, c⟩⟩
      · rcases List.mem_cons.1 hv with rfl | hv
        · exact h1'
        · exact a v hv
      · rcases List.mem_cons.1 hv with rfl | hv
        · exact h3'
        · have q := b v hv hv0
          rw [freeMarkAt_move] at q
          by_cases hk : w.msg.key = v.msg.key
          · rw [if_pos hk] at q
            rw [← hk]
            omega
          · rw [if_neg hk] at q
            exact q
      · by_cases hv0 : v.count = 0
        · exact Or.inr (Or.inl hv0)
        · have q := b v hv hv0
          rw [freeMarkAt_move, if_pos (by rw [hm])] at q
          exact Or.inr (Or.inr q)

/-- **WHERE THE TEST OF ONE PASS ACCEPTS, THE TEST OVER ALL PAIRS ACCEPTS.** -/
theorem wantsFreeL_sound {ws : List Want} (h : wantsFreeL ws = true) : wantsFree ws = true :=
  wantsFree_of_inFront₀ (wantsFreeFrom_sound ws [] h).1 (wantsFreeFrom_sound ws [] h).2.2

/-! ### Tests at the synthetic lists of Honest/BookEntries.lean -/

-- it accepts where wantsFree accepts
#guard wantsFreeL toyWants.1
-- it rejects where the row has fewer free entries than the segment has scalars
#guard !wantsFreeL (segmentWants toySeg 0 { toyRow with free := 12 } toyIdx
  [⟨⟨1, some 0, 4, .K11⟩, 0⟩] 2).1
-- it rejects where two stretches meet
#guard !wantsFreeL (toyWants.1 ++ [⟨⟨⟨1, some 0, 9, .K9⟩, 0⟩, "scalars", toyRow, 4, 1⟩])
-- STRICTER: the same stretches in falling order: wantsFree accepts, this test rejects
#guard wantsFree toyWants.1.reverse && !wantsFreeL toyWants.1.reverse

end ProofFile.Honest

#print axioms ProofFile.Honest.freeMarkAt_move
#print axioms ProofFile.Honest.wantsFreeFrom_sound
#print axioms ProofFile.Honest.wantsFreeL_sound
