-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookHeadStretch.lean: the maker of the book of coins (`ProverCoinCounts`,
Honest/Frame.lean), sixteenth file: THE LONGEST HEAD OF A LIST OF ENTRIES THAT IS ONE STRETCH OF ONE
SENDER's COINS, WITH THE REST. A row whose parts spend of two messages is no one stretch
(`oneStretch`, Honest/BookStretch.lean, says no); what it spends may still BEGIN with one.
Definitions with code, tests at synthetic entries, and statements with proofs, by induction on the
list.

  `headWalk`          the walk: the count, the entries taken, the rest
  `headStretch`      of a list that is not empty: (the owner, the first coin's number, the count),
                    the head, the rest
  `headWalk_split`, `headWalk_run`   the walk's two laws
  `headStretch_of`   where it yields (x, es₁, es₂): `es = es₁ ++ es₂` and `oneStretch es₁ = some x`
  `headStretch_whole`   where `oneStretch es = some x`: it yields (x, es, [])

Limits. «The longest» is not stated: only that the head is one stretch and that head and rest make
up the list; the tests below show at synthetic entries that the walk stops at the first entry that
does not go on. Coins of the extension field alone, as Honest/BookStretch.lean. Nothing on a coin's
value, a run or a measure. This file proves nothing about soundness, completeness, hiding or any
other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.BookStretch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

/-- The walk: o: the owner. s: the first coin's number. c: how many coins so far. It yields the
count, the entries that go on the stretch, and the rest, from the first entry on that does not. -/
def headWalk (o : Addr) (s : Nat) : Nat → List Ahead → Nat × List Ahead × List Ahead
  | c, [] => (c, [], [])
  | c, f :: fs =>
    if f.owner = o ∧ f.start.e = s + c then
      let r := headWalk o s (c + f.count.e) fs
      (r.1, f :: r.2.1, r.2.2)
    else (c, [], f :: fs)

/-- **The head that is one stretch, and the rest.** -/
def headStretch : List Ahead → Option ((Addr × Nat × Nat) × List Ahead × List Ahead)
  | [] => none
  | e :: es =>
    let r := headWalk e.owner e.start.e e.count.e es
    some ((e.owner, e.start.e, r.1), e :: r.2.1, r.2.2)

theorem headWalk_pos {o : Addr} {s c : Nat} {f : Ahead} (fs : List Ahead)
    (h : f.owner = o ∧ f.start.e = s + c) :
    headWalk o s c (f :: fs) = ((headWalk o s (c + f.count.e) fs).1,
      f :: (headWalk o s (c + f.count.e) fs).2.1, (headWalk o s (c + f.count.e) fs).2.2) := by
  rw [headWalk, if_pos h]

theorem headWalk_neg {o : Addr} {s c : Nat} {f : Ahead} (fs : List Ahead)
    (h : ¬(f.owner = o ∧ f.start.e = s + c)) : headWalk o s c (f :: fs) = (c, [], f :: fs) := by
  rw [headWalk, if_neg h]

/-- Head and rest make up the list. -/
theorem headWalk_split (o : Addr) (s : Nat) : ∀ (fs : List Ahead) (c : Nat),
    (headWalk o s c fs).2.1 ++ (headWalk o s c fs).2.2 = fs
  | [], _ => rfl
  | f :: fs, c => by
    by_cases h : f.owner = o ∧ f.start.e = s + c
    · rw [headWalk_pos fs h]
      show f :: ((headWalk o s (c + f.count.e) fs).2.1 ++ (headWalk o s (c + f.count.e) fs).2.2) =
        f :: fs
      rw [headWalk_split o s fs]
    · rw [headWalk_neg fs h]
      rfl

/-- The head goes on the stretch, up to the count. -/
theorem headWalk_run (o : Addr) (s : Nat) : ∀ (fs : List Ahead) (c : Nat),
    runOn o s c (headWalk o s c fs).2.1 = some (headWalk o s c fs).1
  | [], _ => rfl
  | f :: fs, c => by
    by_cases h : f.owner = o ∧ f.start.e = s + c
    · rw [headWalk_pos fs h]
      show runOn o s c (f :: (headWalk o s (c + f.count.e) fs).2.1) =
        some (headWalk o s (c + f.count.e) fs).1
      rw [runOn, if_pos h]
      exact headWalk_run o s fs _
    · rw [headWalk_neg fs h]
      rfl

/-- **Where it yields: head and rest make up the list, and the head is one stretch.** -/
theorem headStretch_of {es es₁ es₂ : List Ahead} {x : Addr × Nat × Nat}
    (h : headStretch es = some (x, es₁, es₂)) : es = es₁ ++ es₂ ∧ oneStretch es₁ = some x := by
  cases es with
  | nil => cases h
  | cons e es =>
    have h' : ((e.owner, e.start.e, (headWalk e.owner e.start.e e.count.e es).1),
        e :: (headWalk e.owner e.start.e e.count.e es).2.1,
        (headWalk e.owner e.start.e e.count.e es).2.2) = (x, es₁, es₂) := Option.some.inj h
    cases h'
    refine ⟨?_, ?_⟩
    · show e :: es = e :: ((headWalk e.owner e.start.e e.count.e es).2.1 ++
        (headWalk e.owner e.start.e e.count.e es).2.2)
      rw [headWalk_split]
    · show (runOn e.owner e.start.e e.count.e (headWalk e.owner e.start.e e.count.e es).2.1).map
        (fun c => (e.owner, e.start.e, c)) = _
      rw [headWalk_run]
      rfl

/-- Where the walk over the whole list yields, the head is the whole list. -/
theorem headWalk_whole (o : Addr) (s : Nat) : ∀ (fs : List Ahead) (c c' : Nat),
    runOn o s c fs = some c' → headWalk o s c fs = (c', fs, [])
  | [], c, c', h => by
    have e : c = c' := Option.some.inj h
    subst e
    rfl
  | f :: fs, c, c', h => by
    by_cases hc : f.owner = o ∧ f.start.e = s + c
    · rw [runOn, if_pos hc] at h
      rw [headWalk_pos fs hc, headWalk_whole o s fs _ _ h]
    · rw [runOn, if_neg hc] at h
      cases h

/-- Where the whole list is one stretch. -/
theorem headStretch_whole {es : List Ahead} {x : Addr × Nat × Nat} (h : oneStretch es = some x) :
    headStretch es = some (x, es, []) := by
  cases es with
  | nil => cases h
  | cons e es =>
    have h' : (runOn e.owner e.start.e e.count.e es).map (fun c => (e.owner, e.start.e, c)) =
        some x := h
    cases hr : runOn e.owner e.start.e e.count.e es with
    | none =>
      rw [hr] at h'
      cases h'
    | some c =>
      rw [hr] at h'
      have e' : (e.owner, e.start.e, c) = x := Option.some.inj h'
      subst e'
      show some ((e.owner, e.start.e, (headWalk e.owner e.start.e e.count.e es).1),
        e :: (headWalk e.owner e.start.e e.count.e es).2.1,
        (headWalk e.owner e.start.e e.count.e es).2.2) = _
      rw [headWalk_whole _ _ es _ _ hr]

/-! ### Tests at synthetic entries -/

namespace BookHeadStretchToy

def o : Addr := ⟨⟨1, some 0, 1, .K1⟩, 0⟩
def o' : Addr := ⟨⟨1, some 0, 4, .K1⟩, 0⟩
def sp : Addr := ⟨⟨1, some 0, 3, .K4⟩, 0⟩
def en (w : Addr) (s c : Nat) : Ahead :=
  { name := "a run", owner := w, start := ⟨0, s⟩, count := ⟨0, c⟩, spender := sp, once := true }

/-- What is looked at: the triple and the two lengths. -/
def short (es : List Ahead) : Option ((Addr × Nat × Nat) × Nat × Nat) :=
  (headStretch es).map fun x => (x.1, x.2.1.length, x.2.2.length)

-- two entries go on; the third is another owner's; the fourth would go on again and is in the rest
#guard short [en o 5 2, en o 7 3, en o' 0 1, en o 10 1] == some ((o, 5, 5), 2, 2)
-- a gap stops the walk
#guard short [en o 5 2, en o 8 3] == some ((o, 5, 2), 1, 1)
-- the whole list; one entry; no entry
#guard short [en o 5 2, en o 7 3] == some ((o, 5, 5), 2, 0)
#guard short [en o 5 2] == some ((o, 5, 2), 1, 0) && (short []).isNone

end BookHeadStretchToy

end ProofFile.Honest

#print axioms ProofFile.Honest.headWalk_pos
#print axioms ProofFile.Honest.headWalk_neg
#print axioms ProofFile.Honest.headWalk_split
#print axioms ProofFile.Honest.headWalk_run
#print axioms ProofFile.Honest.headStretch_of
#print axioms ProofFile.Honest.headWalk_whole
#print axioms ProofFile.Honest.headStretch_whole
