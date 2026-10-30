-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/Tie.lean: the tie of the two sides' roots, from its return:
for each of its steps the row that it leaves, with what `SumOut` says of its coefficients (on the
slots in front; that none on the step's own slots is 0; nothing on its end slots), and the form from
which it starts; and the slots that it passes on, as numbers. Definitions and theorems.

Terms. Honest/K3/GLOSSARY.md: see there stage, sumcheck, row, form, slot, ledger, hearing, sample
and tie. In this file: f is the lookup's face, lo the ledger's count of slots in front of the
lookup, rs the rounds. `Pos` and `SumOut` are those of Honest/K3/Good/Step.lean; `endOf` is that of
Honest/K3/Good/Levels.lean.

What is shown.
  `foldlM_range`: a fold of texts that hear, over the numbers below n, with an invariant by number.
  `e0`, `own_tie`, `endOf_tie`: the first end slots of the tie's steps, as numbers.
  `curOf`, `tieStart`, `planeSlot`: the chain's slot behind step k; the form in front of step t; the
    slot of the root of plane j.
  `TieOut`, `tie_out`: the tie.
Helpers: `foldlM_range'`, `tail_tie0`, `tail_tieS`, `first_tie_succ`, `TieAt`, `le_e0`,
`getD_push_lt`, `getD_push_eq` (these two stand, general in the type, under the same short names in
OnBytes/Tie/Pv/Lookup/Ends/FoPlaceTerm.lean [not in this library]).

Hypotheses that remain, in `tie_out`.
  `h2`: the face has at least two real planes.
  `hok`: every sampled element's words are below the prime (`Ok`, Levels.lean).
  `P`: the hearing stands in front of the tie's first step.
  `h`: the tie's hearing `tieV` returns.
In `endOf_tie` (without a name) and `first_tie_succ` (`h`): t + 1 < planes - 1. In `foldlM_range`:
`hs`, `h`, `hp`: each step keeps the invariant; the fold returns; the invariant holds at the start.
In `getD_push_lt`: `h`: i lies within the array. `foldlM_range'` has three hypotheses without a
name; `endOf_tie` has one: t + 1 < f.planes - 1.

Users. Honest/K3/Good/Trees.lean imports this file; Honest/K3/Good/Walk.lean calls `tie_out`;
Honest/K3/Good/Gives.lean names `planeSlot` and `curOf`.

Limits. The tie alone. The files under Honest/K3/Law/ count the same slots along a course under
names of their own (`endSlot`, `planeSlot`, `form`, Honest/K3/Law/Statements.lean; `cur`,
Honest/K3/Law/LookHeard.lean); no theorem of this file says that the two countings are one.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.Levels

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good
open OnBytes (E zeroE oneE subE mulE okE isZeroE)
open OnBytes.Model (Fork Aff Reading)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Call Ends Heard ownSlots)
open VerifiableInference.Desc.LinkJoin.ViaL (bindHr_some)
open VerifiableInference.Desc.K3 (Hr sumV tieV noVar)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Parts (In in_ofConst in_slot atP_tie)

variable {β : Type}

/-- A fold of texts that hear, over a stretch of numbers, with an invariant by number. -/
theorem foldlM_range' {g : β → Nat → Hr β} (P : Nat → β → Fork → List Fmt.RoundView → Prop) :
    ∀ (n a : Nat) (s : β) (F : Fork) (r : List Fmt.RoundView) (s' : β) (G : Fork) (r' : List Fmt.RoundView),
    (∀ k s F r s' G r', a ≤ k → k < a + n → g s k F r = some (s', G, r') → P k s F r →
      P (k + 1) s' G r') →
    (List.range' a n).foldlM g s F r = some (s', G, r') → P a s F r → P (a + n) s' G r'
  | 0, a, s, F, r, s', G, r', _, h, hp => by
    obtain ⟨x, y, z⟩ := pure_spec (a := s) h
    rw [x, y, z]
    exact hp
  | n + 1, a, s, F, r, s', G, r', hs, h, hp => by
    have h' : (g s a >>= fun t => (List.range' (a + 1) n).foldlM g t) F r = some (s', G, r') := h
    obtain ⟨t, F1, r1, h1, h2⟩ := bindHr_some h'
    have e : a + (n + 1) = a + 1 + n := by omega
    rw [e]
    exact foldlM_range' P n (a + 1) t F1 r1 s' G r'
      (fun k s F r s' G r' k1 k2 => hs k s F r s' G r' (by omega) (by omega)) h2
      (hs a s F r t F1 r1 (Nat.le_refl a) (by omega) h1 hp)

theorem foldlM_range {g : β → Nat → Hr β} (P : Nat → β → Fork → List Fmt.RoundView → Prop) {n : Nat}
    {s : β}
    {F : Fork} {r : List Fmt.RoundView} {s' : β} {G : Fork} {r' : List Fmt.RoundView}
    (hs : ∀ k s F r s' G r', k < n → g s k F r = some (s', G, r') → P k s F r → P (k + 1) s' G r')
    (h : (List.range n).foldlM g s F r = some (s', G, r')) (hp : P 0 s F r) : P n s' G r' := by
  rw [List.range_eq_range'] at h
  have := foldlM_range' P n 0 s F r s' G r'
    (fun k s F r s' G r' _ k2 => hs k s F r s' G r' (by omega)) h hp
  simpa using this

variable {f : LFace} {lo : Nat} {rs : List Fmt.RoundView}

/-! ## The numbers -/

/-- The first end slot of the tie's first step. -/
def e0 (f : LFace) (lo : Nat) : Nat := endOf f lo (.tie 0)

theorem own_tie (f : LFace) (t : Nat) : (Stage.tie t).own f = 4 := by cases t <;> rfl

theorem tail_tie0 (f : LFace) : (Stage.tie 0).tail f = 3 := rfl

theorem tail_tieS (f : LFace) (t : Nat) : (Stage.tie (t + 1)).tail f = 2 := rfl

theorem first_tie_succ {t : Nat} (h : t + 1 < f.planes - 1) :
    firstSlot f (.tie (t + 1)) = firstSlot f (.tie t) + (Stage.tie t).slots f := by
  have a := slotsIn_at (atP_tie f (j := t) (by omega))
  have b := slotsIn_at (atP_tie f (j := t + 1) h)
  have e : iTie f (t + 1) = iTie f t + 1 := by unfold iTie; omega
  rw [b.1, e, a.2, a.1]

/-- The first end slot of the tie's step t + 1, where that step is one of the row's
(t + 1 < planes - 1). -/
theorem endOf_tie : ∀ {t : Nat}, t + 1 < f.planes - 1 → endOf f lo (.tie (t + 1)) = e0 f lo + 6 * t
    + 7
  | 0, h => by
    unfold e0 endOf
    rw [first_tie_succ h, own_tie, own_tie]
    unfold Stage.slots
    rw [own_tie, tail_tie0]
    omega
  | t + 1, h => by
    have ih := endOf_tie (t := t) (by omega)
    unfold endOf at ih ⊢
    rw [first_tie_succ h, own_tie]
    unfold Stage.slots
    rw [own_tie, tail_tieS]
    rw [own_tie] at ih
    omega

/-- The chain's slot behind step number k. -/
def curOf (f : LFace) (lo : Nat) (k : Nat) : Nat := e0 f lo + 6 * k + 1

/-- The form in front of step number t. -/
def tieStart (f : LFace) (lo : Nat) : Nat → Aff
  | 0 => Aff.ofConst zeroE
  | t + 1 => Aff.slot (curOf f lo t)

/-- The slot of plane j's root. From the last plane's number on: the last plane's slot; at fewer
than two planes the difference planes - 2 is cut at 0. -/
def planeSlot (f : LFace) (lo : Nat) (j : Nat) : Nat :=
  if j + 1 < f.planes then e0 f lo + 6 * j + 2 else curOf f lo (f.planes - 2)

/-! ## The tie -/

/-- **What the tie leaves.** -/
structure TieOut (f : LFace) (lo : Nat) (rs : List Fmt.RoundView) (rows : Array Aff) (sZ : Nat)
    (sG : Array Nat) : Prop where
  row : ∀ t, t < f.planes - 1 → ∃ y ∈ rows.toList,
    SumOut f lo rs (.tie t) (tieStart f lo t) y (endOf f lo (.tie t))
  sZ : sZ = e0 f lo
  sG : ∀ j, j < f.planes → sG.getD j 0 = planeSlot f lo j

/-- What the tie's fold carries behind k of its steps. -/
structure TieAt (f : LFace) (lo : Nat) (rs : List Fmt.RoundView) (k : Nat)
    (s : Array Aff × Nat × Array Nat)
    (F : Fork) (rest : List Fmt.RoundView) : Prop where
  pos : Pos f lo rs (iTie f (k + 1)) F rest
  row : ∀ t, t ≤ k → ∃ y ∈ s.1.toList,
    SumOut f lo rs (.tie t) (tieStart f lo t) y (endOf f lo (.tie t))
  cur : s.2.1 = curOf f lo k
  top : F.next = e0 f lo + 6 * k + 3
  size : s.2.2.size = k + 1
  sG : ∀ j, j ≤ k → s.2.2.getD j 0 = e0 f lo + 6 * j + 2

theorem le_e0 (f : LFace) (lo : Nat) : lo ≤ e0 f lo := by
  unfold e0 endOf
  omega

theorem getD_push_lt (a : Array Nat) (y i : Nat) (h : i < a.size) : (a.push y).getD i 0 = a.getD i 0
    := by
  simp [Array.getD, Array.getElem_push, h, Nat.lt_succ_of_lt h]

theorem getD_push_eq (a : Array Nat) (y : Nat) : (a.push y).getD a.size 0 = y := by
  simp [Array.getD]

/-- **The tie, from its return.** -/
theorem tie_out {a : E} {F G : Fork} {rest rest' : List Fmt.RoundView} {rows : Array Aff} {sZ : Nat}
    {sG : Array Nat} (h2 : 2 ≤ f.planes) (hok : Ok rs) (P : Pos f lo rs (iTie f 0) F rest)
    (h : tieV f.planes a F rest = some ((rows, sZ, sG), G, rest')) :
    Pos f lo rs (iTie f (f.planes - 1)) G rest' ∧ TieOut f lo rs rows sZ sG ∧
      G.next = e0 f lo + 6 * (f.planes - 2) + 3 := by
  unfold tieV at h
  obtain ⟨x, F1, r1, e1', h⟩ := bindHr_some h
  obtain ⟨s, F2, r2, e2', h⟩ := bindHr_some h
  obtain ⟨hh, hG, hr⟩ := pure_spec h
  simp only [Prod.mk.injEq] at hh
  obtain ⟨q1, q2, q3⟩ := hh
  subst q1 q2 q3 hG hr
  have hlo : lo ≤ F.next := by rw [P.next]; omega
  obtain ⟨p1, o1, _, n1⟩ := sum_step (k := noVar 3 3) (atP_tie f (j := 0) (by omega)) rfl rfl rfl
    rfl
    (fun v hv => by simp [noVar] at hv) hok P (in_ofConst lo F.next zeroE) e1'
  have n1' : F1.next = x.1.sEnd + 3 := n1
  have hx : x.1.sEnd = e0 f lo := o1.sEnd
  have start : TieAt f lo rs 0 (#[x.2], x.1.sEnd + 1, #[x.1.sEnd + 2]) F1 r1 := by
    refine ⟨p1, ?_, ?_, ?_, rfl, ?_⟩
    · intro t ht
      obtain rfl : t = 0 := by omega
      refine ⟨x.2, by simp, ?_⟩
      have := o1
      rw [hx] at this
      exact this
    · show x.1.sEnd + 1 = _
      rw [hx]
      rfl
    · omega
    · intro j hj
      obtain rfl : j = 0 := by omega
      show x.1.sEnd + 2 = _
      rw [hx]
  have fin := foldlM_range (fun k s F r => TieAt f lo rs k s F r) (n := f.planes - 2)
    (by
      intro k s F r s' G' r' hk hstep I
      obtain ⟨y, F3, r3, e3, hstep⟩ := bindHr_some hstep
      obtain ⟨w1, w2, w3⟩ := pure_spec hstep
      subst w1 w2 w3
      have hk1 : k + 1 < f.planes - 1 := by omega
      have hC : In lo F.next (Aff.slot s.2.1) := by
        rw [I.cur]
        exact in_slot (by have := le_e0 f lo; unfold curOf; omega)
          (by rw [I.top]; unfold curOf; omega)
      obtain ⟨p2, o2, _, n2⟩ := sum_step (k := noVar 3 2) (atP_tie f hk1) rfl rfl rfl rfl
        (fun v hv => by simp [noVar] at hv) hok I.pos hC e3
      have n2' : G'.next = y.1.sEnd + 2 := n2
      have hy : y.1.sEnd = e0 f lo + 6 * k + 7 := by rw [o2.sEnd]; exact endOf_tie hk1
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · have e : iTie f (k + 1 + 1) = iTie f (k + 1) + 1 := by unfold iTie; omega
        rw [e]
        exact p2
      · intro t ht
        by_cases htk : t ≤ k
        · obtain ⟨z, hz, hS⟩ := I.row t htk
          exact ⟨z, mem_push_of hz, hS⟩
        · obtain rfl : t = k + 1 := by omega
          refine ⟨y.2, mem_push_self _ _, ?_⟩
          have := o2
          rw [I.cur, o2.sEnd] at this
          exact this
      · show y.1.sEnd = _
        rw [hy]
        unfold curOf
        omega
      · omega
      · show (s.2.2.push (y.1.sEnd + 1)).size = _
        rw [Array.size_push, I.size]
      · intro j hj
        show (s.2.2.push (y.1.sEnd + 1)).getD j 0 = _
        by_cases hjk : j ≤ k
        · rw [getD_push_lt _ _ _ (by rw [I.size]; omega)]
          exact I.sG j hjk
        · obtain rfl : j = k + 1 := by omega
          have := getD_push_eq s.2.2 (y.1.sEnd + 1)
          rw [I.size] at this
          rw [this, hy]
          omega)
    e2' start
  have hw : f.planes - 2 + 1 = f.planes - 1 := by omega
  refine ⟨?_, ⟨?_, hx, ?_⟩, ?_⟩
  · have := fin.pos
    rw [hw] at this
    exact this
  · intro t ht
    exact fin.row t (by omega)
  · intro j hj
    unfold planeSlot
    by_cases hj1 : j + 1 < f.planes
    · rw [if_pos hj1, getD_push_lt _ _ _ (by rw [fin.size]; omega)]
      exact fin.sG j (by omega)
    · obtain rfl : j = f.planes - 2 + 1 := by omega
      have := getD_push_eq s.2.2 s.2.1
      rw [fin.size] at this
      rw [if_neg hj1, this, fin.cur]
  · exact fin.top

end ProofFile.Honest.K3.Good

#print axioms ProofFile.Honest.K3.Good.foldlM_range'
#print axioms ProofFile.Honest.K3.Good.foldlM_range
#print axioms ProofFile.Honest.K3.Good.own_tie
#print axioms ProofFile.Honest.K3.Good.tail_tie0
#print axioms ProofFile.Honest.K3.Good.tail_tieS
#print axioms ProofFile.Honest.K3.Good.first_tie_succ
#print axioms ProofFile.Honest.K3.Good.endOf_tie
#print axioms ProofFile.Honest.K3.Good.le_e0
#print axioms ProofFile.Honest.K3.Good.getD_push_lt
#print axioms ProofFile.Honest.K3.Good.getD_push_eq
#print axioms ProofFile.Honest.K3.Good.tie_out
