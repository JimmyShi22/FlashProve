-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Key/KeyLay.lean: THE KEY FILE's TABLES: THE MAP ON WITNESSES THAT LAYS, ONCE, GENERAL IN THE CHAIN. A row that CLOSES a pin (the proximity tests) must name, for a witness behind, the witness in front: the same, but that the messages whose pins the row closes are
LAID: message k AND THE PAD AT k's SEAT become one table tbl k.
  layAt at_ l tbl w        the witness w with, for each k of l, message k := tbl k, and the pad at the seat at_ k := tbl k; the cells, the token, every other message and every other seat's pad as they were
  SeatsApart at_ l l'      no message of l' sits at the seat of a message of l but itself: (public: a fact on at_)
  layAt_msg | layAt_msg_off | layAt_cells    what it holds
  laysSeat_layAt           PROVED: it holds one table as message k and as the pad at k's seat (KeyLetters.LaysSeat), where the seats of l are apart
  msgOf_layAt              PROVED: so, under ArrOk and LayIdem, WHAT PIN k PINS AT THE LAID WITNESS IS tbl k
  msgOf_layAt_off          PROVED: THE RIDERS: at the seat of a message k' outside l, apart from l's seats, what PIN k' pins is what it pinned at w
  reads_layAt | reads_layAt_off   PROVED: the like of what the rows read (KRead.of), under ReadsPinned
WHO CALLS IT: whoever pays 1.15 · 2.9 · 2.10 · 3.2: E a b w := layAt at_ ‹the row's «lays»› ‹the tables that the kind's law hands out› w. WHAT IT DOES NOT SAY: where the tables come from (left to K12's files) · that an item which reads the record rides (that is the row's) · the cells' laying at 2.1 (another component: { w with cells := … }: no seat).
Nothing on soundness.
-/
import Johnson.Desc.Key.KeyLetters

set_option autoImplicit false

namespace VerifiableInference.Desc.Key

variable {Cells M : Type}

/-- **The witness with the messages of l laid: each as a message and as the pad at its seat.** -/
def layAt (at_ : Where) (l : List Nat) (tbl : Nat → M) (w : Wit Cells Unit M) : Wit Cells Unit M :=
  { w with
    msg := fun k => if k ∈ l then tbl k else w.msg k
    pad := fun j t => match l.find? (fun k => at_ k == (j, t)) with
      | some k => tbl k
      | none => w.pad j t }

/-- No message of l' sits at the seat of a message of l, but that message itself. -/
def SeatsApart (at_ : Where) (l l' : List Nat) : Prop := ∀ k ∈ l, ∀ k' ∈ l', at_ k = at_ k' → k = k'

theorem layAt_cells (at_ : Where) (l : List Nat) (tbl : Nat → M) (w : Wit Cells Unit M) : (layAt at_ l tbl w).cells = w.cells := rfl

theorem layAt_msg (at_ : Where) (l : List Nat) (tbl : Nat → M) (w : Wit Cells Unit M) (k : Nat) (hk : k ∈ l) : (layAt at_ l tbl w).msg k = tbl k := by
  show (if k ∈ l then tbl k else w.msg k) = tbl k
  rw [if_pos hk]

theorem layAt_msg_off (at_ : Where) (l : List Nat) (tbl : Nat → M) (w : Wit Cells Unit M) (k : Nat) (hk : k ∉ l) : (layAt at_ l tbl w).msg k = w.msg k := by
  show (if k ∈ l then tbl k else w.msg k) = w.msg k
  rw [if_neg hk]

theorem layAt_pad (at_ : Where) (l : List Nat) (tbl : Nat → M) (w : Wit Cells Unit M) (h : SeatsApart at_ l l) (k : Nat) (hk : k ∈ l) :
    (layAt at_ l tbl w).pad (at_ k).1 (at_ k).2 = tbl k := by
  show (match l.find? (fun k' => at_ k' == ((at_ k).1, (at_ k).2)) with | some k' => tbl k' | none => w.pad (at_ k).1 (at_ k).2) = tbl k
  cases hf : l.find? (fun k' => at_ k' == ((at_ k).1, (at_ k).2)) with
  | none =>
    have := List.find?_eq_none.1 hf k hk
    simp at this
  | some k' =>
    have h1 : k' ∈ l := List.mem_of_find?_eq_some hf
    have h2 := List.find?_some hf
    have h3 : at_ k' = at_ k := by simpa using h2
    rw [h k' h1 k hk h3]

theorem layAt_pad_off (at_ : Where) (l : List Nat) (tbl : Nat → M) (w : Wit Cells Unit M) (j t : Nat) (h : ∀ k ∈ l, at_ k ≠ (j, t)) :
    (layAt at_ l tbl w).pad j t = w.pad j t := by
  show (match l.find? (fun k' => at_ k' == (j, t)) with | some k' => tbl k' | none => w.pad j t) = w.pad j t
  have hf : l.find? (fun k' => at_ k' == (j, t)) = none := List.find?_eq_none.2 fun k hk => by simpa using h k hk
  rw [hf]

theorem laysSeat_layAt (at_ : Where) (l : List Nat) (tbl : Nat → M) (w : Wit Cells Unit M) (h : SeatsApart at_ l l) : LaysSeat at_ l (layAt at_ l tbl w) := fun k hk => by
  rw [layAt_pad at_ l tbl w h k hk, layAt_msg at_ l tbl w k hk]

section
variable {A Smp Rec : Type} (G : Reading A Cells M Smp Rec)

/-- **What PIN k pins at the laid witness is the laid table.** -/
theorem msgOf_layAt (at_ : Where) (l : List Nat) (tbl : Nat → M) (w : Wit Cells Unit M) (ha : ArrOk G at_ l) (hi : LayIdem G) (h : SeatsApart at_ l l) :
    ∀ k ∈ l, msgOf G (layAt at_ l tbl w) (at_ k).1 (at_ k).2 = tbl k := fun k hk =>
  (msgOf_of_laysSeat G at_ l _ ha hi (laysSeat_layAt at_ l tbl w h) k hk).trans (layAt_msg at_ l tbl w k hk)

/-- **The riders**: at the seat of a message outside l, apart from l's seats, nothing turns. -/
theorem msgOf_layAt_off (at_ : Where) (l l' : List Nat) (tbl : Nat → M) (w : Wit Cells Unit M) (ha : ArrOk G at_ l') (hd : ∀ k' ∈ l', k' ∉ l) (h : SeatsApart at_ l l') :
    ∀ k' ∈ l', msgOf G (layAt at_ l tbl w) (at_ k').1 (at_ k').2 = msgOf G w (at_ k').1 (at_ k').2 := fun k' hk' => by
  unfold msgOf
  rw [ha k' hk', layAt_msg_off at_ l tbl w k' (hd k' hk'),
    layAt_pad_off at_ l tbl w _ _ fun k hk e => hd k' hk' ((h k hk k' hk' e) ▸ hk)]

theorem reads_layAt (at_ : Where) (R : KRead Cells M) (l : List Nat) (tbl : Nat → M) (w : Wit Cells Unit M) (ha : ArrOk G at_ l) (hr : ReadsPinned G at_ R l) (hi : LayIdem G)
    (h : SeatsApart at_ l l) : ∀ k ∈ l, R.of (layAt at_ l tbl w) k = tbl k := fun k hk =>
  (hr _ k hk).trans (msgOf_layAt G at_ l tbl w ha hi h k hk)

theorem reads_layAt_off (at_ : Where) (R : KRead Cells M) (l l' : List Nat) (tbl : Nat → M) (w : Wit Cells Unit M) (ha : ArrOk G at_ l') (hr : ReadsPinned G at_ R l')
    (hd : ∀ k' ∈ l', k' ∉ l) (h : SeatsApart at_ l l') : ∀ k' ∈ l', R.of (layAt at_ l tbl w) k' = R.of w k' := fun k' hk' =>
  ((hr _ k' hk').trans (msgOf_layAt_off G at_ l l' tbl w ha hd h k' hk')).trans (hr w k' hk').symm

end

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.laysSeat_layAt
#print axioms VerifiableInference.Desc.Key.msgOf_layAt
#print axioms VerifiableInference.Desc.Key.msgOf_layAt_off
#print axioms VerifiableInference.Desc.Key.reads_layAt
#print axioms VerifiableInference.Desc.Key.reads_layAt_off
