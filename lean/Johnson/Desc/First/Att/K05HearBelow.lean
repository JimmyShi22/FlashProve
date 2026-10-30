-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05HearBelow.lean: kind K5: THE HEARING WRITES NOTHING BELOW THE NEXT FREE
NUMBER OF THE LEDGER IN FRONT, and turns of the ledger nothing but that number and the three arrays
on slots.

Why. A table of borders holds, in its promise behind the kind's block, clauses on the ledger that
were made in front of the block: "the slots of the lookup's sumcheck over the leaves are still
free"; "a slot that a run will fill late is free". `Stays` (Att/K5Said.lean) says that what lies
under a slot stays. It does not say that a free slot stays free. This file does, for the slots below
the next free number.

Main names:
  `bare F`: the ledger without its next free number and its three arrays on slots.
  `Below F G`: F.next ≤ G.next; bare G = bare F; at every slot j < F.next the three arrays of G
    read as those of F (the marks at every default).
  `Below.refl`, `Below.trans`, `Below.ns`, `Below.trees`.
  `take_below`, `sum_below`, `takes_below`, `units_below`: from the verb's return itself, at a
    sized ledger: the ledger behind is sized and Below holds.
  `hear_below`: **where `hear` x (F, rs, lead) returns (h, G, rs', lead') and F is sized: G is sized
    and Below F G.**
  `free_below`: so a stretch that ends at or below F.next and is free in F is free in G.
  `put_below`: and below F.next, what lies under a slot in G lay there in F (the converse of Stays).
  `below_bites`: a control: a ledger that differs from F in one mark below F.next is not Below F.

Premises: Sized F; the hearing's return.
Limits. Nothing on the slots from F.next on: `room_behind` (Att/K05Room.lean) speaks of those.
Nothing on what a value under a slot means. That the hearing returns is not shown here. EMPTY AT: a
ledger with F.next = 0 (the third clause says nothing there).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Room

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Free)

/-- The ledger without its next free number and its three arrays on slots. -/
def bare (F : Fork) : Fork := { F with next := 0, gotF := #[], vp := #[], mf := #[] }

/-- G holds, below F's next free number, just what F holds; and beside the next free number and the
three arrays on slots it is F. -/
def Below (F G : Fork) : Prop :=
  F.next ≤ G.next ∧ bare G = bare F ∧ ∀ j, j < F.next → G.vp.getD j zeroE = F.vp.getD j zeroE ∧
    G.mf.getD j zeroE = F.mf.getD j zeroE ∧ ∀ d, G.gotF.getD j d = F.gotF.getD j d

theorem Below.refl (F : Fork) : Below F F := ⟨Nat.le_refl _, rfl, fun _ _ => ⟨rfl, rfl, fun _ => rfl⟩⟩

theorem Below.trans {F G H : Fork} (a : Below F G) (b : Below G H) : Below F H :=
  ⟨Nat.le_trans a.1 b.1, b.2.1.trans a.2.1, fun j hj => by
    obtain ⟨p1, p2, p3⟩ := a.2.2 j hj
    obtain ⟨q1, q2, q3⟩ := b.2.2 j (Nat.lt_of_lt_of_le hj a.1)
    exact ⟨q1.trans p1, q2.trans p2, fun d => (q3 d).trans (p3 d)⟩⟩

theorem Below.ns {F G : Fork} (a : Below F G) : G.ns = F.ns := congrArg (·.ns) a.2.1
theorem Below.trees {F G : Fork} (a : Below F G) : G.trees = F.trees := congrArg (·.trees) a.2.1

/-- A run of hidden values turns the three arrays alone. -/
theorem filled_bare {F G : Fork} {first : Nat} {l : List E} {factor : E}
    (a : Filled F G first l factor) : bare G = bare F :=
  Eq.trans (congrArg bare a.frame) rfl

/-- n scalars are taken. -/
theorem take_below {n j lead lead' : Nat} {F G : Fork} {rs rs' : List Fmt.RoundView}
    (h : take n (F, rs, lead) = some (j, G, rs', lead')) (hz : Sized F) : Sized G ∧ Below F G := by
  obtain ⟨_, _, _, r, rest, v, _, _, _, hG⟩ := take_spec h
  have fill := hideRun_ok _ _ _ _ _ hG ⟨hz.vp, hz.mf, hz.got⟩
  refine ⟨fill.sized, ?_, Eq.trans (filled_bare fill) rfl, fun j hj => fill.other j (Or.inl hj)⟩
  rw [fill.next]
  exact Nat.le_add_right _ _

/-- A sumcheck is heard. -/
theorem sum_below {C : Aff} {vs : List Var} {e : Ends} {hh : MaskedSum.Heard} {lead lead' : Nat}
    {F G : Fork} {rs rs' : List Fmt.RoundView}
    (h : sum C (.sum vs e) (F, rs, lead) = some (hh, G, rs', lead')) (hz : Sized F) :
    Sized G ∧ Below F G := by
  obtain ⟨_, _, G1, f, a1, a2⟩ := sum_spec h
  obtain ⟨_, T, Rd, _, _, b3, b4⟩ := MaskedSum.hear_spec a1
  have F1 := hideRun_ok _ _ _ _ _ b4 ⟨hz.vp, hz.mf, hz.got⟩
  have F2 := hideRun_ok _ _ _ _ _ (row_write a2) F1.sized
  have hfirst : hh.first = F.next := by rw [b3]
  refine ⟨F2.sized, ?_, (filled_bare F2).trans (Eq.trans (filled_bare F1) rfl), fun j hj => ?_⟩
  · rw [F2.next, F1.next]
    exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  · obtain ⟨p1, p2, p3⟩ := F1.other j (Or.inl (Nat.lt_of_lt_of_le hj (Nat.le_add_right _ _)))
    obtain ⟨q1, q2, q3⟩ := F2.other j (Or.inl (by rw [hfirst]; exact hj))
    exact ⟨q1.trans p1, q2.trans p2, fun d => (q3 d).trans (p3 d)⟩

/-- The plane messages' scalars are taken. -/
theorem takes_below : ∀ (n : Nat) (js : List Nat) (s s' : St), TakesRan 3 n js s s' → Sized s.1 →
    Sized s'.1 ∧ Below s.1 s'.1
  | 0, [], _, _, h, hz => by
    have e : _ = _ := h
    rw [e]
    exact ⟨hz, Below.refl _⟩
  | n + 1, _ :: js, ⟨F, rs, lead⟩, s', ⟨⟨F1, rs1, l1⟩, h1, h2⟩, hz => by
    obtain ⟨z1, b1⟩ := take_below h1 hz
    obtain ⟨z2, b2⟩ := takes_below n js _ s' h2 z1
    exact ⟨z2, b1.trans b2⟩
  | 0, _ :: _, _, _, h, _ => h.elim
  | _ + 1, [], _, _, h, _ => h.elim

/-- The units of the scores are heard. -/
theorem units_below : ∀ (us : List (Nat × Nat)) (os : List (Nat × MaskedSum.Heard)) (s s' : St),
    UnitsRan us os s s' → Sized s.1 → Sized s'.1 ∧ Below s.1 s'.1
  | [], [], _, _, h, hz => by
    have e : _ = _ := h
    rw [e]
    exact ⟨hz, Below.refl _⟩
  | u :: us, _ :: os, ⟨F, rs, lead⟩, s', ⟨s2, ⟨⟨F1, rs1, l1⟩, h1, h2⟩, h3⟩, hz => by
    obtain ⟨F2, rs2, l2⟩ := s2
    obtain ⟨z1, b1⟩ := take_below h1 hz
    obtain ⟨z2, b2⟩ := sum_below h2 z1
    obtain ⟨z3, b3⟩ := units_below us os _ s' h3 z2
    exact ⟨z3, (b1.trans b2).trans b3⟩
  | [], _ :: _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, h, _ => h.elim

/-- **The kind's hearing writes nothing below the next free number of the ledger in front.** -/
theorem hear_below {x : Params.AttentionRounds} {F G : Fork} {rs rs' : List Fmt.RoundView}
    {lead lead' : Nat} {h : Heard} (hh : hear x (F, rs, lead) = some (h, G, rs', lead'))
    (hz : Sized F) : Sized G ∧ Below F G := by
  obtain ⟨sa, sb, ⟨F1, r1, l1⟩, ⟨F2, r2, l2⟩, ⟨F3, r3, l3⟩, ⟨F4, r4, l4⟩, ⟨F5, r5, l5⟩, ⟨F6, r6, l6⟩, ⟨F7, r7, l7⟩,
    ⟨F8, r8, l8⟩, ⟨F9, r9, l9⟩, ⟨F10, r10, l10⟩, ⟨F11, r11, l11⟩, ⟨F12, r12, l12⟩, ⟨F13, r13, l13⟩,
    ⟨F14, r14, l14⟩, ⟨F15, r15, l15⟩, pt, ha, hb, h1, h2, h3, h4, h5, h6, h7, h8, h9, _, h10, h11, h12, h13, h14,
    h15, h16⟩ := (hear_ran hh).ran
  obtain ⟨Fb, rb, lb⟩ := sb
  have e5 := (batch_spec h5).1
  have e9 := (close_spec h9).1
  have e11 := (batch_spec h11).1
  have e13 := (batch_spec h13).1
  have e15 := (batch_spec h15).1
  subst e5 e9 e11 e13 e15
  obtain ⟨za, ba⟩ := takes_below _ _ _ sa ha hz
  obtain ⟨zb, bb⟩ := units_below _ _ _ _ hb za
  obtain ⟨z1, b1⟩ := take_below h1 zb
  obtain ⟨z2, b2⟩ := take_below h2 z1
  obtain ⟨z3, b3⟩ := take_below h3 z2
  obtain ⟨z4, b4⟩ := sum_below h4 z3
  obtain ⟨z6, b6⟩ := take_below h6 z4
  obtain ⟨z7, b7⟩ := sum_below h7 z6
  obtain ⟨z8, b8⟩ := sum_below h8 z7
  obtain ⟨z10, b10⟩ := take_below h10 z8
  obtain ⟨z12, b12⟩ := sum_below h12 z10
  obtain ⟨z14, b14⟩ := sum_below h14 z12
  obtain ⟨z16, b16⟩ := sum_below h16 z14
  exact ⟨z16, ba.trans (bb.trans (b1.trans (b2.trans (b3.trans (b4.trans (b6.trans (b7.trans
    (b8.trans (b10.trans (b12.trans (b14.trans b16)))))))))))⟩

/-- **A stretch that ends at or below the next free number in front and is free there stays
free.** -/
theorem free_below {F G : Fork} (b : Below F G) (zG : Sized G) {a n : Nat} (hn : a + n ≤ F.next)
    (hf : Free F a n) : Free G a n :=
  ⟨zG.got, by rw [b.ns]; exact hf.2.1, fun j h1 h2 => by
    rw [(b.2.2 j (Nat.lt_of_lt_of_le h2 hn)).2.2 true]
    exact hf.2.2 j h1 h2⟩

/-- Below the next free number in front, what lies under a slot behind lay there in front. -/
theorem put_below {F G : Fork} (b : Below F G) {j : Nat} (hj : j < F.next) {y f : E}
    (h : Put G j y f) : Put F j y f := by
  obtain ⟨p1, p2, p3⟩ := b.2.2 j hj
  exact ⟨(p3 false).symm.trans h.1, p1.symm.trans h.2.1, p2.symm.trans h.2.2⟩

/-- A control: a ledger with another mark at a slot below F.next is not Below F. -/
theorem below_bites {F G : Fork} {j : Nat} (hj : j < F.next)
    (hd : G.gotF.getD j false ≠ F.gotF.getD j false) : ¬ Below F G :=
  fun b => hd ((b.2.2 j hj).2.2 false)

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.take_below
#print axioms VerifiableInference.Desc.First.Att.P.sum_below
#print axioms VerifiableInference.Desc.First.Att.P.hear_below
#print axioms VerifiableInference.Desc.First.Att.P.free_below
#print axioms VerifiableInference.Desc.First.Att.P.put_below
#print axioms VerifiableInference.Desc.First.Att.P.below_bites
