-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/Keep/PadExact.lean: The kind "lookup" (K3): WHICH SLOTS ARE FILLED BEHIND A
HEARING, BOTH WAYS: just those that were filled in front and the lookup's own, but for the leaves'
stretch. Statements and proofs.

Why. The library's record PadLeft (OnBytes/Tie/Pv/Lookup/Port/FoHeard.lean) says below the ledger's
next slot one way alone: what was filled stays filled. That a slot there which was FREE stays free
is not to be drawn from it. Its proof (pad_left, Johnson/Top/H/FlPort/FoPadLeft.lean) holds both
ways in hand. This file is that proof's sister, under the same premises, and its carriage up to the
kind's decide.

Main names:
  PadExact h F F' g: the leaves' stretch begins at or above F.next and ends within the lookup's
    slots; a slot is filled in F' just if it was filled in F or is one of the lookup's slots
    outside the leaves' stretch; the leaves' sumcheck's walk has 1 + 2 d + 5 members: as many as
    the run "planes" fills.
  pad_exact: the sister of pad_left. lkPad_exact: of the library's flat copy, wherever it returns
    from a ledger that has its sizes. decide_exact: of K3.block's decide, with "the ledger behind
    is later" (at any rounds: no premise on their words).
  PadExact.writesAbove: so the hearing turns no mark below F.next.
  PadExact.owed: so, where nothing at or above F.next was filled, the leaves' stretch is owed
    behind the hearing (SlotsOwed, OnBytes/Tie/Pv/Psc/PscRoom.lean).

Limits. From a return alone. Marks alone: nothing on what lies under a slot (PadLeft has that).
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3DecideHearsAt
import OnBytes.Tie.Pv.Psc.PscRoom
import OnBytes.Tie.Pv.Lookup.Forest.FoR5Ends

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open TwV FoNums OnBytes OnBytes.Model OnBytes.PscRun

/-- **Which slots are filled behind a hearing.** -/
structure PadExact (h : Forest.Shape) (F F' : Fork) (g : Forest.Heard) : Prop where
  next : F'.next = F.next + Forest.elems h
  first : F.next ≤ g.leaves.first
  within : g.leaves.first + (1 + 2 * h.d + 5) ≤ F.next + Forest.elems h
  marks : ∀ j, Filled F' j ↔ Filled F j ∨ (F.next ≤ j ∧ j < F.next + Forest.elems h ∧
    ¬ (g.leaves.first ≤ j ∧ j < g.leaves.first + (1 + 2 * h.d + 5)))
  len : g.leaves.walk.1.length = 1 + 2 * h.d + 5

/-- The sister of pad_left: its premises but the two that this does not need, and the walk's
length. -/
theorem pad_exact {calls : Array Call} {pub : Array Nat} {lid : ℕ} {F F' : Fork} {c c' : Tape}
    {g : Forest.Heard} {M : PadMid} (P : PadCut calls pub lid F c g F' c' M) (nA nB : ℕ)
    (sA : Stretch (owed3 F) M.F7 nA)
    (sB : Stretch (took M.F7 (1 + 2 * (M.h pub).d + 5)) M.G8 nB)
    (hlv : M.lv.first = M.F7.next) (hlen : M.lv.walk.1.length = 1 + 2 * (M.h pub).d + 5) :
    PadExact (M.h pub) F F' g := by
  obtain ⟨nL, hnL⟩ : ∃ nL, nL = 1 + 2 * (M.h pub).d + 5 := ⟨_, rfl⟩
  rw [← hnL] at sB
  have h7 : M.F7.next = F.next + nA := sA.next
  have h8 : M.G8.next = F.next + nA + nL + nB := by
    rw [sB.next]
    show M.F7.next + nL + nB = _
    rw [h7]
  have hel : Forest.elems (M.h pub) = nA + nL + nB := by
    have := P.slots
    omega
  have hfirst : g.leaves.first = F.next + nA := by
    rw [P.heard]
    show M.lv.first = _
    rw [hlv, h7]
  have fA : ∀ j, Filled M.F7 j ↔ Filled F j ∨ (F.next ≤ j ∧ j < F.next + nA) := sA.filled
  have fB : ∀ j, Filled M.G8 j ↔
      Filled M.F7 j ∨ (F.next + nA + nL ≤ j ∧ j < F.next + nA + nL + nB) := by
    intro j
    have := sB.filled j
    rw [show (took M.F7 nL).next = F.next + nA + nL by show M.F7.next + nL = _; rw [h7]] at this
    exact this
  have hlen' : g.leaves.walk.1.length = 1 + 2 * (M.h pub).d + 5 := by
    rw [P.heard]
    exact hlen
  rw [P.fork]
  refine ⟨P.slots, by omega, by omega, fun j => ?_, hlen'⟩
  rw [fB, fA, hfirst, hel, ← hnL]
  constructor
  · rintro ((hj | hj) | hj)
    · exact Or.inl hj
    · exact Or.inr ⟨hj.1, by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩
  · rintro (hj | ⟨h1, h2, h3⟩)
    · exact Or.inl (Or.inl hj)
    · by_cases hA : j < F.next + nA
      · exact Or.inl (Or.inr ⟨h1, hA⟩)
      · exact Or.inr ⟨by omega, by omega⟩

/-- **Of the library's flat copy**, wherever it returns from a ledger that has its sizes. -/
theorem lkPad_exact (calls : Array Call) (pub : Array Nat) (lid : ℕ) (F F' : Fork) (t u : Tape)
    (g : Forest.Heard) (h : lkPad calls pub lid F t = some (g, F', u)) (hF : Sized F) :
    PadExact g.shape F F' g := by
  have h' : lkPad calls pub lid F t = .ok ((g, F'), u) := h
  obtain ⟨M, P⟩ := pad_cut calls pub lid F F' t u g h'
  have hg : g.shape = M.h pub := pad_shape P
  have H : FoNums.ok (M.h pub) = true := Cb.Fo.shape_ok P.shape (_root_.Fo.ask_ok P.ask)
  obtain ⟨l, scs, ptT, lvK, lvT, rowsK, rowsT, evK, evT, D, R⟩ :=
    pad_read Reading.gl P hF trivial 5 H
  have e : 1 + (5 + (M.h pub).d + (M.h pub).d) = 1 + 2 * (M.h pub).d + 5 := by omega
  have hw := walk_len R.r5.ranL (by
    intro h0
    have := congrArg List.length h0
    simp [zdL, zdOf] at this)
  have hsum : (dgOf (zdL (5 + (M.h pub).d) (M.h pub).d M.table.rho)).sum =
      5 + (M.h pub).d + (M.h pub).d := slotsOf_zdL _ _ _ (by omega)
  rw [hg]
  exact pad_exact P _ _
    ((R.f4 ▸ R.tieSt).trans ((⟨R.keys.same, R.keys.filled, R.keys.out⟩ :
      Stretch M.F5 M.F6 _).trans ⟨R.table.same, R.table.filled, R.table.out⟩))
    (e ▸ R.r5.stretch) R.r5.lvFirst (by rw [hw, hsum]; omega)

/-- The hearing turns no mark below the next slot of the ledger in front. -/
theorem PadExact.writesAbove {h : Forest.Shape} {F F' : Fork} {g : Forest.Heard}
    (P : PadExact h F F' g) : WritesAbove F F' :=
  ⟨by rw [P.next]; exact Nat.le_add_right _ _, fun j hj => by
    rw [P.marks]
    exact ⟨fun x => x.elim id fun y => absurd y.1 (by omega), Or.inl⟩⟩

/-- Where nothing at or above the next slot was filled, the leaves' stretch is owed behind the
hearing. -/
theorem PadExact.owed {h : Forest.Shape} {F F' : Fork} {g : Forest.Heard}
    (P : PadExact h F F' g) (hA : FreeAbove F) :
    SlotsOwed F' g.leaves.first (1 + 2 * h.d + 5) :=
  ⟨by rw [P.next]; exact P.within, fun j h1 h2 hf =>
    ((P.marks j).1 hf).elim (hA j (Nat.le_trans P.first h1)) fun y => y.2.2 ⟨h1, h2⟩⟩

end Fo.Tp

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.K.Kc OnBytes.PscRun
open VerifiableInference.Desc.First.Tape (flRun flRun_holds)

/-- **Of K3.block's decide.** -/
theorem decide_exact {S Cl : Type} (seat : Desc.K3.Seat S Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (s s' : S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block seat piece laid before p guests).decide s rs cols = .ok s') :
    ∃ (F : Fork) (x : Forest.Heard × Fork), seat.fork s = some F ∧ seat.heard s = none ∧
      s' = seat.put s x.1 x.2 ∧
      (Sized F → _root_.Fo.Tp.PadExact x.1.shape F x.2 x.1 ∧ Later F x.2) := by
  obtain ⟨F, x, hF, hn, hx, rfl⟩ := decide_ok seat piece laid before p guests s s' rs cols hd
  refine ⟨F, x, hF, hn, rfl, fun hS => ?_⟩
  unfold Desc.K3.hear at hx
  cases hsh : p.shape with
  | none => simp [hsh] at hx
  | some h =>
    simp only [hsh] at hx
    split at hx
    · rename_i hNC
      obtain ⟨t, ht, hm⟩ := (flRun_holds _ _ _ _ _ _ _ _).1
        (show flRun {} (Desc.K3.messages h) (p.entries.getD []) F rs = some (x.1, x.2) from hx)
      have hl := messagesCut p.calls p.pub p.lid h F t _ (shape_some p h hsh) hNC hm
      obtain ⟨_, _, _, hlaw⟩ :=
        _root_.Fo.Tp.lkPad_law Reading.gl p.calls p.pub p.lid 5 F x.2 t [] x.1 hl
      obtain ⟨_, P, _⟩ := hlaw hS
      exact ⟨_root_.Fo.Tp.lkPad_exact p.calls p.pub p.lid F x.2 t [] x.1 hl hS,
        ⟨by rw [P.next]; exact Nat.le_add_right _ _, P.rest.2.1, fun _ => P.fit, P.keep⟩⟩
    · exact absurd hx (by simp)

end VerifiableInference.OnPublicFiles

#print axioms Fo.Tp.pad_exact
#print axioms Fo.Tp.lkPad_exact
#print axioms Fo.Tp.PadExact.writesAbove
#print axioms Fo.Tp.PadExact.owed
#print axioms VerifiableInference.OnPublicFiles.decide_exact
