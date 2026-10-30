-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Shape/Window.lean: the invariant of the walk along a lookup's
hearing, for the sentences "the hearing returns" of this folder: a window of the ledger's slots.
One structure; theorems.

Terms. Honest/K3/GLOSSARY.md: see there window (of the ledger's slots), ledger, slot, sumcheck, form
and shape (of the ledger).

What is shown.
  `Win lo a hi F`: the ledger's arrays have their size; the count of slots stands at a; the slots up
    to hi are there; from a to hi all are free; from lo to a all are filled.
  `ready_of_win`: it gives the library's promise in front of a masked sumcheck (`LedgerReady`,
    Johnson/Desc/Part/MaskedSumReady.lean) at a start form that names slots between lo and a alone.
  `win_sum`, `win_left`, `win_owe`: how a step of the hearing on the ledger's shape (`Went`,
    Honest/K3/Shape/Walk.lean) carries it on.
  `win_of_freeB`: a test with code on the ledger's shape gives it in front of the lookup.
Helpers: `filled_iff`, `fillB_get`, `fillB_length`.
At a sumcheck that is left open (`win_left`) its own slots stay free: so "filled from lo on" is
given up there: the window begins anew behind them.

Hypotheses that remain.
  `h`: the window in front; in `win_of_freeB`, the test `freeB`.
  `hC`, `hr`: the start form names slots between lo and a alone; there is room up to hi.
  `hG`: the step on the ledger's shape.

Users. Honest/K3/Shape/ClosedMarks.lean [not in this library] and Honest/K3/Shape/Returns.lean
import this file.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
Nothing on any value under a slot.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Shape.Closed
import Johnson.Desc.ProofFile.Honest.K3.Shape.Walk
import Johnson.Desc.ProofFile.Honest.K3.Parts.NamesOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Shape
open OnBytes.Model (Fork Aff)
open OnBytes.PscRun (Sized Filled)
open VerifiableInference.Desc.First.Shape (LedSh ledSh fillB freeB sizedB free_get sized_of_B)
open VerifiableInference.Desc.Part.MaskedSum (Call ownSlots LedgerReady)
open ProofFile.Honest.K3.Parts (In)

/-- **The window**: the ledger's arrays have their size; the count of slots stands at a; the slots
up to hi are there; from a to hi all are free; from lo to a all are filled. -/
structure Win (lo a hi : Nat) (F : Fork) : Prop where
  sized : Sized F
  next : F.next = a
  room : hi ≤ F.ns
  free : ∀ j, a ≤ j → j < hi → ¬ Filled F j
  filled : ∀ j, lo ≤ j → j < a → Filled F j

theorem filled_iff (F : Fork) (j : Nat) : Filled F j ↔ (ledSh F).got[j]?.getD false = true := by
  unfold Filled
  show F.gotF.getD j false = true ↔ F.gotF.toList[j]?.getD false = true
  rw [Array.getElem?_toList, Array.getD_eq_getD_getElem?]

/-- What lies at a place of a list of marks in which a run has been filled. Conditional on the run
lying inside the list. -/
theorem fillB_get (got : List Bool) (first n j : Nat) (h : first + n ≤ got.length) :
    (fillB got first n)[j]?.getD false =
      if first ≤ j ∧ j < first + n then true else got[j]?.getD false := by
  unfold fillB
  by_cases h1 : j < first
  · rw [List.append_assoc, List.getElem?_append_left (by rw [List.length_take]; omega),
      List.getElem?_take_of_lt h1, if_neg (by omega)]
  · by_cases h2 : j < first + n
    · rw [List.getElem?_append_left (by simp; omega),
        List.getElem?_append_right (by rw [List.length_take]; omega), if_pos (by omega),
        List.getElem?_replicate, if_pos (by rw [List.length_take]; omega)]
      rfl
    · rw [List.getElem?_append_right (by simp; omega), if_neg (by omega), List.getElem?_drop]
      congr 2
      simp
      omega

theorem fillB_length (got : List Bool) (first n : Nat) (h : first + n ≤ got.length) :
    (fillB got first n).length = got.length := by
  unfold fillB
  simp
  omega

/-- **The window gives the library's promise in front of a masked sumcheck.** Conditional on the
window, a start form on its filled slots and room. No instance of these hypotheses is exhibited in
this file. -/
theorem ready_of_win {lo a hi : Nat} {F : Fork} {C : Aff} {k : Call} (h : Win lo a hi F)
    (hC : In lo a C) (hr : a + ownSlots k.all + k.endsN ≤ hi) : LedgerReady C k F := by
  have hroom := h.room
  refine ⟨h.sized, fun x hx => ?_, by rw [h.next]; omega, fun j h1 h2 => ?_⟩
  · obtain ⟨x1, x2⟩ := hC x hx
    exact ⟨by omega, h.filled _ x1 x2⟩
  · rw [h.next] at h1 h2
    exact h.free j h1 (by omega)

/-- Behind a masked sumcheck with end values, its row made at once. Conditional on the window, the
step on the ledger's shape and room. No instance of these hypotheses is exhibited in this file. -/
theorem win_sum {lo a hi o e : Nat} {F G : Fork} (h : Win lo a hi F) (hG : Went F G [.sum o e])
    (hr : a + o + e ≤ hi) : Win lo (a + o + e) hi G := by
  obtain ⟨hS, hE⟩ := hG
  have hroom := h.room
  have hlen : (ledSh F).got.length = F.ns := by
    show F.gotF.toList.length = F.ns
    rw [Array.length_toList]
    exact h.sized.2.2
  have hn : G.next = F.next + o + e := congrArg LedSh.next hE
  have hns : G.ns = F.ns := congrArg LedSh.ns hE
  have hg : (ledSh G).got =
      fillB (fillB (ledSh F).got (F.next + o) e) F.next o := congrArg LedSh.got hE
  have hget : ∀ j, (ledSh G).got[j]?.getD false =
      if a ≤ j ∧ j < a + o + e then true else (ledSh F).got[j]?.getD false := by
    intro j
    rw [hg, h.next, fillB_get _ _ _ _ (by rw [fillB_length _ _ _ (by omega)]; omega),
      fillB_get _ _ _ _ (by omega)]
    by_cases c1 : a ≤ j ∧ j < a + o
    · rw [if_pos c1, if_pos (by omega)]
    · rw [if_neg c1]
      by_cases c2 : a + o ≤ j ∧ j < a + o + e
      · rw [if_pos c2, if_pos (by omega)]
      · rw [if_neg c2, if_neg (by omega)]
  refine ⟨hS, by rw [hn, h.next], by rw [hns]; exact hroom, fun j h1 h2 => ?_, fun j h1 h2 => ?_⟩
  · rw [filled_iff, hget, if_neg (by omega), ← filled_iff]
    exact h.free j (by omega) h2
  · rw [filled_iff, hget]
    by_cases c : a ≤ j
    · rw [if_pos ⟨c, h2⟩]
    · rw [if_neg (by omega), ← filled_iff]
      exact h.filled j h1 (by omega)

/-- Behind a masked sumcheck that is left open: the window begins anew behind its own slots.
Conditional on the window and the step on the ledger's shape. No instance of these hypotheses is
exhibited in this file. -/
theorem win_left {lo a hi o : Nat} {F G : Fork} (h : Win lo a hi F) (hG : Went F G [.left o]) :
    Win (a + o) (a + o) hi G := by
  obtain ⟨hS, hE⟩ := hG
  have hn : G.next = F.next + o := congrArg LedSh.next hE
  have hns : G.ns = F.ns := congrArg LedSh.ns hE
  have hg : (ledSh G).got = (ledSh F).got := (congrArg LedSh.got hE).trans rfl
  refine ⟨hS, by rw [hn, h.next], by rw [hns]; exact h.room, fun j h1 h2 => ?_,
    fun j h1 h2 => absurd h2 (by omega)⟩
  rw [filled_iff, hg, ← filled_iff]
  exact h.free j (by omega) h2

/-- A claim more on the list of owed claims changes no slot. Conditional on the window and the step
on the ledger's shape. No instance of these hypotheses is exhibited in this file. -/
theorem win_owe {lo a hi : Nat} {F G : Fork} (h : Win lo a hi F) (hG : Went F G [.owe]) :
    Win lo a hi G := by
  obtain ⟨hS, hE⟩ := hG
  have hn : G.next = F.next := congrArg LedSh.next hE
  have hns : G.ns = F.ns := congrArg LedSh.ns hE
  have hg : (ledSh G).got = (ledSh F).got := (congrArg LedSh.got hE).trans rfl
  refine ⟨hS, by rw [hn, h.next], by rw [hns]; exact h.room, fun j h1 h2 => ?_,
    fun j h1 h2 => ?_⟩
  · rw [filled_iff, hg, ← filled_iff]
    exact h.free j h1 h2
  · rw [filled_iff, hg, ← filled_iff]
    exact h.filled j h1 h2

/-- **A test with code on the ledger's shape gives the window in front of a lookup.** Conditional on
that test. No instance of these hypotheses is exhibited in this file. -/
theorem win_of_freeB {F : Fork} {n : Nat} (h : freeB (ledSh F) F.next n = true) :
    Win F.next F.next (F.next + n) F := by
  unfold freeB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨sized_of_B h.1.1, rfl, h.1.2, fun j h1 h2 => ?_, fun j h1 h2 => absurd h2 (by omega)⟩
  rw [filled_iff]
  have e := free_get (ledSh F).got F.next n h.2 (j - F.next) (by omega)
  rw [show F.next + (j - F.next) = j by omega] at e
  rw [e]
  exact Bool.false_ne_true

end ProofFile.Honest.K3.Shape

#print axioms ProofFile.Honest.K3.Shape.filled_iff
#print axioms ProofFile.Honest.K3.Shape.fillB_get
#print axioms ProofFile.Honest.K3.Shape.fillB_length
#print axioms ProofFile.Honest.K3.Shape.ready_of_win
#print axioms ProofFile.Honest.K3.Shape.win_sum
#print axioms ProofFile.Honest.K3.Shape.win_left
#print axioms ProofFile.Honest.K3.Shape.win_owe
#print axioms ProofFile.Honest.K3.Shape.win_of_freeB
