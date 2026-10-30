-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/StackPass.lean: CONDITIONAL.

What is here. THE TOTAL OF THE BATCHED SUMCHECK's CUBE IS THE FIRST PASS's SUM PLUS THE SECOND's
(`passSum`, StackStart.lean): the first of the four sentences from which StackStart.lean has the
start form's worth. The law on the two long vectors is Johnson/Road/K4/C/LongExt.lean's
(`long_total_pass`); here: what the maker of the job's data lays (`stackDataOn`,
Johnson/Desc/K4/Honest/Stack.lean), opened, and the passage from the list of panels zipped with
their sides to the sum that makes each panel's sides anew. Statements and proofs.

  `stackDataOn_open`   some of what the maker lays
  `zip_of_mapM`, `filter_zip_of_mapM`, `pass_of_zip`   from the zipped list to the sum that makes
     the sides anew
  `stack_total_pass`, `stack_total_of`   **the total is the two passes' sums**

Limits. At the reading `Reading.gl`. Premises: the maker of the job's data returns; THE PANELS'
NUMBERS FIT AND THEIR STRETCHES OF PLACES ARE APART (`PanelsFit`,
Johnson/Road/K4/C/LongPlaces.lean): a hypothesis of `stack_total_pass` on public numbers; every
panel's pass is 0 or 1: likewise. Johnson/Road/K4/C/PanelsFitOf.lean has both from the maker's
return: `stack_total_of` calls it and asks the return alone. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.StackStart
import Johnson.Road.K4.C.LongExt
import Johnson.Road.K4.C.PanelsFitOf
import OnBytes.Maker.TablesLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Reading eqTab)
open OnBytes.Model.Layer (SBlk)
open OnBytes.Road.K4.C (PanelsFit zipped panelDot long_total_pass)
open OnBytes.Desc.First.K4.Honest

/-- **Some of what the maker of the job's data lays.** -/
theorem stackDataOn_open {S : OnBytes.Desc.First.K4.Honest.Sides} {p : Pts} {shownT : Array E}
    {D : StackData} (h : stackDataOn S p shownT = some D) :
    D.S = S ∧ D.om = p.om ∧ D.F = S.weights (eqTab p.rt) ∧ D.hR = S.gatedUnder (eqTab p.rt) ∧
      D.hZ = S.gatedUnder (eqTab S.zt) ∧
      readsAt S.Q S.w S.fo (namedPts S.Q { p with fo := S.fo }) = some D.R ∧ p.om.size = 2 ∧
      (∃ places, S.panels shownT = some (D.bl, places)) ∧
      ∃ sides, D.bl.mapM (panelTabs D.S (fun a => valAff? D.S.v D.R (fun _ => zeroE) a) D.om D.F
          D.hZ D.hR) = some sides ∧
        D.SA = (longTabs D.S.Q.hp.lamS D.bl sides).1 ∧
        D.SB = (longTabs D.S.Q.hp.lamS D.bl sides).2 := by
  unfold stackDataOn at h
  obtain ⟨R, hR, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨bl, places⟩, hp, h⟩ := Option.bind_eq_some_iff.1 h
  dsimp only at h
  by_cases hc : (OnBytes.ceilLog2 places != S.Q.hp.lamS || p.om.size != 2 ||
      S.opens.size != S.Q.hp.NCL - (if (S.Q.g == 0) = true then 1 else 0)) = true
  · rw [if_pos hc] at h
    simp at h
  · rw [if_neg hc] at h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨sides, hs, h⟩ := Option.bind_eq_some_iff.1 h
    obtain rfl := Option.some.inj h
    have ho : p.om.size = 2 := by
      simp only [Bool.or_eq_true, bne_iff_ne, not_or, not_not] at hc
      exact hc.1.2
    exact ⟨rfl, rfl, rfl, rfl, rfl, hR, ho, ⟨places, hp⟩, sides, hs, rfl, rfl⟩

/-- A list zipped with what a loop has made of its members. d: what is taken where the loop's
function has no answer: it is never met. -/
theorem zip_of_mapM {α β γ : Type} (f : α → Option β) (g : α × β → γ) (d : α → γ) :
    ∀ (l : List α) (L : List β), l.mapM f = some L →
    (l.zip L).map g = l.map fun a => match f a with
      | some x => g (a, x)
      | none => d a
  | [], L, h => by simp
  | a :: l, L, h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨L', hL, h⟩ := Option.bind_eq_some_iff.mp h
    obtain rfl := Option.some.inj h
    rw [List.zip_cons_cons, List.map_cons, List.map_cons, zip_of_mapM f g d l L' hL, hb]

/-- The like behind a test on the first members. -/
theorem filter_zip_of_mapM {α β : Type} (f : α → Option β) (t : α → Bool) :
    ∀ (l : List α) (L : List β), l.mapM f = some L →
    ∃ L', (l.filter t).mapM f = some L' ∧ (l.zip L).filter (fun x => t x.1) = (l.filter t).zip L'
  | [], L, h => ⟨[], rfl, by simp⟩
  | a :: l, L, h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨L1, hL, h⟩ := Option.bind_eq_some_iff.mp h
    obtain rfl := Option.some.inj h
    obtain ⟨L', h1, h2⟩ := filter_zip_of_mapM f t l L1 hL
    by_cases ht : t a = true
    · refine ⟨b :: L', ?_, ?_⟩
      · rw [List.filter_cons_of_pos ht, List.mapM_cons, hb, h1]
        rfl
      · rw [List.zip_cons_cons, List.filter_cons_of_pos (by exact ht), h2,
          List.filter_cons_of_pos ht, List.zip_cons_cons]
    · refine ⟨L', ?_, ?_⟩
      · rw [List.filter_cons_of_neg ht]
        exact h1
      · rw [List.zip_cons_cons, List.filter_cons_of_neg (by exact ht), h2,
          List.filter_cons_of_neg ht]

/-- One pass's sum, of the panels zipped with their sides. -/
theorem pass_of_zip (D : StackData) (sides : Array (Array E × Array E))
    (hs : D.bl.mapM (panelTabs D.S (fun a => valAff? D.S.v D.R (fun _ => zeroE) a) D.om D.F D.hZ
      D.hR) = some sides) (c : ℕ) :
    (((zipped D.bl sides).filter fun x => x.1.claim == c).map panelDot).sum = passSum D c := by
  rw [Array.mapM_eq_mapM_toList] at hs
  obtain ⟨L, hL, eL⟩ := Option.map_eq_some_iff.mp hs
  obtain ⟨L', h1, h2⟩ := filter_zip_of_mapM _ (fun b : SBlk => b.claim == c) _ _ hL
  unfold zipped passSum
  rw [← eL]
  show (((D.bl.toList.zip L).filter fun x => x.1.claim == c).map panelDot).sum = _
  rw [h2, zip_of_mapM _ panelDot (fun _ => 0) _ _ h1]
  refine congrArg List.sum (List.map_congr_left fun b _ => ?_)
  cases panelTabs D.S (fun a => valAff? D.S.v D.R (fun _ => zeroE) a) D.om D.F D.hZ D.hR b with
  | none => rfl
  | some x => rfl

/-- **The total of the job's cube is the first pass's sum plus the second's.** -/
theorem stack_total_pass {S : OnBytes.Desc.First.K4.Honest.Sides} {p : Pts} {shownT : Array E}
    {D : StackData} (h : stackDataOn S p shownT = some D)
    (hP : PanelsFit D.S.Q.hp.lamS D.bl.toList)
    (hc : ∀ b ∈ D.bl.toList, b.claim = 0 ∨ b.claim = 1) :
    Reading.gl.val (jobStackOn D).cube.total = passSum D 0 + passSum D 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, sides, hs, eA, eB⟩ := stackDataOn_open h
  have hsz : sides.size = D.bl.size := by
    have hs' := hs
    rw [Array.mapM_eq_mapM_toList] at hs'
    obtain ⟨L, hL, eL⟩ := Option.map_eq_some_iff.mp hs'
    rw [← eL, List.size_toArray, OnBytes.Maker.mapM_length _ _ _ hL, Array.length_toList]
  rw [stack_total_read, eA, eB, long_total_pass hP hsz hc, pass_of_zip D sides hs 0,
    pass_of_zip D sides hs 1]

/-- **The same from the maker's return alone.** -/
theorem stack_total_of {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E} {D : StackData}
    (h : stackData Q w p shownT = some D) :
    Reading.gl.val (jobStackOn D).cube.total = passSum D 0 + passSum D 1 := by
  have h' := h
  unfold stackData at h'
  obtain ⟨S, _, hS⟩ := Option.bind_eq_some_iff.mp h'
  exact stack_total_pass hS (OnBytes.Road.K4.C.stack_panelsFit h) (OnBytes.Road.K4.C.stack_passOK h)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.stackDataOn_open
#print axioms ProofFile.Honest.K4.zip_of_mapM
#print axioms ProofFile.Honest.K4.filter_zip_of_mapM
#print axioms ProofFile.Honest.K4.pass_of_zip
#print axioms ProofFile.Honest.K4.stack_total_pass
#print axioms ProofFile.Honest.K4.stack_total_of
