-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/PanelsFitOf.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the prover's side, the batched sumcheck:
the hypothesis `PanelsFit` (LongPlaces.lean) on the placed panels' public numbers, from three laws
of the library (Johnson/Road/FormsKeysEnd.lean): the verifier's own list of panels has the
library's Shape (shape_panels); the placing changes nothing of a panel but its first place
(placed_from); the placed panels' stretches are apart, each begins at a multiple of its size and
ends at or in front of the number of all places (placed_list). The maker tests that number against
the plan's number of rounds. Beside it: each panel belongs to the first pass or to the second,
since the two functions that make a panel are called at 0 in panelA and at 1 in panelT. A
definition; statements and proofs.

  **`panelsFit_of_place`**   PanelsFit of the placed panels.
  **`stack_panelsFit`**      PanelsFit at the panels in the job's data.
  `PassOK`                 the panel's number of its pass is 0 or 1.
  `claims_plain`, `claims_tri`, `claims_panelA`, `claims_panelT`, `claims_panels`   the verifier's
                           own list of panels has it, step by step.
  **`stack_passOK`**         the panels in the job's data have it.

Not shown here. That the maker returns anywhere: no example is known. The maker's return is the one
premise of stack_panelsFit and of stack_passOK.
No property is claimed.
-/
import Johnson.Road.K4.C.LongPlaces
import Johnson.Road.K4.C.StackPanelsAt
import Johnson.Road.FormsKeysEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (SBlk Lay placePanels Panels PanelEnv panelA panelT panelsA panelsT)
open OnBytes.Desc.First.K4.Honest

/-- **PanelsFit OF THE PLACED PANELS.** sh: each panel has the library's Shape (its rows and columns
fit its bits). ht: the number of all places that placePanels returns is at most 2 ^ lam. -/
theorem panelsFit_of_place {y : Lay} (pans : Array SBlk) {lam : ℕ}
    (sh : ∀ b ∈ pans.toList, OnBytes.Road.Shape y b) (ht : (placePanels pans).2 ≤ 2 ^ lam) :
    PanelsFit lam (placePanels pans).1.toList := by
  refine ⟨fun b hb => ?_, (placed_list pans).1⟩
  obtain ⟨h1, h2⟩ := (placed_list pans).2 b hb
  obtain ⟨b0, h0, o, rfl⟩ := placed_from pans b hb
  have S := sh b0 h0
  exact ⟨S.wy_le, S.ny_le, S.ni_le, h2, Nat.le_trans h1 ht⟩

/-- **PanelsFit AT THE PANELS IN THE JOB's DATA**, at the plan's number of rounds. CONDITIONAL: on
the maker's return. -/
theorem stack_panelsFit {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E} {SD : StackData}
    (h : stackData Q w p shownT = some SD) : PanelsFit SD.S.Q.hp.lamS SD.bl.toList := by
  unfold stackData at h
  obtain ⟨S, _, h⟩ := Option.bind_eq_some_iff.1 h
  unfold stackDataOn at h
  obtain ⟨R, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨bl, places⟩, hp, h⟩ := Option.bind_eq_some_iff.1 h
  dsimp only at h
  by_cases hc : (ceilLog2 places != S.Q.hp.lamS || p.om.size != 2 ||
      S.opens.size != S.Q.hp.NCL - (if (S.Q.g == 0) = true then 1 else 0)) = true
  · rw [if_pos hc] at h
    simp at h
  · rw [if_neg hc] at h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨sides, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain rfl := Option.some.inj h
    have hlam : ceilLog2 places = S.Q.hp.lamS := by
      by_contra hne
      refine hc ?_
      rw [bne_iff_ne.mpr hne]
      rfl
    unfold Sides.panels at hp
    obtain ⟨pans, h1, hp⟩ := Option.bind_eq_some_iff.1 hp
    dsimp only at hp
    by_cases hn : (pans.nextV != S.opens.size) = true
    · rw [if_pos hn] at hp
      simp at hp
    · rw [if_neg hn] at hp
      obtain ⟨_, _, hp⟩ := Option.bind_eq_some_iff.1 hp
      have e := Option.some.inj hp
      have e1 : bl = (placePanels pans.bl).1 := (congrArg Prod.fst e).symm
      have e2 : places = (placePanels pans.bl).2 := (congrArg Prod.snd e).symm
      show PanelsFit S.Q.hp.lamS bl.toList
      rw [e1, ← hlam, e2]
      exact panelsFit_of_place pans.bl (shape_panels _ _ h1) (Slice.le_two_pow_ceilLog2 _)

/-! ## The pass that a panel belongs to -/

/-- A panel belongs to the first pass or to the second. -/
def PassOK (b : SBlk) : Prop := b.claim = 0 ∨ b.claim = 1

/-- The function plain, called at 0 or 1, appends such a panel. -/
theorem claims_plain (y : Lay) (ec : E) (claim : ℕ) (moeSet : Bool) (ny : ℕ)
    (A B : Option (ℕ → ℕ → Option Aff)) (wt : ℕ → E) (virt : Option ℕ) (s : Panels)
    (hc : claim = 0 ∨ claim = 1) (hs : ∀ b ∈ s.bl.toList, PassOK b) :
    ∀ b ∈ (Layer.plain y ec claim moeSet ny A B wt virt s).bl.toList, PassOK b := by
  intro b hb
  unfold Layer.plain at hb
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hb
  rcases hb with hb | rfl
  · exact hs b hb
  · exact hc

/-- The function tri, called at 0 or 1, appends such a panel. -/
theorem claims_tri (y : Lay) (ec : E) (claim nk : ℕ) (sl : Array E) (xx : Array Aff)
    (virt : Option ℕ) (wt : E) (s : Panels) (hc : claim = 0 ∨ claim = 1)
    (hs : ∀ b ∈ s.bl.toList, PassOK b) :
    ∀ b ∈ (Layer.tri y ec claim nk sl xx virt wt s).bl.toList, PassOK b := by
  intro b hb
  unfold Layer.tri at hb
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hb
  rcases hb with hb | rfl
  · exact hs b hb
  · exact hc

/-- The panels of one segment of the lookup's join: the first pass. -/
theorem claims_panelA (p : PanelEnv) (ec : E) (el : Array E) (sn : String) (s : Panels)
    (hs : ∀ b ∈ s.bl.toList, PassOK b) : ∀ b ∈ (panelA p ec el sn s).bl.toList, PassOK b := by
  simp only [panelA]
  split_ifs <;> first
    | exact hs
    | exact claims_plain _ _ _ _ _ _ _ _ _ _ (Or.inl rfl) hs

/-- The panels of one segment of the second token sumcheck's terms: the second pass. -/
theorem claims_panelT (p : PanelEnv) (ec : E) (el : Array E) (sn : String) (s s' : Panels)
    (hs : ∀ b ∈ s.bl.toList, PassOK b) (h : panelT p ec el sn s = some s') :
    ∀ b ∈ s'.bl.toList, PassOK b := by
  simp only [panelT] at h
  split_ifs at h <;> first
    | (cases h; exact hs)
    | (cases h; exact claims_plain _ _ _ _ _ _ _ _ _ _ (Or.inr rfl) hs)
    | (obtain ⟨_, _, h⟩ := bind_some h; cases h
       exact claims_plain _ _ _ _ _ _ _ _ _ _ (Or.inr rfl) hs)
    | exact foldlM_inv_mem (fun s : Panels => ∀ b ∈ s.bl.toList, PassOK b) _ _
        (fun s lm s' hm hs h => by
          first
            | (cases h
               exact claims_tri _ _ _ _ _ _ _ _ _ (Or.inr rfl) hs)
            | (obtain ⟨_, _, h⟩ := bind_some h; cases h
               exact claims_tri _ _ _ _ _ _ _ _ _ (Or.inr rfl) hs))
        _ _ hs h

/-- The verifier's own list of panels. -/
theorem claims_panels (p : PanelEnv) (TS : List ℕ) {pans : Panels}
    (h : panelsT p TS (panelsA p {}) = some pans) : ∀ b ∈ pans.bl.toList, PassOK b := by
  have h0 : ∀ b ∈ ({} : Panels).bl.toList, PassOK b := fun b hb => absurd hb List.not_mem_nil
  have hA : ∀ b ∈ (panelsA p {}).bl.toList, PassOK b := by
    unfold panelsA
    refine foldl_inv (fun s : Panels => ∀ b ∈ s.bl.toList, PassOK b) _ (fun s q hs => ?_) _ _ h0
    exact foldl_inv (fun s : Panels => ∀ b ∈ s.bl.toList, PassOK b) _
      (fun s g hs => claims_panelA p _ _ _ s hs) _ _ hs
  unfold panelsT at h
  refine foldlM_inv (fun s : Panels => ∀ b ∈ s.bl.toList, PassOK b) _
    (fun s q s' hs e => ?_) _ _ _ hA h
  exact foldlM_inv (fun s : Panels => ∀ b ∈ s.bl.toList, PassOK b) _
    (fun s g s' hs e => claims_panelT p _ _ _ s s' hs e) _ _ _ hs e

/-- **EACH PANEL IN THE JOB's DATA BELONGS TO THE FIRST PASS OR TO THE SECOND.** CONDITIONAL: on the
maker's return. -/
theorem stack_passOK {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E} {SD : StackData}
    (h : stackData Q w p shownT = some SD) : ∀ b ∈ SD.bl.toList, b.claim = 0 ∨ b.claim = 1 := by
  obtain ⟨pans, h1, e, _⟩ := stack_panels_at h
  intro b hb
  rw [e] at hb
  obtain ⟨b0, h0, o, rfl⟩ := placed_from pans.bl b hb
  exact claims_panels _ _ h1 b0 h0

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.claims_plain
#print axioms OnBytes.Road.K4.C.claims_tri
#print axioms OnBytes.Road.K4.C.claims_panelA
#print axioms OnBytes.Road.K4.C.claims_panelT
#print axioms OnBytes.Road.K4.C.claims_panels
#print axioms OnBytes.Road.K4.C.stack_passOK
#print axioms OnBytes.Road.K4.C.panelsFit_of_place
#print axioms OnBytes.Road.K4.C.stack_panelsFit
