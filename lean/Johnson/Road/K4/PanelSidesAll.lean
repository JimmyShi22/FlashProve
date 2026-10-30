-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/PanelSidesAll.lean: each of the fifteen kinds of panel of the verifier's batched
sumcheck has, side by side, the form parts of its panel of the library.

  `panel_sides`: panel_sides_early (Johnson/Road/K4/PanelSidesEarly.lean) and panel_sides_late
    (Johnson/Road/K4/PanelSidesLate.lean) in one statement, under the record SigFits
    (Johnson/Road/FormsKeysPortSig.lean), for a panel b that IsPanelOf a panel pn of the library.
  `placed_sides`: so on the verifier's own placed list, member by member against the library's list
    pans D, if stackEnd has returned on it.
Limits. As the two files'. The record of reads is rPort. Identities in one world: nothing on a run,
on soundness or on hiding.


-/
import Johnson.Road.K4.PanelSidesEarly
import Johnson.Road.K4.PanelSidesLate

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open OnBytes.Model (Reading World WsClaim WsShape)
open OnBytes.Model.Layer (SBlk Panels PanelEnv ClaimEnv StackEnd stackEnd placePanels panelsA
  panelsT)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell LW Pan pans)

variable {K : Type} [Field K] [scl : Scl] {ρ : Reading K} {Wo : World K} {p : PanelEnv}
  {c : ClaimEnv} {h : Model.Layer.Shape} {pc : List (List String)} {s : WsShape} {D : Dim}
  {lk L0 : ℕ} {cc : Cells K} {t : Cell → K} {low z zh ζ : ℕ → K} {tb : Tables}

/-- **One panel, of any of the fifteen kinds.** -/
theorem panel_sides (S : SigFits ρ Wo p c h pc s D lk L0 cc t low z zh ζ tb) (hh : ℕ → ℕ → K)
    (w : ℕ → LW K) {TS : List ℕ} (hTS : TS = [0, 1, 2, 5]) {cl : List WsClaim} {om : Array E}
    (hom : ρ.val (om.getD 0 zeroE) = 1) {b : SBlk} {pn : Pan} (hI : IsPanelOf p c TS cl b pn)
    (hr : b.tri = false → b.virt = none → (∀ v0, b.v0 = some v0 → b.B = none) → Returns b) :
    SidesAre ρ Wo p.v.y om D (rPort ρ p.v.y p.shownT hh D t z zh) tb L0 w z zh
      (ρ.val (om.getD 1 zeroE)) b pn := by
  cases pn with
  | G => exact panel_sides_early S hh w hTS hom hI (by simp) hr
  | U => exact panel_sides_early S hh w hTS hom hI (by simp) hr
  | O => exact panel_sides_early S hh w hTS hom hI (by simp) hr
  | D => exact panel_sides_early S hh w hTS hom hI (by simp) hr
  | V => exact panel_sides_early S hh w hTS hom hI (by simp) hr
  | LR => exact panel_sides_early S hh w hTS hom hI (by simp) hr
  | QK => exact panel_sides_early S hh w hTS hom hI (by simp) hr
  | _ => exact panel_sides_late S hh w hTS hI (by simp) hr

/-- **The placed list.** -/
theorem placed_sides (S : SigFits ρ Wo p c h pc s D lk L0 cc t low z zh ζ tb) (hh : ℕ → ℕ → K)
    (w : ℕ → LW K) {TS : List ℕ} (hTS : TS = [0, 1, 2, 5]) {pans' : Panels} {cl : List WsClaim}
    (hp : panelsT p TS (panelsA p {}) = some pans') (hc : c.weightClaims TS = some cl)
    {om : Array E} (hom : ρ.val (om.getD 0 zeroE) = 1) {rs H1 V : Array E} {lam : ℕ}
    {shownA shownB : E} {s' : StackEnd}
    (hst : stackEnd p.v.y (placePanels pans'.bl).1 rs lam om H1 V shownA shownB = some s') :
    List.Forall₂ (fun b pn => SidesAre ρ Wo p.v.y om D (rPort ρ p.v.y p.shownT hh D t z zh) tb L0
      w z zh (ρ.val (om.getD 1 zeroE)) b pn) (placePanels pans'.bl).1.toList (pans D) := by
  have h3 : p.v.y.h.p3 = true := by
    rw [S.env]
    exact S.aim.claim.p3
  have hne : p.v.y.LamM = D.ne := by
    rw [S.env]
    exact S.aim.claim.LamM
  refine (f2_mem_left (placed_are_pans p c S.env hp hc h3 hne S.lines hTS)).imp fun b' pn k => ?_
  obtain ⟨hm, b, ⟨o, rfl⟩, hI⟩ := k
  have hr : b.tri = false → b.virt = none → (∀ v0, b.v0 = some v0 → b.B = none) → Returns b := by
    intro ht hk hB
    have r := returns_of_stackEnd hst { b with off := o } hm ht hk hB
    exact r
  have e := panel_sides S hh w hTS hom hI hr
  exact ⟨e.bw, e.bwy, e.sa, e.sb⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.panel_sides
#print axioms OnBytes.Road.K4.placed_sides
