-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/DownPanel.lean: CONDITIONAL.

Not shown here. THAT THE MAKER RETURNS: a hypothesis, of which no example is known here. Where
GatedNums holds: the head of C/GatedNums.lean. Nothing on what a panel's sides hold. Nothing on
soundness, on completeness or on any other property. No property is claimed.

The four numbers of the verifier's panel of the down product that `h1_read` (C/StackEnds.lean) asks:
the bits of a column and of a place, the rows and the columns. The bits are the library's
(`virt_panels`, Johnson/Road/K4/GatedSays.lean). For the rows and the columns the library's walk
over the verifier's list of panels is gone again with another sentence: The proofs of down_plain,
down_tri, down_panelA, down_panelT, down_panels and down_placed follow the library's virt_plain to
virt_placed step for step; their ends differ as the sentence does.

  `DownOK y b`   a panel without the selector that bears a never-sent vector has the group's layers
      as rows and a layer's hidden units as columns.
  `down_plain`, `down_tri`, `down_panelA`, `down_panelT`, `down_panels`, `down_placed`   DownOK at
      every panel of the verifier's list, placed.
  `stack_panels`   the panels in the job's data are the verifier's list, placed.
  `down_nums`   the four numbers, in the form in which h1_read asks them.
-/
import Johnson.Road.K4.C.StackIs
import Johnson.Road.K4.GatedSays

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (SBlk Lay placePanels Panels PanelEnv panelA panelT panelsA panelsT stubO)
open Inst.Model.FFSeg (Dim lF)
open OnBytes.Desc.First.K4.Honest

/-- The rows and the columns of a panel without the selector that bears a never-sent vector. -/
def DownOK (y : Lay) (b : SBlk) : Prop :=
  b.tri = false → ∀ k, b.virt = some k → b.ni = y.Lam ∧ b.ny = y.h.f

theorem down_plain (y : Lay) (ec : E) (claim : ℕ) (moeSet : Bool) (ny : ℕ)
    (A B : Option (ℕ → ℕ → Option Aff)) (wt : ℕ → E) (virt : Option ℕ) (s : Panels)
    (hv : ∀ k, virt = some k → k = 0 ∧ moeSet = false ∧ ny = y.h.f)
    (hs : ∀ b ∈ s.bl.toList, DownOK y b) :
    ∀ b ∈ (Layer.plain y ec claim moeSet ny A B wt virt s).bl.toList, DownOK y b := by
  intro b hb
  unfold Layer.plain at hb
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hb
  rcases hb with hb | rfl
  · exact hs b hb
  · intro _ k hk
    obtain ⟨_, e1, e2⟩ := hv k hk
    subst e1
    subst e2
    exact ⟨rfl, rfl⟩

theorem down_tri (y : Lay) (ec : E) (claim nk : ℕ) (sl : Array E) (xx : Array Aff)
    (virt : Option ℕ) (wt : E) (s : Panels) (hs : ∀ b ∈ s.bl.toList, DownOK y b) :
    ∀ b ∈ (Layer.tri y ec claim nk sl xx virt wt s).bl.toList, DownOK y b := by
  intro b hb
  unfold Layer.tri at hb
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hb
  rcases hb with hb | rfl
  · exact hs b hb
  · intro h
    cases h

theorem down_panelA (p : PanelEnv) (ec : E) (el : Array E) (sn : String) (s : Panels)
    (hs : ∀ b ∈ s.bl.toList, DownOK p.v.y b) :
    ∀ b ∈ (panelA p ec el sn s).bl.toList, DownOK p.v.y b := by
  simp only [panelA]
  split_ifs <;> first
    | exact hs
    | exact down_plain _ _ _ _ _ _ _ _ _ _ no_virtP hs
    | exact down_plain _ _ _ _ _ _ _ _ _ _
        (fun k e => ⟨(Option.some.inj e).symm, rfl, rfl⟩) hs

theorem down_panelT (p : PanelEnv) (ec : E) (el : Array E) (sn : String) (s s' : Panels)
    (hs : ∀ b ∈ s.bl.toList, DownOK p.v.y b) (h : panelT p ec el sn s = some s') :
    ∀ b ∈ s'.bl.toList, DownOK p.v.y b := by
  simp only [panelT] at h
  split_ifs at h <;> first
    | (cases h; exact hs)
    | (cases h; exact down_plain _ _ _ _ _ _ _ _ _ _ no_virtP hs)
    | (obtain ⟨_, _, h⟩ := bind_some h; cases h
       exact down_plain _ _ _ _ _ _ _ _ _ _ no_virtP hs)
    | exact foldlM_inv_mem (fun s : Panels => ∀ b ∈ s.bl.toList, DownOK p.v.y b) _ _
        (fun s lm s' hm hs h => by
          first
            | (cases h
               exact down_tri _ _ _ _ _ _ _ _ _ hs)
            | (obtain ⟨_, _, h⟩ := bind_some h; cases h
               exact down_tri _ _ _ _ _ _ _ _ _ hs))
        _ _ hs h

/-- The verifier's own list of panels. -/
theorem down_panels (p : PanelEnv) (TS : List ℕ) {pans : Panels}
    (h : panelsT p TS (panelsA p {}) = some pans) : ∀ b ∈ pans.bl.toList, DownOK p.v.y b := by
  have h0 : ∀ b ∈ ({} : Panels).bl.toList, DownOK p.v.y b :=
    fun b hb => absurd hb List.not_mem_nil
  have hA : ∀ b ∈ (panelsA p {}).bl.toList, DownOK p.v.y b := by
    unfold panelsA
    refine foldl_inv (fun s : Panels => ∀ b ∈ s.bl.toList, DownOK p.v.y b) _ (fun s q hs => ?_)
      _ _ h0
    exact foldl_inv (fun s : Panels => ∀ b ∈ s.bl.toList, DownOK p.v.y b) _
      (fun s g hs => down_panelA p _ _ _ s hs) _ _ hs
  unfold panelsT at h
  refine foldlM_inv (fun s : Panels => ∀ b ∈ s.bl.toList, DownOK p.v.y b) _
    (fun s q s' hs e => ?_) _ _ _ hA h
  exact foldlM_inv (fun s : Panels => ∀ b ∈ s.bl.toList, DownOK p.v.y b) _
    (fun s g s' hs e => down_panelT p _ _ _ s s' hs e) _ _ _ hs e

/-- The placing changes nothing of it. -/
theorem down_placed {y : Lay} {bl : Array SBlk} (R : ∀ b ∈ bl.toList, DownOK y b) :
    ∀ b ∈ (placePanels bl).1.toList, DownOK y b := by
  intro b hb
  obtain ⟨b0, h0, o, rfl⟩ := placed_from bl b hb
  exact R b0 h0

/-- **The panels in the job's data are the verifier's list, placed.** CONDITIONAL: on the maker's
return. -/
theorem stack_panels {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E} {SD : StackData}
    (h : stackData Q w p shownT = some SD) :
    ∃ (pe : PanelEnv) (pans : Panels), pe.v = SD.S.v ∧
      panelsT pe SD.S.TS (panelsA pe {}) = some pans ∧ SD.bl = (placePanels pans.bl).1 := by
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
    unfold Sides.panels at hp
    obtain ⟨pans, h1, hp⟩ := Option.bind_eq_some_iff.1 hp
    dsimp only at hp
    by_cases hn : (pans.nextV != S.opens.size) = true
    · rw [if_pos hn] at hp
      simp at hp
    · rw [if_neg hn] at hp
      obtain ⟨_, _, hp⟩ := Option.bind_eq_some_iff.1 hp
      have e := Option.some.inj hp
      exact ⟨_, pans, rfl, h1, (congrArg Prod.fst e).symm⟩

/-- **THE FOUR NUMBERS OF THE PANEL OF THE DOWN PRODUCT**, as h1_read asks them. CONDITIONAL: on the
maker's return and on N. -/
theorem down_nums {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E} {SD : StackData} {D : Dim}
    (h : stackData Q w p shownT = some SD) (N : GatedNums Q D) :
    ∀ dn, (SD.bl.find? fun b => !b.tri && b.virt.isSome) = some dn →
      dn.wy = lF D ∧ dn.w = D.lL + lF D ∧ dn.ni = 2 ^ D.lL ∧ dn.ny = 2 ^ lF D := by
  intro dn hd
  obtain ⟨_, tb, I⟩ := stackIs_of h
  obtain ⟨pe, pans, ev, hp, eb⟩ := stack_panels h
  have hy : pe.v.y = Q.P.y := by rw [ev]; exact I.y
  have hm : dn ∈ (placePanels pans.bl).1.toList := by
    rw [← eb]
    exact Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some hd)
  have hq := Array.find?_some hd
  have ht : dn.tri = false := by
    cases e : dn.tri
    · rfl
    · rw [e] at hq
      cases hq
  obtain ⟨k, hk⟩ : ∃ k, dn.virt = some k := by
    rw [ht] at hq
    exact Option.isSome_iff_exists.mp (by simpa using hq)
  obtain ⟨_, a1, a2⟩ := (virt_placed (virt_panels pe SD.S.TS hp) dn hm).plain ht k hk
  obtain ⟨a3, a4⟩ := down_placed (down_panels pe SD.S.TS hp) dn hm ht k hk
  have cf : ceilLog2 Q.P.y.h.f = lF D := by
    rw [N.f, ceilLog2_eq_clog, Nat.clog_pow 2 _ (by decide)]
  have cL : ceilLog2 Q.P.y.Lam = D.lL := by
    rw [N.Lam, ceilLog2_eq_clog, Nat.clog_pow 2 _ (by decide)]
  rw [hy] at a1 a2 a3 a4
  exact ⟨a1.trans cf, by rw [a2, cL, cf], a3.trans N.Lam, a4.trans N.f⟩

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.down_plain
#print axioms OnBytes.Road.K4.C.down_tri
#print axioms OnBytes.Road.K4.C.down_panelA
#print axioms OnBytes.Road.K4.C.down_panelT
#print axioms OnBytes.Road.K4.C.down_panels
#print axioms OnBytes.Road.K4.C.down_placed
#print axioms OnBytes.Road.K4.C.stack_panels
#print axioms OnBytes.Road.K4.C.down_nums
