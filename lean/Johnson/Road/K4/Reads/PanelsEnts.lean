-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/Reads/PanelsEnts.lean: THE TWO FORMS THAT THE END OF THE BATCHED SUMCHECK LEAVES
NAME ENTRIES INSIDE THE FAMILIES OF TABLES: `StackEnd.Alin` and `StackEnd.Blin`, as `stackEnd` makes
them over the placed panels of `panelsA` and `panelsT` (OnBytes/Model/LayerPanels.lean) at the
environment p.v, are `InTab p.v` (Johnson/Road/K4/Reads/TermsEnts.lean). Definitions, statements
and proofs.

MADE BY PROGRAM out of Johnson/Road/K4/Slots/Panels.lean, which shows the same walk for slots:
`SlotsIn S` became `InTab v`, the readers' `gives_x` became `ge_x`
(Johnson/Road/K4/Reads/GivesEnts.lean), the rules `slotsIn_x` became `entsIn_x`; in the four
theorems on a `PanelEnv` p the environment is p.v. `Side`, `core`, `foldl_inv`, `gives_foldlM_inv`
are that file's own and are not typed again. No proof is new.

  `SideIn v A`: whatever the side A returns is `InTab v`. `CoreIn v c`: so for A and B, and every
    member of xx. `PanIn v bl`: so for each panel of the list. `EndIn v s`: the end's two forms.
  `sideIn_none`, `sideIn_some`, `panIn_empty`, `panIn_push`, `inTab_getD_empty`, `mapM_getD_in`:
    small rules.
  `plain_in`, `tri_in`, `panelA_in`, `panelsA_in`, `panelT_in`, `panelsT_in`: the lists of panels.
  `placePanels_in`: placing turns a panel's first place alone (`map_modify_same`).
  `stackEndOf_in`, **`stackEnd_ents`**: the end, over any list of panels with `PanIn`. The title's
    sentence is these laid together: `hearStack_ends` (Johnson/Road/K4/Reads/StackEnts.lean).

Limits. As TermsEnts.lean's: an index that strays to another tensor, layer or limb of the same
family is not caught; nothing on whether the families lie in the part of the array that the reads'
test covers. Nothing on what the forms mean. Nothing on soundness.
-/
import Johnson.Road.K4.Reads.GivesEnts
import Johnson.Road.K4.Slots.Panels

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Reads

open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Road (map_some)
open OnBytes.Desc.First.K4.Slots (Gives Side core foldl_inv gives_foldlM_inv)

variable {v : Env}

/-- Whatever the side returns names entries inside the families alone. -/
def SideIn (v : Env) (A : Side) : Prop := ∀ f, A = some f → ∀ i y, Gives (f i y) (InTab v)

theorem sideIn_none : SideIn v none := fun _ e => by cases e

theorem sideIn_some {g : ℕ → ℕ → Option Aff} (h : ∀ i y, Gives (g i y) (InTab v)) :
    SideIn v (some g) := fun _ e => Option.some.inj e ▸ h

/-- Whatever a panel's A or B side returns, and every member of its xx, names entries inside the
families alone. -/
def CoreIn (v : Env) (c : Side × Side × Array Aff) : Prop :=
  SideIn v c.1 ∧ SideIn v c.2.1 ∧ ∀ k, InTab v (c.2.2.getD k {})

/-- So for each panel of the list. -/
def PanIn (v : Env) (bl : Array SBlk) : Prop := ∀ c ∈ (bl.map core).toList, CoreIn v c

theorem panIn_empty : PanIn v #[] := fun c hc => by simp at hc

theorem panIn_push {bl : Array SBlk} {b : SBlk} (h : PanIn v bl) (hb : CoreIn v (core b)) :
    PanIn v (bl.push b) := fun c hc => by
  simp only [Array.map_push, Array.toList_push, List.mem_append, List.mem_singleton] at hc
  rcases hc with hc | rfl
  · exact h c hc
  · exact hb

theorem inTab_getD_empty (k : ℕ) : InTab v ((#[] : Array Aff).getD k {}) := by
  have e : (#[] : Array Aff).getD k {} = {} := by simp [Array.getD]
  rw [e]
  exact entsIn_empty

theorem plain_in (y : Lay) (ec : E) (claim : ℕ) (moeSet : Bool) (ny : ℕ) {A B : Side} (wt : ℕ → E)
    (virt : Option ℕ) {s : Panels} (hs : PanIn v s.bl) (hA : SideIn v A) (hB : SideIn v B) :
    PanIn v (plain y ec claim moeSet ny A B wt virt s).bl := by
  unfold plain
  refine panIn_push hs ⟨fun f hf i yv => ?_, fun f hf i yv => ?_, inTab_getD_empty⟩
  · obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hf
    exact hA g hg _ _
  · obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hf
    exact hB g hg _ _

theorem tri_in (y : Lay) (ec : E) (claim nk : ℕ) (sl : Array E) {xx : Array Aff}
    (virt : Option ℕ) (wt : E) {s : Panels} (hs : PanIn v s.bl)
    (hx : ∀ k, InTab v (xx.getD k {})) : PanIn v (tri y ec claim nk sl xx virt wt s).bl := by
  unfold tri
  exact panIn_push hs ⟨sideIn_none, sideIn_none, hx⟩

theorem panelA_in (p : PanelEnv) (ec : E) (el : Array E) (sn : String) {s : Panels}
    (hs : PanIn p.v s.bl) : PanIn p.v (panelA p ec el sn s).bl := by
  unfold panelA
  dsimp only
  split
  · exact plain_in _ _ _ _ _ _ _ hs (sideIn_some fun _ _ => ge_shIn _ _ _) sideIn_none
  split
  · exact plain_in _ _ _ _ _ _ _ hs (sideIn_some fun _ _ => ge_shIn _ _ _) sideIn_none
  split
  · refine plain_in _ _ _ _ _ _ _ hs (sideIn_some fun _ _ => ?_) sideIn_none
    refine Gives.ite (ge_shIn _ _ _) (Gives.some ?_)
    unfold stubAt
    exact entsIn_ofConst _
  split
  · exact plain_in _ _ _ _ _ _ _ hs sideIn_none sideIn_none
  split
  · exact plain_in _ _ _ _ _ _ _ hs (sideIn_some fun _ _ => ge_shIn _ _ _) sideIn_none
  · exact hs

theorem panelsA_in (p : PanelEnv) {s : Panels} (hs : PanIn p.v s.bl) :
    PanIn p.v (panelsA p s).bl := by
  unfold panelsA
  refine foldl_inv (P := fun s : Panels => PanIn p.v s.bl) (fun s q hs => ?_) _ _ hs
  exact foldl_inv (P := fun s : Panels => PanIn p.v s.bl)
    (fun s g hs => panelA_in _ _ _ _ hs) _ _ hs

/-- Every member of an array that a function has filled. -/
theorem mapM_getD_in {n : ℕ} {g : ℕ → Option Aff} (hg : ∀ i, Gives (g i) (InTab v)) :
    Gives ((Array.range n).mapM g) fun xx => ∀ k, InTab v (xx.getD k {}) := by
  intro xx h k
  rw [Array.mapM_eq_mapM_toList] at h
  obtain ⟨ys, hys, e⟩ := map_some h
  subst e
  by_cases hj : k < ys.length
  · have e : ys.toArray.getD k {} = ys[k] := by simp [Array.getD, hj]
    rw [e]
    exact all_mapM (Pr := InTab v) (fun i a ha => hg i a ha) _ ys hys _ (List.getElem_mem hj)
  · have e : ys.toArray.getD k {} = {} := by simp [Array.getD, hj]
    rw [e]
    exact entsIn_empty

theorem panelT_in (p : PanelEnv) (ec : E) (el : Array E) (sn : String) {s : Panels}
    (hs : PanIn p.v s.bl) : Gives (panelT p ec el sn s) fun s' => PanIn p.v s'.bl := by
  unfold panelT
  dsimp only
  refine Gives.ite ?_ (Gives.ite ?_ (Gives.ite ?_ (Gives.ite ?_ (Gives.ite ?_ (Gives.ite ?_ ?_)))))
  · exact Gives.skip fun wh => Gives.pure (plain_in _ _ _ _ _ _ _ hs
      (sideIn_some fun _ _ => Gives.some (entsIn_ofConst _))
      (sideIn_some fun _ _ => ge_SxsA _ _ _))
  · exact Gives.pure (plain_in _ _ _ _ _ _ _ hs (sideIn_some fun _ _ => ge_shIn _ _ _)
      sideIn_none)
  · exact Gives.pure hs
  · exact Gives.skip fun ew => Gives.pure (plain_in _ _ _ _ _ _ _ hs
      (sideIn_some fun _ _ => Gives.some (entsIn_ofConst _))
      (sideIn_some fun _ _ => ge_shSum _ _ _ _ _))
  · exact Gives.skip fun ew => Gives.pure (plain_in _ _ _ _ _ _ _ hs
      (sideIn_some fun _ _ => Gives.some (entsIn_ofConst _))
      (sideIn_some fun _ _ => ge_shA _ _ _ _))
  · refine gives_foldlM_inv (P := fun s : Panels => PanIn p.v s.bl) (fun s lm hs => ?_) _ _ hs
    refine Gives.ite (Gives.pure (tri_in _ _ _ _ _ _ _ hs inTab_getD_empty)) ?_
    exact Gives.bind (mapM_getD_in fun _ => ge_shIn _ _ _) fun xx hx =>
      Gives.pure (tri_in _ _ _ _ _ _ _ hs hx)
  · exact Gives.pure hs

theorem panelsT_in (p : PanelEnv) (TS : List ℕ) {s : Panels} (hs : PanIn p.v s.bl) :
    Gives (panelsT p TS s) fun s' => PanIn p.v s'.bl := by
  unfold panelsT
  refine gives_foldlM_inv (P := fun s : Panels => PanIn p.v s.bl) (fun s q hs => ?_) _ _ hs
  exact gives_foldlM_inv (P := fun s : Panels => PanIn p.v s.bl)
    (fun s g hs => panelT_in _ _ _ _ hs) _ _ hs

/-- Placing turns a panel's first place alone. -/
theorem placePanels_in {bl : Array SBlk} (h : PanIn v bl) : PanIn v (placePanels bl).1 := by
  unfold placePanels
  refine foldl_inv (P := fun s : Array SBlk × ℕ => PanIn v s.1) (fun s i hs => ?_) _ _ h
  show PanIn v (s.1.modify i fun b => { b with off := s.2 })
  unfold PanIn
  rw [map_modify_same core (fun b : SBlk => { b with off := s.2 }) (fun _ => rfl)]
  exact hs

/-! ### The end -/

/-- The two forms of the end name entries inside the families alone. -/
def EndIn (v : Env) (s : StackEnd) : Prop := InTab v s.Alin ∧ InTab v s.Blin

/-- **What one panel adds.** -/
theorem stackEndOf_in (y : Lay) (rs : Array E) (lam : ℕ) (om H1 V : Array E) {s : StackEnd}
    {b : SBlk} (hb : CoreIn v (core b)) (hs : EndIn v s) :
    Gives (stackEndOf y rs lam om H1 V s b) (EndIn v) := by
  obtain ⟨hA, hB, hx⟩ := hb
  have guard : ∀ {α : Type} (f : PUnit → Option α) (Φ : α → Prop),
      Gives ((none : Option PUnit) >>= f) Φ :=
    fun f Φ => Gives.bind (Φ := fun _ => False) Gives.none fun _ h => h.elim
  unfold stackEndOf
  cases ht : b.tri with
  | true =>
    cases hk : b.virt with
    | some k =>
      simp only [↓reduceIte]
      refine Gives.ite (guard _ _)
        (Gives.skip fun _ => Gives.skip fun v0 => Gives.ite Gives.none (Gives.pure ?_))
      exact ⟨hs.1, hs.2⟩
    | none =>
      simp only [↓reduceIte]
      refine Gives.ite (guard _ _) (Gives.skip fun _ => Gives.skip fun v0 => Gives.pure ?_)
      exact ⟨entsIn_foldl _ (fun a k2 ha => entsIn_addMul _ ha (hx k2)) _ _ hs.1, hs.2⟩
  | false =>
    cases hk : b.virt with
    | some k =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine Gives.ite (guard _ _)
        (Gives.skip fun _ => Gives.skip fun v0 => Gives.ite Gives.none (Gives.pure ?_))
      exact ⟨hs.1, hs.2⟩
    | none =>
      cases hv : b.v0 with
      | some v0 =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine Gives.ite (guard _ _) (Gives.skip fun _ => ?_)
        refine Gives.bind (Φ := fun A => b.A = some A) (fun _ h => h) fun A hAe => ?_
        refine gives_foldlM_inv (P := EndIn v) (fun s i hs => ?_) _ _ hs
        refine Gives.bind (Φ := EndIn v) ?_ fun s hs => Gives.pure ?_
        · refine gives_foldlM_inv (P := EndIn v) (fun s yv hs => ?_) _ _ hs
          refine Gives.bind (hA A hAe i yv) fun a ha => Gives.pure ?_
          exact ⟨entsIn_addMul _ hs.1 ha, hs.2⟩
        · exact ⟨hs.1, hs.2⟩
      | none =>
        cases hBe : b.B with
        | none =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine Gives.ite (guard _ _) (Gives.skip fun _ => ?_)
          refine Gives.skip fun A => ?_
          refine gives_foldlM_inv (P := EndIn v) (fun s i hs => ?_) _ _ hs
          refine Gives.bind (Φ := EndIn v) ?_ fun s hs => Gives.pure hs
          refine gives_foldlM_inv (P := EndIn v) (fun s yv hs => ?_) _ _ hs
          exact Gives.skip fun _ => Gives.none
        | some B =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine Gives.ite (guard _ _) (Gives.skip fun _ => ?_)
          refine Gives.bind (Φ := fun A => b.A = some A) (fun _ h => h) fun A hAe => ?_
          refine gives_foldlM_inv (P := EndIn v) (fun s i hs => ?_) _ _ hs
          refine Gives.bind (Φ := EndIn v) ?_ fun s hs => Gives.pure hs
          refine gives_foldlM_inv (P := EndIn v) (fun s yv hs => ?_) _ _ hs
          refine Gives.bind (hA A hAe i yv) fun a ha =>
            Gives.bind (hB B hBe i yv) fun c hc => Gives.pure ?_
          exact ⟨entsIn_addMul _ hs.1 ha, entsIn_addMul _ hs.2 hc⟩

/-- **The end of the batched sumcheck over all panels.** -/
theorem stackEnd_ents {y : Lay} {bl : Array SBlk} {rs : Array E} {lam : ℕ} {om H1 V : Array E}
    {shownA shownB : E} {s : StackEnd} (hbl : PanIn v bl)
    (h : stackEnd y bl rs lam om H1 V shownA shownB = some s) : EndIn v s := by
  unfold stackEnd at h
  obtain ⟨s0, h0, h⟩ := Option.bind_eq_some_iff.mp h
  have hs0 : EndIn v s0 := by
    rw [← Array.foldlM_toList] at h0
    have key : ∀ (l : List SBlk) (a : StackEnd), (∀ b ∈ l, CoreIn v (core b)) → EndIn v a →
        Gives (l.foldlM (stackEndOf y rs lam om H1 V) a) (EndIn v) := by
      intro l
      induction l with
      | nil => exact fun a _ ha => Gives.pure ha
      | cons b l ih =>
        intro a hl ha
        rw [List.foldlM_cons]
        exact Gives.bind (stackEndOf_in y rs lam om H1 V (hl b List.mem_cons_self) ha)
          fun c hc => ih c (fun b' hb' => hl b' (List.mem_cons_of_mem _ hb')) hc
    refine key _ _ (fun b hb => hbl _ ?_) ⟨entsIn_empty, entsIn_empty⟩ s0 h0
    rw [Array.toList_map]
    exact List.mem_map_of_mem hb
  split at h
  · cases h
  · obtain rfl := Option.some.inj h
    exact hs0

end OnBytes.Desc.First.K4.Reads

#print axioms OnBytes.Desc.First.K4.Reads.stackEnd_ents
#print axioms OnBytes.Desc.First.K4.Reads.panelsA_in
#print axioms OnBytes.Desc.First.K4.Reads.panelsT_in
#print axioms OnBytes.Desc.First.K4.Reads.placePanels_in
