-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Slots/Panels.lean: THE TWO FORMS THAT THE END OF THE BATCHED SUMCHECK LEAVES NAME NO
SLOT: `StackEnd.Alin` and `StackEnd.Blin`, as `stackEnd` makes them over the placed panels of
`panelsA` and `panelsT` (OnBytes/Model/LayerPanels.lean), are `SlotsIn S` at every S. Definitions,
statements and proofs.

  `core b`: a panel's three fields that hold forms (A, B, xx). `CoreOk S c`: whatever A or B
    returns, and every member of xx, is `SlotsIn S`. `PanOk S bl`: so for each panel of the list.
  `plain_ok`, `tri_ok`, `panelA_ok`, `panelsA_ok`, `panelT_ok`, `panelsT_ok`: the lists of panels.
  `placePanels_ok`: placing turns a panel's first place alone (`map_modify_same`, HideLaws.lean).
  `stackEndOf_ok`, **`stackEnd_slots`**: the end.

Limits. Nothing on which entries are named, or on what the forms mean. Nothing on soundness.

-/
import Johnson.Road.K4.Slots.Gives
import OnBytes.Model.LayerPanels
import OnBytes.Model.HideLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Slots

open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Road (map_some)
open OnBytes.Desc.First.K4.Reads (all_mapM)

variable {S : ℕ → Prop}

/-- A side of a panel, given as forms. -/
abbrev Side : Type := Option (ℕ → ℕ → Option Aff)

/-- Whatever the side returns names slots with S alone. -/
def SideOk (S : ℕ → Prop) (A : Side) : Prop := ∀ f, A = some f → ∀ i y, Gives (f i y) (SlotsIn S)

theorem sideOk_none : SideOk S none := fun _ e => by cases e

theorem sideOk_some {g : ℕ → ℕ → Option Aff} (h : ∀ i y, Gives (g i y) (SlotsIn S)) :
    SideOk S (some g) := fun _ e => Option.some.inj e ▸ h

/-- A panel's three fields that hold forms. -/
def core (b : SBlk) : Side × Side × Array Aff := (b.A, b.B, b.xx)

def CoreOk (S : ℕ → Prop) (c : Side × Side × Array Aff) : Prop :=
  SideOk S c.1 ∧ SideOk S c.2.1 ∧ ∀ k, SlotsIn S (c.2.2.getD k {})

def PanOk (S : ℕ → Prop) (bl : Array SBlk) : Prop := ∀ c ∈ (bl.map core).toList, CoreOk S c

theorem panOk_empty : PanOk S #[] := fun c hc => by simp at hc

theorem panOk_push {bl : Array SBlk} {b : SBlk} (h : PanOk S bl) (hb : CoreOk S (core b)) :
    PanOk S (bl.push b) := fun c hc => by
  simp only [Array.map_push, Array.toList_push, List.mem_append, List.mem_singleton] at hc
  rcases hc with hc | rfl
  · exact h c hc
  · exact hb

theorem slotsIn_getD_empty (k : ℕ) : SlotsIn S ((#[] : Array Aff).getD k {}) := by
  have e : (#[] : Array Aff).getD k {} = {} := by simp [Array.getD]
  rw [e]
  exact slotsIn_empty

theorem plain_ok (y : Lay) (ec : E) (claim : ℕ) (moeSet : Bool) (ny : ℕ) {A B : Side} (wt : ℕ → E)
    (virt : Option ℕ) {s : Panels} (hs : PanOk S s.bl) (hA : SideOk S A) (hB : SideOk S B) :
    PanOk S (plain y ec claim moeSet ny A B wt virt s).bl := by
  unfold plain
  refine panOk_push hs ⟨fun f hf i yv => ?_, fun f hf i yv => ?_, slotsIn_getD_empty⟩
  · obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hf
    exact hA g hg _ _
  · obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hf
    exact hB g hg _ _

theorem tri_ok (y : Lay) (ec : E) (claim nk : ℕ) (sl : Array E) {xx : Array Aff}
    (virt : Option ℕ) (wt : E) {s : Panels} (hs : PanOk S s.bl)
    (hx : ∀ k, SlotsIn S (xx.getD k {})) : PanOk S (tri y ec claim nk sl xx virt wt s).bl := by
  unfold tri
  exact panOk_push hs ⟨sideOk_none, sideOk_none, hx⟩

theorem foldl_inv {α β : Type} {P : β → Prop} {f : β → α → β} (h : ∀ b a, P b → P (f b a)) :
    ∀ (l : List α) (b : β), P b → P (l.foldl f b)
  | [], _, hb => hb
  | a :: l, b, hb => foldl_inv h l (f b a) (h b a hb)

theorem gives_foldlM_inv {α β : Type} {P : β → Prop} {step : β → α → Option β}
    (hs : ∀ b x, P b → Gives (step b x) P) : ∀ (l : List α) (b : β), P b → Gives (l.foldlM step b) P
  | [], b, hb => Gives.pure hb
  | x :: l, b, hb => by
    rw [List.foldlM_cons]
    exact Gives.bind (hs b x hb) fun c hc => gives_foldlM_inv hs l c hc

theorem panelA_ok (p : PanelEnv) (ec : E) (el : Array E) (sn : String) {s : Panels}
    (hs : PanOk S s.bl) : PanOk S (panelA p ec el sn s).bl := by
  unfold panelA
  dsimp only
  split
  · exact plain_ok _ _ _ _ _ _ _ hs (sideOk_some fun _ _ => gives_shIn _ _ _) sideOk_none
  split
  · exact plain_ok _ _ _ _ _ _ _ hs (sideOk_some fun _ _ => gives_shIn _ _ _) sideOk_none
  split
  · refine plain_ok _ _ _ _ _ _ _ hs (sideOk_some fun _ _ => ?_) sideOk_none
    refine Gives.ite (gives_shIn _ _ _) (Gives.some ?_)
    unfold stubAt
    exact slotsIn_ofConst _
  split
  · exact plain_ok _ _ _ _ _ _ _ hs sideOk_none sideOk_none
  split
  · exact plain_ok _ _ _ _ _ _ _ hs (sideOk_some fun _ _ => gives_shIn _ _ _) sideOk_none
  · exact hs

theorem panelsA_ok (p : PanelEnv) {s : Panels} (hs : PanOk S s.bl) :
    PanOk S (panelsA p s).bl := by
  unfold panelsA
  refine foldl_inv (P := fun s : Panels => PanOk S s.bl) (fun s q hs => ?_) _ _ hs
  exact foldl_inv (P := fun s : Panels => PanOk S s.bl) (fun s g hs => panelA_ok _ _ _ _ hs) _ _ hs

/-- Every member of an array that a function has filled. -/
theorem mapM_getD {n : ℕ} {g : ℕ → Option Aff} (hg : ∀ i, Gives (g i) (SlotsIn S)) :
    Gives ((Array.range n).mapM g) fun xx => ∀ k, SlotsIn S (xx.getD k {}) := by
  intro xx h k
  rw [Array.mapM_eq_mapM_toList] at h
  obtain ⟨ys, hys, e⟩ := map_some h
  subst e
  by_cases hj : k < ys.length
  · have e : ys.toArray.getD k {} = ys[k] := by simp [Array.getD, hj]
    rw [e]
    exact all_mapM (Pr := SlotsIn S) (fun i a ha => hg i a ha) _ ys hys _ (List.getElem_mem hj)
  · have e : ys.toArray.getD k {} = {} := by simp [Array.getD, hj]
    rw [e]
    exact slotsIn_empty

theorem panelT_ok (p : PanelEnv) (ec : E) (el : Array E) (sn : String) {s : Panels}
    (hs : PanOk S s.bl) : Gives (panelT p ec el sn s) fun s' => PanOk S s'.bl := by
  unfold panelT
  dsimp only
  refine Gives.ite ?_ (Gives.ite ?_ (Gives.ite ?_ (Gives.ite ?_ (Gives.ite ?_ (Gives.ite ?_ ?_)))))
  · exact Gives.skip fun wh => Gives.pure (plain_ok _ _ _ _ _ _ _ hs
      (sideOk_some fun _ _ => Gives.some (slotsIn_ofConst _))
      (sideOk_some fun _ _ => gives_SxsA _ _ _))
  · exact Gives.pure (plain_ok _ _ _ _ _ _ _ hs (sideOk_some fun _ _ => gives_shIn _ _ _)
      sideOk_none)
  · exact Gives.pure hs
  · exact Gives.skip fun ew => Gives.pure (plain_ok _ _ _ _ _ _ _ hs
      (sideOk_some fun _ _ => Gives.some (slotsIn_ofConst _))
      (sideOk_some fun _ _ => gives_shSum _ _ _ _ _))
  · exact Gives.skip fun ew => Gives.pure (plain_ok _ _ _ _ _ _ _ hs
      (sideOk_some fun _ _ => Gives.some (slotsIn_ofConst _))
      (sideOk_some fun _ _ => gives_shA _ _ _ _))
  · refine gives_foldlM_inv (P := fun s : Panels => PanOk S s.bl) (fun s lm hs => ?_) _ _ hs
    refine Gives.ite (Gives.pure (tri_ok _ _ _ _ _ _ _ hs slotsIn_getD_empty)) ?_
    exact Gives.bind (mapM_getD fun _ => gives_shIn _ _ _) fun xx hx =>
      Gives.pure (tri_ok _ _ _ _ _ _ _ hs hx)
  · exact Gives.pure hs

theorem panelsT_ok (p : PanelEnv) (TS : List ℕ) {s : Panels} (hs : PanOk S s.bl) :
    Gives (panelsT p TS s) fun s' => PanOk S s'.bl := by
  unfold panelsT
  refine gives_foldlM_inv (P := fun s : Panels => PanOk S s.bl) (fun s q hs => ?_) _ _ hs
  exact gives_foldlM_inv (P := fun s : Panels => PanOk S s.bl)
    (fun s g hs => panelT_ok _ _ _ _ hs) _ _ hs

/-- Placing turns a panel's first place alone. -/
theorem placePanels_ok {bl : Array SBlk} (h : PanOk S bl) : PanOk S (placePanels bl).1 := by
  unfold placePanels
  refine foldl_inv (P := fun s : Array SBlk × ℕ => PanOk S s.1) (fun s i hs => ?_) _ _ h
  show PanOk S (s.1.modify i fun b => { b with off := s.2 })
  unfold PanOk
  rw [map_modify_same core (fun b : SBlk => { b with off := s.2 }) (fun _ => rfl)]
  exact hs

/-! ### The end -/

/-- The two forms of the end name slots with S alone. -/
def EndOk (S : ℕ → Prop) (s : StackEnd) : Prop := SlotsIn S s.Alin ∧ SlotsIn S s.Blin

/-- **What one panel adds.** -/
theorem stackEndOf_ok (y : Lay) (rs : Array E) (lam : ℕ) (om H1 V : Array E) {s : StackEnd}
    {b : SBlk} (hb : CoreOk S (core b)) (hs : EndOk S s) :
    Gives (stackEndOf y rs lam om H1 V s b) (EndOk S) := by
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
      exact ⟨slotsIn_foldl _ (fun a k2 ha => slotsIn_addMul _ ha (hx k2)) _ _ hs.1, hs.2⟩
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
        refine gives_foldlM_inv (P := EndOk S) (fun s i hs => ?_) _ _ hs
        refine Gives.bind (Φ := EndOk S) ?_ fun s hs => Gives.pure ?_
        · refine gives_foldlM_inv (P := EndOk S) (fun s yv hs => ?_) _ _ hs
          refine Gives.bind (hA A hAe i yv) fun a ha => Gives.pure ?_
          exact ⟨slotsIn_addMul _ hs.1 ha, hs.2⟩
        · exact ⟨hs.1, hs.2⟩
      | none =>
        cases hBe : b.B with
        | none =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine Gives.ite (guard _ _) (Gives.skip fun _ => ?_)
          refine Gives.skip fun A => ?_
          refine gives_foldlM_inv (P := EndOk S) (fun s i hs => ?_) _ _ hs
          refine Gives.bind (Φ := EndOk S) ?_ fun s hs => Gives.pure hs
          refine gives_foldlM_inv (P := EndOk S) (fun s yv hs => ?_) _ _ hs
          exact Gives.skip fun _ => Gives.none
        | some B =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine Gives.ite (guard _ _) (Gives.skip fun _ => ?_)
          refine Gives.bind (Φ := fun A => b.A = some A) (fun _ h => h) fun A hAe => ?_
          refine gives_foldlM_inv (P := EndOk S) (fun s i hs => ?_) _ _ hs
          refine Gives.bind (Φ := EndOk S) ?_ fun s hs => Gives.pure hs
          refine gives_foldlM_inv (P := EndOk S) (fun s yv hs => ?_) _ _ hs
          refine Gives.bind (hA A hAe i yv) fun a ha =>
            Gives.bind (hB B hBe i yv) fun c hc => Gives.pure ?_
          exact ⟨slotsIn_addMul _ hs.1 ha, slotsIn_addMul _ hs.2 hc⟩

/-- **The end of the batched sumcheck over all panels.** -/
theorem stackEnd_slots {y : Lay} {bl : Array SBlk} {rs : Array E} {lam : ℕ} {om H1 V : Array E}
    {shownA shownB : E} {s : StackEnd} (hbl : PanOk S bl)
    (h : stackEnd y bl rs lam om H1 V shownA shownB = some s) : EndOk S s := by
  unfold stackEnd at h
  obtain ⟨s0, h0, h⟩ := Option.bind_eq_some_iff.mp h
  have hs0 : EndOk S s0 := by
    rw [← Array.foldlM_toList] at h0
    have key : ∀ (l : List SBlk) (a : StackEnd), (∀ b ∈ l, CoreOk S (core b)) → EndOk S a →
        Gives (l.foldlM (stackEndOf y rs lam om H1 V) a) (EndOk S) := by
      intro l
      induction l with
      | nil => exact fun a _ ha => Gives.pure ha
      | cons b l ih =>
        intro a hl ha
        rw [List.foldlM_cons]
        exact Gives.bind (stackEndOf_ok y rs lam om H1 V (hl b List.mem_cons_self) ha)
          fun c hc => ih c (fun b' hb' => hl b' (List.mem_cons_of_mem _ hb')) hc
    refine key _ _ (fun b hb => hbl _ ?_) ⟨slotsIn_empty, slotsIn_empty⟩ s0 h0
    rw [Array.toList_map]
    exact List.mem_map_of_mem hb
  split at h
  · cases h
  · obtain rfl := Option.some.inj h
    exact hs0

end OnBytes.Desc.First.K4.Slots

#print axioms OnBytes.Desc.First.K4.Slots.stackEnd_slots
#print axioms OnBytes.Desc.First.K4.Slots.panelsA_ok
#print axioms OnBytes.Desc.First.K4.Slots.panelsT_ok
#print axioms OnBytes.Desc.First.K4.Slots.placePanels_ok
