-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/PanelsBelow.lean: CONDITIONAL.

Not shown here. TabFront at the panels' environment: a hypothesis (Below.lean's tabFront_of_lay
gives it where layTables has returned). That the panels at which the honest side makes its end
values are the verifier's. No example is known. No property is claimed.

THE TWO FORMS THAT THE END OF THE BATCHED SUMCHECK LEAVES NAME ENTRIES IN FRONT OF THE FAMILY
"b-bits-0": StackEnd.Alin and StackEnd.Blin, as stackEnd makes them over the placed panels of
panelsA and panelsT (OnBytes/Model/LayerPanels.lean). So their entries lie off the matrix of the
lookup's planes, which StackSides.lean asks (hGA, hGB).

FROM SideLow ON THE TEXT IS MADE BY PROGRAM out of the library's
Johnson/Road/K4/Reads/PanelsEnts.lean, which shows the same walk for «inside the families of
tables» (and was itself made by program out of Johnson/Road/K4/Slots/Panels.lean): InTab v became
Below v tB0; the readers' ge_x became gb_x, which take TabFront; in the four theorems on a PanelEnv
p the hypothesis F : TabFront p.v tB0 is new. Side, core, foldl_inv, gives_foldlM_inv and Gives
with its rules are the library's and are not typed again.

  gb_U3at, gb_sumForms, gb_mapP, gb_longA, gb_xbA   the readers, in the form «wherever it is there».
  FoundLow, found_tensorAt   what tensorAt finds begins in front of tB0.
  gb_shIn, gb_shA, gb_shSum, sxs_head, gb_SxsA   the readers that the panels call.
  SideLow, CoreLow, PanLow, EndLow   a side; a panel's two sides and its xx; a list of panels; the
                 end's two forms.
  plain_low, tri_low, panelA_low, panelsA_low, panelT_low, panelsT_low, placePanels_low   the
                 panels.
  stackEndOf_low, stackEnd_below   the end, over any list of panels with PanLow.
  sides_off      hGA and hGB of StackSides.lean, at G := off the planes' matrix.
-/
import Johnson.Road.K4.C.Below
import Johnson.Road.K4.Reads.PanelsEnts

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Road (map_some bind_some)
open OnBytes.Desc.First.K4.Slots (Gives Side core gives_foldlM_inv)
open OnBytes.Desc.First.K4.Reads (entsIn_ofConst entsIn_empty entsIn_addMul entsIn_foldl all_mapM)
open OnBytes.Desc.First.K4.Honest (K4Pub matsOf)

variable {v : Env} {tB0 : ℕ}

/-! ## The readers

Each law of this part says of one reader of the environment v: wherever it returns a form, that form
names entries in front of the place tB0 alone (Below v tB0). The docstring names the reader. -/

/-- One entry of a family that begins in front of tB0. -/
theorem gb_U3at (F : TabFront v tB0) {t : ℕ} (ht : t < tB0) (i : ℕ) :
    Gives (v.U3at t i) (Below v tB0) := fun _ h => below_U3at F ht h

/-- The verifier's sum of forms. -/
theorem gb_sumForms {n : ℕ} {g : ℕ → Option (Aff × E)}
    (hg : ∀ x, Gives (g x) fun p => Below v tB0 p.1) : Gives (sumForms n g) (Below v tB0) :=
  fun _ h => below_sumForms (fun x p hp => hg x p hp) h

/-- A form with a weight beside it. -/
theorem gb_mapP {x : Option Aff} {f : Aff → Aff × E} (hx : Gives x (Below v tB0))
    (hf : ∀ a, Below v tB0 a → Below v tB0 (f a).1) :
    Gives (x.map f) fun p => Below v tB0 p.1 :=
  Gives.map hx hf

/-- A block of a tensor, read from a long table. -/
theorem gb_longA (F : TabFront v tB0) {t : ℕ} (ht : t < tB0) (X : Ten) (i jh : ℕ) :
    Gives (v.longA t X i jh) (Below v tB0) := fun _ h => below_limbs F ht h

/-- A block of a residual stream, read from a long table. -/
theorem gb_xbA (F : TabFront v tB0) {t : ℕ} (ht : t < tB0) (kh : ℕ) :
    Gives (v.xbA t kh) (Below v tB0) := fun _ h => below_limbs F ht h

/-- What has been found begins in front of tB0. -/
def FoundLow (tB0 : ℕ) (found : Option (Ten × ℕ)) : Prop := ∀ x, found = some x → x.2 < tB0

/-- What tensorAt finds begins in front of tB0. -/
theorem found_tensorAt (F : TabFront v tB0) (X Z : String) : FoundLow tB0 (v.tensorAt X Z) := by
  intro x hx
  unfold Env.tensorAt at hx
  obtain ⟨t, -, hx⟩ := bind_some hx
  obtain ⟨tb, htb, hx⟩ := bind_some hx
  obtain rfl := Option.some.inj hx
  exact F.front _ _ htb (mname_head _ _)

/-- An entry of the tensor that has been found. -/
theorem gb_shIn (F : TabFront v tB0) {found : Option (Ten × ℕ)} (hf : FoundLow tB0 found)
    (i j : ℕ) : Gives (v.shIn found i j) (Below v tB0) := by
  intro s h
  unfold Env.shIn at h
  obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
  exact below_limbs F (hf x hx) h

/-- An entry of a tensor at a token point. -/
theorem gb_shA (F : TabFront v tB0) (X P : String) (i j : ℕ) :
    Gives (v.shA X P i j) (Below v tB0) := gb_shIn F (found_tensorAt F X P) i j

/-- A weighted sum of a tensor's entries at a token point. -/
theorem gb_shSum (F : TabFront v tB0) (ew : Array E) (n : ℕ) (X P : String) (i : ℕ) :
    Gives (v.shSum ew n X P i) (Below v tB0) := by
  unfold Env.shSum
  exact gb_sumForms fun x => gb_mapP (gb_shIn F (found_tensorAt F _ _) _ _) fun _ h => h

/-- The name of a residual stream's family at a point does not begin with the letter b. -/
theorem sxs_head (c1 c2 : Bool) (Z : String) :
    ((if c1 then "xbI" else if c2 then "xbO" else "af") ++ "@" ++ Z).toList.head? ≠ some 'b' := by
  rw [String.toList_append, String.toList_append]
  cases c1
  · cases c2
    · exact head_or (c := 'a') (by decide) (by decide)
    · exact head_or (c := 'x') (by decide) (by decide)
  · cases c2
    · exact head_or (c := 'x') (by decide) (by decide)
    · exact head_or (c := 'x') (by decide) (by decide)

/-- A weighted sum of the blocks of a residual stream. -/
theorem gb_SxsA (F : TabFront v tB0) (wh : Array E) (Z : String) (sg : ℕ) :
    Gives (v.SxsA wh Z sg) (Below v tB0) := by
  unfold Env.SxsA
  dsimp only
  refine Gives.bind (Φ := fun tb => tb < tB0) (fun tb htb => F.front _ _ htb (sxs_head _ _ _))
    fun tb ht => Gives.skip fun txs => ?_
  exact gb_sumForms fun xh =>
    gb_mapP (Gives.ite (gb_xbA F ht _) (gb_longA F ht _ _ _)) fun _ h => h

/-! ## The panels and the end

Each law of this part says the same of what a maker of panels lays: its sides' forms and its xx
(PanLow), and at last of the end's two forms (EndLow). The docstring names the maker. -/

/-- Whatever the side returns names entries in front of the place tB0 alone. -/
def SideLow (v : Env) (tB0 : ℕ) (A : Side) : Prop :=
  ∀ f, A = some f → ∀ i y, Gives (f i y) (Below v tB0)

/-- No side. -/
theorem sideLow_none : SideLow v tB0 none := fun _ e => by cases e

/-- A side that is there. -/
theorem sideLow_some {g : ℕ → ℕ → Option Aff} (h : ∀ i y, Gives (g i y) (Below v tB0)) :
    SideLow v tB0 (some g) := fun _ e => Option.some.inj e ▸ h

/-- Whatever a panel's A or B side returns, and every member of its xx, names entries in front
of the place tB0 alone. -/
def CoreLow (v : Env) (tB0 : ℕ) (c : Side × Side × Array Aff) : Prop :=
  SideLow v tB0 c.1 ∧ SideLow v tB0 c.2.1 ∧ ∀ k, Below v tB0 (c.2.2.getD k {})

/-- So for each panel of the list. -/
def PanLow (v : Env) (tB0 : ℕ) (bl : Array SBlk) : Prop :=
  ∀ c ∈ (bl.map core).toList, CoreLow v tB0 c

/-- No panel. -/
theorem panLow_empty : PanLow v tB0 #[] := fun c hc => by simp at hc

/-- One panel more. -/
theorem panLow_push {bl : Array SBlk} {b : SBlk} (h : PanLow v tB0 bl)
    (hb : CoreLow v tB0 (core b)) :
    PanLow v tB0 (bl.push b) := fun c hc => by
  simp only [Array.map_push, Array.toList_push, List.mem_append, List.mem_singleton] at hc
  rcases hc with hc | rfl
  · exact h c hc
  · exact hb

/-- A member of the empty array of forms. -/
theorem below_getD_empty (k : ℕ) : Below v tB0 ((#[] : Array Aff).getD k {}) := by
  have e : (#[] : Array Aff).getD k {} = {} := by simp [Array.getD]
  rw [e]
  exact entsIn_empty

/-- A plain panel. -/
theorem plain_low (y : Lay) (ec : E) (claim : ℕ) (moeSet : Bool) (ny : ℕ) {A B : Side} (wt : ℕ → E)
    (virt : Option ℕ) {s : Panels} (hs : PanLow v tB0 s.bl) (hA : SideLow v tB0 A)
    (hB : SideLow v tB0 B) :
    PanLow v tB0 (plain y ec claim moeSet ny A B wt virt s).bl := by
  unfold plain
  refine panLow_push hs ⟨fun f hf i yv => ?_, fun f hf i yv => ?_, below_getD_empty⟩
  · obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hf
    exact hA g hg _ _
  · obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hf
    exact hB g hg _ _

/-- A panel with the selector. -/
theorem tri_low (y : Lay) (ec : E) (claim nk : ℕ) (sl : Array E) {xx : Array Aff}
    (virt : Option ℕ) (wt : E) {s : Panels} (hs : PanLow v tB0 s.bl)
    (hx : ∀ k, Below v tB0 (xx.getD k {})) :
    PanLow v tB0 (tri y ec claim nk sl xx virt wt s).bl := by
  unfold tri
  exact panLow_push hs ⟨sideLow_none, sideLow_none, hx⟩

/-- The panels of one segment of a call of the lookup's join. -/
theorem panelA_low (p : PanelEnv) (F : TabFront p.v tB0) (ec : E) (el : Array E) (sn : String)
    {s : Panels} (hs : PanLow p.v tB0 s.bl) : PanLow p.v tB0 (panelA p ec el sn s).bl := by
  unfold panelA
  dsimp only
  split
  · exact plain_low _ _ _ _ _ _ _ hs
      (sideLow_some fun _ _ => gb_shIn F (found_tensorAt F _ _) _ _) sideLow_none
  split
  · exact plain_low _ _ _ _ _ _ _ hs
      (sideLow_some fun _ _ => gb_shIn F (found_tensorAt F _ _) _ _) sideLow_none
  split
  · refine plain_low _ _ _ _ _ _ _ hs (sideLow_some fun _ _ => ?_) sideLow_none
    refine Gives.ite (gb_shIn F (found_tensorAt F _ _) _ _) (Gives.some ?_)
    unfold stubAt
    exact entsIn_ofConst _
  split
  · exact plain_low _ _ _ _ _ _ _ hs sideLow_none sideLow_none
  split
  · exact plain_low _ _ _ _ _ _ _ hs
      (sideLow_some fun _ _ => gb_shIn F (found_tensorAt F _ _) _ _) sideLow_none
  · exact hs

/-- The panels of the calls of the lookup's join. -/
theorem panelsA_low (p : PanelEnv) (F : TabFront p.v tB0) {s : Panels} (hs : PanLow p.v tB0 s.bl) :
    PanLow p.v tB0 (panelsA p s).bl := by
  unfold panelsA
  refine OnBytes.Desc.First.K4.Slots.foldl_inv (P := fun s : Panels => PanLow p.v tB0 s.bl)
    (fun s q hs => ?_) _ _ hs
  exact OnBytes.Desc.First.K4.Slots.foldl_inv (P := fun s : Panels => PanLow p.v tB0 s.bl)
    (fun s g hs => panelA_low _ F _ _ _ hs) _ _ hs

/-- Every member of an array that a function has filled. -/
theorem mapM_getD_low {n : ℕ} {g : ℕ → Option Aff} (hg : ∀ i, Gives (g i) (Below v tB0)) :
    Gives ((Array.range n).mapM g) fun xx => ∀ k, Below v tB0 (xx.getD k {}) := by
  intro xx h k
  rw [Array.mapM_eq_mapM_toList] at h
  obtain ⟨ys, hys, e⟩ := map_some h
  subst e
  by_cases hj : k < ys.length
  · have e : ys.toArray.getD k {} = ys[k] := by simp [Array.getD, hj]
    rw [e]
    exact all_mapM (Pr := Below v tB0) (fun i a ha => hg i a ha) _ ys hys _ (List.getElem_mem hj)
  · have e : ys.toArray.getD k {} = {} := by simp [Array.getD, hj]
    rw [e]
    exact entsIn_empty

/-- The panels of one segment of a call with terms in the second token sumcheck. -/
theorem panelT_low (p : PanelEnv) (F : TabFront p.v tB0) (ec : E) (el : Array E) (sn : String)
    {s : Panels} (hs : PanLow p.v tB0 s.bl) :
    Gives (panelT p ec el sn s) fun s' => PanLow p.v tB0 s'.bl := by
  unfold panelT
  dsimp only
  refine Gives.ite ?_ (Gives.ite ?_ (Gives.ite ?_ (Gives.ite ?_ (Gives.ite ?_ (Gives.ite ?_ ?_)))))
  · exact Gives.skip fun wh => Gives.pure (plain_low _ _ _ _ _ _ _ hs
      (sideLow_some fun _ _ => Gives.some (entsIn_ofConst _))
      (sideLow_some fun _ _ => gb_SxsA F _ _ _))
  · exact Gives.pure (plain_low _ _ _ _ _ _ _ hs
      (sideLow_some fun _ _ => gb_shIn F (found_tensorAt F _ _) _ _) sideLow_none)
  · exact Gives.pure hs
  · exact Gives.skip fun ew => Gives.pure (plain_low _ _ _ _ _ _ _ hs
      (sideLow_some fun _ _ => Gives.some (entsIn_ofConst _))
      (sideLow_some fun _ _ => gb_shSum F _ _ _ _ _))
  · exact Gives.skip fun ew => Gives.pure (plain_low _ _ _ _ _ _ _ hs
      (sideLow_some fun _ _ => Gives.some (entsIn_ofConst _))
      (sideLow_some fun _ _ => gb_shA F _ _ _ _))
  · refine gives_foldlM_inv (P := fun s : Panels => PanLow p.v tB0 s.bl) (fun s lm hs => ?_) _ _ hs
    refine Gives.ite (Gives.pure (tri_low _ _ _ _ _ _ _ hs below_getD_empty)) ?_
    exact Gives.bind (mapM_getD_low fun _ => gb_shIn F (found_tensorAt F _ _) _ _) fun xx hx =>
      Gives.pure (tri_low _ _ _ _ _ _ _ hs hx)
  · exact Gives.pure hs

/-- The panels of the calls with terms in the second token sumcheck. -/
theorem panelsT_low (p : PanelEnv) (F : TabFront p.v tB0) (TS : List ℕ) {s : Panels}
    (hs : PanLow p.v tB0 s.bl) :
    Gives (panelsT p TS s) fun s' => PanLow p.v tB0 s'.bl := by
  unfold panelsT
  refine gives_foldlM_inv (P := fun s : Panels => PanLow p.v tB0 s.bl) (fun s q hs => ?_) _ _ hs
  exact gives_foldlM_inv (P := fun s : Panels => PanLow p.v tB0 s.bl)
    (fun s g hs => panelT_low _ F _ _ _ hs) _ _ hs

/-- Placing turns a panel's first place alone. -/
theorem placePanels_low {bl : Array SBlk} (h : PanLow v tB0 bl) :
    PanLow v tB0 (placePanels bl).1 := by
  unfold placePanels
  refine OnBytes.Desc.First.K4.Slots.foldl_inv (P := fun s : Array SBlk × ℕ => PanLow v tB0 s.1)
    (fun s i hs => ?_) _ _ h
  show PanLow v tB0 (s.1.modify i fun b => { b with off := s.2 })
  unfold PanLow
  rw [map_modify_same core (fun b : SBlk => { b with off := s.2 }) (fun _ => rfl)]
  exact hs

/-! ### The end -/

/-- The two forms of the end name entries in front of the place tB0 alone. -/
def EndLow (v : Env) (tB0 : ℕ) (s : StackEnd) : Prop := Below v tB0 s.Alin ∧ Below v tB0 s.Blin

/-- **What one panel adds.** -/
theorem stackEndOf_low (y : Lay) (rs : Array E) (lam : ℕ) (om H1 V : Array E) {s : StackEnd}
    {b : SBlk} (hb : CoreLow v tB0 (core b)) (hs : EndLow v tB0 s) :
    Gives (stackEndOf y rs lam om H1 V s b) (EndLow v tB0) := by
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
        refine gives_foldlM_inv (P := EndLow v tB0) (fun s i hs => ?_) _ _ hs
        refine Gives.bind (Φ := EndLow v tB0) ?_ fun s hs => Gives.pure ?_
        · refine gives_foldlM_inv (P := EndLow v tB0) (fun s yv hs => ?_) _ _ hs
          refine Gives.bind (hA A hAe i yv) fun a ha => Gives.pure ?_
          exact ⟨entsIn_addMul _ hs.1 ha, hs.2⟩
        · exact ⟨hs.1, hs.2⟩
      | none =>
        cases hBe : b.B with
        | none =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine Gives.ite (guard _ _) (Gives.skip fun _ => ?_)
          refine Gives.skip fun A => ?_
          refine gives_foldlM_inv (P := EndLow v tB0) (fun s i hs => ?_) _ _ hs
          refine Gives.bind (Φ := EndLow v tB0) ?_ fun s hs => Gives.pure hs
          refine gives_foldlM_inv (P := EndLow v tB0) (fun s yv hs => ?_) _ _ hs
          exact Gives.skip fun _ => Gives.none
        | some B =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine Gives.ite (guard _ _) (Gives.skip fun _ => ?_)
          refine Gives.bind (Φ := fun A => b.A = some A) (fun _ h => h) fun A hAe => ?_
          refine gives_foldlM_inv (P := EndLow v tB0) (fun s i hs => ?_) _ _ hs
          refine Gives.bind (Φ := EndLow v tB0) ?_ fun s hs => Gives.pure hs
          refine gives_foldlM_inv (P := EndLow v tB0) (fun s yv hs => ?_) _ _ hs
          refine Gives.bind (hA A hAe i yv) fun a ha =>
            Gives.bind (hB B hBe i yv) fun c hc => Gives.pure ?_
          exact ⟨entsIn_addMul _ hs.1 ha, entsIn_addMul _ hs.2 hc⟩

/-- **The end of the batched sumcheck over all panels.** -/
theorem stackEnd_below {y : Lay} {bl : Array SBlk} {rs : Array E} {lam : ℕ} {om H1 V : Array E}
    {shownA shownB : E} {s : StackEnd} (hbl : PanLow v tB0 bl)
    (h : stackEnd y bl rs lam om H1 V shownA shownB = some s) : EndLow v tB0 s := by
  unfold stackEnd at h
  obtain ⟨s0, h0, h⟩ := Option.bind_eq_some_iff.mp h
  have hs0 : EndLow v tB0 s0 := by
    rw [← Array.foldlM_toList] at h0
    have key : ∀ (l : List SBlk) (a : StackEnd), (∀ b ∈ l, CoreLow v tB0 (core b)) →
        EndLow v tB0 a →
        Gives (l.foldlM (stackEndOf y rs lam om H1 V) a) (EndLow v tB0) := by
      intro l
      induction l with
      | nil => exact fun a _ ha => Gives.pure ha
      | cons b l ih =>
        intro a hl ha
        rw [List.foldlM_cons]
        exact Gives.bind (stackEndOf_low y rs lam om H1 V (hl b List.mem_cons_self) ha)
          fun c hc => ih c (fun b' hb' => hl b' (List.mem_cons_of_mem _ hb')) hc
    refine key _ _ (fun b hb => hbl _ ?_) ⟨entsIn_empty, entsIn_empty⟩ s0 h0
    rw [Array.toList_map]
    exact List.mem_map_of_mem hb
  split at h
  · cases h
  · obtain rfl := Option.some.inj h
    exact hs0


/-! ## What StackSides.lean asks -/

/-- **The two forms' entries lie off the matrix of the lookup's planes**: hGA and hGB of
StackSides.lean's sides_read, at G := off that matrix. pe: the panels' environment. -/
theorem sides_off {Q : K4Pub} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r) {fo' : Forest.Heard}
    {pts : List (String × Array E)} {tl : HTailF2} {funs : Array HFun}
    (hf : funsOf Q.P.y fo' pts r.2.1 = some funs) {pe : PanelEnv} (hv : pe.v.tab = r.1)
    (hB : pe.v.tabAt "b-bits-0" = some tB0) {TS : List ℕ} {pans : Panels}
    (hp : panelsT pe TS (panelsA pe {}) = some pans) {y : Lay} {rs : Array E} {lam : ℕ}
    {om H1 V : Array E} {a b : E} {fin : StackEnd}
    (hfin : stackEnd y (placePanels pans.bl).1 rs lam om H1 V a b = some fin) :
    (∀ x ∈ fin.Alin.ents.toList, ∀ z : HFun × ℕ × ℕ, z.1 ∈ funs →
      tl.tabAt z.1 z.2.1 z.2.2 = some (x.row * pe.v.K3 + x.idx) → z.1.mat ≠ (matIx Q.P.y).iB) ∧
    (∀ x ∈ fin.Blin.ents.toList, ∀ z : HFun × ℕ × ℕ, z.1 ∈ funs →
      tl.tabAt z.1 z.2.1 z.2.2 = some (x.row * pe.v.K3 + x.idx) → z.1.mat ≠ (matIx Q.P.y).iB) := by
  have F := tabFront_of_lay hl hv hB
  have h1 : PanLow pe.v tB0 pans.bl := panelsT_low pe F TS (panelsA_low pe F panLow_empty) pans hp
  obtain ⟨eA, eB⟩ := stackEnd_below (placePanels_low h1) hfin
  exact ⟨hG_of_lt hl hf hv hB eA, hG_of_lt hl hf hv hB eB⟩

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.gb_U3at
#print axioms OnBytes.Road.K4.C.gb_sumForms
#print axioms OnBytes.Road.K4.C.gb_mapP
#print axioms OnBytes.Road.K4.C.gb_longA
#print axioms OnBytes.Road.K4.C.gb_xbA
#print axioms OnBytes.Road.K4.C.found_tensorAt
#print axioms OnBytes.Road.K4.C.gb_shIn
#print axioms OnBytes.Road.K4.C.gb_shA
#print axioms OnBytes.Road.K4.C.gb_shSum
#print axioms OnBytes.Road.K4.C.sxs_head
#print axioms OnBytes.Road.K4.C.gb_SxsA
#print axioms OnBytes.Road.K4.C.sideLow_none
#print axioms OnBytes.Road.K4.C.sideLow_some
#print axioms OnBytes.Road.K4.C.panLow_empty
#print axioms OnBytes.Road.K4.C.panLow_push
#print axioms OnBytes.Road.K4.C.below_getD_empty
#print axioms OnBytes.Road.K4.C.plain_low
#print axioms OnBytes.Road.K4.C.tri_low
#print axioms OnBytes.Road.K4.C.panelA_low
#print axioms OnBytes.Road.K4.C.panelsA_low
#print axioms OnBytes.Road.K4.C.mapM_getD_low
#print axioms OnBytes.Road.K4.C.panelT_low
#print axioms OnBytes.Road.K4.C.panelsT_low
#print axioms OnBytes.Road.K4.C.placePanels_low
#print axioms OnBytes.Road.K4.C.stackEndOf_low
#print axioms OnBytes.Road.K4.C.stackEnd_below
#print axioms OnBytes.Road.K4.C.sides_off
