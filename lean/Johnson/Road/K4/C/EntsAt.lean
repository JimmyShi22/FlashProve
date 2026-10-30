-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/EntsAt.lean: CONDITIONAL.

What is here. The library shows that every form which the verifier's readers and its lists of panels
make names entries of the array of the reads that lie in SOME family of tables
(Johnson/Road/K4/Reads/TermsEnts.lean, GivesEnts.lean, PanelsEnts.lean). Here the same walk once
more, at a test T on an entry's place that the caller chooses, so that it can say IN WHICH families:
each reader picks its table by a name `prefix@point`; where every table under such a name, at the
points that the caller admits, has T at all its entries (`PtAt`), every form that these readers make
at these points has T at all the entries that it names (`InTest`). For the two lists of panels of
the batched sumcheck the points are zt, rt and Y (`panelsA_at`, `panelsT_at`, `placePanels_at`).
With T := «the honest reads hold the entry's family's weights» that is the yes of the honest side's
test affFits (`affFits_of_inTest`). The rules for sums are the library's (`EntsIn`, `Gives`).

  `InTest v T f`   each entry that f names lies in the array of the reads, at a place with T.
  `StartAt v T t`   the table that begins at t has T at all its entries.
  `PtAt v T S`   so has every table named prefix@Z, for the seven prefixes and each point Z with S.
  `inTest_U3at`, `at_sumForms`, `at_limbs`, `at_shortA`, `at_longA`, `at_xbA`   a table's readers.
  `at_tensorAt`, `at_shIn`, `at_shA`, `at_shSum`, `at_SxsA`   the readers that pick their table.
  `SideAt`, `CoreTest`, `PanAt`   a panel's two sides and its list xx; a list of panels.
  `plain_at`, `tri_at`, `panelA_at`, `panelsA_at`   the panels of the lookup's join.
  `panelT_at`, `panelsT_at`, `placePanels_at`   those of the second token sumcheck; placing.
  `affFits_of_inTest`   the honest side's test answers true.

Not shown here. PtAt: a hypothesis; no statement here shows it at any test. That a reader or a list
of panels returns: not here: each statement speaks of what is returned, if anything. The forms of
the batched sumcheck's end (stackEnd) and of the second token sumcheck's claims are not treated. As
in the library's files: an index that strays to another tensor, layer or limb of the same family is
not caught. Nothing on soundness, on completeness or on any other property. No property is claimed.
-/
import Johnson.Road.K4.Reads.PanelsEnts
import Johnson.Desc.K4.Honest.Cells

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Road (map_some bind_some)
open OnBytes.Desc.First.K4.Reads (EntsIn entsIn_ofConst entsIn_empty entsIn_ent entsIn_addMul
  all_mapM)
open OnBytes.Desc.First.K4.Slots (Gives Side core gives_foldlM_inv)

/-- Each entry that the form names lies in the array of the reads, at a place with T. -/
abbrev InTest (v : Env) (T : ℕ → Prop) (f : Aff) : Prop :=
  EntsIn (fun t r i => t = v.iU3 ∧ T (r * v.K3 + i)) f

/-- The table that begins at t has T at all its entries. This defines a hypothesis; the definition
claims nothing. -/
def StartAt (v : Env) (T : ℕ → Prop) (t : ℕ) : Prop :=
  ∀ x, (v.tab.find? fun z => z.first == t) = some x →
    ∀ e, x.first ≤ e → e < x.first + x.len → T e

/-- **Every table named prefix@Z, at a point Z with S, has T at all its entries.** This defines a
hypothesis; the definition claims nothing. -/
def PtAt (v : Env) (T : ℕ → Prop) (S : String → Prop) : Prop :=
  ∀ mn ∈ ["af", "ad", "ar", "qa", "xbI", "xbO", ""], ∀ Z t, S Z →
    v.tabAt (mn ++ "@" ++ Z) = some t → StartAt v T t

variable {v : Env} {T : ℕ → Prop} {S : String → Prop}

/-! ## The readers -/

/-- One entry. -/
theorem inTest_U3at {t : ℕ} (hs : StartAt v T t) (i : ℕ) : Gives (v.U3at t i) (InTest v T) := by
  intro f h
  unfold Env.U3at at h
  split at h
  · cases h
  · rename_i x hx
    dsimp only at h
    split at h
    · rename_i hc
      cases h
      have hf : x.first = t := by
        have h1 := List.find?_some hx
        simpa using h1
      have hi : i < x.len := by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        exact hc.1.1
      have e : (t + i) / v.K3 * v.K3 + (t + i) % v.K3 = t + i := Nat.div_add_mod' _ _
      exact entsIn_ent ⟨rfl, by rw [e]; exact hs x hx _ (by omega) (by omega)⟩
    · cases h

/-- A sum made by a loop that may return nothing. -/
theorem at_foldlM {g : ℕ → Option (Aff × E)} (hg : ∀ x, Gives (g x) fun p => InTest v T p.1) :
    ∀ (l : List ℕ) (a : Aff), InTest v T a →
      Gives (l.foldlM (fun a x => (g x).map fun t => a.addMul t.1 t.2) a) (InTest v T)
  | [], a, ha => fun s h => by
    cases h
    exact ha
  | x :: l, a, ha => fun s h => by
    rw [List.foldlM_cons] at h
    obtain ⟨b, hb, h⟩ := bind_some h
    obtain ⟨p, hp, e⟩ := map_some hb
    subst e
    exact at_foldlM hg l _ (entsIn_addMul _ ha (hg x p hp)) s h

/-- The verifier's sum of forms. -/
theorem at_sumForms {n : ℕ} {g : ℕ → Option (Aff × E)}
    (hg : ∀ x, Gives (g x) fun p => InTest v T p.1) : Gives (sumForms n g) (InTest v T) :=
  at_foldlM hg _ _ (entsIn_ofConst _)

/-- A sum over limbs. -/
theorem at_limbs {t : ℕ} (hs : StartAt v T t) (nl : ℕ) (cell : ℕ → ℕ) :
    Gives (v.limbs t nl cell) (InTest v T) :=
  at_sumForms fun _ => Gives.map (inTest_U3at hs _) fun _ h => h

theorem at_shortA {t : ℕ} (hs : StartAt v T t) (X : Ten) (i j : ℕ) :
    Gives (v.shortA t X i j) (InTest v T) := at_limbs hs _ _

theorem at_longA {t : ℕ} (hs : StartAt v T t) (X : Ten) (i jh : ℕ) :
    Gives (v.longA t X i jh) (InTest v T) := at_limbs hs _ _

theorem at_xbA {t : ℕ} (hs : StartAt v T t) (kh : ℕ) : Gives (v.xbA t kh) (InTest v T) :=
  at_limbs hs _ _

/-- The name of a tensor's matrix is one of the seven prefixes. -/
theorem mname_mem (mat : ℕ) : Env.mname mat ∈ ["af", "ad", "ar", "qa", "xbI", "xbO", ""] := by
  match mat with
  | 0 => simp [Env.mname]
  | 1 => simp [Env.mname]
  | 2 => simp [Env.mname]
  | 3 => simp [Env.mname]
  | n + 4 => simp [Env.mname]

/-- A tensor with the first entry of its matrix's tables at a point. -/
theorem at_tensorAt (H : PtAt v T S) (X : String) {Z : String} (hZ : S Z) :
    Gives (v.tensorAt X Z) fun x => StartAt v T x.2 := by
  intro x h
  unfold Env.tensorAt at h
  obtain ⟨t, -, h⟩ := bind_some h
  obtain ⟨tb, htb, h⟩ := bind_some h
  obtain rfl := Option.some.inj h
  exact H _ (mname_mem _) Z tb hZ htb

theorem at_shIn {found : Option (Ten × ℕ)} (hf : Gives found fun x => StartAt v T x.2) (i j : ℕ) :
    Gives (v.shIn found i j) (InTest v T) := by
  unfold Env.shIn
  exact Gives.bind hf fun x hx => at_shortA hx _ _ _

theorem at_shA (H : PtAt v T S) (X : String) {P : String} (hP : S P) (i j : ℕ) :
    Gives (v.shA X P i j) (InTest v T) := at_shIn (at_tensorAt H X hP) i j

theorem at_shSum (H : PtAt v T S) (ew : Array E) (n : ℕ) (X : String) {P : String} (hP : S P)
    (i : ℕ) : Gives (v.shSum ew n X P i) (InTest v T) := by
  unfold Env.shSum
  exact at_sumForms fun _ => Gives.map (at_shIn (at_tensorAt H X hP) _ _) fun _ h => h

theorem at_SxsA (H : PtAt v T S) (wh : Array E) {Z : String} (hZ : S Z) (sg : ℕ) :
    Gives (v.SxsA wh Z sg) (InTest v T) := by
  intro s h
  unfold Env.SxsA at h
  dsimp only at h
  obtain ⟨tb, htb, h⟩ := bind_some h
  obtain ⟨txs, -, h⟩ := bind_some h
  have hs : StartAt v T tb := H _ (by split <;> [simp; (split <;> simp)]) Z tb hZ htb
  exact at_sumForms (fun _ => Gives.map (Gives.ite (at_xbA hs _) (at_longA hs _ _ _))
    fun _ h => h) s h

/-! ## The lists of panels -/

/-- Whatever the side returns has T at the entries that it names. -/
def SideAt (v : Env) (T : ℕ → Prop) (A : Side) : Prop :=
  ∀ f, A = some f → ∀ i y, Gives (f i y) (InTest v T)

theorem sideAt_none : SideAt v T none := fun _ e => by cases e

theorem sideAt_some {g : ℕ → ℕ → Option Aff} (h : ∀ i y, Gives (g i y) (InTest v T)) :
    SideAt v T (some g) := fun _ e => Option.some.inj e ▸ h

/-- A panel's two sides and each member of its xx. -/
def CoreTest (v : Env) (T : ℕ → Prop) (c : Side × Side × Array Aff) : Prop :=
  SideAt v T c.1 ∧ SideAt v T c.2.1 ∧ ∀ k, InTest v T (c.2.2.getD k {})

/-- So for each panel of the list. -/
def PanAt (v : Env) (T : ℕ → Prop) (bl : Array SBlk) : Prop :=
  ∀ c ∈ (bl.map core).toList, CoreTest v T c

theorem panAt_empty : PanAt v T #[] := fun c hc => by simp at hc

theorem panAt_push {bl : Array SBlk} {b : SBlk} (h : PanAt v T bl) (hb : CoreTest v T (core b)) :
    PanAt v T (bl.push b) := fun c hc => by
  simp only [Array.map_push, Array.toList_push, List.mem_append, List.mem_singleton] at hc
  rcases hc with hc | rfl
  · exact h c hc
  · exact hb

theorem inTest_getD_empty (k : ℕ) : InTest v T ((#[] : Array Aff).getD k {}) := by
  have e : (#[] : Array Aff).getD k {} = {} := by simp [Array.getD]
  rw [e]
  exact entsIn_empty

theorem plain_at (y : Lay) (ec : E) (claim : ℕ) (moeSet : Bool) (ny : ℕ) {A B : Side} (wt : ℕ → E)
    (virt : Option ℕ) {s : Panels} (hs : PanAt v T s.bl) (hA : SideAt v T A)
    (hB : SideAt v T B) : PanAt v T (plain y ec claim moeSet ny A B wt virt s).bl := by
  unfold plain
  refine panAt_push hs ⟨fun f hf i yv => ?_, fun f hf i yv => ?_, inTest_getD_empty⟩
  · obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hf
    exact hA g hg _ _
  · obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hf
    exact hB g hg _ _

theorem tri_at (y : Lay) (ec : E) (claim nk : ℕ) (sl : Array E) {xx : Array Aff}
    (virt : Option ℕ) (wt : E) {s : Panels} (hs : PanAt v T s.bl)
    (hx : ∀ k, InTest v T (xx.getD k {})) : PanAt v T (tri y ec claim nk sl xx virt wt s).bl := by
  unfold tri
  exact panAt_push hs ⟨sideAt_none, sideAt_none, hx⟩

/-- **The panels of one segment of a call of the lookup's join**: their forms read at zt. -/
theorem panelA_at (p : PanelEnv) (H : PtAt p.v T S) (hzt : S "zt") (ec : E) (el : Array E)
    (sn : String) {s : Panels} (hs : PanAt p.v T s.bl) :
    PanAt p.v T (panelA p ec el sn s).bl := by
  unfold panelA
  dsimp only
  split
  · exact plain_at _ _ _ _ _ _ _ hs
      (sideAt_some fun _ _ => at_shIn (at_tensorAt H _ hzt) _ _) sideAt_none
  split
  · exact plain_at _ _ _ _ _ _ _ hs
      (sideAt_some fun _ _ => at_shIn (at_tensorAt H _ hzt) _ _) sideAt_none
  split
  · refine plain_at _ _ _ _ _ _ _ hs (sideAt_some fun _ _ => ?_) sideAt_none
    refine Gives.ite (at_shIn (at_tensorAt H _ hzt) _ _) (Gives.some ?_)
    unfold stubAt
    exact entsIn_ofConst _
  split
  · exact plain_at _ _ _ _ _ _ _ hs sideAt_none sideAt_none
  split
  · exact plain_at _ _ _ _ _ _ _ hs
      (sideAt_some fun _ _ => at_shIn (at_tensorAt H _ hzt) _ _) sideAt_none
  · exact hs

theorem panelsA_at (p : PanelEnv) (H : PtAt p.v T S) (hzt : S "zt") {s : Panels}
    (hs : PanAt p.v T s.bl) : PanAt p.v T (panelsA p s).bl := by
  unfold panelsA
  refine OnBytes.Desc.First.K4.Slots.foldl_inv (P := fun s : Panels => PanAt p.v T s.bl)
    (fun s q hs => ?_) _ _ hs
  exact OnBytes.Desc.First.K4.Slots.foldl_inv (P := fun s : Panels => PanAt p.v T s.bl)
    (fun s g hs => panelA_at p H hzt _ _ _ hs) _ _ hs

/-- Every member of an array that a function has filled. -/
theorem mapM_getD_at {n : ℕ} {g : ℕ → Option Aff} (hg : ∀ i, Gives (g i) (InTest v T)) :
    Gives ((Array.range n).mapM g) fun xx => ∀ k, InTest v T (xx.getD k {}) := by
  intro xx h k
  rw [Array.mapM_eq_mapM_toList] at h
  obtain ⟨ys, hys, e⟩ := map_some h
  subst e
  by_cases hj : k < ys.length
  · have e : ys.toArray.getD k {} = ys[k] := by simp [Array.getD, hj]
    rw [e]
    exact all_mapM (Pr := InTest v T) (fun i a ha => hg i a ha) _ ys hys _ (List.getElem_mem hj)
  · have e : ys.toArray.getD k {} = {} := by simp [Array.getD, hj]
    rw [e]
    exact entsIn_empty

/-- **The panels of one segment of a call with terms in the second token sumcheck**: their forms
read at rt and Y. -/
theorem panelT_at (p : PanelEnv) (H : PtAt p.v T S) (hrt : S "rt") (hY : S "Y") (ec : E)
    (el : Array E) (sn : String) {s : Panels} (hs : PanAt p.v T s.bl) :
    Gives (panelT p ec el sn s) fun s' => PanAt p.v T s'.bl := by
  unfold panelT
  dsimp only
  refine Gives.ite ?_ (Gives.ite ?_ (Gives.ite ?_ (Gives.ite ?_ (Gives.ite ?_ (Gives.ite ?_ ?_)))))
  · exact Gives.skip fun wh => Gives.pure (plain_at _ _ _ _ _ _ _ hs
      (sideAt_some fun _ _ => Gives.some (entsIn_ofConst _))
      (sideAt_some fun _ _ => at_SxsA H _ hY _))
  · exact Gives.pure (plain_at _ _ _ _ _ _ _ hs
      (sideAt_some fun _ _ => at_shIn (at_tensorAt H _ hrt) _ _) sideAt_none)
  · exact Gives.pure hs
  · exact Gives.skip fun ew => Gives.pure (plain_at _ _ _ _ _ _ _ hs
      (sideAt_some fun _ _ => Gives.some (entsIn_ofConst _))
      (sideAt_some fun _ _ => at_shSum H _ _ _ hrt _))
  · exact Gives.skip fun ew => Gives.pure (plain_at _ _ _ _ _ _ _ hs
      (sideAt_some fun _ _ => Gives.some (entsIn_ofConst _))
      (sideAt_some fun _ _ => at_shA H _ hrt _ _))
  · refine gives_foldlM_inv (P := fun s : Panels => PanAt p.v T s.bl) (fun s lm hs => ?_) _ _ hs
    refine Gives.ite (Gives.pure (tri_at _ _ _ _ _ _ _ hs inTest_getD_empty)) ?_
    exact Gives.bind (mapM_getD_at fun _ => at_shIn (at_tensorAt H _ hrt) _ _) fun xx hx =>
      Gives.pure (tri_at _ _ _ _ _ _ _ hs hx)
  · exact Gives.pure hs

theorem panelsT_at (p : PanelEnv) (H : PtAt p.v T S) (hrt : S "rt") (hY : S "Y") (TS : List ℕ)
    {s : Panels} (hs : PanAt p.v T s.bl) :
    Gives (panelsT p TS s) fun s' => PanAt p.v T s'.bl := by
  unfold panelsT
  refine gives_foldlM_inv (P := fun s : Panels => PanAt p.v T s.bl) (fun s q hs => ?_) _ _ hs
  exact gives_foldlM_inv (P := fun s : Panels => PanAt p.v T s.bl)
    (fun s g hs => panelT_at p H hrt hY _ _ _ hs) _ _ hs

/-- Placing turns a panel's first place alone. -/
theorem placePanels_at {bl : Array SBlk} (h : PanAt v T bl) : PanAt v T (placePanels bl).1 := by
  unfold placePanels
  refine OnBytes.Desc.First.K4.Slots.foldl_inv (P := fun s : Array SBlk × ℕ => PanAt v T s.1)
    (fun s i hs => ?_) _ _ h
  show PanAt v T (s.1.modify i fun b => { b with off := s.2 })
  unfold PanAt
  rw [map_modify_same core (fun b : SBlk => { b with off := s.2 })
    (fun _ => rfl)]
  exact hs

/-! ## The honest side's test -/

/-- **The test answers true** where the honest reads hold the weights at each entry named. -/
theorem affFits_of_inTest {R : OnBytes.Desc.First.K4.Honest.Reads} {f : Aff}
    (I : InTest v (fun e => R.has e = true) f) :
    OnBytes.Desc.First.K4.Honest.affFits v R f = true := by
  unfold OnBytes.Desc.First.K4.Honest.affFits
  rw [Array.all_eq_true']
  intro y hy
  obtain ⟨a, b⟩ := I y (Array.mem_toList_iff.mpr hy)
  rw [Bool.and_eq_true]
  exact ⟨by rw [a]; exact beq_self_eq_true _, b⟩

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.inTest_U3at
#print axioms OnBytes.Road.K4.C.at_foldlM
#print axioms OnBytes.Road.K4.C.at_sumForms
#print axioms OnBytes.Road.K4.C.at_limbs
#print axioms OnBytes.Road.K4.C.at_shortA
#print axioms OnBytes.Road.K4.C.at_longA
#print axioms OnBytes.Road.K4.C.at_xbA
#print axioms OnBytes.Road.K4.C.mname_mem
#print axioms OnBytes.Road.K4.C.at_tensorAt
#print axioms OnBytes.Road.K4.C.at_shIn
#print axioms OnBytes.Road.K4.C.at_shA
#print axioms OnBytes.Road.K4.C.at_shSum
#print axioms OnBytes.Road.K4.C.at_SxsA
#print axioms OnBytes.Road.K4.C.sideAt_none
#print axioms OnBytes.Road.K4.C.sideAt_some
#print axioms OnBytes.Road.K4.C.panAt_empty
#print axioms OnBytes.Road.K4.C.panAt_push
#print axioms OnBytes.Road.K4.C.inTest_getD_empty
#print axioms OnBytes.Road.K4.C.plain_at
#print axioms OnBytes.Road.K4.C.tri_at
#print axioms OnBytes.Road.K4.C.panelA_at
#print axioms OnBytes.Road.K4.C.panelsA_at
#print axioms OnBytes.Road.K4.C.mapM_getD_at
#print axioms OnBytes.Road.K4.C.panelT_at
#print axioms OnBytes.Road.K4.C.panelsT_at
#print axioms OnBytes.Road.K4.C.placePanels_at
#print axioms OnBytes.Road.K4.C.affFits_of_inTest
