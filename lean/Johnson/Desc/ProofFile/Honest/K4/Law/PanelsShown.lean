-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/PanelsShown.lean.

What is here. HOW THE VERIFIER's LIST OF PANELS OF THE BATCHED SUMCHECK (`panelsA`, `panelsT`,
`placePanels`: OnBytes/Model/LayerPanels.lean) READS THE VALUES THAT THE SECOND TOKEN SUMCHECK HAS
SHOWN. The list is made at a list of shown values. Here: there is ONE list of panels with open
places, which does not hang on the shown values, such that at every list of shown values the
verifier's list is that one with the places filled: a side A that is, at each row and column, the
constant form of ONE shown value of a fixed number; a selector whose entry number e is ONE shown
value of a fixed number. Every other field of every panel is the same at all lists of shown values.
Statements and proofs.

  `SymBlk`, `SymBlk.at`, `SymP`, `SymP.at`, `SymP.at_push`   a panel, and a list of panels, with
     open places; filled
  `IsSym`, `isSym_ite`, `isSym_bind`, `isSym_pure`, `isSym_foldlM`, `isSymT_foldl`,
     `isSym_of_total`   families of lists that are one list with open places
  `plain_form`, `plain_shown`, `tri_shown`   appending a panel
  `panelA_sym`, `panelsA_sym`, `panelT_sym`, `panelsT_sym`, `panels_sym`   **the list**
  `map_modify`, `place_fold`, `place_sym`   **placing**

Limits. On the verifier's public functions alone: equations between machine words and forms. Whether
the list is made at all does not hang on the shown values either; THAT IT IS MADE ANYWHERE IS NOT
SAID. Nothing on what a form or a value is worth. No property is claimed.
-/
import Johnson.Road.FormsKeysPan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE mulE)
open OnBytes.Model (Aff eqTab)
open OnBytes.Model.Layer (Lay SBlk Panels PanelEnv plain tri panelA panelsA panelT panelsT
  placePanels callsAC)
open OnBytes.Road (placeStep placeOrder placePanels_eq)

/-! ## 1 Panels with open places -/

/-- A panel with open places. fA: where it is there, side A at (row, column) is the constant form of
the shown value of that number. gS: where it is there: the selector's number of entries, and for
each entry the number of the shown value that it is. -/
structure SymBlk where
  b : SBlk := {}
  fA : Option (Nat → Nat → Nat) := none
  gS : Option (Nat × (Nat → Nat)) := none

/-- The panel at a list of shown values. -/
def SymBlk.at (s : SymBlk) (sh : Array E) : SBlk :=
  { s.b with
    A := match s.fA with
      | some f => some fun i yv => some (Aff.ofConst (sh.getD (f i yv) zeroE))
      | none => s.b.A
    sl := match s.gS with
      | some x => (Array.range x.1).map fun e => sh.getD (x.2 e) zeroE
      | none => s.b.sl }

/-- A list of panels with open places, and the number of the next weight claim. -/
abbrev SymP : Type := List SymBlk × Nat

/-- The list at a list of shown values. -/
def SymP.at (D : SymP) (sh : Array E) : Panels := ⟨(D.1.map (·.at sh)).toArray, D.2⟩

/-- One panel more. -/
theorem SymP.at_push (D : SymP) (s : SymBlk) (n : Nat) (sh : Array E) :
    (⟨(D.at sh).bl.push (s.at sh), n⟩ : Panels) = SymP.at (D.1 ++ [s], n) sh := by
  show (⟨(D.1.map (·.at sh)).toArray.push (s.at sh), n⟩ : Panels) =
    ⟨((D.1 ++ [s]).map (·.at sh)).toArray, n⟩
  rw [List.push_toArray, List.map_append]
  rfl

/-- A family of answers, one for each list of shown values, that is one list with open places, or
none at all lists. -/
def IsSym (g : Array E → Option Panels) : Prop :=
  ∃ r : Option SymP, ∀ sh, g sh = r.map (·.at sh)

theorem isSym_pure (D : SymP) : IsSym fun sh => pure (D.at sh) := ⟨some D, fun _ => rfl⟩

theorem isSym_ite {c : Prop} [Decidable c] {x y : Array E → Option Panels} (hx : IsSym x)
    (hy : IsSym y) : IsSym fun sh => if c then x sh else y sh := by
  by_cases h : c
  · simpa only [if_pos h] using hx
  · simpa only [if_neg h] using hy

/-- Behind a reading that does not hang on the shown values. -/
theorem isSym_bind {α : Type} (o : Option α) {x : α → Array E → Option Panels}
    (hx : ∀ a, IsSym (x a)) : IsSym fun sh => o.bind fun a => x a sh := by
  cases o with
  | none => exact ⟨none, fun _ => rfl⟩
  | some a => exact hx a

/-- A loop whose step keeps such families. -/
theorem isSym_foldlM {α : Type} {step : Array E → Panels → α → Option Panels}
    (h : ∀ (D : SymP) a, IsSym fun sh => step sh (D.at sh) a) :
    ∀ (l : List α) (D : SymP), IsSym fun sh => l.foldlM (step sh) (D.at sh)
  | [], D => ⟨some D, fun _ => rfl⟩
  | a :: l, D => by
    obtain ⟨r, hr⟩ := h D a
    cases r with
    | none =>
      refine ⟨none, fun sh => ?_⟩
      have h1 : step sh (D.at sh) a = none := hr sh
      show (a :: l).foldlM (step sh) (D.at sh) = none
      rw [List.foldlM_cons, h1]
      rfl
    | some D' =>
      obtain ⟨r', hr'⟩ := isSym_foldlM h l D'
      refine ⟨r', fun sh => ?_⟩
      have h1 : step sh (D.at sh) a = some (D'.at sh) := hr sh
      show (a :: l).foldlM (step sh) (D.at sh) = _
      rw [List.foldlM_cons, h1]
      exact hr' sh

/-- The like for a loop whose step always answers. -/
theorem isSymT_foldl {α : Type} {step : Array E → Panels → α → Panels}
    (h : ∀ (D : SymP) a, ∃ D' : SymP, ∀ sh, step sh (D.at sh) a = D'.at sh) :
    ∀ (l : List α) (D : SymP), ∃ D' : SymP, ∀ sh, l.foldl (step sh) (D.at sh) = D'.at sh
  | [], D => ⟨D, fun _ => rfl⟩
  | a :: l, D => by
    obtain ⟨D1, h1⟩ := h D a
    obtain ⟨D2, h2⟩ := isSymT_foldl h l D1
    refine ⟨D2, fun sh => ?_⟩
    rw [List.foldl_cons, h1 sh]
    exact h2 sh

/-! ## 2 Appending a panel -/

/-- A panel with two factors whose side A does not read the shown values. -/
theorem plain_form (y : Lay) (ec : E) (claim : Nat) (moeSet : Bool) (ny : Nat)
    (A B : Option (Nat → Nat → Option Aff)) (wt : Nat → E) (virt : Option Nat) (D : SymP) :
    ∃ D' : SymP, ∀ sh, plain y ec claim moeSet ny A B wt virt (D.at sh) = D'.at sh := by
  refine ⟨(D.1 ++ [⟨((plain y ec claim moeSet ny A B wt virt ⟨#[], D.2⟩).bl.getD 0 {}), none,
    none⟩], if B.isNone then D.2 + (if moeSet then y.LamM else y.Lam) else D.2), fun sh => ?_⟩
  rw [← SymP.at_push]
  rfl

/-- A panel with two factors whose side A is, at each row and column, the constant form of one shown
value. f: its number, of the layer and the column. -/
theorem plain_shown (y : Lay) (ec : E) (claim : Nat) (moeSet : Bool) (ny : Nat)
    (f : Nat → Nat → Nat) (B : Option (Nat → Nat → Option Aff)) (wt : Nat → E)
    (virt : Option Nat) (D : SymP) :
    ∃ D' : SymP, ∀ sh, plain y ec claim moeSet ny
      (some fun lam k => some (Aff.ofConst (sh.getD (f lam k) zeroE))) B wt virt (D.at sh) =
        D'.at sh := by
  refine ⟨(D.1 ++ [⟨((plain y ec claim moeSet ny none B wt virt ⟨#[], D.2⟩).bl.getD 0 {}),
    some fun i yv => f (if moeSet then 2 * i + 1 else i) yv, none⟩],
    if B.isNone then D.2 + (if moeSet then y.LamM else y.Lam) else D.2), fun sh => ?_⟩
  rw [← SymP.at_push]
  rfl

/-- A panel whose rows carry the selector. g: for each entry the number of the shown value. -/
theorem tri_shown (y : Lay) (ec : E) (claim nk n : Nat) (g : Nat → Nat) (xx : Array Aff)
    (virt : Option Nat) (wt : E) (D : SymP) :
    ∃ D' : SymP, ∀ sh, tri y ec claim nk ((Array.range n).map fun e => sh.getD (g e) zeroE) xx
      virt wt (D.at sh) = D'.at sh := by
  refine ⟨(D.1 ++ [⟨((tri y ec claim nk #[] xx virt wt ⟨#[], D.2⟩).bl.getD 0 {}), none,
    some (n, g)⟩], D.2 + 1), fun sh => ?_⟩
  rw [← SymP.at_push]
  rfl

/-- From an answer that is always there. -/
theorem isSym_of_total {x : Array E → Panels} (h : ∃ D' : SymP, ∀ sh, x sh = D'.at sh) :
    IsSym fun sh => pure (x sh) := by
  obtain ⟨D', h'⟩ := h
  exact ⟨some D', fun sh => by
    show pure (x sh) = _
    rw [h' sh]
    rfl⟩

/-! ## 3 The list -/

variable (p : PanelEnv)

/-- The panels of one segment of a call of the lookup's join do not read the shown values. -/
theorem panelA_sym (ec : E) (el : Array E) (sn : String) (D : SymP) :
    ∃ D' : SymP, ∀ sh, panelA { p with shownT := sh } ec el sn (D.at sh) = D'.at sh := by
  have hst : ∀ (sh et : Array E) (lam k2 : Nat),
      OnBytes.Model.Layer.stubAt { p with shownT := sh } et lam k2 =
        OnBytes.Model.Layer.stubAt p et lam k2 := fun _ _ _ _ => rfl
  unfold panelA
  dsimp only
  simp only [hst]
  by_cases h1 : (sn == "G" || sn == "U") = true
  · simp only [h1, if_true]
    exact plain_form _ _ _ _ _ _ _ _ _ D
  by_cases h2 : (sn == "V") = true
  · simp only [h1, h2, if_true, if_false, Bool.false_eq_true]
    exact plain_form _ _ _ _ _ _ _ _ _ D
  by_cases h3 : (sn == "O") = true
  · simp only [h1, h2, h3, if_true, if_false, Bool.false_eq_true]
    exact plain_form _ _ _ _ _ _ _ _ _ D
  by_cases h4 : (sn == "D") = true
  · simp only [h1, h2, h3, h4, if_true, if_false, Bool.false_eq_true]
    exact plain_form _ _ _ _ _ _ _ _ _ D
  by_cases h5 : (sn == "LR") = true
  · simp only [h1, h2, h3, h4, h5, if_true, if_false, Bool.false_eq_true]
    exact plain_form _ _ _ _ _ _ _ _ _ D
  · simp only [h1, h2, h3, h4, h5, if_false, Bool.false_eq_true]
    exact ⟨D, fun _ => rfl⟩

theorem panelsA_sym (D : SymP) :
    ∃ D' : SymP, ∀ sh, panelsA { p with shownT := sh } (D.at sh) = D'.at sh := by
  unfold panelsA
  dsimp only
  exact isSymT_foldl
    (step := fun sh s q => (p.v.y.calls.getD q default).segs.foldl
      (fun s g => panelA { p with shownT := sh } (p.e.getD q zeroE) (eqTab (p.v.zl q)) g.name s) s)
    (fun D q => isSymT_foldl
      (step := fun sh s (g : OnBytes.Model.Seg) =>
        panelA { p with shownT := sh } (p.e.getD q zeroE) (eqTab (p.v.zl q)) g.name s)
      (fun D g => panelA_sym p _ _ g.name D) _ D) _ D

/-- **The panels of one segment of a call that has terms in the second token sumcheck.** -/
theorem panelT_sym (ec : E) (el : Array E) (sn : String) (D : SymP) :
    IsSym fun sh => panelT { p with shownT := sh } ec el sn (D.at sh) := by
  unfold panelT
  dsimp only
  refine isSym_ite ?_ (isSym_ite ?_ (isSym_ite ?_ (isSym_ite ?_ (isSym_ite ?_
    (isSym_ite ?_ ?_)))))
  · exact isSym_bind _ fun wh => isSym_of_total (plain_shown _ _ _ _ _ _ _ _ _ D)
  · exact isSym_of_total (plain_form _ _ _ _ _ _ _ _ _ D)
  · exact isSym_pure D
  · exact isSym_bind _ fun ew => isSym_of_total (plain_shown _ _ _ _ _ _ _ _ _ D)
  · exact isSym_bind _ fun ew => isSym_of_total (plain_shown _ _ _ _ _ _ _ _ _ D)
  · refine isSym_foldlM (fun D lm => ?_) _ D
    refine isSym_ite (isSym_of_total (tri_shown _ _ _ _ _ _ _ _ _ D)) ?_
    exact isSym_bind _ fun xx => isSym_of_total (tri_shown _ _ _ _ _ _ _ _ _ D)
  · exact isSym_pure D

theorem panelsT_sym (TS : List Nat) (D : SymP) :
    IsSym fun sh => panelsT { p with shownT := sh } TS (D.at sh) := by
  unfold panelsT
  dsimp only
  exact isSym_foldlM
    (step := fun sh s q => (p.v.y.calls.getD q default).segs.foldlM
      (fun s g => panelT { p with shownT := sh } (p.e.getD q zeroE) (eqTab (p.v.zl q)) g.name s) s)
    (fun D q => isSym_foldlM
      (step := fun sh s (g : OnBytes.Model.Seg) =>
        panelT { p with shownT := sh } (p.e.getD q zeroE) (eqTab (p.v.zl q)) g.name s)
      (fun D g => panelT_sym p _ _ g.name D) _ D) _ D

/-- **The whole list, from the empty one.** -/
theorem panels_sym (TS : List Nat) :
    IsSym fun sh => panelsT { p with shownT := sh } TS (panelsA { p with shownT := sh } {}) := by
  obtain ⟨D, hD⟩ := panelsA_sym p ([], 0)
  obtain ⟨r, hr⟩ := panelsT_sym p TS D
  refine ⟨r, fun sh => ?_⟩
  have e : panelsA { p with shownT := sh } {} = D.at sh := hD sh
  show panelsT { p with shownT := sh } TS (panelsA { p with shownT := sh } {}) = _
  rw [e]
  exact hr sh

/-! ## 4 Placing -/

/-- Changing one member in front of a map, or behind it. -/
theorem map_modify {α β : Type} (f : α → β) (g : β → β) (g' : α → α)
    (h : ∀ a, g (f a) = f (g' a)) : ∀ (l : List α) (i : Nat),
    (l.map f).modify i g = (l.modify i g').map f
  | [], i => by rw [List.map_nil, List.modify_nil, List.modify_nil, List.map_nil]
  | a :: l, 0 => by
    rw [List.map_cons, List.modify_zero_cons, List.modify_zero_cons, List.map_cons, h]
  | a :: l, i + 1 => by
    rw [List.map_cons, List.modify_succ_cons, List.modify_succ_cons, List.map_cons,
      map_modify f g g' h l i]

/-- The placing's loop. wv: the panels' numbers of bits, which do not hang on the shown values. -/
theorem place_fold (bl : Array E → Array SBlk) (wv : Nat → Nat)
    (hw : ∀ sh i, ((bl sh).getD i {}).w = wv i) : ∀ (ord : List Nat) (D : List SymBlk) (n : Nat),
    ∃ (D' : List SymBlk) (n' : Nat), ∀ sh,
      ord.foldl (placeStep (bl sh)) ((D.map (·.at sh)).toArray, n) =
        ((D'.map (·.at sh)).toArray, n')
  | [], D, n => ⟨D, n, fun _ => rfl⟩
  | i :: ord, D, n => by
    obtain ⟨D', n', h⟩ := place_fold bl wv hw ord
      (D.modify i fun s => { s with b := { s.b with off := n } }) (n + 2 ^ wv i)
    refine ⟨D', n', fun sh => ?_⟩
    rw [List.foldl_cons, ← h sh]
    congr 1
    show (((D.map (·.at sh)).toArray.modify i fun b => { b with off := n }),
      n + 2 ^ ((bl sh).getD i {}).w) = _
    rw [hw sh i]
    congr 1
    apply Array.toList_inj.mp
    rw [Array.toList_modify]
    exact map_modify (fun s : SymBlk => s.at sh) _ _ (fun _ => rfl) D i

/-- **Placing.** -/
theorem place_sym (D : List SymBlk) :
    ∃ (D' : List SymBlk) (n : Nat), ∀ sh,
      placePanels (D.map (·.at sh)).toArray = ((D'.map (·.at sh)).toArray, n) := by
  have hw : ∀ (sh : Array E) (i : Nat),
      ((D.map fun s : SymBlk => s.at sh).toArray.getD i {}).w = ((D.getD i {}).b).w := by
    intro sh i
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
      List.getD_eq_getElem?_getD]
    cases D[i]? with
    | none => rfl
    | some s => rfl
  have ho : ∀ sh : Array E, placeOrder (D.map (·.at sh)).toArray =
      (List.range D.length).mergeSort fun a b =>
        decide (((D.getD b {}).b).w ≤ ((D.getD a {}).b).w) := by
    intro sh
    unfold placeOrder
    simp only [hw sh, List.size_toArray, List.length_map]
  obtain ⟨D', n, h⟩ := place_fold (fun sh => (D.map (·.at sh)).toArray) _ hw
    ((List.range D.length).mergeSort fun a b =>
      decide (((D.getD b {}).b).w ≤ ((D.getD a {}).b).w)) D 0
  exact ⟨D', n, fun sh => by rw [placePanels_eq, ho sh]; exact h sh⟩

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.SymP.at_push
#print axioms ProofFile.Honest.K4.isSym_pure
#print axioms ProofFile.Honest.K4.isSym_ite
#print axioms ProofFile.Honest.K4.isSym_bind
#print axioms ProofFile.Honest.K4.isSym_foldlM
#print axioms ProofFile.Honest.K4.isSymT_foldl
#print axioms ProofFile.Honest.K4.plain_form
#print axioms ProofFile.Honest.K4.plain_shown
#print axioms ProofFile.Honest.K4.tri_shown
#print axioms ProofFile.Honest.K4.isSym_of_total
#print axioms ProofFile.Honest.K4.panelA_sym
#print axioms ProofFile.Honest.K4.panelsA_sym
#print axioms ProofFile.Honest.K4.panelT_sym
#print axioms ProofFile.Honest.K4.panelsT_sym
#print axioms ProofFile.Honest.K4.panels_sym
#print axioms ProofFile.Honest.K4.map_modify
#print axioms ProofFile.Honest.K4.place_fold
#print axioms ProofFile.Honest.K4.place_sym
