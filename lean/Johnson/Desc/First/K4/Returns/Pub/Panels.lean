-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/Pub/Panels.lean: CONGRUENCES: THE LIST OF PANELS OF THE SUB-PROTOCOL
K4's BATCHED SUMCHECK AT TWO ENVIRONMENTS OF ONE SKELETON (panelsA, panelsT, placePanels:
OnBytes/Model/LayerPanels.lean). Statements and proofs.

Limits. NO FUNCTION IS SHOWN TO RETURN ANYWHERE: each statement compares two calls. One premise
throughout: EnvSkel p.v p₀.v (Johnson/Road/K4/Total/Returns.lean): one layout, one list of the
tables' places, one number of columns of the array of the reads. Nothing on what a panel's forms,
weights or shown values are worth: the relation PanSkel (Skel.lean) does not hold them. Nothing on
the end of the batched sumcheck. No property is claimed.

What may differ between the two calls: the calls' points (zk), the scales (sc), the group (g), the
number of the array of the reads (iU3), the calls' weights (e), the shown values (shownT), the token
point (zt), what takes the place of the attention output (stubO).

  sideSkel_none, sideSkel_some, sideSkel_rows, sideSkel_isNone   on two sides of a panel.
  ite_rel, foldl_rel   two branchings on one test; two folds over one list.
  some_both, optRel_pure   two values that are there.
  all2_getD, all2_modify   two lists, member by member: a member by its number; one member turned.
  plain_skel, tri_skel   the two ways of appending a panel.
  panelA_skel, panelsA_skel   the panels of the lookup's join: total functions.
  panelT_rel, panelsT_rel   the panels of the second token sumcheck's terms: both calls return or
    neither does, and what they return is in PanSkel.
  **panels_rel**   the whole list, from the empty one.
  **placePanels_skel**   placing: the placed panels are in BlkSkel, member by member, with their
    first places, and the numbers of all places are equal. The sort is not opened: its comparison
    reads the panels' bits alone, which are equal (w_skel, placeOrder_skel, placeStep_skel).
  panels_at   the two together, from a return at one of the two environments.
  The examples at the end: an example of the premise; two lists that are not in PanSkel.
-/
import Johnson.Desc.First.K4.Returns.Pub.Kit
import Johnson.Road.FormsKeysPan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.RtPub
open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Flat (All2 OptRel optRel_bind)
open OnBytes.Desc.First.K4.Total (EnvSkel tensorAt_skel shIn_skel shA_skel)
open OnBytes.Road (placeOrder placeStep placePanels_eq)

/-- A side of a panel, given as forms. -/
abbrev Side : Type := Option (Nat → Nat → Option Aff)

/-! ## Two sides -/

theorem sideSkel_none : SideSkel none none := trivial

theorem sideSkel_some {f f₀ : Nat → Nat → Option Aff}
    (h : ∀ i yv, (f i yv).isSome = (f₀ i yv).isSome) : SideSkel (some f) (some f₀) := h

/-- The relation is closed under another numbering of the rows. -/
theorem sideSkel_rows {A A₀ : Side} (h : SideSkel A A₀) (row : Nat → Nat) :
    SideSkel (A.map fun f => fun i yv => f (row i) yv)
      (A₀.map fun f => fun i yv => f (row i) yv) := by
  cases A <;> cases A₀
  · trivial
  · exact False.elim h
  · exact False.elim h
  · exact fun i yv => h (row i) yv

theorem sideSkel_isNone {A A₀ : Side} (h : SideSkel A A₀) : A.isNone = A₀.isNone := by
  cases A <;> cases A₀
  · rfl
  · exact False.elim h
  · exact False.elim h
  · rfl

/-! ## Two branchings, two folds -/

theorem ite_rel {α β : Type} {R : α → β → Prop} {c : Prop} [Decidable c] {a b : α} {a' b' : β}
    (h1 : R a a') (h2 : R b b') : R (if c then a else b) (if c then a' else b') := by
  by_cases h : c
  · rw [if_pos h, if_pos h]
    exact h1
  · rw [if_neg h, if_neg h]
    exact h2

theorem foldl_rel {α σ σ' : Type} {R : σ → σ' → Prop} {f : σ → α → σ} {f' : σ' → α → σ'}
    (h : ∀ a a' x, R a a' → R (f a x) (f' a' x)) :
    ∀ (l : List α) (a : σ) (a' : σ'), R a a' → R (l.foldl f a) (l.foldl f' a')
  | [], _, _, ha => ha
  | x :: l, a, a', ha => foldl_rel h l (f a x) (f' a' x) (h a a' x ha)

/-- Two values that are there. Stated of variables, so that the two values are not compared. -/
theorem some_both {α β : Type} (a : α) (b : β) : (some a).isSome = (some b).isSome := rfl

theorem optRel_pure {α : Type} {R : α → α → Prop} {a a' : α} (h : R a a') :
    OptRel R (pure a) (pure a') := h

/-! ## Two lists, member by member -/

theorem all2_getD {α β : Type} {R : α → β → Prop} {d : α} {d' : β} (hd : R d d') {l : List α}
    {l' : List β} (h : All2 R l l') : ∀ i, R (l.getD i d) (l'.getD i d') := by
  induction h with
  | nil =>
    intro i
    rw [List.getD_nil, List.getD_nil]
    exact hd
  | cons h0 _ ih =>
    intro i
    cases i with
    | zero =>
      rw [List.getD_cons_zero, List.getD_cons_zero]
      exact h0
    | succ i =>
      rw [List.getD_cons_succ, List.getD_cons_succ]
      exact ih i

theorem all2_modify {α β : Type} {R : α → β → Prop} {f : α → α} {g : β → β}
    (hf : ∀ a b, R a b → R (f a) (g b)) {l : List α} {l' : List β} (h : All2 R l l') :
    ∀ i, All2 R (l.modify i f) (l'.modify i g) := by
  induction h with
  | nil =>
    intro i
    rw [List.modify_nil, List.modify_nil]
    exact .nil
  | cons h0 h1 ih =>
    intro i
    cases i with
    | zero =>
      rw [List.modify_zero_cons, List.modify_zero_cons]
      exact .cons (hf _ _ h0) h1
    | succ i =>
      rw [List.modify_succ_cons, List.modify_succ_cons]
      exact .cons h0 (ih i)

/-! ## Appending a panel -/

/-- plain at one layout, flag, number of columns and never-sent vector, at two sides each that are
in SideSkel. -/
theorem plain_skel (y : Lay) (ec ec₀ : E) (claim claim₀ : Nat) (moeSet : Bool) (ny : Nat)
    {A A₀ B B₀ : Side} (wt wt₀ : Nat → E) (virt : Option Nat) {s s₀ : Panels} (hs : PanSkel s s₀)
    (hA : SideSkel A A₀) (hB : SideSkel B B₀) :
    PanSkel (plain y ec claim moeSet ny A B wt virt s)
      (plain y ec₀ claim₀ moeSet ny A₀ B₀ wt₀ virt s₀) := by
  have hn := sideSkel_isNone hB
  refine ⟨?_, ?_⟩
  · refine all2_push hs.bl ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, sideSkel_rows hA _,
      sideSkel_rows hB _⟩
    show (if B.isNone then some s.nextV else none) = (if B₀.isNone then some s₀.nextV else none)
    rw [hn, hs.nextV]
  · show (if B.isNone then s.nextV + (if moeSet then y.LamM else y.Lam) else s.nextV) =
      (if B₀.isNone then s₀.nextV + (if moeSet then y.LamM else y.Lam) else s₀.nextV)
    rw [hn, hs.nextV]

/-- tri at one layout, number of columns and never-sent vector. -/
theorem tri_skel (y : Lay) (ec ec₀ : E) (claim claim₀ nk : Nat) (sl sl₀ : Array E)
    (xx xx₀ : Array Aff) (virt : Option Nat) (wt wt₀ : E) {s s₀ : Panels} (hs : PanSkel s s₀) :
    PanSkel (tri y ec claim nk sl xx virt wt s) (tri y ec₀ claim₀ nk sl₀ xx₀ virt wt₀ s₀) := by
  exact ⟨all2_push hs.bl ⟨rfl, congrArg some hs.nextV, rfl, rfl, rfl, rfl, rfl, rfl, sideSkel_none,
    sideSkel_none⟩, congrArg (· + 1) hs.nextV⟩

/-! ## The panels of the lookup's join -/

variable {p p₀ : PanelEnv}

theorem panelA_skel (S : EnvSkel p.v p₀.v) (ec ec₀ : E) (el el₀ : Array E) (sn : String)
    {s s₀ : Panels} (hs : PanSkel s s₀) :
    PanSkel (panelA p ec el sn s) (panelA p₀ ec₀ el₀ sn s₀) := by
  unfold panelA
  dsimp only
  rw [S.y, tensorAt_skel S "m" "zt", tensorAt_skel S "a" "zt", tensorAt_skel S "o" "zt"]
  refine ite_rel ?_ (ite_rel ?_ (ite_rel ?_ (ite_rel ?_ (ite_rel ?_ hs))))
  · exact plain_skel _ _ _ _ _ _ _ _ _ _ hs (sideSkel_some fun i yv => shIn_skel S _ i yv)
      sideSkel_none
  · exact plain_skel _ _ _ _ _ _ _ _ _ _ hs (sideSkel_some fun i yv => shIn_skel S _ i yv)
      sideSkel_none
  · exact plain_skel _ _ _ _ _ _ _ _ _ _ hs
      (sideSkel_some fun i yv => ite_isSome (shIn_skel S _ i yv) (some_both _ _)) sideSkel_none
  · exact plain_skel _ _ _ _ _ _ _ _ _ _ hs sideSkel_none sideSkel_none
  · exact plain_skel _ _ _ _ _ _ _ _ _ _ hs (sideSkel_some fun i yv => shIn_skel S _ i yv)
      sideSkel_none

theorem panelsA_skel (S : EnvSkel p.v p₀.v) {s s₀ : Panels} (hs : PanSkel s s₀) :
    PanSkel (panelsA p s) (panelsA p₀ s₀) := by
  unfold panelsA
  dsimp only
  rw [S.y]
  refine foldl_rel (R := PanSkel) (fun s s₀ q hs => ?_) _ _ _ hs
  exact foldl_rel (R := PanSkel) (fun s s₀ g hs => panelA_skel S _ _ _ _ g.name hs) _ _ _ hs

/-! ## The panels of the second token sumcheck's terms -/

theorem panelT_rel (S : EnvSkel p.v p₀.v) (ec ec₀ : E) (el el₀ : Array E) (sn : String)
    {s s₀ : Panels} (hs : PanSkel s s₀) :
    OptRel PanSkel (panelT p ec el sn s) (panelT p₀ ec₀ el₀ sn s₀) := by
  unfold panelT
  dsimp only
  rw [S.y, tensorAt_skel S "a" "rt", tensorAt_skel S "xr" "rt"]
  refine optRel_ite ?_ (optRel_ite ?_ (optRel_ite ?_ (optRel_ite ?_ (optRel_ite ?_
    (optRel_ite ?_ ?_)))))
  · exact optRel_bind (optRel_of_isSome (ewh_skel S.y sn)) fun wh wh₀ _ =>
      optRel_pure (plain_skel _ _ _ _ _ _ _ _ _ _ hs (sideSkel_some fun _ _ => some_both _ _)
        (sideSkel_some fun _ _ => SxsA_skel S wh wh₀ "Y" _))
  · exact optRel_pure (plain_skel _ _ _ _ _ _ _ _ _ _ hs
      (sideSkel_some fun i yv => shIn_skel S _ i yv) sideSkel_none)
  · exact optRel_pure hs
  · exact optRel_bind (optRel_of_isSome (ewOf_skel S.y "XR")) fun ew ew₀ _ =>
      optRel_pure (plain_skel _ _ _ _ _ _ _ _ _ _ hs (sideSkel_some fun _ _ => some_both _ _)
        (sideSkel_some fun _ _ => shSum_skel S ew ew₀ _ "m" "rt" _))
  · exact optRel_bind (optRel_of_isSome (ewOf_skel S.y sn)) fun _ _ _ =>
      optRel_pure (plain_skel _ _ _ _ _ _ _ _ _ _ hs (sideSkel_some fun _ _ => some_both _ _)
        (sideSkel_some fun _ _ => shA_skel S "lr" "rt" _ _))
  · refine foldlM_opt_rel (R := PanSkel) (fun s s₀ lm hs => ?_) _ _ _ hs
    refine optRel_ite (optRel_pure (tri_skel _ _ _ _ _ _ _ _ _ _ _ _ _ hs)) ?_
    exact optRel_bind (amapM_size_rel _ fun k2 _ => shIn_skel S _ lm k2) fun _ _ _ =>
      optRel_pure (tri_skel _ _ _ _ _ _ _ _ _ _ _ _ _ hs)
  · exact optRel_pure hs

theorem panelsT_rel (S : EnvSkel p.v p₀.v) (TS : List Nat) {s s₀ : Panels} (hs : PanSkel s s₀) :
    OptRel PanSkel (panelsT p TS s) (panelsT p₀ TS s₀) := by
  unfold panelsT
  dsimp only
  rw [S.y]
  refine foldlM_opt_rel (R := PanSkel) (fun s s₀ q hs => ?_) _ _ _ hs
  exact foldlM_opt_rel (R := PanSkel) (fun s s₀ g hs => panelT_rel S _ _ _ _ g.name hs) _ _ _ hs

/-- **The whole list of panels at two environments of one skeleton**: both calls return or neither
does, and the two lists are in PanSkel. -/
theorem panels_rel (S : EnvSkel p.v p₀.v) (TS : List Nat) :
    OptRel PanSkel (panelsT p TS (panelsA p {})) (panelsT p₀ TS (panelsA p₀ {})) := by
  exact panelsT_rel S TS (panelsA_skel S PanSkel.nil)

/-! ## Placing -/

/-- The bits of the panels of two lists that are in BlkSkel. -/
theorem w_skel {bl bl₀ : Array SBlk} (h : All2 BlkSkel bl.toList bl₀.toList) (i : Nat) :
    (bl.getD i {}).w = (bl₀.getD i {}).w := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, ← Array.getElem?_toList,
    ← Array.getElem?_toList, ← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]
  exact (all2_getD (BlkSkel.refl {}) h i).w

/-- The order of the placing is one: its comparison reads the bits alone. -/
theorem placeOrder_skel {bl bl₀ : Array SBlk} (h : All2 BlkSkel bl.toList bl₀.toList) :
    placeOrder bl = placeOrder bl₀ := by
  have hz : bl.size = bl₀.size := h.length
  unfold placeOrder
  simp only [w_skel h, hz]

/-- One step of the placing. -/
theorem placeStep_skel {bl bl₀ : Array SBlk} (hw : ∀ i, (bl.getD i {}).w = (bl₀.getD i {}).w)
    (s s₀ : Array SBlk × Nat) (i : Nat)
    (hs : All2 BlkSkel s.1.toList s₀.1.toList ∧ s.2 = s₀.2) :
    All2 BlkSkel (placeStep bl s i).1.toList (placeStep bl₀ s₀ i).1.toList ∧
      (placeStep bl s i).2 = (placeStep bl₀ s₀ i).2 := by
  refine ⟨?_, ?_⟩
  · show All2 BlkSkel (s.1.modify i fun b => { b with off := s.2 }).toList
      (s₀.1.modify i fun b => { b with off := s₀.2 }).toList
    rw [Array.toList_modify, Array.toList_modify]
    exact all2_modify
      (fun _ _ k => ⟨k.tri, k.v0, k.ni, k.ny, k.wy, k.w, hs.2, k.virt, k.A, k.B⟩) hs.1 i
  · show s.2 + 2 ^ (bl.getD i {}).w = s₀.2 + 2 ^ (bl₀.getD i {}).w
    rw [hs.2, hw i]

/-- **Placing two lists of panels that are in BlkSkel, member by member.** -/
theorem placePanels_skel {bl bl₀ : Array SBlk} (h : All2 BlkSkel bl.toList bl₀.toList) :
    All2 BlkSkel (placePanels bl).1.toList (placePanels bl₀).1.toList ∧
      (placePanels bl).2 = (placePanels bl₀).2 := by
  have hw := w_skel h
  rw [placePanels_eq, placePanels_eq, placeOrder_skel h]
  exact foldl_rel
    (R := fun s s₀ : Array SBlk × Nat => All2 BlkSkel s.1.toList s₀.1.toList ∧ s.2 = s₀.2)
    (fun s s₀ i hs => placeStep_skel hw s s₀ i hs) _ _ _ ⟨h, rfl⟩

/-- From a return at p₀: the list at p returns, with the same number of the next weight claim and
the same number of places, and the placed panels are in BlkSkel. -/
theorem panels_at (S : EnvSkel p.v p₀.v) (TS : List Nat) {pans₀ : Panels}
    (h : panelsT p₀ TS (panelsA p₀ {}) = some pans₀) :
    ∃ pans, panelsT p TS (panelsA p {}) = some pans ∧ pans.nextV = pans₀.nextV ∧
      (placePanels pans.bl).2 = (placePanels pans₀.bl).2 ∧
      All2 BlkSkel (placePanels pans.bl).1.toList (placePanels pans₀.bl).1.toList := by
  obtain ⟨pans, e, r⟩ := OptRel.of_right (panels_rel S TS) h
  have q := placePanels_skel r.bl
  exact ⟨pans, e, r.nextV, q.2, q.1⟩

/-! ## A member of the premise; two lists that are not in the relation -/

/-- The premise holds of an environment and the same with other points, scales, group and number
of the array of the reads. -/
example (v : Env) (zk : Array (Array E)) (sc : Scales) (g iU3 : Nat) :
    EnvSkel { v with zk := zk, sc := sc, g := g, iU3 := iU3 } v := ⟨rfl, rfl, rfl⟩

/-- Negative test: a list of one panel is not in PanSkel with the empty list. -/
example (y : Lay) (sl : Array E) (xx : Array Aff) :
    ¬ PanSkel (tri y zeroE 1 4 sl xx none zeroE {}) {} :=
  fun h => Nat.succ_ne_zero 0 h.nextV

end OnBytes.Desc.First.K4.RtPub

#print axioms OnBytes.Desc.First.K4.RtPub.sideSkel_none
#print axioms OnBytes.Desc.First.K4.RtPub.sideSkel_some
#print axioms OnBytes.Desc.First.K4.RtPub.sideSkel_rows
#print axioms OnBytes.Desc.First.K4.RtPub.sideSkel_isNone
#print axioms OnBytes.Desc.First.K4.RtPub.ite_rel
#print axioms OnBytes.Desc.First.K4.RtPub.foldl_rel
#print axioms OnBytes.Desc.First.K4.RtPub.some_both
#print axioms OnBytes.Desc.First.K4.RtPub.optRel_pure
#print axioms OnBytes.Desc.First.K4.RtPub.all2_getD
#print axioms OnBytes.Desc.First.K4.RtPub.all2_modify
#print axioms OnBytes.Desc.First.K4.RtPub.w_skel
#print axioms OnBytes.Desc.First.K4.RtPub.placeOrder_skel
#print axioms OnBytes.Desc.First.K4.RtPub.placeStep_skel
#print axioms OnBytes.Desc.First.K4.RtPub.plain_skel
#print axioms OnBytes.Desc.First.K4.RtPub.tri_skel
#print axioms OnBytes.Desc.First.K4.RtPub.panelA_skel
#print axioms OnBytes.Desc.First.K4.RtPub.panelsA_skel
#print axioms OnBytes.Desc.First.K4.RtPub.panelT_rel
#print axioms OnBytes.Desc.First.K4.RtPub.panelsT_rel
#print axioms OnBytes.Desc.First.K4.RtPub.panels_rel
#print axioms OnBytes.Desc.First.K4.RtPub.placePanels_skel
#print axioms OnBytes.Desc.First.K4.RtPub.panels_at
