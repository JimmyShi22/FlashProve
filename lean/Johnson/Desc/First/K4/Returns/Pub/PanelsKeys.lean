-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/Pub/PanelsKeys.lean: CONGRUENCES, FINER THAN Panels.lean's: THE LIST
OF PANELS OF THE SUB-PROTOCOL K4's BATCHED SUMCHECK AT TWO ENVIRONMENTS: the two lists' forms name
THE SAME ENTRIES OF THE READS, in the same order, whatever the coefficients (panelsA, panelsT,
placePanels: OnBytes/Model/LayerPanels.lean). Statements and proofs.

Limits. NO FUNCTION IS SHOWN TO RETURN ANYWHERE: each statement compares two calls. The premise:
EnvKeys p.v p₀.v: one layout, one list of the tables' places, one number of columns and one number
of the array of the reads. Nothing on what a form, a weight or a shown value is worth. Of a form's
slots and constant nothing is said. Nothing on the end of the batched sumcheck.
No property is claimed.

Why. A caller that values a panel's forms on given reads asks of each entry that a form names
whether it can be read. Whether a form is there (SideSkel, Skel.lean) does not answer that; which
entries it names does. A form is put together by Aff.addMul (its leaves are Aff.ent and
Aff.ofConst), which appends every entry of the form that is added, whatever the factor.

The letter W. BlkKeys and PanKeys carry a proposition W, and say of a panel's call weight and row
weights: they are equal IF W. At W := False the statements compare two environments whose points
differ. At W := True, with the premise that the environments and the calls' weights are the same,
they compare two lists of shown values, two token points and two stand-ins for the attention output.

  keysOf, FormKeys   the entries that a form names; two forms that name the same.
  keysOf_addMul, formKeys_addMul, formKeys_const, sumForms_keys   through the forms' operations.
  EnvKeys; U3at_eq, limbs_eq, shortA_eq, longA_eq, xbA_eq, shIn_eq, shA_eq   EQUATIONS: these
    readers read the four fields alone.
  SxsA_keys, shSum_keys   two readers under two lists of weights.
  SideKeys, BlkKeys, PanKeys   two sides; two panels; two lists of panels. With .skel: each gives
    the coarser relation of Skel.lean.
  plain_keys, tri_keys, panelA_keys, panelsA_keys, panelT_keys, panelsT_keys
  optRel_of_eq, map_pair_keys, ewOf_w, sideKeys_none, sideKeys_some, sideKeys_rows, all2_mono,
    PanKeys.nil, placeStep_keys   steps.
  **panels_keys**   the whole list, from the empty one.
  **placePanels_keys**   placing.
  The examples at the end: an example of the premise; two forms that are not in FormKeys.
-/
import Johnson.Desc.First.K4.Returns.Pub.Panels

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.RtPub
open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Flat (All2 OptRel optRel_bind optRel_bind_same)
open OnBytes.Desc.First.K4.Total (EnvSkel tabAt_skel tensorAt_skel)
open OnBytes.Road (placeOrder placeStep placePanels_eq)

/-! ## The entries that a form names -/

/-- The entries that a form names, in the form's order: the array, the virtual row, the index.
Without the coefficients. -/
def keysOf (a : Aff) : List (Nat × Nat × Nat) := a.ents.toList.map fun x => (x.tree, x.row, x.idx)

/-- Two forms name the same entries, in the same order. -/
def FormKeys (a a₀ : Aff) : Prop := keysOf a = keysOf a₀

theorem keysOf_addMul (a b : Aff) (k : E) : keysOf (a.addMul b k) = keysOf a ++ keysOf b := by
  have e := foldl_push_toList (fun x : Ent => ({ x with coef := mulE x.coef k } : Ent)) b.ents
    a.ents
  show ((b.ents.foldl (fun l x => l.push { x with coef := mulE x.coef k }) a.ents).toList.map
    fun x => (x.tree, x.row, x.idx)) = _
  rw [e, List.map_append, List.map_map]
  rfl

theorem formKeys_addMul {a a₀ b b₀ : Aff} (h1 : FormKeys a a₀) (h2 : FormKeys b b₀) (k k₀ : E) :
    FormKeys (a.addMul b k) (a₀.addMul b₀ k₀) := by
  unfold FormKeys at h1 h2 ⊢
  rw [keysOf_addMul, keysOf_addMul, h1, h2]

theorem formKeys_const (x x₀ : E) : FormKeys (Aff.ofConst x) (Aff.ofConst x₀) := rfl

/-- Two values that may be missing and are equal. -/
theorem optRel_of_eq {x y : Option Aff} (h : x = y) : OptRel FormKeys x y :=
  h ▸ OptRel.refl (R := FormKeys) (fun _ => rfl) x

theorem map_pair_keys (o : Option Aff) (k k₀ : E) :
    OptRel (fun t t₀ : Aff × E => FormKeys t.1 t₀.1) (o.map fun a => (a, k))
      (o.map fun a => (a, k₀)) := by
  cases o
  · trivial
  · exact rfl

theorem sumForms_keys (n : Nat) {f f₀ : Nat → Option (Aff × E)}
    (h : ∀ x, x < n → OptRel (fun t t₀ : Aff × E => FormKeys t.1 t₀.1) (f x) (f₀ x)) :
    OptRel FormKeys (sumForms n f) (sumForms n f₀) := by
  unfold sumForms
  refine foldlM_opt_rel_mem (R := FormKeys) (List.range n) (fun a a₀ x hx r => ?_) aff0 aff0 rfl
  have hx' := h x (List.mem_range.mp hx)
  revert hx'
  cases f x <;> cases f₀ x <;> intro hx'
  · trivial
  · exact False.elim hx'
  · exact False.elim hx'
  · exact formKeys_addMul r hx' _ _

/-! ## The readers -/

/-- What of an environment the entries of its forms hang on. -/
structure EnvKeys (v v₀ : Env) : Prop where
  y : v.y = v₀.y
  tab : v.tab = v₀.tab
  K3 : v.K3 = v₀.K3
  iU3 : v.iU3 = v₀.iU3

variable {v v₀ : Env}

theorem EnvKeys.skel (S : EnvKeys v v₀) : EnvSkel v v₀ := ⟨S.y, S.tab, S.K3⟩

theorem U3at_eq (S : EnvKeys v v₀) (t i : Nat) : v.U3at t i = v₀.U3at t i := by
  unfold Env.U3at
  rw [S.tab, S.K3, S.iU3]

theorem limbs_eq (S : EnvKeys v v₀) (t nl : Nat) (cell : Nat → Nat) :
    v.limbs t nl cell = v₀.limbs t nl cell := by
  unfold Env.limbs
  simp only [U3at_eq S]

theorem shortA_eq (S : EnvKeys v v₀) (t : Nat) (X : Ten) (i j : Nat) :
    v.shortA t X i j = v₀.shortA t X i j :=
  limbs_eq S t X.nl _

theorem longA_eq (S : EnvKeys v v₀) (t : Nat) (X : Ten) (i jh : Nat) :
    v.longA t X i jh = v₀.longA t X i jh := by
  unfold Env.longA
  rw [S.y]
  exact limbs_eq S t X.nl _

theorem xbA_eq (S : EnvKeys v v₀) (t kh : Nat) : v.xbA t kh = v₀.xbA t kh := by
  unfold Env.xbA
  rw [S.y]
  exact limbs_eq S t _ _

theorem shIn_eq (S : EnvKeys v v₀) (found : Option (Ten × Nat)) (i j : Nat) :
    v.shIn found i j = v₀.shIn found i j := by
  unfold Env.shIn
  simp only [shortA_eq S]

theorem shA_eq (S : EnvKeys v v₀) (X P : String) (i j : Nat) : v.shA X P i j = v₀.shA X P i j := by
  unfold Env.shA
  rw [tensorAt_skel S.skel, shIn_eq S]

/-- A residual stream's sum over blocks, under two lists of weights. -/
theorem SxsA_keys (S : EnvKeys v v₀) (wh wh₀ : Array E) (Z : String) (sg : Nat) :
    OptRel FormKeys (v.SxsA wh Z sg) (v₀.SxsA wh₀ Z sg) := by
  unfold Env.SxsA
  rw [S.y]
  simp only [tabAt_skel S.skel]
  refine optRel_bind_same fun tb => optRel_bind_same fun txs => sumForms_keys _ fun xh _ => ?_
  rw [xbA_eq S, longA_eq S]
  exact map_pair_keys _ _ _

/-- A tensor's sum over entries at a token point, under two lists of weights. -/
theorem shSum_keys (S : EnvKeys v v₀) (ew ew₀ : Array E) (n : Nat) (X P : String) (i : Nat) :
    OptRel FormKeys (v.shSum ew n X P i) (v₀.shSum ew₀ n X P i) := by
  unfold Env.shSum
  rw [tensorAt_skel S.skel]
  refine sumForms_keys n fun x _ => ?_
  rw [shIn_eq S]
  exact map_pair_keys _ _ _

/-- The weight of each entry of a segment: there at both or at neither; equal if the environments
are. -/
theorem ewOf_w {W : Prop} (S : EnvKeys v v₀) (hW : W → v = v₀) (sn : String) :
    OptRel (fun a a₀ => W → a = a₀) (v.ewOf sn) (v₀.ewOf sn) := by
  have e := ewOf_skel S.y sn
  cases h1 : v.ewOf sn <;> cases h2 : v₀.ewOf sn
  · trivial
  · rw [h1, h2] at e
    cases e
  · rw [h1, h2] at e
    cases e
  · intro w
    rw [hW w, h2] at h1
    exact (Option.some.inj h1).symm

/-! ## Two sides, two panels, two lists -/

/-- Two sides of a panel: both are absent, or both are forms that are there at the same rows and
columns and name the same entries. -/
def SideKeys (A A₀ : Side) : Prop :=
  OptRel (fun f f₀ => ∀ i yv, OptRel FormKeys (f i yv) (f₀ i yv)) A A₀

/-- Two panels: the flag, the numbers, the field claim (0 for a panel of the lookup's join, 1 for
one of the second token sumcheck's terms); the entries that the two sides and the column factor
name; and, if W, the call's weight and the rows' weights. NOT in it: sl. The column factors are
compared by getD at the empty form, as stackEndOf reads them: two factors of different lengths can
be in the relation where the surplus names no entry. -/
structure BlkKeys (W : Prop) (b b₀ : SBlk) : Prop where
  tri : b.tri = b₀.tri
  v0 : b.v0 = b₀.v0
  claim : b.claim = b₀.claim
  ni : b.ni = b₀.ni
  ny : b.ny = b₀.ny
  wy : b.wy = b₀.wy
  w : b.w = b₀.w
  off : b.off = b₀.off
  virt : b.virt = b₀.virt
  A : SideKeys b.A b₀.A
  B : SideKeys b.B b₀.B
  xx : ∀ k, FormKeys (b.xx.getD k {}) (b₀.xx.getD k {})
  ec : W → b.ec = b₀.ec
  wt : W → b.wt = b₀.wt

/-- Two lists of panels, member by member, and the number of the next weight claim. -/
structure PanKeys (W : Prop) (s s₀ : Panels) : Prop where
  bl : All2 (BlkKeys W) s.bl.toList s₀.bl.toList
  nextV : s.nextV = s₀.nextV

variable {W : Prop}

theorem sideKeys_none : SideKeys none none := trivial

theorem sideKeys_some {f f₀ : Nat → Nat → Option Aff}
    (h : ∀ i yv, OptRel FormKeys (f i yv) (f₀ i yv)) : SideKeys (some f) (some f₀) := h

theorem sideKeys_rows {A A₀ : Side} (h : SideKeys A A₀) (row : Nat → Nat) :
    SideKeys (A.map fun f => fun i yv => f (row i) yv)
      (A₀.map fun f => fun i yv => f (row i) yv) := by
  cases A <;> cases A₀
  · trivial
  · exact False.elim h
  · exact False.elim h
  · exact fun i yv => h (row i) yv

theorem SideKeys.skel {A A₀ : Side} (h : SideKeys A A₀) : SideSkel A A₀ := by
  cases A <;> cases A₀
  · trivial
  · exact False.elim h
  · exact False.elim h
  · exact fun i yv => OptRel.isSome_eq (h i yv)

theorem BlkKeys.skel {b b₀ : SBlk} (h : BlkKeys W b b₀) : BlkSkel b b₀ :=
  ⟨h.tri, h.v0, h.ni, h.ny, h.wy, h.w, h.off, h.virt, h.A.skel, h.B.skel⟩

theorem all2_mono {α β : Type} {R R' : α → β → Prop} (h : ∀ a b, R a b → R' a b) {l : List α}
    {l' : List β} (hl : All2 R l l') : All2 R' l l' := by
  induction hl with
  | nil => exact .nil
  | cons h0 _ ih => exact .cons (h _ _ h0) ih

theorem PanKeys.skel {s s₀ : Panels} (h : PanKeys W s s₀) : PanSkel s s₀ :=
  ⟨all2_mono (fun _ _ k => k.skel) h.bl, h.nextV⟩

/-- The empty list of panels. -/
theorem PanKeys.nil : PanKeys W {} {} := ⟨.nil, rfl⟩

/-! ## Appending a panel -/

theorem plain_keys (y : Lay) (ec ec₀ : E) (claim : Nat) (moeSet : Bool) (ny : Nat)
    {A A₀ B B₀ : Side} (wt wt₀ : Nat → E) (virt : Option Nat) {s s₀ : Panels}
    (hs : PanKeys W s s₀) (hA : SideKeys A A₀) (hB : SideKeys B B₀) (hec : W → ec = ec₀)
    (hwt : W → ∀ lam, wt lam = wt₀ lam) :
    PanKeys W (plain y ec claim moeSet ny A B wt virt s)
      (plain y ec₀ claim moeSet ny A₀ B₀ wt₀ virt s₀) := by
  have hn := sideSkel_isNone hB.skel
  refine ⟨?_, ?_⟩
  · refine all2_push hs.bl ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, sideKeys_rows hA _,
      sideKeys_rows hB _, fun _ => rfl, hec, fun w => ?_⟩
    · show (if B.isNone then some s.nextV else none) = (if B₀.isNone then some s₀.nextV else none)
      rw [hn, hs.nextV]
    · obtain rfl : wt = wt₀ := funext (hwt w)
      rfl
  · show (if B.isNone then s.nextV + (if moeSet then y.LamM else y.Lam) else s.nextV) =
      (if B₀.isNone then s₀.nextV + (if moeSet then y.LamM else y.Lam) else s₀.nextV)
    rw [hn, hs.nextV]

theorem tri_keys (y : Lay) (ec ec₀ : E) (claim nk : Nat) (sl sl₀ : Array E) {xx xx₀ : Array Aff}
    (virt : Option Nat) (wt wt₀ : E) {s s₀ : Panels} (hs : PanKeys W s s₀)
    (hx : ∀ k, FormKeys (xx.getD k {}) (xx₀.getD k {})) (hec : W → ec = ec₀)
    (hwt : W → wt = wt₀) :
    PanKeys W (tri y ec claim nk sl xx virt wt s) (tri y ec₀ claim nk sl₀ xx₀ virt wt₀ s₀) :=
  ⟨all2_push hs.bl ⟨rfl, congrArg some hs.nextV, rfl, rfl, rfl, rfl, rfl, rfl, rfl, sideKeys_none,
    sideKeys_none, hx, hec, fun w => congrArg (fun x => #[x]) (hwt w)⟩,
    congrArg (· + 1) hs.nextV⟩

/-! ## The panels of the lookup's join -/

variable {p p₀ : PanelEnv}

theorem panelA_keys (S : EnvKeys p.v p₀.v) (hW : W → p.v = p₀.v) (ec ec₀ : E) (el el₀ : Array E)
    (sn : String) {s s₀ : Panels} (hs : PanKeys W s s₀) (hec : W → ec = ec₀)
    (hel : W → el = el₀) : PanKeys W (panelA p ec el sn s) (panelA p₀ ec₀ el₀ sn s₀) := by
  unfold panelA
  dsimp only
  rw [S.y, tensorAt_skel S.skel "m" "zt", tensorAt_skel S.skel "a" "zt",
    tensorAt_skel S.skel "o" "zt"]
  refine ite_rel ?_ (ite_rel ?_ (ite_rel ?_ (ite_rel ?_ (ite_rel ?_ hs))))
  · exact plain_keys _ _ _ _ _ _ _ _ _ hs
      (sideKeys_some fun i yv => optRel_of_eq (shIn_eq S _ i yv)) sideKeys_none hec
      fun w lam => by rw [hel w, hW w]
  · exact plain_keys _ _ _ _ _ _ _ _ _ hs
      (sideKeys_some fun i yv => optRel_of_eq (shIn_eq S _ i yv)) sideKeys_none hec
      fun w lam => by rw [hel w, hW w]
  · exact plain_keys _ _ _ _ _ _ _ _ _ hs
      (sideKeys_some fun i yv =>
        optRel_ite (optRel_of_eq (shIn_eq S _ i yv)) (OptRel.some (formKeys_const _ _)))
      sideKeys_none hec fun w lam => by rw [hel w, hW w]
  · exact plain_keys _ _ _ _ _ _ _ _ _ hs sideKeys_none sideKeys_none hec
      fun w lam => by rw [hel w, hW w]
  · exact plain_keys _ _ _ _ _ _ _ _ _ hs
      (sideKeys_some fun i yv => optRel_of_eq (shIn_eq S _ i yv)) sideKeys_none hec
      fun w lam => by rw [hel w, hW w]

theorem panelsA_keys (S : EnvKeys p.v p₀.v) (hW : W → p.v = p₀.v ∧ p.e = p₀.e) {s s₀ : Panels}
    (hs : PanKeys W s s₀) : PanKeys W (panelsA p s) (panelsA p₀ s₀) := by
  unfold panelsA
  dsimp only
  rw [S.y]
  refine foldl_rel (R := PanKeys W) (fun s s₀ q hs => ?_) _ _ _ hs
  exact foldl_rel (R := PanKeys W)
    (fun s s₀ g hs => panelA_keys S (fun w => (hW w).1) _ _ _ _ g.name hs
      (fun w => by rw [(hW w).2]) fun w => by rw [(hW w).1]) _ _ _ hs

/-! ## The panels of the second token sumcheck's terms -/

theorem panelT_keys (S : EnvKeys p.v p₀.v) (hW : W → p.v = p₀.v) (ec ec₀ : E) (el el₀ : Array E)
    (sn : String) {s s₀ : Panels} (hs : PanKeys W s s₀) (hec : W → ec = ec₀)
    (hel : W → el = el₀) :
    OptRel (PanKeys W) (panelT p ec el sn s) (panelT p₀ ec₀ el₀ sn s₀) := by
  unfold panelT
  dsimp only
  rw [S.y, tensorAt_skel S.skel "a" "rt", tensorAt_skel S.skel "xr" "rt"]
  refine optRel_ite ?_ (optRel_ite ?_ (optRel_ite ?_ (optRel_ite ?_ (optRel_ite ?_
    (optRel_ite ?_ ?_)))))
  · exact optRel_bind (optRel_of_isSome (ewh_skel S.y sn)) fun wh wh₀ _ =>
      optRel_pure (plain_keys _ _ _ _ _ _ _ _ _ hs
        (sideKeys_some fun _ _ => OptRel.some (formKeys_const _ _))
        (sideKeys_some fun _ _ => SxsA_keys S wh wh₀ "Y" _) hec fun w lam => by rw [hel w])
  · exact optRel_pure (plain_keys _ _ _ _ _ _ _ _ _ hs
      (sideKeys_some fun i yv => optRel_of_eq (shIn_eq S _ i yv)) sideKeys_none hec
      fun w lam => by rw [hel w, hW w])
  · exact optRel_pure hs
  · exact optRel_bind (optRel_of_isSome (ewOf_skel S.y "XR")) fun ew ew₀ _ =>
      optRel_pure (plain_keys _ _ _ _ _ _ _ _ _ hs
        (sideKeys_some fun _ _ => OptRel.some (formKeys_const _ _))
        (sideKeys_some fun _ _ => shSum_keys S ew ew₀ _ "m" "rt" _) hec
        fun w lam => by rw [hel w])
  · exact optRel_bind (ewOf_w S hW sn) fun ew ew₀ he =>
      optRel_pure (plain_keys _ _ _ _ _ _ _ _ _ hs
        (sideKeys_some fun _ _ => OptRel.some (formKeys_const _ _))
        (sideKeys_some fun _ _ => optRel_of_eq (shA_eq S "lr" "rt" _ _)) hec
        fun w lam => by rw [hel w, he w])
  · refine foldlM_opt_rel (R := PanKeys W) (fun s s₀ lm hs => ?_) _ _ _ hs
    refine optRel_ite (optRel_pure (tri_keys _ _ _ _ _ _ _ _ _ _ hs (fun _ => rfl) hec
      fun w => by rw [hel w, hW w])) ?_
    simp only [shIn_eq S]
    exact optRel_bind_same fun xx => optRel_pure (tri_keys _ _ _ _ _ _ _ _ _ _ hs (fun _ => rfl) hec
      fun w => by rw [hel w, hW w])
  · exact optRel_pure hs

theorem panelsT_keys (S : EnvKeys p.v p₀.v) (hW : W → p.v = p₀.v ∧ p.e = p₀.e) (TS : List Nat)
    {s s₀ : Panels} (hs : PanKeys W s s₀) :
    OptRel (PanKeys W) (panelsT p TS s) (panelsT p₀ TS s₀) := by
  unfold panelsT
  dsimp only
  rw [S.y]
  refine foldlM_opt_rel (R := PanKeys W) (fun s s₀ q hs => ?_) _ _ _ hs
  exact foldlM_opt_rel (R := PanKeys W)
    (fun s s₀ g hs => panelT_keys S (fun w => (hW w).1) _ _ _ _ g.name hs
      (fun w => by rw [(hW w).2]) fun w => by rw [(hW w).1]) _ _ _ hs

/-- **The whole list of panels**: both calls return or neither does, and the two lists are in
PanKeys. -/
theorem panels_keys (S : EnvKeys p.v p₀.v) (hW : W → p.v = p₀.v ∧ p.e = p₀.e) (TS : List Nat) :
    OptRel (PanKeys W) (panelsT p TS (panelsA p {})) (panelsT p₀ TS (panelsA p₀ {})) :=
  panelsT_keys S hW TS (panelsA_keys S hW PanKeys.nil)

/-! ## Placing -/

theorem placeStep_keys {bl bl₀ : Array SBlk} (hw : ∀ i, (bl.getD i {}).w = (bl₀.getD i {}).w)
    (s s₀ : Array SBlk × Nat) (i : Nat)
    (hs : All2 (BlkKeys W) s.1.toList s₀.1.toList ∧ s.2 = s₀.2) :
    All2 (BlkKeys W) (placeStep bl s i).1.toList (placeStep bl₀ s₀ i).1.toList ∧
      (placeStep bl s i).2 = (placeStep bl₀ s₀ i).2 := by
  refine ⟨?_, ?_⟩
  · show All2 (BlkKeys W) (s.1.modify i fun b => { b with off := s.2 }).toList
      (s₀.1.modify i fun b => { b with off := s₀.2 }).toList
    rw [Array.toList_modify, Array.toList_modify]
    exact all2_modify
      (fun _ _ k => ⟨k.tri, k.v0, k.claim, k.ni, k.ny, k.wy, k.w, hs.2, k.virt, k.A, k.B, k.xx,
        k.ec, k.wt⟩) hs.1 i
  · show s.2 + 2 ^ (bl.getD i {}).w = s₀.2 + 2 ^ (bl₀.getD i {}).w
    rw [hs.2, hw i]

/-- **Placing two lists of panels that are in BlkKeys, member by member.** -/
theorem placePanels_keys {bl bl₀ : Array SBlk} (h : All2 (BlkKeys W) bl.toList bl₀.toList) :
    All2 (BlkKeys W) (placePanels bl).1.toList (placePanels bl₀).1.toList ∧
      (placePanels bl).2 = (placePanels bl₀).2 := by
  have hk : All2 BlkSkel bl.toList bl₀.toList := all2_mono (fun _ _ k => k.skel) h
  have hw := w_skel hk
  rw [placePanels_eq, placePanels_eq, placeOrder_skel hk]
  exact foldl_rel
    (R := fun s s₀ : Array SBlk × Nat => All2 (BlkKeys W) s.1.toList s₀.1.toList ∧ s.2 = s₀.2)
    (fun s s₀ i hs => placeStep_keys hw s s₀ i hs) _ _ _ ⟨h, rfl⟩

/-! ## A member of the premise; two forms that are not in the relation -/

/-- The premise holds of an environment and the same with other points, scales and group. -/
example (v : Env) (zk : Array (Array E)) (sc : Scales) (g : Nat) :
    EnvKeys { v with zk := zk, sc := sc, g := g } v := ⟨rfl, rfl, rfl, rfl⟩

/-- Negative test: two forms that name two entries of one row are not in FormKeys. -/
example : ¬ FormKeys (Aff.ent 2 0 0) (Aff.ent 2 0 1) := fun h =>
  absurd (show keysOf (Aff.ent 2 0 0) = keysOf (Aff.ent 2 0 1) from h) (by decide)

end OnBytes.Desc.First.K4.RtPub

#print axioms OnBytes.Desc.First.K4.RtPub.keysOf_addMul
#print axioms OnBytes.Desc.First.K4.RtPub.formKeys_addMul
#print axioms OnBytes.Desc.First.K4.RtPub.formKeys_const
#print axioms OnBytes.Desc.First.K4.RtPub.optRel_of_eq
#print axioms OnBytes.Desc.First.K4.RtPub.map_pair_keys
#print axioms OnBytes.Desc.First.K4.RtPub.sumForms_keys
#print axioms OnBytes.Desc.First.K4.RtPub.EnvKeys.skel
#print axioms OnBytes.Desc.First.K4.RtPub.U3at_eq
#print axioms OnBytes.Desc.First.K4.RtPub.limbs_eq
#print axioms OnBytes.Desc.First.K4.RtPub.shortA_eq
#print axioms OnBytes.Desc.First.K4.RtPub.longA_eq
#print axioms OnBytes.Desc.First.K4.RtPub.xbA_eq
#print axioms OnBytes.Desc.First.K4.RtPub.shIn_eq
#print axioms OnBytes.Desc.First.K4.RtPub.shA_eq
#print axioms OnBytes.Desc.First.K4.RtPub.SxsA_keys
#print axioms OnBytes.Desc.First.K4.RtPub.shSum_keys
#print axioms OnBytes.Desc.First.K4.RtPub.ewOf_w
#print axioms OnBytes.Desc.First.K4.RtPub.sideKeys_none
#print axioms OnBytes.Desc.First.K4.RtPub.sideKeys_some
#print axioms OnBytes.Desc.First.K4.RtPub.sideKeys_rows
#print axioms OnBytes.Desc.First.K4.RtPub.SideKeys.skel
#print axioms OnBytes.Desc.First.K4.RtPub.BlkKeys.skel
#print axioms OnBytes.Desc.First.K4.RtPub.all2_mono
#print axioms OnBytes.Desc.First.K4.RtPub.PanKeys.skel
#print axioms OnBytes.Desc.First.K4.RtPub.PanKeys.nil
#print axioms OnBytes.Desc.First.K4.RtPub.plain_keys
#print axioms OnBytes.Desc.First.K4.RtPub.tri_keys
#print axioms OnBytes.Desc.First.K4.RtPub.panelA_keys
#print axioms OnBytes.Desc.First.K4.RtPub.panelsA_keys
#print axioms OnBytes.Desc.First.K4.RtPub.panelT_keys
#print axioms OnBytes.Desc.First.K4.RtPub.panelsT_keys
#print axioms OnBytes.Desc.First.K4.RtPub.panels_keys
#print axioms OnBytes.Desc.First.K4.RtPub.placeStep_keys
#print axioms OnBytes.Desc.First.K4.RtPub.placePanels_keys
