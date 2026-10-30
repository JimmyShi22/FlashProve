-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/PanelsShape.lean: THE LAYERS' OWN ROUNDS (K4): THE PANELS OF THE
BATCHED SUMCHECK AND ITS END, AT TWO ENVIRONMENTS: THE FORMS HAVE ONE SHAPE: ENTRIES AND SLOTS.
Congruences: each statement compares two calls. Nothing is evaluated.

AFTER Johnson/Desc/First/K4/Returns/Pub/PanelsKeys.lean AND EndKeys.lean, STATEMENT BY STATEMENT AND
PROOF BY PROOF: these say "the same entries"; here the relation on two forms is SameSh
(Johnson/Desc/First/K4/Returns/FormsShape.lean): the same entries AND the same slots. The texts were
carried over by program: the relation's name and the names of its five small laws are exchanged;
besides, foldl_rel is written RtPub.foldl_rel (four places), the small laws map_pair_sh and
sumForms_lt are proved anew, and PanelsKeys.lean's two examples are not carried over: THIS FILE HAS
NO EXAMPLE. The letter W is theirs (PanelsKeys.lean's head): a proposition under which two panels'
fields ec and wt are equal (BlkShp's last two fields). Comments were turned by hand since, where
they no longer fitted; they were not all held one by one.

  optRel_of_eqS, map_pair_sh, sumForms_lt   the small laws, at SameSh.
  SxsA_shp, shSum_shp; SideShp, BlkShp, PanShp with their .skel; plain_shp, tri_shp, panelA_shp,
  panelsA_shp, panelT_shp, panelsT_shp, **panels_shp**, placeStep_shp, **placePanels_shp**; EndShp,
  stackEndOf_shp, **stackEnd_shp**.

Limits. NO FUNCTION IS SHOWN TO RETURN ANYWHERE. Nothing on what a form, a weight or a shown value
is worth, nor on a form's constant. "Side" here is RtPub.Side (a panel's side), seen through the
open line; Ledger.lean declares another Side (on two ledgers) in this very namespace, and is not
imported here. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.K4.Returns.Pub.EndKeys
import Johnson.Desc.First.K4.Returns.FormsShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt
open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Flat (All2 OptRel optRel_bind optRel_bind_same)
open OnBytes.Desc.First.K4.Total (EnvSkel tabAt_skel tensorAt_skel)
open OnBytes.Road (placeOrder placeStep placePanels_eq)
open OnBytes.Desc.First.K4.RtPub
open VerifiableInference.Desc.First.Shape

theorem optRel_of_eqS {x y : Option Aff} (h : x = y) : OptRel SameSh x y :=
  h ▸ OptRel.refl (R := SameSh) (fun _ => rfl) x

theorem map_pair_sh (o : Option Aff) (k k₀ : E) :
    OptRel (fun t t₀ : Aff × E => SameSh t.1 t₀.1) (o.map fun a => (a, k))
      (o.map fun a => (a, k₀)) := pair_rel o _ _

theorem sumForms_lt (n : Nat) {f f₀ : Nat → Option (Aff × E)}
    (h : ∀ x, x < n → OptRel (fun t t₀ : Aff × E => SameSh t.1 t₀.1) (f x) (f₀ x)) :
    OptRel SameSh (sumForms n f) (sumForms n f₀) := by
  unfold sumForms
  have key : ∀ (l : List Nat) (a b : Aff), SameSh a b → (∀ x ∈ l, x < n) →
      OptRel SameSh (l.foldlM (fun a x => (f x).map fun t => a.addMul t.1 t.2) a)
        (l.foldlM (fun a x => (f₀ x).map fun t => a.addMul t.1 t.2) b) := by
    intro l
    induction l with
    | nil => exact fun _ _ h _ => h
    | cons x l ih =>
      intro a b hab hl
      rw [List.foldlM_cons, List.foldlM_cons]
      refine optRel_bind (S := SameSh) ?_ fun c d hcd =>
        ih c d hcd fun y hy => hl y (List.mem_cons_of_mem _ hy)
      have h1 := h x (hl x (List.mem_cons_self ..))
      cases hf : f x <;> cases hg : f₀ x <;> rw [hf, hg] at h1
      · trivial
      · exact h1.elim
      · exact h1.elim
      · exact SameSh.addMul hab h1 _ _
  exact key _ _ _ (SameSh.refl _) fun x hx => List.mem_range.1 hx

variable {v v₀ : Env}

/-- A residual stream's sum over blocks, under two lists of weights. -/
theorem SxsA_shp (S : EnvKeys v v₀) (wh wh₀ : Array E) (Z : String) (sg : Nat) :
    OptRel SameSh (v.SxsA wh Z sg) (v₀.SxsA wh₀ Z sg) := by
  unfold Env.SxsA
  rw [S.y]
  simp only [tabAt_skel S.skel]
  refine optRel_bind_same fun tb => optRel_bind_same fun txs => sumForms_lt _ fun xh _ => ?_
  rw [xbA_eq S, longA_eq S]
  exact map_pair_sh _ _ _

/-- A tensor's sum over entries at a token point, under two lists of weights. -/
theorem shSum_shp (S : EnvKeys v v₀) (ew ew₀ : Array E) (n : Nat) (X P : String) (i : Nat) :
    OptRel SameSh (v.shSum ew n X P i) (v₀.shSum ew₀ n X P i) := by
  unfold Env.shSum
  rw [tensorAt_skel S.skel]
  refine sumForms_lt n fun x _ => ?_
  rw [shIn_eq S]
  exact map_pair_sh _ _ _

/-! ## Two sides, two panels, two lists -/

/-- Two sides of a panel: both are absent, or both are forms that are there at the same rows and
columns and have one shape. -/
def SideShp (A A₀ : Side) : Prop :=
  OptRel (fun f f₀ => ∀ i yv, OptRel SameSh (f i yv) (f₀ i yv)) A A₀

/-- Two panels: the flag, the numbers, the pass; the shapes of the two sides' and the column
factor's forms; and, if W, the call's weight and the rows' weights. NOT in it: sl. The column
factors are compared by getD at the empty form, as stackEndOf reads them: two factors of different
lengths can be in the relation where the surplus names no entry and no slot. -/
structure BlkShp (W : Prop) (b b₀ : SBlk) : Prop where
  tri : b.tri = b₀.tri
  v0 : b.v0 = b₀.v0
  claim : b.claim = b₀.claim
  ni : b.ni = b₀.ni
  ny : b.ny = b₀.ny
  wy : b.wy = b₀.wy
  w : b.w = b₀.w
  off : b.off = b₀.off
  virt : b.virt = b₀.virt
  A : SideShp b.A b₀.A
  B : SideShp b.B b₀.B
  xx : ∀ k, SameSh (b.xx.getD k {}) (b₀.xx.getD k {})
  ec : W → b.ec = b₀.ec
  wt : W → b.wt = b₀.wt

/-- Two lists of panels, member by member, and the number of the next weight claim. -/
structure PanShp (W : Prop) (s s₀ : Panels) : Prop where
  bl : All2 (BlkShp W) s.bl.toList s₀.bl.toList
  nextV : s.nextV = s₀.nextV

variable {W : Prop}

theorem sideShp_none : SideShp none none := trivial

theorem sideShp_some {f f₀ : Nat → Nat → Option Aff}
    (h : ∀ i yv, OptRel SameSh (f i yv) (f₀ i yv)) : SideShp (some f) (some f₀) := h

theorem sideShp_rows {A A₀ : Side} (h : SideShp A A₀) (row : Nat → Nat) :
    SideShp (A.map fun f => fun i yv => f (row i) yv)
      (A₀.map fun f => fun i yv => f (row i) yv) := by
  cases A <;> cases A₀
  · trivial
  · exact False.elim h
  · exact False.elim h
  · exact fun i yv => h (row i) yv

theorem SideShp.skel {A A₀ : Side} (h : SideShp A A₀) : SideSkel A A₀ := by
  cases A <;> cases A₀
  · trivial
  · exact False.elim h
  · exact False.elim h
  · exact fun i yv => OptRel.isSome_eq (h i yv)

theorem BlkShp.skel {b b₀ : SBlk} (h : BlkShp W b b₀) : BlkSkel b b₀ :=
  ⟨h.tri, h.v0, h.ni, h.ny, h.wy, h.w, h.off, h.virt, h.A.skel, h.B.skel⟩

theorem PanShp.skel {s s₀ : Panels} (h : PanShp W s s₀) : PanSkel s s₀ :=
  ⟨all2_mono (fun _ _ k => k.skel) h.bl, h.nextV⟩

/-- The empty list of panels. -/
theorem PanShp.nil : PanShp W {} {} := ⟨.nil, rfl⟩

/-! ## Appending a panel -/

theorem plain_shp (y : Lay) (ec ec₀ : E) (claim : Nat) (moeSet : Bool) (ny : Nat)
    {A A₀ B B₀ : Side} (wt wt₀ : Nat → E) (virt : Option Nat) {s s₀ : Panels}
    (hs : PanShp W s s₀) (hA : SideShp A A₀) (hB : SideShp B B₀) (hec : W → ec = ec₀)
    (hwt : W → ∀ lam, wt lam = wt₀ lam) :
    PanShp W (plain y ec claim moeSet ny A B wt virt s)
      (plain y ec₀ claim moeSet ny A₀ B₀ wt₀ virt s₀) := by
  have hn := sideSkel_isNone hB.skel
  refine ⟨?_, ?_⟩
  · refine all2_push hs.bl ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, sideShp_rows hA _,
      sideShp_rows hB _, fun _ => rfl, hec, fun w => ?_⟩
    · show (if B.isNone then some s.nextV else none) = (if B₀.isNone then some s₀.nextV else none)
      rw [hn, hs.nextV]
    · obtain rfl : wt = wt₀ := funext (hwt w)
      rfl
  · show (if B.isNone then s.nextV + (if moeSet then y.LamM else y.Lam) else s.nextV) =
      (if B₀.isNone then s₀.nextV + (if moeSet then y.LamM else y.Lam) else s₀.nextV)
    rw [hn, hs.nextV]

theorem tri_shp (y : Lay) (ec ec₀ : E) (claim nk : Nat) (sl sl₀ : Array E) {xx xx₀ : Array Aff}
    (virt : Option Nat) (wt wt₀ : E) {s s₀ : Panels} (hs : PanShp W s s₀)
    (hx : ∀ k, SameSh (xx.getD k {}) (xx₀.getD k {})) (hec : W → ec = ec₀)
    (hwt : W → wt = wt₀) :
    PanShp W (tri y ec claim nk sl xx virt wt s) (tri y ec₀ claim nk sl₀ xx₀ virt wt₀ s₀) :=
  ⟨all2_push hs.bl ⟨rfl, congrArg some hs.nextV, rfl, rfl, rfl, rfl, rfl, rfl, rfl, sideShp_none,
    sideShp_none, hx, hec, fun w => congrArg (fun x => #[x]) (hwt w)⟩,
    congrArg (· + 1) hs.nextV⟩

/-! ## The panels of the lookup's join -/

variable {p p₀ : PanelEnv}

theorem panelA_shp (S : EnvKeys p.v p₀.v) (hW : W → p.v = p₀.v) (ec ec₀ : E) (el el₀ : Array E)
    (sn : String) {s s₀ : Panels} (hs : PanShp W s s₀) (hec : W → ec = ec₀)
    (hel : W → el = el₀) : PanShp W (panelA p ec el sn s) (panelA p₀ ec₀ el₀ sn s₀) := by
  unfold panelA
  dsimp only
  rw [S.y, tensorAt_skel S.skel "m" "zt", tensorAt_skel S.skel "a" "zt",
    tensorAt_skel S.skel "o" "zt"]
  refine ite_rel ?_ (ite_rel ?_ (ite_rel ?_ (ite_rel ?_ (ite_rel ?_ hs))))
  · exact plain_shp _ _ _ _ _ _ _ _ _ hs
      (sideShp_some fun i yv => optRel_of_eqS (shIn_eq S _ i yv)) sideShp_none hec
      fun w lam => by rw [hel w, hW w]
  · exact plain_shp _ _ _ _ _ _ _ _ _ hs
      (sideShp_some fun i yv => optRel_of_eqS (shIn_eq S _ i yv)) sideShp_none hec
      fun w lam => by rw [hel w, hW w]
  · exact plain_shp _ _ _ _ _ _ _ _ _ hs
      (sideShp_some fun i yv =>
        optRel_ite (optRel_of_eqS (shIn_eq S _ i yv)) (OptRel.some (SameSh.const _ _)))
      sideShp_none hec fun w lam => by rw [hel w, hW w]
  · exact plain_shp _ _ _ _ _ _ _ _ _ hs sideShp_none sideShp_none hec
      fun w lam => by rw [hel w, hW w]
  · exact plain_shp _ _ _ _ _ _ _ _ _ hs
      (sideShp_some fun i yv => optRel_of_eqS (shIn_eq S _ i yv)) sideShp_none hec
      fun w lam => by rw [hel w, hW w]

theorem panelsA_shp (S : EnvKeys p.v p₀.v) (hW : W → p.v = p₀.v ∧ p.e = p₀.e) {s s₀ : Panels}
    (hs : PanShp W s s₀) : PanShp W (panelsA p s) (panelsA p₀ s₀) := by
  unfold panelsA
  dsimp only
  rw [S.y]
  refine RtPub.foldl_rel (R := PanShp W) (fun s s₀ q hs => ?_) _ _ _ hs
  exact RtPub.foldl_rel (R := PanShp W)
    (fun s s₀ g hs => panelA_shp S (fun w => (hW w).1) _ _ _ _ g.name hs
      (fun w => by rw [(hW w).2]) fun w => by rw [(hW w).1]) _ _ _ hs

/-! ## The panels of the second token sumcheck's terms -/

theorem panelT_shp (S : EnvKeys p.v p₀.v) (hW : W → p.v = p₀.v) (ec ec₀ : E) (el el₀ : Array E)
    (sn : String) {s s₀ : Panels} (hs : PanShp W s s₀) (hec : W → ec = ec₀)
    (hel : W → el = el₀) :
    OptRel (PanShp W) (panelT p ec el sn s) (panelT p₀ ec₀ el₀ sn s₀) := by
  unfold panelT
  dsimp only
  rw [S.y, tensorAt_skel S.skel "a" "rt", tensorAt_skel S.skel "xr" "rt"]
  refine optRel_ite ?_ (optRel_ite ?_ (optRel_ite ?_ (optRel_ite ?_ (optRel_ite ?_
    (optRel_ite ?_ ?_)))))
  · exact optRel_bind (optRel_of_isSome (ewh_skel S.y sn)) fun wh wh₀ _ =>
      optRel_pure (plain_shp _ _ _ _ _ _ _ _ _ hs
        (sideShp_some fun _ _ => OptRel.some (SameSh.const _ _))
        (sideShp_some fun _ _ => SxsA_shp S wh wh₀ "Y" _) hec fun w lam => by rw [hel w])
  · exact optRel_pure (plain_shp _ _ _ _ _ _ _ _ _ hs
      (sideShp_some fun i yv => optRel_of_eqS (shIn_eq S _ i yv)) sideShp_none hec
      fun w lam => by rw [hel w, hW w])
  · exact optRel_pure hs
  · exact optRel_bind (optRel_of_isSome (ewOf_skel S.y "XR")) fun ew ew₀ _ =>
      optRel_pure (plain_shp _ _ _ _ _ _ _ _ _ hs
        (sideShp_some fun _ _ => OptRel.some (SameSh.const _ _))
        (sideShp_some fun _ _ => shSum_shp S ew ew₀ _ "m" "rt" _) hec
        fun w lam => by rw [hel w])
  · exact optRel_bind (ewOf_w S hW sn) fun ew ew₀ he =>
      optRel_pure (plain_shp _ _ _ _ _ _ _ _ _ hs
        (sideShp_some fun _ _ => OptRel.some (SameSh.const _ _))
        (sideShp_some fun _ _ => optRel_of_eqS (shA_eq S "lr" "rt" _ _)) hec
        fun w lam => by rw [hel w, he w])
  · refine foldlM_opt_rel (R := PanShp W) (fun s s₀ lm hs => ?_) _ _ _ hs
    refine optRel_ite (optRel_pure (tri_shp _ _ _ _ _ _ _ _ _ _ hs (fun _ => rfl) hec
      fun w => by rw [hel w, hW w])) ?_
    simp only [shIn_eq S]
    exact optRel_bind_same fun xx => optRel_pure (tri_shp _ _ _ _ _ _ _ _ _ _ hs (fun _ => rfl) hec
      fun w => by rw [hel w, hW w])
  · exact optRel_pure hs

theorem panelsT_shp (S : EnvKeys p.v p₀.v) (hW : W → p.v = p₀.v ∧ p.e = p₀.e) (TS : List Nat)
    {s s₀ : Panels} (hs : PanShp W s s₀) :
    OptRel (PanShp W) (panelsT p TS s) (panelsT p₀ TS s₀) := by
  unfold panelsT
  dsimp only
  rw [S.y]
  refine foldlM_opt_rel (R := PanShp W) (fun s s₀ q hs => ?_) _ _ _ hs
  exact foldlM_opt_rel (R := PanShp W)
    (fun s s₀ g hs => panelT_shp S (fun w => (hW w).1) _ _ _ _ g.name hs
      (fun w => by rw [(hW w).2]) fun w => by rw [(hW w).1]) _ _ _ hs

/-- **The whole list of panels**: both calls return or neither does, and the two lists are in
PanShp. -/
theorem panels_shp (S : EnvKeys p.v p₀.v) (hW : W → p.v = p₀.v ∧ p.e = p₀.e) (TS : List Nat) :
    OptRel (PanShp W) (panelsT p TS (panelsA p {})) (panelsT p₀ TS (panelsA p₀ {})) :=
  panelsT_shp S hW TS (panelsA_shp S hW PanShp.nil)

/-! ## Placing -/

theorem placeStep_shp {bl bl₀ : Array SBlk} (hw : ∀ i, (bl.getD i {}).w = (bl₀.getD i {}).w)
    (s s₀ : Array SBlk × Nat) (i : Nat)
    (hs : All2 (BlkShp W) s.1.toList s₀.1.toList ∧ s.2 = s₀.2) :
    All2 (BlkShp W) (placeStep bl s i).1.toList (placeStep bl₀ s₀ i).1.toList ∧
      (placeStep bl s i).2 = (placeStep bl₀ s₀ i).2 := by
  refine ⟨?_, ?_⟩
  · show All2 (BlkShp W) (s.1.modify i fun b => { b with off := s.2 }).toList
      (s₀.1.modify i fun b => { b with off := s₀.2 }).toList
    rw [Array.toList_modify, Array.toList_modify]
    exact all2_modify
      (fun _ _ k => ⟨k.tri, k.v0, k.claim, k.ni, k.ny, k.wy, k.w, hs.2, k.virt, k.A, k.B, k.xx,
        k.ec, k.wt⟩) hs.1 i
  · show s.2 + 2 ^ (bl.getD i {}).w = s₀.2 + 2 ^ (bl₀.getD i {}).w
    rw [hs.2, hw i]

/-- **Placing two lists of panels that are in BlkShp, member by member.** -/
theorem placePanels_shp {bl bl₀ : Array SBlk} (h : All2 (BlkShp W) bl.toList bl₀.toList) :
    All2 (BlkShp W) (placePanels bl).1.toList (placePanels bl₀).1.toList ∧
      (placePanels bl).2 = (placePanels bl₀).2 := by
  have hk : All2 BlkSkel bl.toList bl₀.toList := all2_mono (fun _ _ k => k.skel) h
  have hw := w_skel hk
  rw [placePanels_eq, placePanels_eq, placeOrder_skel hk]
  exact RtPub.foldl_rel
    (R := fun s s₀ : Array SBlk × Nat => All2 (BlkShp W) s.1.toList s₀.1.toList ∧ s.2 = s₀.2)
    (fun s s₀ i hs => placeStep_shp hw s s₀ i hs) _ _ _ ⟨h, rfl⟩

/-! ## The batched sumcheck's end -/

/-- Two states of the batched sumcheck's end: the bits of the down product's panel, and the two
forms' shapes. -/
def EndShp (s s₀ : StackEnd) : Prop :=
  s.wD = s₀.wD ∧ SameSh s.Alin s₀.Alin ∧ SameSh s.Blin s₀.Blin

theorem EndShp.intro {s s₀ : StackEnd} (h1 : s.wD = s₀.wD) (h2 : SameSh s.Alin s₀.Alin)
    (h3 : SameSh s.Blin s₀.Blin) : EndShp s s₀ := And.intro h1 (And.intro h2 h3)

variable {W : Prop}

/-- **One panel's step.** -/
theorem stackEndOf_shp (y : Lay) {rs rs₀ : Array E} (lam : Nat) (om H1 V om₀ H1₀ V₀ : Array E)
    {s s₀ : StackEnd} {b b₀ : SBlk} (hb : BlkShp W b b₀) (hr : rs.size = rs₀.size)
    (hs : EndShp s s₀) :
    OptRel EndShp (stackEndOf y rs lam om H1 V s b) (stackEndOf y rs₀ lam om₀ H1₀ V₀ s₀ b₀) := by
  obtain ⟨tri, v0, claim, ec, ni, ny, wy, w, off, A, B, wt, sl, xx, virt⟩ := b
  obtain ⟨tri₀, v0₀, claim₀, ec₀, ni₀, ny₀, wy₀, w₀, off₀, A₀, B₀, wt₀, sl₀, xx₀, virt₀⟩ := b₀
  obtain ⟨e1, e2, e9, e3, e4, e5, e6, e7, e8, hA, hB, hx, _, _⟩ := hb
  dsimp only at e1 e2 e9 e3 e4 e5 e6 e7 e8 hA hB hx
  subst e1 e2 e9 e3 e4 e5 e6 e7 e8
  have hI : eqIndexOK (rs.extract w lam) (off / 2 ^ w) =
      eqIndexOK (rs₀.extract w lam) (off / 2 ^ w) := by
    unfold eqIndexOK
    rw [Array.size_extract, Array.size_extract, hr]
  have hw : s.wD = s₀.wD := hs.1
  unfold stackEndOf
  cases tri with
  | true =>
    cases virt with
    | some k =>
      simp only [↓reduceIte]
      exact optRel_iteB (by rw [hI]) trivial (optRel_bind_same fun _ => optRel_bind_same fun _ =>
        optRel_iteB rfl trivial hs)
    | none =>
      simp only [↓reduceIte]
      exact optRel_iteB (by rw [hI]) trivial (optRel_bind_same fun _ => optRel_bind_same fun _ =>
        optRel_pure (EndShp.intro hs.1
          (RtPub.foldl_rel (R := SameSh) (fun _ _ k2 r => SameSh.addMul r (hx k2) _ _) _ _ _ hs.2.1)
          hs.2.2))
  | false =>
    cases virt with
    | some k =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact optRel_iteB (by rw [hI]) trivial (optRel_bind_same fun _ => optRel_bind_same fun _ =>
        optRel_iteB (by rw [hw]) trivial (optRel_pure (EndShp.intro rfl hs.2.1 hs.2.2)))
    | none =>
      cases v0 with
      | some v0 =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine optRel_iteB (by rw [hI]) trivial (optRel_bind_same fun _ =>
          optRel_bind hA fun f f₀ hf => ?_)
        refine foldlM_opt_rel (fun a a₀ i ha => optRel_bind ?_ fun c c₀ hc => hc) _ _ _ hs
        refine foldlM_opt_rel (fun c c₀ yv hc => ?_) _ _ _ ha
        exact optRel_bind (hf i yv) fun _ _ hq =>
          optRel_pure (EndShp.intro hc.1 (SameSh.addMul hc.2.1 hq _ _) hc.2.2)
      | none =>
        cases B with
        | none =>
          cases B₀ with
          | some _ => exact False.elim hB
          | none =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            refine optRel_iteB (by rw [hI]) trivial (optRel_bind_same fun _ =>
              optRel_bind hA fun f f₀ hf => ?_)
            refine foldlM_opt_rel (fun a a₀ i ha => optRel_bind ?_ fun c c₀ hc => hc) _ _ _ hs
            refine foldlM_opt_rel (fun c c₀ yv hc => ?_) _ _ _ ha
            exact optRel_bind (hf i yv) fun _ _ _ => trivial
        | some g =>
          cases B₀ with
          | none => exact False.elim hB
          | some g₀ =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            refine optRel_iteB (by rw [hI]) trivial (optRel_bind_same fun _ =>
              optRel_bind hA fun f f₀ hf => ?_)
            refine foldlM_opt_rel (fun a a₀ i ha => optRel_bind ?_ fun c c₀ hc => hc) _ _ _ hs
            refine foldlM_opt_rel (fun c c₀ yv hc => ?_) _ _ _ ha
            exact optRel_bind (hf i yv) fun _ _ hq =>
              optRel_bind (hB i yv) fun _ _ hq' =>
                optRel_pure (EndShp.intro hc.1 (SameSh.addMul hc.2.1 hq _ _)
                  (SameSh.addMul hc.2.2 hq' _ _))

/-- **The end over all panels**: both calls return or neither does, and then the down product's bits
agree and the two forms of the one have the shapes of the two forms of the other (EndShp; SameSh:
entries and slots). -/
theorem stackEnd_shp (y : Lay) {bl bl₀ : Array SBlk} {rs rs₀ : Array E} (lam : Nat)
    (om H1 V om₀ H1₀ V₀ : Array E) (a b a₀ b₀ : E)
    (hb : All2 (BlkShp W) bl.toList bl₀.toList) (hr : rs.size = rs₀.size) :
    OptRel EndShp (stackEnd y bl rs lam om H1 V a b)
      (stackEnd y bl₀ rs₀ lam om₀ H1₀ V₀ a₀ b₀) := by
  have key : OptRel EndShp (bl.foldlM (stackEndOf y rs lam om H1 V) { As := a, Bs := b })
      (bl₀.foldlM (stackEndOf y rs₀ lam om₀ H1₀ V₀) { As := a₀, Bs := b₀ }) :=
    afoldlM_all2_rel (S := BlkShp W) (R := EndShp) (f := stackEndOf y rs lam om H1 V)
      (f' := stackEndOf y rs₀ lam om₀ H1₀ V₀)
      (fun _ _ _ _ hs hx => stackEndOf_shp y lam om H1 V om₀ H1₀ V₀ hx hr hs) hb
      { As := a, Bs := b } { As := a₀, Bs := b₀ } (EndShp.intro rfl rfl rfl)
  unfold stackEnd
  refine optRel_bind key fun s s₀ hs => ?_
  have hw : s.wD = s₀.wD := hs.1
  exact optRel_iteB (by rw [hw]) trivial hs

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.optRel_of_eqS
#print axioms OnBytes.Desc.First.K4.Rt.map_pair_sh
#print axioms OnBytes.Desc.First.K4.Rt.sumForms_lt
#print axioms OnBytes.Desc.First.K4.Rt.SxsA_shp
#print axioms OnBytes.Desc.First.K4.Rt.shSum_shp
#print axioms OnBytes.Desc.First.K4.Rt.sideShp_none
#print axioms OnBytes.Desc.First.K4.Rt.sideShp_some
#print axioms OnBytes.Desc.First.K4.Rt.sideShp_rows
#print axioms OnBytes.Desc.First.K4.Rt.SideShp.skel
#print axioms OnBytes.Desc.First.K4.Rt.BlkShp.skel
#print axioms OnBytes.Desc.First.K4.Rt.PanShp.skel
#print axioms OnBytes.Desc.First.K4.Rt.PanShp.nil
#print axioms OnBytes.Desc.First.K4.Rt.plain_shp
#print axioms OnBytes.Desc.First.K4.Rt.tri_shp
#print axioms OnBytes.Desc.First.K4.Rt.panelA_shp
#print axioms OnBytes.Desc.First.K4.Rt.panelsA_shp
#print axioms OnBytes.Desc.First.K4.Rt.panelT_shp
#print axioms OnBytes.Desc.First.K4.Rt.panelsT_shp
#print axioms OnBytes.Desc.First.K4.Rt.panels_shp
#print axioms OnBytes.Desc.First.K4.Rt.placeStep_shp
#print axioms OnBytes.Desc.First.K4.Rt.placePanels_shp
#print axioms OnBytes.Desc.First.K4.Rt.EndShp.intro
#print axioms OnBytes.Desc.First.K4.Rt.stackEndOf_shp
#print axioms OnBytes.Desc.First.K4.Rt.stackEnd_shp
#print axioms OnBytes.Desc.First.K4.Rt.SideShp
#print axioms OnBytes.Desc.First.K4.Rt.BlkShp
#print axioms OnBytes.Desc.First.K4.Rt.PanShp
#print axioms OnBytes.Desc.First.K4.Rt.EndShp
