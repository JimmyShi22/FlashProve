-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBatShapeProofs.lean: the proofs of the statements of Cb/Ld/LdBatShape.lean (a code of a main
relation in another shape; virtual rows; renamings of coordinates).

Named tools: `shape_cnt_inj` (an injective map that keeps a property does not lower a count),
`Reshape.Laws.near_fwd`, `Reshape.Laws.near_bwd` (closeness forth and back), `pair_T_iff`,
`fam_T_iff` (the symbols at a long position, `C.T f x`, of codes side by side), `LdCode.dist_eq`,
`arr_T_some`, `arr_T_none` (long symbols of an arranged word), `Reshape.laws_of_bij`. Nothing is
defined here that a statement reads.

Main names (statements and hypotheses: Cb/Ld/LdBatShape.lean):
  `ldShape_step`, `ldShape_piece`: the reshape as a step without rounds, as a piece of a chain.
  `ldShape_same`: one relation up to a bijection of witnesses.
  `ldShape_list`: the two codes' lists.
  `ldShape_refl`, `ldShape_comp`, `ldShape_pairL`, `ldShape_pairR`, `ldShape_fam`: the operations.
  `ldShape_arr`, `ldShape_arr_fix`: the two statements on virtual rows.
  `ldShape_two`: main rows and mask rows at once.
  `ldShape_gather`, `ldShape_curry`: the two renamings.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdBatShape
import Cb.Ld.LdRelProofsCode

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR

theorem shape_cnt_inj {α β : Type} [Finite α] [Finite β] (φ : α → β) (hφ : Function.Injective φ)
    {A : α → Prop} {B : β → Prop} (h : ∀ a, A a → B (φ a)) : cnt A ≤ cnt B := by
  unfold cnt
  exact Nat.card_le_card_of_injective (fun a : {a // A a} => (⟨φ a.1, h a.1 a.2⟩ : {b // B b}))
    fun a b hab => Subtype.ext (hφ (congrArg Subtype.val hab))

section General
variable {E P : Type} [Field E] [Fintype P] {C C' C'' : LdCode E P}

theorem Reshape.Laws.near_fwd {ρ : Reshape C C'} (hL : ρ.Laws) (e : ℕ) (f : C.Word)
    (w : (C.J → E) × (C.Q → E)) (h : C.Near e f (C.enc w.1 w.2)) :
    C'.Near e (ρ.wd f) (C'.enc (ρ.up w).1 (ρ.up w).2) := by
  rw [← hL.enc w]
  exact le_trans
    (cnt_mono (Q := fun x => C.T f x ≠ C.T (C.enc w.1 w.2) x) fun x hx hfg => hx (hL.loc _ _ x hfg))
    h

theorem Reshape.Laws.near_bwd {ρ : Reshape C C'} (hL : ρ.Laws) (e : ℕ) (f : C.Word)
    (w' : (C'.J → E) × (C'.Q → E)) (h : C'.Near e (ρ.wd f) (C'.enc w'.1 w'.2)) :
    C.Near e f (C.enc (ρ.dn w').1 (ρ.dn w').2) :=
  le_trans (cnt_mono (Q := fun x => C'.T (ρ.wd f) x ≠ C'.T (C'.enc w'.1 w'.2) x)
    fun x hx hfg => hx (hL.off _ _ x hfg)) h

omit [Fintype P] in
theorem Reshape.Laws.val_up {ρ : Reshape C C'} (hL : ρ.Laws)
    (a : C.J → E) (w : (C.J → E) × (C.Q → E)) :
    ∑ j, ρ.fm a j * (ρ.up w).1 j = ∑ j, a j * w.1 j := by
  rw [hL.val a (ρ.up w), hL.inj w]

end General

section Statements
variable (E P : Type) [Field E] [Fintype E] [Fintype P]

theorem ldShape_step : Spec.ldShape_step E P := by
  intro C C' ρ e St s hL
  refine ⟨fun y y' q h => hL.loc y y' q (h q (Finset.mem_singleton_self q)), ?_,
    fun _ _ _ _ _ => trivial, fun _ _ => rfl, ?_⟩
  · rintro x y w ⟨h1, h2⟩
    refine ⟨rfl, ?_, (hL.val_up (s x.2) w).trans h2⟩
    show ρ.wd y = C'.enc (ρ.up w).1 (ρ.up w).2
    rw [h1]
    exact hL.enc w
  · rintro x y x' w' _ hx ⟨h1, h2⟩
    rw [← Option.some.inj hx] at h2
    exact ⟨hL.near_bwd e y w' h1, (hL.val (s x.2) w').symm.trans h2⟩

open Classical in
theorem ldShape_piece : Spec.ldShape_piece E P := by
  intro C C' ρ e St s q hL
  refine pieceTr_pure Unit _ _ C.ext C'.ext _ _ _ _ _ ρ.map _ (fun _ w => ρ.dn w) q q
    (ldShape_step E P C C' ρ e St s hL) fun U hU => ?_
  have e1 : U.biUnion ρ.map.src = U := by
    ext x
    simp [Reshape.map]
  rw [e1]
  exact hU

theorem ldShape_same : Spec.ldShape_same E P := by
  intro C C' ρ e St s hL hF x f
  refine ⟨fun w => ⟨fun h => ⟨hL.near_fwd e f w h.1, (hL.val_up (s x.2) w).trans h.2⟩, fun h => ?_⟩,
    fun w' h => hF f w' h.1,
    fun w =>
      ⟨fun h => ⟨?_, (hL.val_up (s x.2) w).trans h.2⟩,
        fun h => ⟨?_, (hL.val_up (s x.2) w).symm.trans h.2⟩⟩,
    fun w' h => hF f w' ?_⟩
  · have h1 := hL.near_bwd e f (ρ.up w) h.1
    rw [hL.inj w] at h1
    exact ⟨h1, (hL.val_up (s x.2) w).symm.trans h.2⟩
  · show ρ.wd f = C'.enc (ρ.up w).1 (ρ.up w).2
    rw [show f = C.enc w.1 w.2 from h.1]
    exact hL.enc w
  · exact hL.winj _ _ ((show ρ.wd f = C'.enc (ρ.up w).1 (ρ.up w).2 from h.1).trans (hL.enc w).symm)
  · have h1 : ρ.wd f = C'.enc w'.1 w'.2 := h.1
    show cnt (fun x => C'.T (ρ.wd f) x ≠ C'.T (C'.enc w'.1 w'.2) x) ≤ e
    rw [h1, cnt_false fun _ hx => hx rfl]
    exact Nat.zero_le e

theorem ldShape_list : Spec.ldShape_list E P := by
  intro C C' ρ e L hL hl f
  exact (shape_cnt_inj ρ.up (fun w v h => by rw [← hL.inj w, h, hL.inj v]) fun w h =>
      hL.near_fwd e f w h).trans (hl (ρ.wd f))

omit [Fintype E] in
theorem ldShape_refl : Spec.ldShape_refl E P := fun _ =>
  ⟨⟨fun _ _ _ h => h, fun _ => rfl, fun _ _ _ h => h, fun _ => rfl, fun _ _ h => h, fun _ _ => rfl⟩,
    fun _ _ _ _ => rfl⟩

omit [Fintype E] in
theorem ldShape_comp : Spec.ldShape_comp E P := by
  intro C C' C'' ρ ρ' hL hL'
  refine ⟨⟨fun f g x h => hL'.loc _ _ x (hL.loc f g x h),
      fun w => ?_,
      fun f w x h => hL.off f _ x (hL'.off _ w x h),
      fun w => ?_,
      fun f g h => hL.winj f g (hL'.winj _ _ h),
      fun a w => ?_⟩,
    fun e hF hF' f w h => ?_⟩
  · show ρ'.wd (ρ.wd (C.enc w.1 w.2)) = _
    rw [hL.enc w]
    exact hL'.enc (ρ.up w)
  · show ρ.dn (ρ'.dn (ρ'.up (ρ.up w))) = w
    rw [hL'.inj, hL.inj]
  · exact (hL'.val (ρ.fm a) w).trans (hL.val a (ρ'.dn w))
  · show ρ'.up (ρ.up (ρ.dn (ρ'.dn w))) = w
    rw [hF f (ρ'.dn w) (hL'.near_bwd e (ρ.wd f) w h)]
    exact hF' (ρ.wd f) w h

end Statements

section Sides
variable {E P : Type} {C₁ C₂ : LdCode E P}

theorem pair_T_iff (f g : (C₁.pair C₂).Word) (x : P) :
    (C₁.pair C₂).T f x = (C₁.pair C₂).T g x ↔
    C₁.T (LdCode.fstW f) x = C₁.T (LdCode.fstW g) x ∧
    C₂.T (LdCode.sndW f) x = C₂.T (LdCode.sndW g) x := by
  constructor
  · intro h
    exact ⟨funext fun α => congrFun h (.inl α), funext fun α => congrFun h (.inr α)⟩
  · rintro ⟨h1, h2⟩
    funext α
    rcases α with α | α
    · exact congrFun h1 α
    · exact congrFun h2 α

theorem mkP_eta (w : ((C₁.pair C₂).J → E) × ((C₁.pair C₂).Q → E)) :
    Reshape.mkP (Reshape.fstP w) (Reshape.sndP w) = w :=
  Prod.ext (funext fun j => by rcases j with j | j <;> rfl)
    (funext fun q => by rcases q with q | q <;> rfl)

theorem mkW_eta (f : (C₁.pair C₂).Word) : LdCode.mkW (LdCode.fstW f) (LdCode.sndW f) = f :=
  funext fun p => by rcases p with p | p <;> rfl

theorem fam_T_iff {A : Type} [Fintype A] [DecidableEq A] (D : A → LdCode E P)
    (f g : (LdCode.fam D).Word) (x : P) :
    (LdCode.fam D).T f x = (LdCode.fam D).T g x ↔
    ∀ a, (D a).T (fun p => f ⟨a, p⟩) x = (D a).T (fun p => g ⟨a, p⟩) x :=
  ⟨fun h a => funext fun α => congrFun h ⟨a, α⟩, fun h => funext fun α => congrFun (h α.1) α.2⟩

end Sides

section Statements2
variable (E P : Type) [Field E] [Fintype E] [Fintype P]

omit [Fintype E] in
theorem ldShape_pairL : Spec.ldShape_pairL E P := by
  intro C C' D ρ hL
  refine ⟨⟨fun f g x h => ?_, fun w => ?_, fun f w x h => ?_, fun w => ?_,
      fun f g h => ?_, fun a w => ?_⟩,
    fun e hF f w h => ?_⟩
  · obtain ⟨h1, h2⟩ := (pair_T_iff f g x).1 h
    exact (pair_T_iff _ _ x).2 ⟨hL.loc _ _ x h1, h2⟩
  · funext p
    rcases p with p | p
    · exact congrFun (hL.enc (Reshape.fstP w)) p
    · rfl
  · obtain ⟨h1, h2⟩ := (pair_T_iff _ _ x).1 h
    exact (pair_T_iff _ _ x).2 ⟨hL.off (LdCode.fstW f) (Reshape.fstP w) x h1, h2⟩
  · show Reshape.mkP (ρ.dn (ρ.up (Reshape.fstP w))) (Reshape.sndP w) = w
    rw [hL.inj]
    exact mkP_eta w
  · have h1 : LdCode.fstW f = LdCode.fstW g := hL.winj _ _ (congrArg LdCode.fstW h)
    have h2 : LdCode.sndW f = LdCode.sndW g :=
      (congrArg LdCode.sndW h : LdCode.sndW ((ρ.pairL D).wd f) = LdCode.sndW ((ρ.pairL D).wd g))
    rw [← mkW_eta f, ← mkW_eta g, h1, h2]
  · rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    exact congrArg (· + _) (hL.val (fun j => a (.inl j)) (Reshape.fstP w))
  · have h1 := (ld_near_pair E P C' D e _ _ h).1
    show Reshape.mkP (ρ.up (ρ.dn (Reshape.fstP w))) (Reshape.sndP w) = w
    rw [hF (LdCode.fstW f) (Reshape.fstP w) h1]
    exact mkP_eta w

omit [Fintype E] in
theorem ldShape_pairR : Spec.ldShape_pairR E P := by
  intro C C' D ρ hL
  refine ⟨⟨fun f g x h => ?_, fun w => ?_, fun f w x h => ?_, fun w => ?_,
      fun f g h => ?_, fun a w => ?_⟩,
    fun e hF f w h => ?_⟩
  · obtain ⟨h1, h2⟩ := (pair_T_iff f g x).1 h
    exact (pair_T_iff _ _ x).2 ⟨h1, hL.loc _ _ x h2⟩
  · funext p
    rcases p with p | p
    · rfl
    · exact congrFun (hL.enc (Reshape.sndP w)) p
  · obtain ⟨h1, h2⟩ := (pair_T_iff _ _ x).1 h
    exact (pair_T_iff _ _ x).2 ⟨h1, hL.off (LdCode.sndW f) (Reshape.sndP w) x h2⟩
  · show Reshape.mkP (Reshape.fstP w) (ρ.dn (ρ.up (Reshape.sndP w))) = w
    rw [hL.inj]
    exact mkP_eta w
  · have h1 : LdCode.fstW f = LdCode.fstW g :=
      (congrArg LdCode.fstW h : LdCode.fstW ((ρ.pairR D).wd f) = LdCode.fstW ((ρ.pairR D).wd g))
    have h2 : LdCode.sndW f = LdCode.sndW g := hL.winj _ _ (congrArg LdCode.sndW h)
    rw [← mkW_eta f, ← mkW_eta g, h1, h2]
  · rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    exact congrArg (_ + ·) (hL.val (fun j => a (.inr j)) (Reshape.sndP w))
  · have h1 := (ld_near_pair E P D C' e _ _ h).2
    show Reshape.mkP (Reshape.fstP w) (ρ.up (ρ.dn (Reshape.sndP w))) = w
    rw [hF (LdCode.sndW f) (Reshape.sndP w) h1]
    exact mkP_eta w

omit [Fintype E] in
theorem ldShape_fam : Spec.ldShape_fam E P := by
  intro A _ _ D D' ρ hL
  refine ⟨⟨fun f g x h => ?_, fun w => ?_, fun f w x h => ?_, fun w => ?_,
      fun f g h => ?_, fun a w => ?_⟩,
    fun e hF f w h => ?_⟩
  · exact (fam_T_iff D' _ _ x).2 fun a => (hL a).loc _ _ x ((fam_T_iff D f g x).1 h a)
  · funext p
    exact congrFun ((hL p.1).enc (Reshape.atP w p.1)) p.2
  · exact (fam_T_iff D _ _ x).2 fun a =>
      (hL a).off _ (Reshape.atP w a) x ((fam_T_iff D' _ _ x).1 h a)
  · exact Prod.ext
      (funext fun j => congrFun (congrArg Prod.fst ((hL j.1).inj (Reshape.atP w j.1))) j.2)
      (funext fun q => congrFun (congrArg Prod.snd ((hL q.1).inj (Reshape.atP w q.1))) q.2)
  · funext p
    exact congrFun
      ((hL p.1).winj (fun p' => f ⟨p.1, p'⟩) (fun p' => g ⟨p.1, p'⟩)
        (funext fun p' => congrFun h ⟨p.1, p'⟩)) p.2
  · rw [Fintype.sum_sigma, Fintype.sum_sigma]
    exact Finset.sum_congr rfl fun b _ => (hL b).val (fun j' => a ⟨b, j'⟩) (Reshape.atP w b)
  · have h1 : ∀ a, (ρ a).up ((ρ a).dn (Reshape.atP w a)) = Reshape.atP w a := fun a =>
      hF a (fun p => f ⟨a, p⟩) (Reshape.atP w a) (near_fam E P D' e _ _ h a)
    exact Prod.ext (funext fun j => congrFun (congrArg Prod.fst (h1 j.1)) j.2)
      (funext fun q => congrFun (congrArg Prod.snd (h1 q.1)) q.2)

end Statements2

section ArrTools
variable {E P : Type} [Field E] {C : LdCode E P}

/-- Under the laws of C, two codewords that differ at fewer long positions than the distance are
one. -/
theorem LdCode.dist_eq [Fintype P] (hC : C.Laws) {d e : ℕ} (hd : C.Dist d) (he : e < d)
    (u v : (C.J → E) × (C.Q → E))
    (h : cnt (fun x => C.T (C.enc u.1 u.2) x ≠ C.T (C.enc v.1 v.2) x) ≤ e) : u = v := by
  by_contra hne
  have h0 : ¬ (u.1 - v.1 = 0 ∧ u.2 - v.2 = 0) := fun h0 =>
    hne (Prod.ext (sub_eq_zero.1 h0.1) (sub_eq_zero.1 h0.2))
  have h1 := hd (u.1 - v.1) (u.2 - v.2) h0
  have h2 : C.enc (u.1 - v.1) (u.2 - v.2) = C.enc u.1 u.2 - C.enc v.1 v.2 := hC.encLin.map_sub u v
  rw [h2, hC.tLin.map_sub] at h1
  refine absurd (h1.trans ((cnt_mono fun x hx hxe => hx ?_).trans h)) (not_le.2 he)
  show C.T (C.enc u.1 u.2) x - C.T (C.enc v.1 v.2) x = 0
  rw [hxe, sub_self]

variable {R R' : Type} [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R'] (a : Arr R R')

omit [Field E] in
theorem arr_T_some [Zero E] (f : (C.il R).Word) (x : P) (i : R') (r : R)
    (β : C.Aa) (h : a.src i = some r) :
    (C.il R').T ((a.reshape C).wd f) x (i, β) = (C.il R).T f x (r, β) := by
  show C.T (fun p s => a.spread (f p) (i, s)) x β = C.T (fun p s => f p (r, s)) x β
  simp only [Arr.spread, h]

theorem arr_T_none (hC : C.Laws) (f : (C.il R).Word) (x : P) (i : R')
    (β : C.Aa) (h : a.src i = none) :
    (C.il R').T ((a.reshape C).wd f) x (i, β) = 0 := by
  show C.T (fun p s => a.spread (f p) (i, s)) x β = 0
  simp only [Arr.spread, h]
  exact congrFun (congrFun hC.tLin.map_zero x) β

omit [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R'] [Field E] in
theorem Arr.pick_spread [Zero E] {X : Type} (ha : a.OK) (v : R × X → E) :
    a.pick (a.spread v) = v := by
  funext n
  simp [Arr.pick, Arr.spread, ha n.1]

omit [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R'] in
theorem Arr.rep_inj (ha : a.OK) : Function.Injective a.rep := fun r r' h =>
  Option.some.inj ((ha r).symm.trans ((congrArg a.src h).trans (ha r')))

end ArrTools

section Statements3
variable (E P : Type) [Field E] [Fintype E] [Fintype P]

omit [Fintype E] [Fintype P] in
theorem ldShape_arr : Spec.ldShape_arr E P := by
  intro C R R' _ _ _ _ a hC ha
  refine ⟨fun f g x h => ?_, fun w => ?_, fun f w x h => ?_,
    fun w => Prod.ext (a.pick_spread ha w.1) (a.pick_spread ha w.2), fun f g h => ?_, fun c w => ?_⟩
  · funext α
    obtain ⟨i, β⟩ := α
    cases hi : a.src i with
    | some r => rw [arr_T_some a f x i r β hi, arr_T_some a g x i r β hi, h]
    | none => rw [arr_T_none a hC f x i β hi, arr_T_none a hC g x i β hi]
  · funext p s
    obtain ⟨i, s⟩ := s
    show a.spread ((C.il R).enc w.1 w.2 p) (i, s) =
      C.enc (fun j => a.spread w.1 (i, j)) (fun q => a.spread w.2 (i, q)) p s
    cases hi : a.src i with
    | some r => simp only [Arr.spread, hi]
    | none =>
      simp only [Arr.spread, hi]
      exact (congrFun (congrFun hC.encLin.map_zero p) s).symm
  · funext α
    obtain ⟨r, β⟩ := α
    rw [← arr_T_some a f x (a.rep r) r β (ha r), h]
    rfl
  · funext p s
    have h1 := congrFun (congrFun h p) (a.rep s.1, s.2)
    have h2 : ∀ k : (C.il R).Word, (a.reshape C).wd k p (a.rep s.1, s.2) = k p s := fun k => by
      show a.spread (k p) (a.rep s.1, s.2) = k p s
      simp [Arr.spread, ha s.1]
    rw [h2 f, h2 g] at h1
    exact h1
  · show ∑ n : R' × C.J, a.place c n * w.1 n = ∑ n : R × C.J, c n * a.pick w.1 n
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine (Fintype.sum_of_injective a.rep (a.rep_inj ha) _ _ (fun i hi => ?_) fun r => ?_).symm
    · refine Finset.sum_eq_zero fun j _ => ?_
      cases hs : a.src i with
      | some r =>
        have hne : a.rep r ≠ i := fun e => hi ⟨r, e⟩
        simp [Arr.place, hs, hne]
      | none => simp [Arr.place, hs]
    · exact Finset.sum_congr rfl fun j _ => by simp [Arr.place, Arr.pick, ha r]

omit [Fintype E] in
theorem ldShape_arr_fix : Spec.ldShape_arr_fix E P := by
  intro C R R' _ _ _ _ a d e hC hd he ha f w h
  have hrow : ∀ i : R', ((fun j => w.1 (i, j), fun q => w.2 (i, q)) : (C.J → E) × (C.Q → E)) =
      (fun j => a.spread (a.pick w.1) (i, j), fun q => a.spread (a.pick w.2) (i, q)) := by
    intro i
    refine LdCode.dist_eq hC hd he _ _
      (le_trans (cnt_mono
          (Q := fun x => (C.il R').T ((a.reshape C).wd f) x ≠ (C.il R').T ((C.il R').enc w.1 w.2) x)
          fun x hx hxe => hx ?_) h)
    funext β
    have hi0 : C.T (C.enc (fun j => w.1 (i, j)) fun q => w.2 (i, q)) x β =
        (C.il R').T ((a.reshape C).wd f) x (i, β) :=
      (congrFun hxe (i, β)).symm
    show C.T (C.enc (fun j => w.1 (i, j)) fun q => w.2 (i, q)) x β =
      C.T (C.enc (fun j => a.spread (a.pick w.1) (i, j)) fun q => a.spread (a.pick w.2) (i, q)) x β
    rw [hi0]
    cases hi : a.src i with
    | some r =>
      simp only [Arr.spread, Arr.pick, hi]
      rw [arr_T_some a f x i r β hi, ← arr_T_some a f x (a.rep r) r β (ha r)]
      exact congrFun hxe (a.rep r, β)
    | none =>
      simp only [Arr.spread, hi]
      rw [arr_T_none a hC f x i β hi]
      have h0 : C.enc (fun _ => (0 : E)) (fun _ => (0 : E)) = 0 := hC.encLin.map_zero
      rw [h0]
      exact (congrFun (congrFun hC.tLin.map_zero x) β).symm
  exact Prod.ext (funext fun n => (congrFun (congrArg Prod.fst (hrow n.1)) n.2).symm)
    (funext fun n => (congrFun (congrArg Prod.snd (hrow n.1)) n.2).symm)

omit [Fintype E] in
theorem ldShape_two : Spec.ldShape_two E P := by
  intro C Z R R' Rz Rz' _ _ _ _ _ _ _ _ a az hC ha hZ haz
  have h1 := ldShape_pairL E P _ _ (Z.il Rz) (a.reshape C) (ldShape_arr E P C R R' a hC ha)
  have h2 := ldShape_pairR E P _ _ (C.il R') (az.reshape Z) (ldShape_arr E P Z Rz Rz' az hZ haz)
  have h3 := ldShape_comp E P _ _ _ _ _ h1.1 h2.1
  exact ⟨h3.1,
    fun d dz e hd he hdz hez =>
      h3.2 e (h1.2 e (ldShape_arr_fix E P C R R' a d e hC hd he ha))
        (h2.2 e (ldShape_arr_fix E P Z Rz Rz' az dz e hZ hdz hez haz))⟩

end Statements3

/-- A renaming that is a bijection: under the hypotheses below it has the laws, and `Fix` at every
radius. -/
theorem Reshape.laws_of_bij {E P : Type} [Field E] [Fintype P] {C C' : LdCode E P}
    (ρ : Reshape C C') (hT : ∀ f g x, C.T f x = C.T g x ↔ C'.T (ρ.wd f) x = C'.T (ρ.wd g) x)
    (henc : ∀ w, ρ.wd (C.enc w.1 w.2) = C'.enc (ρ.up w).1 (ρ.up w).2) (hud : ∀ w, ρ.up (ρ.dn w) = w)
    (hdu : ∀ w, ρ.dn (ρ.up w) = w) (hw : ∀ f g, ρ.wd f = ρ.wd g → f = g)
    (hval : ∀ a w', ∑ j, ρ.fm a j * w'.1 j = ∑ j, a j * (ρ.dn w').1 j) : ρ.Laws ∧ ∀ e, ρ.Fix e :=
  ⟨⟨fun f g x h => (hT f g x).1 h, henc,
      fun f w' x h => (hT _ _ x).2 (by rw [henc, hud]; exact h), hdu, hw, hval⟩,
    fun _ _ w' _ => hud w'⟩

section Statements4
variable (E P : Type) [Field E] [Fintype E] [Fintype P]

omit [Fintype E] in
theorem ldShape_gather : Spec.ldShape_gather E P := by
  intro A Rm Rz _ _ _ _ _ _ Cb Zb
  refine Reshape.laws_of_bij _ (fun f g x => ⟨fun h => ?_, fun h => ?_⟩) (fun w => ?_) (fun w => ?_)
    (fun w => ?_) (fun f g h => ?_) fun a w => ?_
  · funext α
    rcases α with ⟨⟨a, i⟩, β⟩ | ⟨⟨a, i⟩, β⟩
    · exact congrFun h ⟨a, .inl (i, β)⟩
    · exact congrFun h ⟨a, .inr (i, β)⟩
  · funext α
    rcases α with ⟨a, ⟨i, β⟩ | ⟨i, β⟩⟩
    · exact congrFun h (.inl (⟨a, i⟩, β))
    · exact congrFun h (.inr (⟨a, i⟩, β))
  · funext p
    rcases p with p | p <;> rfl
  · exact Prod.ext (funext fun j => congrArg w.1 ((gatE Rm Rz Cb.J Zb.J).symm_apply_apply j))
      (funext fun q => congrArg w.2 ((gatE Rm Rz Cb.Q Zb.Q).symm_apply_apply q))
  · exact Prod.ext (funext fun j => congrArg w.1 ((gatE Rm Rz Cb.J Zb.J).apply_symm_apply j))
      (funext fun q => congrArg w.2 ((gatE Rm Rz Cb.Q Zb.Q).apply_symm_apply q))
  · funext p
    rcases p with ⟨a, p | p⟩
    · funext s
      exact congrFun (congrFun h (.inl p)) (⟨a, s.1⟩, s.2)
    · funext s
      exact congrFun (congrFun h (.inr p)) (⟨a, s.1⟩, s.2)
  · refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_)
      (Equiv.sum_comp (gatE Rm Rz Cb.J Zb.J) (fun j => a j * w.1 ((gatE Rm Rz Cb.J Zb.J).symm j)))
    show a (gatE Rm Rz Cb.J Zb.J j) * w.1 j =
      a (gatE Rm Rz Cb.J Zb.J j) * w.1 ((gatE Rm Rz Cb.J Zb.J).symm (gatE Rm Rz Cb.J Zb.J j))
    rw [Equiv.symm_apply_apply]

omit [Fintype E] in
theorem ldShape_curry : Spec.ldShape_curry E P := by
  intro C R₁ R₂ _ _ _ _
  refine Reshape.laws_of_bij _ (fun f g x => ⟨fun h => ?_, fun h => ?_⟩) (fun w => rfl)
    (fun w => rfl) (fun w => rfl) (fun f g h => ?_) fun a w => ?_
  · funext α
    exact congrFun h ((α.1, α.2.1), α.2.2)
  · funext α
    exact congrFun h (α.1.1, (α.1.2, α.2))
  · funext p s
    exact congrFun (congrFun h p) (s.1.1, (s.1.2, s.2))
  · exact (Equiv.sum_comp (Equiv.prodAssoc R₁ R₂ C.J)
      (fun j : R₁ × (R₂ × C.J) => a ((j.1, j.2.1), j.2.2) * w.1 j)).symm

end Statements4
end Cb
