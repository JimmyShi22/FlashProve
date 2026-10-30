-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinkCloseProofs.lean: the proofs of the statements of Cb/Ld/LdLinkClose.lean (the closing of
the link between two encoded indices).

The order: a chain in front of a closing (`ldChain_front`: no hypothesis on what stands before:
`c₀.Ok` is not asked; c₀ enters by `h₁` alone); the value of each kind of form (`LdLkP.recF_val`,
`LdLkP.colF_val`, `LdLkP.layF_val`); the rows (`ldLkC_rows`); what is needed of the members' words
(`ldLkC_need`); the step without rounds (`ldLkC_step`); the closing chain (`ldLkC_chain`); the link
with it (`ldLkC_tail`). Nothing is defined here that a statement reads.
What the statements say, with their hypotheses, and what they do not say: Cb/Ld/LdLinkClose.lean.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinkClose
import Cb.Ld.LdFoldEqProofs
import Cb.Ld.LdLinkWordsProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- A chain in front of another, behind a third. Under `h₁`, `h₂`: `(c₁.append c₂).OkFrom c₀`. -/
theorem ldChain_okFrom_append {K : Type} {Z A B C : Joint K} (c₀ : Chain K Z A) (c₁ : Chain K A B)
    (c₂ : Chain K B C) (h₁ : c₁.OkFrom c₀) (h₂ : c₂.OkFrom (c₀.append c₁)) :
    (c₁.append c₂).OkFrom c₀ := by
  induction c₂ with
  | one l =>
      rw [Chain.append_one]
      exact (Chain.okFrom_snoc c₀ c₁ l).2 ⟨h₁, (Chain.okFrom_one _ l).1 h₂⟩
  | snoc c l ih =>
      rw [Chain.append_snoc]
      obtain ⟨h3, h4⟩ := (Chain.okFrom_snoc _ c l).1 h₂
      rw [ldChain_assoc] at h4
      exact (Chain.okFrom_snoc c₀ (c₁.append c) l).2 ⟨ih h3, h4⟩

/-- Links in front of a closing. Under `hQ`, `h₁`, `s₁`: `(c₁.append Q.c).OkFrom c₀` and
`(c₁.append Q.c).SidesCT qa`. Nothing is asked of what stands before them (`c₀.Ok` is not asked; c₀
enters by `h₁` alone). -/
theorem ldChain_front {E : Type} [Field E] {S : Sig E} {E₀ : ExtSpec} {Wp : Type} (Q : LdTc S E₀ Wp)
    {Z A : Joint Unit} (c₀ : Chain Unit Z A) (c₁ : Chain Unit A (S.jointCf Q.base))
    (qa : Finset A.E.Pos → Prop) (hQ : Q.OK) (h₁ : c₁.OkFrom c₀) (s₁ : c₁.SidesC qa Q.q) :
    (c₁.append Q.c).OkFrom c₀ ∧ (c₁.append Q.c).SidesCT qa :=
  ⟨ldChain_okFrom_append c₀ c₁ Q.c h₁ (ldChain_behind E S E₀ Wp Q Z (c₀.append c₁) hQ).1,
    sidesCT_append Unit _ _ _ c₁ Q.c qa Q.q s₁ hQ.2⟩

section
variable {E ι κ J Λ : Type} [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J]
  [Fintype Λ] (P : LdLkP E ι κ J Λ)

omit [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype Λ] in
theorem LdLkP.recF_val (G : Grp P.N) (i : P.N.O) (h : G.mem i) (l : κ → (P.N.om i).C.J)
    (s : P.D.X.Z.S) (ρ : P.D.X.Z.D) (m : P.N.Msg) :
    (G.onMem i h (P.recF i l s)).val ρ (G.msg m) =
      P.D.X.Z.val ρ (P.D.X.msg fun k => m i (l k)) s := by
  rw [ldForm_onMem]
  exact ldForm_push E _ _ _ _ _ ρ (m i)

omit [Fintype E] [Fintype ι] [Nonempty ι] [Fintype J] [Fintype Λ] in
theorem LdLkP.colF_val (G : Grp P.N) (i : P.N.O) (h : G.mem i)
    (l : κ → (P.N.om i).C.J) (x : ι) (m : P.N.Msg) :
    (G.onMem i h (P.colF i l)).val x (G.msg m) = P.D.X.G.mulVec (fun k => m i (l k)) x := by
  rw [ldForm_onMem]
  exact ldForm_push E _ _ _ _ _ x (m i)

omit [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] in
theorem LdLkP.layF_val (G : Grp P.N) (i : P.N.O) (h : G.mem i) (l : κ → (P.N.om i).C.J)
    (φ : Fin P.D.l → E) (m : P.N.Msg) :
    (G.onMem i h (P.layF i l)).val φ (G.msg m) =
      ∑ a, Alg.eqk φ (P.D.pl a) * P.D.layV (fun k => m i (l k)) a := by
  rw [ldForm_onMem]
  exact ldForm_push E _ _ _ _ _ φ (m i)

end

section
variable (E ι κ J Λ : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Λ]

omit [Fintype E] [Fintype ι] [Nonempty ι] in
theorem ldLkC_rows : Spec.ldLkC_rows E ι κ J Λ := by
  intro P G all x m
  have e0 : ∀ s, (P.rows G all (.inl (.inl s))).val ((P.claims x).2 (.inl (.inl s))) (G.msg m) =
      P.D.X.Z.val x.1.1.1.1.1.1 (P.D.X.msg (P.uv₀ m)) s :=
    fun s => P.recF_val G P.i₀ (all _) P.l₀ s _ m
  have e1 : ∀ i, (P.rows G all (.inl (.inr i))).val ((P.claims x).2 (.inl (.inr i))) (G.msg m) =
      P.D.X.G.mulVec (P.uv₀ m) (x.1.2.1.1 i) :=
    fun i => P.colF_val G P.i₀ (all _) P.l₀ _ m
  have e2 : ∀ s,
      (P.rows G all (.inr (.inl (.inl s)))).val ((P.claims x).2 (.inr (.inl (.inl s)))) (G.msg m) =
        P.D.X.Z.val x.1.1.1.1.2.1 (P.D.X.msg (P.uv₁ m)) s :=
    fun s => P.recF_val G P.i₁ (all _) P.l₁ s _ m
  have e3 : ∀ i,
      (P.rows G all (.inr (.inl (.inr i)))).val ((P.claims x).2 (.inr (.inl (.inr i)))) (G.msg m) =
        P.D.X.G.mulVec (P.uv₁ m) (x.1.2.2.1 i) :=
    fun i => P.colF_val G P.i₁ (all _) P.l₁ _ m
  have e4 : (P.rows G all (.inr (.inr ()))).val ((P.claims x).2 (.inr (.inr ()))) (G.msg m) =
      ∑ a, Alg.eqk x.2 (P.D.pl a) * (P.D.layV (P.uv₀ m) a - P.D.layV (P.uv₁ m) a) := by
    show ((G.onMem P.i₀ (all _) (P.layF P.i₀ P.l₀)).sub
          (G.onMem P.i₁ (all _) (P.layF P.i₁ P.l₁))).val
        x.2 (G.msg m) = _
    rw [ldForm_sub, P.layF_val, P.layF_val, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => (mul_sub _ _ _).symm
  constructor
  · intro h
    exact ⟨⟨funext fun s => (e0 s).symm.trans (h (.inl (.inl s))),
        fun i => (e1 i).symm.trans (h (.inl (.inr i)))⟩,
      ⟨funext fun s => (e2 s).symm.trans (h (.inr (.inl (.inl s)))),
        fun i => (e3 i).symm.trans (h (.inr (.inl (.inr i))))⟩,
      e4.symm.trans (h (.inr (.inr ())))⟩
  · rintro ⟨⟨h0, h1⟩, ⟨h2, h3⟩, h4⟩ b
    rcases b with (s | i) | (s | i) | u
    · exact (e0 s).trans (congrFun h0 s)
    · exact (e1 i).trans (h1 i)
    · exact (e2 s).trans (congrFun h2 s)
    · exact (e3 i).trans (h3 i)
    · exact e4.trans h4

/-- Membership in a union and in an image, whatever the instance that decides equality. -/
theorem ldLkC_mem_biUnion {α β : Type} (inst : DecidableEq β) {s : Finset α}
    {t : α → Finset β} {b : β} :
    b ∈ @Finset.biUnion α β inst s t ↔ ∃ a ∈ s, b ∈ t a :=
  Finset.mem_biUnion
theorem ldLkC_mem_image {α β : Type} (inst : DecidableEq β) {f : α → β} {s : Finset α} {b : β} :
    b ∈ @Finset.image α β inst f s ↔ ∃ a ∈ s, f a = b := Finset.mem_image

omit [Fintype ι] [Nonempty ι] in
/-- What the closing needs of the members' words is within `P.q3 S`: at most `S.t a` long positions
of each member a (under `ht`, `hV`). -/
theorem ldLkC_need (P : LdLkP E ι κ J Λ) (K : P.Cl) (d : P.W2) (S : P.Snd) (ht : ∀ a, K.t ≤ S.t a)
    (V : Finset (extNone.prod P.N.ext).Pos) (hV : (K.tc d).q V) (inst : DecidableEq P.E3.Pos) :
    P.q3 S (@Finset.biUnion _ _ inst V P.stepG.src) := by
  classical
  obtain ⟨U, ⟨hU, hU0⟩, rfl⟩ := hV
  intro a
  refine le_trans
    (le_trans (le_trans (Finset.card_le_card (t := U.toLeft.image (K.G.pos ⟨a, K.all a⟩)) ?_)
        Finset.card_image_le) hU) (ht a)
  intro y hy
  obtain ⟨v, hv, hyv⟩ := (ldLkC_mem_biUnion _).1 (Finset.mem_preimage.1 hy)
  obtain ⟨u, hu, hvu⟩ := (ldLkC_mem_biUnion _).1 hv
  rcases v with v | v
  · exact v.elim
  · have hv' : (⟨a, y⟩ : P.N.ext.Pos) = v := Finset.mem_singleton.1 hyv
    subst hv'
    rcases u with x | u
    · obtain ⟨p, hp, hpv⟩ := (ldLkC_mem_biUnion _).1 hvu
      have hp' : (⟨a, y⟩ : P.N.ext.Pos) = p := Sum.inr.inj (Finset.mem_singleton.1 hpv)
      subst hp'
      obtain ⟨a', -, ha'⟩ := (ldLkC_mem_image _).1 hp
      obtain ⟨a'', ha''⟩ := a'
      have h1 : a'' = a := congrArg Sigma.fst ha'
      subst h1
      exact Finset.mem_image.2 ⟨x, Finset.mem_toLeft.2 hu, eq_of_heq (Sigma.mk.inj ha').2⟩
    · have : u ∈ U.toRight := Finset.mem_toRight.2 hu
      rw [show U.toRight = ∅ from hU0] at this
      exact absurd this (Finset.notMem_empty _)

omit [Fintype ι] [Nonempty ι] in
theorem ldLkC_step : Spec.ldLkC_step E ι κ J Λ := by
  classical
  intro P K d S ht
  refine pieceTr_pure Unit P.X4 _ P.E3 (extNone.prod P.N.ext) P.W2 P.W2 P.j4
    (P.N.over (K.tc d).base) (fun x => some (P.stepF x)) P.stepG (fun a => (P.stepF a.1, a.2))
    (fun _ w => w) (P.q3 S) (K.tc d).q
    { isLocal := extMap_isLocal.2.2.2.2 _ _ _ _ _ (extMap_isLocal.2.2.1 _) (extMap_isLocal.1 _)
      acc := ?_
      onOut := ?_
      keeps := fun _ _ => rfl
      know := ?_ } (fun V hV => ldLkC_need E ι κ J Λ P K d S ht V hV _)
  · rintro x y w ⟨hEnc, hAns, hR0, hR1, hSame, hu0, hu1, hC0, hC1⟩
    refine ⟨rfl, hEnc, hAns,
      (ldLkC_rows E ι κ J Λ P K.G K.all x (P.N.msgs w.1)).2 ⟨⟨?_, hC0⟩, ⟨?_, hC1⟩, ?_⟩, trivial⟩
    · rw [hu0]
      exact ldFe_rec_fold P.D.X _ _ hR0 _
    · rw [hu1]
      exact ldFe_rec_fold P.D.X _ _ hR1 _
    · rw [hu0, hu1]
      exact (ldLk_complete P.D _ _ _ x.2 hSame).2
  · intro x y x' h hx
    obtain rfl := Option.some.inj hx
    exact ⟨h, trivial⟩
  · intro x y x' w' _ hx h
    obtain rfl := Option.some.inj hx
    exact ⟨h.1, (ldLkC_rows E ι κ J Λ P K.G K.all x (P.N.msgs w'.1)).1 h.2.1⟩

omit [Fintype ι] [Nonempty ι] in
theorem ldLkC_chain : Spec.ldLkC_chain E ι κ J Λ := by
  intro P K d S A c₀ hK ht
  have hs := ldk_pieceTr_cf (ldLkC_step E ι κ J Λ P K d S ht)
  have hQ : (K.tc d).OK :=
    ldChain_cons E P.N extNone P.W0 K.run _ d _ hK (ldChain_nil E _ extNone P.W0 _)
  exact ldChain_front (K.tc d) c₀ (Chain.one (K.lStep d)) (P.q3 S) hQ
    ((Chain.okFrom_one c₀ _).2 (Or.inl hs.good))
    ((Chain.sidesC_one _ _ _).2
      (sideC_of_side _ _ _ _ _ _ _ _ _ _ _ ⟨hs.noHid, hs.noTie, hs.bears⟩))

theorem ldLkC_tail : Spec.ldLkC_tail E ι κ J Λ := by
  intro P on0 on1 ε₀ ε₁ S K d d₀ hF hpl hS hK ht
  obtain ⟨h1, h2⟩ := ldLkC_chain E ι κ J Λ P K d S _ (P.coreC on0 on1 S ε₀ ε₁) hK ht
  exact ldLc_tail P on0 on1 ε₀ ε₁ S (K.cZ d) d₀ hF hpl hS h1 h2

end
end Cb
