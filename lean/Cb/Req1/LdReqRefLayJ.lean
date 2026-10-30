-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqRefLayJ.lean: where the masks of a reference request come from, with joins: own masks
of one block may come from several sendings.

Definitions, statements (each a `Prop` in `Cb.Spec`) and proofs.
The reference request r is the term `ldReqRef`, with its list L (`LdRefL`) of segments S (`LdRefS`)
and its last segment T (Cb/Req1/LdReqRef.lean). Facts: A `MaskFact W` is a reading `kc` of witnesses
of type W into a type `Kc`, a finite, non-empty type `Mk`, and a map `put : Mk → Kc → Kc`.
(Cb/Req1/LdSegFresh.lean); `S.New`, `S.Enters`, `S.Carries`, `L.Laid`: Cb/Req1/LdReqRefLay.lean;
`A.ZkAt`: Cb/Req1/LdReqRefZkP.lean; `AfterJ`, `ZkJ`, `r.ZkS`: Cb/Req1/LdReqS.lean; `MaskFact.JCl`:
Cb/Req1/LdSegFreshS.lean; wide facts: `LdStage.wideFact` (Cb/Req1/LdSegCarry.lean).
Cb/Req1/LdReqRefLay.lean's calculus (laid by the sending before the segment, or carried across
closings) has a gap, declared in its head: a sumcheck of a later segment that ends at a map of the
index has its hiding coefficients in the segment's mask rows and its inner masks in the index-mask
message: own masks of one block from two sendings; no rule joined two facts. Cb/Req1/LdReqS.lean
closes the set of fresh facts, at the entry of each segment and before the last part, under join at
one reading, a coarser reading, another type for the same masks (`MaskFact.JCl`), and states (the
proofs are in Cb/Req1/LdReqSProofs.lean) the whole bundle from `r.Hyp` and `r.ZkS`. Here the
calculus follows.

Main names:
  `L.LaidJ base g`: as `L.Laid`, the set closed at each stage between segments: the closure of
    "base", if L is empty; else the closure of: `S.New g`, or `S.Carries g' g` for some g' with
    `L'.LaidJ base g'`.
  `L.LayJ pp base`: for each segment S: `A.ZkAt pp` at the facts that `S.Enters` hands on from facts
    g with LaidJ before S.
  `L.LayWJ pp base`: the same in wide facts (`A.ZkW`: Cb/Req1/LdReqRefLayWide.lean).
  `Spec.ldReqRefLayJ_after`: `L.LaidJ base g → L.segs.AfterJ base g`.
  `Spec.ldReqRefLayJ_of`: `L.Laid base g → L.LaidJ base g`: nothing that stands is lost.
  `Spec.ldReqRefLayJ_segs`: for pp the characteristic of E (`[CharP E pp]`):
    `L.OK pp → L.LayJ pp base → L.segs.ZkJ base`. `Spec.ldReqRefLayJ_wide`:
    `L.LayWJ pp base → L.LayJ pp base`.
  `Spec.ldReqRefLayJ`: for pp the characteristic of E (`[CharP E pp]`): `r.ZkS` of the reference
    request from: `L.OK pp`, `T.OK pp`, the final batching's conditions; `L.LayJ` at the facts fresh
    behind the first sendings; the last segment's `A.ZkAt` at the facts handed on from facts with
    `LaidJ`; such a fact that the last segment's moves hand on as the wide fact of the final
    batching's own masks, in a reading that holds what the batching reads.

Limits: this file says nothing on whether both parts of a pair can be had at one wide reading at a
segment's entry.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdReqRefLayWide
import Cb.Req1.LdReqSProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

theorem MaskFact.jcl_mono {W : Type} {X X' : MaskFact W → Prop} (h : ∀ f, X f → X' f) :
    ∀ f, MaskFact.JCl X f → MaskFact.JCl X' f := by
  intro f hf
  induction hf with
  | base f hx => exact .base f (h f hx)
  | join Kc kc M₁ M₂ put₁ put₂ _ _ i1 i2 => exact .join Kc kc M₁ M₂ put₁ put₂ i1 i2
  | conseq f Kc' g put' hg _ ih => exact .conseq f Kc' g put' hg ih
  | equiv f Mk' e _ ih => exact .equiv f Mk' e ih

namespace LdRefL
variable {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} {a : LdStage E Kc}

/-- Laid at the end of the list, the set closed at each stage between segments. -/
def LaidJ (base : MaskFact a.J.W → Prop) :
    {b : LdStage E Kc} → LdRefL E Kc I a b → MaskFact b.J.W → Prop
  | _, .nil => MaskFact.JCl base
  | _, .snoc L S => MaskFact.JCl fun g => S.New g ∨ ∃ g', L.LaidJ base g' ∧ S.Carries g' g

def LayJ (pp : ℕ) (base : MaskFact a.J.W → Prop) : {b : LdStage E Kc} → LdRefL E Kc I a b → Prop
  | _, .nil => True
  | _, .snoc L S => L.LayJ pp base ∧ S.A.ZkAt pp fun f => ∃ g, L.LaidJ base g ∧ S.Enters g f

def LayWJ (pp : ℕ) (base : MaskFact a.J.W → Prop) : {b : LdStage E Kc} → LdRefL E Kc I a b → Prop
  | _, .nil => True
  | _, .snoc L S => L.LayWJ pp base ∧ S.A.ZkW pp fun f => ∃ g, L.LaidJ base g ∧ S.Enters g f

end LdRefL

namespace Spec

def ldReqRefLayJ_after : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E) (a b : LdStage E Kc) (L : LdRefL E Kc I a b)
      (base : MaskFact a.J.W → Prop) (g : MaskFact b.J.W),
    L.LaidJ base g → L.segs.AfterJ base g

def ldReqRefLayJ_of : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E) (a b : LdStage E Kc) (L : LdRefL E Kc I a b)
      (base : MaskFact a.J.W → Prop) (g : MaskFact b.J.W),
    L.Laid base g → L.LaidJ base g

def ldReqRefLayJ_segs : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (pp : ℕ) [CharP E pp] (I : LdRefIx E) (a b : LdStage E Kc)
      (L : LdRefL E Kc I a b) (base : MaskFact a.J.W → Prop),
    L.OK pp → L.LayJ pp base → L.segs.ZkJ base

def ldReqRefLayJ_wide : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E) (a b : LdStage E Kc) (L : LdRefL E Kc I a b)
      (pp : ℕ) (base : MaskFact a.J.W → Prop),
    L.LayWJ pp base → L.LayJ pp base

/-- What honest-verifier zero knowledge asks of the reference request (`ZkS`), beside its
hypotheses, with joins. -/
def ldReqRefLayJ : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (pp : ℕ) [CharP E pp]
      (R : LdORE F E Kc) (a : LdStage E Kc) (first : LdSendD a) (a₁ : LdStage E Kc)
      (more : LdProg first.tgt a₁) (hm : more.All fun t => t = .send ∨ t = .step) (b : LdStage E Kc)
      (L : LdRefL E Kc R.ix a₁ b) (T : LdRefT R b) (Rd : R.S.Ent → Prop) (Rr : R.S.O → Prop),
    L.OK pp → T.OK pp → 2 ≤ R.n → R.Z.OK → R.Tie → R.X.Own → (∀ n, R.Rd n → Rd n) →
    L.LayJ pp (ldReqRef R first a₁ more hm b L T).base₀ →
    T.A.ZkAt pp (fun f =>
      ∃ g,
        L.LaidJ (ldReqRef R first a₁ more hm b L T).base₀ g ∧
        ∀ Y : MaskFact b.J.W → Prop, Y g → T.entry.After Y f) →
    (∃ g,
      L.LaidJ (ldReqRef R first a₁ more hm b L T).base₀ g ∧
      ∀ Y : MaskFact b.J.W → Prop, Y g →
        T.tail.After Y
          (R.X.src.wideFact Rd Rr (R.X.atOwn R.X.wAt) R.X.mask.Mk fun M => R.X.atVal R.X.wAt M)) →
    (ldReqRef R first a₁ more hm b L T).ZkS

end Spec

theorem ldReqRefLayJ_after : Spec.ldReqRefLayJ_after := by
  intro E Kc _ _ I a b L base
  induction L with
  | nil => intro g h; simpa only [LdRefL.LaidJ, LdRefL.segs, LdSegs.AfterJ] using h
  | snoc L S ih =>
      intro g h
      simp only [LdRefL.LaidJ] at h
      simp only [LdRefL.segs, LdSegs.AfterJ]
      refine MaskFact.jcl_mono (fun g hg => ?_) g h
      rcases hg with hg | ⟨g', hg', hc⟩
      · exact ldReqRefLay_new E Kc _ _ S g hg _
      · exact hc _ (ih g' hg')

theorem ldReqRefLayJ_of : Spec.ldReqRefLayJ_of := by
  intro E Kc _ _ I a b L base
  induction L with
  | nil => intro g h; simp only [LdRefL.Laid] at h; simp only [LdRefL.LaidJ]; exact .base g h
  | snoc L S ih =>
      intro g h
      simp only [LdRefL.Laid] at h
      simp only [LdRefL.LaidJ]
      rcases h with h | ⟨g', hg', hc⟩
      · exact .base g (Or.inl h)
      · exact .base g (Or.inr ⟨g', ih g' hg', hc⟩)

theorem ldReqRefLayJ_segs : Spec.ldReqRefLayJ_segs := by
  intro E Kc _ _ pp _ I a b L base
  induction L with
  | nil => intro _ _; simp only [LdRefL.segs, LdSegs.ZkJ]
  | snoc L S ih =>
      intro hO hZ
      rw [LdRefL.OK] at hO
      simp only [LdRefL.LayJ] at hZ
      simp only [LdRefL.segs, LdSegs.ZkJ]
      refine ⟨ih hO.1 hZ.1, ldReqRefK_zk E Kc _ _ _ (S.K.seg S.l S.Qc) S.entry rfl _ ?_⟩
      exact ldSegWholeZk_one E Kc _ S.K.R.c1 _ S.K.kinds S.l S.Qc _
        (ldReqRefZkP_body E Kc pp _ S.A S.K.St₁ S.K.fz S.K.Az _ hO.2.body
          (ldReqRefLay_mono E Kc _ S.A pp _ _
            (fun f ⟨g, hg, he⟩ => he _ (ldReqRefLayJ_after E Kc _ _ _ L base g hg)) hZ.2))

theorem ldReqRefLayJ_wide : Spec.ldReqRefLayJ_wide := by
  intro E Kc _ _ I a b L pp base
  induction L with
  | nil => intro _; simp only [LdRefL.LayJ]
  | snoc L S ih =>
      intro h
      simp only [LdRefL.LayWJ] at h
      simp only [LdRefL.LayJ]
      exact ⟨ih h.1,
        ldReqRefLayW_zk E Kc I S.A pp _ (ldReqRefLayW_closed E Kc _ _ S.entry (L.LaidJ base)) h.2⟩

theorem ldReqRefLayJ : Spec.ldReqRefLayJ := by
  intro F E Kc _ _ _ _ _ pp _ R a first a₁ more hm b L T Rd Rr hL hT hn hZ hTie
    hO hRd zL zT ⟨g, hg, hB⟩
  refine ⟨ldReqRefLayJ_segs E Kc pp _ _ _ L _ hL zL, ?_⟩
  refine ldReqLast_zk E Kc _ _ _ _
    ((ldProg_app_hyp E Kc _ _ _ T.tail R.lastP).2
      ⟨ldReqRef_tail F E Kc pp R b T hT, ldORE_hyp F E Kc R hn hZ hTie⟩)
    ((ldProg_app_zk E Kc _ _ _ T.tail R.lastP _).2
      ⟨?_, ldORE_zk F E Kc R _ hn hZ hO
          (segTen_in R.X _ Rd Rr hO hRd (hB _ (ldReqRefLayJ_after E Kc _ _ _ L _ g hg)))⟩)
  unfold LdRefT.tail
  refine (LdProg.zk_snoc _ _ _).2
    ⟨(ldProg_app_zk E Kc _ _ _ _ _ _).2
        ⟨(LdProg.zk_snoc _ _ _).2 ⟨(LdProg.zk_nil _ _).2 trivial, trivial⟩, ?_⟩,
      trivial⟩
  rw [LdProg.after_snoc, LdProg.after_nil]
  exact ldReqRefZkP_body E Kc pp _ T.A T.St₁ T.fz T.Az _ hT.body
    (ldReqRefLay_mono E Kc _ T.A pp _ _
      (fun f ⟨g, hg, he⟩ => he _ (ldReqRefLayJ_after E Kc _ _ _ L _ g hg)) zT)

end Cb
