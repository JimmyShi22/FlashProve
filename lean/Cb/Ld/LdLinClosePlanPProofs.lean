-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinClosePlanPProofs.lean: the proofs of the statements of Cb/Ld/LdLinClosePlanP.lean (the
plan with the one shared splitting).
Named tools: `LdLinPp.hyp₀` (the hypotheses of the splitting, from `p.Plain`), `LdLinPp.rows₃` (the
instance's two rows). Nothing is defined here that a statement reads.

Main names (statements and hypotheses: Cb/Ld/LdLinClosePlanP.lean):
  `ldLinPp_says`: what the stage `p.x₁` says
  `ldLinPp_hyp`: the hypotheses of the front's moves, from `p.Plain` and `p.Kept`
  `ldLinPp_sd`: see its statement in Cb/Ld/LdLinClosePlanP.lean
  `ldLinPp_zk`: see its statement in Cb/Ld/LdLinClosePlanP.lean
-/
import Cb.Ld.LdLinClosePlanP

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section Own
variable {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype Y] {C : LdLinC E ι κ J Y} (p : LdLinPp C)

theorem LdLinPp.hyp₀ (hP : p.Plain) {St₀ : Type} (A₀ : IOR.Rels Unit St₀ C.E₀ (C.S.Msg × C.Wpa)) :
    (Front.splD p.GO p.GU p.k₀ C.Sh6 C.Sh6 p.fO p.fU St₀ A₀ p.Rs₀ inferInstance).Hyp := by
  refine ⟨fun s => p.GO.onMem_ne _ _ _ s _ hP.ne₀O, fun s => p.GU.onMem_ne _ _ _ s _ hP.ne₀U,
    fun s n hn => ?_, fun s n hn => ?_, hP.rs₀K⟩
  · obtain ⟨⟨o, h⟩, j⟩ := n
    by_cases e : o = C.nO
    · subst e
      refine (p.GO.onMem_self _ _ h _ s j).trans (Slf.push_zero _ _ s j fun i hi => hn ?_)
      subst hi
      exact hP.rs₀O _
    · exact p.GO.onMem_ne _ _ _ s _ e
  · obtain ⟨⟨o, h⟩, j⟩ := n
    by_cases e : o = C.nU
    · subst e
      refine (p.GU.onMem_self _ _ h _ s j).trans (Slf.push_zero _ _ s j fun i hi => hn ?_)
      subst hi
      exact hP.rs₀U _
    · exact p.GU.onMem_ne _ _ _ s _ e

end Own

section
variable (E ι κ J Y : Type) [Field E] [Fintype E] [Fintype ι] [Fintype κ] [Fintype J] [Fintype Y]

omit [Fintype E] [Fintype ι] [Fintype κ] [Fintype J] in
/-- Where `restG` is "rest" (`hr`), the instance's two rows, on what is left, hold if and only if
the evaluation and the inner product do. -/
theorem LdLinPp.rows₃ (C : LdLinC E ι κ J Y) (p : LdLinPp C) (st : C.St6) (m : C.S.Msg)
    (hr : p.restG.val st.1.1.1.1 (p.Gc.msg (p.left₂ m)) = C.rest st.1.1.1.1 (C.aM m)) :
    Slf.All p.r₃ (C.tg₂ st, fun _ => st) (p.Gc.msg (p.left₂ m)) ↔
    C.D.Eval (C.ψ st.1.1.1.1) (C.wM m) (C.rest st.1.1.1.1 (C.aM m)) (C.τ st.1.1.1.1) ∧
    C.D.Dot (C.g st.1.1.1.1) (C.oM m) st.1.1.2 (C.wM m) := by
  have hev : ∀ u : Unit, (p.r₃ (.inl u)).val st (p.Gc.msg (p.left₂ m)) =
      Alg.mle (C.wM m) (C.D.pt (C.ψ st.1.1.1.1)) + C.rest st.1.1.1.1 (C.aM m) := by
    intro u
    show (Slf.plus (p.Gc.onMem p.nW₂ p.hcW _) fun st => p.restG st.1.1.1.1).val st _ = _
    rw [Slf.plus_val, ldForm_onMem, ldForm_push, ← hr]
    rfl
  have hdot : ∀ u : Unit, (p.r₃ (.inr u)).val st (p.Gc.msg (p.left₂ m)) =
      (∑ y, C.g st.1.1.1.1 y * C.oM m y) - Alg.mle (C.wM m) (C.D.pt st.1.1.2) := by
    intro u
    show (Slf.sub (p.Gc.onMem p.nO₂ p.hcO _) (p.Gc.onMem p.nW₂ p.hcW _)).val st _ = _
    rw [ldForm_sub, ldForm_onMem, ldForm_onMem, ldForm_push, ldForm_push]
    rfl
  constructor
  · intro h
    exact ⟨(hev ()).symm.trans (h (.inl ())), sub_eq_zero.1 ((hdot ()).symm.trans (h (.inr ())))⟩
  · rintro ⟨h1, h2⟩ (u | u)
    · exact (hev u).trans h1
    · exact (hdot u).trans (sub_eq_zero.2 h2)

omit [Fintype E] [Fintype ι] in
theorem ldLinPp_says : Spec.ldLinPp_says E ι κ J Y := by
  intro C p St' B' fa hr hA
  have hF : ∀ (st : C.St6) (m : C.S.Msg),
      splitIn p.fO p.fU (0, (C.sh st, C.sh st)) m ↔
      C.D.FoldR st.2 st.1.1.2.2 (C.D.X.msg (C.uM m)) (C.oM m) := by
    intro st m
    have e1 : p.fO.val (C.sh st) (p.GO.msg m) = ∑ y, Alg.eqk st.2 (C.D.py y) * C.oM m y := by
      show (p.GO.onMem C.nO p.hO _).val (C.sh st) (p.GO.msg m) = _
      rw [ldForm_onMem, ldForm_push]
      rfl
    have e2 : p.fU.val (C.sh st) (p.GU.msg m) = -∑ y, Alg.eqk st.2 (C.D.py y) * C.D.omU (C.D.X.msg (C.uM m)) st.1.1.2.2 y := by
      show (p.GU.onMem C.nU p.hU _).val (C.sh st) (p.GU.msg m) = _
      rw [ldForm_onMem, ldForm_push, Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      unfold LdLinW.omU
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by
        show -(Alg.eqk st.2 (C.D.py y) * Alg.eqk st.1.1.2.2 j) *
            C.D.X.msg (C.uM m) (C.D.lay (y, j)) =
          -(Alg.eqk st.2 (C.D.py y) * (Alg.eqk st.1.1.2.2 j * C.D.X.msg (C.uM m) (C.D.lay (y, j))))
        ring
    show p.fO.val (C.sh st) (p.GO.msg m) + p.fU.val (C.sh st) (p.GU.msg m) = 0 ↔ _
    rw [e1, e2, ← sub_eq_add_neg, sub_eq_zero]
    exact Iff.rfl
  have hRC : ∀ (st : C.St6) (m : C.S.Msg),
      Slf.All p.rc (C.tgRC (C.sh st), fun _ => C.sh st) (p.GU.msg m) ↔
      C.D.X.RecRow st.1.1.1.2 st.1.1.2.1 (C.uM m) ∧
      ∀ i, C.D.X.G.mulVec (C.uM m) (st.1.2.1 i) = st.1.2.2 i := by
    intro st m
    have hrec : ∀ s, (p.rc (.inl s)).val (C.sh st) (p.GU.msg m) =
        C.D.X.Z.val st.1.1.1.2.1 (C.D.X.msg (C.uM m)) s := by
      intro s
      show (p.GU.onMem C.nU p.hU _).val (C.sh st) (p.GU.msg m) = _
      rw [ldForm_onMem, ldForm_push]
      rfl
    have hcol : ∀ i,
        (p.rc (.inr i)).val (C.sh st) (p.GU.msg m) = C.D.X.G.mulVec (C.uM m) (st.1.2.1 i) := by
      intro i
      show (p.GU.onMem C.nU p.hU _).val (C.sh st) (p.GU.msg m) = _
      rw [ldForm_onMem, ldForm_push]
      rfl
    constructor
    · intro h
      exact ⟨funext fun s => (hrec s).symm.trans (h (.inl s)),
        fun i => (hcol i).symm.trans (h (.inr i))⟩
    · rintro ⟨h1, h2⟩ (s | i)
      · exact (hrec s).trans (congrFun h1 s)
      · exact (hcol i).trans (h2 i)
  refine ⟨fun st y m wp h hab => ?_, fun st y m wp hon h => ?_, fun st y hon => hA.on _ y hon⟩
  · exact ⟨(hF st m).2 h.2.2.1,
      (hRC st m).2 ⟨h.1, h.2.1⟩,
      (LdLinPp.rows₃ E ι κ J Y C p st m (hr _ m)).2 ⟨h.2.2.2.1, h.2.2.2.2⟩,
      hA.fwd _ y m wp hab⟩
  · obtain ⟨h1, h3, h2, h5⟩ := h
    obtain ⟨a1, a2⟩ := (hRC st m).1 h3
    obtain ⟨b1, b2⟩ := (LdLinPp.rows₃ E ι κ J Y C p st m (hr _ m)).1 h2
    exact ⟨⟨a1, a2, (hF st m).1 h1, b1, b2⟩, hA.bwd _ y m wp hon h5⟩

omit [Fintype ι] in
theorem ldLinPp_hyp : Spec.ldLinPp_hyp E ι κ J Y := by
  intro C p St' B' hP hK
  have i1 : ∀ (a : (C.Brc → E) × (C.Brc → C.Sh6)) (c : E × C.Sh6) (u : p.GU.C.J → E),
      Slf.All p.r₁ (Sum.elim a.1 fun _ => c.1, Sum.elim a.2 fun _ => c.2) u ↔
      Slf.All p.rc a u ∧ (p.fU.addAt (-1) p.k₀.e₂).Holds c u :=
    fun a c u => ⟨fun h => ⟨fun b => h (.inl b), h (.inr ())⟩, fun h b => by
      rcases b with b | b
      · exact h.1 b
      · exact h.2⟩
  have i2 : ∀ (c : E × C.Sh6) (m : C.S.Msg),
      Slf.All p.r₂ (oneClaim c) (p.G₂.msg (C.S.res (T := OMsg.Msg) p.kp₁ m)) ↔
      (p.fO.addAt 1 p.k₀.e₁).Holds c (p.GO.msg m) :=
    fun c m =>
      ⟨fun h => (holds_toSub p.GO p.kp₁ (p.fO.addAt 1 p.k₀.e₁) c m hK.o₁).1 (h ()),
        fun h _ => (holds_toSub p.GO p.kp₁ (p.fO.addAt 1 p.k₀.e₁) c m hK.o₁).2 h⟩
  suffices key : ((True ∧
        (Front.splD p.GO p.GU p.k₀ C.Sh6 C.Sh6 p.fO p.fU _ (p.Ar₁ B') p.Rs₀ inferInstance).Hyp) ∧
      (ldStepF C.S (claimRels (splitOut p.k₀ p.fO p.fU) (p.Ar₁ B')) (p.base₁ B') fun s =>
        ((Sum.elim s.2.1.1 fun _ => s.1.2.1, Sum.elim s.2.1.2 fun _ => s.1.2.2),
          (oneClaim s.1.1, s.2.2))).Hyp) by
    unfold LdLinPp.front₁ LdLinPt.stepOn
    rw [Front.prog_step, Front.prog_split, Front.prog_nil]
    simpa only [LdProg.Hyp] using key
  refine ⟨⟨trivial, p.hyp₀ hP _⟩,
    ldStepF_hyp C.S _ _ _ (fun s y w h => ?_) (fun _ _ h => h) (fun _ => rfl) fun s y w _ h => ?_⟩
  · obtain ⟨⟨f1, f2⟩, hrc, hx⟩ := h
    exact ⟨(i1 _ _ _).2 ⟨hrc, f2⟩, (i2 _ _).2 f1, hx⟩
  · obtain ⟨h1, h2, hx⟩ := h
    obtain ⟨hrc, f2⟩ := (i1 _ _ _).1 h1
    exact ⟨⟨(i2 _ _).1 h2, f2⟩, hrc, hx⟩

omit [Fintype ι] [Fintype E] in
theorem ldLinPp_sd : Spec.ldLinPp_sd E ι κ J Y := by
  intro C p St' B' q₁
  unfold LdLinPp.front₁ LdLinPt.stepOn
  rw [Front.sd_step, Front.sd_split, Front.Sd]
  exact ⟨trivial, side_stepF C.S _ q₁⟩

omit [Fintype ι] in
theorem ldLinPp_zk : Spec.ldLinPp_zk E ι κ J Y := by
  intro C p St' B' Rd Rr bs h0 b0
  unfold LdLinPp.front₁ LdLinPt.stepOn
  rw [Front.zkOK_step, Front.zkOK_split]
  exact ⟨by rw [Front.ZkOK]; trivial, by rw [Front.Quiet]; trivial, h0, b0⟩

end
end Cb
