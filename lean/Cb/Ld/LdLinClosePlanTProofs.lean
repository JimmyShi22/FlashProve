-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinClosePlanTProofs.lean: the proofs of the statements of Cb/Ld/LdLinClosePlanT.lean (the
plan with two splittings in the order of a batch). Named tools: `LdLinPt.hyp₀`, `LdLinPt.hyp₁` (the
hypotheses of the two splittings). Nothing is defined here that a statement reads.

Main names (statements and hypotheses: Cb/Ld/LdLinClosePlanT.lean):
  `ldLinPt_says`: what the stage at which the shared front starts says.
  `ldLinPt_hyp`: the hypotheses of the moves of both fronts.
  `ldLinPt_sd`: `Sd` of both fronts.
  `ldLinPt_zk`: see its statement in Cb/Ld/LdLinClosePlanT.lean.

Limits: what the head of Cb/Ld/LdLinClosePlanT.lean lists as not said is not said here either.
-/
import Cb.Ld.LdLinClosePlanT

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section Own
variable {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype Y] {C : LdLinC E ι κ J Y} (p : LdLinPt C)

theorem LdLinPt.hyp₀ (hP : p.Plain) {St₀ : Type} (A₀ : IOR.Rels Unit St₀ C.E₀ (C.S.Msg × C.Wpa)) :
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

theorem LdLinPt.hyp₁ (hP : p.Plain) {St₀ : Type} (A₀ : IOR.Rels Unit St₀ C.E₀ (p.S₂.Msg × C.Wpa)) :
    (Front.splD p.GcO p.GcW p.k₁ C.St6 C.St6 p.dO p.dW St₀ A₀ p.Rs₁ inferInstance).Hyp := by
  refine ⟨fun s => p.GcO.onMem_ne _ _ _ s _ hP.ne₁O, fun s => p.GcW.onMem_ne _ _ _ s _ hP.ne₁W,
    fun s n hn => ?_, fun s n hn => ?_, hP.rs₁K⟩
  · obtain ⟨⟨o, h⟩, j⟩ := n
    by_cases e : o = p.nO₂
    · subst e
      refine (p.GcO.onMem_self _ _ h _ s j).trans (Slf.push_zero _ _ s j fun i hi => hn ?_)
      subst hi
      exact hP.rs₁O _
    · exact p.GcO.onMem_ne _ _ _ s _ e
  · obtain ⟨⟨o, h⟩, j⟩ := n
    by_cases e : o = p.nW₂
    · subst e
      refine (p.GcW.onMem_self _ _ h _ s j).trans (Slf.push_zero _ _ s j fun i hi => hn ?_)
      subst hi
      exact hP.rs₁W _
    · exact p.GcW.onMem_ne _ _ _ s _ e

end Own

section
variable (E ι κ J Y : Type) [Field E] [Fintype E] [Fintype ι] [Fintype κ] [Fintype J] [Fintype Y]

omit [Fintype E] [Fintype ι] in
theorem ldLinPt_says : Spec.ldLinPt_says E ι κ J Y := by
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
  have hD : ∀ (st : C.St6) (m : C.S.Msg),
      splitIn p.dO p.dW (0, (st, st)) (p.left₂ m) ↔
      C.D.Dot (C.g st.1.1.1.1) (C.oM m) st.1.1.2 (C.wM m) := by
    intro st m
    have e1 : p.dO.val st (p.GcO.msg (p.left₂ m)) = ∑ y, C.g st.1.1.1.1 y * C.oM m y := by
      show (p.GcO.onMem p.nO₂ p.hcO _).val st (p.GcO.msg (p.left₂ m)) = _
      rw [ldForm_onMem, ldForm_push]
      rfl
    have e2 : p.dW.val st (p.GcW.msg (p.left₂ m)) = -Alg.mle (C.wM m) (C.D.pt st.1.1.2) := by
      show (p.GcW.onMem p.nW₂ p.hcW _).val st (p.GcW.msg (p.left₂ m)) = _
      rw [ldForm_onMem, ldForm_push]
      unfold Alg.mle
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun c _ => neg_mul _ _
    show p.dO.val st (p.GcO.msg (p.left₂ m)) + p.dW.val st (p.GcW.msg (p.left₂ m)) = 0 ↔ _
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
  have hEv : ∀ (st : C.St6) (m : C.S.Msg),
      p.ev.Holds (C.τ st.1.1.1.1, st) (p.GcW.msg (p.left₂ m)) ↔
      C.D.Eval (C.ψ st.1.1.1.1) (C.wM m) (C.rest st.1.1.1.1 (C.aM m)) (C.τ st.1.1.1.1) := by
    intro st m
    have e : p.ev.val st (p.GcW.msg (p.left₂ m)) =
        Alg.mle (C.wM m) (C.D.pt (C.ψ st.1.1.1.1)) + C.rest st.1.1.1.1 (C.aM m) := by
      show (Slf.plus (p.GcW.onMem p.nW₂ p.hcW _) fun st => p.restG st.1.1.1.1).val st _ = _
      rw [Slf.plus_val, ldForm_onMem, ldForm_push, ← hr]
      rfl
    exact ⟨fun h => e.symm.trans h, fun h => e.trans h⟩
  refine ⟨fun st y m wp h hab => ?_, fun st y m wp hon h => ?_, fun st y hon => hA.on _ y hon⟩
  · exact ⟨(hF st m).2 h.2.2.1, (hRC st m).2 ⟨h.1, h.2.1⟩, (hD st m).2 h.2.2.2.2,
      (hEv st m).2 h.2.2.2.1, hA.fwd _ y m wp hab⟩
  · obtain ⟨h1, h3, h2, h4, h5⟩ := h
    obtain ⟨a1, a2⟩ := (hRC st m).1 h3
    exact ⟨⟨a1, a2, (hF st m).1 h1, (hEv st m).1 h4, (hD st m).1 h2⟩, hA.bwd _ y m wp hon h5⟩

omit [Fintype ι] in
theorem ldLinPt_hyp : Spec.ldLinPt_hyp E ι κ J Y := by
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
  have i4 : ∀ (c c' : E × C.St6) (m : p.S₂.Msg),
      Slf.All p.r₄ (Sum.elim (fun _ => c.1) fun _ => c'.1, Sum.elim (fun _ => c.2) fun _ => c'.2)
        (p.G₄.msg (p.S₂.res (T := OMsg.Msg) p.kp₃ m)) ↔
      p.ev.Holds c (p.GcW.msg m) ∧ (p.dW.addAt (-1) p.k₁.e₂).Holds c' (p.GcW.msg m) :=
    fun c c' m => ⟨fun h => ⟨(holds_toSub p.GcW p.kp₃ p.ev c m hK.w₃).1 (h (.inl ())), (holds_toSub p.GcW p.kp₃ (p.dW.addAt (-1) p.k₁.e₂) c' m hK.w₃).1 (h (.inr ()))⟩, fun h b => by
      rcases b with b | b
      · exact (holds_toSub p.GcW p.kp₃ p.ev c m hK.w₃).2 h.1
      · exact (holds_toSub p.GcW p.kp₃ (p.dW.addAt (-1) p.k₁.e₂) c' m hK.w₃).2 h.2⟩
  constructor
  · suffices key : ((True ∧
      (Front.splD p.GO p.GU p.k₀ C.Sh6 C.Sh6 p.fO p.fU _ (p.Ar₁ B') p.Rs₀ inferInstance).Hyp) ∧
        (ldStepF C.S (claimRels (splitOut p.k₀ p.fO p.fU) (p.Ar₁ B')) (p.base₁ B') fun s =>
          ((Sum.elim s.2.1.1 fun _ => s.1.2.1, Sum.elim s.2.1.2 fun _ => s.1.2.2),
            (oneClaim s.1.1, s.2.2))).Hyp) by
      unfold LdLinPt.front₁ LdLinPt.stepOn
      rw [Front.prog_step, Front.prog_split, Front.prog_nil]
      simpa only [LdProg.Hyp] using key
    refine ⟨⟨trivial, p.hyp₀ hP _⟩,
      ldStepF_hyp C.S _ _ _ (fun s y w h => ?_) (fun _ _ h => h) (fun _ => rfl) fun s y w _ h => ?_⟩
    · obtain ⟨⟨f1, f2⟩, hrc, hx⟩ := h
      exact ⟨(i1 _ _ _).2 ⟨hrc, f2⟩, (i2 _ _).2 f1, hx⟩
    · obtain ⟨h1, h2, hx⟩ := h
      obtain ⟨hrc, f2⟩ := (i1 _ _ _).1 h1
      exact ⟨⟨(i2 _ _).1 h2, f2⟩, hrc, hx⟩
  · suffices key : ((True ∧
      (Front.splD p.GcO p.GcW p.k₁ C.St6 C.St6 p.dO p.dW _ (p.Ar₂ B') p.Rs₁ inferInstance).Hyp) ∧
        (ldStepF p.S₂ (claimRels (splitOut p.k₁ p.dO p.dW) (p.Ar₂ B')) (p.base₂ B') fun s =>
          (oneClaim s.1.1,
            ((Sum.elim (fun _ => s.2.1.1) fun _ => s.1.2.1,
                Sum.elim (fun _ => s.2.1.2) fun _ => s.1.2.2),
              s.2.2))).Hyp) by
      unfold LdLinPt.front₂ LdLinPt.stepOn
      rw [Front.prog_step, Front.prog_split, Front.prog_nil]
      simpa only [LdProg.Hyp] using key
    refine ⟨⟨trivial, p.hyp₁ hP _⟩,
      ldStepF_hyp p.S₂ _ _ _ (fun s y w h => ?_) (fun _ _ h => h)
        (fun _ => rfl) fun s y w _ h => ?_⟩
    · obtain ⟨⟨d1, d2⟩, hev, hx⟩ := h
      exact ⟨(all_one _ _ _).2 d1, (i4 _ _ _).2 ⟨hev, d2⟩, hx⟩
    · obtain ⟨h3, h4, hx⟩ := h
      obtain ⟨hev, d2⟩ := (i4 _ _ _).1 h4
      exact ⟨⟨(all_one _ _ _).1 h3, d2⟩, hev, hx⟩

omit [Fintype ι] [Fintype E] in
theorem ldLinPt_sd : Spec.ldLinPt_sd E ι κ J Y := by
  intro C p St' B' q₁ q₂
  constructor
  · unfold LdLinPt.front₁ LdLinPt.stepOn
    rw [Front.sd_step, Front.sd_split, Front.Sd]
    exact ⟨trivial, side_stepF C.S _ q₁⟩
  · unfold LdLinPt.front₂ LdLinPt.stepOn
    rw [Front.sd_step, Front.sd_split, Front.Sd]
    exact ⟨trivial, side_stepF p.S₂ _ q₂⟩

omit [Fintype ι] in
theorem ldLinPt_zk : Spec.ldLinPt_zk E ι κ J Y := by
  intro C p St' B'
  constructor
  · intro Rd Rr bs h0 b0
    unfold LdLinPt.front₁ LdLinPt.stepOn
    rw [Front.zkOK_step, Front.zkOK_split]
    exact ⟨by rw [Front.ZkOK]; trivial, by rw [Front.Quiet]; trivial, h0, b0⟩
  · intro Rd Rr bs h1 b1
    unfold LdLinPt.front₂ LdLinPt.stepOn
    rw [Front.zkOK_step, Front.zkOK_split]
    exact ⟨by rw [Front.ZkOK]; trivial, by rw [Front.Quiet]; trivial, h1, b1⟩

end
end Cb
