-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinClosePlanSProofs.lean: the proofs of the statements of Cb/Ld/LdLinClosePlanS.lean (the
plan with two splittings).
Named tools: `Grp.onMem_ne` (a form on one member vanishes at the entries of the others),
`Grp.onMem_self` (at an entry of that member it is the form), `holds_toSub` (a row on a group, read
among the kept oracle messages, holds exactly if the row holds, if all members are kept),
`sideG_id_src`, `side_stepF` (a step that only maps the explicit part has the budgets' half).
Nothing is defined here that a statement reads.

Main names (statements and hypotheses: Cb/Ld/LdLinClosePlanS.lean):
  `ldLinPs_says`: what the unsplit stage (`p.x`) says.
  `ldLinPs_hyp`: the hypotheses of the front's moves.
  `ldLinPs_sd`: the budgets' half of every step of the front.
  `ldLinPs_zk`: see its statement in Cb/Ld/LdLinClosePlanS.lean.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinClosePlanS
import Cb.Ld.LdFrontProofs
import Cb.Ld.LdLinCloseDemandVProofs
import Cb.Ld.LdLinClosePlanRowsAt

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

theorem Grp.onMem_ne {E : Type} [Field E] {S : Sig E} (G : Grp S) {St : Type} (o : S.O)
    (h : G.mem o) (sl : Slf E St (S.om o).C.J) (st : St) (n : G.C.J) (hn : n.1.1 ≠ o) :
    G.onMem o h sl st n = 0 :=
  dif_neg fun e => hn (congrArg Subtype.val e)

theorem Grp.onMem_self {E : Type} [Field E] {S : Sig E} (G : Grp S) {St : Type} (o : S.O)
    (h h' : G.mem o) (sl : Slf E St (S.om o).C.J) (st : St) (j : (S.om o).C.J) :
    G.onMem o h sl st ⟨⟨o, h'⟩, j⟩ = sl st j :=
  dif_pos rfl

theorem holds_toSub {E : Type} [Field E] {S : Sig E} (G : Grp S)
    (kp : S.O → Prop) [DecidablePred kp] {St : Type} (sl : Slf E St G.C.J)
    (x : E × St) (m : S.Msg) (h : ∀ o, G.mem o → kp o) :
    (sl.toSub kp).Holds x ((G.sub kp).msg (S.res (T := OMsg.Msg) kp m)) ↔ sl.Holds x (G.msg m) := by
  have e := ldPeel_toSub E S G kp St sl x.2 m h
  exact ⟨fun h1 => e.symm.trans h1, fun h1 => e.trans h1⟩

theorem sideG_id_src {E : Type} (S : Sig E) (E₀ : ExtSpec)
    (inst : DecidableEq (E₀.prod S.ext).Pos) (U : Finset (E₀.prod S.ext).Pos) :
    @Finset.biUnion _ _ inst U (sideG S (ExtMap.id E₀)).src = U := by
  ext q
  constructor
  · intro h
    obtain ⟨u, hu, hq⟩ := (ldDemand_mem_biUnion _).1 h
    rcases u with p | r
    · obtain ⟨p', hp', hq'⟩ := (ldDemand_mem_biUnion _).1 hq
      obtain rfl := Finset.mem_singleton.1 hp'
      obtain rfl := Finset.mem_singleton.1 hq'
      exact hu
    · obtain rfl := Finset.mem_singleton.1 hq
      exact hu
  · intro h
    refine (ldDemand_mem_biUnion _).2 ⟨q, h, ?_⟩
    rcases q with p | r
    · exact (ldDemand_mem_biUnion _).2 ⟨p, Finset.mem_singleton_self _, Finset.mem_singleton_self _⟩
    · exact Finset.mem_singleton_self _

theorem side_stepF {E : Type} (S : Sig E) {St St' Wp : Type} {E₀ : ExtSpec} (f : St → St')
    (q : Finset (E₀.prod S.ext).Pos → Prop) :
    IOR.SideC (IOR.pure (sideF S f) (sideG S (ExtMap.id E₀)))
      (IOR.Honest.pure (sideF S f) (sideG S (ExtMap.id E₀))
        (sideM S f fun (_ : St) (w : S.Msg × Wp) => w.2))
      (IOR.Nums.pure Unit (sideF S f) (sideG S (ExtMap.id E₀))).bud q q :=
  sideC_of_side _ _ _ _ _ _ _ _ _ _ _ ⟨fun _ _ => rfl, fun _ _ => rfl,
    fun ρ U hU => ⟨trivial, by rw [need_pure, sideG_id_src]; exact hU⟩⟩

section
variable (E ι κ J Y : Type) [Field E] [Fintype E] [Fintype ι] [Fintype κ] [Fintype J] [Fintype Y]

omit [Fintype E] [Fintype ι] in
theorem ldLinPs_says : Spec.ldLinPs_says E ι κ J Y := by
  intro C p hr
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
      splitIn p.dO p.dW (0, (st, st)) m ↔ C.D.Dot (C.g st.1.1.1.1) (C.oM m) st.1.1.2 (C.wM m) := by
    intro st m
    have e1 : p.dO.val st (p.GcO.msg m) = ∑ y, C.g st.1.1.1.1 y * C.oM m y := by
      show (p.GcO.onMem C.nO p.hcO _).val st (p.GcO.msg m) = _
      rw [ldForm_onMem, ldForm_push]
      rfl
    have e2 : p.dW.val st (p.GcW.msg m) = -Alg.mle (C.wM m) (C.D.pt st.1.1.2) := by
      show (p.GcW.onMem C.nW p.hcW _).val st (p.GcW.msg m) = _
      rw [ldForm_onMem, ldForm_push]
      unfold Alg.mle
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun c _ => neg_mul _ _
    show p.dO.val st (p.GcO.msg m) + p.dW.val st (p.GcW.msg m) = 0 ↔ _
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
      p.ev.Holds (C.τ st.1.1.1.1, st) (p.GcW.msg m) ↔
      C.D.Eval (C.ψ st.1.1.1.1) (C.wM m) (C.rest st.1.1.1.1 (C.aM m)) (C.τ st.1.1.1.1) := by
    intro st m
    have e : p.ev.val st (p.GcW.msg m) =
        Alg.mle (C.wM m) (C.D.pt (C.ψ st.1.1.1.1)) + C.rest st.1.1.1.1 (C.aM m) := by
      show (Slf.plus (p.GcW.onMem C.nW p.hcW _) fun st => p.restG st.1.1.1.1).val st _ = _
      rw [Slf.plus_val, ldForm_onMem, ldForm_push, ← hr]
      rfl
    exact ⟨fun h => e.symm.trans h, fun h => e.trans h⟩
  refine ⟨fun st y m wp h hab => ?_, fun st y m wp _ h => ?_, fun st y hon => hon⟩
  · exact ⟨(hF st m).2 h.2.2.1, (hD st m).2 h.2.2.2.2, (hRC st m).2 ⟨h.1, h.2.1⟩,
      (hEv st m).2 h.2.2.2.1, hab⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := h
    obtain ⟨a1, a2⟩ := (hRC st m).1 h3
    exact ⟨⟨a1, a2, (hF st m).1 h1, (hEv st m).1 h4, (hD st m).1 h2⟩, h5⟩

end

section Own
variable {E ι κ J Y : Type} [Field E] [Fintype Y] {C : LdLinC E ι κ J Y} (p : LdLinPs C)

/-- the hypotheses of the first splitting -/
theorem LdLinPs.hyp₀ [Fintype E] (hP : p.Plain) {St₀ : Type}
    (A₀ : IOR.Rels Unit St₀ C.E₀ (C.S.Msg × C.Wpa)) :
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

/-- the hypotheses of the second splitting -/
theorem LdLinPs.hyp₁ [Fintype E] (hP : p.Plain) {St₀ : Type}
    (A₀ : IOR.Rels Unit St₀ C.E₀ (C.S.Msg × C.Wpa)) :
    (Front.splD p.GcO p.GcW p.k₁ C.St6 C.St6 p.dO p.dW St₀ A₀ p.Rs₁ inferInstance).Hyp := by
  refine ⟨fun s => p.GcO.onMem_ne _ _ _ s _ hP.ne₁O, fun s => p.GcW.onMem_ne _ _ _ s _ hP.ne₁W,
    fun s n hn => ?_, fun s n hn => ?_, hP.rs₁K⟩
  · obtain ⟨⟨o, h⟩, j⟩ := n
    by_cases e : o = C.nO
    · subst e
      refine (p.GcO.onMem_self _ _ h _ s j).trans (Slf.push_zero _ _ s j fun i hi => hn ?_)
      subst hi
      exact hP.rs₁O _
    · exact p.GcO.onMem_ne _ _ _ s _ e
  · obtain ⟨⟨o, h⟩, j⟩ := n
    by_cases e : o = C.nW
    · subst e
      refine (p.GcW.onMem_self _ _ h _ s j).trans (Slf.push_zero _ _ s j fun i hi => hn ?_)
      subst hi
      exact hP.rs₁W _
    · exact p.GcW.onMem_ne _ _ _ s _ e

end Own

section
variable (E ι κ J Y : Type) [Field E] [Fintype E] [Fintype ι] [Fintype κ] [Fintype J] [Fintype Y]

omit [Fintype ι] in
theorem ldLinPs_hyp : Spec.ldLinPs_hyp E ι κ J Y := by
  intro C p St' B' fa hP hK hA
  -- the rows of the four tests, one by one
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
  have i3 : ∀ (c : E × C.St6) (m : C.S.Msg),
      Slf.All p.r₃ (oneClaim c)
        (p.G₃.msg (p.S₁.res (T := OMsg.Msg) p.kp₂ (C.S.res (T := OMsg.Msg) p.kp₁ m))) ↔
      (p.dO.addAt 1 p.k₁.e₁).Holds c (p.GcO.msg m) :=
    fun c m =>
      have e := (holds_toSub (p.GcO.sub p.kp₁) p.kp₂ ((p.dO.addAt 1 p.k₁.e₁).toSub p.kp₁) c
          (C.S.res (T := OMsg.Msg) p.kp₁ m) hK.c₂).trans
        (holds_toSub p.GcO p.kp₁ (p.dO.addAt 1 p.k₁.e₁) c m hK.c₁)
      ⟨fun h => e.1 (h ()), fun h _ => e.2 h⟩
  have t3 : ∀ {St : Type} (sl : Slf E St p.GcW.C.J) (c : E × St) (m : C.S.Msg),
      (((sl.toSub p.kp₁).toSub p.kp₂).toSub p.kp₃).Holds c
        (p.G₄.msg (p.S₂.res (T := OMsg.Msg) p.kp₃
            (p.S₁.res (T := OMsg.Msg) p.kp₂ (C.S.res (T := OMsg.Msg) p.kp₁ m)))) ↔
      sl.Holds c (p.GcW.msg m) :=
    fun sl c m =>
      (holds_toSub ((p.GcW.sub p.kp₁).sub p.kp₂) p.kp₃ ((sl.toSub p.kp₁).toSub p.kp₂) c
          (p.S₁.res (T := OMsg.Msg) p.kp₂ (C.S.res (T := OMsg.Msg) p.kp₁ m)) hK.w₃).trans
        ((holds_toSub (p.GcW.sub p.kp₁) p.kp₂ (sl.toSub p.kp₁) c
            (C.S.res (T := OMsg.Msg) p.kp₁ m) hK.w₂).trans
          (holds_toSub p.GcW p.kp₁ sl c m hK.w₁))
  have i4 : ∀ (c c' : E × C.St6) (m : C.S.Msg),
      Slf.All p.r₄ (Sum.elim (fun _ => c.1) fun _ => c'.1, Sum.elim (fun _ => c.2) fun _ => c'.2)
        (p.G₄.msg (p.S₂.res (T := OMsg.Msg) p.kp₃
            (p.S₁.res (T := OMsg.Msg) p.kp₂ (C.S.res (T := OMsg.Msg) p.kp₁ m)))) ↔
      p.ev.Holds c (p.GcW.msg m) ∧ (p.dW.addAt (-1) p.k₁.e₂).Holds c' (p.GcW.msg m) :=
    fun c c' m => ⟨fun h => ⟨(t3 p.ev c m).1 (h (.inl ())), (t3 (p.dW.addAt (-1) p.k₁.e₂) c' m).1 (h (.inr ()))⟩, fun h b => by
      rcases b with b | b
      · exact (t3 p.ev c m).2 h.1
      · exact (t3 (p.dW.addAt (-1) p.k₁.e₂) c' m).2 h.2⟩
  suffices key : ((((True ∧
            (Front.splD p.GO p.GU p.k₀ C.Sh6 C.Sh6 p.fO p.fU _ (claimRels (splitIn p.dO p.dW) p.Ar)
              p.Rs₀ inferInstance).Hyp) ∧
          (ldStepF C.S (claimRels (splitOut p.k₀ p.fO p.fU) (claimRels (splitIn p.dO p.dW) p.Ar))
            (claimRels (splitIn p.dO p.dW) (claimRels (splitOut p.k₀ p.fO p.fU) p.Ar))
            LdLinPs.swp).Hyp) ∧
        (Front.splD p.GcO p.GcW p.k₁ C.St6 C.St6 p.dO p.dW _
          (claimRels (splitOut p.k₀ p.fO p.fU) p.Ar) p.Rs₁ inferInstance).Hyp) ∧
      (ldStepF C.S (claimRels (splitOut p.k₁ p.dO p.dW) (claimRels (splitOut p.k₀ p.fO p.fU) p.Ar))
        (p.base B') (LdLinPs.fin fa)).Hyp) by
    unfold LdLinPs.front LdLinPs.stepOf
    rw [Front.prog_step]
    unfold LdLinPs.f₃
    rw [Front.prog_split]
    unfold LdLinPs.f₂ LdLinPs.stepOf
    rw [Front.prog_step]
    unfold LdLinPs.f₁
    rw [Front.prog_split, Front.prog_nil]
    simpa only [LdProg.Hyp] using key
  refine ⟨⟨⟨⟨trivial, p.hyp₀ hP _⟩, ?_⟩, p.hyp₁ hP _⟩, ?_⟩
  · exact ldStepF_hyp C.S _ _ _ (fun s y w h => ⟨h.2.1, h.1, h.2.2⟩) (fun _ _ h => h)
      (fun _ => rfl) fun s y w _ h => ⟨h.2.1, h.1, h.2.2⟩
  · refine ldStepF_hyp C.S _ _ _ (fun s y w h => ?_) (fun s y h => hA.on _ y h)
      (fun w => hA.core w.1 w.2) fun s y w hon h => ?_
    · obtain ⟨⟨d1, d2⟩, ⟨f1, f2⟩, hrc, hev, hab⟩ := h
      exact ⟨(i1 _ _ _).2 ⟨hrc, f2⟩, (i2 _ _).2 f1, (i3 _ _).2 d1,
        (i4 _ _ _).2 ⟨hev, d2⟩, hA.fwd _ y w.1 w.2 hab⟩
    · obtain ⟨h1, h2, h3, h4, h5⟩ := h
      obtain ⟨hrc, f2⟩ := (i1 _ _ _).1 h1
      obtain ⟨hev, d2⟩ := (i4 _ _ _).1 h4
      exact ⟨⟨(i3 _ _).1 h3, d2⟩, ⟨(i2 _ _).1 h2, f2⟩, hrc, hev, hA.bwd _ y w.1 w.2 hon h5⟩

omit [Fintype ι] [Fintype E] in
theorem ldLinPs_sd : Spec.ldLinPs_sd E ι κ J Y := by
  intro C p St' B' fa q
  unfold LdLinPs.front LdLinPs.stepOf
  rw [Front.sd_step]
  refine ⟨?_, side_stepF C.S _ q⟩
  unfold LdLinPs.f₃
  rw [Front.sd_split]
  unfold LdLinPs.f₂ LdLinPs.stepOf
  rw [Front.sd_step]
  refine ⟨?_, side_stepF C.S _ q⟩
  unfold LdLinPs.f₁
  rw [Front.sd_split, Front.Sd]
  trivial

omit [Fintype ι] in
theorem ldLinPs_zk : Spec.ldLinPs_zk E ι κ J Y := by
  intro C p St' B' fa Rd Rr bs hP hne h0 h1 b0 b1
  unfold LdLinPs.front LdLinPs.stepOf
  rw [Front.zkOK_step]
  unfold LdLinPs.f₃
  rw [Front.zkOK_split]
  refine ⟨?_, ?_, h1, b1⟩
  · unfold LdLinPs.f₂ LdLinPs.stepOf
    rw [Front.zkOK_step]
    unfold LdLinPs.f₁
    rw [Front.zkOK_split]
    refine ⟨by rw [Front.ZkOK]; trivial, by rw [Front.Quiet]; trivial, h0, b0⟩
  · unfold LdLinPs.f₂ LdLinPs.stepOf
    rw [Front.quiet_step]
    refine ⟨?_, fun _ _ => rfl, fun _ _ _ => rfl⟩
    unfold LdLinPs.f₁
    rw [Front.quiet_split]
    refine ⟨by rw [Front.Quiet]; trivial, h0, fun s n hn => ?_, hne⟩
    refine p.GO.onMem_ne _ _ _ s n fun e => hP.ne₁O ?_
    have e2 : (p.GO.ent n).1 = p.k₁.o := congrArg Sigma.fst hn
    exact e2.symm.trans e

end
end Cb
