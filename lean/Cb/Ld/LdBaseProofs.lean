-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBaseProofs.lean: proofs of the statements of Cb/Ld/LdBase.lean.

Every "Spec.name" there is "theorem name" here. Nothing is assumed beyond what a statement names
(among them the laws of the code, transparency, the two counts). The mathematics is that of
Cb/Ld/LdBaseWordsProofs.lean; this file carries it to a code read under a transformation, to the
oracles, the transcripts and the relations. What the statements say, and the limits: the head of
Cb/Ld/LdBase.lean.

Main names (statements and hypotheses: Cb/Ld/LdBase.lean):
  `ldBase_within`: the bad sets within the errors, round by round.
  `ldBase_clean`: the backward step.
  `ldBase_exact`: see its statement in Cb/Ld/LdBase.lean.
  `ldBase_reads`: how much is read.
  `ldBase_good`: the base case's record `IOR.GoodT`.
  `ldBase_literal`: knowledge soundness in the field's form.
-/
import Cb.Ld.LdBase
import Cb.Ld.LdBaseWordsProofs
import Cb.Gen.CodeEraseLdProofs
import Ior.ExactSeq
import Ior.KnowLit

set_option autoImplicit false

namespace Cb
open Iop Prob Blocks Hiop

/-! ## From a code read under a transformation to plain words -/

/-- A count is not made smaller by an injective map that keeps the property. -/
theorem ldw_cnt_inj {α β : Type} [Finite α] [Finite β] (φ : α → β) (hφ : Function.Injective φ)
    {A : α → Prop} {B : β → Prop} (h : ∀ a, A a → B (φ a)) : cnt A ≤ cnt B := by
  unfold cnt
  exact Nat.card_le_card_of_injective (fun a : {a // A a} => (⟨φ a.1, h a.1 a.2⟩ : {b // B b}))
    fun a b hab => Subtype.ext (hφ (congrArg Subtype.val hab))

section
variable {E P : Type} [Field E] {C : LdCode E P}

theorem ldCw_lin (hC : C.Laws) : LdwLin (E := E) (ldCw C) := by
  intro a b μ x
  have h1 : C.enc (a + μ • b).1 (a + μ • b).2 = C.enc a.1 a.2 + μ • C.enc b.1 b.2 :=
    (hC.encLin.map_add a (μ • b)).trans
      (congrArg (fun z => C.enc a.1 a.2 + z) (hC.encLin.map_smul μ b))
  show C.T (C.enc (a + μ • b).1 (a + μ • b).2) x = _
  rw [h1, hC.tLin.map_add, hC.tLin.map_smul]
  rfl

/-- Under `hC` (`C.Laws`): the encoder alone, read as a word at one position, is linear (`LdwLin`).
-/
theorem ldEnc_lin (hC : C.Laws) :
    LdwLin (E := E) (fun (w : C.MR) (_ : Unit) => C.enc w.1 w.2) := fun a b μ _ =>
  (hC.encLin.map_add a (μ • b)).trans
    (congrArg (fun z => C.enc a.1 a.2 + z) (hC.encLin.map_smul μ b))

theorem ldForm_form {St : Type} (sl : Slf E St C.J) (x : E × St) :
    LdwForm (ldForm (C := C) sl x) := by
  intro a b μ
  unfold ldForm
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

omit [Field E] in
theorem ldwOn_iff {y : P → C.Aa → E} {S : Finset P} : LdwOn (ldCw C) y S ↔ C.OnCode y S :=
  ⟨fun ⟨M, h⟩ => ⟨M.1, M.2, h⟩, fun ⟨m, r, h⟩ => ⟨(m, r), h⟩⟩

variable [Fintype P]

/-- The exceptional values of a line, counted by the code's mutual correlated agreement. -/
theorem ldw_cnt_exc [Finite E] {e bad : ℕ} (h : C.MCAat e bad) (g f : C.Word) :
    cnt (fun μ : E => LdwExc (ldCw C) e (C.T g) (C.T f) μ) ≤ bad :=
  le_trans (cnt_mono fun _ ⟨S, hS, h1, h2⟩ =>
    ⟨S, hS, ldwOn_iff.1 h1, fun hb => h2 ⟨ldwOn_iff.2 hb.1, ldwOn_iff.2 hb.2⟩⟩) (h g f)

omit [Field E] in
/-- The list of a pair of words, counted by the list of the code with two interleaved rows. -/
theorem ldw_cnt_pairs [Finite E] {e L2 : ℕ} (h : (C.il Bool).ListAt e L2) (g f : C.Word) :
    cnt (fun MM : C.MR × C.MR => LdwNear2 (ldCw C) e (C.T g) (C.T f) MM.1 MM.2) ≤ L2 := by
  refine le_trans
    (ldw_cnt_inj
      (fun MM : C.MR × C.MR =>
        ((fun j : Bool × C.J => bif j.1 then MM.2.1 j.2 else MM.1.1 j.2,
          fun q : Bool × C.Q => bif q.1 then MM.2.2 q.2 else MM.1.2 q.2) : (C.il Bool).MR))
      ?_ ?_)
    (h fun p s => bif s.1 then f p s.2 else g p s.2)
  · intro MM MM' hh
    have h1 := congrArg Prod.fst hh
    have h2 := congrArg Prod.snd hh
    refine Prod.ext
      (Prod.ext (funext fun j => congrFun h1 (false, j)) (funext fun q => congrFun h2 (false, q)))
      (Prod.ext (funext fun j => congrFun h1 (true, j)) (funext fun q => congrFun h2 (true, q)))
  · intro MM hMM
    refine le_trans (cnt_mono fun x hne => ?_) hMM
    by_contra hcon
    have hcon : C.T g x = ldCw C MM.1 x ∧ C.T f x = ldCw C MM.2 x :=
      ⟨by_contra fun h => hcon (Or.inl h), by_contra fun h => hcon (Or.inr h)⟩
    refine hne (funext fun α => ?_)
    obtain ⟨b, α'⟩ := α
    cases b
    · exact congrFun hcon.1 α'
    · exact congrFun hcon.2 α'

/-- The corrector's result agrees on S, whenever S passes the threshold and something agrees.
(Nothing is asked of d.) -/
theorem ldEraseD_agrees {d : ℕ} {S : Finset P} {y : P → C.Aa → E}
    (hS : Fintype.card P < S.card + d) (hw : ∃ w, C.AgreesOn S y w) :
    C.AgreesOn S y (C.eraseD d S y) := by
  have h : Fintype.card P < S.card + d ∧ ∃ w, C.AgreesOn S y w := ⟨hS, hw⟩
  unfold LdCode.eraseD LdCode.erase?
  rw [dif_pos h]
  exact h.2.choose_spec

omit [Field E] in
theorem ld_mem_agr {y : P → C.Aa → E} {w : C.MR} {x : P} :
    x ∈ C.agr y w ↔ x ∈ ldwAgree (ldCw C) y w := by
  rw [mem_ldwAgree]
  classical
  unfold LdCode.agr
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ x, h⟩⟩

end

/-! ## Knowledge soundness -/

theorem ldBase_within : Spec.ldBase_within := by
  intro E P _ _ _ _ C St sl t e bad L2 hm hl a
  exact ⟨fun m =>
      ldw_cnt_bad1 E C.MR (C.Aa → E) P (ldCw C) e bad L2 _ _ _ _ _
        (ldw_cnt_exc hm m.1 a.2) (ldw_cnt_pairs hl m.1 a.2),
    fun m μ =>
      ⟨fun m' => ldw_cnt_bad2 E C.MR (C.Aa → E) P (ldCw C) e (C.T a.2) (C.T m.1) μ m'.2 t,
        fun _ _ => trivial⟩⟩

theorem ldBase_clean : Spec.ldBase_clean := by
  intro E P _ _ _ _ C St sl t cov d e hC hed a τ hcl hout
  obtain ⟨m, μ, m', Q, u0⟩ := τ
  have hacc : LdwAccept (ldCw C) (ldForm sl a.1) a.1.1 (C.T a.2) (C.T m.1) m.2 μ m'.2 Q := by
    by_contra hn
    have : (ldBaseIOR C sl t cov).out a.1 a.2 (m, μ, m', Q, u0) = none := if_neg hn
    rw [this] at hout
    cases hout
  have hnear : LdwNear (ldCw C) e (fun x => C.T m.1 x + μ • C.T a.2 x) m'.2 :=
    by_contra fun hc => hcl.2.1 ⟨hacc.2, hc⟩
  obtain ⟨hon, hall⟩ := ldw_back E C.MR (C.Aa → E) P (ldCw C) e (ldForm sl a.1) a.1.1 (C.T a.2)
    (C.T m.1) m.2 μ m'.2 t Q (ldCw_lin hC) (ldForm_form sl a.1) hcl.1 hcl.2.1 hacc
  have hsub : ∀ x,
      x ∈ C.agr (C.T m.1 + μ • C.T a.2) m'.2 ↔
      x ∈ ldwAgree (ldCw C) (fun x => C.T m.1 x + μ • C.T a.2 x) m'.2 :=
    fun x => ld_mem_agr
  have hcard : (C.agr (C.T m.1 + μ • C.T a.2) m'.2).card =
      (ldwAgree (ldCw C) (fun x => C.T m.1 x + μ • C.T a.2 x) m'.2).card :=
    congrArg Finset.card (Finset.ext hsub)
  have hS := hnear.card_agree
  have hag := ldEraseD_agrees (C := C) (d := d) (S := C.agr (C.T m.1 + μ • C.T a.2) m'.2)
    (y := C.T a.2) (by omega) (hon.elim fun M hM => ⟨M, fun x hx => hM x ((hsub x).1 hx)⟩)
  exact hall _ fun x hx => hag x ((hsub x).2 hx)

/-! ## Locality, completeness -/

section
variable {E P : Type} [Field E] [Fintype E] [Fintype P] [Nonempty P] {C : LdCode E P} {St : Type}
  {sl : Slf E St C.J} {t : ℕ} {cov : C.NP → P}

omit [Fintype E] [Fintype P] [Nonempty P] in
/-- The decision reads the two long words at the positions of Q only. -/
theorem LdwAccept.congr' {W Y : Type} [AddCommGroup Y] [Module E Y] {cw : W → P → Y} {L : W → E}
    {tg : E} {f f' g g' : P → Y} {u μ : E} {ms : W} {Q : Fin t → P}
    (hf : ∀ i, f (Q i) = f' (Q i)) (hg : ∀ i, g (Q i) = g' (Q i)) :
    LdwAccept cw L tg f g u μ ms Q ↔ LdwAccept cw L tg f' g' u μ ms Q := by
  unfold LdwAccept
  simp only [hf, hg]

theorem ldBase_mem_reads {ρ : Rho (ldBaseShape C t)} {p : C.NP} :
    (Sum.inl p : OPos (ldBaseShape C t)) ∈ (ldBaseIOR C sl t cov).reads ρ ↔
    ∃ i, p ∈ C.src (ρ.2.1 i) := by
  classical
  constructor
  · intro h
    obtain ⟨p', hp', he⟩ :=
      (@Finset.mem_image _ _ (fun a b => Classical.propDecidable (a = b)) _ _ _).1 h
    obtain ⟨x, hx, hpx⟩ := Finset.mem_biUnion.1 hp'
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨i, (Sum.inl.inj he) ▸ hpx⟩
  · rintro ⟨i, hi⟩
    exact (@Finset.mem_image _ _ (fun a b => Classical.propDecidable (a = b)) _ _ _).2
      ⟨p, Finset.mem_biUnion.2 ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ i), hi⟩, rfl⟩

theorem ldBase_isLocal (hC : C.Laws) : (ldBaseIOR C sl t cov).IsLocal := by
  refine ⟨?_, fun _ _ _ _ q => q.elim⟩
  intro x y y' τ τ' hρ hpl hy hτ
  obtain ⟨⟨o, u⟩, μ, ⟨v, ms⟩, Q, u0⟩ := τ
  obtain ⟨⟨o', u'⟩, μ', ⟨v', ms'⟩, Q', u0'⟩ := τ'
  obtain ⟨rfl, hρ2⟩ := Prod.mk.inj hρ
  obtain ⟨rfl, -⟩ := Prod.mk.inj hρ2
  obtain ⟨rfl, hpl2⟩ := Prod.mk.inj hpl
  obtain ⟨rfl, -⟩ := Prod.mk.inj hpl2
  classical
  refine if_congr (LdwAccept.congr' (fun i => ?_) fun i => ?_) rfl rfl
  · exact hy (Q i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  · exact hC.loc o o' (Q i) fun p hp => hτ (Sum.inl p) (ldBase_mem_reads.2 ⟨i, hp⟩)

theorem ldBase_acc (hC : C.Laws) (e : ℕ) :
    (ldBaseHon C sl t cov).Acc (C.rels sl e fun _ => ()).rel trivRels.rel := by
  intro x y w h ρ hrel _
  obtain ⟨μ, Q, u0⟩ := ρ
  obtain ⟨rfl, hw⟩ := hrel
  exact ⟨if_pos
      (ldw_complete E C.MR (C.Aa → E) P (ldCw C) (ldForm sl x) x.1 w h μ t Q
        (ldCw_lin hC) (ldForm_form sl x) hw),
    trivial⟩

omit [Field E] [Fintype E] [Fintype P] [Nonempty P] in
/-- A native position that is read for a position of Q is looked up at such a position. -/
theorem ldPick_of_read {Q : Fin t → P} {p : C.NP} (h : ∃ i, p ∈ C.src (Q i)) :
    (∃ i, ldPick C cov Q p = Q i) ∧ p ∈ C.src (ldPick C cov Q p) := by
  unfold ldPick
  rw [dif_pos h]
  exact ⟨⟨_, rfl⟩, h.choose_spec⟩

end

/-! ## Honest-verifier zero knowledge -/

theorem ldBase_exact : Spec.ldBase_exact := by
  intro E P _ _ _ _ C St sl t cov e bk hC hbk x y w hrel ρ _ T hT
  obtain ⟨rfl, hw⟩ := hrel
  rw [(ldBaseHon C sl t cov).output_of_not_mem T (fun h => h.elim id id)]
  have hlaw := ldw_law E C.MR C.Word Unit (fun (w : C.MR) (_ : Unit) => C.enc w.1 w.2) (ldForm sl x)
    x.1 w ρ.1 (ldEnc_lin hC) (ldForm_form sl x) hw
  have h1 := congrArg
    (fun p =>
      p.map fun q : E × C.MR × (Unit → C.Word) =>
        some ((ldBaseIOR C sl t cov).view T (ldBaseTr ρ q.1 q.2.1 (q.2.2 ())))) hlaw
  simp only [PMF.map_comp] at h1
  refine Eq.trans ?_ (h1.trans ?_)
  · rfl
  · show PMF.map _ _ = PMF.map _ _
    refine congrArg (fun g => PMF.map g (unif C.MR)) (funext fun ms => ?_)
    refine congrArg some ?_
    refine IOR.view_congr T rfl rfl fun p hp => ?_
    rcases p with p | p | p
    · have hp' : (Sum.inl p : OPos (ldBaseShape C t)) ∈ (ldBaseIOR C sl t cov).reads ρ ∨
          (Sum.inl p : OPos (ldBaseShape C t)) ∈ T :=
        hp.elim Or.inl fun h => h.elim Or.inr fun h => Bool.noConfusion h
      have hsrc : p ∈ C.src (ldPick C cov ρ.2.1 p) :=
        hp'.elim (fun h => (ldPick_of_read (ldBase_mem_reads.1 h)).2) fun h => hT p h
      have hmem : ldPick C cov ρ.2.1 p ∈ (ldBaseIOR C sl t cov).given ρ T :=
        IOR.mem_given.2 (Or.inr ⟨_, hp', Finset.mem_singleton_self _⟩)
      show C.enc ms.1 ms.2 p - ρ.1 • C.enc w.1 w.2 p =
        C.enc ms.1 ms.2 p -
          ρ.1 • bk (ldPick C cov ρ.2.1 p) ((C.ext.ans _ _ (ldPick C cov ρ.2.1 p)).getD 0) p
      rw [ExtSpec.ans_of_mem _ _ hmem]
      show _ = C.enc ms.1 ms.2 p -
          ρ.1 • bk (ldPick C cov ρ.2.1 p) (C.T (C.enc w.1 w.2) (ldPick C cov ρ.2.1 p)) p
      rw [hbk w.1 w.2 _ p hsrc]
    · exact p.elim
    · exact p.elim

/-! ## How much is read -/

theorem ldBase_reads : Spec.ldBase_reads := by
  classical
  intro E P _ _ _ _ C St sl t cov b ρ T
  have himg : (Finset.univ.image ρ.2.1).card ≤ t := Finset.card_image_le.trans (by simp)
  have hx : ((ldBaseIOR C sl t cov).extReads ρ).card ≤ t := himg
  refine ⟨hx, fun hb => ?_, ?_⟩
  · refine Finset.card_image_le.trans
      ((Finset.card_biUnion_le_card_mul _ _ b fun x _ => hb x).trans (Nat.mul_le_mul_right b himg))
  · have hsub : (ldBaseIOR C sl t cov).given ρ T ⊆
        (ldBaseIOR C sl t cov).extReads ρ ∪ T.biUnion ((ldBaseIOR C sl t cov).tie ρ) := by
      intro q hq
      rcases IOR.mem_given.1 hq with h | ⟨p, hp | hp, hq'⟩
      · exact Finset.mem_union_left _ h
      · rcases p with p | p | p
        · obtain ⟨i, hi⟩ := (ldPick_of_read (cov := cov) (ldBase_mem_reads.1 hp)).1
          rw [Finset.mem_singleton.1 hq', hi]
          exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
        · exact p.elim
        · exact p.elim
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨p, hp, hq'⟩)
    have htie : (T.biUnion ((ldBaseIOR C sl t cov).tie ρ)).card ≤
        T.card * 1 := Finset.card_biUnion_le_card_mul _ _ 1 fun p _ => by
      rcases p with p | p
      · exact (Finset.card_singleton _).le
      · exact Nat.zero_le 1
    calc ((ldBaseIOR C sl t cov).given ρ T).card ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ t + T.card := Nat.add_le_add hx (by simpa using htie)

/-! ## The bundle -/

theorem ldBase_know {E P : Type} [Field E] [Fintype E] [Fintype P] [Nonempty P] (C : LdCode E P)
    {St : Type} (sl : Slf E St C.J) (t : ℕ) (cov : C.NP → P) {d e bad L2 : ℕ} (hC : C.Laws)
    (hed : e < d) (hm : C.MCAat e bad) (hl : (C.il Bool).ListAt e L2) :
    (ldBaseIOR C sl t cov).red.Know (fun _ => True) (C.rels sl e fun _ => ()).relR trivRels.relR
      (ldBaseExt C t d) (ldBaseErr C t e bad L2) :=
  Reduction.Know.of_badFam (ldBaseBad C sl t e)
      (fun a _ => ldBase_within E P C St sl t e bad L2 hm hl a) fun a τ b _ _ hcl hout _ => by
    obtain ⟨xo, hxo, -⟩ := Option.map_eq_some_iff.1 hout
    exact ldBase_clean E P C St sl t cov d e hC hed a τ hcl hxo

theorem ldBase_good : Spec.ldBase_good := by
  intro E P _ _ _ _ C St sl t cov d e bad L2 hC htr hed hm hl
  obtain ⟨bk, hbk⟩ := htr
  exact {
    point := ⟨ldBasePoint C t⟩
    isLocal := ldBase_isLocal hC
    acc := ldBase_acc hC e
    onOut := fun _ _ _ _ _ => trivial
    keeps := fun _ _ _ _ => rfl
    prBad := prRho_empty _ fun _ h => h
    cover := fun _ _ => le_refl _
    prCov := fun _ => prRho_empty _ fun _ h => h
    know := ldBase_know C sl t cov hC hed hm hl
    exact := ⟨ldBaseSim C sl t cov bk, ldBase_exact E P C St sl t cov e bk hC hbk⟩ }

theorem ldBase_literal : Spec.ldBase_literal := by
  intro E P _ _ _ _ C St sl t cov d e bad L2 hC hed hm hl
  exact literal_of_know _ _ _ _ (ldBaseIOR C sl t cov).red _ _ _ _ _
    (List.cons_ne_nil _ _) (ldBase_know C sl t cov hC hed hm hl)

end Cb
