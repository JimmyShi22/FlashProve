-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegFrontProofs.lean: the proofs of the statements of Cb/Req1/LdSegFront.lean.
By the rules for lists of moves (Cb/Req1/LdSegRefKit.lean, Cb/Req1/LdSegProofs.lean,
Cb/Req1/LdReqProofs.lean), the rule for a step that only maps the explicit part (`ldStepF_hyp`,
Cb/Req1/LdSegCloseProofs.lean) and the packing of blocks as moves (Cb/Req1/LdSegRefPsc.lean).

Main names (statements and hypotheses: Cb/Req1/LdSegFront.lean):
  `ldSegFront_hyp`: for every `F : LdFrontD E Kc` (the first part of a segment's body), `F.OK` gives
    `F.prog.Hyp`, the hypotheses of all moves of the front `F.prog`.

Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegFront
import Cb.Req1.LdSegCloseProofs
import Cb.Ld.LdPscProofsOur

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR IOR.Chain
open scoped ENNReal

section
variable {E Kc : Type} [Field E] [Fintype E]

/-- a step that only maps the explicit part: its kind, what zero knowledge asks, beside its
hypotheses, its numbers -/
theorem ldStepF_tag (S : Sig E) {St St' Wp : Type} {E₀ : ExtSpec} (A : Rels Kc St E₀ (S.Msg × Wp))
    (A' : Rels Kc St' E₀ (S.Msg × Wp)) (f : St → St') :
    (ldStepF S A A' f).tag = .step := rfl
theorem ldStepF_zk (S : Sig E) {St St' Wp : Type} {E₀ : ExtSpec} (A : Rels Kc St E₀ (S.Msg × Wp))
    (A' : Rels Kc St' E₀ (S.Msg × Wp)) (f : St → St') (base) : (ldStepF S A A' f).Zk base := trivial
theorem ldStepF_nums (S : Sig E) {St St' Wp : Type} {E₀ : ExtSpec} (A : Rels Kc St E₀ (S.Msg × Wp))
    (A' : Rels Kc St' E₀ (S.Msg × Wp)) (f : St → St') :
    (ldStepF S A A' f).chain.nAll = 0 ∧
    (ldStepF S A A' f).chain.nVer = 0 ∧
    (ldStepF S A A' f).chain.pBad = 0 ∧
    (ldStepF S A A' f).chain.pHid = 0 :=
  (ldSeg_rounds E Kc).2.2.2.2.2 _ _ _ _ _ _

namespace LdFrontD
variable (F : LdFrontD E Kc)

theorem mid_zero : F.mid 0 = .nil _ := rfl
theorem mid_succ (k : ℕ) : F.mid (k + 1) = ((F.mid k).app (F.blk k)).snoc (F.step k) := rfl

theorem StepOK.hyp {St St' : Type} {A : Rels Kc St F.E₀ (F.S.Msg × F.Wp)}
    {A' : Rels Kc St' F.E₀ (F.S.Msg × F.Wp)} {f : St → St'} (h : F.StepOK A A' f) :
    (ldStepF F.S A A' f).Hyp :=
  ldStepF_hyp F.S A A' f h.fw h.on h.core h.bw

theorem mid_hyp (h : F.OK) : ∀ k ≤ F.n, (F.mid k).Hyp
  | 0, _ => LdProg.hyp_nilK _
  | k + 1, hk => by
      rw [mid_succ]
      exact (LdProg.hyp_snoc _ _).2
        ⟨(ldProg_app_hyp E Kc _ _ _ _ _).2 ⟨mid_hyp h k (Nat.le_of_succ_le hk), h.block k hk⟩,
          (h.step k hk).hyp⟩

theorem mid_all (k : LdTag → Prop) (hs : k .step) (hb : ∀ i < F.n, (F.blk i).All k) :
    ∀ j ≤ F.n, (F.mid j).All k
  | 0, _ => LdProg.all_nilK _ _
  | j + 1, hj => by
      rw [mid_succ]
      exact (LdProg.all_snoc _ _ _).2
        ⟨(ldProg_app_all E Kc _ _ _ _ _ k).2 ⟨mid_all k hs hb j (Nat.le_of_succ_le hj), hb j hj⟩,
          hs⟩

theorem mid_nums :
    ∀ k,
      (F.mid k).nAll = ∑ i ∈ Finset.range k, (F.blk i).nAll ∧
      (F.mid k).nVer = ∑ i ∈ Finset.range k, (F.blk i).nVer ∧
      (F.mid k).pBad = ∑ i ∈ Finset.range k, (F.blk i).pBad ∧
      (F.mid k).pHid = ∑ i ∈ Finset.range k, (F.blk i).pHid
  | 0 => ⟨LdProg.nAll_nil _, LdProg.nVer_nil _, LdProg.pBad_nil _, LdProg.pHid_nil _⟩
  | k + 1 => by
      obtain ⟨a1, a2, a3, a4⟩ := mid_nums k
      obtain ⟨b1, b2, b3, b4⟩ := ldProg_app_nums E Kc _ _ _ (F.mid k) (F.blk k)
      obtain ⟨c1, c2, c3, c4⟩ := ldStepF_nums F.S (F.At k) (F.As (k + 1)) (F.g k)
      rw [mid_succ, LdProg.nAll_snoc, LdProg.nVer_snoc, LdProg.pBad_snoc, LdProg.pHid_snoc, b1, b2,
        b3, b4, a1, a2, a3, a4, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ]
      exact ⟨by rw [show (F.step k).chain.nAll = 0 from c1]; rfl,
        by rw [show (F.step k).chain.nVer = 0 from c2]; rfl,
        by rw [show (F.step k).chain.pBad = 0 from c3, add_zero],
        by rw [show (F.step k).chain.pHid = 0 from c4, add_zero]⟩

theorem mid_zk (base : MaskFact F.a.J.W → Prop)
    (hb : ∀ i < F.n, (F.blk i).Zk ((F.pre.app (F.mid i)).After base)) :
    ∀ k ≤ F.n, (F.mid k).Zk (F.pre.After base)
  | 0, _ => (LdProg.zk_nil _ _).2 trivial
  | k + 1, hk => by
      rw [mid_succ]
      have h1 := hb k hk
      rw [ldProg_app_after] at h1
      exact (LdProg.zk_snoc _ _ _).2
        ⟨(ldProg_app_zk E Kc _ _ _ _ _ _).2 ⟨mid_zk base hb k (Nat.le_of_succ_le hk), h1⟩,
          ldStepF_zk _ _ _ _ _⟩

end LdFrontD
end

theorem ldSegFront_hyp : Spec.ldSegFront_hyp := fun E Kc _ _ F h =>
  (LdProg.hyp_snoc _ _).2
    ⟨(ldProg_app_hyp E Kc _ _ _ _ _).2 ⟨h.pre, F.mid_hyp h F.n le_rfl⟩, h.post.hyp⟩

theorem ldSegFront_kinds : Spec.ldSegFront_kinds := fun E Kc _ _ F k hs hp hb =>
  (LdProg.all_snoc _ _ _).2
    ⟨(ldProg_app_all E Kc _ _ _ _ _ k).2 ⟨hp, F.mid_all k hs hb F.n le_rfl⟩, hs⟩

theorem ldSegFront_nums : Spec.ldSegFront_nums := by
  intro E Kc _ _ F
  obtain ⟨a1, a2, a3, a4⟩ := F.mid_nums F.n
  obtain ⟨b1, b2, b3, b4⟩ := ldProg_app_nums E Kc _ _ _ F.pre (F.mid F.n)
  obtain ⟨c1, c2, c3, c4⟩ := ldStepF_nums F.S (F.As F.n) F.Az F.gz
  unfold LdFrontD.prog
  rw [LdProg.nAll_snoc, LdProg.nVer_snoc, LdProg.pBad_snoc, LdProg.pHid_snoc, b1,
    b2, b3, b4, a1, a2, a3, a4]
  exact ⟨by rw [show F.post.chain.nAll = 0 from c1]; rfl,
    by rw [show F.post.chain.nVer = 0 from c2]; rfl,
    by rw [show F.post.chain.pBad = 0 from c3, add_zero],
    by rw [show F.post.chain.pHid = 0 from c4, add_zero]⟩

theorem ldSegFront_zk : Spec.ldSegFront_zk := fun E Kc _ _ F base hp hb =>
  (LdProg.zk_snoc _ _ _).2
    ⟨(ldProg_app_zk E Kc _ _ _ _ _ _).2 ⟨hp, F.mid_zk base hb F.n le_rfl⟩, ldStepF_zk _ _ _ _ _⟩

theorem ldSegFront_psc_hyp : Spec.ldSegFront_psc_hyp := fun _ Kc _ _ T S E₀ Wp A0 msg hV hX hY hI =>
  (LdProg.hyp_snoc _ _).2
    ⟨LdProg.hyp_nilK _, mvA_hyp _ _ _ (pscBk_good T E₀ S.Msg Wp Kc msg A0 hV hX hY hI)⟩

theorem ldSegFront_in_hyp :
    Spec.ldSegFront_in_hyp := fun _ Kc _ _ Z S E₀ Wp R0 msg hL hB hO hV hX hY hI =>
  (LdProg.hyp_snoc _ _).2
    ⟨(LdProg.hyp_snoc _ _).2
        ⟨LdProg.hyp_nilK _, mvA_hyp _ _ _ (inBk_good Z E₀ S.Msg Wp Kc R0 msg hL hB hO)⟩,
      mvA_hyp (frPscS Kc Z.T S E₀ Wp (Z.ride R0) msg) _ _
        (pscBk_good Z.T E₀ S.Msg Wp Kc msg (Z.ride R0) hV hX hY hI)⟩

theorem ldSegFront_psc_zk : Spec.ldSegFront_psc_zk := by
  intro E Kc _ _ T S E₀ Wp A0 msg Rd base hM hb
  refine (LdProg.zk_snoc _ _ _).2 ⟨(LdProg.zk_nil _ _).2 trivial, ?_⟩
  rw [LdProg.after_nil]
  exact mvA_okM (frPscS Kc T S E₀ Wp A0 msg) _ _ base (frMask Kc T S E₀ Wp A0 msg Rd) hM hb

theorem ldSegFront_in_zk : Spec.ldSegFront_in_zk := by
  intro E Kc _ _ Z S E₀ Wp R0 msg Rd base hL hB hO hM hb
  refine (LdProg.zk_snoc _ _ _).2 ⟨(LdProg.zk_snoc _ _ _).2 ⟨(LdProg.zk_nil _ _).2 trivial, ?_⟩, ?_⟩
  · rw [LdProg.after_nil]
    exact mvA_okT (frInS Kc Z S E₀ Wp R0 msg) _ _ base
      (inBk_good Z E₀ S.Msg Wp Kc R0 msg hL hB hO) (inBk_exact Z E₀ S.Msg Wp Kc _)
  · rw [LdProg.after_snoc, LdProg.after_nil]
    refine mvA_okM (frPscS Kc Z.T S E₀ Wp (Z.ride R0) msg) _ _ _
      (frMask Kc Z.T S E₀ Wp (Z.ride R0) msg Rd) hM ?_
    exact mvA_carry (frInS Kc Z S E₀ Wp R0 msg) _ _ (inBk_plain Z E₀ S.Msg Wp Kc)
      (inBk_sameOn Z E₀ S.Msg Wp Kc Z.T.J msg fun _ => False) base
      (frFact Kc Z.T S E₀ Wp (Z.ride R0) msg Rd) (fun _ _ _ _ _ h => h.elim) hb

theorem ldSegFront_psc_nums : Spec.ldSegFront_psc_nums := by
  intro E Kc _ _ T S E₀ Wp A0 msg
  unfold frPsc
  rw [LdProg.nAll_snoc, LdProg.pBad_snoc, LdProg.pHid_snoc, LdProg.nAll_nil,
    LdProg.pBad_nil, LdProg.pHid_nil]
  refine ⟨?_, ?_, ?_, (LdProg.all_snoc _ _ _).2 ⟨LdProg.all_nilK _ _, rfl⟩⟩
  · rw [Nat.zero_add]
    exact (nAll_one _).trans (psc_our_len E T E₀)
  · rw [zero_add]
    exact (pBad_one _).trans rfl
  · rw [zero_add]
    exact (pHid_one _).trans rfl

theorem ldSegFront_in_nums : Spec.ldSegFront_in_nums := by
  intro E Kc _ _ Z S E₀ Wp R0 msg
  unfold frIn
  rw [LdProg.nAll_snoc, LdProg.pBad_snoc, LdProg.pHid_snoc, LdProg.nAll_snoc, LdProg.pBad_snoc,
    LdProg.pHid_snoc, LdProg.nAll_nil, LdProg.pBad_nil, LdProg.pHid_nil]
  refine ⟨?_, ?_, ?_,
    (LdProg.all_snoc _ _ _).2 ⟨(LdProg.all_snoc _ _ _).2 ⟨LdProg.all_nilK _ _, rfl⟩, rfl⟩⟩
  · rw [Nat.zero_add]
    exact congrArg₂ (· + ·) ((nAll_one _).trans rfl) ((nAll_one _).trans (psc_our_len E Z.T E₀))
  · rw [zero_add]
    exact (congrArg₂ (· + ·) ((pBad_one _).trans rfl) ((pBad_one _).trans rfl)).trans (add_zero 0)
  · rw [zero_add]
    exact (congrArg₂ (· + ·) ((pHid_one _).trans rfl) ((pHid_one _).trans rfl)).trans (add_zero 0)

end Cb
