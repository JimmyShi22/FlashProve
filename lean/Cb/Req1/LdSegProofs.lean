-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegProofs.lean: the proofs of the statements of Cb/Req1/LdSeg.lean, but for `ldSeg_kept`
(Cb/Req1/LdSegProofsFold.lean). By composition only: the blocks' own theorems, the rules for chains
(Ior/KnowCollRulesChain.lean), for a condition that is moved (`goodT_cf`, `goodB_cf`, `goodM_cf`,
`knowInto_iff`) and for steps without rounds (`goodT_pure`, `extMap_isLocal`), `goodT_iff`, the
lifting rule (`sigLift_goodB`, `sigLift_goodT`), and Cb/Req1/LdSegProofsFold.lean,
Cb/Req1/LdSegProofsLoc.lean for the two moves, "fold" and "loc", whose link (`LdFoldD.link`,
`LdLocD.link`, Cb/Req1/LdSegKit.lean) adds steps without rounds to a block.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegProofsLoc
import Cb.Ld.LdSigSumProofs
import Cb.Ld.LdSplitProofs
import Cb.Ld.LdSigLiftProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood IOR IOR.Chain
open scoped ENNReal

section
variable {E Kc : Type} [Field E]

theorem goodB_of_goodT' {A B : Joint Kc} {l : Link Kc A B} (h : l.GoodT) : l.GoodB :=
  ((goodT_iff _ _ _ _ _ _ _ _ _ _ _ _ _).1 h).1

theorem LdSendD.goodT {a : LdStage E Kc} (d : LdSendD a) (h : d.Hyp) : d.link.GoodT :=
  ldSendSig_chain E a.S d.N d.Sd Kc a.St a.Wp d.Wp' a.E₀ a.A d.bk d.D d.L d.t h.laws h.fair h.list
    h.evades h.sender h.blind h.hides

theorem LdBatD.goodT (D : LdBatD E Kc) (h : D.Hyp) : D.link.GoodT :=
  goodT_cf _ _ _ _ _ _ _ _ _ _ _ _ _
    (ldBat_sig_lin E D.B Kc D.St₀ D.Wp D.S D.Sb D.sl D.Z D.E₀ D.A₀ (fun _ => True) h).good

theorem LdStage.idLink_goodT (a : LdStage E Kc) : a.idLink.GoodT := by
  have hS : StepT (fun x : a.X => some x) (ExtMap.id a.Ex) (fun p : a.X × a.W => p)
      (fun _ w => w) a.J.rels a.J.rels :=
    { isLocal := extMap_isLocal.1 _
      acc := fun _ _ _ h => ⟨rfl, h⟩
      onOut := fun _ _ _ _ _ => trivial
      keeps := fun _ _ => rfl
      know := by
        intro x y x' w' _ hx hw
        cases hx
        exact hw }
  exact goodT_pure _ _ _ _ _ _ _ _ _ _ _ _ _ hS

end

theorem ldSeg_split : Spec.ldSeg_split := fun E Kc _ _ D h =>
  goodM_cf _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (ldSpl_good E Kc D.St₀ D.Wp D.S D.G₁ D.G₂ D.k D.St₁ D.St₂ D.sl₁ D.sl₂ D.E₀ D.A₀ D.Rd h.own₁
      h.own₂ h.rd₁ h.rd₂ h.rdK)

theorem ldSeg_mvT : Spec.ldSeg_mvT := by
  intro E Kc _ _ a b m h h1 h2
  cases m with
  | send a d => exact (allT_one _).2 (d.goodT h)
  | sub a b c => exact absurd rfl h1
  | bat D => exact (allT_one _).2 (D.goodT h)
  | split D => exact absurd rfl h2
  | fold D l => exact (allT_one _).2 (ldSeg_fold_goodT D l h)
  | loc D => exact (allT_one _).2 (ldSeg_loc_goodT D h)
  | step a b f g m back => exact (allT_one _).2 (goodT_pure _ _ _ _ _ _ _ _ _ f g m back h)

theorem ldSeg_mv : Spec.ldSeg_mv := by
  intro E Kc _ _ a b m h
  cases m with
  | send a d => exact (allB_one _).2 (goodB_of_goodT' (d.goodT h))
  | sub a b c => exact h
  | bat D => exact (allB_one _).2 (goodB_of_goodT' (D.goodT h))
  | split D => exact (allB_one _).2 (ldSeg_split E Kc D h).base
  | fold D l => exact (allB_one _).2 (goodB_of_goodT' (ldSeg_fold_goodT D l h))
  | loc D => exact (allB_one _).2 (goodB_of_goodT' (ldSeg_loc_goodT D h))
  | step a b f g m back => exact (allB_one _).2 (goodB_of_goodT' (goodT_pure _ _ _ _ _ _ _ _ _ f g m back h))

section
variable {E Kc : Type} [Field E] [Fintype E]

namespace LdProg
variable {A : Joint Kc}

theorem onto_nil (a : LdStage E Kc) (c : Chain Kc A a.J) : (LdProg.nil a).onto c = c := by rw [onto]
theorem onto_snoc {a b c : LdStage E Kc} (c₀ : Chain Kc A a.J) (p : LdProg a b) (m : LdMv b c) :
    (p.snoc m).onto c₀ = (p.onto c₀).append m.chain := by rw [onto]
theorem hyp_snoc {a b c : LdStage E Kc} (p : LdProg a b) (m : LdMv b c) :
    (p.snoc m).Hyp ↔ p.Hyp ∧ m.Hyp := by rw [Hyp]
theorem nAll_nil (a : LdStage E Kc) : (LdProg.nil a).nAll = 0 := by rw [nAll]
theorem nVer_nil (a : LdStage E Kc) : (LdProg.nil a).nVer = 0 := by rw [nVer]
theorem pBad_nil (a : LdStage E Kc) : (LdProg.nil a).pBad = 0 := by rw [pBad]
theorem pHid_nil (a : LdStage E Kc) : (LdProg.nil a).pHid = 0 := by rw [pHid]
theorem nAll_snoc {a b c : LdStage E Kc} (p : LdProg a b) (m : LdMv b c) :
    (p.snoc m).nAll = p.nAll + m.chain.nAll := by rw [nAll]
theorem nVer_snoc {a b c : LdStage E Kc} (p : LdProg a b) (m : LdMv b c) :
    (p.snoc m).nVer = p.nVer + m.chain.nVer := by rw [nVer]
theorem pBad_snoc {a b c : LdStage E Kc} (p : LdProg a b) (m : LdMv b c) :
    (p.snoc m).pBad = p.pBad + m.chain.pBad := by rw [pBad]
theorem pHid_snoc {a b c : LdStage E Kc} (p : LdProg a b) (m : LdMv b c) :
    (p.snoc m).pHid = p.pHid + m.chain.pHid := by rw [pHid]

/-- a list of moves behind a chain: the bundle without its clause on zero knowledge, link by link
(not all hypotheses are named here: see the statement below) -/
theorem onto_allB {a b : LdStage E Kc} (p : LdProg a b) :
    ∀ c₀ : Chain Kc A a.J, c₀.AllB → p.Hyp → (p.onto c₀).AllB := by
  induction p with
  | nil =>
      intro c₀ h0 _
      rw [onto_nil]
      exact h0
  | snoc p m ih =>
      intro c₀ h0 h
      rw [onto_snoc]
      exact ((all_append Kc _ _ _ _ _).1).2
        ⟨ih c₀ h0 ((hyp_snoc p m).1 h).1, ldSeg_mv E Kc _ _ m ((hyp_snoc p m).1 h).2⟩

/-- its numbers add -/
theorem onto_nums {a b : LdStage E Kc} (p : LdProg a b) :
    ∀ c₀ : Chain Kc A a.J,
      (p.onto c₀).nAll = c₀.nAll + p.nAll ∧
      (p.onto c₀).nVer = c₀.nVer + p.nVer ∧
      (p.onto c₀).pBad = c₀.pBad + p.pBad ∧
      (p.onto c₀).pHid = c₀.pHid + p.pHid := by
  induction p with
  | nil =>
      intro c₀
      rw [onto_nil, nAll_nil, nVer_nil, pBad_nil, pHid_nil]
      exact ⟨rfl, rfl, (add_zero _).symm, (add_zero _).symm⟩
  | snoc p m ih =>
      intro c₀
      obtain ⟨h1, h2, h3, h4⟩ := ih c₀
      obtain ⟨k1, k2, k3, k4⟩ := nums_append Kc _ _ _ (p.onto c₀) m.chain
      rw [onto_snoc, nAll_snoc, nVer_snoc, pBad_snoc, pHid_snoc, k1, k2, k3, k4, h1, h2, h3, h4]
      exact ⟨Nat.add_assoc _ _ _, Nat.add_assoc _ _ _, add_assoc _ _ _, add_assoc _ _ _⟩

end LdProg
end

theorem ldSeg_onto : Spec.ldSeg_onto := by
  intro E Kc _ _ A a d c₀ s h0 h
  refine s.loc.onto_allB _ ?_ h.loc
  exact (allB_snoc _ _).2
    ⟨s.fold.onto_allB _ (s.bat.onto_allB _ (s.body.onto_allB _ h0 h.body) h.bat) h.fold,
      goodB_of_goodT' (s.snd.goodT h.snd)⟩

theorem ldSeg_goodB : Spec.ldSeg_goodB := fun E Kc _ _ a d s w₀ h =>
  chain_goodB Kc _ _ s.chain w₀
    (ldSeg_onto E Kc _ a d _ s ((allB_one _).2 (goodB_of_goodT' a.idLink_goodT)) h)

theorem ldSeg_into : Spec.ldSeg_into := fun E Kc _ _ a d s w₀ h =>
  (knowInto_iff _ _ _ _ _ _ _ _ _ _ _).2 (ldSeg_goodB E Kc a d s w₀ h).know

theorem ldSeg_nums : Spec.ldSeg_nums := by
  intro E Kc _ _ A a d c₀ s
  have key : ∀ (A : Joint Kc) (c₀ : Chain Kc A a.J),
      (s.onto c₀).nAll = c₀.nAll + s.nAll ∧
      (s.onto c₀).nVer = c₀.nVer + s.nVer ∧
      (s.onto c₀).pBad = c₀.pBad + s.pBad ∧
      (s.onto c₀).pHid = c₀.pHid + s.pHid := by
    intro A c₀
    obtain ⟨a1, a2, a3, a4⟩ := s.body.onto_nums c₀
    obtain ⟨b1, b2, b3, b4⟩ := s.bat.onto_nums (s.body.onto c₀)
    obtain ⟨c1, c2, c3, c4⟩ := s.fold.onto_nums (s.bat.onto (s.body.onto c₀))
    obtain ⟨d1, d2, d3, d4⟩ :=
      s.loc.onto_nums (.snoc (s.fold.onto (s.bat.onto (s.body.onto c₀))) s.snd.link)
    refine ⟨?_, ?_, ?_, ?_⟩
    · show (s.loc.onto _).nAll = _
      rw [d1, nAll_snoc, c1, b1, a1]
      simp only [LdSeg.nAll, Nat.add_assoc]
    · show (s.loc.onto _).nVer = _
      rw [d2, nVer_snoc, c2, b2, a2]
      simp only [LdSeg.nVer, Nat.add_assoc]
    · show (s.loc.onto _).pBad = _
      rw [d3, pBad_snoc, c3, b3, a3]
      simp only [LdSeg.pBad, add_assoc]
    · show (s.loc.onto _).pHid = _
      rw [d4, pHid_snoc, c4, b4, a4]
      simp only [LdSeg.pHid, add_assoc]
  refine ⟨key A c₀, fun w₀ => ?_⟩
  obtain ⟨n1, n2, n3, n4⟩ := chain_nums Kc _ _ s.chain w₀
  obtain ⟨k1, k2, k3, k4⟩ := key _ (.one a.idLink)
  rw [n1, n2, n3, n4]
  refine ⟨k1.trans ?_, k2.trans ?_, k3.trans ?_, k4.trans ?_⟩
  · rw [nAll_one]; exact Nat.zero_add _
  · rw [nVer_one]; exact Nat.zero_add _
  · rw [pBad_one]; exact zero_add _
  · rw [pHid_one]; exact zero_add _

theorem ldSeg_rounds : Spec.ldSeg_rounds := by
  intro E Kc _ _
  have hU : ∀ (i : Fintype Unit), @Fintype.card Unit i = 1 := fun i =>
    @Fintype.card_eq_one_iff Unit i |>.2 ⟨(), fun _ => rfl⟩
  refine ⟨fun a d => ⟨rfl, ?_, rfl, rfl⟩,
    fun D => ⟨rfl, rfl, rfl⟩,
    fun D => ⟨rfl, ?_, rfl, rfl⟩,
    fun D => ⟨rfl, rfl, rfl⟩,
    fun D l => ⟨rfl, rfl, rfl⟩,
    fun a b f g m back => ?_⟩
  · show (if _ then 0 else 1) + ((if _ then 0 else 1) + 0) ≤ 1
    rw [if_pos (hU _)]
    split <;> omega
  · show (if _ then 0 else 1) + 0 = 0
    rw [if_pos (hU _)]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact (nAll_one _).trans rfl
    · exact (nVer_one _).trans rfl
    · exact (pBad_one _).trans rfl
    · exact (pHid_one _).trans rfl

theorem ldSeg_sub_goodT : Spec.ldSeg_sub_goodT := fun _ _ _ _ _ _ _ h =>
  goodT_cf _ _ _ _ _ _ _ _ _ _ _ _ _ h

theorem ldSeg_sub_goodM : Spec.ldSeg_sub_goodM := fun _ _ _ _ _ _ _ _ h =>
  goodM_cf _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

theorem ldSeg_lift : Spec.ldSeg_lift := fun E Kc _ _ a St' Wp' E₀' B R H ext P g =>
  ⟨goodB_cf _ _ _ _ _ _ _ _ _ _ _ _ _
      (sigLift_goodB E a.S Kc a.St St' a.Wp Wp' a.E₀ E₀' R H a.A B ext P g),
    fun hx =>
      goodT_cf _ _ _ _ _ _ _ _ _ _ _ _ _
        (sigLift_goodT E a.S Kc a.St St' a.Wp Wp' a.E₀ E₀' R H a.A B ext P g hx)⟩

end Cb
