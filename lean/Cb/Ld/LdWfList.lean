-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdWfList.lean: the numbers of the parameter list of the preamble of weights-formedness in
closed form (rounds, errors, the two probabilities), and the count of mask values.
Proofs of `Spec.ldWf_rounds`, `ldWf_err`, `ldWf_prob`, `ldWf_masks` (Cb/Ld/LdWf.lean); that of
`ldWf_side` is in Cb/Ld/LdWfSide.lean. Nothing is assumed beside the hypotheses in the statements'
texts.

Why: the numbers of a chain are sums over its links (`IOR.Link`) (Ior/KnowCollRulesChain.lean:
`chain_nums`); the errors of two links in a row are joined by definition (`Nums.seq`); as plain
lists: `Err.list_app` (Cb/Ld/LdWfPre.lean); for `ldWf_side` (Cb/Ld/LdWfSide.lean): the budgets' half
goes link by link (Ior/KnowCollPiece.lean: `chain_sides`; a masked block has it almost for nothing:
`side_of_mm`).

Limits: what the head of Cb/Ld/LdWf.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdWfProofs
import Cb.Ld.LdPscZk
import Ior.KnowCollPiece

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.LdLkp IOR.Chain
open scoped ENNReal

namespace LdWfP
variable {E : Type} [Field E] [Fintype E] {C : ConfigurationWithOutOfDomainSample} {P : LdWfP E C}

/-! ### Rounds, probabilities -/

theorem cLkp_nums (B : P.Blk) :
    ∀ l,
      (B.cLkp l).nAll = 2 + ∑ j ∈ Finset.range (l + 1), (B.sub j).R.shape.nAll ∧
      (B.cLkp l).nVer = (P.S.sh P.Sd).nVer + ∑ j ∈ Finset.range (l + 1), (B.sub j).R.shape.nVer ∧
      (B.cLkp l).pBad = ∑ j ∈ Finset.range (l + 1), (B.sub j).P.pBad ∧
      (B.cLkp l).pHid = ∑ j ∈ Finset.range (l + 1), (B.sub j).P.pHid
  | 0 => by
      rw [cLkp_zero, nAll_snoc, nVer_snoc, pBad_snoc, pHid_snoc, nAll_one,
        nVer_one, pBad_one, pHid_one]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_zero, Finset.sum_range_zero,
        Finset.sum_range_zero, Finset.sum_range_zero]
      refine ⟨?_, ?_, rfl, rfl⟩
      · show 2 + (B.sub 0).R.shape.nAll = 2 + (0 + (B.sub 0).R.shape.nAll)
        rw [Nat.zero_add]
      · show (P.S.sh P.Sd).nVer + (B.sub 0).R.shape.nVer =
          (P.S.sh P.Sd).nVer + (0 + (B.sub 0).R.shape.nVer)
        rw [Nat.zero_add]
  | l + 1 => by
      obtain ⟨h1, h2, h3, h4⟩ := cLkp_nums B l
      rw [cLkp_succ, nAll_snoc, nVer_snoc, pBad_snoc, pHid_snoc, h1, h2, h3, h4,
        Finset.sum_range_succ _ (l + 1), Finset.sum_range_succ _ (l + 1),
        Finset.sum_range_succ _ (l + 1), Finset.sum_range_succ _ (l + 1)]
      exact ⟨Nat.add_assoc _ _ _, Nat.add_assoc _ _ _, rfl, rfl⟩

/-! ### Errors -/

theorem err_snoc {K : Type} {A B D : Joint K} (c : Chain K A B) (l : Link K B D) (d : A.W) :
    ((c.snoc l).link d).P.err.list = (c.link d).P.err.list ++ l.P.err.list := by
  rw [link_snoc]
  exact Err.list_app _ _

theorem cLkp_err (B : P.Blk) :
    ∀ l, ((B.cLkp l).link B.p0).P.err.list =
      [ldSendFamErr P.S P.Sd B.L, 0] ++ (List.range (l + 1)).flatMap fun j => (B.sub j).P.err.list
  | 0 => by
      rw [cLkp_zero, err_snoc, link_one]
      simp only [List.range_succ, List.range_zero, List.nil_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
      rfl
  | l + 1 => by
      rw [cLkp_succ, err_snoc, cLkp_err B l, List.range_succ (n := l + 1),
        List.flatMap_append, List.append_assoc]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rfl

end LdWfP

section
variable (E : Type) [Field E] [Fintype E]

theorem ldWf_rounds : Spec.ldWf_rounds E := by
  intro C P B
  obtain ⟨h1, h2, _, _⟩ := chain_nums Unit _ _ B.chain B.p0
  obtain ⟨g1, g2, _, _⟩ := LdWfP.cLkp_nums B P.n
  have e1 : B.chain.nAll = (B.cLkp P.n).nAll + P.lBatt.R.shape.nAll := nAll_snoc _ _
  have e2 : B.chain.nVer = (B.cLkp P.n).nVer + P.lBatt.R.shape.nVer := nVer_snoc _ _
  refine ⟨h1.trans ?_, h2.trans ?_⟩
  · rw [e1, g1]
    exact congrArg _ (batt_len E P.bt C.E0)
  · rw [e2, g2]
    rfl

theorem ldWf_err : Spec.ldWf_err E := by
  intro C P B
  show (((B.cLkp P.n).snoc P.lBatt).link B.p0).P.err.list = _
  rw [LdWfP.err_snoc, LdWfP.cLkp_err B P.n]
  rfl

theorem ldWf_prob : Spec.ldWf_prob E := by
  intro C P B
  obtain ⟨_, _, h3, h4⟩ := chain_nums Unit _ _ B.chain B.p0
  obtain ⟨_, _, g3, g4⟩ := LdWfP.cLkp_nums B P.n
  have e3 : B.chain.pBad = (B.cLkp P.n).pBad + P.lBatt.P.pBad := pBad_snoc _ _
  have e4 : B.chain.pHid = (B.cLkp P.n).pHid + P.lBatt.P.pHid := pHid_snoc _ _
  have z3 : P.lBatt.P.pBad = 0 := add_zero (0 : ℝ≥0∞)
  have z4 : P.lBatt.P.pHid = 0 := add_zero (0 : ℝ≥0∞)
  refine ⟨h3.trans ?_, h4.trans ?_⟩
  · rw [e3, g3, z3, add_zero]
  · rw [e4, g4, z4, add_zero]

theorem ldWf_masks : Spec.ldWf_masks E := by
  classical
  intro C P B nm h
  have hB : Fintype.card B.DmB.Mk = Fintype.card E ^ (P.k * P.deg + 1) := by
    have e : Fintype.card B.DmB.Mk = Fintype.card (PIdx P.bt.fmt → E) :=
      Fintype.card_congr (Equiv.refl _)
    rw [e, Fintype.card_fun, batt_own_card E P.bt]
    rfl
  rw [Fintype.card_prod, Fintype.card_pi, hB,
    pow_add (Fintype.card E) (∑ l ∈ Finset.range (P.n + 1), nm l), ← Finset.prod_pow_eq_pow_sum,
    ← Fin.prod_univ_eq_prod_range (fun l => Fintype.card E ^ nm l) (P.n + 1)]
  exact congrArg (· * _) (Finset.prod_congr rfl fun l _ => h l (Nat.le_of_lt_succ l.2))

end
end Cb
