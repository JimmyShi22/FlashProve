-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/ChainRuleProofs.lean: proofs of the statements of
Johnson/Desc/Sound/ChainRule.lean that follow from the library's own rules, and the two implications
that leave `FoldIsRow` as the one statement with new content.

Main names.
  `rowRule : RowRule`: by induction, with `KObj.BK.good_seq`.
  `shapeIsChain : ShapeIsChain`: by `uLT_append`.
  `pieceOfProved : PieceOfProved`: it is `know_carryS`.
  `pieceGood : PieceGood`: with `pointsT`, `stageIOR_isLocal`, `knowInto_of_carry`.
  `chainRule_of : FoldIsRow → ChainRule`. `chainRuleAt_of : ChainRule → ChainRuleAt`.

Limits: those of the sheet.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.ChainRule
import OnBytes.Flat.ShapesRow
import OnBytes.Maker.TreesLaws
import OnBytes.Maker.RowLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)

theorem rowRule : RowRule := by
  intro S Cl W C F on R d i p l
  induction l generalizing p i with
  | nil =>
    intro h
    exact h.1
  | cons q l ih =>
    intro h
    have k := BK.good_seq (p.bk (on i) (on (i + 1)) (R i) (R (i + 1))) _ d h.1 (ih (i + 1) q h.2)
    have e : i + 1 + 1 + l.length = i + 1 + (q :: l).length := by
      simp only [List.length_cons]
      omega
    rw [e] at k
    exact k

theorem shapeIsChain : ShapeIsChain := by
  intro S Cl W C F p l
  induction l generalizing p with
  | nil =>
    show uLT C p.ds = uLT C (rowData p [])
    simp [rowData]
  | cons q l ih =>
    show uLT C p.ds ++ (rowIOR q l).shape = uLT C (rowData p (q :: l))
    have e : rowData p (q :: l) = p.ds ++ rowData q l := by simp [rowData]
    rw [ih q, e, uLT_append]

theorem pieceOfProved : PieceOfProved := by
  intro S Cl W C F p Xp Yp Wp Wq Kp G δ rd on onp RA RB RAp RBp ep hF hon hyes hk
  exact know_carryS p.ior.red Kp G δ p.err hF rd on onp RA RB RAp RBp p.ext ep hon hyes hk

theorem pieceGood : PieceGood := by
  intro S Cl W C F p Xp Yp Wp Wq Kp G δ rd on on' onp RA RB RAp RBp ep hF hon hyes hcar hk
  exact ⟨⟨pointsT C p.ds⟩, stageIOR_isLocal C p.stage p.run,
    Iop.knowInto_of_carry _ _ _ _ p.ior.red on on' RA RB p.ext p.err hcar
      (pieceOfProved S Cl W C F p Xp Yp Wp Wq Kp G δ rd on onp RA RB RAp RBp ep hF hon hyes hk)⟩

theorem chainRule_of (hf : FoldIsRow) : ChainRule := by
  intro S Cl W C F name on R d p l h ht hg
  have k := (rowRule S Cl W C F on R d 0 p l hg).know
  rw [Nat.zero_add] at k
  intro a ha
  refine Iop.Doomed.mono _ _ ?_ (k a ha)
  intro τ hτ b w hb hw
  exact hτ b w ((hf S Cl W C F name p l h ht a τ).symm.trans hb) hw

theorem chainRuleAt_of (hc : ChainRule) : ChainRuleAt := by
  intro S Cl W C F name on R d c p l h e ht hg
  rw [← e]
  exact hc S Cl W C F name on R d p l h ht hg

end VerifiableInference.Desc.Sound
