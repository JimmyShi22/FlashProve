-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/BodyEnds.lean: THE TWO ENDS OF THE VALUES' CHAIN AT THE STATE BY INDEX
(Johnson/Prover/Link/BodyState.lean), and the OOD answers at the coding's own words. Small
statements and proofs: each is a rewriting.

  frontMem, muOf_front   the link's first state, at the two members' messages that hold the folds,
                         has frontMsg (FrontWhole.lean) as its message: so front_holds' end IS
                         stage_V_first's premise
  mainOf_muOf, maskOf_muOf   at a stage without a row variable: the last message's main row and mask
                         row, as BASE's law reads them (mainOf | maskOf, BaseClaim.lean), are the
                         state's two tables by index
  rec_cells              the sample map's own answers at the messages that hold a matrix
                         (Johnson/Flat/CodingCells.lean: cellWords) are each row's answers at the
                         polynomials of the words that the coding's encoder encodes

Not shown here. Nothing on a decision; nothing on soundness; nothing on what any entry discloses or
does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.BodyState
import Johnson.Prover.Link.FrontWhole
import Johnson.Prover.Link.FrontCoding
import Johnson.Prover.Link.BaseClaim

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Slice OnBytes.Flat Cb Cb.Ood

/-- The two members' messages that hold the folds. -/
def frontMem (S : Sz) (γ : Fin S.P.v → GE) (M₀ M₁ : (Fin S.P.v → Bool) → S.Co → GE)
    (fr : Bool → S.MJ → GE) : Bool → S.MJ → GE :=
  fun a => membMsg S (foldAll γ (if a then M₁ else M₀)) (fr a)

theorem muOf_front (S : Sz) (t : ℕ) (γ : Fin S.P.v → GE)
    (M₀ M₁ : (Fin S.P.v → Bool) → S.Co → GE) (fr : Bool → S.MJ → GE)
    (tN : Bool → ℕ → ℕ → GE) (φN ψN : ℕ → GE) :
    μOf (S.sg t) (firstPS S (frontMem S γ M₀ M₁ fr) tN φN ψN) = frontMsg S t γ M₀ M₁ fr :=
  muOf_first S t _ tN φN ψN

theorem mainOf_muOf (s : Sg) (P : PS) (hh : s.h = 0) (hg : s.g = 0) (j : ℕ) (hj : j < s.C.l) :
    mainOf s (μOf s P) j = P.tabM j := by
  unfold mainOf
  rw [dif_pos hj]
  show P.tabM (Sz.rowNo (fun _ : Fin (s.h + s.g) => false) + 2 ^ (s.h + s.g) * j) = _
  rw [rowNo_false, hh, hg]
  simp

theorem maskOf_muOf (s : Sg) (P : PS) (hh : s.h = 0) (j : ℕ) (hj : j < s.Z.l) :
    maskOf s (μOf s P) j = P.tabZ j := by
  unfold maskOf
  rw [dif_pos hj]
  show P.tabZ (Sz.rowNo (fun _ : Fin s.h => false) + 2 ^ s.h * j) = _
  rw [rowNo_false, hh]
  simp

theorem rec_cells (S : Sz) (Z : Sample GE S.En) (cut : ℕ) (N : MatrixNums)
    (M : Cells (S.toDecR Z cut) N) (η : PadsOf S cut) (tl : ℕ → List UInt64) (σ : Z.D)
    (r : (S.ixR Z).Row) (s : Z.S) :
    (S.ixR Z).ZR.val σ (honestMsgs S (cellWords S Z cut N M η)) (r, s) =
      ∑ j, Z.mat σ s j *
        honestPolys S (rowWords S (honestMsgs S (cellWords S Z cut N M η))) tl r
          ((S.ixR Z).pl j) := by
  rw [← rec_honest S Z _ tl σ r s, honestMsgs_rowWords]

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.frontMem
#print axioms Johnson.Prover.Link.muOf_front
#print axioms Johnson.Prover.Link.mainOf_muOf
#print axioms Johnson.Prover.Link.maskOf_muOf
#print axioms Johnson.Prover.Link.rec_cells
