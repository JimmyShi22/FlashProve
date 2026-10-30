-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FrontSrc.lean: the seven clauses of Johnson/Prover/Link/FrontRows.lean AT A
MESSAGE THAT HOLDS THE TWO TABLES' FOLDS. Statements and proofs, in the library's typed terms.

  Src t x μ M₀ M₁   where the message comes from. M₀, M₁: the two tables, each row's FULL message
                    (the polynomial's coefficients: tail, then message). γ := the point in x.
      free   μ is 0 on the rows that no member has
      sm     each member's share has the sample's answer that stands in x
      at0 | at1    μ holds, at the places putAt, the fold at γ of the table's rows
      rec0 | rec1  the OOD sample in x holds each row's OOD answers at its OOD seed
      col0 | col1  what x holds as read at a drawn location is the fold at γ of the rows' code
                   words' symbols there
      same   the two tables' message parts agree on the entries that are compared
  frontTrue_of_src  Src ⟹ FrontTrue
  holds_of_src      so, with IsRowsR and Covers: (Slf.idf).Holds (sumStmR N t tg vs θ) μ at every θ

By: LdIx.mulVec_foldAll (Cb/Ld/LdFoldEqProofs.lean) · foldAll_apply (Cb/Gen/FoldWordsProofs.lean) ·
ldLk_complete (Cb/Ld/LdLinkWordsProofs.lean: on plain vectors) · sums swapped.

Not shown here. That any prover's written message, or any statement that a verifier holds, meets
Src. Nothing on a decision, a view, a file or a hash function; nothing on soundness; nothing on what
any entry of a message discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FrontRows
import Cb.Ld.LdLinkWordsProofs

set_option autoImplicit false

namespace Johnson.Prover.Link
open OnBytes.Slice Cb Cb.Ood Iop Run

variable {S : Sz} {Z : Sample GE S.En}

/-- **Where the message comes from.** General in S. at0 | at1 speak at every k : S.Co. Sz asks t0 +
T.r ≤ R * C.l (fitT), not <: where 0 < T.r and t0 + T.r = R * C.l, S.putAt of the tail's last
coefficient is S.padJ, and at0 | at1 then fix μ there. Likewise where T.r = 0 and T.l = R * C.l, of
the message's last coefficient. No clause bars either shape. -/
structure Src (t : ℕ) (x : (S.lkR Z).X4) (μ : (S.sg t).cIn.J → GE)
    (M₀ M₁ : (S.ixR Z).Row → S.Co → GE) : Prop where
  free : FreeZero S t μ
  sm : ∀ a : Bool, ∑ j, (S.fam.om a).Z.mat (x.1.1.2 a).1 () j * μ (atJ S t a j) = (x.1.1.2 a).2 ()
  at0 : ∀ k, μ (atJ S t false (S.putAt k)) = foldAll x.1.1.1.2 M₀ k
  at1 : ∀ k, μ (atJ S t true (S.putAt k)) = foldAll x.1.1.1.2 M₁ k
  rec0 : ∀ r s, x.1.1.1.1.1.2 (r, s) = ∑ j, Z.mat x.1.1.1.1.1.1 s j * M₀ r ((S.ixR Z).pl j)
  rec1 : ∀ r s, x.1.1.1.1.2.2 (r, s) = ∑ j, Z.mat x.1.1.1.1.2.1 s j * M₁ r ((S.ixR Z).pl j)
  col0 : ∀ i, x.1.2.1.2 i =
    foldAll x.1.1.1.2 (fun r => (S.ixR Z).G.mulVec (M₀ r)) (x.1.2.1.1 i)
  col1 : ∀ i, x.1.2.2.2 i =
    foldAll x.1.1.1.2 (fun r => (S.ixR Z).G.mulVec (M₁ r)) (x.1.2.2.1 i)
  same : (S.lwR Z).SameOn ((S.ixR Z).view M₀) ((S.ixR Z).view M₁)

/-- An OOD sample's row at the fold. -/
theorem rec_fold (X : LdIx GE S.Pos S.Co S.En) (rec : X.Rec) (γ : Fin X.v → GE)
    (M : X.Row → S.Co → GE)
    (h : ∀ r s, rec.2 (r, s) = ∑ j, X.Z.mat rec.1 s j * M r (X.pl j)) (s : X.Z.S) :
    ∑ j, X.Z.mat rec.1 s j * foldAll γ M (X.pl j) = X.tgt rec γ s := by
  unfold LdIx.tgt
  simp only [foldAll_apply, Alg.mle, h, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun j _ => by ring

/-- **The seven clauses of FrontTrue.** -/
theorem frontTrue_of_src (t : ℕ) (x : (S.lkR Z).X4) (μ : (S.sg t).cIn.J → GE)
    (M₀ M₁ : (S.ixR Z).Row → S.Co → GE) (h : Src t x μ M₀ M₁) : FrontTrue t x μ where
  free := h.free
  sm := h.sm
  rc0 := fun s => by
    simp only [h.at0]
    exact rec_fold (S.ixR Z) x.1.1.1.1.1 x.1.1.1.2 M₀ h.rec0 s
  rc1 := fun s => by
    simp only [h.at1]
    exact rec_fold (S.ixR Z) x.1.1.1.1.2 x.1.1.1.2 M₁ h.rec1 s
  c0 := fun i => by
    simp only [h.at0]
    rw [h.col0 i, ← (S.ixR Z).mulVec_foldAll M₀ x.1.1.1.2]
    rfl
  c1 := fun i => by
    simp only [h.at1]
    rw [h.col1 i, ← (S.ixR Z).mulVec_foldAll M₁ x.1.1.1.2]
    rfl
  eq := by
    simp only [h.at0, h.at1]
    exact (ldLk_complete (S.lwR Z) M₀ M₁ x.1.1.1.2 x.2 h.same).2

/-- **The rows' sum holds at the folds, at every θ.** -/
theorem holds_of_src (N : RowNo S Z) (t : ℕ) (x : (S.lkR Z).X4) (tg : ℕ → GE)
    (vs : ℕ → (S.sg t).cIn.J → GE) (hr : IsRowsR S Z t N x tg vs) (hN : Covers N)
    (μ : (S.sg t).cIn.J → GE) (M₀ M₁ : (S.ixR Z).Row → S.Co → GE) (h : Src t x μ M₀ M₁) (θ : GE) :
    (Slf.idf (E := GE) (J := (S.sg t).cIn.J)).Holds (sumStmR N t tg vs θ) μ :=
  holds_sumStmR N t x tg vs hr hN μ (frontTrue_of_src t x μ M₀ M₁ h) θ

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.Src
#print axioms Johnson.Prover.Link.rec_fold
#print axioms Johnson.Prover.Link.frontTrue_of_src
#print axioms Johnson.Prover.Link.holds_of_src
