-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/At/FootW.lean: the records of the last stretch of a layers' sub-proof's own rounds, the
claims on the committed weights, with each claim in the form in which the library's merge takes it.

Cb/Pv/Lay/Weights.lean and Cb/Pv/Lay/WeightsFirst.lean state the stretch at letters: a claim has a
summand on the cube of the column bits. Blocks/MergeBlock.lean takes a tensor claim as a pair (γ, ε)
of coefficients on the rows and on the columns of the matrix: its value is the sum over the columns
c of ε(c) times the sum over the rows r of γ(r) W[r][c]. This file fills the summand from such a
pair: at a point z it is the multilinear extension of ε at z times that of the column sums at z.

Main names.
  FootW0: what stays free: the entries, how they are read as the matrix, the numbers of column bits,
    rows and claims, each claim's pair as a function of the state, the places of the mask entries.
  St7: what the stretch reads of the statement before it: four points, in the first group two more,
    the factor of the masks and what was shown.
  tval: a pair's value on a matrix. summand, summand_deg, summand_sum: the summand, its degree 2 in
    each variable, and its sum over the cube.
  FootW0.wt: the record. FootW0.wt_val: the value of claim a is the pair's value on the matrix plus
    the mask entry times the factor.
  FootW0.wf, FootW0.wf_lhs: the same for the first group, which has one claim more.

Limits. Which pairs the claims of a layers' sub-proof have, and that a pair's value is the library's
value of the tensor claim (Pan.TnRow, Pan.TnPan in Inst/Model/FF/Objects.lean), is not said here.
That the programs' summands are these is not said. Nothing on an honest prover, on completeness or
on hiding.


-/
import Cb.Pv.Lay.WeightsFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay.At
open Iop Prob Cb IOR Finset TWhole

noncomputable section

/-! ### A claim's summand -/

section Summand
variable {E : Type} [Field E] {h k : ℕ}

/-- The value of the pair (γ, ε) on the matrix W. -/
def tval (a : (Fin h → E) × ((Fin k → Bool) → E)) (W : Fin h → (Fin k → Bool) → E) : E :=
  ∑ c, a.2 c * ∑ r, a.1 r * W r c

/-- The summand of the pair (γ, ε) on the matrix W, at a point of the column bits. -/
def summand (a : (Fin h → E) × ((Fin k → Bool) → E)) (W : Fin h → (Fin k → Bool) → E)
    (z : Fin k → E) : E :=
  Alg.mle a.2 z * Alg.mle (fun c => ∑ r, a.1 r * W r c) z

theorem summand_deg (a : (Fin h → E) × ((Fin k → Bool) → E)) (W : Fin h → (Fin k → Bool) → E) :
    Alg.DegLE (fun _ : Fin k => 2) (summand a W) :=
  (Alg.DegLE.mul (Alg.DegLE.mle a.2) (Alg.DegLE.mle fun c => ∑ r, a.1 r * W r c)).mono
    fun _ => le_refl _

theorem summand_sum (a : (Fin h → E) × ((Fin k → Bool) → E)) (W : Fin h → (Fin k → Bool) → E) :
    ∑ b : Fin k → Bool, summand a W (Alg.corner b) = tval a W := by
  unfold summand tval
  exact sum_congr rfl fun b _ => by rw [Alg.mle_corner, Alg.mle_corner]

end Summand

/-! ### What stays free -/

/-- What the stretch reads of the statement before it. -/
structure St7 (E : Type) (n : ℕ) where
  /-- the earlier sumcheck's output point; the lookup's point; the second token sumcheck's -/
  zeta : ℕ → E
  z : ℕ → E
  zh : ℕ → E
  /-- the lookup's point as the panels that come in late read it -/
  zl : ℕ → E
  /-- in the first group: the embedding's point inside a block and at the positions; its point on
  the blocks. In a later group nothing reads them. -/
  pa : ℕ → E
  pb : ℕ → E
  /-- in the first group: the request's tokens, by position -/
  tok : ℕ → ℕ
  /-- the factor of the masks; what was shown -/
  be : E
  v : Fin n → E

/-- The letters of the stretch that stay free. -/
structure FootW0 (E : Type) [Field E] [Fintype E] where
  /-- the entries -/
  J : Type
  [finJ : Fintype J]
  /-- the column bits, the rows, the claims -/
  k : ℕ
  h : ℕ
  n : ℕ
  /-- how the entries are read as the matrix -/
  Wm : (J → E) → Fin h → (Fin k → Bool) → E
  /-- a claim's coefficients on the rows and on the columns -/
  ten : Fin n → St7 E n → (Fin h → E) × ((Fin k → Bool) → E)
  /-- the mask entries of the claims' values -/
  nm : Fin n → J
  /-- the sumcheck's own masks -/
  wAt : PIdx (ldPartFmt E k (fun _ => 2) ++ [pDummy E 1]) → J
  cAt : J

attribute [instance] FootW0.finJ

variable {E : Type} [Field E] [Fintype E]

namespace FootW0
variable (P : FootW0 E)

/-- The stretch, at the value. -/
def wt : WeightsL E where
  J := P.J
  k := P.k
  n := P.n
  St := St7 E P.n
  fa := fun a st m => summand (P.ten a st) (P.Wm m)
  deg := fun a st m => summand_deg (P.ten a st) (P.Wm m)
  nm := P.nm
  be := fun _ st => st.be
  sh := fun a st => st.v a
  wAt := P.wAt
  cAt := P.cAt
  Rd := fun _ _ => True

/-- The value of claim a. -/
theorem wt_val (st : St7 E P.n) (m : P.J → E) (a : Fin P.n) :
    P.wt.val st m a = tval (P.ten a st) (P.Wm m) + m (P.nm a) * st.be := by
  unfold WeightsL.val
  show ∑ b : Fin P.k → Bool, summand (P.ten a st) (P.Wm m) (Alg.corner b) + _ = _
  rw [summand_sum]
  rfl

/-- The stretch of the first group, at the value. tenE: the pair of the claim that the first group
adds; rhs: the other side of its identity; mkE: the mask entry of the scalar that is sent. -/
def wf (tenE : St7 E P.n → (Fin P.h → E) × ((Fin P.k → Bool) → E))
    (rhs : St7 E P.n → (P.J → E) → E) (mkE : P.J) : WFirstL E where
  toWeightsL := P.wt
  fe := fun st m => summand (tenE st) (P.Wm m)
  dege := fun st m => summand_deg (tenE st) (P.Wm m)
  rhs := rhs
  mkE := mkE

/-- The left side of the first group's identity. -/
theorem wf_lhs (tenE : St7 E P.n → (Fin P.h → E) × ((Fin P.k → Bool) → E))
    (rhs : St7 E P.n → (P.J → E) → E) (mkE : P.J) (st : St7 E P.n) (m : P.J → E) :
    (P.wf tenE rhs mkE).lhs st m = tval (tenE st) (P.Wm m) := by
  unfold WFirstL.lhs
  show ∑ b : Fin P.k → Bool, summand (tenE st) (P.Wm m) (Alg.corner b) = _
  rw [summand_sum]

end FootW0

end

end Cb.Pv.Lay.At
