--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/Values.lean: the equations of the linear claim's shared rounds hold at the
data that an honest prover lays into the two vectors of these rounds (uHon and omegaHon:
Johnson/Desc/K14/Honest/Moves.lean).

The committed table has rows under one code. Rw r is row r before encoding, laid out as the folded
row is: its message (pads among it) at the places below ell, its random tail from the place
tailFirst on. That is the convention of Johnson/Desc/K14/Law/NearRows.lean and HonestRows.lean. The
verifier has sampled gamma, which gives a weight w r for each row. The folded row holds, place by
place, the sum of w r times row r. The second vector, omega_col, has one entry for each row of the
matrix that the committed table holds.

  IsFold          a vector holds the rows' fold at the message's places and at the tail's
  uHon_isFold, omegaHon_row   the two vectors at the places that the equations read. No theorem
                  here reads them at another place. Beyond the last place of a row uHon is 0, a
                  placeholder. BETWEEN THE MESSAGE's END AND tailFirst, where these two differ,
                  uHon holds the fold of whatever Rw has there: a caller's Rw is 0 there
  RowAnswer       one row's own answer to the out-of-domain (OOD) sample, as an equation; the same
                  equation, by numbers, is the premise h of hrec_of_rows (HonestRows.lean)
  recEq_of_isFold, foldEq_of_col   RecEq and FoldEq (Johnson/Desc/K14/Law/LawRL.lean, Base.lean) at
                  such vectors. The like for LocEq is locAt_of_rows (NearRows.lean)
  uIsFold_of_isFold, omegaIs_honest   omega_col is matOf of the rows, applied to the equality vector
                  at the shared point
  dotEq_honest    so the equation DotEq of the last chain's constraint (Dot) holds
                  (Johnson/Desc/K14/Law/DotCount.lean), if the other vector is the row weights
                  applied to matOf of the rows

What is assumed, as premises. RowAnswer of every row: to be shown by whoever makes the committed
table and its key. On public numbers: the pads fit a row's message; the answer's number is below the
number of answers; the matrix lies in front of the pads; psi_lo has kLo coordinates. The weights are
the equality vector's entries at gamma. In dotEq_honest: the other vector is the row weights applied
to matOf of the rows (hW).
What is not claimed. matOf (Johnson/Desc/K14/Law/OmegaTable.lean) is a definition: no lemma here
ties it to the program's layout of the table or to the matrix of which a request's claims speak. No
sub-protocol, round or decision stands in any statement of this file. Nothing on a verifier's
acceptance, on soundness or on hiding.

-/
import Johnson.Desc.K14.Honest.Moves
import Johnson.Desc.K14.Law.OmegaTable
import Johnson.Desc.K14.Law.PointGood
import Johnson.Desc.K14.Law.LawRL
import Johnson.Desc.K14.Law.Placed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open Desc.K14.Law

variable {K : Type} [Field K]

/-! ## What the two vectors hold -/

/-- The vector u holds the rows' fold at the places of a row's message and of its tail. -/
structure IsFold (S : FoldeqShape) (w : Nat → K) (Rw : Nat → Nat → K) (u : Nat → K) : Prop where
  onMsg : ∀ k < S.index.code.ell, u k = foldRows S.index.rows w Rw k
  onTail : ∀ j < S.index.code.r, u (S.tailFirst + j) = foldRows S.index.rows w Rw (S.tailFirst + j)

/-- The tails begin behind the messages. -/
theorem ell_le_tailFirst (S : FoldeqShape) : S.index.code.ell ≤ S.tailFirst :=
  le_roundUp _ _ (Nat.two_pow_pos _)

/-- The folded row holds the rows' fold. -/
theorem uHon_isFold (S : FoldeqShape) (w : Nat → K) (Rw : Nat → Nat → K) :
    IsFold S w Rw (uHon S w Rw) := by
  have h0 := ell_le_tailFirst S
  refine ⟨fun k hk => ?_, fun j hj => ?_⟩
  · have h1 : k < S.entries := by
      unfold FoldeqShape.entries
      omega
    unfold uHon
    rw [if_pos h1]
  · have h1 : S.tailFirst + j < S.entries := by
      unfold FoldeqShape.entries
      omega
    unfold uHon
    rw [if_pos h1]

/-- omega_col on the matrix's rows. -/
theorem omegaHon_row (S : LinShape) (psiLo : List K) (u : Nat → K) (j : Nat)
    (hj : j < S.matrixRows) :
    omegaHon S psiLo u j = ∑ t ∈ Finset.range (2 ^ S.kLo), eqK psiLo t * u (t + 2 ^ S.kLo * j) := by
  unfold omegaHon
  rw [if_pos hj]

/-! ## A linear form applied to a fold -/

/-- A linear form applied to a fold of rows is the fold of the form's values on the rows. -/
theorem sum_fold (n N : Nat) (w a : Nat → K) (g : Nat → Nat → K) :
    ∑ k ∈ Finset.range N, a k * ∑ r ∈ Finset.range n, w r * g r k =
      ∑ r ∈ Finset.range n, w r * ∑ k ∈ Finset.range N, a k * g r k := by
  calc ∑ k ∈ Finset.range N, a k * ∑ r ∈ Finset.range n, w r * g r k
      = ∑ k ∈ Finset.range N, ∑ r ∈ Finset.range n, w r * (a k * g r k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun r _ => by ring
    _ = ∑ r ∈ Finset.range n, ∑ k ∈ Finset.range N, w r * (a k * g r k) := Finset.sum_comm
    _ = ∑ r ∈ Finset.range n, w r * ∑ k ∈ Finset.range N, a k * g r k := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.mul_sum]

/-! ## (rec_gamma) -/

/-- One row's own answer number i to the out-of-domain sample: the equality vector at z in front of
the pads, and beta theta t on pad t of that answer; theta t: what X ^ t reads as. -/
def RowAnswer (s : IndexShape) (z : List K) (beta : K) (theta : Nat → K) (i : Nat) (row : Nat → K)
    (y : K) : Prop :=
  (∑ k ∈ Finset.range s.plain, eqK z k * row k) +
      ∑ t ∈ Finset.range 3, beta * theta t * row (s.padPlace i t) = y

/-- **(rec_gamma)'s equation holds at the fold**, if each row's answer is that row's own. -/
theorem recEq_of_isFold (S : FoldeqShape) (z : List K) (beta : K) (theta : Nat → K) (i : Nat)
    (w y u : Nat → K) (Rw : Nat → Nat → K) (hu : IsFold S w Rw u)
    (hp : S.index.pads ≤ S.index.code.ell) (hi : i < S.index.answers)
    (hR : ∀ r < S.index.rows,
      RowAnswer S.index z beta theta i (Rw r) (y (r * S.index.answers + i))) :
    RecEq S.index z beta theta i w y u := by
  have h1 : ∀ k ∈ Finset.range S.index.plain,
      eqK z k * u k = eqK z k * ∑ r ∈ Finset.range S.index.rows, w r * Rw r k := by
    intro k hk
    have hk' : k < S.index.code.ell :=
      lt_of_lt_of_le (Finset.mem_range.1 hk) (Nat.sub_le _ _)
    rw [hu.onMsg k hk']
    rfl
  have h2 : ∀ t ∈ Finset.range 3, beta * theta t * u (S.index.padPlace i t) =
      beta * theta t * ∑ r ∈ Finset.range S.index.rows, w r * Rw r (S.index.padPlace i t) := by
    intro t ht
    have ht' := Finset.mem_range.1 ht
    have hlt : S.index.padPlace i t < S.index.code.ell := by
      unfold IndexShape.pads at hp
      unfold IndexShape.padPlace IndexShape.plain IndexShape.pads
      omega
    rw [hu.onMsg _ hlt]
    rfl
  have e1 : ∑ k ∈ Finset.range S.index.plain,
        eqK z k * ∑ r ∈ Finset.range S.index.rows, w r * Rw r k =
      ∑ r ∈ Finset.range S.index.rows, w r * ∑ k ∈ Finset.range S.index.plain, eqK z k * Rw r k :=
    sum_fold S.index.rows S.index.plain w (eqK z) Rw
  have e2 : ∑ t ∈ Finset.range 3, beta * theta t *
        ∑ r ∈ Finset.range S.index.rows, w r * Rw r (S.index.padPlace i t) =
      ∑ r ∈ Finset.range S.index.rows,
        w r * ∑ t ∈ Finset.range 3, beta * theta t * Rw r (S.index.padPlace i t) :=
    sum_fold S.index.rows 3 w (fun t => beta * theta t) (fun r t => Rw r (S.index.padPlace i t))
  show (∑ k ∈ Finset.range S.index.plain, eqK z k * u k) +
      ∑ t ∈ Finset.range 3, beta * theta t * u (S.index.padPlace i t) =
    ∑ r ∈ Finset.range S.index.rows, w r * y (r * S.index.answers + i)
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, e1, e2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r hr => ?_
  have h := hR r (Finset.mem_range.1 hr)
  unfold RowAnswer at h
  rw [← h]
  ring

/-! ## (fold) -/

/-- **(fold)'s equation holds at every point z_fd**, if omega_col is what the folded row gives at
psi_lo, row by row of the matrix. -/
theorem foldEq_of_col (S : LinShape) (psiLo z : List K) (omega u : Nat → K)
    (h : ∀ j < S.matrixRows,
      omega j = ∑ t ∈ Finset.range (2 ^ S.kLo), eqK psiLo t * u (t + 2 ^ S.kLo * j)) :
    FoldEq S psiLo z omega u := by
  show (∑ j ∈ Finset.range S.matrixRows, eqK z j * omega j) =
    ∑ j ∈ Finset.range S.matrixRows, ∑ t ∈ Finset.range (2 ^ S.kLo),
      eqK psiLo t * eqK z j * u (t + 2 ^ S.kLo * j)
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [h j (Finset.mem_range.1 hj), Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => by ring

/-- (fold)'s equation at the honest omega_col. -/
theorem foldEq_honest (S : LinShape) (psiLo z : List K) (u : Nat → K) :
    FoldEq S psiLo z (omegaHon S psiLo u) u :=
  foldEq_of_col S psiLo z _ u fun j hj => omegaHon_row S psiLo u j hj

/-! ## omega_col is the matrix applied to the equality vector -/

/-- A vector that holds the fold with the equality vector's weights meets UIsFold
(Johnson/Desc/K14/Law/OmegaTable.lean), the form in which the law of the constraint (Dot) asks
it. -/
theorem uIsFold_of_isFold (S : LinShape) (gam : List K) (w u : Nat → K) (Rw : Nat → Nat → K)
    (hu : IsFold S.fold w Rw u) (hw : ∀ r < S.fold.index.rows, w r = eqK gam r)
    (hroom : S.matrixRows * 2 ^ S.kLo ≤ S.fold.index.plain) :
    UIsFold S.matrixRows S.kLo S.fold.index.v Rw gam u := by
  intro k hk
  have hk' : k < S.fold.index.code.ell :=
    lt_of_lt_of_le hk (Nat.le_trans hroom (Nat.sub_le _ _))
  rw [hu.onMsg k hk']
  show ∑ r ∈ Finset.range S.fold.index.rows, w r * Rw r k =
    ∑ r ∈ Finset.range S.fold.index.rows, eqK gam r * Rw r k
  exact Finset.sum_congr rfl fun r hr => by rw [hw r (Finset.mem_range.1 hr)]

/-- **The honest omega_col is matOf of the rows, applied to the equality vector at the shared point
(psi_lo, gamma).** -/
theorem omegaIs_honest (S : LinShape) (psiLo gam : List K) (w u : Nat → K) (Rw : Nat → Nat → K)
    (hp : psiLo.length = S.kLo) (hu : IsFold S.fold w Rw u)
    (hw : ∀ r < S.fold.index.rows, w r = eqK gam r)
    (hroom : S.matrixRows * 2 ^ S.kLo ≤ S.fold.index.plain) :
    OmegaIs S.matrixRows (S.kLo + S.fold.index.v) (matOf S.kLo Rw) (psiLo ++ gam)
      (omegaHon S psiLo u) :=
  omegaIs_of_col S.matrixRows S.kLo S.fold.index.v Rw psiLo gam _ u hp
    (fun y hy => omegaHon_row S psiLo u y hy) (uIsFold_of_isFold S gam w u Rw hu hw hroom)

/-- **(Dot)'s equation holds at the honest omega_col**, if the other vector is the row weights g
applied to matOf of the rows. -/
theorem dotEq_honest (S : LinShape) (psiLo gam : List K) (g w u W : Nat → K)
    (Rw : Nat → Nat → K) (hp : psiLo.length = S.kLo) (hu : IsFold S.fold w Rw u)
    (hw : ∀ r < S.fold.index.rows, w r = eqK gam r)
    (hroom : S.matrixRows * 2 ^ S.kLo ≤ S.fold.index.plain) (hW : VIs S g Rw W) :
    DotEq S.matrixRows S.kCol g (omegaHon S psiLo u) (psiLo ++ gam) W := by
  have hO := omegaIs_honest S psiLo gam w u Rw hp hu hw hroom
  have h1 : ∀ y ∈ Finset.range S.matrixRows, g y * omegaHon S psiLo u y =
      g y * ∑ c ∈ Finset.range (2 ^ S.kCol), eqK (psiLo ++ gam) c * matOf S.kLo Rw y c := by
    intro y hy
    rw [hO y (Finset.mem_range.1 hy)]
    rfl
  have h2 : ∀ c ∈ Finset.range (2 ^ S.kCol), eqK (psiLo ++ gam) c * W c =
      eqK (psiLo ++ gam) c * ∑ y ∈ Finset.range S.matrixRows, g y * matOf S.kLo Rw y c := by
    intro c hc
    rw [hW c (Finset.mem_range.1 hc)]
  show ∑ y ∈ Finset.range S.matrixRows, g y * omegaHon S psiLo u y =
    ∑ c ∈ Finset.range (2 ^ S.kCol), eqK (psiLo ++ gam) c * W c
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
  exact (sum_fold S.matrixRows (2 ^ S.kCol) g (eqK (psiLo ++ gam)) (matOf S.kLo Rw)).symm

end Desc.K14.Honest

#print axioms Desc.K14.Honest.ell_le_tailFirst
#print axioms Desc.K14.Honest.uHon_isFold
#print axioms Desc.K14.Honest.omegaHon_row
#print axioms Desc.K14.Honest.sum_fold
#print axioms Desc.K14.Honest.recEq_of_isFold
#print axioms Desc.K14.Honest.foldEq_of_col
#print axioms Desc.K14.Honest.foldEq_honest
#print axioms Desc.K14.Honest.uIsFold_of_isFold
#print axioms Desc.K14.Honest.omegaIs_honest
#print axioms Desc.K14.Honest.dotEq_honest
