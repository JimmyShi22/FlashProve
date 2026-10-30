-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/CodingCells.lean: HOW A MATRIX OF CELLS IS HELD BY A TABLE'S MESSAGES, WRITTEN, AND THE
DECODER'S LAW AT THE CLAIMS OF THE TWO SIZES: from the honest word and the honest record of a matrix
that holds an index the index decoder gives that matrix back. Definitions, statements and proofs.

Why. OnBytes/Flat/CodingHonest.lean writes the honest side of a stored table's configuration but for
one letter, holdW (the words that hold a matrix), and shows the decoder's law under the premise hmat
(these words hold the matrix). Here holdW is written for the matrices of Johnson/Flat/Claims.lean
(`Cells D N`, read off a decoded table by `cellsOf`), and hmat is shown for every matrix in range
(`VerifiableInference.OnPublicFiles.Flat.InRange`: the matrix holds an index).

Main names (namespace `OnBytes.Flat`).
  `PadsOf S cut`: the pads: a field element for each row and each entry from the cut on.
  `cellEntryAt`, `cellEntry`, `cellWords S Z cut N M η`: entry e of row number b is, before the cut,
    the first coordinate of the cell (e / 2^kLo, b 2^kLo + e % 2^kLo), or 0 where the matrix has no
    such cell; from the cut on, the pads. ON CHOICE, BY THE PRINT AT THE FOOT OF THIS FILE:
    `cellEntryAt`, which holds all of the text but the projection to a cell's first coordinate and
    is stated over the base field, is on [propext] alone. `cellEntry` and `cellWords` show
    `Classical.choice` there: their types name the extension field and the decoder's data. Through
    which constant it comes in is not traced.
  **`cellWords_mat`**: read back by `cellsOf`, the messages of these words are the matrix, if the
    matrix is in range and its cells fit a row's message before the pads.
  `codingCells S Z cut N pp req`: `codingHonest` at these words: a value of `Coding` at the claims
    `claimsLedgerOnAt` (Johnson/Top/H/TargetAtPolicy.lean), for every table pp of scales and policy.
  **`obj_decodes_cells`**: the decoder's law at `F.withProvers P`, for every F and P over that
    configuration, at every matrix in range.
  `obj_decodes_cells_full`, `obj_decodes_cells_small`: at the two sizes' decoders and matrices
    (`numsRef`; `numsSmall`): the one premise left is "in range".
  **`obj_decodes_index_full`**: there, at the matrix of every index of `Cm.Idx` (`Flat.matrixOf`,
    Johnson/Flat/ThreeFull.lean): no premise is left.
  `cells_differ`: two different matrices in range never have the same honest word and record.

WHO READS EACH LETTER (D: the index decoder; E: the honest side; -: nobody here).
- S, Z: D and E. cut: D (`cellsOf` reads no entry from the cut on) and E (where the pads begin).
- N (the matrix's rows, and the logarithm of its columns in one row of the table): D (`cellsOf`) and
  E (`cellEntry`): ONE letter in both.
- pp, req, X: the claim `Rel` alone: -.
- hfit, hcut: the matrix's cells fit before the cut, and the cut lies in the message. At the two
  sizes they are proved (`full_fits`, `small_fits`, Johnson/Flat/ClaimsSizes.lean).
- d, hd, he: as in OnBytes/Flat/CodingHonest.lean. F, P: -. η, ρ, s: under "for all".
NOTHING THAT A VERIFIER READS STANDS UNDER "THERE IS". `InRange M` is "there is an index that M
holds": a premise on the honest side's own matrix.

Limits.
- "In range" is a premise everywhere but in `obj_decodes_index_full`. That two indices have two
  matrices is not shown here. At the small example no matrix in range is named here.
- Out of range nothing is said, and two matrices that differ only in second or third coordinates of
  cells have the same words.
- That the programs lay a matrix so into their tables, or draw their pads so, is not said: no file
  of a program is compared here. The order of cells is that of `cellsOf`, which the decoder's side
  fixes.
- All limits of OnBytes/Flat/CodingHonest.lean stand: nothing on hiding, on a verifier, on
  soundness, on completeness; no commitment, no hash function.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Flat.CodingHonest
import Johnson.Top.H.TargetAtPolicy
import Johnson.Flat.ThreeFull
import Johnson.Flat.ClaimsSizes

set_option autoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Flat
open Iop Prob Cb Cb.Ood Blocks Hiop OnBytes.Slice Inst.Model VerifiableInference
open VerifiableInference.OnPublicFiles (numsRef)

/-- Entry e of row number b, of a matrix of rows × 2^(kLo + v) cells over the base field: v row
variables; l entries in a row's message, of which those from the cut on are pads. -/
def cellEntryAt (rows kLo v cut l : ℕ) (M : Fin rows → Fin (2 ^ (kLo + v)) → GF)
    (η : Fin (2 ^ v) → Fin (l - cut) → GF) (b e : ℕ) : UInt64 :=
  if e < cut then
    if h : e / 2 ^ kLo < rows ∧ b * 2 ^ kLo + e % 2 ^ kLo < 2 ^ (kLo + v) then
      OnBytes.Slice.ofF (M ⟨_, h.1⟩ ⟨_, h.2⟩)
    else 0
  else if h : b < 2 ^ v ∧ e - cut < l - cut then
    OnBytes.Slice.ofF (η ⟨b, h.1⟩ ⟨e - cut, h.2⟩)
  else 0

section
variable (S : Sz) (Z : Sample GE S.En) (cut : ℕ) (N : MatrixNums)

/-- The pads: a field element for each row and each entry of its message from the cut on. -/
abbrev PadsOf (S : Sz) (cut : ℕ) : Type := Fin (2 ^ S.P.v) → Fin (S.P.T.l - cut) → GF

/-- Entry e of row number b. -/
def cellEntry (M : Cells (S.toDecR Z cut) N) (η : PadsOf S cut) (b e : ℕ) : UInt64 :=
  cellEntryAt N.rows N.kLo S.P.v cut S.P.T.l (fun y c => (M y c).c0) η b e

/-- **A matrix as the words of a table's messages, pads laid in.** -/
def cellWords (M : Cells (S.toDecR Z cut) N) (η : PadsOf S cut) : ℕ → List UInt64 :=
  fun b => (List.range S.P.T.l).map (cellEntry S Z cut N M η b)

theorem cellWords_getD (M : Cells (S.toDecR Z cut) N) (η : PadsOf S cut) (b e : ℕ)
    (he : e < S.P.T.l) : (cellWords S Z cut N M η b).getD e 0 = cellEntry S Z cut N M η b e := by
  have hl : e < (cellWords S Z cut N M η b).length := by
    unfold cellWords
    rw [List.length_map, List.length_range]
    exact he
  rw [List.getD_eq_getElem _ _ hl]
  unfold cellWords
  rw [List.getElem_map, List.getElem_range]

/-- **The matrix that the held messages spell is the matrix, if it is in range** and its cells fit a
row's message before the pads (hfit, hcut). -/
theorem cellWords_mat (hfit : N.rows * 2 ^ N.kLo ≤ cut) (hcut : cut ≤ S.P.T.l)
    (M : Cells (S.toDecR Z cut) N) (hM : OnPublicFiles.Flat.InRange M) (η : PadsOf S cut) :
    cellsOf (S.toDecR Z cut) N (honestMsgs S (cellWords S Z cut N M η)) = M := by
  obtain ⟨idx, hS, -⟩ := hM
  funext y c
  have hK : 0 < 2 ^ N.kLo := Nat.two_pow_pos _
  have hy : y.val + 1 ≤ N.rows := y.isLt
  have hm : c.val % 2 ^ N.kLo < 2 ^ N.kLo := Nat.mod_lt _ hK
  have hlt : c.val % 2 ^ N.kLo + 2 ^ N.kLo * y.val < cut := by
    have h1 : 2 ^ N.kLo * (y.val + 1) ≤ 2 ^ N.kLo * N.rows := Nat.mul_le_mul_left _ hy
    rw [Nat.mul_add_one, Nat.mul_comm (2 ^ N.kLo) N.rows] at h1
    omega
  have he : c.val % 2 ^ N.kLo + 2 ^ N.kLo * y.val < (S.toDecR Z cut).T.l ∧
      c.val % 2 ^ N.kLo + 2 ^ N.kLo * y.val < (S.toDecR Z cut).cut :=
    ⟨lt_of_lt_of_le hlt hcut, hlt⟩
  unfold cellsOf
  rw [dif_pos he]
  show algebraMap GF GE (OnBytes.Slice.toF ((cellWords S Z cut N M η
    (Sz.rowNo (rowAt (S.toDecR Z cut).v (c.val / 2 ^ N.kLo)))).getD
      (c.val % 2 ^ N.kLo + 2 ^ N.kLo * y.val) 0)) = M y c
  have hq : c.val / 2 ^ N.kLo < 2 ^ (S.toDecR Z cut).v := by
    refine Nat.div_lt_of_lt_mul ?_
    rw [← pow_add]
    exact c.isLt
  have hr : Sz.rowNo (rowAt (S.toDecR Z cut).v (c.val / 2 ^ N.kLo)) = c.val / 2 ^ N.kLo := by
    unfold rowAt
    rw [rowNo_testBit, Nat.mod_eq_of_lt hq]
  rw [hr, cellWords_getD S Z cut N M η _ _ he.1]
  unfold cellEntry cellEntryAt
  rw [if_pos hlt]
  have e1 : (c.val % 2 ^ N.kLo + 2 ^ N.kLo * y.val) / 2 ^ N.kLo = y.val := by
    rw [Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt hm, Nat.zero_add]
  have e2 : c.val / 2 ^ N.kLo * 2 ^ N.kLo +
      (c.val % 2 ^ N.kLo + 2 ^ N.kLo * y.val) % 2 ^ N.kLo = c.val := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_mod]
    exact Nat.div_add_mod' _ _
  have hd : (c.val % 2 ^ N.kLo + 2 ^ N.kLo * y.val) / 2 ^ N.kLo < N.rows ∧
      c.val / 2 ^ N.kLo * 2 ^ N.kLo +
        (c.val % 2 ^ N.kLo + 2 ^ N.kLo * y.val) % 2 ^ N.kLo <
          2 ^ (N.kLo + (S.toDecR Z cut).v) := by
    rw [e1, e2]
    exact ⟨y.isLt, c.isLt⟩
  rw [dif_pos hd]
  have a1 : (⟨_, hd.1⟩ : Fin N.rows) = y := Fin.ext e1
  have a2 : (⟨_, hd.2⟩ : Fin (2 ^ (N.kLo + (S.toDecR Z cut).v))) = c := Fin.ext e2
  rw [a1, a2, OnBytes.Slice.toF_ofF]
  show algebraMap GF GE (M y c).c0 = M y c
  have hc : M y c = algebraMap GF GE ((idx.mat y.val c.val : ℤ) : GF) := by
    rw [hS y c, map_intCast]
  rw [hc]
  rfl

variable {X : Type} (pp : ScalesAndPolicy) (req : X → Instance ppref)

/-- **The honest side at the claims on a matrix of cells**: `codingHonest` at `cellWords`. -/
def codingCells : Coding (claimsLedgerOnAt (S.toDecR Z cut) N pp req) :=
  codingHonest S Z cut (claimsLedgerOnAt (S.toDecR Z cut) N pp req) (PadsOf S cut)
    (cellWords S Z cut N)

variable {d : ℕ}

/-- **The decoder's law at the claims on a matrix of cells**, at every three protocols F over the
configuration with the written honest side and all their honest provers P, at every matrix in range.
-/
theorem obj_decodes_cells (hd : HasDist S.ix.G d) (he : S.eM < d)
    (hfit : N.rows * 2 ^ N.kLo ≤ cut) (hcut : cut ≤ S.P.T.l)
    (F : Files (DecR.configurationOfStoredTable (claimsLedgerOnAt (S.toDecR Z cut) N pp req)
      (relationsAndEncodingOfClaims _ (codingCells S Z cut N pp req)))) (P : F.Provers)
    (M : Cells (S.toDecR Z cut) N) (hM : OnPublicFiles.Flat.InRange M)
    (r : (F.withProvers P).EncodingRandomness) (s : (F.withProvers P).OutOfDomainSeed) :
    (F.withProvers P).decodeIndex ((F.withProvers P).encodeIndex M r) ((F.withProvers P).recOf M r s) = some M :=
  obj_decodes S Z cut (claimsLedgerOnAt (S.toDecR Z cut) N pp req) (PadsOf S cut)
    (cellWords S Z cut N) hd he F P M hM (cellWords_mat S Z cut N hfit hcut M hM) r s

/-- **Two different matrices in range never have the same honest word and record.** -/
theorem cells_differ (hd : HasDist S.ix.G d) (he : S.eM < d)
    (hfit : N.rows * 2 ^ N.kLo ≤ cut) (hcut : cut ≤ S.P.T.l)
    (F : Files (DecR.configurationOfStoredTable (claimsLedgerOnAt (S.toDecR Z cut) N pp req)
      (relationsAndEncodingOfClaims _ (codingCells S Z cut N pp req)))) (P : F.Provers)
    (M M' : Cells (S.toDecR Z cut) N) (hM : OnPublicFiles.Flat.InRange M)
    (hM' : OnPublicFiles.Flat.InRange M') (hne : M ≠ M')
    (r r' : (F.withProvers P).EncodingRandomness) (s s' : (F.withProvers P).OutOfDomainSeed) :
    ¬ ((F.withProvers P).encodeIndex M r = (F.withProvers P).encodeIndex M' r' ∧
      (F.withProvers P).recOf M r s = (F.withProvers P).recOf M' r' s') :=
  fun h => hne (same_of_decodes (F.withProvers P) M M' r r' s s'
    (obj_decodes_cells S Z cut N pp req hd he hfit hcut F P M hM r s)
    (obj_decodes_cells S Z cut N pp req hd he hfit hcut F P M' hM' r' s') h.1 h.2)

end

/-! ## At the two sizes -/

/-- **At the full size's decoder and the full size's matrix**: the one premise left is "in range".
-/
theorem obj_decodes_cells_full {X : Type} (pp : ScalesAndPolicy) (req : X → Instance ppref)
    (F : Files (DecR.configurationOfStoredTable (claimsLedgerOnAt (frS.toDecR frZ 402653181) numsRef pp req)
      (relationsAndEncodingOfClaims _ (codingCells frS frZ 402653181 numsRef pp req)))) (P : F.Provers)
    (M : Cells (frS.toDecR frZ 402653181) numsRef) (hM : OnPublicFiles.Flat.InRange M)
    (r : (F.withProvers P).EncodingRandomness) (s : (F.withProvers P).OutOfDomainSeed) :
    (F.withProvers P).decodeIndex ((F.withProvers P).encodeIndex M r) ((F.withProvers P).recOf M r s) = some M :=
  obj_decodes_cells frS frZ 402653181 numsRef pp req OnBytes.K.Oracle.full_dist.1
    OnBytes.K.Oracle.full_dist.2 full_fits.1 full_fits.2 F P M hM r s

/-- **At the small example's decoder and matrix**: the one premise left is "in range". -/
theorem obj_decodes_cells_small {X : Type} (pp : ScalesAndPolicy) (req : X → Instance ppref)
    (F : Files (DecR.configurationOfStoredTable (claimsLedgerOnAt (srS.toDecR srZ 524285) numsSmall pp req)
      (relationsAndEncodingOfClaims _ (codingCells srS srZ 524285 numsSmall pp req)))) (P : F.Provers)
    (M : Cells (srS.toDecR srZ 524285) numsSmall) (hM : OnPublicFiles.Flat.InRange M)
    (r : (F.withProvers P).EncodingRandomness) (s : (F.withProvers P).OutOfDomainSeed) :
    (F.withProvers P).decodeIndex ((F.withProvers P).encodeIndex M r) ((F.withProvers P).recOf M r s) = some M :=
  obj_decodes_cells srS srZ 524285 numsSmall pp req OnBytes.K.Oracle.small_dist.1
    OnBytes.K.Oracle.small_dist.2 small_fits.1 small_fits.2 F P M hM r s

/-- **At the full size, at the matrix of every index: no premise is left.** `Flat.matrixOf i`
(Johnson/Flat/ThreeFull.lean): the casts of the entries of the index i, a matrix of the full size's
shape; it holds i (`Flat.holds_matrixOf`), so it is in range. -/
theorem obj_decodes_index_full {X : Type} (pp : ScalesAndPolicy) (req : X → Instance ppref)
    (F : Files (DecR.configurationOfStoredTable (claimsLedgerOnAt (frS.toDecR frZ 402653181) numsRef pp req)
      (relationsAndEncodingOfClaims _ (codingCells frS frZ 402653181 numsRef pp req)))) (P : F.Provers)
    (i : Cm.Idx) (r : (F.withProvers P).EncodingRandomness) (s : (F.withProvers P).OutOfDomainSeed) :
    (F.withProvers P).decodeIndex ((F.withProvers P).encodeIndex (OnPublicFiles.Flat.matrixOf i) r)
      ((F.withProvers P).recOf (OnPublicFiles.Flat.matrixOf i) r s) = some (OnPublicFiles.Flat.matrixOf i) :=
  obj_decodes_cells_full pp req F P (OnPublicFiles.Flat.matrixOf i)
    ⟨i, OnPublicFiles.Flat.holds_matrixOf i⟩ r s

end OnBytes.Flat

#print axioms OnBytes.Flat.cellEntryAt
#print axioms OnBytes.Flat.cellEntry
#print axioms OnBytes.Flat.cellWords
#print axioms OnBytes.Flat.cellWords_mat
#print axioms OnBytes.Flat.obj_decodes_cells
#print axioms OnBytes.Flat.cells_differ
#print axioms OnBytes.Flat.obj_decodes_cells_full
#print axioms OnBytes.Flat.obj_decodes_cells_small
#print axioms OnBytes.Flat.obj_decodes_index_full
