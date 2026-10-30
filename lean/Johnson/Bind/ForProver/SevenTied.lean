-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/SevenTied.lean: AT THE PACKING OF A MATRIX, THE THREE TERMS OF
Johnson/Bind/ForProver/SevenAt.lean (`strAt`, `recAt`, `polysAt`) ARE THE LIBRARY'S OWN ENCODING,
OOD SAMPLE AND HONEST POLYNOMIALS AT THE GOALS' INPUT THAT IS MADE OF THE FRAME'S BY `cellsOfF` AND
`qOf`. LAWS ON THE MAPS OF THE TIE. Statements and proofs; general in the sizes.

Why. The library pays the seven clauses of the link's relation at its typed encoder
(`FlashProve.meant_obj`, Johnson/Goal/Conditions/LinkMeant.lean); `seven_at_ours` pays them at the
stand-in committer's columns. These equations say that the two payments are one where the plain
entries are the packing of a matrix: each term of the one is the like term of the other. Two inputs
are spoken of below: the goals' (a matrix of cells, pads and tails on finite ranges: what the
library's typed encoder takes) and the frame's (functions of two plain numbers: what the frame for
an honest prover hands out).

Main names (namespace `Bind.ForProver`).
   **`strAt_tied`**: under `Bind.Column.Agree sh S cut` and hfit: `strAt` at the packing of w and
      the coins ρ is the library's table of code words at the words of `cellsOfF` of w under the
      pads and tails `qOf` of ρ: the right side is what `FlashProve.enc_obj` writes out.
   **`recAt_tied`**: and `recAt` is the seed with the sample map's answers at these words' messages:
      the right side is what `FlashProve.recW_obj` writes out.
   `enc_tied`, `recOf_tied`: the same two with the object's own `encodeIndex` and `recOf` on the right: at
      all three protocols over the written honest side and all their provers: pp and req stand in
      F's type alone; F and P stand on the right sides in `(F.withProvers P)`; the proofs are the two laws
      above, whose right sides name none of the four; at the full size `FlashProve.meant_home` fills
      them.
   The third term: `polysOf_eq_polysAt` (Johnson/Bind/ForProver/Polys.lean).
Limits. EVERY STATEMENT HERE HOLDS AT AN INPUT OF THE GOALS' TYPE THAT IS MADE OF THE FRAME'S BY TWO
DEFINITIONS (`cellsOfF`, Johnson/Bind/ForProver/CellsInField.lean; `qOf`,
Johnson/Bind/ForProver/PolysAt.lean); THAT THE HONEST PROVER'S INPUT AT THE PROTOCOL IS SO MADE IS
SAID BY NO FILE BENEATH THIS ONE. THE LAWS FOR THE OTHER DIRECTION, IN WHICH THE FRAME'S READERS ARE
MADE OF THE GOALS' INPUT, HOLD AT EVERY MATRIX OF CELLS, not only at those that `cellsOfF` makes:
Johnson/Bind/ForProver/SevenReaders.lean, which spends this file's. `strAt_tied` is `words_typed`
(Johnson/Bind/ForProver/LawsSizes.lean) without the letters of the three protocols. The matrix w is
a letter: an index's or not. `Agree` and hfit are premises; at the full size they are theorems
without premises (`Bind.Column.agree_full`, Johnson/Bind/ColumnSizes.lean; `full_fits`,
Johnson/Flat/ClaimsSizes.lean). `seven_at_ours` and `meant_ours` do not rest on this file. One
committed table; which of the protocol's tables it is, the first or a copy, is not said here. No
hash function, no query, no coin's law. This file writes no honest prover. Nothing on completeness,
on index privacy, on soundness or on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.SevenAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Bind.ForProver
open Prob Cb Cb.Ood Blocks Hiop OnBytes.Slice OnBytes.Flat Inst.Model VerifiableInference
open Iop hiding Shape
open ProofFile.Honest (TableRand)
open Bind.Twin (Shape)
open Bind.Column (Agree)

section
variable {S : Sz} {Zs : Cb.Ood.Sample GE S.En} {cut : ℕ} {N : MatrixNums} {sh : Shape}

/-- **The stored string at the packing of a matrix is the library's table of code words at the
goals' input made of the frame's.** A law on the maps of the tie (`cellsOfF`, `qOf`); that the
honest prover's input at the protocol is so made is said by no file beneath this one. -/
theorem strAt_tied (h : Agree sh S cut) (hfit : N.rows * 2 ^ N.kLo ≤ cut) (w : ℕ → ℕ → GF)
    (ρ : TableRand) :
    strAt S sh (entryAtF N.kLo N.rows S.P.v w) ρ =
      honestTab S
        (rowWords S (honestMsgs S (cellWords S Zs cut N (cellsOfF S Zs cut N w) (qOf S cut ρ).1)))
        (tailWords S (qOf S cut ρ).2) := by
  funext x
  have hx : x.val < 2 ^ sh.a := by
    rw [h.a]
    exact x.isLt
  have k := honestAt_wordsTable (Z := Zs) (N := N) h w ρ.pad ρ.tail (fun _ => ByteArray.empty) x
  rw [wordsTable_eq hfit] at k
  unfold Bind.Column.honestAt at k
  simp only [OnBytes.Slice.toF_ofF] at k
  unfold strAt encAt
  rw [if_pos hx, Option.getD_some, words_columnOf]
  exact k.symm

/-- **The typed OOD sample at the packing of a matrix is the library's at the goals' input made of
the frame's.** A law on the maps of the tie; that the honest prover's input at the protocol is so
made is said by no file beneath this one. -/
theorem recAt_tied (h : Agree sh S cut) (hfit : N.rows * 2 ^ N.kLo ≤ cut) (w : ℕ → ℕ → GF)
    (ρ : TableRand) (σ : Zs.D) :
    recAt S Zs sh (entryAtF N.kLo N.rows S.P.v w) ρ σ =
      (σ, (S.ixR Zs).ZR.val σ
        (honestMsgs S (cellWords S Zs cut N (cellsOfF S Zs cut N w) (qOf S cut ρ).1))) := by
  have e : (S.ixR Zs).view (polysAt S sh (entryAtF N.kLo N.rows S.P.v w) ρ) =
      honestMsgs S (cellWords S Zs cut N (cellsOfF S Zs cut N w) (qOf S cut ρ).1) := by
    rw [← polysOf_eq_polysAt (Zs := Zs) h hfit w ρ]
    exact (OnBytes.Slice.view_honestPolys S _ _).trans (OnBytes.Flat.honestMsgs_rowWords S _)
  exact congrArg (fun u => (σ, (S.ixR Zs).ZR.val σ u)) e

variable {X : Type} (pp : Inst.Model.ScalesAndPolicy) (req : X → Inst.Model.Instance Inst.Model.ppref)
  (F : Files (DecR.configurationOfStoredTable (claimsLedgerOnAt (S.toDecR Zs cut) N pp req)
    (relationsAndEncodingOfClaims _ (codingCells S Zs cut N pp req)))) (P : F.Provers)

/-- The first, with the object's own encoder on the right. The letters pp and req stand in F's type
alone; F and P stand on the right side in `(F.withProvers P).encodeIndex`. A law on the maps of the tie. -/
theorem enc_tied (h : Agree sh S cut) (hfit : N.rows * 2 ^ N.kLo ≤ cut) (w : ℕ → ℕ → GF)
    (ρ : TableRand) :
    strAt S sh (entryAtF N.kLo N.rows S.P.v w) ρ =
      (F.withProvers P).encodeIndex (cellsOfF S Zs cut N w) (qOf S cut ρ) :=
  strAt_tied (Zs := Zs) h hfit w ρ

/-- The second, with the object's own sample on the right. A law on the maps of the tie. -/
theorem recOf_tied (h : Agree sh S cut) (hfit : N.rows * 2 ^ N.kLo ≤ cut) (w : ℕ → ℕ → GF)
    (ρ : TableRand) (σ : Zs.D) :
    recAt S Zs sh (entryAtF N.kLo N.rows S.P.v w) ρ σ =
      (F.withProvers P).recOf (cellsOfF S Zs cut N w) (qOf S cut ρ) σ :=
  recAt_tied (Zs := Zs) h hfit w ρ σ

end

end Bind.ForProver

end

#print axioms Bind.ForProver.strAt_tied
#print axioms Bind.ForProver.recAt_tied
#print axioms Bind.ForProver.enc_tied
#print axioms Bind.ForProver.recOf_tied
