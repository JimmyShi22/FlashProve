-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/LawsSizes.lean: THE ENCODED INDEX'S COLUMN FOR AN HONEST PROVER IS THE
LIBRARY'S TYPED ENCODER'S SYMBOL, WHERE SHAPE AND SIZES AGREE (`Bind.Column.Agree`) AND THE MATRIX'S
CELLS FIT BEFORE THE PADS (hfit). General in the sizes; then at a public part; then what is asked of
a public part at the two sizes that the library has. Definitions, statements and proofs.

Why. `encAt` and `encW` (Johnson/Bind/ForProver/Enc.lean) call the column of the stand-in committer
on byte strings (`Bind.Twin.commitW`, Johnson/Bind/Twin.lean). The library's own object over
`codingCells` (Johnson/Flat/CodingCells.lean) has a typed encoder, of which its theorems on decoding
speak. Johnson/Bind/ForProver/CellsInField.lean ties the two at letters. Here that is said in the
names that a prover's writer calls.

Main names (namespace `Bind.ForProver`).
  `entryAtF_intCast`: at a matrix of integers, cast into the field, the packing's word is the
    integer's least residue modulo the prime.
  `wordsTable_eq`: under hfit the table of words of CellsInField.lean is `tableOfRand` at
    `entryAtF`.
  `rowsFit_iff`: under `Bind.Column.Agree sh S cut` the test with code `rowsFit` passes just where
    the matrix's cells fit a row's message before the pads (hfit).
  **`encAt_typed`**: under `Agree` and hfit: at every position `encAt` gives the typed encoder's
    symbol's words, read in the field. **`words_typed`**: and the position's number with `encAt`'s
    column, written as words, IS the typed encoder's symbol.
  `numsOf`: the matrix's two numbers off a public part.
  **`encW_typed`**: the first of the two at a public part Z, the shape and the numbers read off Z.
  `ShapeAtFull`, `ShapeAtSmall`: what is asked of a public part: the shape and the numbers off it
    are those of the full size, or of the small stored example's size: all six numbers of the shape,
    which is more than `encW_typed` needs (`Agree` asks nothing of sigma). `paid_full`,
    `paid_small`: under them the two premises of `encW_typed` are paid.

Limits. `ShapeAtFull Z` AND `ShapeAtSmall Z` ARE PREMISES: each reads one field of Z
(Z.p.chains.made.sized.proof.batch.shape). Z ranges over ALL values of the structure `ProofFile.Pub`
(Johnson/Desc/ProofFile/Pub.lean), made of three public files or not. Nothing in this file shows a Z
that meets either. Elsewhere: at files in the goals' scope `ShapeAtFull Z` follows from "the maker
of the public part (`ProofFile.pubPlain`) returned Z" (`shapeAtFull_inScope`,
Johnson/Bind/ForProver/InScope.lean); that it returns at `OnBytes.secondHashFunction` the side library proves at
the library's written copies of the two stored sets, which are in scope (`okStart_zFull_whole`,
`okStart_zGap_whole`, AtFullSide/E2E/StartAtWrittenFiles.lean, by the field `pub` of `LaidAt`,
Johnson/P5J/LaidOpens.lean). No
theorem of this file ends in `ShapeAtSmall`. `paid_full` and `paid_small`, with `entryOfPub_full`,
`premises_full`, `premises_small`, `encW_full`, `words_full` and `column_decodes_at`
(Johnson/Bind/ForProver/JoinsSizes.lean), are theorems under them: a definition that nothing meets
would pass these; `shapeAtFull_inScope` would not. That no public part meets both is plain from the
numerals and is no theorem of this file. `Agree` and hfit are premises of the general forms. The
typed encoder's matrix is `cellsOfF` of the reader's matrix: that a reader's matrix is an index's is
not said here (Johnson/Bind/ForProver/JoinsSizes.lean). The letters X, pp and req stand in F's type
alone; F and P stand on the right sides in `(F.withProvers P).encodeIndex`, whose value hangs on none of the five
(`Bind.Column.encIsHonestTab`, Johnson/Bind/Column.lean); at the full size the description's own
files and provers are members of the general forms at `numsRef`, not of `encW_typed`, whose files
are typed at the numbers off Z (`words_full`, Johnson/Bind/ForProver/JoinsSizes.lean, stands at
`numsRef`); at the small size none is named. One committed table; which of the protocol's tables it
is, the first or a copy, is not said here. No hash function, no query and no salt is read. This file
writes no honest prover. No binding of the commitment (the opening form), no correctness of
extraction, no completeness, no index privacy; nothing on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.Laws
import Johnson.Bind.ForProver.CellsInField
import Johnson.Bind.ColumnSizes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Bind.ForProver
open Prob Cb Cb.Ood Blocks Hiop OnBytes.Slice OnBytes.Flat Inst.Model VerifiableInference
open Iop hiding Shape
open VerifiableInference.OnPublicFiles (numsRef)
open ProofFile.Honest (TableRand)
open Bind.Twin (Shape Table)
open Bind.Column (Agree)

/-- At a matrix of integers, cast into the field, the packing's word is the least residue. -/
theorem entryAtF_intCast (kLo rows v : ℕ) (mat : ℕ → ℕ → ℤ) (b e : ℕ) :
    entryAtF kLo rows v (fun y c => ((mat y c : ℤ) : GF)) b e =
      if e / 2 ^ kLo < rows ∧ b * 2 ^ kLo + e % 2 ^ kLo < 2 ^ (kLo + v) then
        UInt64.ofNat (mat (e / 2 ^ kLo) (b * 2 ^ kLo + e % 2 ^ kLo) % (Code.pGold : ℤ)).toNat
      else 0 := by
  unfold entryAtF
  rw [Bind.Column.ofF_intCast]

section
variable {S : Sz} {Z : Sample GE S.En} {cut : ℕ} {N : MatrixNums} {sh : Shape}

/-- Under hfit the table of words is `tableOfRand` at the packing. -/
theorem wordsTable_eq (hfit : N.rows * 2 ^ N.kLo ≤ cut) (w : ℕ → ℕ → GF) (ρ : TableRand) :
    wordsTable S Z cut N w ρ.pad ρ.tail (fun _ => ByteArray.empty) =
      tableOfRand (entryAtF N.kLo N.rows S.P.v w) ρ := by
  have e : cellEntry S Z cut N (cellsOfF S Z cut N w) (fun _ _ => 0) =
      entryAtF N.kLo N.rows S.P.v w :=
    funext fun b => funext fun e => cellEntry_cellsOfF S Z cut N hfit w b e
  unfold wordsTable Bind.Column.tableOf tableOfRand
  rw [e]

/-- Under `Agree` the test with code passes just where the matrix fits before the pads. -/
theorem rowsFit_iff (h : Agree sh S cut) (kLo rows : ℕ) :
    rowsFit sh kLo rows = true ↔ rows * 2 ^ kLo ≤ cut := by
  have hc : cut + 3 * sh.s = sh.l := h.cut
  have hp : sh.plain = cut := by
    show sh.l - 3 * sh.s = cut
    omega
  unfold rowsFit
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, hp]
  exact ⟨fun a => a.2, fun a => ⟨by omega, a⟩⟩

variable (X : Type) (pp : ScalesAndPolicy) (req : X → Instance ppref)
  (F : Files (DecR.configurationOfStoredTable (claimsLedgerOnAt (S.toDecR Z cut) N pp req)
    (relationsAndEncodingOfClaims _ (codingCells S Z cut N pp req)))) (P : F.Provers)

/-- **`encAt` gives the typed encoder's symbol's words, read in the field.** -/
theorem encAt_typed (h : Agree sh S cut) (hfit : N.rows * 2 ^ N.kLo ≤ cut) (w : ℕ → ℕ → GF)
    (ρ : TableRand) (x : S.Pos) :
    encAt sh (entryAtF N.kLo N.rows S.P.v w) ρ x.val =
      some (((F.withProvers P).encodeIndex (cellsOfF S Z cut N w)
        (fun b j => ρ.pad b.val j.val, fun b q => ρ.tail b.val q.val) x).2.map toF) := by
  have hx : x.val < 2 ^ sh.a := by
    rw [h.a]
    exact x.isLt
  rw [enc_wordsTable h w ρ.pad ρ.tail (fun _ => ByteArray.empty) X pp req F P x,
    wordsTable_eq hfit]
  unfold encAt
  rw [if_pos hx]

/-- **The position's number with `encAt`'s column, written as words, is the typed encoder's
symbol.** -/
theorem words_typed (h : Agree sh S cut) (hfit : N.rows * 2 ^ N.kLo ≤ cut) (w : ℕ → ℕ → GF)
    (ρ : TableRand) (x : S.Pos) :
    (x.val, ((encAt sh (entryAtF N.kLo N.rows S.P.v w) ρ x.val).getD []).map ofF) =
      (F.withProvers P).encodeIndex (cellsOfF S Z cut N w)
        (fun b j => ρ.pad b.val j.val, fun b q => ρ.tail b.val q.val) x := by
  have hx : x.val < 2 ^ sh.a := by
    rw [h.a]
    exact x.isLt
  rw [enc_wordsTable h w ρ.pad ρ.tail (fun _ => ByteArray.empty) X pp req F P x,
    wordsTable_eq hfit]
  unfold encAt
  rw [if_pos hx, Option.getD_some, words_columnOf]

end

/-! ## At a public part -/

/-- The matrix's two numbers, off the public part. -/
def numsOf (Z : ProofFile.Pub) : MatrixNums := ⟨(linOf Z).matrixRows, (linOf Z).kLo⟩

section
variable {S : Sz} {Zs : Sample GE S.En} {cut : ℕ} (Z : ProofFile.Pub)
  (X : Type) (pp : ScalesAndPolicy) (req : X → Instance ppref)
  (F : Files (DecR.configurationOfStoredTable (claimsLedgerOnAt (S.toDecR Zs cut) (numsOf Z) pp req)
    (relationsAndEncodingOfClaims _ (codingCells S Zs cut (numsOf Z) pp req)))) (P : F.Provers)

/-- **At a public part**: the shape and the numbers are read off it. -/
theorem encW_typed (h : Agree (shapeOf Z) S cut)
    (hfit : (numsOf Z).rows * 2 ^ (numsOf Z).kLo ≤ cut) (w : ProofFile.Honest.Weights)
    (rc : ℕ → TableRand) (x : S.Pos) :
    encW Z w rc 0 x.val =
      some (((F.withProvers P).encodeIndex (cellsOfF S Zs cut (numsOf Z) w.entry)
        (fun b j => (rc 0).pad b.val j.val, fun b q => (rc 0).tail b.val q.val) x).2.map toF) := by
  have hr : rowsFit (shapeOf Z) (linOf Z).kLo (linOf Z).matrixRows = true :=
    (rowsFit_iff h _ _).2 hfit
  rw [← encAt_typed X pp req F P h hfit w.entry (rc 0) x, ← h.v]
  unfold encW
  exact if_pos ⟨rfl, hr⟩

end

/-! ## What is asked of a public part at the library's two sizes -/

/-- The shape and the matrix's numbers off the public part are the full size's. -/
def ShapeAtFull (Z : ProofFile.Pub) : Prop := shapeOf Z = Bind.Column.shFull ∧ numsOf Z = numsRef

/-- The shape and the matrix's numbers off the public part are the small stored example's. -/
def ShapeAtSmall (Z : ProofFile.Pub) : Prop := shapeOf Z = Bind.Column.shSmall ∧ numsOf Z = numsSmall

/-- Under `ShapeAtFull` the two premises are paid. -/
theorem paid_full (Z : ProofFile.Pub) (hZ : ShapeAtFull Z) :
    Agree (shapeOf Z) frS 402653181 ∧ (numsOf Z).rows * 2 ^ (numsOf Z).kLo ≤ 402653181 := by
  rw [hZ.1, hZ.2]
  exact ⟨Bind.Column.agree_full, full_fits.1⟩

/-- Under `ShapeAtSmall` the two premises are paid. -/
theorem paid_small (Z : ProofFile.Pub) (hZ : ShapeAtSmall Z) :
    Agree (shapeOf Z) srS 524285 ∧ (numsOf Z).rows * 2 ^ (numsOf Z).kLo ≤ 524285 := by
  rw [hZ.1, hZ.2]
  exact ⟨Bind.Column.agree_small, small_fits.1⟩

end Bind.ForProver

end

#print axioms Bind.ForProver.entryAtF_intCast
#print axioms Bind.ForProver.wordsTable_eq
#print axioms Bind.ForProver.rowsFit_iff
#print axioms Bind.ForProver.encAt_typed
#print axioms Bind.ForProver.words_typed
#print axioms Bind.ForProver.encW_typed
#print axioms Bind.ForProver.paid_full
#print axioms Bind.ForProver.paid_small
#print axioms Bind.ForProver.numsOf
#print axioms Bind.ForProver.ShapeAtFull
#print axioms Bind.ForProver.ShapeAtSmall
