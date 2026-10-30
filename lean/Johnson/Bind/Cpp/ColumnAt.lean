-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Cpp/ColumnAt.lean: AT THE DESCRIPTION'S OWN ENCODER, AT ALL PUBLIC FILES: THE WRITTEN
COMMITTER'S SYMBOL AT A POSITION IS THE RUNNING COMMITTER'S COLUMN THERE, AND THE RUNNING TEXT OF
THE TABLE'S PLAIN ENTRIES IS WHAT THE WEIGHTS' MATRIX SPELLS. The proofs of `ColumnIs Z`
(Johnson/Bind/Cpp/Spells.lean) and `EntryIs` (Johnson/Bind/Cpp/Defs.lean).

How. Both are the general statements of Johnson/Bind/ColumnDefs.lean (proved in
Johnson/Bind/Column.lean and Johnson/Bind/Digits.lean with the sizes as letters), taken at the full
size's numbers (Johnson/Bind/ColumnSizes.lean). What is added here: the description's encoder is the
encoder of the object over `codingCells` (by unfolding); the matrix that is laid for given weights
is the matrix of casts of their digits (`backThe_eq`).

Main names (namespace `Bind.Cpp`).
  `shapeFull_eq`: the full size's shape of Johnson/Bind/Cpp/Defs.lean is `Bind.Column.shFull`.
  `agreeFull`: `Bind.Column.Agree shapeFull frS 402653181`. `positions_R₀`: 2^32 positions.
  `enc_R₀`: the description's encoder at Z is the library's honest table.
  **`columnIs Z`**: `ColumnIs Z`: at every Z, no premise.
  `honest_symbol`: so the written committer's symbol at a position has the position's number and
    2^11 words, each below the prime.
  `backThe_eq`: `backThe Z s w` is `Flat.matrixOf (idxOf s w)`, valid settings or not.
  **`entryIs`**: `EntryIs`: no premise.

Limits. No hash function, no query and no string is named: nothing is said here on the hash tree,
the out-of-domain sample or the commitment ID. The two statements are two of the debts of the tie
between the written and the running committer; the tie is not concluded here. Nothing on any
program. Nothing on soundness, completeness or index privacy. "At every Z" is cheap: the encoder
hangs on Z through a type alone. `positions_R₀` and `honest_symbol` are called by no theorem of this
library.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Bind.Cpp.Spells
import Johnson.Bind.ColumnSizes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Bind.Cpp
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open OnBytes.Flat OnBytes.Slice

/- Lean compares these names and does not open them. The coding is not among them: it is opened. -/
attribute [local irreducible] theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate theProofGate
  theLinkGate theProvers theNamed LPFD.Full.GF FlashProve.thePlan FlashProve.theItem

/-- The two names of the full size's shape are one shape. -/
theorem shapeFull_eq : shapeFull = Bind.Column.shFull := rfl

/-- The full size's shape has the library's a, l, r and v; the pads begin at 402,653,181. -/
theorem agreeFull : Bind.Column.Agree shapeFull frS 402653181 := Bind.Column.agree_full

/-- The written committer's word has 2^32 positions: for whoever speaks of all the tree's leaves. -/
theorem positions_R₀ (Z : PublicFiles) : (R₀ Z).protocol.wordLength = 2 ^ 32 := rfl

/-- The description's encoder at Z is the library's honest table at the words of the matrix, the
pads laid in, and the tails' words. -/
theorem enc_R₀ (Z : PublicFiles) (M : (R₀ Z).Index) (x : Coins) :
    (R₀ Z).protocol.encodeIndex M (riOf Z x) = Bind.Column.honestAt frS frZ 402653181 numsRef M x.tail x.pad :=
  Bind.Column.encIsHonestTab frS frZ 402653181 numsRef _
    (ppAtFiles (asDescriptionFiles Z).pol (asDescriptionFiles Z).KL) Subtype.val (flashProveDescription.F Z) (flashProveDescription.P Z) M (riOf Z x)

/-- **The column, at every Z.** -/
theorem columnIs (Z : PublicFiles) : ColumnIs Z := by
  intro M x j
  exact (congrFun (enc_R₀ Z M x) j).trans
    (Bind.Column.columnAgrees (Z := frZ) (N := numsRef) agreeFull M x.tail x.pad x.salt j)

/-- What the written committer's symbol at a position has, at every matrix and all coins: the
position's number, a word for each of the 2^11 rows, and every word below the prime. The first two
are the premises of `SpellsLeaf` (Johnson/Bind/Cpp/Spells.lean) at the honest table; the third is
for whoever needs the words in the field's range. -/
theorem honest_symbol (Z : PublicFiles) (M : (R₀ Z).Index) (x : Coins) (j : Fin (R₀ Z).protocol.wordLength) :
    ((R₀ Z).protocol.encodeIndex M (riOf Z x) j).1 = j.val ∧ ((R₀ Z).protocol.encodeIndex M (riOf Z x) j).2.length = 2 ^ 11 ∧
      ∀ w ∈ ((R₀ Z).protocol.encodeIndex M (riOf Z x) j).2, Fmt.Fld.two.ok w = true := by
  have h := columnIs Z M x j
  have hl := Bind.Column.length_columnOf shapeFull (x.table (entryOfCells M)) j.val
  have hok := Bind.Column.ok_columnOf shapeFull
    (Bind.Twin.laid shapeFull (x.table (entryOfCells M))) j.val
  rw [show shapeFull.v = 11 from rfl] at hl
  generalize Bind.Twin.columnOf shapeFull
    (Bind.Twin.laid shapeFull (x.table (entryOfCells M))) j.val = col at h hl hok
  rw [h]
  exact ⟨rfl, hl, hok⟩

/-- The matrix that is laid for given weights is the matrix of casts of their digits. -/
theorem backThe_eq (Z : PublicFiles) (s : IntegerTransformer.Settings) (w : ModelWeights s) :
    backThe Z s w = Flat.matrixOf (idxOf s w) := by
  unfold backThe idxOf
  by_cases hv : settingsAreValid s = true
  · rw [dif_pos hv, dif_pos hv]
    rfl
  · rw [dif_neg hv, dif_neg hv]

/-- **The digits.** -/
theorem entryIs : EntryIs := by
  intro Z s w
  funext b e
  rw [backThe_eq]
  exact (Bind.Column.entry_full (Flat.matrixOf (idxOf s w)) (idxOf s w).mat (fun _ _ => rfl) b
    e).symm

end Bind.Cpp

end

#print axioms Bind.Cpp.shapeFull_eq
#print axioms Bind.Cpp.agreeFull
#print axioms Bind.Cpp.positions_R₀
#print axioms Bind.Cpp.honest_symbol
#print axioms Bind.Cpp.enc_R₀
#print axioms Bind.Cpp.columnIs
#print axioms Bind.Cpp.backThe_eq
#print axioms Bind.Cpp.entryIs
