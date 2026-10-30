-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsConduit.lean: THE LETTERS oW, wOf, msgW OF THE LOOKUP's LAW AS THE TABLE's
FILES FILL THEM ("the conduit": Johnson/Desc/First/Look/K3StoredThree.lean, K3LettersAt.lean),
HELD AGAINST WHAT K4's FILES ASK OF THEM. Until here by reading. Theorems, by unfolding. No
draw, no count.

  `msg_conduit`: the conduit's msgW is enc at the witness's cells, at enc := `Stored.entries`: the
    field msg of `MeansTies` (Johnson/Road/K4/K4PinsOfMeans.lean) at `k3StoredAt rad arr seat`.
  `wOf_entries`: `Stored.wOfC (Stored.entries C) r c = rcQ rows cols C r c`
    (Johnson/Road/K4/K4PinsMat.lean): the entry inside rows × cols, 0 outside: at every r and c.
  `cutW_conduit`: so K4's value's reader of the committed matrix, `cutW` (K4PinsW.lean), at the
    conduit is `rcQ` cut at nr rows and nc columns; `encIs_conduit`: at nr := rows, nc := cols it is
    `rcQ` itself.
  **`table_of_noRec`**: `Stored.NoRec decT` ("the decoder does not read the verifier's state") gives
    the line table of `RecRides` (Johnson/Road/K4/K4Pins.lean); `recRides_of_noRec`: so `RecRides`
    is left with its line sample.

  `cols_full`: the number of columns of the committed matrix at the full size, as the table's
    files have it, is 2 ^ kRef: the library's `full_columns`, called (the rows: its `full_rows`:
    Johnson/Flat/ClaimsSizes.lean).

STANDS OVER K3StoredThree.lean · K3LettersAt.lean (Johnson/Desc/First/Look/),
which stand in this tree.

OBJECT: `k3StoredAt`. USER: Johnson/Road/K4/K4PinsAtWide.lean; meant: the assembly of K4's law.
LETTERS: rows, cols, rad, arr, seat, decT: free.

Limits. K04_law IS NOT PROVED BY THIS. `k3StoredAt` LAYS nr := rows AND nc := cols; `WorthTies`
(Johnson/Road/K4/K4PinsEndFill.lean) ASKS nr = hRef AND nc = 2 ^ kRef. AS REPORTED
the meant rows is `OnBytes.Flat.numsFull.rows` and the meant cols is 2 ^ (`numsFull.kLo` + the
committed table's number of row variables at the full size's frame): the library's `full_rows` and
`full_columns` say that these are hRef and 2 ^ kRef: THAT THE CONSTANT IS LAID AT THESE TWO IS
A REPORT, NOT A THEOREM HERE. The line sample of `RecRides` is not touched.
-/
import Johnson.Road.K4.K4PinsMat
import Johnson.Desc.First.Look.K3LettersAt
import Johnson.Flat.ClaimsSizes
import OnBytes.Slice.FullRecLink
import OnBytes.Slice.LinkAtRec

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (Stored.CellsW Stored.entries Stored.wOfC Stored.msgWc
  Stored.NoRec)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles (k3StoredAt)

variable {rows cols : ℕ}

/-- **The conduit's msgW is enc at the witness's cells.** -/
theorem msg_conduit {Tok : Type} (rad : OnBytes.OracleShape → ℕ) (arr : ℕ → ℕ → ℕ)
    (seat : ℕ → Bool → ℕ → ℕ × ℕ) :
    (k3StoredAt (rows := rows) (cols := cols) (Tok := Tok) rad arr seat).msgW =
      fun w => Stored.entries w.cells := rfl

/-- **What the conduit reads of a matrix's entries is the matrix**, 0 outside. -/
theorem wOf_entries (C : Stored.CellsW rows cols) (r c : ℕ) :
    Stored.wOfC (Stored.entries C) r c = rcQ rows cols C r c := rfl

/-- The value's reader of the committed matrix, at the conduit. -/
theorem cutW_conduit (nr nc : ℕ) (C : Stored.CellsW rows cols) (a b : ℕ) :
    cutW Stored.entries Stored.wOfC nr nc C a b =
      if a < nr ∧ b < nc then rcQ rows cols C a b else 0 := rfl

/-- **At the conduit's own numbers of rows and columns that reader is `rcQ`**: the tie of two
readers that the assembly of K4's law asks (its field encIs). -/
theorem encIs_conduit :
    cutW (Stored.entries (rows := rows) (cols := cols)) Stored.wOfC rows cols = rcQ rows cols := by
  funext C a b
  rw [cutW_conduit]
  by_cases h : a < rows ∧ b < cols
  · rw [if_pos h]
  · rw [if_neg h]
    unfold rcQ
    rw [dif_neg h]

/-- **A decoder that does not read the verifier's state has the line table of `RecRides`.** -/
theorem table_of_noRec {P : Type}
    {decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option (Stored.CellsW rows cols)}
    (h : Stored.NoRec decT) (Zt : P) (s s' : S) (c : ℕ → Option (ℕ × List UInt64))
    (_ : OnBytes.Desc.First.K4.Rest s s') : decT c (Zt, s') = decT c (Zt, s) := h c Zt s' s

/-- So `RecRides` is left with its line sample. -/
theorem recRides_of_noRec {P : Type} (cs : OnBytes.Codes)
    (smp : P × S → (s : VerifiableInference.Desc.Sound.Sending) → (i : Fin s.l.length) →
      Option ((Johnson.Pack.sigOf cs s.l).om i).Smp)
    {decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option (Stored.CellsW rows cols)}
    (h : Stored.NoRec decT) (Zt : P)
    (hs : ∀ s s' : S, OnBytes.Desc.First.K4.Rest s s' → ∀ sd i,
      smp (Zt, s') sd i = smp (Zt, s) sd i) : RecRides cs smp decT Zt :=
  ⟨hs, fun s s' c r => table_of_noRec h Zt s s' c r⟩

/-- **The number of columns of the committed matrix at the full size, as the table's files have it**
(`P5J.colsAt numsFull`, Johnson/P5J/TopJoint.lean, unfolded) **is 2 ^ kRef**: the library's own
`full_columns` (Johnson/Flat/ClaimsSizes.lean), called: its decoder `decFull` is that text by
abbreviation. The rows: the library's `full_rows`, as it stands. -/
theorem cols_full :
    2 ^ (OnBytes.Flat.numsFull.kLo + (OnBytes.Slice.frS.toDecR OnBytes.Slice.frZ 402653181).v) =
      2 ^ Inst.Model.Layout.kRef :=
  congrArg (2 ^ ·) OnBytes.Flat.full_columns

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.cols_full
#print axioms OnBytes.Road.K4.recRides_of_noRec
#print axioms OnBytes.Road.K4.msg_conduit
#print axioms OnBytes.Road.K4.wOf_entries
#print axioms OnBytes.Road.K4.cutW_conduit
#print axioms OnBytes.Road.K4.encIs_conduit
#print axioms OnBytes.Road.K4.table_of_noRec
