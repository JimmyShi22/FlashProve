-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyStoredRows.lean: the rows of the committed table as the honest side's parts of the shared
chain read them (`rowsOf`, Johnson/Desc/ProofFile/Honest/K14/Parts.lean), held against the encoder's
own messages. Statements and proofs.

The setting. The parts that send the folded row and Omega read "row r of the committed table before
encoding, at the place k": the message below the code's message length, the encoding randomness from
a public place on. The encoder of the configuration of a committed table makes its messages of a
matrix and pads, and takes encoding randomness beside them. E2E/KeyReaders.lean has both as three
plain readers.

What is shown.
  `eOfF_read`: the honest side's spelling of a base-field element reads as that element.
  **`rowsOf_message`**: below the code's message length `rowsOf S ⟨entry⟩ ⟨pad, tail⟩ r k` reads as
    `storedAt entry pad` at the shape's own numbers, if the encoding randomness begins behind the
    message.
  **`rowsOf_tail`**: from the public place on, it reads as the letter `tail`. THAT LETTER IS FREE
    HERE: it is not held against the encoder's own reader of the encoding randomness (`tailReader`,
    `tail_eq`, E2E/KeyReaders.lean), and nothing says that the places behind the public place are as
    many as the code's encoding randomness has entries.
  **`rowsOf_encoder`**: so, for a table's sizes S₀, a matrix M, pads η and a shape with these sizes'
    numbers: below the message length it reads as the encoder's own message (`honestMsgs` at
    `cellWords`): ONE MATRIX AND ONE SET OF PADS IN BOTH.
  `stored_written`, **`rowsOf_encoder_written`**: at the written shape of the key and the full
    size's encoder the ties of numbers hold (by an evaluation in Lean's kernel): no premise is left.

Limits. Readings (`readE`), not words. Of what the parts make of these rows nothing
is said. Nothing on hiding follows from this file.


-/
import E2E.KeyReaders
import Johnson.Desc.ProofFile.Honest.K14.Parts
import Johnson.Goal.PlanValues.KeySizedReturns

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.Key
open OnBytes.Slice (GF GE readE)
open OnBytes.Params (LinShape)
open ProofFile.Honest (eOfF)
open ProofFile.Honest.K14 (rowsOf entriesOf)
open Lk6.AtPlan (keyFull)

/-- The honest side's spelling of a base-field element reads as that element. -/
theorem eOfF_read (x : GF) : readE (eOfF x) = algebraMap GF GE x := by
  show readE (OnBytes.ofF (OnBytes.Slice.ofF x)) = _
  rw [OnBytes.Slice.readE_ofF, OnBytes.Slice.toF_ofF]

section
variable (S : LinShape) (entry pad tail : ℕ → ℕ → GF) (r k : ℕ)

/-- **Below the code's message length: the message.** -/
theorem rowsOf_message (hk : k < S.fold.index.code.ell)
    (htail : S.fold.index.code.ell ≤ S.fold.tailFirst) :
    readE (rowsOf S ⟨entry⟩ ⟨pad, tail⟩ r k) =
      algebraMap GF GE (storedAt entry pad S.matrixRows S.kLo S.fold.index.plain
        S.fold.index.code.ell r k) := by
  unfold rowsOf storedAt entriesOf
  by_cases h1 : k < S.matrixRows * 2 ^ S.kLo
  · rw [if_pos h1, if_pos h1, if_pos h1, eOfF_read]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : S.fold.index.plain ≤ k ∧ k < S.fold.index.code.ell
    · rw [if_pos h2, if_pos h2, eOfF_read]
    · rw [if_neg h2, if_neg h2, if_neg (fun h => absurd (lt_of_lt_of_le hk (htail.trans h.1))
        (lt_irrefl _)), OnBytes.Slice.readE_zero, map_zero]

/-- **From the public place on: the encoding randomness.** -/
theorem rowsOf_tail (h1 : S.fold.tailFirst ≤ k) (h2 : k < S.fold.entries)
    (hfit : S.matrixRows * 2 ^ S.kLo ≤ S.fold.index.code.ell)
    (htail : S.fold.index.code.ell ≤ S.fold.tailFirst) :
    readE (rowsOf S ⟨entry⟩ ⟨pad, tail⟩ r k) =
      algebraMap GF GE (tail r (k - S.fold.tailFirst)) := by
  have hk : S.fold.index.code.ell ≤ k := htail.trans h1
  unfold rowsOf
  rw [if_neg (Nat.not_lt.2 (hfit.trans hk)), if_neg (fun h => absurd (lt_of_lt_of_le h.2 hk)
    (lt_irrefl _)), if_pos ⟨h1, h2⟩, eOfF_read]

end

/-- **The message is the encoder's own**, at one matrix and one set of pads. -/
theorem rowsOf_encoder (S₀ : OnBytes.Slice.Sz) (cut : ℕ) (N : OnBytes.Flat.MatrixNums)
    (Z : Cb.Ood.Sample GE S₀.En) (hfit : N.rows * 2 ^ N.kLo ≤ cut)
    (M : OnBytes.Flat.Cells (S₀.toDecR Z cut) N) (η : OnBytes.Flat.PadsOf S₀ cut)
    (tail : ℕ → ℕ → GF) (S : LinShape) (e1 : S.matrixRows = N.rows) (e2 : S.kLo = N.kLo)
    (e3 : S.fold.index.plain = cut) (e4 : S.fold.index.code.ell = S₀.P.T.l)
    (htail : S.fold.index.code.ell ≤ S.fold.tailFirst) (k : S₀.ix.Row) (j : S₀.En) :
    readE (rowsOf S ⟨cellsReader M⟩ ⟨padReader η, tail⟩ (OnBytes.Slice.Sz.rowNo k) j.val) =
      OnBytes.Slice.honestMsgs S₀ (OnBytes.Flat.cellWords S₀ Z cut N M η) (k, j) := by
  rw [rowsOf_message S _ _ tail _ _ (by rw [e4]; exact j.isLt) htail, e1, e2, e3, e4,
    stored_eq_hold S₀ cut N Z hfit M η k j]

/-! ## At the written sizes of the key -/

set_option maxRecDepth 1000000 in
/-- The written shape's numbers. -/
theorem stored_written : keyFull.once.shape.matrixRows = 3076096 ∧ keyFull.once.shape.kLo = 7 ∧
    keyFull.once.shape.fold.index.plain = 402653181 ∧
    keyFull.once.shape.fold.index.code.ell = 402653184 ∧
    keyFull.once.shape.fold.index.code.ell ≤ keyFull.once.shape.fold.tailFirst := by
  decide +kernel

/-- **At the written shape and the full size's encoder**: no premise is left. -/
theorem rowsOf_encoder_written
    (M : OnBytes.Flat.Cells (OnBytes.Slice.frS.toDecR OnBytes.Slice.frZ 402653181)
      VerifiableInference.OnPublicFiles.numsRef)
    (η : OnBytes.Flat.PadsOf OnBytes.Slice.frS 402653181) (tail : ℕ → ℕ → GF)
    (k : OnBytes.Slice.frS.ix.Row) (j : OnBytes.Slice.frS.En) :
    readE (rowsOf keyFull.once.shape ⟨cellsReader M⟩ ⟨padReader η, tail⟩
        (OnBytes.Slice.Sz.rowNo k) j.val) =
      OnBytes.Slice.honestMsgs OnBytes.Slice.frS
        (OnBytes.Flat.cellWords OnBytes.Slice.frS OnBytes.Slice.frZ 402653181
          VerifiableInference.OnPublicFiles.numsRef M η) (k, j) :=
  rowsOf_encoder OnBytes.Slice.frS 402653181 VerifiableInference.OnPublicFiles.numsRef OnBytes.Slice.frZ
    (by show 3076096 * 2 ^ 7 ≤ 402653181; norm_num) M η tail keyFull.once.shape stored_written.1
    stored_written.2.1 stored_written.2.2.1 stored_written.2.2.2.1 stored_written.2.2.2.2 k j

end AtPublicFiles.Key

#print axioms AtPublicFiles.Key.eOfF_read
#print axioms AtPublicFiles.Key.rowsOf_message
#print axioms AtPublicFiles.Key.rowsOf_tail
#print axioms AtPublicFiles.Key.rowsOf_encoder
#print axioms AtPublicFiles.Key.stored_written
#print axioms AtPublicFiles.Key.rowsOf_encoder_written
