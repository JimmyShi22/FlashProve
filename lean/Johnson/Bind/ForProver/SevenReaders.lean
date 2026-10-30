-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/SevenReaders.lean: AT ANY INPUT OF THE GOALS' TYPE, THE LIBRARY'S OWN
ENCODING AND OOD SAMPLE ARE `strAt` AND `recAt` (Johnson/Bind/ForProver/SevenAt.lean) AT THE PLAIN
READERS OF THAT INPUT. LAWS ON THE MAPS OF THE TIE. Statements and proofs; general in the sizes.

Why. Johnson/Bind/ForProver/SevenTied.lean has these equations where the goals' input is made of the
frame's. Here they stand for the other direction, where the frame's matrix and coins are the readers
(the library's E2E/KeyReaders.lean) of the goals' input. They follow from the former by the two
equations on the way there and back (Johnson/Bind/ForProver/PolysReaders.lean). Two inputs are
spoken of below: the goals' (a matrix of cells, pads and tails on finite ranges: what the library's
typed encoder takes) and the frame's (functions of two plain numbers: what the frame for an honest
prover hands out).

Main names (namespace `Bind.ForProver`).
   **`strAt_readers`**: under `Bind.Column.Agree sh S cut` and hfit: at EVERY matrix of cells i and
      all pads and tails q: `strAt` at the packing of `cellsReader i` and the coins made of
      `padReader q.1` and `tailReader q.2` is the library's table of code words at the words of i
      under q.
   **`recAt_readers`**: and `recAt` there is the seed with the sample map's answers at these words'
      messages.
   `enc_readers`, `recOf_readers`: the same two with the object's own `encodeIndex` and `recOf` on the
      right: at all three protocols over the written honest side and all their provers: pp and req
      stand in F's type alone; F and P stand on the right sides in `(F.withProvers P)`; the proofs are the
      two laws above, whose right sides name none of the four; at the full size
      `FlashProve.meant_home` fills them.
   The third term: `polysOf_eq_polysAt_readers` (Johnson/Bind/ForProver/PolysReaders.lean).
Limits. EVERY STATEMENT HERE IS ON MAPS BETWEEN THE TWO INPUTS (`cellsReader`, `padReader`,
`tailReader`). THAT THE HONEST PROVER'S PRIVATE INPUT AT THE PROTOCOL IS THE GOALS', WITH THE
FRAME'S READERS MADE OF IT BY THESE MAPS, IS SAID BY NO FILE BENEATH THIS ONE. The matrix is a
letter: in range or not, an index's or not; of a cell the first coordinate alone is read, on both
sides. WITHOUT `Agree` THE READERS GIVE 0 WHERE A PAD OR A TAIL IS DUE, IN SILENCE: the premise is
not idle (read off the definitions; no example of this file shows it). `Agree` and hfit are
premises; at the full size they are theorems without premises (`Bind.Column.agree_full`,
Johnson/Bind/ColumnSizes.lean; `full_fits`, Johnson/Flat/ClaimsSizes.lean), and `home_is_ours`
(Johnson/Bind/ForProver/HomeIsOurs.lean) spends them at the input of the library's typed compiler at
the full size: so the premises are met there. `seven_at_ours` and `meant_ours` do not rest on this
file. One committed table; which of the protocol's tables it is, the first or a copy, is not said
here. No hash function, no query, no coin's law. This file writes no honest prover. Nothing on
completeness, on index privacy, on soundness or on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.SevenTied
import Johnson.Bind.ForProver.PolysReaders

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Bind.ForProver
open Prob Cb Cb.Ood Blocks Hiop OnBytes.Slice OnBytes.Flat Inst.Model VerifiableInference
open Iop hiding Shape
open AtPublicFiles.Key (cellsReader padReader tailReader)
open Bind.Twin (Shape)
open Bind.Column (Agree)

section
variable {S : Sz} {Zs : Cb.Ood.Sample GE S.En} {cut : ℕ} {N : MatrixNums} {sh : Shape}

/-- **The library's table of code words, at any input of the goals' type, is `strAt` at that input's
plain readers.** A law on the maps of the tie; that the honest prover's input at the protocol is so
made is said by no file beneath this one. -/
theorem strAt_readers (h : Agree sh S cut) (hfit : N.rows * 2 ^ N.kLo ≤ cut)
    (i : OnBytes.Flat.Cells (S.toDecR Zs cut) N)
    (q : PadsOf S cut × (Fin (2 ^ S.P.v) → Fin S.P.T.r → GF)) :
    strAt S sh (entryAtF N.kLo N.rows S.P.v (cellsReader i)) ⟨padReader q.1, tailReader q.2⟩ =
      honestTab S (rowWords S (honestMsgs S (cellWords S Zs cut N i q.1))) (tailWords S q.2) := by
  have k := strAt_tied (Zs := Zs) h hfit (cellsReader i) ⟨padReader q.1, tailReader q.2⟩
  rw [qOf_readers, cellWords_readers] at k
  exact k

/-- **The library's OOD sample, at any input of the goals' type, is `recAt` at that input's plain
readers.** A law on the maps of the tie; that the honest prover's input at the protocol is so made
is said by no file beneath this one. -/
theorem recAt_readers (h : Agree sh S cut) (hfit : N.rows * 2 ^ N.kLo ≤ cut)
    (i : OnBytes.Flat.Cells (S.toDecR Zs cut) N)
    (q : PadsOf S cut × (Fin (2 ^ S.P.v) → Fin S.P.T.r → GF)) (σ : Zs.D) :
    recAt S Zs sh (entryAtF N.kLo N.rows S.P.v (cellsReader i))
        ⟨padReader q.1, tailReader q.2⟩ σ =
      (σ, (S.ixR Zs).ZR.val σ (honestMsgs S (cellWords S Zs cut N i q.1))) := by
  have k := recAt_tied (Zs := Zs) h hfit (cellsReader i) ⟨padReader q.1, tailReader q.2⟩ σ
  rw [qOf_readers, cellWords_readers] at k
  exact k

variable {X : Type} (pp : Inst.Model.ScalesAndPolicy) (req : X → Inst.Model.Instance Inst.Model.ppref)
  (F : Files (DecR.configurationOfStoredTable (claimsLedgerOnAt (S.toDecR Zs cut) N pp req)
    (relationsAndEncodingOfClaims _ (codingCells S Zs cut N pp req)))) (P : F.Provers)

/-- The first, with the object's own encoder on the right. The letters pp and req stand in F's type
alone; F and P stand on the right side in `(F.withProvers P).encodeIndex`. A law on the maps of the tie. -/
theorem enc_readers (h : Agree sh S cut) (hfit : N.rows * 2 ^ N.kLo ≤ cut)
    (i : OnBytes.Flat.Cells (S.toDecR Zs cut) N) (q : (F.withProvers P).EncodingRandomness) :
    strAt S sh (entryAtF N.kLo N.rows S.P.v (cellsReader i))
        ⟨padReader (S := S) (cut := cut) q.1, tailReader (S := S) q.2⟩ =
      (F.withProvers P).encodeIndex i q :=
  strAt_readers h hfit i q

/-- The second, with the object's own sample on the right. A law on the maps of the tie. -/
theorem recOf_readers (h : Agree sh S cut) (hfit : N.rows * 2 ^ N.kLo ≤ cut)
    (i : OnBytes.Flat.Cells (S.toDecR Zs cut) N) (q : (F.withProvers P).EncodingRandomness) (σ : (F.withProvers P).OutOfDomainSeed) :
    recAt S Zs sh (entryAtF N.kLo N.rows S.P.v (cellsReader i))
        ⟨padReader (S := S) (cut := cut) q.1, tailReader (S := S) q.2⟩ σ =
      (F.withProvers P).recOf i q σ :=
  recAt_readers h hfit i q σ

end

end Bind.ForProver

end

#print axioms Bind.ForProver.strAt_readers
#print axioms Bind.ForProver.recAt_readers
#print axioms Bind.ForProver.enc_readers
#print axioms Bind.ForProver.recOf_readers
