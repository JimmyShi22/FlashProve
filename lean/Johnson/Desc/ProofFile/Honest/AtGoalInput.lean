-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/AtGoalInput.lean: THE HONEST SIDE OF THE PROOF FILE's PROTOCOL
(`honestCFile`, Honest/CommitterFile.lean) AT A PRIVATE INPUT IN WHICH ONE COMMITTED TABLE's
RANDOMNESS STANDS ON ITS FINITE RANGES: (index, (pads, encoding randomness), seed, the copy's
number). The frame's parts read the index committer's coins as plain functions of numbers
(`TableRand`, Honest/ForKinds.lean), one for each item of the statement. Here these are MADE OF the
randomness on finite ranges, by the library's own readers (`padReader`, `tailReader`,
E2E/KeyReaders.lean), and the record reads its private input through that function. No type of the
frame, of a filling or of a half turns. Definitions alone; no theorem.

  `BHonest.comap`   a record of an honest side, its private input read through a function: the same
                   coins, the same public sets; the external string, the two strategies and the
                   withheld set at f w
  `TableR S cut`    one committed table's randomness on its finite ranges: the pads; the encoding
                   randomness
  `randOf`          the frame's reader of it: THAT ONE TABLE's AT EVERY ITEM OF THE STATEMENT
  `goalInput`       (index, randomness, seed, number) as the frame's private input
  `honestCGoal`     `honestCFile` through `goalInput`

WHY THIS FORM. The library's record of the three honest sides gives the session's side the private
input (index, one table's randomness, that table's seed, the copy's number). That `TableR` at the
full size's numbers is that record's type of randomness is by the definitions, by reading; no
statement here says so. The index stays the letter W₀: to carry a sentence on the honest side from
the frame's own index to the library's index, a matrix, there is the library's map from the one to
the other; no such carrying is typed here.

Limits. As Honest/CommitterFile.lean's. `randOf` answers alike at all items of the statement: it
serves the session's side alone, not the link's, which reads two tables. Which items of the
statement the proof file's parts read through the reader is not said here. Nothing on a run, a coin
or a measure. This file proves nothing about soundness, completeness, hiding or any other property
of the protocol.

THREE LIMITS ON HIDING AT THIS FILE's `randOf`, BY A READING OF THE DEFINITIONS: NO THEOREM HERE
STATES THEM (the answers: the committer's OOD answers, those of `Bind.ForProver.oodAt`,
Johnson/Bind/ForProver/Ood.lean; (i, rc): index and randomness; q, q′: two tables' randomness):
(1) A PAD's 0 CAN REACH THE EXPLICIT INPUT: the pad reader gives 0 outside its finite range, and the
answers read pads 3i to 3i + 2 below THE LIST's length at a free letter: at a list longer than a
third of the pads, or at a cut at or beyond the table's length, A ROW's WEIGHTED SUM STANDS UNMASKED
in the instance and in both messages; this file's `randOf` is that very composition. THE PREMISE
THAT BARS IT: `Bind.Column.Agree` (Johnson/Bind/ColumnDefs.lean): under it, at a list no longer than
the shape's s, nothing is read outside: NAME IT IN EVERY LAW THAT READS THESE ANSWERS.
(2) The seed and the number stand free beside (i, rc), and q beside q′: two records over the same
pads reveal exact equations (the format's own rule): one session lays one: a law over two sessions,
or over link and session, must say: one seed to each table's randomness; q and q′ apart; the link's
q′ = the session's q.
(3) The number n is sent and is NOT in the instance: a simulator must be handed it.
-/
import Johnson.Desc.ProofFile.Honest.CommitterFile
import Johnson.Desc.ProofFile.Honest.ForKinds
import E2E.KeyReaders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription)
open OnBytes.Maker (WholeD FrontMsg)
open Compile.Joined (JoinMsg)
open _root_.Run.PQ (CK)
open OnBytes.Flat (PadsOf)
open OnBytes.Slice (Sz GF)

/-- **A record of an honest side, its private input read through a function.** -/
def BHonest.comap {X : Type} {E : Iop.ExtSpec} {Q : Iop.BatchInteractiveOracleProof X E} {Wt Wt' : Type}
    (H : Iop.BatchHonestProver Q Wt) (f : Wt' → Wt) : Iop.BatchHonestProver Q Wt' where
  Coin0 := H.Coin0
  Coin := H.Coin
  ext := fun w => H.ext (f w)
  strat0 := fun w => H.strat0 (f w)
  strat := fun w => H.strat (f w)
  Bad := H.Bad
  Hid := fun w => H.Hid (f w)
  stop0 := H.stop0

/-- **One committed table's randomness on its finite ranges**: the pads; the encoding randomness. -/
abbrev TableR (S : Sz) (cut : ℕ) : Type := PadsOf S cut × (Fin (2 ^ S.P.v) → Fin S.P.T.r → GF)

/-- **The frame's reader of it**: that one table's, at every item of the statement. -/
def randOf {S : Sz} {cut : ℕ} (r : TableR S cut) : ℕ → TableRand :=
  fun _ => ⟨AtPublicFiles.Key.padReader r.1, AtPublicFiles.Key.tailReader r.2⟩

/-- (index, randomness, seed, number) as the frame's private input. -/
def goalInput {W₀ Sd : Type} {S : Sz} {cut : ℕ} (w : W₀ × TableR S cut × Sd × ℕ) :
    W₀ × (ℕ → TableRand) × (Sd × ℕ) :=
  (w.1, randOf w.2.1, w.2.2)

variable {W₀ X Xi Ky Tr X₀ Xh Sd : Type}

/-- **`honestCFile` at that private input.** -/
noncomputable def honestCGoal (S : Sz) (cut : ℕ) (C : CK) (D : WholeD) (F : FileDescription Xi) (B : ProverCoinCounts)
    (Cm : Committer W₀ (ℕ → TableRand) (Sd × ℕ) X Xi Ky) (item₀ : Nat)
    (H : Prover W₀ (ℕ → TableRand) Xi Ky Tr X₀ Xh) (ans : Xi → List OnBytes.E)
    (answers : Isk W₀ (ℕ → TableRand) (Sd × ℕ) → List OnBytes.E) (a₀ : List OnBytes.E) :
    Iop.BatchHonestProver
      (batchOf C D (⟨a₀, 0⟩ : FrontMsg (List OnBytes.E))
        (⟨a₀, ByteArray.empty⟩ : JoinMsg (List OnBytes.E) ByteArray) ByteArray.empty F
        (silentAns ans)) (W₀ × TableR S cut × Sd × ℕ) :=
  BHonest.comap (honestCFile C D F B Cm item₀ H ans answers a₀) goalInput

end ProofFile.Honest
