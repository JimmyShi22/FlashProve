-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Thr/CloseAt.lean: the closing of a segment (K10) at a border of a thread
(Honest/Thread/Thr.lean): one structure of named premises on a thread's parameters, on which Thr/Plays.lean and
Thr/Yes.lean stand. The thread T is a variable. One structure, three theorems.

Words. A thread is the structure of parameters of one chain's invariant `Thr T b`; border number b is the point in front
of the chain's block number b. A job J (`CloseJob`, Honest/K10/Job.lean) is the structure of a closing's parameters at a
place.

  `CloseAt T b c Z l p blk J`   four fields. tied: `Tied c Z l p J.pub.par blk` (Honest/K10/SimLot.lean). num: b is the
                    closing's number at the link l, 14 l + 12 (14 l + 14 at the last link). bs: the thread's list of
                    blocks is c's flat list, whole. half: the first of the thread's sides at the closing's place has
                    the one part `closePart (foldShellT true J foldWords)` (Honest/K10/Half.lean, Sim.lean)
  `CloseAt.blkAt`, `CloseAt.halfAt`   the thread's block number b is blk; the field half, at blk's own place
  `closeRounds_len`   the kind declares 2 + k rounds

Limits. The structure is a premise: it is shown here of no thread (Thr/AtThread.lean has it at the first chain's threads
under the library's head, from a premise on the prover's list of halves). T, b, c, Z, l, p, blk and J are variables. Of
the job's `stAt` and `rows` nothing is asked. No property of the protocol is claimed: nothing is said on its soundness,
completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.SimLot
import Johnson.Desc.ProofFile.Honest.K10.SimSent
import Johnson.Desc.ProofFile.Honest.Thread.Thr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Block Chain Place OpenedColumn)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (Par entries)

variable {V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **The named premises on a thread's parameters at a closing's border**: on the block, the border's number, the
thread's list of blocks, and the thread's side at the closing's place. -/
structure CloseAt (T : Thread Bk S ProofFile.Cl V W X Pb) (b : Nat) (c : Chain S ProofFile.Cl) (Z : ProofFile.Pub) (l : Nat)
    (p : VerifiableInference.Desc.K9.Where) (blk : Block S ProofFile.Cl) (J : CloseJob W) : Prop where
  /-- blk is the chain's block at the closing's number of link l, and the job's place's numbers are that closing's -/
  tied : Tied c Z l p J.pub.par blk
  /-- the border's number is the closing's: 14 l + 12, and 14 l + 14 at the last link -/
  num : b = 14 * l + (if l = 24 then 9 else 7) + 5
  /-- the thread's list of blocks is the chain's flat list, whole -/
  bs : T.bs = c.blocksInOrder
  /-- the first of the thread's sides at the closing's place has one part: "BAT"'s move, then the form of the fold's
  part that never refuses, at the job J -/
  half : ∃ g, (T.hs.find? fun h => h.place == closePlace J.pub.par) = some g ∧
    g.parts = [closePart (foldShellT true J foldWords)]

section
variable {T : Thread Bk S ProofFile.Cl V W X Pb} {b : Nat} {c : Chain S ProofFile.Cl} {Z : ProofFile.Pub} {l : Nat}
  {p : VerifiableInference.Desc.K9.Where} {blk : Block S ProofFile.Cl} {J : CloseJob W}

/-- The thread's block number b is the closing's block. -/
theorem CloseAt.blkAt (H : CloseAt T b c Z l p blk J) : T.bs[b]? = some blk := by
  obtain ⟨-, -, hb, -⟩ := H.tied
  rw [H.bs, H.num]
  exact hb

/-- The field half, with the block's own place for the closing's. -/
theorem CloseAt.halfAt (H : CloseAt T b c Z l p blk J) :
    ∃ g, (T.hs.find? fun h => h.place == blk.place) = some g ∧
      g.parts = [closePart (foldShellT true J foldWords)] := by
  obtain ⟨-, -, -, -, -, hp, -⟩ := H.tied
  rw [hp]
  exact H.half

end

/-- The kind declares 2 + k rounds. -/
theorem closeRounds_len (Q : Par) : ((closeRounds Q).map (·.1)).length = 2 + Q.k := by
  simp only [closeRounds, entries, List.length_map, List.length_cons, List.length_replicate]
  omega

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.CloseAt
#print axioms ProofFile.Honest.K10.CloseAt.blkAt
#print axioms ProofFile.Honest.K10.CloseAt.halfAt
#print axioms ProofFile.Honest.K10.closeRounds_len
