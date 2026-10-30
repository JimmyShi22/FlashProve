-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/M1/NumbersAt.lean: the count of Johnson/M1/Numbers.lean at the proof file's OTHER two chains: every opening of every
tree that the shared chain (number 1) and the last chain (number 2) send, by any round of the three chains, summed, against the
tails of that tree's rows. Definitions, and each theorem-to-be as a `def … : Prop`. No proof.

Why. Omega's message is sent on the shared chain and opened twice in one proof file: at the test on its own group and again at
the request's own test. A count that keeps the first chain's trees alone does not see it. Here a tree is named by (chain, number),
as Honest/Frame.lean's srcOf names a source, and drawnTabAt sums all openings of that source. Both chains number their own trees
from 0 in the declared rounds, the last chain too: its offset lastChainFirstTreeNumber is in the label of a tree, not in its source.

THE SHARED CHAIN HAS A SENDING THAT Johnson.G.sendsFullLit DOES NOT LIST. That list holds the entries "SEND seed". The fresh mask
of the fold at the head of Omega's test goes in its entry "FOLD epsilon" (round 44; Johnson/G/Sends.lean, head). So the shared
chain has ten sendings and eleven trees, and sendsAt 1 lays that sending in at number 6. Spec.treesTieAt holds the ten and the
four against the written cut, and Spec.rootsTieAt against the declared rounds' numbers of roots: so no tree is missing.

WHOSE VIEW: one proof file's declared rounds: one request. A batch's other requests open Omega's rows again: not counted here.
At one request some rows have tails longer than their draws: Spec.countAtEdges says which, by how much.
-/
import Johnson.M1.Numbers
import Johnson.SendSim.Seat.ReadsCountAt

set_option autoImplicit false

namespace OnBytes.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At OnBytes.SendSim.Seat
open Johnson.Prover.Send (shapeAt)
open VerifiableInference.PlanWritten (cutSharedFull cutSecondFull proofSizedFull)

/-- The positions that are drawn for the tree number n of the chain number ch, over all openings of the table. drawnTab is its
value at ch = 0. -/
def drawnTabAt (T : List ((Nat × Nat) × Nat)) (ch n : Nat) : Nat :=
  ((T.filter fun x => x.1 == (ch, n)).map (·.2)).sum

/-- The test on queried positions on a table of openings, at a sending of the chain number ch. readsWithinT is its value at
ch = 0. -/
def readsWithinTAt (T : List ((Nat × Nat) × Nat)) (ch : Nat) (P : K1.Par) (n₀ : Nat) : Bool :=
  (List.range P.sent.size).all fun k =>
    match ((Own.treesMade P.codes P.sent).getD {}).tree[k]? with
    | none => true
    | some τ =>
      ((shapeAt P k).mainRows == 0 ||
          decide (drawnTabAt T ch (n₀ + τ) ≤ (P.codes.base.getD (shapeAt P k).code default).r)) &&
        ((shapeAt P k).maskRows == 0 ||
          decide (drawnTabAt T ch (n₀ + τ) ≤ (P.codes.mask.getD (shapeAt P k).maskCode default).r))

/-- The entries "SEND seed" of the proof file's chain number ch, in the order of sending. sendsW is its value at ch = 0. -/
def listedAt (ch : Nat) : List (Array OnBytes.OracleNotice) :=
  (Johnson.G.sendsFullLit.filter fun s => s.1 == 2 && s.2.1 == ch).map fun s => s.2.2.2.toArray

/-- The fresh mask that the fold at the head of Omega's test sends in its own entry "FOLD epsilon": foldMaskNotice at that
stage's shape, which the written sizes give. That this is the stage is a reading of the verifier's text: linSharedTestsVerify
(OnBytes/Iop/Lin.lean) calls ioppVerify at S.testOmega with no mask, so foldStartVerify (OnBytes/Iop/Fold.lean) receives
foldMaskNotice (ioppFoldShape cur L), where cur is the head. The cut and the rounds below hold its tree's length and width, not
its mask code. -/
def foldSentW : Array OnBytes.OracleNotice :=
  (proofSizedFull.batch.shape.testOmega.take 1).toArray.map fun s => foldMaskNotice (ioppFoldShape s {})

/-- The proof file's sendings on the chain number ch, in the order of sending: the listed ones, and on the shared chain the
fold's own, at number 6. -/
def sendsAt (ch : Nat) : List (Array OnBytes.OracleNotice) :=
  if ch == 1 then (listedAt 1).take 6 ++ foldSentW :: (listedAt 1).drop 6 else listedAt ch

def sentAtC (ch i : Nat) : Array OnBytes.OracleNotice := (sendsAt ch).getD i #[]

def parAtC (ch i : Nat) : K1.Par := ProofFile.Honest.K2.sendingPar codesW (sentAtC ch i)

/-- How many trees the sendings in front of number i of the chain number ch have laid: the number of the sending's first tree,
as the declared rounds name sources. -/
def treesBeforeC (ch i : Nat) : Nat :=
  ((List.range i).map fun j => ((Own.treesMade codesW (sentAtC ch j)).getD {}).shapes.size).sum

/-- The test at every sending of the chain number ch, on a table of openings. -/
def passAt (T : List ((Nat × Nat) × Nat)) (ch : Nat) : Bool :=
  (List.range (sendsAt ch).length).all fun i => readsWithinTAt T ch (parAtC ch i) (treesBeforeC ch i)

/-- THE COUNT AT THE OTHER TWO CHAINS, with the clause that shuts out an idle yes: every message lies in a tree for which
positions are drawn. -/
def Spec.countAt : Prop :=
  (sendsAt 1).length = 10 ∧ (sendsAt 2).length = 4 ∧ treesBeforeC 1 10 = 11 ∧ treesBeforeC 2 4 = 4 ∧
  ∀ ch ∈ [1, 2],
    ((List.range (sendsAt ch).length).all fun i =>
      (Own.treesMade codesW (sentAtC ch i)).isSome &&
        readsWithinTAt tabM ch (parAtC ch i) (treesBeforeC ch i) &&
        (List.range (sentAtC ch i).size).all fun k =>
          match ((Own.treesMade codesW (sentAtC ch i)).getD {}).tree[k]? with
          | none => false
          | some τ => drawnTabAt tabM ch (treesBeforeC ch i + τ) != 0) = true

/-- The trees that a written cut tells, in order: log-length and words of a column. -/
def cutTreesAt
    (C : List (String × Place × Nat × Nat × List (Nat × List VerifiableInference.Desc.Oracle) × List (Nat × Nat))) :
    List (Nat × Nat) :=
  C.flatMap fun r => r.2.2.2.2.1.flatMap fun x => x.2.map fun o => (o.logLength, o.words)

/-- The trees that the sendings of the chain number ch lay, in order: the same two numbers. -/
def sendTreesAt (ch : Nat) : List (Nat × Nat) :=
  (List.range (sendsAt ch).length).flatMap fun i =>
    ((Own.treesMade codesW (sentAtC ch i)).map fun L =>
      L.shapes.toList.map fun t =>
        (t.logN, t.mainSymbols.foldl (· + ·) 0 + t.maskSymbols.foldl (· + ·) 0)).getD []

/-- NO TREE IS MISSING, BY THE CUT: the cut and the sendings tell one list of trees, on each of the two chains. -/
def Spec.treesTieAt : Prop := cutTreesAt cutSharedFull = sendTreesAt 1 ∧ cutTreesAt cutSecondFull = sendTreesAt 2

/-- The written rounds of the chain number 1 or 2. -/
def declAt (ch : Nat) : List Fmt.DeclaredRound := if ch == 1 then declW.2.1 else declW.2.2

/-- NO TREE IS MISSING, BY THE DECLARED ROUNDS: the rounds that hold roots, in order, hold as many as the sendings lay. -/
def Spec.rootsTieAt : Prop :=
  ∀ ch ∈ [1, 2], (((declAt ch).filter fun d => d.entry.roots != 0).map (·.entry.roots)) =
    (List.range (sendsAt ch).length).map fun i => ((Own.treesMade codesW (sentAtC ch i)).getD {}).shapes.size

/-- WHERE THE TEST BITES, AND WHERE IT HAS ROOM. On the shared chain one more position drawn refuses at nine trees; tree 1 (Omega)
has room for 3465 more and tree 7 (the fold's fresh mask) for 101 more. On the last chain one more refuses at all four. -/
def Spec.countAtEdges : Prop :=
  (∀ n ∈ [0, 2, 3, 4, 5, 6, 8, 9, 10], passAt (((1, n), 1) :: tabM) 1 = false) ∧
  passAt (((1, 1), 3465) :: tabM) 1 = true ∧ passAt (((1, 1), 3466) :: tabM) 1 = false ∧
  passAt (((1, 7), 101) :: tabM) 1 = true ∧ passAt (((1, 7), 102) :: tabM) 1 = false ∧
  ∀ n ∈ [0, 1, 2, 3], passAt (((2, n), 1) :: tabM) 2 = false

end OnBytes.M1
