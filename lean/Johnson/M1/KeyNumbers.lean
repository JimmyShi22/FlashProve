-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/M1/KeyNumbers.lean: M1's count at the key file: every opening of every tree that the key file's three chains send, by any round
of the three chains, summed, against the tails of that tree's rows. Definitions, and each theorem-to-be as a def … : Prop.

Why. A row's random tail hides what the positions drawn show; a simulator of a sending needs that the positions read of a tree are at
most the tail. The key file is the phase in which the weights are committed.

THE WRITTEN VALUES. The rounds are Johnson.G.dryKeyFull, the lists of the dry runs at the full size; a tree that a later chain reads stands
there under its made-up name, which OnBytes.Three.named reads back. The sendings and codes are Johnson/G/SendsWritten.lean's.

THE SHARED CHAIN HAS A SENDING THAT THE WRITTEN LIST DOES NOT HOLD: the fresh mask of the fold at the head of Omega's test goes in its entry
"FOLD epsilon" (Johnson/G/Sends.lean, head). foldSentK lays it in at number 6, from the written shape's first stage of Omega's test.

No property of the protocol is claimed here.
-/
import Johnson.M1.NumbersAt
import Johnson.G.DryKeyLit
import Johnson.G.SendsWritten
import OnBytes.Three.Data
import OnBytes.Params.KeyRec.OnceDefs

set_option autoImplicit false

namespace OnBytes.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At OnBytes.SendSim.Seat
open Johnson.G (dryKeyFull keySends0 keySends1 keySends2 keyCodesWritten ChainSends)
open OnBytes.Three (named)

/-- One chain's openings, at the dry list: each with its source and the positions that its round samples. -/
def opensK (c : Nat) (R : OnBytes.Params.Rounds) : List ((Nat × Nat) × Nat) :=
  R.flatMap fun x => x.1.opens.filterMap fun o => (named c o.2).map fun s => (s, x.1.entry.poss)

/-- The three chains' openings. -/
def tabK : List ((Nat × Nat) × Nat) :=
  opensK 0 dryKeyFull.1 ++ opensK 1 dryKeyFull.2.1 ++ opensK 2 dryKeyFull.2.2

def keyChain (ch : Nat) : ChainSends :=
  if ch == 0 then keySends0 else if ch == 1 then keySends1 else keySends2

def listedK (ch : Nat) : List (Array OracleNotice) := (keyChain ch).sends.map fun s => s.sent.toArray

/-- The fold's own sending, in the entry "FOLD epsilon", at the first stage of Omega's test in the key's written shape. -/
def foldSentK : Array OracleNotice :=
  (OnBytes.Params.keyOnceShape.testOmega.take 1).toArray.map fun s => foldMaskNotice (ioppFoldShape s {})

def sendsK (ch : Nat) : List (Array OracleNotice) :=
  if ch == 1 then (listedK 1).take 6 ++ foldSentK :: (listedK 1).drop 6 else listedK ch

def sentK (ch i : Nat) : Array OracleNotice := (sendsK ch).getD i #[]

def parK (ch i : Nat) : K1.Par := ProofFile.Honest.K2.sendingPar keyCodesWritten (sentK ch i)

def treesBeforeK (ch i : Nat) : Nat :=
  ((List.range i).map fun j => ((Own.treesMade keyCodesWritten (sentK ch j)).getD {}).shapes.size).sum

/-- The test at every sending of the chain number ch, on a table of openings. -/
def passK (T : List ((Nat × Nat) × Nat)) (ch : Nat) : Bool :=
  (List.range (sendsK ch).length).all fun i => readsWithinTAt T ch (parK ch i) (treesBeforeK ch i)

/-- THE DRAWN LINE. -/
def Spec.drawnK : Prop :=
  (List.range 7).map (drawnTabAt tabK 0) = [49, 49, 39, 33, 25, 49, 0] ∧
  (List.range 12).map (drawnTabAt tabK 1) = [97, 98, 146, 52, 52, 52, 49, 49, 49, 49, 39, 0] ∧
  (List.range 5).map (drawnTabAt tabK 2) = [49, 49, 41, 29, 0]

/-- THE COUNT AT THE KEY FILE, with the clause that shuts out an idle yes: every message lies in a tree for which positions are drawn. -/
def Spec.countK : Prop :=
  (sendsK 0).length = 6 ∧ (sendsK 1).length = 10 ∧ (sendsK 2).length = 4 ∧
  treesBeforeK 0 6 = 6 ∧ treesBeforeK 1 10 = 11 ∧ treesBeforeK 2 4 = 4 ∧
  ∀ ch ∈ [0, 1, 2],
    ((List.range (sendsK ch).length).all fun i =>
      (Own.treesMade keyCodesWritten (sentK ch i)).isSome &&
        readsWithinTAt tabK ch (parK ch i) (treesBeforeK ch i) &&
        (List.range (sentK ch i).size).all fun k =>
          match ((Own.treesMade keyCodesWritten (sentK ch i)).getD {}).tree[k]? with
          | none => false
          | some τ => drawnTabAt tabK ch (treesBeforeK ch i + τ) != 0) = true

/-- The written rounds of the chain number ch. -/
def roundsK (ch : Nat) : OnBytes.Params.Rounds :=
  if ch == 0 then dryKeyFull.1 else if ch == 1 then dryKeyFull.2.1 else dryKeyFull.2.2

/-- NO TREE IS MISSING: the rounds that hold roots, in order, hold as many as the sendings lay. -/
def Spec.rootsTieK : Prop :=
  ∀ ch ∈ [0, 1, 2], (((roundsK ch).filter fun d => d.1.entry.roots != 0).map (·.1.entry.roots)) =
    (List.range (sendsK ch).length).map fun i =>
      ((Own.treesMade keyCodesWritten (sentK ch i)).getD {}).shapes.size

/-- THE TABLE NAMES NO TREE OUTSIDE THE THREE CHAINS. -/
def Spec.tabWithinK : Prop :=
  (tabK.all fun x => (x.1.1 == 0 && decide (x.1.2 < 6)) || (x.1.1 == 1 && decide (x.1.2 < 11)) ||
    (x.1.1 == 2 && decide (x.1.2 < 4))) = true

/-- WHERE THE TEST BITES, AND WHERE IT HAS ROOM: one more position refuses at every tree but the fold's, tree 7 of the shared chain, which has
room for 97. -/
def Spec.edgesK : Prop :=
  (∀ n ∈ [0, 1, 2, 3, 4, 5], passK (((0, n), 1) :: tabK) 0 = false) ∧
  (∀ n ∈ [0, 1, 2, 3, 4, 5, 6, 8, 9, 10], passK (((1, n), 1) :: tabK) 1 = false) ∧
  passK (((1, 7), 97) :: tabK) 1 = true ∧ passK (((1, 7), 98) :: tabK) 1 = false ∧
  (∀ n ∈ [0, 1, 2, 3], passK (((2, n), 1) :: tabK) 2 = false)

end OnBytes.M1
