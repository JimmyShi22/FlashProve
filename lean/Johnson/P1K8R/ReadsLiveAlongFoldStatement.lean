-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/ReadsLiveAlongFoldStatement.lean: AT THE OUTPUT HEAD's SEGMENT, ALONG ONE FOLD: FROM A
STATE sk THAT HOLDS x AS WHAT WAS HEARD AT THE HEAD, OVER THE FIVE MEMBERS 342 .. 346 OF THE FIRST
CHAIN's FLAT LIST, TO THE STATE s' IN FRONT OF THE BATCHING: UNDER `HeardFine` AT THAT VERY x
(ReadsLiveAtBatchStatement.lean of this folder) THE TEST `readsLive`
(Johnson/Desc/K8/Honest/LinkedFew.lean) SAYS YES AT s'. In the goals' scope, at an opening's
letters. STATEMENTS ALONE: three definitions of propositions; no definition of another kind. NOTHING
IS PROVED IN THIS FILE, and none is one of the library's goals: they are lemmas' statements.

WHY. A statement of the form "there are a state reached at 343 and an x that it holds, such that .."
hands its own x. Whoever holds a run, with the x behind the head's own sub-protocol's step in hand,
cannot call it: two walks back along "reached" may end at two states. Here the x is the caller's,
and the five members are met along the caller's own fold.

WHAT IT IS NOT. CONDITIONAL: the fold's yes, "reached" at 347 and `HeardFine` are premises; none is
shown of anything here. NOTHING TIES THE FOLD AND "REACHED" BUT THE STATE s' THAT BOTH END IN. The
head's segment alone. At the format's second hash function alone (OnBytes.secondHashFunction). The full size alone.

  `KeptByReads`          a yes of the block of the reads' place, at a built segment of kind 2, keeps
                         what the head's link holds as heard (`Kept`,
                         Johnson/Desc/Reads/LiesBehind.lean)
  `Member342Of`          number 342 of the flat list decides every relation that such a block
                         decides
  `ReadsLiveAlongFold`   the title

NEAR. `tablesCome_at_reads` (Johnson/Desc/K1/Law/ArmHead.lean) with `TablesCome`
(Johnson/Desc/Kinds/Law/FourRunsTie.lean) and `withTables_iff` (K6Silent.lean): the tables made at
the x of the state in front of the reads' member are the list behind it, its matrices and their
number the plan's: under "the tables return". `Core`, `core_of_steps`, `core_of_pieces`
(LiesBehind.lean): 21 clauses behind the two steps. `wide_stays` (WideToRun.lean of this folder):
called. `HeadListAt343`, `HeadListAt347` (HeadListAtBatchStatement.lean): at states under "there
is".

Limits. A yes of a test with code, under premises. Nothing on any property.
-/
import Johnson.P1K8R.ReadsLiveAtBatchStatement
import Johnson.Desc.Reads.LiesBehind
import Johnson.IMR.K1Seat
import Johnson.Desc.FoldKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Decides)
open VerifiableInference.Desc.First.K8.Honest (readsLive)
open VerifiableInference.Reads.AtSeat (Kept)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- The statement on the reads' block. Not proved here; a lemma's statement, none of the library's
goals. -/
def KeptByReads : Prop :=
  ∀ (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : Nat) (X : Stages.LinkH) (pr : Nat)
    (reads : Option (List Nat)), G.built[l]? = some X → X.kind = 2 →
    Decides Kept (IM.k1Reads Z G l X pr reads)

/-- The statement on member 342. Not proved here; a lemma's statement, none of the library's goals.
-/
def Member342Of : Prop :=
  ∀ (P : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (lay : ByteArray) (F : FileDescription ProofFile.Inst) (Z : ProofFile.Pub)
    (Bs : ProofFile.PureBase) (base : List (Block S ProofFile.Cl)) (c : Chain S ProofFile.Cl) (A : ProofFile.SharedSeat)
    (B : ProofFile.SecondSeat), VerifierAndGoals.InScope P = true → VerifierAndGoals.readFiles P = .ok pp →
    IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B → ∀ (R : S → S → Prop),
      (∀ Xl pr reads, Bs.G₀.built[24]? = some Xl → Xl.kind = 2 →
        Decides R (IM.k1Reads Z Bs.G₀ 24 Xl pr reads)) →
      ∃ b, c.blocksInOrder[342]? = some b ∧ Decides R b

/-- **The statement of the title.** Not proved here; a lemma's statement, none of the library's
goals. -/
def ReadsLiveAlongFold : Prop :=
  ∀ (P : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (lay : ByteArray) (F : FileDescription ProofFile.Inst) (Z : ProofFile.Pub)
    (Bs : ProofFile.PureBase) (base : List (Block S ProofFile.Cl)) (c : Chain S ProofFile.Cl) (A : ProofFile.SharedSeat)
    (B : ProofFile.SecondSeat), VerifierAndGoals.InScope P = true → VerifierAndGoals.readFiles P = .ok pp →
    IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B →
    ∀ (sk s' : S) (o : VerifiableInference.Desc.First.HeadOwn) (x : Head.Heard)
      (r₂ r₃ : List Fmt.RoundView) (c₂ c₃ : List VerifiableInference.Desc.OpenedColumn) (z : ProofFile.InstPub),
      sk.here = .head o → o.x = some x →
      foldBlocks 0 ((c.blocksInOrder.take 347).drop 342) sk r₂ c₂ = .ok (s', r₃, c₃) →
      Reach 0 c.blocksInOrder (ProofFile.startS Z) 347 (z, s') → HeardFine Bs.G₀.W.hS x →
      ∃ tl, s'.tl? = some tl ∧ readsLive tl = true

end P1K8

#print axioms P1K8.KeptByReads
#print axioms P1K8.Member342Of
#print axioms P1K8.ReadsLiveAlongFold
