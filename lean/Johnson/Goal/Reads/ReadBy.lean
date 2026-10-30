-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Reads/ReadBy.lean: the further public reading of the goals' verifier WITH ITS LIST OF
PARAMETER BYTES, AND THE PLANNER BENEATH THAT LIST, AS LETTERS: no hash function and no planner is
named in this file's definitions. Definitions, and the laws of Ladder/ReadThru.lean once more,
general in these letters.

Why. `VerifierAndGoals.readMoreAt` (Ladder/ReadThru.lean) asks the strings of `par7`
(Johnson/Top/PreThreePub.lean), whose planner's text (`plannedAt`) calls the second hash function
by name. A description that takes that function as its argument o (the goals hand it so:
`SecondHashFunctionType → Description`, Ladder.lean) needs the same reading over a planner that takes o. Here
the text of each of the two stands once more with the part that names a hash as a
letter, and `par7`, `readMoreAt` and `readBoth` are these at `plannedAt`, by definition.

Main names.
  `par7By pl G c`: `par7`'s text over any planner pl. `par7By_plannedAt`: at `plannedAt` it is
    `par7`.
  `readMoreBy par c`: `readMoreAt`'s text over any list par. `readMoreAt_eq_by`: at `par7` it is
    `readMoreAt`. `readBothBy`, `readBoth_eq_by`: the like for the two readings together.
  `readMoreBy_evaluate`, `readBothBy_evaluate`, `readBothBy_reads`, `length_par7By_ok`,
    `length_par7By_error`, `length_readMoreBy`, `readMoreBy_of`, `readBothBy_of`: ReadThru's laws.
  `readMoreBy_congr`: two lists that agree at the digest's bytes give one reading.

Limits. Those of Ladder/ReadThru.lean. Nothing says which planner a description lays in, nor that a
planner over o names no hash: that is a walk's or another file's matter. `entryXD G c` stands in
`par7By` as it does in `par7`. The public algorithm in `readBothBy_reads` is `pubN` at the letters;
that it is `pub8` at `par7` is `pub8`'s definition. No bound on the number of queries. Nothing on
soundness.

-/
import Ladder.ReadThru

set_option autoImplicit false

namespace VerifierAndGoals
open VerifiableInference OnBytes.K.Arm.Pub OnBytes.Tie
open Rom TypedOracleCompiler.Slice TypedOracleCompiler.Compile.Batch.Cms
open _root_.Run (digToBytes bytesToDig bytesToBits toBytes)

/-- `par7`'s text over a planner pl: the entry's chain's parameter bytes as the ground G spells
them; then, where pl returns a plan at c, the proof's three and the key's three. -/
def par7By (pl : ByteArray → Except String OnBytes.Model.Verify.Planned) (G : EntryGround)
    (c : ByteArray) : List ByteArray :=
  (entryXD G c).base.params ::
    match pl c with
    | .error _ => []
    | .ok p =>
      [p.chains.proof.first.given.bytes, p.chains.proof.shared.given.bytes,
        p.chains.proof.second.given.bytes, p.chains.key.oneTime.given.bytes,
        p.chains.key.shared.given.bytes, p.chains.key.second.given.bytes]

/-- At `plannedAt` it is `par7`. By definition. -/
theorem par7By_plannedAt (G : EntryGround) (pol KL lay : ByteArray) :
    par7By (plannedAt pol KL (some lay)) G = par7 G pol KL lay := rfl

/-- Planners that return the same at c give the same list at c. -/
theorem par7By_congr {pl pl' : ByteArray → Except String OnBytes.Model.Verify.Planned}
    (G : EntryGround) (c : ByteArray) (h : pl c = pl' c) : par7By pl G c = par7By pl' G c := by
  unfold par7By
  rw [h]

/-- Where the planner returns a plan, seven strings. -/
theorem length_par7By_ok (pl : ByteArray → Except String OnBytes.Model.Verify.Planned)
    (G : EntryGround) (c : ByteArray) {p : _} (h : pl c = .ok p) :
    (par7By pl G c).length = 7 := by
  unfold par7By
  rw [h]
  rfl

/-- Where it refuses, one. -/
theorem length_par7By_error (pl : ByteArray → Except String OnBytes.Model.Verify.Planned)
    (G : EntryGround) (c : ByteArray) {e : _} (h : pl c = .error e) :
    (par7By pl G c).length = 1 := by
  unfold par7By
  rw [h]
  rfl

/-- The further public reading over a list par of parameter bytes: its strings at the digest c, in
order. -/
def readMoreBy (par : ByteArray → List ByteArray) (c : Digest) :
    DeterministicAlgorithm (List Digest) :=
  askList (ssOf par c)

/-- At `par7` it is `readMoreAt`. By definition. -/
theorem readMoreAt_eq_by (G : EntryGround) (Z : PublicFiles) :
    readMoreAt G Z = readMoreBy (par7 G Z.pol Z.KL Z.lay) := rfl

/-- Two lists that agree at the digest's bytes give one reading. -/
theorem readMoreBy_congr {par par' : ByteArray → List ByteArray} (c : Digest)
    (h : par (digToBytes c) = par' (digToBytes c)) : readMoreBy par c = readMoreBy par' c := by
  unfold readMoreBy ssOf
  rw [h]

/-- It returns the answers at the list's strings. -/
theorem readMoreBy_evaluate (hash : VerifiableInference.Hash) (par : ByteArray → List ByteArray)
    (c : Digest) :
    (readMoreBy par c).evaluate hash = ((par (digToBytes c)).map sParOf).map hash := by
  unfold readMoreBy ssOf
  rw [evaluate_askList]

/-- It returns as many digests as there are strings. -/
theorem length_readMoreBy (hash : VerifiableInference.Hash) (par : ByteArray → List ByteArray)
    (c : Digest) : ((readMoreBy par c).evaluate hash).length = (par (digToBytes c)).length := by
  rw [readMoreBy_evaluate, List.length_map, List.length_map]

/-- The two readings, one behind the other, as `verify` makes them. -/
def readBothBy (par : ByteArray → List ByteArray) (Z : PublicFiles) :
    DeterministicAlgorithm (Digest × List Digest) :=
  andThen (readConfig Z) fun c => andThen (readMoreBy par c) fun m => .done (c, m)

/-- At `par7` they are `readBoth`. By definition. -/
theorem readBoth_eq_by (G : EntryGround) (Z : PublicFiles) :
    readBoth G Z = readBothBy (par7 G Z.pol Z.KL Z.lay) Z := rfl

/-- What the two readings return together. -/
theorem readBothBy_evaluate (hash : VerifiableInference.Hash) (par : ByteArray → List ByteArray)
    (Z : PublicFiles) :
    (readBothBy par Z).evaluate hash =
      (hash (s0Of Z.pol Z.lay Z.KL),
        ((par (digToBytes (hash (s0Of Z.pol Z.lay Z.KL)))).map sParOf).map hash) := by
  unfold readBothBy
  rw [evaluate_andThen, evaluate_andThen, readMoreBy_evaluate, readConfig_evaluate]
  rfl

/-- **The condition "reads"**: at every hash function the two readings return the value of the
public algorithm `pubN` at the string of the three public files and the list's strings. -/
theorem readBothBy_reads (par : ByteArray → List ByteArray) (Z : PublicFiles)
    (hash : VerifiableInference.Hash) :
    (readBothBy par Z).evaluate hash =
      (pubN Prod.mk (s0Of Z.pol Z.lay Z.KL) (ssOf par)).det fun _ => hash := by
  rw [readBothBy_evaluate, pubN_det]
  rfl

/-- **The further reading through O**: O's answers at the list's strings. -/
theorem readMoreBy_of (O : ByteArray → ByteArray) (par : ByteArray → List ByteArray) (c : Digest) :
    (readMoreBy par c).evaluate (ofBytes O) =
      ((par (digToBytes c)).map fun b => O (chainBytesString b)).map bytesToDig := by
  rw [readMoreBy_evaluate, List.map_map, List.map_map]
  exact List.map_congr_left fun b _ => ofBytes_oStr O 169 0 1 _ b

/-- **The two readings through O**, where O's answer at the first public string has 32 bytes. -/
theorem readBothBy_of (O : ByteArray → ByteArray) (par : ByteArray → List ByteArray) (Z : PublicFiles)
    (h : (O (configBytesString Z)).size = 32) :
    (readBothBy par Z).evaluate (ofBytes O) =
      (bytesToDig (O (configBytesString Z)),
        ((par (O (configBytesString Z))).map fun b => O (chainBytesString b)).map bytesToDig) := by
  unfold readBothBy
  rw [evaluate_andThen, evaluate_andThen, readMoreBy_of, readConfig_of,
    _root_.Run.digToBytes_bytesToDig _ h]
  rfl

end VerifierAndGoals

#print axioms VerifierAndGoals.par7By_plannedAt
#print axioms VerifierAndGoals.par7By_congr
#print axioms VerifierAndGoals.length_par7By_ok
#print axioms VerifierAndGoals.length_par7By_error
#print axioms VerifierAndGoals.readMoreAt_eq_by
#print axioms VerifierAndGoals.readMoreBy_congr
#print axioms VerifierAndGoals.readMoreBy_evaluate
#print axioms VerifierAndGoals.length_readMoreBy
#print axioms VerifierAndGoals.readBoth_eq_by
#print axioms VerifierAndGoals.readBothBy_evaluate
#print axioms VerifierAndGoals.readBothBy_reads
#print axioms VerifierAndGoals.readMoreBy_of
#print axioms VerifierAndGoals.readBothBy_of
