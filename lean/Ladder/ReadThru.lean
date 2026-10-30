-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ladder/ReadThru.lean: what the two public readings of the goals' verifier return, at any hash
function: the hash function's answers at the format's eight public strings.

`verify` (Ladder.lean) first asks the digest of the three public files (`readConfig`), then lets the
description ask for more (`readMore`). Here: the law of evaluation of `andThen`; `askList`, which
asks the strings of a list in order; `readMoreAt G`, the further reading that asks the seven chains'
strings at a ground G for the entry's chain; and what each returns.

Then the same at the hash function on bit strings that a function O from bytes to bytes makes
(`TypedOracleCompiler.Run.PageRun.gOf O ()`): the answers are O's own, at the strings as bytes.

Main statements: `evaluate_andThen`, `readConfig_evaluate`, `readMoreAt_evaluate`,
`readBoth_evaluate`; `readBoth_reads`; `readConfig_of`, `readMoreAt_of`, `readBoth_of`.
`readBoth_reads` is the condition "reads" of the theorem on a verifier that is told its public part
(`LayoutsByPublicReading.ladder_yes`, Johnson/Top/InnerCompiledVerifierByPublicReading.lean), at the public algorithm `pub8`
(Johnson/Top/PreThreePub.lean): at every hash function the two readings return `pub8`'s value.

Limits. "Seven" strings are asked only where the planner's text returns a plan at the digest's
bytes; where it refuses, `par7` holds the entry's chain's bytes alone and ONE string is asked
(`length_par7_ok`, `length_par7_error`, `length_readMoreAt`): the reading goes on, and whoever uses
it has to test the number or the planner's yes. The ground G is free: nothing here says that it fits
the files. The answers are digests of 256 bits; in the forms at a function O on bytes nothing is
asked of the length of O's seven further answers, and `bytesToDig` is one to one at 32 bytes alone.
These forms speak of the hash functions that some O makes. No bound on the number of queries is
here, and `askList` asks a string again that stands twice in its list. The second hash
function stands by name beneath `par7`.

-/
import Ladder
import Johnson.Top.PreThreePub
import Johnson.Top.Pub.PubMany
import Run.ParserHashProofs
import OnBytes.TypedOracleCompiler.Run.PageRunFast

set_option autoImplicit false

namespace VerifierAndGoals
open VerifiableInference OnBytes.K.Arm.Pub OnBytes.Tie
open _root_.Run (digToBytes bytesToDig bytesToBits toBytes)

/-- To evaluate `andThen a f` is to evaluate a, then f at its result. -/
theorem evaluate_andThen {α β : Type} (hash : VerifiableInference.Hash)
    (f : α → DeterministicAlgorithm β) :
    ∀ a : DeterministicAlgorithm α,
      (andThen a f).evaluate hash = (f (a.evaluate hash)).evaluate hash
  | .done _ => rfl
  | .query s k => evaluate_andThen hash f (k (hash s))

/-- Ask the strings of a list, in order. -/
def askList : List BitString → DeterministicAlgorithm (List Digest)
  | [] => .done []
  | s :: l => .query s fun a => andThen (askList l) fun r => .done (a :: r)

/-- It returns the hash function's answers, in order. -/
theorem evaluate_askList (hash : VerifiableInference.Hash) :
    ∀ l : List BitString, (askList l).evaluate hash = l.map hash
  | [] => rfl
  | s :: l => by
      show (andThen (askList l) fun r => .done (hash s :: r)).evaluate hash = hash s :: l.map hash
      rw [evaluate_andThen, evaluate_askList hash l]
      rfl

/-- The further public reading at a ground G for the entry's chain: the seven chains' strings at the
digest c, in order. -/
def readMoreAt (G : EntryGround) (Z : PublicFiles) (c : Digest) : DeterministicAlgorithm (List Digest) :=
  askList (ssOf (par7 G Z.pol Z.KL Z.lay) c)

/-- The first reading returns the answer at the first public string. -/
theorem readConfig_evaluate (hash : VerifiableInference.Hash) (Z : PublicFiles) :
    (readConfig Z).evaluate hash = hash (s0Of Z.pol Z.lay Z.KL) := rfl

/-- The further reading returns the answers at the seven further public strings. -/
theorem readMoreAt_evaluate (hash : VerifiableInference.Hash) (G : EntryGround) (Z : PublicFiles)
    (c : Digest) :
    (readMoreAt G Z c).evaluate hash =
      ((par7 G Z.pol Z.KL Z.lay (digToBytes c)).map sParOf).map hash := by
  unfold readMoreAt ssOf
  rw [evaluate_askList]

/-- The two readings, one behind the other, as `verify` makes them. -/
def readBoth (G : EntryGround) (Z : PublicFiles) : DeterministicAlgorithm (Digest × List Digest) :=
  andThen (readConfig Z) fun c => andThen (readMoreAt G Z c) fun m => .done (c, m)

/-- What the two readings return together. -/
theorem readBoth_evaluate (hash : VerifiableInference.Hash) (G : EntryGround) (Z : PublicFiles) :
    (readBoth G Z).evaluate hash =
      (hash (s0Of Z.pol Z.lay Z.KL),
        ((par7 G Z.pol Z.KL Z.lay (digToBytes (hash (s0Of Z.pol Z.lay Z.KL)))).map sParOf).map
          hash) := by
  unfold readBoth
  rw [evaluate_andThen, evaluate_andThen, readMoreAt_evaluate, readConfig_evaluate]
  rfl

/-- **The condition "reads"**: at every hash function the two readings return the value of the
public algorithm `pub8`. -/
theorem readBoth_reads (G : EntryGround) (Z : PublicFiles) (hash : VerifiableInference.Hash) :
    (readBoth G Z).evaluate hash = (pub8 G Z.pol Z.KL Z.lay).det fun _ => hash := by
  rw [readBoth_evaluate, pub8_det]
  rfl

/-- Where the planner's text returns a plan, seven strings are asked. -/
theorem length_par7_ok (G : EntryGround) (pol KL lay c : ByteArray) {p : _}
    (h : plannedAt pol KL (some lay) c = .ok p) : (par7 G pol KL lay c).length = 7 := by
  unfold par7
  rw [h]
  rfl

/-- Where it refuses, one. -/
theorem length_par7_error (G : EntryGround) (pol KL lay c : ByteArray) {e : _}
    (h : plannedAt pol KL (some lay) c = .error e) : (par7 G pol KL lay c).length = 1 := by
  unfold par7
  rw [h]
  rfl

/-- The further reading returns as many digests as there are strings. -/
theorem length_readMoreAt (hash : VerifiableInference.Hash) (G : EntryGround) (Z : PublicFiles)
    (c : Digest) :
    ((readMoreAt G Z c).evaluate hash).length =
      (par7 G Z.pol Z.KL Z.lay (digToBytes c)).length := by
  rw [readMoreAt_evaluate, List.length_map, List.length_map]

/-! ## At the hash function that a function on bytes makes -/

/-- The hash function on bit strings that a function from bytes to bytes makes. -/
abbrev ofBytes (O : ByteArray → ByteArray) : VerifiableInference.Hash :=
  fun s => TypedOracleCompiler.Run.PageRun.gOf O () s

/-- The string of the call that hashes the three public files, as bytes. -/
def configBytesString (Z : PublicFiles) : ByteArray :=
  Fmt.oStr 0 169 0 2 Fmt.zero32 (Fmt.configBytes [Z.pol, Z.lay, Z.KL])

/-- The string of the call that hashes a chain's parameter bytes, as bytes. -/
def chainBytesString (b : ByteArray) : ByteArray := Fmt.oStr 0 169 0 1 Fmt.zero32 b

/-- At the bits of a call's string it answers O at the string. -/
theorem ofBytes_oStr (O : ByteArray → ByteArray) (n t i : ℕ) (st bs : ByteArray) :
    ofBytes O (bytesToBits (Fmt.oStr 0 n t i st bs)) = bytesToDig (O (Fmt.oStr 0 n t i st bs)) := by
  show bytesToDig (O (toBytes (bytesToBits (Fmt.oStr 0 n t i st bs)))) = _
  rw [_root_.Run.toBytes_plain _ (_root_.Run.plain_oStr 0 n t i st bs (Or.inl rfl)),
    _root_.Run.bitsToBytes_bytesToBits]

/-- **The first reading through O**: O's answer at the first public string. -/
theorem readConfig_of (O : ByteArray → ByteArray) (Z : PublicFiles) :
    (readConfig Z).evaluate (ofBytes O) = bytesToDig (O (configBytesString Z)) :=
  ofBytes_oStr O 169 0 2 _ _

/-- **The further reading through O**: O's answers at the seven further public strings. -/
theorem readMoreAt_of (O : ByteArray → ByteArray) (G : EntryGround) (Z : PublicFiles) (c : Digest) :
    (readMoreAt G Z c).evaluate (ofBytes O) =
      ((par7 G Z.pol Z.KL Z.lay (digToBytes c)).map fun b => O (chainBytesString b)).map
        bytesToDig := by
  rw [readMoreAt_evaluate, List.map_map, List.map_map]
  exact List.map_congr_left fun b _ => ofBytes_oStr O 169 0 1 _ b

/-- **The two readings through O**, where O's answer at the first public string has 32 bytes: the
seven are asked at that very answer. -/
theorem readBoth_of (O : ByteArray → ByteArray) (G : EntryGround) (Z : PublicFiles)
    (h : (O (configBytesString Z)).size = 32) :
    (readBoth G Z).evaluate (ofBytes O) =
      (bytesToDig (O (configBytesString Z)),
        ((par7 G Z.pol Z.KL Z.lay (O (configBytesString Z))).map fun b =>
          O (chainBytesString b)).map bytesToDig) := by
  unfold readBoth
  rw [evaluate_andThen, evaluate_andThen, readMoreAt_of, readConfig_of,
    _root_.Run.digToBytes_bytesToDig _ h]
  rfl

end VerifierAndGoals

#print axioms VerifierAndGoals.evaluate_andThen
#print axioms VerifierAndGoals.readConfig_evaluate
#print axioms VerifierAndGoals.readMoreAt_evaluate
#print axioms VerifierAndGoals.readBoth_evaluate
#print axioms VerifierAndGoals.readConfig_of
#print axioms VerifierAndGoals.readMoreAt_of
#print axioms VerifierAndGoals.readBoth_of
#print axioms VerifierAndGoals.readBoth_reads
#print axioms VerifierAndGoals.length_par7_ok
#print axioms VerifierAndGoals.length_readMoreAt
