-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Reads/ReadAtSecondHashFunction.lean: the further public reading of the goals' verifier with the
format's second hash function as an argument o. Definitions, and their laws.

`par7O o`, `readMoreAtO o`, `readBothO o`, `pub8O o`: `par7`
(Johnson/Top/PreThreePub.lean), `readMoreAt`, `readBoth` (Ladder/ReadThru.lean) and `pub8` over the
planner's text at o (`plannedAtO`), by the general forms of Johnson/Goal/Reads/ReadBy.lean. A
description that takes o (`SecondHashFunctionType → Description`, Ladder.lean) can lay `readMoreAtO o` as its further
reading.

Main statements.
  `par7O_of_eq`, `readMoreAtO_of_eq`, `readBothO_of_eq`, `pub8O_of_eq`: where the planner's text at
    o returns what `OnBytes.Tie.plannedAt` returns, these four are the four without O in the name.
  `par7O_older`, `readMoreAtO_older`, `readBothO_older`, `pub8O_older`: so at o := `OnBytes.secondHashFunction`
    they are the same four, by `plannedAtO_older` (Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean):
    every theorem on those names carries over by rewriting.
  `readMoreAtO_evaluate`, `readBothO_evaluate`, `readBothO_reads`, `length_par7O_ok`,
    `length_par7O_error`, `readMoreAtO_of`, `readBothO_of`: the laws of Ladder/ReadThru.lean at o.
  `length_par7O_le`: at most seven strings are asked, whatever the planner returns.
  `pub8O_noCoin`, `pub8O_noRepeat`, `pub8O_asks169`, `pub8O_det`: what a bound asks of a public
    algorithm, as for `pub8`.

Limits. Those of Ladder/ReadThru.lean and Johnson/Top/PreThreePub.lean. That nothing beneath
`plannedAtO o` names a hash function is not said here. The strings that are asked hang on o's values
at the three public files. No bound on the number of queries. Nothing on soundness. `par7O`,
`readMoreAtO` and `readBothO` have compiled code; `pub8O` has none, like `pub8`.

-/
import Johnson.Goal.Reads.ReadBy
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws

set_option autoImplicit false

namespace VerifierAndGoals
open VerifiableInference OnBytes.K.Arm.Pub OnBytes.Tie
open Rom TypedOracleCompiler.Slice TypedOracleCompiler.Compile.Batch.Cms
open _root_.Run (digToBytes bytesToDig bytesToBits toBytes)
open VerifiableInference.PlanWritten (plannedAtO plannedAtO_older)

/-- The parameter bytes at the bytes c for the digest, over the planner's text at o. -/
def par7O (o : SecondHashFunctionType) (G : EntryGround) (pol KL lay : ByteArray) : ByteArray → List ByteArray :=
  par7By (plannedAtO o pol KL (some lay)) G

/-- The further public reading at o. -/
def readMoreAtO (o : SecondHashFunctionType) (G : EntryGround) (Z : PublicFiles) (c : Digest) :
    DeterministicAlgorithm (List Digest) :=
  readMoreBy (par7O o G Z.pol Z.KL Z.lay) c

/-- The two readings at o, one behind the other. -/
def readBothO (o : SecondHashFunctionType) (G : EntryGround) (Z : PublicFiles) :
    DeterministicAlgorithm (Digest × List Digest) :=
  readBothBy (par7O o G Z.pol Z.KL Z.lay) Z

/-- The public algorithm at o. -/
noncomputable def pub8O (o : SecondHashFunctionType) (G : EntryGround) (pol KL lay : ByteArray) :
    OComp (rom 256) D8 :=
  pubN Prod.mk (s0Of pol lay KL) (ssOf (par7O o G pol KL lay))

/-! ## Where the planner's text at o is `OnBytes.Tie.plannedAt` -/

theorem par7O_of_eq (o : SecondHashFunctionType) (G : EntryGround) (pol KL lay : ByteArray)
    (h : ∀ c, plannedAtO o pol KL (some lay) c = plannedAt pol KL (some lay) c) :
    par7O o G pol KL lay = par7 G pol KL lay :=
  funext fun c => par7By_congr G c (h c)

theorem readMoreAtO_of_eq (o : SecondHashFunctionType) (G : EntryGround) (Z : PublicFiles)
    (h : ∀ c, plannedAtO o Z.pol Z.KL (some Z.lay) c = plannedAt Z.pol Z.KL (some Z.lay) c) :
    readMoreAtO o G Z = readMoreAt G Z := by
  unfold readMoreAtO
  rw [par7O_of_eq o G Z.pol Z.KL Z.lay h]
  rfl

theorem readBothO_of_eq (o : SecondHashFunctionType) (G : EntryGround) (Z : PublicFiles)
    (h : ∀ c, plannedAtO o Z.pol Z.KL (some Z.lay) c = plannedAt Z.pol Z.KL (some Z.lay) c) :
    readBothO o G Z = readBoth G Z := by
  unfold readBothO
  rw [par7O_of_eq o G Z.pol Z.KL Z.lay h]
  rfl

theorem pub8O_of_eq (o : SecondHashFunctionType) (G : EntryGround) (pol KL lay : ByteArray)
    (h : ∀ c, plannedAtO o pol KL (some lay) c = plannedAt pol KL (some lay) c) :
    pub8O o G pol KL lay = pub8 G pol KL lay := by
  unfold pub8O
  rw [par7O_of_eq o G pol KL lay h]
  rfl

/-! ## At the format's second hash function itself -/

/-- **At `OnBytes.secondHashFunction` the list is `par7`.** -/
theorem par7O_older (G : EntryGround) (pol KL lay : ByteArray) :
    par7O OnBytes.secondHashFunction G pol KL lay = par7 G pol KL lay :=
  par7O_of_eq _ G pol KL lay fun c => plannedAtO_older pol KL (some lay) c

/-- **At `OnBytes.secondHashFunction` the further reading is `readMoreAt`.** -/
theorem readMoreAtO_older (G : EntryGround) (Z : PublicFiles) :
    readMoreAtO OnBytes.secondHashFunction G Z = readMoreAt G Z :=
  readMoreAtO_of_eq _ G Z fun c => plannedAtO_older Z.pol Z.KL (some Z.lay) c

theorem readBothO_older (G : EntryGround) (Z : PublicFiles) :
    readBothO OnBytes.secondHashFunction G Z = readBoth G Z :=
  readBothO_of_eq _ G Z fun c => plannedAtO_older Z.pol Z.KL (some Z.lay) c

theorem pub8O_older (G : EntryGround) (pol KL lay : ByteArray) :
    pub8O OnBytes.secondHashFunction G pol KL lay = pub8 G pol KL lay :=
  pub8O_of_eq _ G pol KL lay fun c => plannedAtO_older pol KL (some lay) c

/-! ## The laws at o -/

/-- At most seven strings, whatever the planner returns. -/
theorem length_par7By_le (pl : ByteArray → Except String OnBytes.Model.Verify.Planned)
    (G : EntryGround) (c : ByteArray) : (par7By pl G c).length ≤ 7 := by
  unfold par7By
  split <;> simp

theorem length_par7O_le (o : SecondHashFunctionType) (G : EntryGround) (pol KL lay c : ByteArray) :
    (par7O o G pol KL lay c).length ≤ 7 :=
  length_par7By_le _ G c

theorem length_par7O_ok (o : SecondHashFunctionType) (G : EntryGround) (pol KL lay c : ByteArray) {p : _}
    (h : plannedAtO o pol KL (some lay) c = .ok p) : (par7O o G pol KL lay c).length = 7 :=
  length_par7By_ok _ G c h

theorem length_par7O_error (o : SecondHashFunctionType) (G : EntryGround) (pol KL lay c : ByteArray) {e : _}
    (h : plannedAtO o pol KL (some lay) c = .error e) : (par7O o G pol KL lay c).length = 1 :=
  length_par7By_error _ G c h

theorem readMoreAtO_evaluate (hash : VerifiableInference.Hash) (o : SecondHashFunctionType) (G : EntryGround)
    (Z : PublicFiles) (c : Digest) :
    (readMoreAtO o G Z c).evaluate hash =
      ((par7O o G Z.pol Z.KL Z.lay (digToBytes c)).map sParOf).map hash :=
  readMoreBy_evaluate hash _ c

theorem readBothO_evaluate (hash : VerifiableInference.Hash) (o : SecondHashFunctionType) (G : EntryGround)
    (Z : PublicFiles) :
    (readBothO o G Z).evaluate hash =
      (hash (s0Of Z.pol Z.lay Z.KL),
        ((par7O o G Z.pol Z.KL Z.lay (digToBytes (hash (s0Of Z.pol Z.lay Z.KL)))).map sParOf).map
          hash) :=
  readBothBy_evaluate hash _ Z

/-- **The condition "reads" at o**: at every hash function the two readings return the value of the
public algorithm at o. -/
theorem readBothO_reads (o : SecondHashFunctionType) (G : EntryGround) (Z : PublicFiles)
    (hash : VerifiableInference.Hash) :
    (readBothO o G Z).evaluate hash = (pub8O o G Z.pol Z.KL Z.lay).det fun _ => hash :=
  readBothBy_reads _ Z hash

theorem readMoreAtO_of (O : ByteArray → ByteArray) (o : SecondHashFunctionType) (G : EntryGround) (Z : PublicFiles)
    (c : Digest) :
    (readMoreAtO o G Z c).evaluate (ofBytes O) =
      ((par7O o G Z.pol Z.KL Z.lay (digToBytes c)).map fun b => O (chainBytesString b)).map
        bytesToDig :=
  readMoreBy_of O _ c

theorem readBothO_of (O : ByteArray → ByteArray) (o : SecondHashFunctionType) (G : EntryGround) (Z : PublicFiles)
    (h : (O (configBytesString Z)).size = 32) :
    (readBothO o G Z).evaluate (ofBytes O) =
      (bytesToDig (O (configBytesString Z)),
        ((par7O o G Z.pol Z.KL Z.lay (O (configBytesString Z))).map fun b =>
          O (chainBytesString b)).map bytesToDig) :=
  readBothBy_of O _ Z h

/-! ## What a bound asks of a public algorithm -/

theorem pub8O_noCoin (o : SecondHashFunctionType) (G : EntryGround) (pol KL lay : ByteArray) :
    (pub8O o G pol KL lay).NoCoin := pubN_noCoin _ _ _

theorem pub8O_det (o : SecondHashFunctionType) (G : EntryGround) (pol KL lay : ByteArray) (g : Fam (rom 256)) :
    (pub8O o G pol KL lay).det g =
      (g () (s0Of pol lay KL),
        (ssOf (par7O o G pol KL lay) (g () (s0Of pol lay KL))).map (answerAt g)) :=
  pubN_det Prod.mk _ _ g

theorem pub8O_noRepeat (o : SecondHashFunctionType) (G : EntryGround) (pol KL lay : ByteArray) :
    NoRepeat (pub8O o G pol KL lay) := pubN_noRepeat _ _ _

theorem pub8O_asks169 (o : SecondHashFunctionType) (G : EntryGround) (pol KL lay : ByteArray) :
    (pub8O o G pol KL lay).AsksIn fun _ (s : List Bool) => OnBytes.Slice.IsCall169 s :=
  pubN_asksIn_of _ _ _ OnBytes.Slice.IsCall169 ⟨0, 0, 2, Fmt.zero32, _, Or.inl rfl, rfl, rfl⟩
    fun c s hs => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 hs
      exact ⟨0, 0, 1, Fmt.zero32, _, Or.inl rfl, rfl, rfl⟩

end VerifierAndGoals

#print axioms VerifierAndGoals.par7O_of_eq
#print axioms VerifierAndGoals.readMoreAtO_of_eq
#print axioms VerifierAndGoals.readBothO_of_eq
#print axioms VerifierAndGoals.pub8O_of_eq
#print axioms VerifierAndGoals.par7O_older
#print axioms VerifierAndGoals.readMoreAtO_older
#print axioms VerifierAndGoals.readBothO_older
#print axioms VerifierAndGoals.pub8O_older
#print axioms VerifierAndGoals.length_par7O_le
#print axioms VerifierAndGoals.length_par7O_ok
#print axioms VerifierAndGoals.length_par7O_error
#print axioms VerifierAndGoals.readMoreAtO_evaluate
#print axioms VerifierAndGoals.readBothO_evaluate
#print axioms VerifierAndGoals.readBothO_reads
#print axioms VerifierAndGoals.readMoreAtO_of
#print axioms VerifierAndGoals.readBothO_of
#print axioms VerifierAndGoals.pub8O_noCoin
#print axioms VerifierAndGoals.pub8O_det
#print axioms VerifierAndGoals.pub8O_noRepeat
#print axioms VerifierAndGoals.pub8O_asks169
