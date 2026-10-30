-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/OfflineLaying.lean: the written book lays every half of the offline prover, at every coin, and
each half has the number of parts that the book's cut says.

  `partsTable`, `partsAt`, `withinHalves`, `within_full`   how many parts each of the sixteen places
                has; no row and no entry of the written book names a part beyond them (the kernel)
  `cutsTable`, `cuts_full`   the book's cuts at the ten places of one or two parts (the kernel)
  `writtenFace`, `lookupFits`, `lookups_full`   the two lookups' cuts and numbers of parts (the kernel)
  `LookupsStated`   a premise: the parts of the two lookups' rows state what the book has for them:
                it is stated, general in the face, as key_lends' hypothesis
  `RowStated`, `RowLaid`   what the frame's `chainSteps` asks of a half and its book; `RowLaid` is
                cut, no row or entry beyond the half, and `lendRow` returns at every coin
  `testStated`, `tests_full`   what a proximity test's two parts state against the book, at the
                four tests' written jobs (the kernel)
  `offlineValue`   the offline prover's senders at the letters of `valueAt`
  `OfflineRowsLaid`   THE STATEMENT (proved on premises: E2E/OfflineRowsAtValue.lean): each of
                the sixteen halves of the offline prover is laid, at the written book
  `OfflineParts`   THE TEST OF EMPTINESS: their numbers of parts: 1, 1, 935, 920, 2, 2, 1; 1, 1, 1, 1,
                1, 1, 2, 2; 2

Limits. The written sizes alone. The book's carried entries are a proposal (E2E/KeyBook.lean). That
`chainSteps` returns at a whole chain is not stated here. Nothing says what a part sends, and nothing
on any simulator. Nothing on any property.
-/
import E2E.OfflineSides
import E2E.KeyValueHolds
import E2E.KeyBookHeldHash
import E2E.KeyBookHeldK1Jobs
import E2E.KeyShapeSharedTies
import E2E.KeyNineClosed
import E2E.KeyRangesK12
import Johnson.Desc.ProofFile.Honest.K12.StepsAtKey

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.K12 (TestJob proverSideOfProximityTest firstPart restPart firstLen restLen first_states jobKR)
open VerifiableInference.Desc (Block FileDescription Place)
open VerifiableInference.Desc.Key (Source LaterPlaces pieces)
open VerifiableInference.Desc.K12 (P12)
open OnBytes (TableKey)
open OnBytes.Slice (GF)
open Lk6.AtPlan (keyFull)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver keyProver_first keyProver_second sharedChainProverSidesInOrder randK14)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub atFull of_atFull full_two key_lends chainPlaces hasFor
  Stated OneFull idxPlace msgPlace lookPlace rngPlace battPlace wPlace pointPlace foldedPlace
  locPlace omegaPlace zetaPlace splitPlace foldedTestPlace omegaTestPlace ownTestPlace
  idxJob_stated msgJob_stated wJob_stated k13_stated k14_stated k14_sends_stated rides_full)
open AtPublicFiles.KeyTest (jobFolded jobOwn)
open AtPublicFiles.KeyValues (WitK indexMaskSending multiplicitiesSending batchedRowsSending keyBatt lookOf faceAt lookAt oneOf)
open AtPublicFiles.KeyValueHolds (valueAt)
open AtPublicFiles.KeyLay (withTests proverSideOfGuardedSending)
open AtPublicFiles.AtFiles (KeySourced five_sourced)
open AtPublicFiles.AtFiles.Full (QK PF par_sourced later_sourced)
open H2K.Member (piKUFull piKOFull piKWFull piKRFull)
open VerifierAndGoals (PublicFiles InScope)

/-! ## 1 The places' numbers of parts, against the book -/

/-- The sixteen places that have a half, each with its number of parts. -/
def partsTable : List (Place × Nat) :=
  [(idxPlace, 1), (msgPlace, 1), (lookPlace 0, 935), (lookPlace 1, 920), (rngPlace, 2),
    (battPlace, 2), (wPlace, 1), (pointPlace, 1), (foldedPlace, 1), (locPlace, 1), (omegaPlace, 1),
    (zetaPlace, 1), (splitPlace, 1), (foldedTestPlace, 2), (omegaTestPlace, 2), (ownTestPlace, 2)]

/-- The number of parts at a place; 0 at a place of no half. -/
def partsAt (p : Place) : Nat := (partsTable.lookup p).getD 0

/-- Every row and every entry of a book names a part within these numbers. -/
def withinHalves (B : ProverCoinCounts) : Bool :=
  (B.first ++ B.shared ++ B.second).all (fun r => decide (r.1.part < partsAt r.1.place)) &&
    B.ahead.all fun e => decide (e.spender.part < partsAt e.spender.place)

/-- **At the written book they do.** By evaluation. -/
theorem within_full : atFull (fun K => withinHalves (keyBook K)) = true := by decide +kernel

/-- The cuts of the ten places of the kinds K1, K13, K14. -/
def cutsTable : List (Place × List Nat) :=
  [(idxPlace, [2]), (msgPlace, [2]), (battPlace, [1, 19]), (wPlace, [2]), (pointPlace, [1]),
    (foldedPlace, [2]), (locPlace, [1]), (omegaPlace, [2]), (zetaPlace, [1]), (splitPlace, [1])]

/-- **The written book's cuts there.** By evaluation. -/
theorem cuts_full :
    atFull (fun K => cutsTable.all fun x => (keyBook K).cuts.lookup x.1 == some x.2) = true := by
  decide +kernel

/-- The face of lookup number i at the written sizes, by the calls of the description's source. -/
def writtenFace (i : Nat) : K3.LFace :=
  VerifiableInference.Desc.K3.faceOfLkp
    ((OnBytes.Wf.lookupsOf keyFull.ranges.x (OnBytes.Wf.matrixOf keyFull.once.shape)).getD i default)

/-- What the written book says at lookup number i, which has n parts: its cut is the stages' numbers
of rounds; there are n stages. -/
def lookupFits (K : KeyPub) (i n : Nat) : Bool :=
  ((keyBook K).cuts.lookup (lookPlace i) ==
      some ((K3.stages (writtenFace i)).map (K3.Stage.rounds (writtenFace i)))) &&
    ((K3.stages (writtenFace i)).length == n)

/-- **So it is at both lookups.** By evaluation. -/
theorem lookups_full :
    atFull (fun K => lookupFits K 0 935 && lookupFits K 1 920) = true := by decide +kernel

section Laid
variable {V W Y : Type}

/-- **What a half states against a book**: the book's cut is its parts' numbers of moves, and each
part states what the book has for it. -/
structure RowStated (B : ProverCoinCounts) (ch : Nat) (h : Placed V W Y) : Prop where
  cut : B.cuts.lookup h.place = some (h.parts.map (·.moves.length))
  stated : ∀ i p, h.parts[i]? = some p → Stated B (B.rowsOf ch) ⟨h.place, i⟩ p

/-- **A half is laid**: what `chainSteps` asks at a half, but for the number of its rounds: the book's
cut; no row and no entry of the book beyond its parts; and at every coin `lendRow` returns. -/
structure RowLaid (B : ProverCoinCounts) (ch : Nat) (h : Placed V W Y) : Prop where
  cut : B.cuts.lookup h.place = some (h.parts.map (·.moves.length))
  noRow : (B.rowsOf ch).any (fun r =>
    r.1.place == h.place && decide (h.parts.length ≤ r.1.part)) = false
  noEntry : B.ahead.any (fun e =>
    e.spender.place == h.place && decide (h.parts.length ≤ e.spender.part)) = false
  lends : ∀ k : Coins B, ∃ c, lendRow B (B.rowsOf ch) (k.look ch) h.place h.parts 0 = .ok c

/-- No row beyond the parts. -/
theorem noRow_of_within {B : ProverCoinCounts} (hw : withinHalves B = true) (ch : Nat) {p : Place} {n : Nat}
    (hn : partsAt p = n) :
    (B.rowsOf ch).any (fun r => r.1.place == p && decide (n ≤ r.1.part)) = false := by
  unfold withinHalves at hw
  rw [Bool.and_eq_true, List.all_eq_true] at hw
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨r, hr, hb⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb
  obtain ⟨e, hle⟩ := hb
  have hm : r ∈ B.first ++ B.shared ++ B.second := by
    unfold ProverCoinCounts.rowsOf at hr
    split at hr
    · exact List.mem_append_left _ (List.mem_append_left _ hr)
    · split at hr
      · exact List.mem_append_left _ (List.mem_append_right _ hr)
      · exact List.mem_append_right _ hr
  have hlt := of_decide_eq_true (hw.1 r hm)
  rw [e, hn] at hlt
  omega

/-- No entry beyond the parts. -/
theorem noEntry_of_within {B : ProverCoinCounts} (hw : withinHalves B = true) {p : Place} {n : Nat}
    (hn : partsAt p = n) :
    B.ahead.any (fun e => e.spender.place == p && decide (n ≤ e.spender.part)) = false := by
  unfold withinHalves at hw
  rw [Bool.and_eq_true] at hw
  have h2 := List.all_eq_true.1 hw.2
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨e, he, hb⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb
  obtain ⟨ep, hle⟩ := hb
  have hlt := of_decide_eq_true (h2 e he)
  rw [ep, hn] at hlt
  omega

/-- **A half that states what the book has for it is laid**, at the written book. -/
theorem laid_of_stated {K₀ : KeyPub} (hK : fullPub = some K₀) {ch : Nat}
    (hch : ch = 0 ∨ ch = 1 ∨ ch = 2) {h : Placed V W Y}
    (ha : (chainPlaces ch).contains h.place = true) (hn : partsAt h.place = h.parts.length)
    (hs : RowStated (keyBook K₀) ch h) : RowLaid (keyBook K₀) ch h where
  cut := hs.cut
  noRow := noRow_of_within (of_atFull within_full hK) ch hn
  noEntry := noEntry_of_within (of_atFull within_full hK) hn
  lends := fun k => key_lends K₀ hK k ch hch h.place ha h.parts hs.stated

/-- The guard on a half keeps what it states. -/
theorem RowStated.needsField {B : ProverCoinCounts} {ch : Nat} {h : Placed V W Y} (hs : RowStated B ch h) :
    RowStated B ch h.needsField where
  cut := by
    show B.cuts.lookup h.place = some ((h.parts.map Part.needsField).map (·.moves.length))
    rw [hs.cut, List.map_map]
    congr 1
    exact List.map_congr_left fun p _ => (needsField_length p).symm
  stated := by
    intro i p hp
    obtain ⟨q, hq, rfl⟩ : ∃ q, h.parts[i]? = some q ∧ p = q.needsField := by
      have hp' : (h.parts.map Part.needsField)[i]? = some p := hp
      rw [List.getElem?_map] at hp'
      cases hq : h.parts[i]? with
      | none => rw [hq] at hp'; cases hp'
      | some q =>
        rw [hq] at hp'
        exact ⟨q, rfl, (Option.some.inj hp').symm⟩
    exact hs.stated i q hq

end Laid

/-! ## 2 A proximity test against the book -/

section Test
variable {V W X W' X' : Type}

/-- **What a test's two parts state, against a book.** Of a job it reads the numbers, the members and
the word on the fresh table. -/
def testStated (B : ProverCoinCounts) (ch : Nat) (J : TestJob W X) : Bool :=
  (B.cuts.lookup J.p.place == some [firstLen J.p.nums.stages, restLen J.p.nums.stages]) &&
    decide (((firstPart J : Part Unit W X).takes, (firstPart J : Part Unit W X).spends,
      (firstPart J : Part Unit W X).carries) = hasFor B (B.rowsOf ch) ⟨J.p.place, 0⟩) &&
    decide (((restPart J : Part Unit W X).takes, (restPart J : Part Unit W X).spends,
      (restPart J : Part Unit W X).carries) = hasFor B (B.rowsOf ch) ⟨J.p.place, 1⟩)

/-- It reads of a job the three fields alone. -/
theorem testStated_same (B : ProverCoinCounts) (ch : Nat) (J : TestJob W X) (J' : TestJob W' X')
    (hp : J.p = J'.p) (hm : J.members = J'.members) (hf : J.fresh = J'.fresh) :
    testStated B ch J = testStated B ch J' := by
  cases J with
  | mk p ms fresh r ro tr =>
    cases J' with
    | mk p' ms' fresh' r' ro' tr' =>
      obtain rfl : p = p' := hp
      obtain rfl : ms = ms' := hm
      obtain rfl : fresh = fresh' := hf
      cases fresh <;> rfl

/-- The test on the folded row's group at its written numbers. -/
def foldedAt : TestJob Unit Unit := { jobFolded with p := piKUFull }
/-- The test on Omega's group at its written numbers. -/
def omegaAt : TestJob Unit Unit := { AtPublicFiles.KeyTest.jobOmega with p := piKOFull }
/-- The last chain's test at its written numbers. -/
def ownAt : TestJob Unit Unit := { jobOwn with p := piKWFull }

/-- **The four tests' parts state what the written book has for them.** By evaluation. -/
theorem tests_full : atFull (fun K =>
    testStated (keyBook K) 0 jobKR && testStated (keyBook K) 1 foldedAt &&
      testStated (keyBook K) 1 omegaAt && testStated (keyBook K) 2 ownAt) = true := by
  decide +kernel

/-- **Where the test says yes, a test's half states what the book has for it.** -/
theorem stated_of_test {B : ProverCoinCounts} {ch : Nat} (J : TestJob W X) (s t : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: t :: rest)
    (hT : testStated B ch J = true) : RowStated B ch (proverSideOfProximityTest J : Placed V W X) := by
  unfold testStated at hT
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hT
  obtain ⟨⟨a1, a2⟩, a3⟩ := hT
  have l1 : (firstPart J : Part V W X).moves.length = firstLen J.p.nums.stages := by
    rw [ProofFile.Honest.K12.first_moves]
    exact (List.length_map _).trans List.length_range
  have l2 : (restPart J : Part V W X).moves.length = restLen J.p.nums.stages := by
    rw [ProofFile.Honest.K12.rest_moves J s t rest hst]
    exact (List.length_map _).trans List.length_range
  refine ⟨?_, ?_⟩
  · show B.cuts.lookup J.p.place = some [(firstPart J : Part V W X).moves.length,
      (restPart J : Part V W X).moves.length]
    rw [l1, l2]
    exact a1
  · intro i p hp
    match i, hp with
    | 0, hp =>
      obtain rfl := Option.some.inj hp
      exact (first_states J).trans a2
    | 1, hp =>
      obtain rfl := Option.some.inj hp
      exact a3
    | i + 2, hp => cases hp

end Test

/-! ## 3 The value -/

section Value
variable {W₀ Rc : Type} (K' : KeyParts W₀ Rc Unit Unit WitK) (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (f : W₀ → Weights) (g : Rc → Nat → TableRand) (inR : W₀ → Bool) (d : W₀)
  (ent : Local W₀ Rc KeyInst Unit → Nat → Nat → GF) (groups : List (List Nat)) (first : Nat)

/-- **The parts of the two lookups' rows state what the book has for them.** A premise, CONDITIONAL:
if it is false at the written book every statement that takes it is empty. No evaluation here: the
test on the whole row timed out, and whether it is false,
refused or heavy is not known to this file; a stretch of 20 stages passed there. The lookups' house
has a theorem general in the face, in a ride. -/
def LookupsStated (K₀ : KeyPub) (K : KeyParts W₀ Rc Unit Unit WitK) : Prop :=
  (∀ i p, (K3.proverSideOfLookupInChain (V₁ := Local W₀ Rc KeyInst Unit) (X₁ := Unit)
      (K3.keyOwners K.look0.face) K.reads K.jobs0 K.wit K.look0).parts[i]? = some p →
    Stated (keyBook K₀) (keyBook K₀).first ⟨K.look0.place, i⟩ p) ∧
  ∀ i p, (K3.proverSideOfLookupInChain (V₁ := Local W₀ Rc KeyInst Unit) (X₁ := Unit)
      (K3.keyOwners K.look1.face) K.reads K.jobs1 K.wit K.look1).parts[i]? = some p →
    Stated (keyBook K₀) (keyBook K₀).first ⟨K.look1.place, i⟩ p

/-- **The offline prover's senders**, at its two places of the shared tests. -/
abbrev offlineValue : KeyParts W₀ Rc Unit Unit WitK :=
  valueAt K' Xs N Pl f g inR d (H2U.proximityTestParametersAt foldedTestPlace Pl.U)
    (H2U.proximityTestParametersAt omegaTestPlace (Pl.O.getD Pl.U)) ent groups first

/-- **THE TEST OF EMPTINESS: the halves' numbers of parts**, in scope. -/
def OfflineParts : Prop :=
  (keyProver (offlineValue K' Xs N Pl f g inR d ent groups first)).first.map (·.parts.length) =
      [1, 1, 935, 920, 2, 2, 1] ∧
    (keyProver (offlineValue K' Xs N Pl f g inR d ent groups first)).shared.map
      (·.parts.length) = [1, 1, 1, 1, 1, 1, 2, 2] ∧
    (keyProver (offlineValue K' Xs N Pl f g inR d ent groups first)).second.map
      (·.parts.length) = [2]

/-- **THE STATEMENT: each half of the offline prover is laid, at the written book.** -/
def OfflineRowsLaid (K₀ : KeyPub) : Prop :=
  (∀ h ∈ (keyProver (offlineValue K' Xs N Pl f g inR d ent groups first)).first,
      RowLaid (V := Local W₀ Rc KeyInst Unit) (keyBook K₀) 0 h) ∧
    (∀ h ∈ (keyProver (offlineValue K' Xs N Pl f g inR d ent groups first)).shared,
      RowLaid (V := Empty) (keyBook K₀) 1 h) ∧
    ∀ h ∈ (keyProver (offlineValue K' Xs N Pl f g inR d ent groups first)).second,
      RowLaid (V := Local W₀ Rc KeyInst Unit) (keyBook K₀) 2 h

end Value

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.within_full
#print axioms AtPublicFiles.OfflineRows.cuts_full
#print axioms AtPublicFiles.OfflineRows.lookups_full
#print axioms AtPublicFiles.OfflineRows.laid_of_stated
#print axioms AtPublicFiles.OfflineRows.tests_full
#print axioms AtPublicFiles.OfflineRows.stated_of_test
