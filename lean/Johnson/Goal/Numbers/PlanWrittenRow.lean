-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/PlanWrittenRow.lean: over Johnson/Goal/Numbers/PlanWrittenDescScope.lean: "THE
DESCRIPTION IS MADE AT THE WRITTEN PLAN VALUES": the statement, with the two files' descriptions and
their yes as letters; and that it follows where the test that pins the plan at the full size's key
is laid beneath that yes. This file reaches Ladder.lean through its imports.

ROW OR TOOL. `PlanWrittenAt FP FK yes` is a statement with free letters for the makers of the two
descriptions and for what their yes is: at named makers it is the first clause of a row; here NO
DESCRIPTION IS NAMED, so every declaration is a tool.

Definitions, statements and proofs.
  `PlanWrittenAt FP FK yes`: for every Z with `VerifierAndGoals.InScope Z = true` and `yes Z`: the data that
    the proof file's description `FP Z` hands the compiler are `writtenPFull`, and those of the key
    file's description `FK Z` are `writtenKFull` (Johnson/Flat/Dec/FitAtWritten.lean): the data of
    the library's written lists of the full size at the depth 32. IT NAMES NO WAY IN WHICH THE
    DESCRIPTIONS ARE MADE: where they are made of what a planner returns, with the test laid, it
    follows by `planWrittenAt_of_seat`; where they are made of written values, it is to follow by
    unfolding. IT SPEAKS OF THE DATA ALONE: the declared rounds, written out, and the depth: a
    description with the written rounds in its blocks and the depth 32, and any decisions, first
    states and other fields, meets it. `yes` IS A FACT ON THE PUBLIC FILES (`VerifierAndGoals.PublicFiles → Prop`): it
    can see no commitment, no proof, no digest and no hash: it is not the verifier's yes. AT A yes
    THAT IS NEVER MET THE STATEMENT HOLDS OF ANY MAKERS, and the more yes asks the less the
    statement says: nothing in Lean keeps a caller from an idle yes: at named makers the row wants,
    beside the statement, that yes holds at the two named sets of public files, which a run alone
    can show.
  `SeatLaid FP FK yes`: THE NAMED PREMISE: in scope, `yes Z` gives a yes of `seatPinnedProof Z.pol
    (FP Z)` and of `seatPinnedKey Z.pol (FK Z)` (Johnson/Desc/Ok/PlanWritten/Test.lean). It is for
    whoever lays the test to show, at the named makers. IT BINDS BOTH FILES' DESCRIPTIONS UNDER ONE
    yes: whoever can show the proof file's half alone has not shown it. A maker that may refuse (a
    value in `Except`) is put for FP so: for each F that it returns, FP the constant F, and yes Z:
    "the maker returns F at Z, and what rests on it is laid".
  `planWrittenAt_of_seat`: `SeatLaid` gives `PlanWrittenAt`. By `seat_in_scope` and
    `seat_in_scope_key`. `lists_of_seat`: and, written out, the two descriptions' declared rounds
    are the written lists, and their depths are 32.
  `AtLaid FP FK yes`, `planWrittenAt_of_at`: the like where the makers hold an m of their own: in
    scope, `yes Z` gives a c and an m that `madeOfAt` returns at Z's three files and c, with a yes
    of `pinnedProofAt m (FP Z)` and `pinnedKeyAt m (FK Z)`. THAT ROAD NAMES THE SECOND HASH
    FUNCTION: `madeOfAt` reaches it by name through `publicOf` (the Limits of
    Johnson/Desc/Ok/NumberPrices/AtDigest.lean): a maker on it is one that a description which is to
    name no hash may not be. `scan_returns_in_scope`: IN SCOPE THE STRICT SCAN OF THE PARAMETER FILE
    RETURNS, and its key is the full size's: the scope holds the reader of the public files, which
    begins with that scan (`settingsAtRef_held`, Johnson/Flat/SettingsRead.lean).
    `seat_eq_in_scope`: so in scope `seatPinnedProof Z.pol F` is `descPinnedProof fullKey F`:
    neither the arm of the refusal nor the arm "another key: yes" is reached there. (So the tooth on
    the arm of the refusal, `lax_not_rule`, Johnson/Desc/Ok/PlanWritten/Seat.lean, bites out of
    scope alone.)
  A TOOTH. `data_depth`: the data that a description hands on bear its own depth.
    `not_planWrittenAt`: THE STATEMENT CAN FAIL: at makers, a Z in scope and a yes where the proof
    file's description has another depth than 32 it is false. It bites where yes is met, on the
    proof file's depth alone; no tooth here is on a round, none on the key file.

Beside the statement, and no clause of it: that the written values are what the library's planner
makes of the two named sets of public files (`RoundsWrittenAtBoth`,
Johnson/Goal/Numbers/PlanWrittenAtFiles.lean, for the six lists and the depth; `FieldIs`,
Johnson/Desc/Ok/PlanWritten/Row.lean, as a form for further fields) can be
shown by a run alone.

Limits. NO DESCRIPTION IS NAMED: `SeatLaid` and `AtLaid` are shown of no makers. THAT A
DESCRIPTION's TEXT NAMES NO HASH IS NO PROPOSITION (the head of Ladder.lean, 9): nothing here says
it; what can be proved toward it is that the road takes the hashes' values as letters and that what
is taken of it does not hang on them (for the digest:
Johnson/Desc/Ok/PlanWritten/Row.lean).
`not_planWrittenAt` has the premise that Z is in scope: that any Z is in scope is held by tests of
the build (Ladder/Guards.lean), by no theorem known to this file. What the data do not hold: each
plan's six settings, the entry RECORD, the entry file's rounds, the errors' numbers, sizes and codes
but for the depth. All limits of Johnson/Goal/Numbers/PlanWrittenDescScope.lean. Nothing on
soundness.


-/
import Johnson.Goal.Numbers.PlanWrittenDescScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten
open Johnson.G Johnson.G.OfPlan VerifiableInference.Number VerifiableInference.Desc
open OnBytes.Maker (WholeD)

variable {XiP XiK : Type}

/-- **"The description is made at the written plan values."** Of the data alone: the declared
rounds, written out, and the depth. FP, FK: the makers of the proof file's and the key file's
description. yes: a fact on the public files under which the statement is claimed; at a yes that is
never met it holds of any makers. -/
def PlanWrittenAt (FP : VerifierAndGoals.PublicFiles → FileDescription XiP) (FK : VerifierAndGoals.PublicFiles → FileDescription XiK)
    (yes : VerifierAndGoals.PublicFiles → Prop) : Prop :=
  ∀ Z : VerifierAndGoals.PublicFiles, VerifierAndGoals.InScope Z = true → yes Z →
    (FP Z).data "proof file" = .ok writtenPFull ∧ (FK Z).data "key file" = .ok writtenKFull

/-- **THE NAMED PREMISE: the test from the public parameter file is laid beneath the yes.** -/
def SeatLaid (FP : VerifierAndGoals.PublicFiles → FileDescription XiP) (FK : VerifierAndGoals.PublicFiles → FileDescription XiK)
    (yes : VerifierAndGoals.PublicFiles → Prop) : Prop :=
  ∀ Z : VerifierAndGoals.PublicFiles, VerifierAndGoals.InScope Z = true → yes Z →
    seatPinnedProof Z.pol (FP Z) = true ∧ seatPinnedKey Z.pol (FK Z) = true

/-- **Where the test is laid, the description is made at the written plan values.** -/
theorem planWrittenAt_of_seat {FP : VerifierAndGoals.PublicFiles → FileDescription XiP} {FK : VerifierAndGoals.PublicFiles → FileDescription XiK}
    {yes : VerifierAndGoals.PublicFiles → Prop} (h : SeatLaid FP FK yes) : PlanWrittenAt FP FK yes :=
  fun Z hZ hy => ⟨(seat_in_scope XiP (FP Z) Z hZ (h Z hZ hy).1).2.2,
    (seat_in_scope_key XiK (FK Z) Z hZ (h Z hZ hy).2).2.2⟩

/-- And, written out, the declared rounds are the written lists, and the depths are 32. -/
theorem lists_of_seat {FP : VerifierAndGoals.PublicFiles → FileDescription XiP} {FK : VerifierAndGoals.PublicFiles → FileDescription XiK}
    {yes : VerifierAndGoals.PublicFiles → Prop} (h : SeatLaid FP FK yes) {Z : VerifierAndGoals.PublicFiles}
    (hZ : VerifierAndGoals.InScope Z = true) (hy : yes Z) :
    (writtenOf "proof file" (FP Z).roundsDeclaredByBlocks = .ok dryProofFull ∧ (FP Z).tableDepth = 32) ∧
      writtenOf "key file" (FK Z).roundsDeclaredByBlocks = .ok dryKeyFull ∧ (FK Z).tableDepth = 32 :=
  ⟨⟨(seat_in_scope XiP (FP Z) Z hZ (h Z hZ hy).1).1,
      (seat_in_scope XiP (FP Z) Z hZ (h Z hZ hy).1).2.1⟩,
    (seat_in_scope_key XiK (FK Z) Z hZ (h Z hZ hy).2).1,
    (seat_in_scope_key XiK (FK Z) Z hZ (h Z hZ hy).2).2.1⟩

/-- The named premise where the makers hold an m of their own. -/
def AtLaid (FP : VerifierAndGoals.PublicFiles → FileDescription XiP) (FK : VerifierAndGoals.PublicFiles → FileDescription XiK)
    (yes : VerifierAndGoals.PublicFiles → Prop) : Prop :=
  ∀ Z : VerifierAndGoals.PublicFiles, VerifierAndGoals.InScope Z = true → yes Z →
    ∃ (c : ByteArray) (m : Made), madeOfAt Z.pol Z.lay Z.KL c = .ok m ∧
      pinnedProofAt m (FP Z) = true ∧ pinnedKeyAt m (FK Z) = true

/-- There too the description is made at the written plan values. -/
theorem planWrittenAt_of_at {FP : VerifierAndGoals.PublicFiles → FileDescription XiP} {FK : VerifierAndGoals.PublicFiles → FileDescription XiK}
    {yes : VerifierAndGoals.PublicFiles → Prop} (h : AtLaid FP FK yes) : PlanWrittenAt FP FK yes := by
  intro Z hZ hy
  obtain ⟨c, m, hm, hP, hK⟩ := h Z hZ hy
  exact ⟨(at_in_scope XiP (FP Z) Z c m hZ hm hP).2.2,
    (at_in_scope_key XiK (FK Z) Z c m hZ hm hK).2.2⟩

/-! ## In scope the scan returns -/

/-- **In scope the strict scan of the parameter file returns, and its key is the full size's.** The
scope holds the reader of the public files, which begins with that scan. -/
theorem scan_returns_in_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) :
    ∃ P, OnBytes.Model.polScan Z.pol = .ok P ∧ keyOfScan P = fullKey := by
  have h := hZ
  unfold VerifierAndGoals.InScope at h
  rw [Bool.and_eq_true] at h
  have h2 := h.2
  split at h2
  · rename_i pp hpp
    obtain ⟨S, hS, _⟩ := OnBytes.Flat.settingsAtRef_held hpp
    exact ⟨S, hS, scan_key_in_scope hZ hS⟩
  · cases h2

/-- So in scope the test from the parameter file IS the test at the full size's key: the arm of the
refusal and the arm "another key: yes" are not reached. -/
theorem seat_eq_in_scope {Xi : Type} {Z : VerifierAndGoals.PublicFiles} (F : FileDescription Xi)
    (hZ : VerifierAndGoals.InScope Z = true) : seatPinnedProof Z.pol F = descPinnedProof fullKey F := by
  obtain ⟨P, hP, hk⟩ := scan_returns_in_scope hZ
  unfold seatPinnedProof
  rw [hP]
  show descPinnedProof (keyOfScan P) F = descPinnedProof fullKey F
  rw [hk]

/-! ## The statement can fail -/

/-- The data that a description hands on bear its own depth. -/
theorem data_depth {Xi : Type} {F : FileDescription Xi} {file : String} {D : WholeD}
    (h : F.data file = .ok D) : D.a = F.tableDepth := by
  unfold FileDescription.data at h
  obtain ⟨R, _, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · rw [← Except.ok.inj h]
    rfl
  · have h' : (Except.error (file ++ ": the makers' tests on the written rounds say no") :
        Except String WholeD) = .ok D := h
    cases h'

/-- **A tooth**: at makers, a Z in scope and a yes where the proof file's description has another
depth than 32 the statement is false. -/
theorem not_planWrittenAt {FP : VerifierAndGoals.PublicFiles → FileDescription XiP} {FK : VerifierAndGoals.PublicFiles → FileDescription XiK}
    {yes : VerifierAndGoals.PublicFiles → Prop} {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) (hy : yes Z)
    (hd : (FP Z).tableDepth ≠ 32) : ¬ PlanWrittenAt FP FK yes := fun H =>
  hd (data_depth (H Z hZ hy).1).symm

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.planWrittenAt_of_seat
#print axioms VerifiableInference.PlanWritten.lists_of_seat
#print axioms VerifiableInference.PlanWritten.planWrittenAt_of_at
#print axioms VerifiableInference.PlanWritten.scan_returns_in_scope
#print axioms VerifiableInference.PlanWritten.seat_eq_in_scope
#print axioms VerifiableInference.PlanWritten.data_depth
#print axioms VerifiableInference.PlanWritten.not_planWrittenAt
