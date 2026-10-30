-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/PlanWrittenPlans.lean: the three lists of the plan's own entries in the public
part of the proof file's description (`ProofFile.Pub.plans`, Johnson/Desc/ProofFile/Pub.lean) are the
entries of its three lists of declared rounds; and in scope, where the value for the proof file is
laid (`LPFD.Full.proofDataAndDecisionOfPublicFiles`, Johnson/Desc/Laid/ProofFull.lean), they are the entries of the library's
written lists of the full size.

What it is for. The test on a proof file's description (`seatPinnedProof`,
Johnson/Desc/Ok/PlanWritten/Test.lean) holds the description's declared rounds against the written
lists. Laws on the description's blocks also read the plan's entries through the public part. This
file carries the test's yes to these.

Row or tool. `pubBy_entries` and `descPure_plans` are tools, for all public files. `plans_written`
names the value that is laid for the proof file and the public part that the description binds, at
every o, all public files in scope and whatever the laid value's two parts are. It is a tool beneath
the rows that read the plan's entries.

What is here.
  `atCall_ok`: a step under a name returns what the step returns.
  `pubBy_entries`: what `pubBy` returns, at every function for the planner's record and every way to
    the first state: the entries of `Z.D`'s three lists are `Z.plans`' three. By the text of `pubBy`
    and `fileOf_entries` (Johnson/G/DataEntries.lean).
  `bindU_ok`: a step and what follows it, where the two values' types may lie in two universes.
  `pureTail_plans`, `pureZ_plans`, `descPure_plans`: where the description is made, its field
    `plans` is the `D` of the public part that it binds, which is what `pubPlain o` returns at the
    three files.
  `plans_written`: in scope, where the value is laid: `pubPlain o` returns a Z at the three files,
    and `Z.plans`' three lists are the entries of `dryProofFull`'s three lists, each whole: the
    first with its last round, the seal.

Limits. One direction: from runs that return. Nothing is evaluated. Nothing on the key file. Nothing
says that the value is laid at any public files. Nothing on soundness.


-/
import Johnson.Desc.Laid.ProofFullScope
import Johnson.Desc.Sound.ReadsOkProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten
open Johnson.G Johnson.G.OfPlan VerifiableInference.Desc LPFD.Full

/-- A step under a name returns what the step returns. -/
theorem atCall_ok {α : Type} {n : String} {x : Except String α} {a : α}
    (h : _root_.ProofFile.atCall n x = .ok a) : x = .ok a := by
  cases x with
  | error e => simp [_root_.ProofFile.atCall, Except.mapError] at h
  | ok b => exact h

/-- **The entries of the public part's declared rounds are the plan's own entries**, all three
chains. -/
theorem pubBy_entries
    {made : ByteArray → ByteArray → ByteArray → Except String Made} {st : _root_.ProofFile.Starts}
    {pol lay KL : ByteArray} {Z : _root_.ProofFile.Pub}
    (h : _root_.ProofFile.pubBy made st pol lay KL = .ok Z) :
    Z.D.1.map (·.entry) = Z.plans.1 ∧ Z.D.2.1.map (·.entry) = Z.plans.2.1 ∧
      Z.D.2.2.map (·.entry) = Z.plans.2.2 := by
  unfold _root_.ProofFile.pubBy at h
  obtain ⟨m, _, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, h', _⟩ := bind_ok h
    exact absurd h' (throw_ne _ _)
  · obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨D, hD, h⟩ := bind_ok h
    obtain ⟨told, _, h⟩ := bind_ok h
    obtain ⟨depth, _, h⟩ := bind_ok h
    obtain ⟨cuts, _, h⟩ := bind_ok h
    obtain ⟨s₀, _, h⟩ := bind_ok h
    obtain rfl := Except.ok.inj h
    have hD' := atCall_ok hD
    unfold declPOf at hD'
    exact fileOf_entries hD'

/-- A step and what follows it, where the two values' types may lie in two universes. -/
theorem bindU_ok.{u, v} {ε : Type} {α : Type u} {β : Type v} {x : Except ε α}
    {f : α → Except ε β} {b : β} (h : x.bind f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- What the last step returns has the public part's declared rounds as its plan. -/
theorem pureTail_plans {Z : _root_.ProofFile.Pub} {T : _root_.ProofFile.PureSeat} {P : _root_.ProofFile.PureParts}
    {F : FileDescription _root_.ProofFile.Inst} (h : _root_.ProofFile.onlineDescriptionAfterTests Z T P = .ok F) : F.plans = Z.D := by
  unfold _root_.ProofFile.onlineDescriptionAfterTests at h
  obtain ⟨base, _, h⟩ := bindU_ok h
  obtain ⟨c, _, h⟩ := bindU_ok h
  split at h
  · obtain rfl := Except.ok.inj h
    rfl
  · cases h

/-- So has the description that is made of a public part. -/
theorem pureZ_plans {Z : _root_.ProofFile.Pub} {T : _root_.ProofFile.PureSeat}
    {F : FileDescription _root_.ProofFile.Inst} (h : _root_.ProofFile.onlineDescriptionFromPublicPart Z T = .ok F) : F.plans = Z.D := by
  unfold _root_.ProofFile.onlineDescriptionFromPublicPart at h
  obtain ⟨B, _, h⟩ := bindU_ok h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · exact pureTail_plans h

/-- **Where the description is made, its plan is the `D` of the public part that it binds.** -/
theorem descPure_plans {o : _root_.ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {F : FileDescription _root_.ProofFile.Inst} (h : _root_.ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ Z, _root_.ProofFile.pubPlain o pol lay KL = .ok Z ∧ F.plans = Z.D := by
  unfold _root_.ProofFile.onlineDescription _root_.ProofFile.onlineDescriptionFromBlockTables at h
  obtain ⟨Z, hZ, h⟩ := bindU_ok h
  exact ⟨Z, hZ, pureZ_plans h⟩

/-- **In scope, where the value is laid, the plan's own entries are the written lists' entries.** -/
theorem plans_written {o : _root_.ProofFile.SecondHashFunctionArgument} {Z₀ : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r : RunPF} (hS : VerifierAndGoals.InScope Z₀ = true)
    (h : proofDataAndDecisionOfPublicFiles o Z₀.pol Z₀.lay Z₀.KL = .ok (D, r)) :
    ∃ Z, _root_.ProofFile.pubPlain o Z₀.pol Z₀.lay Z₀.KL = .ok Z ∧
      Z.plans.1 = dryProofFull.1.map (·.1.entry) ∧
      Z.plans.2.1 = dryProofFull.2.1.map (·.1.entry) ∧
      Z.plans.2.2 = dryProofFull.2.2.map (·.1.entry) := by
  obtain ⟨F, hd, hp, _, _, _⟩ := laidPOf_ok h
  obtain ⟨F', hd', hw⟩ := laidPOf_rounds hS h
  obtain rfl : F' = F := Except.ok.inj (hd'.symm.trans hd)
  obtain ⟨Z, hZ, hpl⟩ := descPure_plans hd
  obtain ⟨e1, e2, e3⟩ := pubBy_entries hZ
  obtain ⟨w1, w2, w3⟩ := writtenOf_entries hw
  have hdec : F'.roundsDeclaredByBlocks = Z.D := (Sound.decl_of_planOk F' hp).trans hpl
  rw [hdec] at w1 w2 w3
  exact ⟨Z, hZ, e1.symm.trans w1.symm, e2.symm.trans w2.symm, e3.symm.trans w3.symm⟩

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.atCall_ok
#print axioms VerifiableInference.PlanWritten.pubBy_entries
#print axioms VerifiableInference.PlanWritten.bindU_ok
#print axioms VerifiableInference.PlanWritten.pureTail_plans
#print axioms VerifiableInference.PlanWritten.pureZ_plans
#print axioms VerifiableInference.PlanWritten.descPure_plans
#print axioms VerifiableInference.PlanWritten.plans_written
