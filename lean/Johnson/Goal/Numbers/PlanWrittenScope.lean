-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/PlanWrittenScope.lean: over Johnson/Goal/Numbers/PlanWrittenAtFiles.lean,
Johnson/Desc/Ok/PlanWritten/Pinned.lean and Johnson/Goal/PlanValues/ScopeAtPlan.lean: IN THE GOALS'
SCOPE ONLY THE FULL SIZE's KEY CAN OCCUR: at every three public files in scope, whatever `madeOfAt`
returns has the full size's key. So there a yes of `planPinnedFull`, or of `planIsWritten`, says:
the six written lists of the full size, and the depth 32. This file reaches Ladder.lean through its
imports.

ROW OR TOOL. EVERY DECLARATION HERE IS A TOOL AT THE PLANNER: rules for all files in scope, for all
files, or at the two named sets. None speaks of a description of the protocol.

Definitions, statements and proofs.
  `key_at_policy`: at the stored parameter file at ANY values v of the eight free numbers, any
    layout file, any scale file and ANY c: what `madeOfAt` returns has the full size's key. By
    `scan_sizes` (Johnson/Goal/PlanValues/ScopeAtPlan.lean) (where the strict scan returns on
    `VerifierAndGoals.policyFile v` its record has L = 48, d = 5120, V = 202048) and the library's
    `plannedAt_scan` (OnBytes/Tie/PlanAtPolicy.lean): the scan in the planner's public part is the
    strict scan of the parameter file. `key_at_full`, `key_at_gap`: SO BOTH STORED FULL-SIZE SETS
    CARRY THE FULL SIZE's KEY: the key reads the sizes alone, not the acceptance policy.
  `KeyInScope`, `key_in_scope`: THE CLOSED RULE and its proof: for every Z with `VerifierAndGoals.InScope Z =
    true`, every c and every m that `madeOfAt` returns there: `keyOf m = fullKey`. By
    `inScope_policy` (the same file). `key_in_scope_own`: the like for `madeOf`.
  `pinnedFull_in_scope`: IN SCOPE A YES OF `planPinnedFull`
    (Johnson/Desc/Ok/PlanWritten/Pinned.lean), of what `madeOfAt` returns at any c, says: the rounds
    are the six written lists of the full size and the depth is 32. `full_in_scope`: the like for
    `planIsWritten` and `madeOf`. `smallArm_no_in_scope`: in scope the small example's arm of
    `planIsWritten` never says yes.
  `ridePinnedFull note`, `ridePinnedGap note`: FOR A RUN: `ridePinned` at the two named sets: three
    named Bools each, one call of the planner each: to say true, true, false.
  `pinned_of_written`: `RoundsWrittenAtBoth` gives `PinnedAtBoth`
    (Johnson/Goal/Numbers/PlanWrittenAtFiles.lean): the key, which is no clause of the statement, is
    paid here at both named sets. `pinned_of_rides`: so two true first answers of the rides of
    Johnson/Goal/Numbers/PlanWrittenAtFiles.lean give `PinnedAtBoth`, whatever control 5 says.
  `key_of_ok`, at any files: a yes of the test at the depth 32 and a yes of `pinnedOk` give the full
    size's key at what is made at the anchor: the two written sets' depths differ. `plantOk_no`: so
    beside the two true first answers of a ride of Johnson/Desc/Ok/PlanWritten/Rounds.lean the
    third, the plant's, is foretold by a theorem. No line of that ride prints the key; these two say
    what its answers show of it.

Beside it, by reading. The goals' verifier refuses outright at files out of scope (`verify :=
verifyAt InScope`; `verifyAt … else .done false`, Ladder.lean). So in a run of that term the arm
"another key: yes" of `planPinnedFull` is never reached, if the description's m is what `madeOfAt`
returns at Z's own three files. No theorem here says so: no description is named.

What of OnBytes/Model/ and OnBytes/Tie/ is used. Called: `Tie.plannedAt_scan`. Named through it and
through the theorems of Johnson/Goal/PlanValues/ScopeAtPlan.lean: `Tie.plannedAt`, `Model.polScan`.
All of it is a function of the public files.

Limits. ONE DIRECTION: from a planner that returns. That it returns at a file in scope is not shown.
Nothing here says that either test says yes anywhere. In scope they may say no at honest files: at
other values of the eight free numbers and at other scale files it is not shown that the rounds are
the written lists. The key is three of the eleven sizes that `scan_sizes` has. The rides were run by
nobody known to this file. All limits of Johnson/Desc/Ok/PlanWritten/Rounds.lean,
Johnson/Goal/Numbers/PlanWrittenAtFiles.lean and Johnson/Desc/Ok/PlanWritten/Pinned.lean. Nothing on
soundness.


-/
import Johnson.Goal.Numbers.PlanWrittenAtFiles
import Johnson.Desc.Ok.PlanWritten.Pinned
import Johnson.Goal.PlanValues.ScopeAtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten
open Johnson.G Johnson.G.OfPlan VerifiableInference.Number

/-- **At the stored parameter file at any values of the eight free numbers**: what `madeOfAt`
returns has the full size's key. -/
theorem key_at_policy {v : VerifierAndGoals.FreeLines} {lay KL c : ByteArray} {m : Made}
    (h : madeOfAt (VerifierAndGoals.policyFile v) lay KL c = .ok m) : keyOf m = fullKey := by
  obtain ⟨_, b1, b2, _, _, _, _, _, _, b9, _⟩ :=
    Lk6.AtPlan.scan_sizes (OnBytes.Tie.plannedAt_scan (madeOfAt_planned h))
  exact key_of_sizes b1 b2 b9

/-- Both stored full-size sets carry the full size's key: the first. The key reads the sizes alone,
and the two sets' parameter files are `VerifierAndGoals.policyFile` at two values, by definition. -/
theorem key_at_full {c : ByteArray} {m : Made}
    (h : madeOfAt VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.lay VerifierAndGoals.storedPublicFiles.KL c = .ok m) :
    keyOf m = fullKey :=
  key_at_policy (v := VerifierAndGoals.storedLines) h

/-- The second, with the other policy. -/
theorem key_at_gap {c : ByteArray} {m : Made}
    (h : madeOfAt VerifierAndGoals.zGap.pol VerifierAndGoals.zGap.lay VerifierAndGoals.zGap.KL c = .ok m) :
    keyOf m = fullKey :=
  key_at_policy (v := { VerifierAndGoals.storedLines with C := 25856, theta := 512, cap := 1 }) h

/-- FOR A RUN: `ridePinned` (Johnson/Desc/Ok/PlanWritten/Pinned.lean) at the stored full-size public
files. -/
def ridePinnedFull (note : String) : List (String × Bool) :=
  ridePinned note VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.lay VerifierAndGoals.storedPublicFiles.KL

/-- FOR A RUN: at the same three files with the other policy. -/
def ridePinnedGap (note : String) : List (String × Bool) :=
  ridePinned note VerifierAndGoals.zGap.pol VerifierAndGoals.zGap.lay VerifierAndGoals.zGap.KL

/-- **THE CLOSED RULE: in the goals' scope only the full size's key occurs.** -/
def KeyInScope : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (c : ByteArray) (m : Made), VerifierAndGoals.InScope Z = true →
    madeOfAt Z.pol Z.lay Z.KL c = .ok m → keyOf m = fullKey

/-- Its proof. -/
theorem key_in_scope : KeyInScope := by
  intro Z c m hZ h
  obtain ⟨v, hv⟩ := Lk6.AtPlan.inScope_policy hZ
  rw [hv] at h
  exact key_at_policy h

/-- The like for `madeOf`, at the format's own digest. -/
theorem key_in_scope_own {Z : VerifierAndGoals.PublicFiles} {m : Made} (hZ : VerifierAndGoals.InScope Z = true)
    (h : madeOf Z.pol Z.lay Z.KL = .ok m) : keyOf m = fullKey :=
  key_in_scope Z _ m hZ (madeOfAt_of_madeOf h)

/-- **In scope a yes of `planIsWritten` says: the six written lists of the full size, and the depth
32.** -/
theorem full_in_scope {Z : VerifierAndGoals.PublicFiles} {m : Made} (hZ : VerifierAndGoals.InScope Z = true)
    (h : madeOf Z.pol Z.lay Z.KL = .ok m) (hy : planIsWritten m = true) :
    roundsAt m = .ok (dryKeyFull, dryProofFull) ∧ depthOf m = .ok 32 :=
  full_of_yes (key_in_scope_own hZ h) hy

/-- **In scope a yes of `planPinnedFull` says the same**, at every digest c. -/
theorem pinnedFull_in_scope {Z : VerifierAndGoals.PublicFiles} {c : ByteArray} {m : Made}
    (hZ : VerifierAndGoals.InScope Z = true) (h : madeOfAt Z.pol Z.lay Z.KL c = .ok m)
    (hy : planPinnedFull m = true) :
    roundsAt m = .ok (dryKeyFull, dryProofFull) ∧ depthOf m = .ok 32 :=
  pinnedFull_yes (key_in_scope Z c m hZ h) hy

/-- In scope the small example's arm never says yes: the test at the small example's set alone says
no. -/
theorem smallArm_no_in_scope {Z : VerifierAndGoals.PublicFiles} {m : Made} (hZ : VerifierAndGoals.InScope Z = true)
    (h : madeOf Z.pol Z.lay Z.KL = .ok m) : planIsAmong [smallSet] m = false := by
  refine no_of_key fun W hW => ?_
  rw [List.mem_singleton] at hW
  subst hW
  rw [key_in_scope_own hZ h]
  decide

/-- **The closed statement gives a yes of `planIsWritten` at both named sets.** -/
theorem pinned_of_written (h : RoundsWrittenAtBoth) : PinnedAtBoth := by
  obtain ⟨⟨m, hm, k⟩, ⟨m', hm', k'⟩⟩ := pinned_both h
  exact ⟨⟨m, hm, k (key_at_policy (v := VerifierAndGoals.storedLines) (madeOfAt_of_madeOf hm))⟩,
    ⟨m', hm', k' (key_at_policy
      (v := { VerifierAndGoals.storedLines with C := 25856, theta := 512, cap := 1 })
      (madeOfAt_of_madeOf hm'))⟩⟩

/-! ## What a ride's first two answers pay -/

/-- **From a yes of the test at the depth 32 and a yes of `pinnedOk`: what is made at the anchor has
the full size's key.** The two written sets' depths differ. -/
theorem key_of_ok {L : Six} {pol lay KL : ByteArray} (h : roundsOk L 32 pol lay KL = true)
    (hp : pinnedOk pol lay KL = true) :
    ∃ m, madeOfAt pol lay KL Fmt.zero32 = .ok m ∧ keyOf m = fullKey ∧ planIsWritten m = true := by
  obtain ⟨m, hm, _, _, hd⟩ := anchor_of_ok h
  obtain ⟨m', hm', hy⟩ := pinned_of_ok hp
  have em : m' = m := Except.ok.inj (hm'.symm.trans hm)
  rw [em] at hy
  obtain ⟨W, hW, k, _, d⟩ := written_of_yes hy
  have e : W.depth = 32 := Except.ok.inj (d.symm.trans hd)
  unfold written at hW
  rcases List.mem_cons.1 hW with rfl | hW
  · exact ⟨m, hm, k.symm, hy⟩
  · rw [List.mem_singleton] at hW
    subst hW
    exact absurd e (by decide)

/-- **So beside a ride's two true first answers its third, the plant's, is foretold**: no. -/
theorem plantOk_no {pol lay KL : ByteArray}
    (h : roundsOk (dryKeyFull, dryProofFull) 32 pol lay KL = true)
    (hp : pinnedOk pol lay KL = true) : plantOk pol lay KL = false := by
  obtain ⟨m, hm, k, hy⟩ := key_of_ok h hp
  unfold plantOk
  split
  · rename_i y hy'
    obtain ⟨m', hm', e⟩ := amongSeen_eq planted hy'
    have em : m' = m := Except.ok.inj (hm'.symm.trans hm)
    rw [em] at e
    rw [← e]
    exact planted_no k hy
  · rfl

/-- **If the first answer of both rides is true, `PinnedAtBoth` holds too**: whatever control 5
says. -/
theorem pinned_of_rides {s t : String} (hF : ((rideFull s).map Prod.snd).head? = some true)
    (hG : ((rideGap t).map Prod.snd).head? = some true) : PinnedAtBoth :=
  pinned_of_written (both_of_rides hF hG)

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.key_of_ok
#print axioms VerifiableInference.PlanWritten.plantOk_no
#print axioms VerifiableInference.PlanWritten.pinned_of_rides
#print axioms VerifiableInference.PlanWritten.key_at_policy
#print axioms VerifiableInference.PlanWritten.key_at_full
#print axioms VerifiableInference.PlanWritten.key_at_gap
#print axioms VerifiableInference.PlanWritten.key_in_scope
#print axioms VerifiableInference.PlanWritten.key_in_scope_own
#print axioms VerifiableInference.PlanWritten.full_in_scope
#print axioms VerifiableInference.PlanWritten.pinnedFull_in_scope
#print axioms VerifiableInference.PlanWritten.smallArm_no_in_scope
#print axioms VerifiableInference.PlanWritten.pinned_of_written
