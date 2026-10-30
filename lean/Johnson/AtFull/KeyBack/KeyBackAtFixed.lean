-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/KeyBackAtFixed.lean: The key file's back returns, at a named value, in the
goals' scope: from the two makers' returns and one named premise on the proof file's three
strings. A join: calls, and one case split. Nothing is evaluated here.

«The key file's back» is `Key.keyDataAndDecisionOfPlannerAnswer X₀ lay m` (Johnson/Desc/Key/Slot.lean): what the key
file's piece does behind the planner's return m. The ledger (`IM.keyBack_of_rows`,
Johnson/IMR/KeyBackOfRows.lean) has its return from ten rows. Here nine rows get the theorems that
pay them, and of the tenth (r7) four strings of seven; the other three are the premise h7.

  `sourceKFull m`: the value at which `Key.sourceOf` returns (InScopeNamed.lean).
  `r7_of_three`: the ledger's row r7 (all seven strings of parameter bytes are shorter than 2 ^
    64): four from the scope, three from h7.
  `keyBack_at_fixed_of_rest`: the return, with the written data and the description's own
    decision.
  `keyBack_returns_at_fixed`: so it returns.
Who pays which row. r1, r2, r3: InScopeNamed.lean and InScope.lean in this folder. r4:
`Johnson.KB4.key_planOk_in_scope` (Johnson/HB/LLHARD/KB4/RowInScope.lean). r5, r6:
`IM.key_wantedOk`, `IM.key_owedOk` (Johnson/IMR/KeyRowsFull.lean, KeyOwedFull.lean), at
`Johnson.KB8.pinsX_at_fixed` and `pinsNP_full` (KB8/PinsOfReturns.lean, PinsOfEnds.lean) and at
`decl_at_return`. r8, r8', hk: laid in by `Johnson.KB8.fits_the_ledger` (KB8/FitsTheLedger.lean).
r7: four strings by `_root_.AtFull.KeyBack.four_at_scope` (BytesShort.lean in this folder,
whose namespace has no "Johnson" in front). h7 is a premise and is not paid here:
the proof file's three strings (proofFirst, proofShared, proofSecond) are shorter than 2 ^ 64. The
key file's door tests all seven strings (`Key.bytesFit` over `Key.chainNames`,
Johnson/Desc/Key/BytesFit.lean), so the row cannot be narrowed. Who can pay it:
`_root_.AtFull.KeyBack.r7_of_layout` (BytesShort.lean) gives all seven from two premises: what the
planner configured is the written value, and the layout that `shapesOf` returns is the written
one. These come down to three equations on the shapes that `shapesOf` returns: the proof file's
sizes are the written ones; its first plan is the written one; the layout is the written one:
`r7_at_made`, `r7_of_shapes` (R7AtMade.lean in this folder); two of the three strings from the
first equation alone: `two_at_scope` (TwoShort.lean): six of seven with the four above; the
join with the three in h7's place: KeyBackOfShapes.lean. That these hold at every file in the
scope is shown nowhere. h7 asks less than they do and names no written value of the proof file.
It takes two returns and gives a third: hX and hm are the returns of `publicOfO` and of
`Key.madeAt`. That either returns at any files is not shown here. That hZ, hX, hm and h7 can be met
together is not shown in this file: if they could not, the three statements would be idle and
nothing here would show it. In other files the four are used together inside the proof of
`AtFullSide.Planner.theKeyLaid_zFull_returns` (AtFullSide/Planner/KeyLaidReturns.lean), in a side
library outside the main library (one theorem beneath `theKeyLaid_zFull_returns`,
`Johnson.Unfolds.Layout.lay_chars` in AtFullSide/Layout/TieRfl.lean, passes Lean's kernel only at a
thread stack larger than the default; Lean's re-checker leanchecker, run on it, fails at each
shell stack limit that was tried, up to 1 GiB; no independent checker has given a verdict on it),
and in that proof only at Lean's written copy of the full-size public files (`VerifierAndGoals.storedPublicFiles`: three
terms written in Lean, tied to the repository's files by no theorem; the example's weights are
synthetic), at the format's second hash function (`OnBytes.secondHashFunction`) and the constant digest
`Key.fixedDigest` (32 bytes of 1), at which the key file's piece is laid for the verifier's text,
where no digest is handed in; not the files' own. That proof reaches `keyBack_at_fixed_of_rest`
through `Johnson.AtFull.Top.theKeyLaid_zFull` (Johnson/AtFull/Top/KeyLaidZFull.lean: that theorem
takes two facts on that copy's layout file as premises, which the side library shows) and
`keyBack_at_fixed_of_shapes` (KeyBackOfShapes.lean in this folder): the proof of `theKeyLaid_zFull`
hands in `VerifierAndGoals.inScope_full` (Johnson/Goal/Files/ScopeExample.lean) for hZ, and the proof of
`keyBack_at_fixed_of_shapes` makes h7 with `r7_of_shapes` (R7AtMade.lean in this folder).
No theorem is known that states the conjunction by itself. `theKeyLaid_zFull_returns`
speaks of `VerifierAndGoals.storedPublicFiles` alone, not of other files in scope.
Limits. The value is still no written value whole: `sourceKFull m` keeps m's own fields. The full
size and the constant `Key.fixedDigest` in the digest's place alone. Nothing on soundness,
nothing on hiding.

-/
import Johnson.AtFull.KeyBack.InScopeNamed
import Johnson.HB.LLHARD.KB8.FitsTheLedger
import Johnson.HB.LLHARD.KB4.RowInScope
import Johnson.IMR.KeyRowsFull
import Johnson.IMR.KeyOwedFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open VerifiableInference VerifiableInference.Desc
open Johnson.G.OfPlan (Made)
open OnBytes.Model.Verify (Public ChainName)

/-- The value at which `Key.sourceOf` returns in scope: m's own fields, the written declared rounds
and the written table of trees. -/
abbrev sourceKFull (m : Made) : Key.Source :=
  sourceAt m Johnson.KB8.declKeyFull Johnson.KB4.toldKeyFull

section
variable {Z : VerifierAndGoals.PublicFiles} {o : ℕ → ByteArray → ByteArray} {X₀ : Public} {m : Made}

/-- The ledger's row r7: four strings from the scope, the proof file's three from h7. -/
theorem r7_of_three (hZ : VerifierAndGoals.InScope Z = true)
    (hX : PlanWritten.publicOfO o Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hm : Key.madeAt X₀ Z.lay Key.fixedDigest = .ok m)
    (h7 : (m.p.chains.bytes .proofFirst).size < 2 ^ 64 ∧
      (m.p.chains.bytes .proofShared).size < 2 ^ 64 ∧
      (m.p.chains.bytes .proofSecond).size < 2 ^ 64) :
    ∀ n : ChainName, (m.p.chains.bytes n).size < 2 ^ 64 := by
  obtain ⟨b1, b2, b3, b4⟩ :=
    _root_.AtFull.KeyBack.four_at_scope hZ hX hm Key.fixedDigest_size
  intro n
  cases n
  · exact Nat.lt_trans b1 (by norm_num)
  · exact Nat.lt_trans b2 (by norm_num)
  · exact Nat.lt_trans b3 (by norm_num)
  · exact Nat.lt_trans b4 (by norm_num)
  · exact h7.1
  · exact h7.2.1
  · exact h7.2.2

/-- **The key file's back returns, in scope, at a named value.** -/
theorem keyBack_at_fixed_of_rest (hZ : VerifierAndGoals.InScope Z = true)
    (hX : PlanWritten.publicOfO o Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hm : Key.madeAt X₀ Z.lay Key.fixedDigest = .ok m)
    (h7 : (m.p.chains.bytes .proofFirst).size < 2 ^ 64 ∧
      (m.p.chains.bytes .proofShared).size < 2 ^ 64 ∧
      (m.p.chains.bytes .proofSecond).size < 2 ^ 64) :
    Key.keyDataAndDecisionOfPlannerAnswer X₀ Z.lay m = .ok (Johnson.G.writtenKFull,
                             ((Key.descriptionFromSource (sourceKFull m) Johnson.KB8.rangesNumsFull
                               Johnson.KB8.laterPlacesFull).pull Key.keyInstanceOfOutOfDomainSample).run) := by
  have r1 := sourceOf_named_in_scope hZ hX hm
  have r2 := rangesNumbers_in_scope hZ hX hm
  have r3 := laterPlaces_in_scope hZ hX hm
  have hx := Johnson.KB8.pinsX_at_fixed hZ hX hm r1
  have hp := Johnson.KB8.pins_of_parts hx Johnson.KB8.pinsNP_full
  exact Johnson.KB8.fits_the_ledger hZ hX hm Key.fixedDigest_size r1 r2 r3
    (Johnson.KB4.key_planOk_in_scope hZ hX hm r1 r2 r3)
    (IM.key_wantedOk hp hx.sharedLin)
    (IM.key_owedOk hp hx.sharedLin (congrArg (·.1) (decl_at_return hZ hX hm r1)))
    (r7_of_three hZ hX hm h7) Johnson.KB8.pinsNP_full

/-- So it returns. -/
theorem keyBack_returns_at_fixed (hZ : VerifierAndGoals.InScope Z = true)
    (hX : PlanWritten.publicOfO o Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hm : Key.madeAt X₀ Z.lay Key.fixedDigest = .ok m)
    (h7 : (m.p.chains.bytes .proofFirst).size < 2 ^ 64 ∧
      (m.p.chains.bytes .proofShared).size < 2 ^ 64 ∧
      (m.p.chains.bytes .proofSecond).size < 2 ^ 64) :
    ∃ K, Key.keyDataAndDecisionOfPlannerAnswer X₀ Z.lay m = .ok K :=
  ⟨_, keyBack_at_fixed_of_rest hZ hX hm h7⟩

end

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.r7_of_three
#print axioms Johnson.AtFull.KeyBack.keyBack_at_fixed_of_rest
#print axioms Johnson.AtFull.KeyBack.keyBack_returns_at_fixed
