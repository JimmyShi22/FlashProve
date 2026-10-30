-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB4/RowInScope.lean: `key_planOk_in_scope`: for public files in scope of the
goals, and where the five routines named under "The premises" return a value, the IOP as written in
Lean for the key file (its description, `Key.descriptionFromSource`, Johnson/Desc/Key/Desc.lean) passes its tests on
the plan (`FileDescription.planOk`, Johnson/Desc/Block.lean): (Key.descriptionFromSource X N P).planOk = true. This is the
premise r4 of `IM.keyBack_of_rows` (Johnson/IMR/KeyBackOfRows.lean), a theorem whose premises
together make `Key.keyDataAndDecisionOfPlannerAnswer` return a value. The proof calls theorems of other files, with small
steps in between.

The premises. hZ: the three public files Z are in scope of the goals (`VerifierAndGoals.InScope`,
Ladder.lean). hX: `publicOfO o` returns X₀ on them; o may be any function: it stands in place of the
format's second hash function (`secondHashFunction`). hm: `Key.madeAt` returns m at X₀, Z's layout file and the
fixed digest, `Key.fixedDigest`: the constant at which `Key.keyDataAndDecisionAtFixedDigest` (Johnson/Desc/Key/Slot.lean)
calls `Key.madeAt`. r1, r2, r3: `Key.sourceOf`, `Key.rangesNumbers` and `Key.laterPlaces` return X,
N and P at m; these are r1, r2 and r3 of `IM.keyBack_of_rows`. Its r7, a bound on the length of
every chain's byte string, is not needed here.

The called theorems, in order. KB8/ and KB9/ stand for Johnson/HB/LLHARD/KB8/ and KB9/.
  `IM.keyPins_at_made`, `IM.keyPlans_at_made` (Johnson/IMR/KeyPinsAtMade.lean, KeyPlansAtMade.lean):
    parts of m equal written constants; what `chainsOf`, `sendsFrom`, `wsLayOf` and `KeyChains.read`
    returned.
  `chainsOf_parts` (OnBytes/Model/Fit/PlannedParts.lean): `configure` returned `m.p.chains.made`.
  `_root_.AtFull.KeyBack.four_at_scope` (Johnson/AtFull/KeyBack/BytesShort.lean): two byte strings
    have under 2 ^ 24 bytes. It is named from the root: its namespace has no "Johnson" in front.
  `Johnson.KB9.items_at_made` (KB9/ItemsAtMade.lean): seven items, as read back, are `keyFull`'s.
  `decl_at_return`, `toldOfMade_in_scope` (Johnson/AtFull/KeyBack/InScopeNamed.lean): X.Y.D is
    `declKeyFull` (KB8/Written.lean); `Key.toldOfMade` returns `toldKeyFull` (Told.lean in this
    folder).
  `rangesNumbers_in_scope`, `laterPlaces_in_scope` (Johnson/AtFull/KeyBack/InScope.lean): with r2
    and r3, N is `rangesNumsFull` and P is `laterPlacesFull` (both: KB8/Written.lean).
  `Johnson.KB9.ha_of`, `Johnson.KB9.sends_of_from` (KB9/FileSamples.lean, KB9/FileSends.lean): the
    sendings remade from the chains as read back are m's.
  `Key.fixedDigest_size`, `Key.fixedDigest_ne` (Johnson/Desc/Key/SlotIs.lean): the fixed digest has
    32 bytes and is not 32 zero bytes.
  `key_planOk_at_source` (RowAtSource.lean in this folder): the conclusion, from all of these.

Limits. No theorem in this file or in the files that it imports shows that hZ, hX and hm can hold
together. As far as these files go, that they do rests only on a report of a run of Lean's evaluator
at the stored full-size example's files (`VerifierAndGoals.storedPublicFiles`), and a run is no proof. If they could not,
the theorem would hold vacuously. In other files the three are met at the library's written copy of
the full-size public files (`VerifierAndGoals.storedPublicFiles`: three terms written in Lean; no theorem
ties them to the repository's files): hZ by `VerifierAndGoals.inScope_full`
(Johnson/Goal/Files/ScopeExample.lean); hX and hm, at one X₀ and one m, by
`AtFullSide.Planner.theKeyLaid_zFull_returns` (AtFullSide/Planner/KeyLaidReturns.lean), at the
format's second hash function (`OnBytes.secondHashFunction`) and a constant digest (`Key.fixedDigest`), not the
files' own, in a side library outside the main library (one constant beneath it passes Lean's kernel
only at a larger thread stack; Lean's re-checker, leanchecker, was run on it and fails there at each
shell stack limit that was tried; the toolchain's own replay passes it at a larger thread stack; so
that constant has been checked by the kernel in the build and by that replay, and by no independent
program); no independent checker has replayed any of the closed facts beneath it, and the
full-size example's weights are synthetic. These last two theorems speak of `VerifierAndGoals.storedPublicFiles` alone,
not of other files in scope.

Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB4.RowAtSource
import Johnson.HB.LLHARD.KB9.FileSends
import Johnson.HB.LLHARD.KB9.FileSamples
import Johnson.IMR.KeyPinsAtMade
import Johnson.IMR.KeyPlansAtMade
import Johnson.AtFull.KeyBack.BytesShort
import Johnson.AtFull.KeyBack.InScope
import Johnson.AtFull.KeyBack.InScopeNamed
import OnBytes.Model.Fit.PlannedParts
import Johnson.Desc.Key.SlotIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB4

open VerifiableInference VerifiableInference.Desc
open Johnson.G.OfPlan (Made)
open OnBytes.Model.Verify (Public chainsOf chainsOf_parts)
open Lk6.AtPlan (keyFull)
open Johnson.KB8 (declKeyFull rangesNumsFull laterPlacesFull)

variable {Z : VerifierAndGoals.PublicFiles} {o : ℕ → ByteArray → ByteArray} {X₀ : Public} {m : Made} {X : Key.Source}
  {N : H2U.PlaceNums} {P : Key.LaterPlaces}

/-- **In scope of the goals, the key file's description passes its tests on the plan**, from the
returns of `publicOfO`, of `Key.madeAt` at the fixed digest and of the three routines that make X, N
and P (the premise r4 of `IM.keyBack_of_rows`). -/
theorem key_planOk_in_scope (hZ : VerifierAndGoals.InScope Z = true)
    (hX : PlanWritten.publicOfO o Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hm : Key.madeAt X₀ Z.lay Key.fixedDigest = .ok m) (r1 : Key.sourceOf m = .ok X)
    (r2 : Key.rangesNumbers m = .ok N) (r3 : Key.laterPlaces m = .ok P) :
    (Key.descriptionFromSource X N P).planOk = true := by
  obtain ⟨-, hch, ⟨e, hse⟩, -, hz, c1, c2, c3, hY⟩ := IM.keyPins_at_made hZ hX hm
  obtain ⟨hs, pk, p1, p2, p3, hread⟩ := IM.keyPlans_at_made hZ hX hm
  obtain ⟨links, shapes, -, hcf, -, -⟩ := chainsOf_parts hch
  obtain ⟨b1, b2, -⟩ := _root_.AtFull.KeyBack.four_at_scope hZ hX hm Key.fixedDigest_size
  have hb₁ : m.p.chains.made.keyOneTime.size < 2 ^ 64 := Nat.lt_trans b1 (by norm_num)
  have hb₂ : m.p.chains.made.keyShared.size < 2 ^ 64 := Nat.lt_trans b2 (by norm_num)
  obtain ⟨i1, i2, i3, -, i4, i5, i6, i7⟩ :=
    Johnson.KB9.items_at_made hcf Key.fixedDigest_size hb₁ hb₂ hread hz
  have hD : X.Y.D = declKeyFull := Johnson.AtFull.KeyBack.decl_at_return hZ hX hm r1
  have hT : Key.toldOfMade m = .ok toldKeyFull :=
    Johnson.AtFull.KeyBack.toldOfMade_in_scope hZ hX hm
  have hN : N = rangesNumsFull :=
    Except.ok.inj (r2.symm.trans (Johnson.AtFull.KeyBack.rangesNumbers_in_scope hZ hX hm))
  have hP : P = laterPlacesFull :=
    Except.ok.inj (r3.symm.trans (Johnson.AtFull.KeyBack.laterPlaces_in_scope hZ hX hm))
  have hsends : Key.sendsOfKey m.p.chains.key = .ok m.key :=
    Johnson.KB9.sends_of_from hse pk p1 p2 p3 (i1.trans (congrArg (·.once.input) hz).symm)
      (i2.trans (congrArg (·.ranges.x) hz).symm) (i4.trans (congrArg (·.codes) hz).symm)
      (i5.trans (congrArg (·.once.shape) hz).symm) (Johnson.KB9.ha_of p1 hs)
  exact key_planOk_at_source r1 hD hT hz hs c1 c2 c3 i1 i2 i3 i4 i5 i6 i7 p1 p2 p3 pk hN hP hread
    hcf Key.fixedDigest_size Key.fixedDigest_ne hb₁ hsends hY

end Johnson.KB4

#print axioms Johnson.KB4.key_planOk_in_scope
