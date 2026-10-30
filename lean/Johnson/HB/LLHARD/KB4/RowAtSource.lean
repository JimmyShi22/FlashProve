-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB4/RowAtSource.lean: (Key.descriptionFromSource X N P).planOk = true, the premise r4 of
IM.keyBack_of_rows (Johnson/IMR/KeyBackOfRows.lean), at what Key.sourceOf returns; its premises are
worded as the conclusions of the theorems that are meant to give them. Calls, with small steps in
between.

How it differs from key_planOk_at_made (RowAtMade.lean). Two premises are exchanged.
  The declared rounds: there "declKOf m = .ok declKeyFull"; here "X.Y.D = declKeyFull", an equation
  on the source that was returned: no theorem at hand ends in declKOf's return, and one ends in
  Key.sourceOf's.
  The clause "digest": there chainsOf's return and all of r7 of IM.keyBack_of_rows (a bound on every
  chain's string), of which three bounds are used, one of them on the proof file's first string;
  here configure's return and one bound, on the key's one-time chain's string (CfgOfRead.lean).

Main names.
  decl_of_source, told_of_source: what Key.sourceOf lays as the declared rounds and as the tenants
  as told is what declKOf and Key.toldOfMade returned: by its unfolding.
  key_planOk_at_source: (Key.descriptionFromSource X N P).planOk = true.
The premises of key_planOk_at_source, and what gives each: as in RowAtMade.lean's head, but for:
hD: from r1 and the theorem that says what Key.sourceOf returns, by injection. hcf:
OnBytes.Model.Verify.chainsOf_parts. hb₁: a bound on one string.
  hT, that Key.toldOfMade returns toldKeyFull: Johnson.AtFull.KeyBack.toldOfMade_in_scope
  (Johnson/AtFull/KeyBack/InScopeNamed.lean, not imported here), for public files in scope of the
  goals, where publicOfO returns and Key.madeAt returns at the fixed digest.
Limits. Not one of these premises is shown here; that they can be met together is shown by
no theorem in this file or in the files that it imports. If they could not, the theorem would hold
vacuously. They are used together at VerifierAndGoals.storedPublicFiles inside the proof of
AtFullSide.Planner.theKeyLaid_zFull_returns (AtFullSide/Planner/KeyLaidReturns.lean), which reaches
key_planOk_at_source through key_planOk_in_scope (RowInScope.lean); no theorem is known
that states the conjunction by itself. theKeyLaid_zFull_returns speaks of the library's
written copy of the full-size public files (VerifierAndGoals.storedPublicFiles: three terms written in Lean; no theorem
ties them to the repository's files), at the second hash
function (OnBytes.secondHashFunction) and a constant digest (Key.fixedDigest), not the files' own, in a side
library outside the main library (one constant beneath it passes Lean's kernel only at a larger
thread stack; Lean's re-checker, leanchecker, was run on it and fails there at each shell stack
limit that was tried; the toolchain's own replay passes it at a larger thread stack; so that
constant has been checked by the kernel in the build and by that replay, and by no independent
program); no independent checker has replayed any of the closed facts beneath it, and the
full-size example's weights are synthetic. theKeyLaid_zFull_returns speaks of VerifierAndGoals.storedPublicFiles alone,
not of other files in scope.
Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB4.RowAtMade
import Johnson.HB.LLHARD.KB4.CfgOfRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB4

open VerifiableInference.Desc VerifiableInference.Desc.Key
open OnBytes OnBytes.Params
open OnBytes.Params (exc_bind)
open Johnson.G.OfPlan (Made)
open Lk6.AtPlan (keyFull wsFull)
open VerifiableInference.Number.ByRuns (keyThree)
open Johnson.KB8 (declKeyFull rangesNumsFull laterPlacesFull)

theorem decl_of_source {m : Made} {X : Source} (r1 : sourceOf m = .ok X) :
    Johnson.G.OfPlan.declKOf m = .ok X.Y.D := by
  unfold sourceOf at r1
  obtain ⟨D, h1, r1⟩ := exc_bind r1
  obtain ⟨T, _, r1⟩ := exc_bind r1
  obtain rfl : _ = X := Except.ok.inj r1
  exact h1

theorem told_of_source {m : Made} {X : Source} (r1 : sourceOf m = .ok X) :
    toldOfMade m = .ok X.Y.told := by
  unfold sourceOf at r1
  obtain ⟨D, _, r1⟩ := exc_bind r1
  obtain ⟨T, h2, r1⟩ := exc_bind r1
  obtain rfl : _ = X := Except.ok.inj r1
  exact h2

/-- **The premise r4 of IM.keyBack_of_rows, at the source that was returned.** -/
theorem key_planOk_at_source {m : Made} {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
    {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat}
    (r1 : sourceOf m = .ok X) (hD : X.Y.D = declKeyFull) (hT : toldOfMade m = .ok toldKeyFull)
    (hz : m.p.chains.made.sized.key = keyFull)
    (hs : m.p.chains.made.sized.set = recordSet) (c1 : m.key.1.codes = keyFull.codes)
    (c2 : m.key.2.1.codes = keyFull.codes) (c3 : m.key.2.2.codes = keyFull.codes)
    (i1 : m.p.chains.key.oneTime.indexMasks = keyFull.once.input)
    (i2 : m.p.chains.key.oneTime.ranges = keyFull.ranges.x)
    (i3 : m.p.chains.key.oneTime.binding = keyFull.binding)
    (i4 : m.p.chains.key.oneTime.codes = keyFull.codes)
    (i5 : m.p.chains.key.oneTime.lin = keyFull.once.shape)
    (i6 : m.p.chains.key.shared.codes = keyFull.codes)
    (i7 : m.p.chains.key.shared.lin = keyFull.once.shape)
    (p1 : m.p.chains.key.oneTime.given.plan = keyThree.A.plan.plan)
    (p2 : m.p.chains.key.shared.given.plan = keyThree.B.plan.plan)
    (p3 : m.p.chains.key.second.given.plan = keyThree.C.plan.plan)
    (pk : m.p.chains.made.key = [keyThree.A.plan, keyThree.B.plan, keyThree.C.plan])
    (hN : N = rangesNumsFull) (hP : P = laterPlacesFull)
    (hread : KeyChains.read m.p.chains.made.keyOneTime m.p.chains.made.keyShared
      m.p.chains.made.keySecond = some m.p.chains.key)
    (hcf : configure l x cfg bits = .ok m.p.chains.made) (h32 : cfg.size = 32)
    (hne : (cfg != Fmt.zero32) = true) (hb₁ : m.p.chains.made.keyOneTime.size < 2 ^ 64)
    (hsends : sendsOfKey m.p.chains.key = .ok m.key)
    (hY : Model.wsLayOf wsFull true recordLines.blockLog = .ok m.p.X.layers.wsLay) :
    (descriptionFromSource X N P).planOk = true :=
  key_planOk
    (pins_of_made r1 ((decl_of_source r1).trans (congrArg Except.ok hD)) hT hz hs c1 c2 c3 i1 i2 i3
      i4 i5 i6 i7 p1 p2 p3 pk hN hP)
    (by rw [k_of_made r1]; exact hread)
    (by rw [k_of_made r1]; exact digest_of_read hcf h32 hne hb₁ hread)
    (Johnson.KB9.made_ok r1 (i5.trans (congrArg (·.once.shape) hz).symm) hsends)
    (Johnson.KB9.weights_ok r1 hY i2)

end Johnson.KB4

#print axioms Johnson.KB4.decl_of_source
#print axioms Johnson.KB4.told_of_source
#print axioms Johnson.KB4.key_planOk_at_source
