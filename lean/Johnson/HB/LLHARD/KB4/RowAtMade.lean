-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB4/RowAtMade.lean: (Key.descriptionFromSource X N P).planOk = true, the premise r4 of
IM.keyBack_of_rows (Johnson/IMR/KeyBackOfRows.lean), from Key.sourceOf's return and plain equations
and returns about m, the planner's answer with the sendings: so that a later proof needs one call.
Calls, with small steps in between.

Main names.
  hcfg_of_made: the clause "digest" at Key.sourceOf's return: the digest as read back is the digest
  at which the planner was called (OnBytes.TieK.G.chains_same, OnBytes/TieK/G/SameChainsG.lean,
  under three of the bounds on the strings' lengths), and that one is not 32 zero bytes.
  key_planOk_at_made: key_planOk (Row.lean) with Pins gathered by pins_of_made (PinsOfMade.lean),
  "digest" by hcfg_of_made, "made" by Johnson.KB9.made_ok, "weights" by Johnson.KB9.weights_ok.
The premises of key_planOk_at_made, and what is meant to give each.
  r1, hD, hT: Key.sourceOf returns; the declared rounds and the tenants as told are the written
  ones: whatever shows what Key.sourceOf returns. hN, hP: whatever shows what Key.rangesNumbers and
  Key.laterPlaces return.
  hc, hz, c1, c2, c3, hY: IM.keyPins_at_made. hs, p1, p2, p3, pk, hread: IM.keyPlans_at_made.
  i1 to i7: Johnson.KB9.items_at_made. hsends: Johnson.KB9.sends_of_from.
  r7: the premise r7 of IM.keyBack_of_rows. h32, hne: at the fixed digest Key.fixedDigest_size and
  Key.fixedDigest_ne (Johnson/Desc/Key/SlotIs.lean).
Limits. NOT ONE OF THESE PREMISES IS SHOWN HERE; that they can be met together is shown by
no theorem in this file or in the files that it imports, and, as far as this file's authors know,
no theorem in this library states it and no proof calls key_planOk_at_made. If they could not,
the theorem would hold vacuously. Parts are had in other files. All the premises but hD, hc, r7 and
hread are premises of key_planOk_at_source (RowAtSource.lean) too, which key_planOk_in_scope
(RowInScope.lean) calls: where those are used together, and with what limits, is said in
RowAtSource.lean's head. Of the four: for public files in scope of the goals, where publicOfO and
Key.madeAt return, hc is among the conclusions of IM.keyPins_at_made
(Johnson/IMR/KeyPinsAtMade.lean) and hread, at three named strings, among those of
IM.keyPlans_at_made (Johnson/IMR/KeyPlansAtMade.lean); hD follows, at the constant digest
Key.fixedDigest, from decl_of_source (RowAtSource.lean) and Johnson.AtFull.KeyBack.decl_at_return
(Johnson/AtFull/KeyBack/InScopeNamed.lean); r7 is the conclusion of
Johnson.AtFull.KeyBack.r7_of_shapes (Johnson/AtFull/KeyBack/R7AtMade.lean), which has further
premises. As far as this file's authors know, no proof puts the four together with the rest.
Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB4.Row
import Johnson.HB.LLHARD.KB4.PinsOfMade
import Johnson.HB.LLHARD.KB9.FileMade
import Johnson.HB.LLHARD.KB9.FileWeights
import OnBytes.TieK.G.SameChainsG

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB4

open VerifiableInference.Desc VerifiableInference.Desc.Key
open OnBytes OnBytes.Params OnBytes.Model.Verify
open OnBytes.Params (exc_bind)
open Johnson.G.OfPlan (Made)
open Lk6.AtPlan (keyFull wsFull)
open VerifiableInference.Number.ByRuns (keyThree)
open Johnson.KB8 (declKeyFull rangesNumsFull laterPlacesFull)

/-- What the source holds as the three chains' values is the planner's. -/
theorem k_of_made {m : Made} {X : Source} (r1 : sourceOf m = .ok X) : X.Y.k = m.p.chains.key := by
  unfold sourceOf at r1
  obtain ⟨D, _, r1⟩ := exc_bind r1
  obtain ⟨T, _, r1⟩ := exc_bind r1
  obtain rfl : _ = X := Except.ok.inj r1
  rfl

/-- **The clause "digest" at the source's return.** -/
theorem hcfg_of_made {m : Made} {X : Source} {X₀ : Public} {lay : Option ByteArray}
    {cfg : ByteArray} (r1 : sourceOf m = .ok X) (hc : chainsOf X₀ lay cfg = .ok m.p.chains)
    (h32 : cfg.size = 32) (hne : (cfg != Fmt.zero32) = true)
    (r7 : ∀ n : ChainName, (m.p.chains.bytes n).size < 2 ^ 64) :
    (X.Y.k.oneTime.given.cfg != Fmt.zero32) = true := by
  rw [k_of_made r1, (OnBytes.TieK.G.chains_same h32 hc (r7 _) (r7 _) (r7 _)).1.1]
  exact hne

/-- **The premise r4 of IM.keyBack_of_rows, from equations and returns about m.** -/
theorem key_planOk_at_made {m : Made} {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
    {X₀ : Public} {lay : Option ByteArray} {cfg b₁ b₂ b₃ : ByteArray}
    (r1 : sourceOf m = .ok X) (hD : Johnson.G.OfPlan.declKOf m = .ok declKeyFull)
    (hT : toldOfMade m = .ok toldKeyFull) (hz : m.p.chains.made.sized.key = keyFull)
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
    (hread : KeyChains.read b₁ b₂ b₃ = some m.p.chains.key)
    (hc : chainsOf X₀ lay cfg = .ok m.p.chains) (h32 : cfg.size = 32)
    (hne : (cfg != Fmt.zero32) = true)
    (r7 : ∀ n : ChainName, (m.p.chains.bytes n).size < 2 ^ 64)
    (hsends : sendsOfKey m.p.chains.key = .ok m.key)
    (hY : Model.wsLayOf wsFull true recordLines.blockLog = .ok m.p.X.layers.wsLay) :
    (descriptionFromSource X N P).planOk = true :=
  key_planOk (pins_of_made r1 hD hT hz hs c1 c2 c3 i1 i2 i3 i4 i5 i6 i7 p1 p2 p3 pk hN hP)
    (by rw [k_of_made r1]; exact hread) (hcfg_of_made r1 hc h32 hne r7)
    (Johnson.KB9.made_ok r1 (i5.trans (congrArg (·.once.shape) hz).symm) hsends)
    (Johnson.KB9.weights_ok r1 hY i2)

end Johnson.KB4

#print axioms Johnson.KB4.k_of_made
#print axioms Johnson.KB4.hcfg_of_made
#print axioms Johnson.KB4.key_planOk_at_made
