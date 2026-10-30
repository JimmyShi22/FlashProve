-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.WrittenAtSeats
import Johnson.Desc.K12.Law.SitsKey
import Johnson.Desc.K12.Law.RoundsOfG
import Johnson.Desc.K12.Law.Sizes.KeyClosedAtScope
import Johnson.Goal.Numbers.PlanWrittenDescScope
/-
Johnson/Loose/H2K12/RoundsAtKeySeats.lean: AT THE FULL SIZE: IN THE KEY FILE's IOP AS WRITTEN IN
LEAN (`Key.descriptionFromSource`) THE DECLARED ROUNDS OF THE PROXIMITY TEST's THREE LATER PLACES ARE THE CLOSED
PLACES'; so the places' seven numbers are the closed places', whole, and `ClosedL` holds at the
three seats. The like of H2K12/WrittenAtSeats.lean and H2K12/RoundsAtFull.lean, which do it for a
proof file.

How. The declared rounds of a chain of that IOP are the rounds of the sub-protocols (`Block`) in the
chain's flat list; the flat lists are cut at the three seats
(Johnson/Desc/K12/Law/SitsKeyChains.lean). Where the declared rounds, written out, are the written
lists of a key file at the full size (`dryKeyFull`), the seat's place in the list is found by
counting the rounds named "BAT" in front (none; one; at the last chain no round at all is declared
in front), and the stretch there is the closed place's (Johnson/Desc/K12/Law/StretchKeyFull.lean).
The general step: `roundsOfNums_at_stretch` (Johnson/Desc/K12/Law/RoundsOfG.lean).
Main names.
  `keyDecl_atU`, `keyDecl_atO`, `keyDecl_atW`: the declared rounds, cut at the seats.
  `keySharedPre_bats`, `keySharedPreO_bats`: the rounds named "BAT" in front: 0 and 1.
  `keyPlan_U`, `keyPlan_O`, `keyPlan_W`: at the three seats the proximity test's sub-protocol passes
    its own public test on the list of rounds (`planOk`), where `Key.descriptionFromSource` passes its own.
  `earlierK_full`: the placeholders for the trees of the two chains in front are the closed ones.
  `rounds_at_key_U`, `rounds_at_key_O`, `rounds_at_key_W`: THE DECLARED ROUNDS.
  `closedL_at_key_U`, `closedL_at_key_O`, `closedL_at_key_W`: `ClosedL` at the seats.
  `closedL_key_of_pins`: the three at once, with the written lists paid by a yes of the test
    `seatPinnedKey` at public files in the goals' scope (`seat_in_scope_key`,
    Johnson/Goal/Numbers/PlanWrittenDescScope.lean). hk, hset and h stay premises.
What is asked. hk, hset: the planner's sizes of a key are `keyFull`, the setting is `setAt`. h: what
`Key.laterPlaces` returns. hp: `Key.descriptionFromSource`'s public tests on the list of rounds (`planOk`). hW: its
declared rounds, written out, are `dryKeyFull`.
What it is not. hk, hset and h are paid nowhere here. That the list of rounds has a place for
Omega's test is a premise at that seat. The written lists are what a print of the planner showed. No
law and no bound by itself. The first chain's own test is not here. Off the library's tree. No
soundness is claimed. Nothing on hiding.

-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Coin (ClosedL)
open H2K.Made (batsR bats)
open H2K.Member (piKUFull piKOFull piKWFull rKUFull rKOFull rKWFull setAt earlierKFull)
open Johnson.G (dryKeyFull)

/-! ## 1. The declared rounds, cut at the seats -/

theorem keyDecl_atU (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces) :
    (Key.descriptionFromSource X N P).roundsDeclaredByBlocks.2.1 =
      (keySharedPre X.chains P).flatMap (·.rounds) ++
        ((proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) : Blk').rounds ++
          ((P.O.toList.map keyOmega) ++ [keySharedEnd X.chains P]).flatMap (·.rounds)) := by
  rw [← (keyGu_sits P).rounds, ← flat_rounds, ← keyShared_cut X.chains P]
  rfl

theorem keyDecl_atO (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces)
    (nO : H2U.PlaceNums) (hO : P.O = some nO) :
    (Key.descriptionFromSource X N P).roundsDeclaredByBlocks.2.1 =
      (keySharedPre X.chains P ++ [keyGu P]).flatMap (·.rounds) ++
        ((proximityTestKind guardedProximityTestParts (pGomega nO) : Blk').rounds ++
          [keySharedEnd X.chains P].flatMap (·.rounds)) := by
  rw [← (omegaEntry_sits Key.Claim nO).rounds, ← flat_rounds]
  show _ = ((keySharedPre X.chains P ++ [keyGu P]) ++ keyOmega nO ::
    [keySharedEnd X.chains P]).flatMap (·.rounds)
  rw [← keyShared_cut_omega X.chains P nO hO]
  rfl

theorem keyDecl_atW (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces) :
    (Key.descriptionFromSource X N P).roundsDeclaredByBlocks.2.2 =
      (proximityTestKind guardedProximityTestParts (pOwnK P) : Blk').rounds ++
        [secondEnd Key.Claim (Key.thirdPar X.chains) (proximityTestKind guardedProximityTestParts (pOwnK P) : Blk')].flatMap
          (·.rounds) := by
  have e : (Key.descriptionFromSource X N P).roundsDeclaredByBlocks.2.2 =
      (secondPre Key.Claim (Key.thirdPar X.chains) (proximityTestKind guardedProximityTestParts (pOwnK P) : Blk')).flatMap
          (·.rounds) ++
        ((ownEntry Key.Claim (proximityTestKind guardedProximityTestParts (pOwnK P) : Blk')).rounds ++
          [secondEnd Key.Claim (Key.thirdPar X.chains) (proximityTestKind guardedProximityTestParts (pOwnK P) : Blk')].flatMap
            (·.rounds)) := by
    rw [← flat_rounds, ← keySecond_cut X.chains P]
    rfl
  rw [e, secondPre_rounds, (ownEntry_sits Key.Claim _).rounds]
  rfl

/-! ## 2. The rounds named "BAT" in front; the sub-protocol's own public test at the seats -/

/-- In front of the test on G_u no declared round is named "BAT". -/
theorem keySharedPre_bats (c : OnBytes.Model.Verify.Chains) (P : Key.LaterPlaces) :
    batsR ((keySharedPre c P).flatMap (·.rounds)) = 0 := by
  apply batsR_zero
  intro r hr
  obtain ⟨b, hb, hr⟩ := List.mem_flatMap.1 hr
  unfold keySharedPre at hb
  rcases List.mem_cons.1 hb with rfl | hb
  · exact absurd (show r ∈ ([] : List Fmt.DeclaredRound) from hr) List.not_mem_nil
  · obtain ⟨b0, hb0, rfl⟩ := List.mem_map.1 hb
    exact blocksOr_noBat _ b0 hb0 r hr

section
variable (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces)
  (hp : (Key.descriptionFromSource X N P).planOk = true)
include hp

theorem keyPlan_U : (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) : Blk').planOk = true := by
  obtain ⟨_, b2, _⟩ := Keeps.planOk_blocks _ hp
  exact (keyGu_sits P).plan (b2 _ ((keyShared_cut X.chains P) ▸
    List.mem_append_right _ List.mem_cons_self))

theorem keyPlan_O (nO : H2U.PlaceNums) (hO : P.O = some nO) :
    (proximityTestKind guardedProximityTestParts (pGomega nO) : Blk').planOk = true := by
  obtain ⟨_, b2, _⟩ := Keeps.planOk_blocks _ hp
  exact (omegaEntry_sits Key.Claim nO).plan (b2 _ ((keyShared_cut_omega X.chains P nO hO) ▸
    List.mem_append_right _ List.mem_cons_self))

theorem keyPlan_W : (proximityTestKind guardedProximityTestParts (pOwnK P) : Blk').planOk = true := by
  obtain ⟨_, _, b3⟩ := Keeps.planOk_blocks _ hp
  exact (ownEntry_sits Key.Claim _).plan (b3 _ ((keySecond_cut X.chains P) ▸
    List.mem_append_right _ List.mem_cons_self))

/-- In front of the test on G_omega: one: G_u's test's own. -/
theorem keySharedPreO_bats :
    batsR ((keySharedPre X.chains P ++ [keyGu P]).flatMap (·.rounds)) = 1 := by
  have h1 := keySharedPre_bats X.chains P
  have h2 : batsR (keyGu P).rounds = 1 := by
    rw [(keyGu_sits P).rounds]
    exact k12_bats guardedProximityTestParts _ (keyPlan_U X N P hp)
  unfold batsR bats at h1 h2 ⊢
  rw [List.flatMap_append, List.map_append, List.filter_append, List.length_append, h1]
  simpa using h2

end

/-- At the written lists the placeholders for the trees of the two chains in front are the closed
ones. -/
theorem earlierK_full {D : Johnson.G.OfPlan.Decl3}
    (hW : Johnson.G.OfPlan.writtenOf "key file" D = .ok dryKeyFull) :
    H2K.Pub.earlierOf D = earlierKFull := by
  unfold H2K.Pub.earlierOf
  rw [roots_whole (H2K.Pub.chains_of_written hW).1, H2K.Member.rootsK_first,
    roots_whole (H2K.Pub.chains_of_written hW).2.1]
  rw [show ((dryKeyFull.2.1.map (·.1)).map (·.entry.roots)).sum = 11 from
    H2K.Member.rootsK_shared]
  rfl

/-! ## 3. The declared rounds at the three seats -/

section
variable {m : Johnson.G.OfPlan.Made} {P : Key.LaterPlaces}
  (hk : m.p.chains.made.sized.key = Lk6.AtPlan.keyFull) (hset : m.p.chains.made.sized.set = setAt)
  (h : Key.laterPlaces m = .ok P) (X : Key.Source) (N : H2U.PlaceNums)
  (hp : (Key.descriptionFromSource X N P).planOk = true)
  (hW : Johnson.G.OfPlan.writtenOf "key file" (Key.descriptionFromSource X N P).roundsDeclaredByBlocks = .ok dryKeyFull)
include hk hset h hp hW

/-- **At the test on G_u.** -/
theorem rounds_at_key_U : H2U.roundsOfNums P.U.nums = H2U.roundsOfNums piKUFull.nums := by
  obtain ⟨hr0, r, R', er, hr⟩ := seat_rounds ⟨2, none, 9, .K12⟩ P.U (keyPlan_U X N P hp)
  have hx := (H2K.Pub.chains_of_written hW).2.1
  rw [keyDecl_atU] at hx
  have hl : ((keySharedPre X.chains P).flatMap (·.rounds)).length = 8 := by
    have hx' := hx
    rw [er] at hx'
    exact pre_length_closed hx' hr (keySharedPre_bats X.chains P) H2K.Member.bat_KUFull
  obtain ⟨e1, _, e3, _⟩ := (H2K.Sizes.later_of_full hk hset h).1
  exact H2K.Pub.roundsOfNums_at_stretch H2K.Pub.srcInj_nil hx hr0 H2K.Member.rounds_KUFull
    (by rw [hl]; exact H2K.Member.stretch_KUFull)
    (e3.trans H2K.Pub.held_KU.2.2.1.symm) (e1.trans H2K.Pub.held_KU.1.symm)

/-- **At the test on G_omega, where the plan has one.** -/
theorem rounds_at_key_O (nO : H2U.PlaceNums) (hO : P.O = some nO) :
    H2U.roundsOfNums nO.nums = H2U.roundsOfNums piKOFull.nums := by
  obtain ⟨hr0, r, R', er, hr⟩ := seat_rounds ⟨2, none, 10, .K12⟩ nO (keyPlan_O X N P hp nO hO)
  have hx := (H2K.Pub.chains_of_written hW).2.1
  rw [keyDecl_atO X N P nO hO] at hx
  have hl : ((keySharedPre X.chains P ++ [keyGu P]).flatMap (·.rounds)).length = 43 := by
    have hx' := hx
    rw [show (proximityTestKind guardedProximityTestParts (pGomega nO) : Blk').rounds = r :: R' from er] at hx'
    exact pre_length_closed hx' hr (keySharedPreO_bats X N P hp) H2K.Member.bat_KOFull
  obtain ⟨e1, _, e3, _⟩ := (H2K.Sizes.later_of_full hk hset h).2.2 nO hO
  exact H2K.Pub.roundsOfNums_at_stretch H2K.Pub.srcInj_nil hx hr0 H2K.Member.rounds_KOFull
    (by rw [hl]; exact H2K.Member.stretch_KOFull)
    (e3.trans H2K.Pub.held_KO.2.2.1.symm) (e1.trans H2K.Pub.held_KO.1.symm)

/-- **At the own test.** -/
theorem rounds_at_key_W : H2U.roundsOfNums P.W.nums = H2U.roundsOfNums piKWFull.nums := by
  obtain ⟨hr0, _⟩ := seat_rounds ⟨3, none, 2, .K12⟩ P.W (keyPlan_W X N P hp)
  have hx := (H2K.Pub.chains_of_written hW).2.2
  rw [earlierK_full hW, keyDecl_atW] at hx
  obtain ⟨e1, _, e3, _⟩ := (H2K.Sizes.later_of_full hk hset h).2.1
  exact H2K.Pub.roundsOfNums_at_stretch (pre := []) (H2K.Pub.srcInj_tags 6 11) hx hr0
    H2K.Member.rounds_KWFull H2K.Member.stretch_KWFull
    (e3.trans H2K.Pub.held_KW.2.2.1.symm) (e1.trans H2K.Pub.held_KW.1.symm)

/-! ## 4. `ClosedL` at the three seats -/

theorem closedL_at_key_U :
    ClosedL (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) rKUFull 1 0 0 H2K.Pub.TKUFull :=
  H2K.Sizes.closedL_KU hk hset h _ (keyPlan_U X N P hp) (rounds_at_key_U hk hset h X N hp hW)

theorem closedL_at_key_O (nO : H2U.PlaceNums) (hO : P.O = some nO) :
    ClosedL (pGomega nO) rKOFull 1 0 0 H2K.Pub.TKOFull :=
  H2K.Sizes.closedL_KO hk hset h ⟨2, none, 10, .K12⟩ nO hO (keyPlan_O X N P hp nO hO)
    (rounds_at_key_O hk hset h X N hp hW nO hO)

theorem closedL_at_key_W : ClosedL (pOwnK P) rKWFull 2 6 2 H2K.Pub.TKWFull :=
  H2K.Sizes.closedL_KW hk hset h _ (keyPlan_W X N P hp) (rounds_at_key_W hk hset h X N hp hW)

end

/-- **The three at once.** hk, hset and h stand as premises; the written lists are paid by a yes of
the test `seatPinnedKey` at public files in the goals' scope. -/
theorem closedL_key_of_pins {S : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope S = true)
    {m : Johnson.G.OfPlan.Made} {P : Key.LaterPlaces}
    (hk : m.p.chains.made.sized.key = Lk6.AtPlan.keyFull)
    (hset : m.p.chains.made.sized.set = setAt) (h : Key.laterPlaces m = .ok P) (X : Key.Source)
    (N : H2U.PlaceNums) (hp : (Key.descriptionFromSource X N P).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedKey S.pol (Key.descriptionFromSource X N P) = true) :
    ClosedL (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) rKUFull 1 0 0 H2K.Pub.TKUFull ∧
      (∀ nO, P.O = some nO → ClosedL (pGomega nO) rKOFull 1 0 0 H2K.Pub.TKOFull) ∧
      ClosedL (pOwnK P) rKWFull 2 6 2 H2K.Pub.TKWFull := by
  have hW := (VerifiableInference.PlanWritten.seat_in_scope_key _ _ S hS hpin).1
  exact ⟨closedL_at_key_U hk hset h X N hp hW,
    fun nO hO => closedL_at_key_O hk hset h X N hp hW nO hO,
    closedL_at_key_W hk hset h X N hp hW⟩

end H2K.JointK

#print axioms H2K.JointK.rounds_at_key_U
#print axioms H2K.JointK.rounds_at_key_O
#print axioms H2K.JointK.rounds_at_key_W
#print axioms H2K.JointK.closedL_key_of_pins
