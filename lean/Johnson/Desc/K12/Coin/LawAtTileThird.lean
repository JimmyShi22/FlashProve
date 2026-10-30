-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Coin/LawAtTileThird.lean: the law's public premises of the proximity test (the kind
K12) at the stretch that a description's own data hold for it ON THE LAST CHAIN, first arm, and the
two comparisons of its counts with the cap at 128 bits; general in the description. Statements and
proofs; each proof is a row of calls.

Why so little. The game at the piece that the description's tiling holds on the last chain lies in
`rowTwo_cand_game` (RowTwoGame.lean), at any errors above the counts (and over it the whole row of
the last chain from one structure of premises). That structure books four fields to K12's files: two
tests on the place (`johOk`, `batOneOk`) and two comparisons: "BAT"'s count times the sampler's
number against the cap's number for that round, and the place's own errors `errJ` against the cap's,
round by round. This file has the two comparisons, at whatever description has data. No piece and no
game is typed here: they would be twins.
What is called: `atPlace_lastJ` (AtDescJ.lean); `TileAt`, `errJ_small`
(LawAtTile.lean), `ChainAt` (LawAtLight.lean), `batBelow_like`
(Johnson/Desc/K12/Law/BatValsPayAt.lean); `roundsOfData`
(Johnson/Desc/Sound/DataRounds.lean); `Err.le_cap_of_below_inv` (Iop/ErrCap.lean). The proof of
`atPlace_tile₃` is LawAtTile.lean's `atPlace_tile₂` and LawAtTileFirst.lean's `atPlace_tile₁`,
carried to the last chain by a program that turns names.
What it is not, first.
  (1) The first arm alone (no own mask), the last chain alone.
  (2) How the flat list parts, that the block declares the test's rounds, the count of roots in
    front, the block's test on the plan, the chain at the radii, the two tests and that the
    description has data are premises: shown here of no description.
  (3) "At most the cap" is a comparison of counts with the number of a round's written verifier
    messages divided by 2 ^ 128. It says nothing on what a count is worth.
Main names.
  `atPlace_tile₃`: at a description with data whose last chain's flat list is pre ++ B :: post, B
    declaring the test's rounds: `TileAt` at the stretch of the last chain's data.
  `cap_of_tile`: `TileAt` at the bar 2⁻¹ ^ 128 gives: the whole entry is at most the cap, round by
    round. General in the frame and the numbering.
  `count_errs_tile₃`: the two comparisons at that stretch, apart.
Limits: those of the files called. No soundness is claimed. Nothing on hiding.

-/
import Johnson.Desc.K12.Coin.LawAtTile
import Johnson.Desc.K12.Coin.AtDescJ
import Iop.ErrCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open H2K.Pub (sgOf writtenOf WR chainFrom johOk batV0 batPriceOk)
open H2K.Member (wsAt w0At dtAt wsAt_cons)
open H2K.Pin (NTuple)
open Johnson.G.OfPlan (rootsOf)
open scoped ENNReal

/-- **At the last chain of a description with data.** -/
theorem atPlace_tile₃ {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D) (key : ℕ → ℕ) (ft : ℕ) (π : P12) (r : Fmt.M1.Stage → ℕ) (k : ℕ)
    (pre : List (Block F.S₃ F.Cl)) (B : Block F.S₃ F.Cl) (post : List (Block F.S₃ F.Cl))
    (hfl : F.second.blocksInOrder = pre ++ B :: post)
    (hB : B.rounds = (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds)
    (hfree : π.nums.free = rootsOf (pre.flatMap (·.rounds)))
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hC : ChainAt π r ((2 : ℝ≥0∞)⁻¹ ^ k)) (hj : johOk π r = true)
    (hbat : batPriceOk π r k = true) (ho : π.nums.ownMask = false) :
    ∃ dB dt, (D.ds₃.drop (pre.flatMap (·.rounds)).length).take
        (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length = dB :: dt ∧
      TileAt (frameAt D (allOf D) key ft) π (numAt F.t₁ F.t₂ 2) r ((2 : ℝ≥0∞)⁻¹ ^ k)
        (D.t₁ + D.t₂ + nTrees (D.ds₃.take (pre.flatMap (·.rounds)).length)) dB dt := by
  have hA := roundsOfData F file D h
  have e : F.roundsDeclaredByBlocks.2.2 = pre.flatMap (·.rounds) ++
      ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds ++ post.flatMap (·.rounds)) := by
    show F.second.blocksInOrder.flatMap (·.rounds) = _
    rw [hfl, List.flatMap_append, List.flatMap_cons, hB]
  have hAs : List.Forall₂ RoundAsG D.ds₃ (pre.flatMap (·.rounds) ++
      ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds ++ post.flatMap (·.rounds))) := by
    rw [← e]
    exact hA.2.2
  have hL := (forall₂_cut _ _ _ hAs).length_eq
  have hrs : H2U.roundsOfNums π.nums = some (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds :=
    VerifiableInference.Desc.K12.k12_rounds guardedProximityTestParts π hp
  have hpos : 0 < (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length := by
    obtain ⟨_, _, _, R, _, _, hR⟩ := H2K.Made.rounds_top π.nums _ hrs
    rw [hR]
    exact Nat.succ_pos _
  obtain ⟨dB, dt, hlist⟩ : ∃ dB dt, (D.ds₃.drop (pre.flatMap (·.rounds)).length).take
      (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length = dB :: dt := by
    cases hq : (D.ds₃.drop (pre.flatMap (·.rounds)).length).take
        (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length with
    | nil =>
      rw [hq, List.length_nil] at hL
      omega
    | cons x y => exact ⟨x, y, rfl⟩
  have hw := (wsAt_cons π hp).1
  have hAt : AtPlace (frameAt D (allOf D) key ft) π (numAt F.t₁ F.t₂ 2) Sg.lstJ Sg.flC Sg.flZ
      Sg.flZ (fun s => r s.st)
      (D.t₁ + D.t₂ + nTrees (D.ds₃.take (pre.flatMap (·.rounds)).length)) dB dt (errJ π r dt) :=
    atPlace_lastJ F file D h key ft π r (pre.flatMap (·.rounds)) (post.flatMap (·.rounds)) e dB dt
      hlist.symm hfree (H2K.JointK.early_of_planOk π hp) (H2K.JointK.answers_of_planOk π hp) hp
      (H2K.Made.spendOk_of_planOk π hp) hj ho _ _ hw
  refine ⟨dB, dt, hlist, hAt, errJ_small hC hAt.like ?_⟩
  obtain ⟨a₀, rest₀, _, _, _, e1, _⟩ := hC
  exact H2K.Pin.batBelow_like π r k a₀ rest₀ e1 dB dt hAt.like hbat

/-- **Below the bar 2⁻¹ ^ 128 is at most the cap**, the whole entry, round by round. -/
theorem cap_of_tile {Fr : Frame} {π : P12} {num : Fmt.TreeSource → ℕ} {r : Fmt.M1.Stage → ℕ}
    {base : ℕ} {dB : RDT} {dt : List RDT}
    (h : TileAt Fr π num r ((2 : ℝ≥0∞)⁻¹ ^ 128) base dB dt) :
    Err.le (s := uLT (ckP .two) (dB :: dt))
      (batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt)
      (Err.cap 128 (uLT (ckP .two) (dB :: dt))) :=
  Err.le_cap_of_below_inv 128 _ h.2

/-- **The two comparisons at the last chain's stretch, apart**: "BAT"'s count times the sampler's
number is at most the cap's first entry; the place's own errors are at most the cap's other entries,
round by round. The stretch is named by its equation, so that whoever holds dB :: dt from elsewhere
can call it. -/
theorem count_errs_tile₃ {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D) (π : P12) (r : Fmt.M1.Stage → ℕ)
    (pre : List (Block F.S₃ F.Cl)) (B : Block F.S₃ F.Cl) (post : List (Block F.S₃ F.Cl))
    (hfl : F.second.blocksInOrder = pre ++ B :: post)
    (hB : B.rounds = (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds)
    (hfree : π.nums.free = rootsOf (pre.flatMap (·.rounds)))
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hC : ChainAt π r ((2 : ℝ≥0∞)⁻¹ ^ 128)) (hj : johOk π r = true)
    (hbat : batPriceOk π r 128 = true) (ho : π.nums.ownMask = false)
    (dB : RDT) (dt : List RDT)
    (hds : (D.ds₃.drop (pre.flatMap (·.rounds)).length).take
      (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length = dB :: dt) :
    batV0 π r * (bsRound .two dB.entry dB.kind).w ≤
        (Err.cap 128 (uLT (ckP .two) (dB :: dt))).1 ∧
      Err.le (errJ π r dt) (Err.cap 128 (uLT (ckP .two) (dB :: dt))).2 := by
  obtain ⟨dB', dt', hc', ht⟩ := atPlace_tile₃ F file D h D.key₃ F.lastChainFirstTreeNumber π r 128 pre B post
    hfl hB hfree hp hC hj hbat ho
  obtain ⟨e1, e2⟩ := List.cons.inj (hds.symm.trans hc')
  subst e1
  subst e2
  exact cap_of_tile ht

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.atPlace_tile₃
#print axioms VerifiableInference.Desc.K12.Coin.cap_of_tile
#print axioms VerifiableInference.Desc.K12.Coin.count_errs_tile₃
