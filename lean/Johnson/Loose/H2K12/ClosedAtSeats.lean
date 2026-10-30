-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.RoundsAtFull
import Johnson.Loose.H2K12.AtFullPlain
import Johnson.Desc.K12.Law.Sizes.ClosedAtScope
import Johnson.Goal.Numbers.PlanWrittenDescScope
import Johnson.Desc.K12.Coin.FirstBookOwn
/-
Johnson/Loose/H2K12/ClosedAtSeats.lean: what a caller of the law of a proximity test (the kind K12)
lays at a place, `ClosedL` (Johnson/Desc/K12/Coin/LawAtLight.lean), AT THE THREE LATER SEATS OF THE
PROOF FILE's DESCRIPTION, AT EVERY SET OF PUBLIC FILES IN THE GOALS' SCOPE; and what that file draws
from the record, there.

An assembly. No equation on a closed place is left as a premise.
The premises, five, and at O a sixth: hS: the three public files are in the goals' scope
(`VerifierAndGoals.InScope`). hZ:
the plain road's public part is made of them. hN: the places' numbers. hp: the description's tests
on the plan. hpin: the test `seatPinnedProof` says yes of the description. At O also hO: the
places' numbers hold a place for Omega (N.O = some nO). The second hash function o, the links' maker
and the first chain are free letters.
Who pays what: `AtFull`: `atFull_of_pubPlain` (H2K12/AtFullPlain.lean). The description's declared
rounds are the written lists: `seat_in_scope` (Johnson/Goal/Numbers/PlanWrittenDescScope.lean), off
hpin; whoever holds that equation by another road over the same theorem meets this one there. The
block's test on the plan at a seat: `plan_at_seat_U` and its like, here, off hp. The written rounds,
the declared rounds and the first free own number at a seat: H2K12/WrittenAtFull.lean and
H2K12/RoundsAtFull.lean. The record: `closedL_U_of_full` and its like
(Johnson/Desc/K12/Law/Sizes/ClosedAtScope.lean).
Main names, X one of U, O, W:
  `plan_at_seat_X`: the block's test on the plan says yes at the seat.
  `closedL_in_scope_X`: THE STATEMENT: `ClosedL` at the seat's place, at the closed radii and the
    closed members' own letters; and beside it: these radii are the planner's own at each stage.
  `gameV_in_scope_U`, `game_in_scope_U`, `gameOwn_in_scope_O`, `game_in_scope_W`: the forms of the
    game at a seat (Coin/GameAt.lean). THE FOUR ARE NOT ALIKE, AND NOT BY OVERSIGHT. `gameV`:
    nothing is promised of the record, and the book's places are numbered by the labels of the trees
    that stand there: it wants the test on the labels, which says yes at U (`labels_U_of_full`). At
    the closed place of W that test says no (`ownLabels_WFull`: the opened trees are taken over from
    other chains), and what it is a test for cannot be met there under any numbering
    (`noLabels_WFull`: two of the three opened trees bear one label): so W has `game`, under that
    form's promise on the record, and from 83 and 2 trees on the earlier chains on. At O the first
    fold sends its own mask: the other arm, `gameOwn`, which has no form without a promise. At U
    both forms stand; a top that wants no promise takes `gameV`.
  `numbers_in_scope_X`: the counts are the chain's own; each is below 2^-128 of its round's
    challenge values; so is the number priced at "BAT".
  `nums_in_scope_U`, `nums_in_scope_O`: all seven numbers of the seat's place are the closed
    place's. NOT an equation of whole places: the address, the index, the oracle messages, «before»,
    «early» and the answers lie outside the numbers.
  `tests_in_scope_O`: three more tests on the plan say yes at Omega's seat (`ownLabelsB`,
    Coin/FirstBook.lean; `firstNe`, Law/FirstNe.lean; a root has been sent in front).
Limits: no run, no record, no codes. NOT THE FIRST CHAIN's SEAT. hpin is a test that the description
itself does not ask; the value that is to be laid for the proof file does. Nothing shows that the
five premises hold together at any files. One round's share each, no sum; part of the 128 bits is
work at "CS" and "BASE"; "BAT"'s number is priced and is no law's count. No bound on anything that
the file's game counts follows. The closed members' limits stand.
Nothing on soundness of a verifier. Nothing on hiding.

-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Coin (ClosedL SeatGameAt SeatGameVAt SeatGameOwnAt CountsAre εAt)
open VerifiableInference.Desc.K12.Coin.At (TUFull TOFull TWFull)
open H2K.Member (piUFull piOFull piWFull rUFull rOFull rWFull dBAt)
open H2K.Pub (radBy sgOf batV0)
open OnBytes.Maker (LeftT)
open scoped ENNReal

/-! ## 1. The block's test on the plan at a seat -/

theorem plan_at_seat_U (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true) :
    (proximityTestKind guardedProximityTestParts (pGu N) : Blk').planOk = true := by
  obtain ⟨_, b2, _⟩ := Keeps.planOk_blocks _ hp
  have mU : guEntry ProofFile.Cl N ∈ (descN o mk guardedProximityTestParts Z N c).shared.blocksInOrder :=
    (descN_shared o mk guardedProximityTestParts Z N c) ▸ List.mem_append_right _ List.mem_cons_self
  exact (guEntry_sits ProofFile.Cl N).plan (b2 _ mU)

theorem plan_at_seat_O (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (nO : H2U.PlaceNums) (hO : N.O = some nO) (c : Chain First.S ProofFile.Cl)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true) :
    (proximityTestKind guardedProximityTestParts (pGomega nO) : Blk').planOk = true := by
  obtain ⟨_, b2, _⟩ := Keeps.planOk_blocks _ hp
  have hcut := shared_cut_omega ProofFile.Cl Z.p.chains (p14N Z N) N nO hO
  have mO : omegaEntry ProofFile.Cl nO ∈ (descN o mk guardedProximityTestParts Z N c).shared.blocksInOrder :=
    hcut ▸ List.mem_append_right _ List.mem_cons_self
  exact (omegaEntry_sits ProofFile.Cl nO).plan (b2 _ mO)

theorem plan_at_seat_W (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true) :
    (proximityTestKind guardedProximityTestParts (pOwn N) : Blk').planOk = true := by
  obtain ⟨_, _, b3⟩ := Keeps.planOk_blocks _ hp
  have mW : ownEntry ProofFile.Cl (proximityTestKind guardedProximityTestParts (pOwn N) : Blk') ∈
      (descN o mk guardedProximityTestParts Z N c).second.blocksInOrder :=
    (descN_second o mk guardedProximityTestParts Z N c) ▸ List.mem_append_right _ List.mem_cons_self
  exact (ownEntry_sits ProofFile.Cl _).plan (b3 _ mW)

/-! ## 2. The record at the three seats, in scope -/

/-- **In the goals' scope, at the seat of the folded row's test.** -/
theorem closedL_in_scope_U {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles}
    (hS : VerifierAndGoals.InScope S = true) (Z : ProofFile.Pub) (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z)
    (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (descN o mk guardedProximityTestParts Z N c) = true) :
    ClosedL (pGu N) rUFull 1 0 0 TUFull ∧
      ∀ a ∈ N.U.nums.stages, radBy Z.made.p.chains.made.sized.proof.set
        Z.made.p.chains.made.sized.proof.batch.folded.stages (sgOf a) = rUFull a := by
  have A := H2K.Sizes.atFull_of_pubPlain hS hZ
  have hW := (VerifiableInference.PlanWritten.seat_in_scope _ _ S hS hpin).1
  exact ⟨H2K.Sizes.closedL_U_of_full A hN _ (plan_at_seat_U o Z mk N c hp)
      (written_at_seat_U o S.pol S.lay S.KL Z hZ mk N c hN hp A hW)
      (rounds_at_seat_U o S.pol S.lay S.KL Z hZ mk N c hN hp A hW)
      (free_at_seat_U o S.pol S.lay S.KL Z hZ mk N c hN hp hW),
    (H2K.Sizes.place_U_of_full A hN).2.2⟩

/-- **In the goals' scope, at the seat of Omega's test.** -/
theorem closedL_in_scope_O {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles}
    (hS : VerifierAndGoals.InScope S = true) (Z : ProofFile.Pub) (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z)
    (mk : ProofFile.LinksBy) (N : H2U.Places4) (nO : H2U.PlaceNums) (hO : N.O = some nO)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (descN o mk guardedProximityTestParts Z N c) = true) :
    ClosedL (pGomega nO) rOFull 1 0 0 TOFull ∧
      ∀ a ∈ nO.nums.stages, radBy Z.made.p.chains.made.sized.proof.set
        Z.made.p.chains.made.sized.proof.batch.omega.stages (sgOf a) = rOFull a := by
  have A := H2K.Sizes.atFull_of_pubPlain hS hZ
  have hW := (VerifiableInference.PlanWritten.seat_in_scope _ _ S hS hpin).1
  exact ⟨H2K.Sizes.closedL_O_of_full A hN _ nO hO (plan_at_seat_O o Z mk N nO hO c hp)
      (written_at_seat_O o S.pol S.lay S.KL Z hZ mk N nO hO c hN hp A hW)
      (rounds_at_seat_O o S.pol S.lay S.KL Z hZ mk N nO hO c hN hp A hW)
      (free_at_seat_O o S.pol S.lay S.KL Z hZ mk N nO hO c hN hp hW),
    (H2K.Sizes.place_O_of_full A hN nO hO).2.2⟩

/-- **In the goals' scope, at the seat of the request's own test.** -/
theorem closedL_in_scope_W {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles}
    (hS : VerifierAndGoals.InScope S = true) (Z : ProofFile.Pub) (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z)
    (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (descN o mk guardedProximityTestParts Z N c) = true) :
    ClosedL (pOwn N) rWFull 2 83 2 TWFull ∧
      ∀ a ∈ N.W.nums.stages, radBy Z.made.p.chains.made.sized.proof.set
        Z.made.p.chains.made.sized.proof.batch.own.stages (sgOf a) = rWFull a := by
  have A := H2K.Sizes.atFull_of_pubPlain hS hZ
  have hW := (VerifiableInference.PlanWritten.seat_in_scope _ _ S hS hpin).1
  exact ⟨H2K.Sizes.closedL_W_of_full A hN _ (plan_at_seat_W o Z mk N c hp)
      (written_at_seat_W o S.pol S.lay S.KL Z hZ mk N c hN hp A hW)
      (rounds_at_seat_W o Z mk N c hN hp A hW)
      (free_at_seat_W o S.pol S.lay S.KL Z hZ mk N c hN hp),
    (H2K.Sizes.place_W_of_full A hN).2.2⟩

/-! ## 3. What follows from the record, in scope -/

/-- The own mask at the three seats, in scope: as at the closed places. The test hpin is not asked.
-/
theorem ownMask_in_scope_U {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles}
    (hS : VerifierAndGoals.InScope S = true) (Z : ProofFile.Pub) (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z)
    (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true) :
    (pGu N).nums.ownMask = false := by
  have A := H2K.Sizes.atFull_of_pubPlain hS hZ
  have hn := H2K.Made.nums_of_planOk ⟨2, none, 9, .K12⟩ N.U (plan_at_seat_U o Z mk N c hp)
  exact (congrArg (·.ownMask) hn).trans (H2K.Sizes.more_U_of_full A hN).2.1

theorem ownMask_in_scope_O {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles}
    (hS : VerifierAndGoals.InScope S = true) (Z : ProofFile.Pub) (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z)
    (mk : ProofFile.LinksBy) (N : H2U.Places4) (nO : H2U.PlaceNums) (hO : N.O = some nO)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true) :
    (pGomega nO).nums.ownMask = true := by
  have A := H2K.Sizes.atFull_of_pubPlain hS hZ
  have hn := H2K.Made.nums_of_planOk ⟨2, none, 10, .K12⟩ nO (plan_at_seat_O o Z mk N nO hO c hp)
  exact (congrArg (·.ownMask) hn).trans (H2K.Sizes.more_O_of_full A hN nO hO).2.1

theorem ownMask_in_scope_W {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles}
    (hS : VerifierAndGoals.InScope S = true) (Z : ProofFile.Pub) (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z)
    (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true) :
    (pOwn N).nums.ownMask = false := by
  have A := H2K.Sizes.atFull_of_pubPlain hS hZ
  have hn := H2K.Made.nums_of_planOk ⟨3, none, 2, .K12⟩ N.W (plan_at_seat_W o Z mk N c hp)
  exact (congrArg (·.ownMask) hn).trans (H2K.Sizes.more_W_of_full A hN).2.1

/-- **The game at the folded row's seat with nothing promised of the record.** -/
theorem gameV_in_scope_U {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles}
    (hS : VerifierAndGoals.InScope S = true) (Z : ProofFile.Pub) (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z)
    (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (descN o mk guardedProximityTestParts Z N c) = true)
    (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ) :
    SeatGameVAt (pGu N) rUFull 1 TUFull t₁ t₂ a more key := by
  have A := H2K.Sizes.atFull_of_pubPlain hS hZ
  have hW := (VerifiableInference.PlanWritten.seat_in_scope _ _ S hS hpin).1
  exact (closedL_in_scope_U hS Z hZ mk N c hN hp hpin).1.gameV
    (ownMask_in_scope_U hS Z hZ mk N c hN hp)
    (H2K.Sizes.labels_U_of_full A hN _ (plan_at_seat_U o Z mk N c hp)
      (rounds_at_seat_U o S.pol S.lay S.KL Z hZ mk N c hN hp A hW)
      (free_at_seat_U o S.pol S.lay S.KL Z hZ mk N c hN hp hW))
    t₁ t₂ a more key (Nat.zero_le _) (Nat.zero_le _)

theorem game_in_scope_U {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles}
    (hS : VerifierAndGoals.InScope S = true) (Z : ProofFile.Pub) (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z)
    (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (descN o mk guardedProximityTestParts Z N c) = true)
    (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ) :
    SeatGameAt (pGu N) rUFull 1 TUFull t₁ t₂ a more key :=
  (closedL_in_scope_U hS Z hZ mk N c hN hp hpin).1.game
    (ownMask_in_scope_U hS Z hZ mk N c hN hp)
    t₁ t₂ a more key (Nat.zero_le _) (Nat.zero_le _)

theorem gameOwn_in_scope_O {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles}
    (hS : VerifierAndGoals.InScope S = true) (Z : ProofFile.Pub) (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z)
    (mk : ProofFile.LinksBy) (N : H2U.Places4) (nO : H2U.PlaceNums) (hO : N.O = some nO)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (descN o mk guardedProximityTestParts Z N c) = true)
    (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ) :
    SeatGameOwnAt (pGomega nO) rOFull 1 TOFull t₁ t₂ a more key :=
  (closedL_in_scope_O hS Z hZ mk N nO hO c hN hp hpin).1.gameOwn
    (ownMask_in_scope_O hS Z hZ mk N nO hO c hN hp)
    t₁ t₂ a more key (Nat.zero_le _) (Nat.zero_le _)

theorem game_in_scope_W {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles}
    (hS : VerifierAndGoals.InScope S = true) (Z : ProofFile.Pub) (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z)
    (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (descN o mk guardedProximityTestParts Z N c) = true)
    (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ) (h₁ : 83 ≤ t₁) (h₂ : 2 ≤ t₂) :
    SeatGameAt (pOwn N) rWFull 2 TWFull t₁ t₂ a more key :=
  (closedL_in_scope_W hS Z hZ mk N c hN hp hpin).1.game
    (ownMask_in_scope_W hS Z hZ mk N c hN hp)
    t₁ t₂ a more key h₁ h₂

/-- **The numbers at the folded row's seat**: the counts are the chain's own; each is below; so is
the number priced at "BAT". -/
theorem numbers_in_scope_U {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles}
    (hS : VerifierAndGoals.InScope S = true) (Z : ProofFile.Pub) (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z)
    (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (descN o mk guardedProximityTestParts Z N c) = true)
    (num : Fmt.TreeSource → ℕ) :
    CountsAre num (pGu N) rUFull ∧ Iop.Err.Below (εAt num (pGu N) rUFull) ((2 : ℝ≥0∞)⁻¹ ^ 128) ∧
      OnBytes.Slice.RoundBelow (batV0 (pGu N) rUFull) (OnBytes.Flat.toRD (dBAt num (pGu N)))
        ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  have C := (closedL_in_scope_U hS Z hZ mk N c hN hp hpin).1
  ⟨C.counts num, C.small num, C.batSmall num⟩

theorem numbers_in_scope_O {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles}
    (hS : VerifierAndGoals.InScope S = true) (Z : ProofFile.Pub) (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z)
    (mk : ProofFile.LinksBy) (N : H2U.Places4) (nO : H2U.PlaceNums) (hO : N.O = some nO)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (descN o mk guardedProximityTestParts Z N c) = true)
    (num : Fmt.TreeSource → ℕ) :
    CountsAre num (pGomega nO) rOFull ∧
      Iop.Err.Below (εAt num (pGomega nO) rOFull) ((2 : ℝ≥0∞)⁻¹ ^ 128) ∧
      OnBytes.Slice.RoundBelow (batV0 (pGomega nO) rOFull)
        (OnBytes.Flat.toRD (dBAt num (pGomega nO))) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  have C := (closedL_in_scope_O hS Z hZ mk N nO hO c hN hp hpin).1
  ⟨C.counts num, C.small num, C.batSmall num⟩

theorem numbers_in_scope_W {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles}
    (hS : VerifierAndGoals.InScope S = true) (Z : ProofFile.Pub) (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z)
    (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (descN o mk guardedProximityTestParts Z N c) = true)
    (num : Fmt.TreeSource → ℕ) :
    CountsAre num (pOwn N) rWFull ∧ Iop.Err.Below (εAt num (pOwn N) rWFull) ((2 : ℝ≥0∞)⁻¹ ^ 128) ∧
      OnBytes.Slice.RoundBelow (batV0 (pOwn N) rWFull) (OnBytes.Flat.toRD (dBAt num (pOwn N)))
        ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  have C := (closedL_in_scope_W hS Z hZ mk N c hN hp hpin).1
  ⟨C.counts num, C.small num, C.batSmall num⟩

/-! ## 4. All seven numbers, and three more tests on the plan, in scope -/

/-- **In the goals' scope all seven numbers of the place at the folded row's seat are the closed
place's.** Outside them lie the address, the index, the oracle messages, «before», «early» and the
answers: no equation of whole places is said. -/
theorem nums_in_scope_U {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles}
    (hS : VerifierAndGoals.InScope S = true) (Z : ProofFile.Pub) (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z)
    (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (descN o mk guardedProximityTestParts Z N c) = true) :
    (pGu N).nums = piUFull.nums := by
  have A := H2K.Sizes.atFull_of_pubPlain hS hZ
  have hW := (VerifiableInference.PlanWritten.seat_in_scope _ _ S hS hpin).1
  have hq := plan_at_seat_U o Z mk N c hp
  exact (H2K.Made.nums_of_planOk ⟨2, none, 9, .K12⟩ N.U hq).trans
    (H2K.Sizes.nums_U_of_full A hN _ hq
      (rounds_at_seat_U o S.pol S.lay S.KL Z hZ mk N c hN hp A hW)
      (free_at_seat_U o S.pol S.lay S.KL Z hZ mk N c hN hp hW))

/-- The same at the seat of Omega's test. -/
theorem nums_in_scope_O {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles}
    (hS : VerifierAndGoals.InScope S = true) (Z : ProofFile.Pub) (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z)
    (mk : ProofFile.LinksBy) (N : H2U.Places4) (nO : H2U.PlaceNums) (hO : N.O = some nO)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (descN o mk guardedProximityTestParts Z N c) = true) :
    (pGomega nO).nums = piOFull.nums := by
  have A := H2K.Sizes.atFull_of_pubPlain hS hZ
  have hW := (VerifiableInference.PlanWritten.seat_in_scope _ _ S hS hpin).1
  have hq := plan_at_seat_O o Z mk N nO hO c hp
  exact (H2K.Made.nums_of_planOk ⟨2, none, 10, .K12⟩ nO hq).trans
    (H2K.Sizes.nums_O_of_full A hN _ nO hO hq
      (rounds_at_seat_O o S.pol S.lay S.KL Z hZ mk N nO hO c hN hp A hW)
      (free_at_seat_O o S.pol S.lay S.KL Z hZ mk N nO hO c hN hp hW))

/-- **Three tests on the plan at the seat of Omega's test, in scope**: every declared opening of the
first switch is a tree of the chain's own with the label that its number gives; no tree of the
test's group is the first fold's own mask's; the chain has sent a root in front of the test. -/
theorem tests_in_scope_O {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles}
    (hS : VerifierAndGoals.InScope S = true) (Z : ProofFile.Pub) (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z)
    (mk : ProofFile.LinksBy) (N : H2U.Places4) (nO : H2U.PlaceNums) (hO : N.O = some nO)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (descN o mk guardedProximityTestParts Z N c) = true) :
    VerifiableInference.Desc.K12.Coin.ownLabelsB (pGomega nO) = true ∧
      H2K.Made.firstNe (pGomega nO) = true ∧ 0 < (pGomega nO).nums.free := by
  have hn := nums_in_scope_O hS Z hZ mk N nO hO c hN hp hpin
  have hq := plan_at_seat_O o Z mk N nO hO c hp
  have hc := VerifiableInference.Desc.K12.Coin.At.closed_OFull.plan
  refine ⟨?_, ?_, ?_⟩
  · exact (H2K.Sizes.ownLabelsB_reads hq hc (by rw [hn])
      (H2K.Sizes.rdsAt_reads hq hc (by rw [hn])) (by rw [hn])).trans
      VerifiableInference.Desc.K12.Coin.oFull_ownLabels
  · exact (H2K.Sizes.firstNe_reads (by rw [hn]) (by rw [hn])).trans H2K.Sizes.firstNe_OFull
  · rw [hn]
    decide

end H2K.JointK

#print axioms H2K.JointK.closedL_in_scope_U
#print axioms H2K.JointK.closedL_in_scope_O
#print axioms H2K.JointK.closedL_in_scope_W
#print axioms H2K.JointK.gameV_in_scope_U
#print axioms H2K.JointK.game_in_scope_U
#print axioms H2K.JointK.gameOwn_in_scope_O
#print axioms H2K.JointK.game_in_scope_W
#print axioms H2K.JointK.numbers_in_scope_U
#print axioms H2K.JointK.numbers_in_scope_O
#print axioms H2K.JointK.numbers_in_scope_W
#print axioms H2K.JointK.nums_in_scope_U
#print axioms H2K.JointK.nums_in_scope_O
#print axioms H2K.JointK.tests_in_scope_O
