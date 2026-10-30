-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.ClosedAtSeats
import Johnson.Loose.H2K12.SitsAtDescPure
import Johnson.Desc.K12.Coin.LawAtTile
import Johnson.Desc.K12.Coin.Alike
import Johnson.Desc.K12.Law.OpensOwn
/-
Johnson/Loose/H2K12/TileAtGu.lean: THE TILE AT G_u's SEAT (⟨2, none, 9, .K12⟩) OF THE PROOF FILE's
SEATED DESCRIPTION, IN SCOPE: ProofFile.onlineDescription o S.pol S.lay S.KL's return F (= descN o
ProofFile.pureRoad.links guardedProximityTestParts Z N c: SitsAtDescPure.lean: k12_sits): AtPlace AT THE FILE's OWN
FRAME · BASE · DATA, at errors made off the plan over the file's own stretch. An assembly: ONE CALL
of Coin/LawAtTile.lean's atPlace_tile₂ (general in the description) at D := writtenPFull, π := pGu
N,
r := rUFull, k := 128. Who pays its premises: F.data's yes and the written lists:
seat_in_scope (Johnson/Goal/Numbers/PlanWrittenDescScope.lean) · the flat list's cut: descN_shared ·
the entry's rounds: guEntry_sits · «free»: plain_free · the block's test on the plan, ClosedL's
chain
and Johnson test, ownMask: ClosedAtSeats.lean · that the blocks in front declare 8 rounds:
stretch_at_U at the kernel's line bat_UFull. NO SOUNDNESS
IS CLAIMED. NOTHING ON HIDING. NO NEW MATHEMATICS.
  guEntry_alike | omegaEntry_alike     the entry at a seat on the shared chain is alike
      (Coin/Alike.lean:
      name · rounds · DECISION) to the seat itself: retype and asBare alone stand between.
  shared_behind · descN_shared_cons     G_u's seat is not the chain's last block; the flat list's
      own
      cons form: for the piece's number in the file's second row.
  atPlace_tile₂_at     atPlace_tile₂ with the number of rounds in front under a letter: general in
      the description.
  tile_at_descN · tile_at_Gu
  ho_at_Gu             the tile's data open no tree of the first chain (Law/OpensOwn.lean's
      opens_own_stretch at the written data).
WHAT IT IS NOT: IT IS THE LAW's PREMISES AT THE TILE (AtPlace and the two comparisons: TileAt), AT
THE SEAT: NO PIECE, NO LAW, NO GAME AND NO piecesAt STAND IN IT: left to other files, over
Coin/LawAtTile.lean · hp (F.planOk) AND hpin (seatPinnedProof) ARE PREMISES: what the
SEATED VALUE's door asks behind onlineDescription's return · key and ft are letters here: the file's own tile
is at D.key₂ and 0 · the first arm alone (ownMask = false) · π stays pGu N, not the closed place.
-/
set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Coin (TileAt)
open H2K.Member (rUFull)
open Johnson.G (writtenPFull)
open scoped ENNReal

/-- The entry at G_u's seat is alike to the seat itself. -/
theorem guEntry_alike (Cl' : Type) (N : H2U.Places4) :
    Coin.Alike ((proximityTestKind guardedProximityTestParts (pGu N) : Blk').inside (Seat.enter (·.gU) (·.firstMask)) Seat.leave)
      (guEntry Cl' N) :=
  (Coin.alike_retype _).trans (Coin.alike_plan _ _)

/-- The entry at G_omega's seat is alike to the seat itself. -/
theorem omegaEntry_alike (Cl' : Type) (nO : H2U.PlaceNums) :
    Coin.Alike
      ((proximityTestKind guardedProximityTestParts (pGomega nO) : Blk').inside (Seat.enter (·.gOmega) fun _ => none) Seat.leave)
      (omegaEntry Cl' nO) :=
  (Coin.alike_retype _).trans (Coin.alike_plan _ _)

/-- G_u's seat is not the shared chain's last block. -/
theorem shared_behind (Cl' : Type) (P : _root_.Desc.K14.P14) (N : H2U.Places4) :
    ∃ b' post', (N.O.toList.map fun nO => omegaEntry Cl' nO) ++ [sharedEnd Cl' P N] =
      b' :: post' := by
  cases N.O with
  | none => exact ⟨_, _, rfl⟩
  | some nO => exact ⟨_, _, rfl⟩

/-- The shared chain's flat list in its own cons form, cut at G_u's seat with a block behind. -/
theorem descN_shared_cons (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (X : Parts T12) (Z : ProofFile.Pub)
    (N : H2U.Places4) (c : Chain First.S ProofFile.Cl) :
    ∃ b₂ l₂ b' post', (descN o mk X Z N c).shared.blocksInOrder = b₂ :: l₂ ∧
      b₂ :: l₂ = sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ guEntry ProofFile.Cl N :: b' :: post' := by
  obtain ⟨b', post', e⟩ := shared_behind ProofFile.Cl (p14N Z N) N
  refine ⟨((_root_.Desc.K14.chainOf Z.p.chains (p14N Z N) (Seat.tests N) Seat.last).retype
      (Cl' := ProofFile.Cl)).first.asBare,
    ((_root_.Desc.K14.blocksOr (p14N Z N)).map fun b => (b.retype (Cl' := ProofFile.Cl)).asBare) ++
      guEntry ProofFile.Cl N :: b' :: post', b', post', ?_, rfl⟩
  rw [descN_shared o mk X Z N c, e]
  rfl

/-- Coin/LawAtTile.lean's atPlace_tile₂ with the number of rounds that the blocks in front declare
under a letter n: general in the description. (So that a caller who holds that number at the
description's own unfolded types can hand it over.) -/
theorem atPlace_tile₂_at {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D) (key : ℕ → ℕ) (ft : ℕ) (π : P12) (r : Fmt.M1.Stage → ℕ) (k : ℕ)
    (pre : List (Block F.S₂ F.Cl)) (B : Block F.S₂ F.Cl) (post : List (Block F.S₂ F.Cl))
    (hfl : F.shared.blocksInOrder = pre ++ B :: post)
    (hB : B.rounds = (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds)
    (hfree : π.nums.free = Johnson.G.OfPlan.rootsOf (pre.flatMap (·.rounds)))
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hC : Coin.ChainAt π r ((2 : ℝ≥0∞)⁻¹ ^ k)) (hj : H2K.Pub.johOk π r = true)
    (hbat : H2K.Pub.batPriceOk π r k = true) (ho : π.nums.ownMask = false) (n : ℕ)
    (hn : (pre.flatMap (·.rounds)).length = n) :
    ∃ dB dt, (D.ds₂.drop n).take (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length = dB :: dt ∧
      TileAt (frameAt D (allOf D) key ft) π (numAt F.t₁ F.t₂ 1) r ((2 : ℝ≥0∞)⁻¹ ^ k)
        (D.t₁ + nTrees (D.ds₂.take n)) dB dt := by
  subst hn
  exact Coin.atPlace_tile₂ F file D h key ft π r k pre B post hfl hB hfree hp hC hj hbat ho

/-- The tile at G_u's seat of descN, in scope. -/
theorem tile_at_descN (o : ProofFile.SecondHashFunctionArgument) (S : VerifierAndGoals.PublicFiles) (hS : VerifierAndGoals.InScope S = true)
    (Z : ProofFile.Pub) (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z) (mk : ProofFile.LinksBy)
    (N : H2U.Places4) (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (descN o mk guardedProximityTestParts Z N c) = true) (key : ℕ → ℕ) (ft : ℕ) :
    ∃ dB dt,
      (writtenPFull.ds₂.drop 8).take (proximityTestKind guardedProximityTestParts (pGu N) : Blk').rounds.length =
        dB :: dt ∧
      TileAt (frameAt writtenPFull (allOf writtenPFull) key ft)
        (pGu N) (numAt (descN o mk guardedProximityTestParts Z N c).t₁ (descN o mk guardedProximityTestParts Z N c).t₂ 1) rUFull
        ((2 : ℝ≥0∞)⁻¹ ^ 128)
        (writtenPFull.t₁ + nTrees (writtenPFull.ds₂.take 8))
        dB dt := by
  obtain ⟨hW, _, hD⟩ := VerifiableInference.PlanWritten.seat_in_scope _ _ S hS hpin
  have hC := (closedL_in_scope_U hS Z hZ mk N c hN hp hpin).1
  have hl := (stretch_at_U o S.pol S.lay S.KL Z hZ mk N c hN hp _ hW 8
    H2K.Member.bat_UFull).2.2.1
  have hfree : (pGu N).nums.free = Johnson.G.OfPlan.rootsOf
      ((sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N).flatMap (·.rounds)) :=
    (congrArg (·.free) (H2K.Made.nums_of_planOk ⟨2, none, 9, .K12⟩ N.U hC.plan)).trans
      (plain_free o S.pol S.lay S.KL Z hZ mk N c hN hp).1.2
  exact atPlace_tile₂_at (descN o mk guardedProximityTestParts Z N c) "proof file" _ hD key ft (pGu N) rUFull
    128 _ _ _ (descN_shared o mk guardedProximityTestParts Z N c) (guEntry_sits ProofFile.Cl N).rounds
    hfree hC.plan hC.chain hC.joh hC.bat (ownMask_in_scope_U hS Z hZ mk N c hN hp) 8 hl

/-- THE TILE AT G_u's SEAT OF THE SEATED DESCRIPTION, IN SCOPE. -/
theorem tile_at_Gu (o : ProofFile.SecondHashFunctionArgument) (S : VerifierAndGoals.PublicFiles) (hS : VerifierAndGoals.InScope S = true)
    (F : FileDescription ProofFile.Inst) (hF : ProofFile.onlineDescription o S.pol S.lay S.KL = .ok F)
    (hp : F.planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol F = true) (key : ℕ → ℕ)
    (ft : ℕ) :
    ∃ (Z : ProofFile.Pub) (N : H2U.Places4) (c : Chain First.S ProofFile.Cl) (dB : RDT) (dt : List RDT),
      ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z ∧ H2U.placesOfMade Z.made = .ok N ∧
      F = descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c ∧
      (writtenPFull.ds₂.drop 8).take (proximityTestKind guardedProximityTestParts (pGu N) : Blk').rounds.length =
        dB :: dt ∧
      TileAt (frameAt writtenPFull (allOf writtenPFull) key ft)
        (pGu N) (numAt F.t₁ F.t₂ 1) rUFull ((2 : ℝ≥0∞)⁻¹ ^ 128)
        (writtenPFull.t₁ + nTrees (writtenPFull.ds₂.take 8))
        dB dt := by
  obtain ⟨Z, N, c, _, hZ, hN, rfl, _⟩ := k12_sits o S.pol S.lay S.KL F hF
  obtain ⟨dB, dt, h1, h2⟩ := tile_at_descN o S hS Z hZ ProofFile.pureRoad.links N c hN hp hpin key ft
  exact ⟨Z, N, c, dB, dt, hZ, hN, rfl, h1, h2⟩

/-- The tile's data open no tree of the first chain: what leadsK_of_lift | liftHands
ask
under the name ho, at lo := writtenPFull.t₁, at the very stretch of tile_at_Gu. Of any description
that passes the pin in scope: no onlineDescription and no test on the plan is asked. -/
theorem ho_at_Gu (S : VerifierAndGoals.PublicFiles) (hS : VerifierAndGoals.InScope S = true) {Xi : Type} (F : FileDescription Xi)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol F = true) (n : ℕ) :
    ∀ d ∈ (writtenPFull.ds₂.drop 8).take n, ∀ j ∈ d.opens, writtenPFull.t₁ ≤ j :=
  opens_own_stretch F "proof file" writtenPFull
    (VerifiableInference.PlanWritten.seat_in_scope _ _ S hS hpin).2.2 8 n

end H2K.JointK

#print axioms H2K.JointK.ho_at_Gu
#print axioms H2K.JointK.guEntry_alike
#print axioms H2K.JointK.omegaEntry_alike
#print axioms H2K.JointK.descN_shared_cons
#print axioms H2K.JointK.tile_at_descN
#print axioms H2K.JointK.tile_at_Gu
