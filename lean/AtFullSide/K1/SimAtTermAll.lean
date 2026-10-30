-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/SimAtTermAll.lean: the shared "sending" (the kind K1): ALL THAT THE KIND's HOUSE HANDS IN FOR
ITS 52 ROWS ON THE FIRST CHAIN, UNDER ONE NAME, AT THE TWO VALUES THAT THE HOUSES READ: the return of
baseMaker (the maker at the base filling baseFilling, E2E/BaseMaker.lean) and the return of onlineMaker
(E2E/TheHonestProver.lean). Instances of the laws at
letters. No definition; five theorems.

  base_returns     in scope, where the gate accepts, baseMaker returns
  k1_sim_at_base   THE BUNDLE at every return of baseMaker, the two values standing at g := id, rd := id:
                   (1) the prover's sides at places of the kind K1, in order, are our rows' halves
                   (2) there are 52 rows (3) at 52 places (4) every job fits its place
                   (5) job by job: a member is at the row's place · every side has fits and exact · every
                   side has Good for some A₁, B₁ at .own, A.B, orderOf A.F, 0, 0, NO PREMISE ON THE BOOK
                   LEFT · bud holds at every due list of challenges · On follows from every thread
                   (6) no row ever stops (7) the owner's fresh at every address p
  k1_shows_at_base at every coin the sender shows something and its simulator tells something
  k1_good_all_base, k1_good_all   Good at each of the 52 rows, row by row, at the base and at the term

Limits. Good is had at predicates A₁, B₁ that never hold: plays and acc are met for nothing; fits, exact
and fresh alone speak. fresh has content at two rows, the opening's and W's. exact and fresh speak of one
sender at a time, at challenges that its rounds can draw and at positions within budAt. The first chain
alone: the kind's two sendings on the shared chain, those in the key file's description and in a copy's
are not here. One request. All limits of the files named. No property of the protocol is claimed.
-/
import AtFullSide.K1.SimAtTermBook
import AtFullSide.K1.GoodAtReturn
import Johnson.Desc.ProofFile.Honest.K1.Sim.HalvesAtReturn
import Johnson.Desc.ProofFile.Honest.K1.Sim.ShowsAtReturn
import E2E.BaseMaker

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K1
open VerifiableInference.Desc
open ProofFile (Inst)
open ProofFile.Honest ProofFile.Honest.K1 ProofFile.Honest.K1.Sim
open ProofFile.Honest.Term (matrixInput tableCoins onlineFilling onlineMaker OnlineReturn makerReturns
  range_matrixInput baseFilling baseMaker)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open OnBytes.SendSim.At OnBytes.SendSim.Seat

/-- **The maker returns at the base filling.** -/
theorem base_returns (Z : VerifierAndGoals.PublicFiles) (hS : VerifierAndGoals.InScope Z = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) : ∃ A, baseMaker Z = .ok A := by
  obtain ⟨pp, hR⟩ := H2K.Sizes.inScope_readFiles hS
  obtain ⟨Zp, Np, cF, x, h⟩ := P5J.head_exists_at_name Z hS hR hL (P5J.owed_of_live hL)
  obtain ⟨A, hA, -⟩ := AtFullSide.K12.atPure_returns_fillW_at h hL matrixInput OnBytes.secondHashFunction
    OnBytes.HonestTrace.Sz.ref openHonest range_matrixInput
  exact ⟨A, hA⟩

/-- **K1's 52 ROWS AT THE BASE: THE BUNDLE.** -/
theorem k1_sim_at_base {pre₀ : List (Nat × Nat × List Fmt.DeclaredRound)} (Z : VerifierAndGoals.PublicFiles)
    (hS : VerifierAndGoals.InScope Z = true) (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (hA : baseMaker Z = .ok A) :
    ((A.H.first.filter fun x => x.place.kind == .K1) =
      (rowsOfLots A.Z A.G [lotS matrixInput id id OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref,
        wS matrixInput id id OnBytes.secondHashFunction openHonest]).map (·.half)) ∧
    (rowsOfLots A.Z A.G [lotS matrixInput id id OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref,
      wS matrixInput id id OnBytes.secondHashFunction openHonest]).length = 52 ∧
    ((rowsOfLots A.Z A.G [lotS matrixInput id id OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref,
      wS matrixInput id id OnBytes.secondHashFunction openHonest]).map (·.place)).Nodup ∧
    (∀ J ∈ k1Jobs OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest A.Z A.G,
      sendFits J.P J.ride = true) ∧
    (∀ (T : Local FullSizeMatrix IndexCommitterCoins Inst Cells → Thread A.B A.F.S₁ A.F.Cl (Local FullSizeMatrix IndexCommitterCoins Inst Cells)
        (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit Inst)
      (Sd : Local FullSizeMatrix IndexCommitterCoins Inst Cells → Nat → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit → Prop)
      (fs : List (Fall A.F.S₁)),
      ∀ J ∈ k1Jobs OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest A.Z A.G,
      ∀ r : Unlettered (Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit Inst,
      r = jobRow (witAt matrixInput id id A.Z) J →
      A.F.first.blocksInOrder.any (fun b => b.place == r.place) = true ∧
      (∀ σ, (r.lay T Sd A.F.first.blocksInOrder).side A.F.first.blocksInOrder fs = some σ →
        σ.fits = true ∧ ExactAt .own σ 0 0 r.On r.bud) ∧
      (∀ σ, (r.lay T Sd A.F.first.blocksInOrder).side A.F.first.blocksInOrder fs = some σ →
        ∃ A₁ B₁, Good pre₀ .own σ A.B (orderOf A.F) 0 0 A₁ B₁ (r.lay T Sd A.F.first.blocksInOrder).On
          (r.lay T Sd A.F.first.blocksInOrder).bud) ∧
      (∀ σ, (r.lay T Sd A.F.first.blocksInOrder).side A.F.first.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t n,
        A.F.first.blocksInOrder = pre ++ σ.block :: t →
        n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number →
        ∀ ρ : ProofFile.Honest.Draws, ρ.due A.F = true →
        (r.lay T Sd A.F.first.blocksInOrder).bud u.number ((ρ.first.drop n).take u.rounds.length)
          (asksFrom (treeAsks A.F ρ 0) (u.rounds.map (·.2.length))
            (((rowsOfChain A.F.first.blocksInOrder).take n).map (·.2.length)).sum)) ∧
      ∀ w b len, OnFromS (T w) (Sd w) (r.lay T Sd A.F.first.blocksInOrder) b len) ∧
    (∀ J : SendJob (PlaceIn Inst) Unit,
      ∀ x ∈ (jobRow (V := Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Pb := Inst) (witAt matrixInput id id A.Z) J).row,
        (∀ a b, x.1.bad a b = none) ∧ ∀ a b c, x.1.hid a b c = none) ∧
    ∀ (fs : List (Fall A.F.S₁)) (p : Addr),
      ∀ J ∈ k1Jobs OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest A.Z A.G,
      ∀ σ : Side A.F.S₁ A.F.Cl (Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit Inst,
      Side.seated A.F.first.blocksInOrder (jobRow (V := Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Pb := Inst)
                   (witAt matrixInput id id A.Z) J).place (jobRow (V := Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Pb := Inst)
                   (witAt matrixInput id id A.Z) J).row fs = some σ →
      FreshAtP .own σ A.B (orderOf A.F) (fun _ _ asks => budAt J.P asks) p := by
  obtain ⟨h52, hnd⟩ := rows_52 hS matrixInput id id OnBytes.HonestTrace.Sz.ref openHonest hA
  refine ⟨k1_halves_at_base matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest hA, h52,
    hnd, fits_at_return hL OnBytes.HonestTrace.Sz.ref openHonest hA, fun T Sd fs J hJ r hr => ?_,
    fun J => rows_never_stop _ J, fun fs p =>
      owner_fresh_at_return hS hL matrixInput id id OnBytes.HonestTrace.Sz.ref openHonest hA .own fs p⟩
  have H := handIn_at_return (pre₀ := pre₀) hS hL matrixInput id id OnBytes.HonestTrace.Sz.ref
    openHonest hA .own A.B (orderOf A.F) 0 0 T Sd fs J hJ r hr
  exact ⟨H.1, H.2.1, H.2.2.1 (clear_all hS hL _ _ hA J hJ), H.2.2.2.1, H.2.2.2.2⟩

/-- **AT EVERY COIN THE SENDER SHOWS SOMETHING, AND ITS SIMULATOR TELLS SOMETHING**, at the base. -/
theorem k1_shows_at_base (Z : VerifierAndGoals.PublicFiles) (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (hA : baseMaker Z = .ok A) (fs : List (Fall A.F.S₁)) :
    ∀ J ∈ k1Jobs OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest A.Z A.G,
      ∀ σ : Side A.F.S₁ A.F.Cl (Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit Inst,
      Side.seated A.F.first.blocksInOrder (jobRow (V := Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Pb := Inst)
                   (witAt matrixInput id id A.Z) J).place (jobRow (V := Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Pb := Inst)
                   (witAt matrixInput id id A.Z) J).row fs = some σ →
      σ.members = [memberAt σ (jobOver J (witAt matrixInput id id A.Z))] ∧
      ∀ (m : Mid (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit) (front : Before) (ds : List Fmt.Drawn)
        (asks : List (List (List Nat))) (c : Cs (dueR J.P J.ride)),
        drawsFit σ.block.rounds ds = true →
        σ.shows .own (memberAt σ (jobOver J (witAt matrixInput id id A.Z))) (c, (), ()) m ds asks =
            some (shownR J.P J.first J.ride
              ((jobOver J (witAt matrixInput id id A.Z)).data m.st.input (frontOf m)) ds asks c) ∧
          (memberAt σ (jobOver J (witAt matrixInput id id A.Z))).tells .own c m.st.input front ds asks =
            some (shownR J.P J.first J.ride (fun _ _ _ => none) ds asks c) :=
  shows_some_at_return hL matrixInput id id OnBytes.HonestTrace.Sz.ref openHonest hA .own fs

/-- **GOOD AT ALL 52 ROWS AT THE BASE**, row by row. -/
theorem k1_good_all_base {pre₀ : List (Nat × Nat × List Fmt.DeclaredRound)} (Z : VerifierAndGoals.PublicFiles)
    (hS : VerifierAndGoals.InScope Z = true) (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (hA : baseMaker Z = .ok A)
    (T : Local FullSizeMatrix IndexCommitterCoins Inst Cells → Thread A.B A.F.S₁ A.F.Cl (Local FullSizeMatrix IndexCommitterCoins Inst Cells)
      (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit Inst)
    (Sd : Local FullSizeMatrix IndexCommitterCoins Inst Cells → Nat → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit → Prop)
    (fs : List (Fall A.F.S₁)) :
    ∀ r ∈ rowsOfLots A.Z A.G [lotS matrixInput id id OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref,
        wS matrixInput id id OnBytes.secondHashFunction openHonest],
      ∀ σ, (r.lay T Sd A.F.first.blocksInOrder).side A.F.first.blocksInOrder fs = some σ →
        ∃ A₁ B₁, Good pre₀ .own σ A.B (orderOf A.F) 0 0 A₁ B₁ (r.lay T Sd A.F.first.blocksInOrder).On
          (r.lay T Sd A.F.first.blocksInOrder).bud :=
  good_all_at_return hS hL matrixInput id id OnBytes.HonestTrace.Sz.ref openHonest hA .own 0 0 T Sd fs

/-- **GOOD AT ALL 52 ROWS, AT THE ONLINE PROVER's OWN MAKER, BOOK AND ORDER.** -/
theorem k1_good_all {pre₀ : List (Nat × Nat × List Fmt.DeclaredRound)} (Z : VerifierAndGoals.PublicFiles)
    (hS : VerifierAndGoals.InScope Z = true) (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    {A : OnlineReturn Z} (hA : onlineMaker Z = .ok A)
    (T : Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Inst Cells → Thread A.B A.F.S₁ A.F.Cl
      (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Inst Cells) (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Inst Cells) Unit Inst)
    (Sd : Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Inst Cells → Nat → Coins A.B →
      Mid (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Inst Cells) Unit → Prop) (fs : List (Fall A.F.S₁)) :
    ∀ r ∈ rowsOfLots A.Z A.G [lotS matrixInput id (tableCoins Z) OnBytes.secondHashFunction
        OnBytes.HonestTrace.Sz.ref, wS matrixInput id (tableCoins Z) OnBytes.secondHashFunction openHonest],
      ∀ σ, (r.lay T Sd A.F.first.blocksInOrder).side A.F.first.blocksInOrder fs = some σ →
        ∃ A₁ B₁, Good pre₀ .own σ A.B (orderOf A.F) 0 0 A₁ B₁ (r.lay T Sd A.F.first.blocksInOrder).On
          (r.lay T Sd A.F.first.blocksInOrder).bud :=
  good_all_at_return hS hL matrixInput id (tableCoins Z) OnBytes.HonestTrace.Sz.ref openHonest hA .own
    0 0 T Sd fs

end AtFullSide.K1

#print axioms AtFullSide.K1.base_returns
#print axioms AtFullSide.K1.k1_sim_at_base
#print axioms AtFullSide.K1.k1_shows_at_base
#print axioms AtFullSide.K1.k1_good_all_base
#print axioms AtFullSide.K1.k1_good_all
