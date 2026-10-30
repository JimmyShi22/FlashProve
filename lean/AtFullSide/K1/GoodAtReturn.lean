-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/GoodAtReturn.lean: the shared "sending" (the kind K1): AT WHAT THE MAKER onlineProverFromPublicFiles RETURNS, AT
ANY FILLING, AT ITS OWN BOOK AND ORDER OF PLACES: Good (fits, exact, fresh) AT ALL 52 ROWS of lotS and
wS (Johnson/Desc/ProofFile/Honest/K1/Sim/AtFill.lean), with no premise on the book left. The index's and
the randomness's types, the filling, the readers g and rd, the sizes and the open functions are letters:
so the theorems serve at the base filling and at the filling read through alike. Three theorems; no
definition.

  clear_all           the premise on the book at each of the 52 jobs
  good_all_at_return  Good at each of the 52 rows, at every face and every pre₀, at A.B, orderOf A.F
  owner_fresh_at_return   FOR THE HOUSES WHOSE PARTS SPEND A COIN OF A K1 SENDER: the field fresh at one
                      address p (FreshAtP, Johnson/SendSim/At/Fresh.lean) at each of the 52 rows' sides

By what. handIn_at_return (AtFill.lean); clear_but_opening (BookAtWClear.lean); clear_at_opening
(BookAtOpening.lean); freshAtLots_of_spenders (Johnson/SendSim/Seat/AtDescLotsSpenders.lean).

Limits. Good is had at predicates A₁, B₁ that never hold: plays and acc are met for nothing; fits, exact
and fresh alone speak. fresh has content at two rows, the opening's and W's; at the fifty nobody spends
a coin of the sender. exact and fresh speak of one sender at a time. The first chain alone: the kind's
two sendings on the shared chain, five in the key file's description and one in a copy's are not here.
One request. The order is the returned description's own. All limits of the files named. No property of
the protocol is claimed.
-/
import AtFullSide.K1.BookAtWClear
import AtFullSide.K1.BookAtOpening

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K1
open VerifiableInference.Desc
open ProofFile (Inst Pub Ground)
open ProofFile.Honest ProofFile.Honest.K1 ProofFile.Honest.K1.Sim
open OnBytes.SendSim.At OnBytes.SendSim.Seat

/-- **THE PREMISE ON THE BOOK AT EACH OF THE 52 JOBS**, at the book and the order of what the maker
returns, at any filling. -/
theorem clear_all {W₀ Rc Tr X₀ X : Type} {Z : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope Z = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    ∀ J ∈ k1Jobs OnBytes.secondHashFunction S O A.Z A.G,
      SpendersClearAny J.P J.ride A.B (orderOf A.F) ⟨J.P.place, 0⟩ := by
  intro J hJ
  by_cases hne : J.P.place = ⟨1, some 0, 1, .K1⟩
  swap
  · exact clear_but_opening hS hL S O hA _ J hJ hne
  rcases List.mem_append.1 hJ with hJ' | hJ'
  · have hc : J ∈ placeJob (X := Unit) (K1.firstPar A.G.first (K1.gpOf A.Z))
        (lotNo OnBytes.secondHashFunction A.Z ⟨1, some 0, 1, .K1⟩) (firstFold A.G.first) (lotData S A.Z A.G) ::
        (lotJobs (X := Unit) (lotNo OnBytes.secondHashFunction A.Z) (lotData S) A.Z A.G).tail := hJ'
    rcases List.mem_cons.1 hc with rfl | ht
    · exact spendersClearAny_of_bookClearAny (clear_at_opening hS hL hA)
    · exact absurd hne (later_place OnBytes.secondHashFunction S A.Z A.G ht).2.2
  · exact clear_at_w hS hL _ hA _ J hJ'

variable {W₀ W₀' Rc' : Type}

/-- **GOOD AT ALL 52 ROWS, AT THE MAKER's OWN BOOK AND ORDER; NO PREMISE ON THE BOOK IS LEFT.** -/
theorem good_all_at_return {pre₀ : List (Nat × Nat × List Fmt.DeclaredRound)} {Z : VerifierAndGoals.PublicFiles}
    (hS : VerifierAndGoals.InScope Z = true) (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (I : WiderIn W₀) (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {P : OnlineProverParts W₀' Rc' Cells Unit Unit} {A : OnlineProverWithDescription W₀' Rc' Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (φ : Face (Local W₀' Rc' Inst Cells) (Local W₀' Rc' Inst Cells) Inst) (chain ft : Nat)
    (T : Local W₀' Rc' Inst Cells → Thread A.B A.F.S₁ A.F.Cl (Local W₀' Rc' Inst Cells)
      (Local W₀' Rc' Inst Cells) Unit Inst)
    (Sd : Local W₀' Rc' Inst Cells → Nat → Coins A.B → Mid (Local W₀' Rc' Inst Cells) Unit → Prop)
    (fs : List (Fall A.F.S₁)) :
    ∀ r ∈ rowsOfLots A.Z A.G [lotS I g rd OnBytes.secondHashFunction S, wS I g rd OnBytes.secondHashFunction O],
      ∀ σ, (r.lay T Sd A.F.first.blocksInOrder).side A.F.first.blocksInOrder fs = some σ →
        ∃ A₁ B₁, Good pre₀ φ σ A.B (orderOf A.F) chain ft A₁ B₁ (r.lay T Sd A.F.first.blocksInOrder).On
          (r.lay T Sd A.F.first.blocksInOrder).bud := by
  intro r hr
  rw [rows_eq] at hr
  obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hr
  exact (handIn_at_return (pre₀ := pre₀) hS hL I g rd S O hA φ A.B (orderOf A.F) chain ft T Sd fs J hJ
    _ rfl).2.2.1 (clear_all hS hL S O hA J hJ)

/-- **THE OWNER's fresh AT ONE ADDRESS p**, at each of the 52 rows' sides: over the sender's own coins
the blocks that p spends are uniform and independent of what the sender shows together with what is
known at p. Asked at challenges that the sender's rounds can draw and at positions within budAt. -/
theorem owner_fresh_at_return {Z : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope Z = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) (I : WiderIn W₀) (g : W₀' → W₀)
    (rd : Rc' → IndexCommitterCoins) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {P : OnlineProverParts W₀' Rc' Cells Unit Unit} {A : OnlineProverWithDescription W₀' Rc' Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (φ : Face (Local W₀' Rc' Inst Cells) (Local W₀' Rc' Inst Cells) Inst)
    (fs : List (Fall A.F.S₁)) (p : Addr) :
    ∀ J ∈ k1Jobs OnBytes.secondHashFunction S O A.Z A.G,
      ∀ σ : Side A.F.S₁ A.F.Cl (Local W₀' Rc' Inst Cells) (Local W₀' Rc' Inst Cells) Unit Inst,
      Side.seated A.F.first.blocksInOrder (jobRow (V := Local W₀' Rc' Inst Cells) (Pb := Inst)
                   (witAt I g rd A.Z) J).place (jobRow (V := Local W₀' Rc' Inst Cells) (Pb := Inst)
                   (witAt I g rd A.Z) J).row fs = some σ →
      FreshAtP φ σ A.B (orderOf A.F) (fun _ _ asks => budAt J.P asks) p := by
  intro J hJ σ hσ
  have hB := clear_all hS hL S O hA J hJ
  obtain ⟨Bs, base, c, S₂, S₃, Op, hG⟩ := open_at hA
  rw [← hG] at hJ
  obtain ⟨D, hD⟩ := job_mem hJ
  have hF := freshAtLots_of_spenders Op φ (witAt I g rd A.Z) (lotNo OnBytes.secondHashFunction A.Z) D hD hσ A.B
    (orderOf A.F) hB
  exact fun u hu sp ca m ds asks => hF u hu p sp ca m ds asks

end AtFullSide.K1

#print axioms AtFullSide.K1.clear_all
#print axioms AtFullSide.K1.good_all_at_return
#print axioms AtFullSide.K1.owner_fresh_at_return
