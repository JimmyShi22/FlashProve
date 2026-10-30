-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/PaysLast.lean: the last chain pays. Under the library's head, where onlineProverFromPublicFiles returns at
onlineProverPartsInUse I (K1/Law/WSideAtFill.lean), at any index type, the last chain's one side, the
pair of the request's own proximity test behind the guard, fits at onlineProverFromPublicFiles's book and description.

  realW_numbers        the job's parameters are the planner's record
  pairW_fits           the pair secondW fits, at the book and description of any filling
  lastTest_fits        every side of the prover's last chain fits
  lastChain_pays       every side of it pays: the field pays₃ of ReadyDebts

By what. secondW_letters (K12/AtProof/WMemberSent.lean): the pair is halfW; ground_at_head (AtFullSide/K12/GroundAtHeadW.lean): that ground is the
opening's, at which realW_public (AtFullSide/K12/HalfAtHeadW.lean) stands; fourW_written; lays_W_at
(AtFullSide/K12/LaysLastTest.lean).

Limits.
- Conditional on the head, and on onlineProverFromPublicFiles's return (hA), which atPure_returns_fillW_at pays.
- The index type, the filling's reader and its open functions are free: the statement reads the
  job's public fields alone. o is the format's second hash function.
- Where realW is none the last chain has no side and the law says nothing. Under the head it has
  one: second_made (AtFullSide/K12/SecondMadeW.lean), at any index type.
- What it says is that chainSteps returns at this side. Behind the guard the pair's moves err where
  no columns are handed: that a round is played is not said.
- The filling is the one that the honest prover's term is to read through. Nothing here is read
  through: SideFits.thru (PaysThrough.lean) carries it.
- Nothing on completeness, soundness or hiding.
-/
import AtFullSide.K12.PaysAtHead
import AtFullSide.K12.PaysRoundsW
import AtFullSide.K12.HalfAtHeadW
import AtFullSide.K12.GroundAtHeadW
import AtFullSide.K12.SecondMadeW

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12
open VerifiableInference.Desc (Chain FileDescription)
open VerifiableInference.Desc.K12 (T12)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open H2K.Member (piWFull)
open P5J (AtMg AtMgA TS)
open AtFullSide.K14 (bookWhole_returns_written_ahead)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **The job at the last chain's test has the planner's record as its parameters.** -/
theorem realW_numbers {W₀ Rc Xi Tr X : Type} (h : AtMg o Z D r Zp Np cF)
    (S : OnBytes.HonestTrace.Sz) (Fd : FileDescription Xi) (enter : Fd.S₃ → Except String T12)
    (pile : ProofFile.Pub → ProofFile.Ground → K13.PileOf Xi) (no : VerifiableInference.Desc.Place → Nat)
    (readers : Local W₀ Rc Xi Tr → Readers) (weights : Local W₀ Rc Xi Tr → Weights)
    (rand : Desc.K14.P14 → Local W₀ Rc Xi Tr → TableRand) (G : ProofFile.Ground)
    {J : TestJob (Local W₀ Rc Xi Tr) X}
    (hJ : realW S Fd enter pile no readers weights rand Zp G = some J) :
    J.p = (fourOf Np).W := by
  unfold realW jobRealW at hJ
  obtain ⟨M, hM, rfl⟩ := Option.map_eq_some_iff.1 hJ
  obtain ⟨F, hF, hM⟩ := Option.bind_eq_some_iff.1 hM
  obtain ⟨A, -, hM⟩ := Option.bind_eq_some_iff.1 hM
  obtain ⟨msg, -, rfl⟩ := Option.map_eq_some_iff.1 hM
  obtain rfl : F = fourOf Np :=
    Option.some.inj (hF.symm.trans (ProofFile.Honest.K12.Light.stages_at_head h).1)
  rfl

/-- **The pair secondW fits**, at the book, the description and the ground of any filling. -/
theorem pairW_fits {W₀ W₁ Rc Tr X₀ X : Type} {P : OnlineProverParts W₁ Rc Tr X₀ X} {A : OnlineProverWithDescription W₁ Rc Tr X₀ X}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    ∀ g ∈ (secondW I OnBytes.secondHashFunction S O Zp A.G : List (Placed _ _ Unit)),
      SideFits A.B 2 A.F.second.blocksInOrder g := by
  obtain ⟨Bs, base, Op⟩ := h.laid.opened
  have h6 := ProofFile.Honest.K14.nowSharedBy_at_head h (I.weights Zp)
  have hG := ground_at_head h.laid Op hA
  intro g hg
  rw [secondW_letters I OnBytes.secondHashFunction S O A.G h6 h.laid.places h.laid.chain, hG] at hg
  obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hg
  have hJ' := Option.mem_toList.1 hJ
  obtain ⟨-, hm, hf, -⟩ := realW_public h Op S _ _ _ _ _ _ _ hJ'
  have hp : J.p = ({ piWFull with place := placeW } : VerifiableInference.Desc.K12.P12) :=
    (realW_numbers h.toAtMg S _ _ _ _ _ _ _ _ hJ').trans (fourW_written h.toAtMg)
  obtain ⟨B₀, h₀, -⟩ := bookWhole_returns_written_ahead
  have hl : laysLastB A.B J = true := by
    rw [book_of_atPure h hA h₀]
    exact lays_W_at h₀ J hp hm hf
  obtain ⟨-, -, sh3⟩ := planOk_all (atPure_planOk h.laid hA)
  exact SideFits.guarded (fits_at_numbers_last A.B J _ hp two_stages_W hl
    (fun b hb => (shaped_parts (sh3 b hb).2).1)
    (rounds_of_alike (alike_at_atPure h hA).second rounds_at_W))

variable {W₀ : Type} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **Every side of the prover's last chain fits**, at onlineProverFromPublicFiles's book and description. -/
theorem lastTest_fits (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    ∀ g ∈ A.H.second, SideFits A.B 2 A.F.second.blocksInOrder g := by
  have hZ := (atPure_at_laid h.laid hA).1
  obtain ⟨-, -, -, -, -, -, -, -, -, e3, -⟩ := atPure_ok hA
  intro g hg
  rw [e3, hZ] at hg
  exact pairW_fits h I S O hA g hg

/-- **The last chain pays**: the field pays₃ of ReadyDebts. -/
theorem lastChain_pays (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A)
    (κ : VerifiableInference.Desc.KindName) : KindPays A.B 2 A.F.second.blocksInOrder A.H.second κ :=
  fun g hg _ => sidePays_of_fits (lastTest_fits h I S O hA g hg)

end AtFullSide.K12

#print axioms AtFullSide.K12.realW_numbers
#print axioms AtFullSide.K12.pairW_fits
#print axioms AtFullSide.K12.lastTest_fits
#print axioms AtFullSide.K12.lastChain_pays
