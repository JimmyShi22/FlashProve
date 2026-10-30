-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/T3/TheOneOfSides.lean: ZERO KNOWLEDGE ON SERVED REQUESTS AT ANY SIDES WHOSE PROVER IS THE RETURN'S: AN IMPLICATION.

1.  The head's three equations follow from that; the fields input and hst of RowDebtsP are theorems at the base. The
    number 2^-174 comes from window_at_term.
2.  Read it beside completeness, at the same return and the same rows G. On is asked only at parts that a run has
    called, and Good at letters that never hold, so a prover whose early block is always refused would meet all
    later rows with nothing shown. Completeness at the same G is what rules that out; this file does not show it.
3.  _start and _whole are guards: no proof in this file uses them.
4.  The premises are listed in the statement: the head, its tests, one ready input, and the kinds' three shares as
    RowDebtsP has them. This file proves zero knowledge of nothing.
-/
import AtFullSide.T3.TheOneAtWindow
import AtFullSide.T3.HstAtBase

set_option autoImplicit false
set_option maxRecDepth 100000
attribute [-instance] Inst.Model.Scl.ref
noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open Iop Prob AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.AtFiles AtPublicFiles.Committed AtPublicFiles.Cut
open AtPublicFiles.AtFiles.HonestTerm
open ProofFile.Honest (Sides Owed relAt AtHonest OnlineProverWithDescription Cells BudDebts ThreadsP OnAtRun₁ OnAtRun₂ OnAtRun₃
  silentAt runC ready onlineProverFromPublicFiles frameAsks)
open VerifiableInference.Desc (Chain)
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD)
open LPFD.Full (instanceAsPlainRecord XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (protocolDataWellFormed committerCoinCountLessOne)
open P5J

local instance (priority := high) oneSidesPad : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) oneSidesValue : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) oneSidesDefault : Inhabited RunValue := ⟨fun _ => 0⟩

variable {files : PublicFiles}

/-- **Zero knowledge on served requests at any sides whose prover is the return's**: an implication. -/
theorem zeroKnowledgeOnServedRequests_ofSides
    (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp) {D : WholeD} {r : LPFD.Full.RunPF}
    {x : VerifiableInference.Desc.First.Look.Place}
    {A : OnlineProverWithDescription FullSizeMatrix ProofFile.Honest.IndexCommitterCoins Cells Unit Unit} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    {G : Sides A.F A.B FullSizeMatrix ProofFile.Honest.IndexCommitterCoins TableKey Cells Unit Unit} {more : List (String × Bool)}
    (hP : G.prover A.H = A.H)
    (head : AtMgA OnBytes.secondHashFunction files D r A.Z Np cF x)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFilling = .ok A)
    (asks : ∀ t ∈ frameAsks A G ++ (baseAsks A ++ more), t.2 = true)
    (one : ∃ w₀ rc ξ k R, ready A.F A.B A.H w₀ rc ξ k = .ok R)
    (kinds : ∀ κ, KindPays G κ) (hbud : BudDebts A.F A.B G)
    (threads : ∀ w₀ rc ξ, BaseRel files hr w₀ rc ξ → ∀ k R,
      ready A.F A.B (G.prover A.H) w₀ rc ξ k = .ok R →
      ∃ T : ThreadsP A.F A.B (G.prover A.H) w₀ rc ξ k R, ∀ ρ run, ρ.due A.F = true →
        silentAt A.F (G.prover A.H) w₀ rc ξ ρ = none →
        runC A.F A.B (G.prover A.H) w₀ rc ξ k ρ = .ok run →
        (∀ L ∈ G.first, OnAtRun₁ (G := G) (H := A.H) T ρ run L) ∧
        (∀ L ∈ G.shared, OnAtRun₂ (G := G) (H := A.H) T ρ run L) ∧
        ∀ L ∈ G.second, OnAtRun₃ (G := G) (H := A.H) T ρ run L)
    (_start : ∃ z₀, A.F.okStart (instanceAsPlainRecord z₀) = true)
    (parts : Parts files) (_whole : OfflineSidesAreWhole parts) :
    ∃ d : OfflineDescription, offlineDescription files = .ok d ∧
      ∀ (GK : Sides (keyFileDescription d.source d.numbers d.later) parts.book (Cz files).I
          ((Cz files).Pad × (Cz files).Rnd) TableKey Unit parts.SharedState parts.OwnState)
        (_ : IsProvK files (keyFileDescription d.source d.numbers d.later) parts.book GK (parts.prover d))
        (_ : Owed (keyFileDescription d.source d.numbers d.later) parts.book
          ((cmKey files).proverAt 0 (parts.prover d)) GK.mute
          (relAt (ansAt (AZ files) PadZ (holdZ files)) (fun i _ => inRange i) wrK))
        (_ : GK.owns = true),
        ZeroKnowledgeOnServedRequests files hr (HonestProvers.ofThreeProvers (honestProvers files parts)) 0 0
          (ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ))) :=
  have hd : AtHonest OnBytes.secondHashFunction files D r A.Z Np cF x baseFilling A G (baseAsks A ++ more) :=
    ⟨head, made, (congrArg (·.first) hP).symm, (congrArg (·.shared) hP).symm,
      (congrArg (·.second) hP).symm, asks, one⟩
  zeroKnowledgeOnServedRequests_atTheWindow scope live hr hd
    ⟨kinds, input_at_base_whole files scope live hr hd, hst_at_base files scope live hr hd, hbud,
      threads⟩ _start parts _whole

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.zeroKnowledgeOnServedRequests_ofSides
