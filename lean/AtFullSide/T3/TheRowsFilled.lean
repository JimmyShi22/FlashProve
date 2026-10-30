-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/T3/TheRowsFilled.lean: the premise `shares` of zeroKnowledgeOnServedRequests_atTheG (AtFullSide/T3/TheOneAtTheG.lean), one row for each kind of sub-protocol, filled at the kinds that have a term here, at one G, one T, one K and one Th: so that Lean shows which rows have a term and that the terms fit together.

  `rowsLaid_of_entries`, `zkOnServedRequests_fromRowsAtTheK`   the same at the K of record `theK E apart R`: each membership by its entry's equation
  `zkOnServedRequests_fromRowsAtTheG`   `zeroKnowledgeOnServedRequests_atTheG` with the terms of the kinds named below, each under its membership premise on K, and `rest`: a share at each other kind

A term here, by kind: term · (a) no premise but memberships, at every h, T, Th · (b) each list of the kind is a row of its lot · (c) the lists stand in G, with their number · (d) where the kind spends coins that another kind owns, the kind whose KindPays holds their freshness:
  K2 · `kindShare_k2`, laid as `k2_kind_share` (ShareK2.lean) · (a) scope, live beside · (b) not here · (c) not here · (d) K1 or K2
  K3 · the lookup row and On, laid as `k3_kind_share` (ShareK3.lean) · (a) yes · (b) not here · (c) not here · (d) K1 or K2
  K4 · `k4_kind_share` · (a) yes · (b) not here · (c) not here · (d) K1, K2
  K5 · the attention row, laid as `k5_kind_share` (ShareK5.lean) · (a) yes · (b) not here · (c) not here · (d) not in the share
  K6 · `k6Share_atTheG` · (a) scope, live beside · (b) not here · (c) not here · (d) K1 or K2
  K7 · `reply_share_at_the_G`, laid as `k7_kind_share` (ShareK7.lean) · (a) yes · (b) not here · (c) not here · (d) K1 or K2
  K8 · `k8Share_at_theGOfReturn`, laid as `k8_kind_share` (ShareK8.lean) · (a) yes · (b) not here · (c) not here · (d) K1 or K2
  K11 · the K11 row, laid as `k11_kind_share` (ShareK11.lean) · (a) yes · (b) not here · (c) not here · (d) K2 and K1, beside: at this row fresh says next to nothing

K, T and Th are binders, and all the memberships are asked at one K (`RowsLaid`). rowsLaid_of_entries gives them at the K of record (E2E/TheKOfRecord.lean) from the entries' equations.

This file proves zero knowledge of nothing: `rest`, `Th` and every other binder stay premises. A share that holds where G has no list of that kind says nothing: the statements that the rows stand in G are beside the kinds' terms.
-/
import AtFullSide.T3.TheOneAtTheG
import AtFullSide.K4.K4sRowsOfT3
import AtFullSide.E2E.OutputHeadRowAtTheG
import AtFullSide.T3.ShareK3
import AtFullSide.T3.ShareK5
import AtFullSide.T3.ShareK2
import AtFullSide.T3.ShareK8
import AtFullSide.T3.ShareK7
import AtFullSide.T3.ShareK11
import E2E.TheKOfRecord

set_option autoImplicit false
set_option maxRecDepth 100000
attribute [-instance] Inst.Model.Scl.ref
noncomputable section
open scoped ENNReal

namespace AtFullSide.T3
open VerifiableInference.Compilation
open Iop Prob AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.AtFiles AtPublicFiles.Committed AtPublicFiles.Cut
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.TheG (ThreadParts theGOfReturn theGOfReturn_prover)
open AtPublicFiles.TheSides (KindRows replyBaseLot)
open ProofFile.Honest (Sides Owed relAt AtHonest OnlineProverWithDescription Cells ThreadsP ready onlineProverFromPublicFiles frameAsks KindShare
  rowDebtsP_of_kinds)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open ProofFile.Honest.Term (matrixInput)
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open LPFD.Full (instanceAsPlainRecord XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (protocolDataWellFormed committerCoinCountLessOne)
open P5J
open ProofFile.Honest.K4.ExactFresh (k4BaseSlot)
open ProofFile.Honest.K6 (headSimulatorLot)
open ProofFile.Honest.K5 (k5SLot)

local instance (priority := high) rowsFilledPad : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) rowsFilledValue : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) rowsFilledDefault : Inhabited RunValue := ⟨fun _ => 0⟩

variable {files : PublicFiles} {Wt : Type}

section Rows
variable (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
  {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp)
  {A : OnlineProverWithDescription FullSizeMatrix ProofFile.Honest.IndexCommitterCoins Cells Unit Unit}
  (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFilling = .ok A)
  (h : HeadAtReturn files A) (T : ThreadParts A Wt) (K : KindRows baseFilling A.Z A.G)
  (Th : ∀ w₀ rc ξ, BaseRel files hr w₀ rc ξ → ∀ k R,
    ready A.F A.B ((theGOfReturn made h T K).prover A.H) w₀ rc ξ k = .ok R →
    ThreadsP A.F A.B ((theGOfReturn made h T K).prover A.H) w₀ rc ξ k R)

/-- The kinds that have a term in this file. -/
abbrev Paid (κ : VerifiableInference.Desc.KindName) : Prop :=
  κ = .K2 ∨ κ = .K3 ∨ κ = .K4 ∨ κ = .K5 ∨ κ = .K6 ∨ κ = .K7 ∨ κ = .K8 ∨ κ = .K11

/-- **The memberships on the one K that the rows with a term ask.** -/
structure RowsLaid : Prop where
  k2 : AtFullSide.K2.baseSimLot ∈ K.lots
  k3 : AtPublicFiles.Lookup.lookupSimulatorLotAtTheBaseProver ∈ K.lots
  k4 : k4BaseSlot ∈ K.lots
  k5 : k5SLot (W₀ := FullSizeMatrix) (Rc := ProofFile.Honest.IndexCommitterCoins) (Xi := ProofFile.Inst) (X := Unit) (Pb := ProofFile.Inst) id
    ProofFile.Honest.K5.keyOfK3 ∈ K.lots
  k6 : headSimulatorLot (Rc := ProofFile.Honest.IndexCommitterCoins) (X := Unit) matrixInput.weights ∈ K.lots
  k7 : replyBaseLot ∈ K.lots
  k8 : ProofFile.Honest.K8.k8LotAtBase ∈ K.lots
  k11 : AtFullSide.K11.k11LotAtBase ∈ K.lots

include scope live in
/-- **`shares`, at the rows that have a term, from the memberships, and `rest` at the others.** -/
theorem sharesFilled (laid : RowsLaid K)
    (rest : ∀ κ, ¬ Unlaid κ → ¬ Paid κ →
      KindShare A (theGOfReturn made h T K) A.H (BaseRel files hr) Th κ) :
    ∀ κ, ¬ Unlaid κ → KindShare A (theGOfReturn made h T K) A.H (BaseRel files hr) Th κ := by
  intro κ hκ
  by_cases hp : Paid κ
  · rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact k2_kind_share scope live made h T K laid.k2 A.H (BaseRel files hr) Th
    · exact k3_kind_share made h T K laid.k3 A.H (BaseRel files hr) Th
    · exact AtFullSide.K4.k4_kind_share made h T K laid.k4 A.H (BaseRel files hr) Th
    · exact k5_kind_share made h T K laid.k5 A.H (BaseRel files hr) Th
    · exact AtPublicFiles.AtFiles.HonestTerm.OutputHead.k6Share_atTheG scope live made h T K (BaseRel files hr)
        Th laid.k6
    · exact k7_kind_share made h T K laid.k7 A.H (BaseRel files hr) Th
    · exact k8_kind_share made h T K laid.k8 A.H (BaseRel files hr) Th
    · exact k11_kind_share made h T K laid.k11 A.H (BaseRel files hr) Th
  · exact rest κ hκ hp

end Rows

/-- **The one theorem, its `shares` filled where a kind has a term.** -/
theorem zkOnServedRequests_fromRowsAtTheG
    (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp)
    {A : OnlineProverWithDescription FullSizeMatrix ProofFile.Honest.IndexCommitterCoins Cells Unit Unit} {more : List (String × Bool)}
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFilling = .ok A)
    (h : HeadAtReturn files A) (T : ThreadParts A Wt) (K : KindRows baseFilling A.Z A.G)
    (asks : ∀ t ∈ baseAsks A ++ more, t.2 = true)
    (one : ∃ w₀ rc ξ k R, ready A.F A.B A.H w₀ rc ξ k = .ok R)
    (Th : ∀ w₀ rc ξ, BaseRel files hr w₀ rc ξ → ∀ k R,
      ready A.F A.B ((theGOfReturn made h T K).prover A.H) w₀ rc ξ k = .ok R →
      ThreadsP A.F A.B ((theGOfReturn made h T K).prover A.H) w₀ rc ξ k R)
    (laid : RowsLaid K)
    (rest : ∀ κ, ¬ Unlaid κ → ¬ Paid κ →
      KindShare A (theGOfReturn made h T K) A.H (BaseRel files hr) Th κ)
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
  zeroKnowledgeOnServedRequests_atTheG scope live hr made h T K asks one Th
    (sharesFilled scope live hr made h T K Th laid rest) _start parts _whole

section Record
open AtPublicFiles.TheSides (TheThirteen LaterRows theK mem_theK)
variable {A : OnlineProverWithDescription FullSizeMatrix ProofFile.Honest.IndexCommitterCoins Cells Unit Unit}

/-- **At the K of record the memberships are the entries' equations.** -/
theorem rowsLaid_of_entries (E : TheThirteen baseFilling A.Z A.G)
    (apart : (E.entries.map (·.slot.name)).Nodup) (R : LaterRows baseFilling A.Z A.G)
    (e2 : E.k2.slot = AtFullSide.K2.baseSimLot)
    (e3 : E.k3.slot = AtPublicFiles.Lookup.lookupSimulatorLotAtTheBaseProver)
    (e4 : E.k4.slot = k4BaseSlot)
    (e5 : E.k5.slot = k5SLot (W₀ := FullSizeMatrix) (Rc := ProofFile.Honest.IndexCommitterCoins) (Xi := ProofFile.Inst) (X := Unit)
      (Pb := ProofFile.Inst) id ProofFile.Honest.K5.keyOfK3)
    (e6 : E.k6.slot = headSimulatorLot (Rc := ProofFile.Honest.IndexCommitterCoins) (X := Unit) matrixInput.weights)
    (e7 : E.k7.slot = replyBaseLot)
    (e8 : E.k8.slot = ProofFile.Honest.K8.k8LotAtBase)
    (e11 : E.k11.slot = AtFullSide.K11.k11LotAtBase) : RowsLaid (theK E apart R) :=
  ⟨e2 ▸ mem_theK (e := E.k2) (by simp [TheThirteen.entries]) apart R,
    e3 ▸ mem_theK (e := E.k3) (by simp [TheThirteen.entries]) apart R,
    e4 ▸ mem_theK (e := E.k4) (by simp [TheThirteen.entries]) apart R,
    e5 ▸ mem_theK (e := E.k5) (by simp [TheThirteen.entries]) apart R,
    e6 ▸ mem_theK (e := E.k6) (by simp [TheThirteen.entries]) apart R,
    e7 ▸ mem_theK (e := E.k7) (by simp [TheThirteen.entries]) apart R,
    e8 ▸ mem_theK (e := E.k8) (by simp [TheThirteen.entries]) apart R,
    e11 ▸ mem_theK (e := E.k11) (by simp [TheThirteen.entries]) apart R⟩

/-- **The one theorem at the K of record, its `shares` filled where a kind has a term.** -/
theorem zkOnServedRequests_fromRowsAtTheK
    (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp) {more : List (String × Bool)}
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFilling = .ok A)
    (h : HeadAtReturn files A) (T : ThreadParts A Wt) (E : TheThirteen baseFilling A.Z A.G)
    (apart : (E.entries.map (·.slot.name)).Nodup) (R : LaterRows baseFilling A.Z A.G)
    (asks : ∀ t ∈ baseAsks A ++ more, t.2 = true)
    (one : ∃ w₀ rc ξ k R', ready A.F A.B A.H w₀ rc ξ k = .ok R')
    (Th : ∀ w₀ rc ξ, BaseRel files hr w₀ rc ξ → ∀ k R',
      ready A.F A.B ((theGOfReturn made h T (theK E apart R)).prover A.H) w₀ rc ξ k = .ok R' →
      ThreadsP A.F A.B ((theGOfReturn made h T (theK E apart R)).prover A.H) w₀ rc ξ k R')
    (laid : RowsLaid (theK E apart R))
    (rest : ∀ κ, ¬ Unlaid κ → ¬ Paid κ →
      KindShare A (theGOfReturn made h T (theK E apart R)) A.H (BaseRel files hr) Th κ)
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
  zkOnServedRequests_fromRowsAtTheG scope live hr made h T (theK E apart R) asks one Th laid
    rest _start parts _whole

end Record

end AtFullSide.T3

#print axioms AtFullSide.T3.rowsLaid_of_entries
#print axioms AtFullSide.T3.zkOnServedRequests_fromRowsAtTheK
#print axioms AtFullSide.T3.zkOnServedRequests_fromRowsAtTheG
