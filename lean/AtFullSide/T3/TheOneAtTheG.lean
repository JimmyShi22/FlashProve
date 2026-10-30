-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/T3/TheOneAtTheG.lean: ZERO KNOWLEDGE ON SERVED REQUESTS AT THE SIDES theGOfReturn, FROM ONE SHARE PER KIND OF SUB-PROTOCOL: AN IMPLICATION.

1.  General in the threads' parts T and the kinds' rows K. The family of invariants Th is a variable: a family chosen
    out of an existence statement reveals nothing of itself, so only a share at every family, or one built from its own fields, fits it.
    Here the head's three equations, its three frame tests, input and hst are theorems. The number 2^-174 comes from window_at_term.
2.  Read it beside completeness, at the same return and the same rows G. On is asked only at parts that a run has
    called, and Good at letters that never hold, so a prover whose early block is always refused would meet all
    later rows with nothing shown. Completeness at the same G is what rules that out; this file does not show it.
3.  _start and _whole are guards: no proof in this file uses them.
4.  The premises are listed in the statement. This file proves zero knowledge of nothing.
-/
import AtFullSide.T3.TheOneOfSides
import Johnson.M1.SeatedOfReturn
import Johnson.Desc.ProofFile.Honest.K1.Pay.Whole
import Johnson.Desc.ProofFile.Honest.Law.RowDebtsByKind
import AtFullSide.T3.NoListAtTheG
import E2E.TheG

set_option autoImplicit false
set_option maxRecDepth 100000
attribute [-instance] Inst.Model.Scl.ref
noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open Iop Prob AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.AtFiles AtPublicFiles.Committed AtPublicFiles.Cut
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.TheG (ThreadParts theGOfReturn theGOfReturn_prover)
open AtPublicFiles.TheSides (KindRows)
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

local instance (priority := high) oneAtGPad : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) oneAtGValue : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) oneAtGDefault : Inhabited RunValue := ⟨fun _ => 0⟩

variable {files : PublicFiles} {Wt : Type}

/-- **The head at theGOfReturn**: its three equations and its frame's tests are theorems here. -/
theorem headAt_theG {A : OnlineProverWithDescription FullSizeMatrix ProofFile.Honest.IndexCommitterCoins Cells Unit Unit} {more : List (String × Bool)}
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFilling = .ok A)
    (h : HeadAtReturn files A) (T : ThreadParts A Wt) (K : KindRows baseFilling A.Z A.G)
    (asks : ∀ t ∈ baseAsks A ++ more, t.2 = true)
    (one : ∃ w₀ rc ξ k R, ready A.F A.B A.H w₀ rc ξ k = .ok R) :
    AtHonest OnBytes.secondHashFunction files (VerifierAndGoals.AtTheName.dpZ files) (FlashProve.theProofRun (asDescriptionFiles files)) A.Z
      h.places h.firstChain h.look baseFilling A (theGOfReturn made h T K) (baseAsks A ++ more) :=
  have hP := theGOfReturn_prover made h T K
  have e₁ := (congrArg (·.first) hP).symm
  have e₂ := (congrArg (·.shared) hP).symm
  have e₃ := (congrArg (·.second) hP).symm
  have sw := ProofFile.Honest.K1.Pay.sides_are_whole matrixInput OnBytes.HonestTrace.Sz.ref
    ProofFile.Honest.openHonest rfl h.head made
  ⟨h.head, made, e₁, e₂, e₃, fun t ht => by
    rcases List.mem_append.1 ht with ht | ht
    · simp only [frameAsks, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl
      · exact Johnson.M1.seated_of_return made _ e₁ e₂ e₃
      · exact sw.2.2
      · show ProofFile.Honest.rootedAll A.F ((theGOfReturn made h T K).prover A.H) = true
        rw [hP]
        exact sw.2.1
    · exact asks t ht, one⟩

/-- **Only the kinds with a list need a share**: K9, K15 and frame have no list at sides whose prover is the return's. -/
theorem shares_of_laid {A : OnlineProverWithDescription FullSizeMatrix ProofFile.Honest.IndexCommitterCoins Cells Unit Unit}
    {G : Sides A.F A.B FullSizeMatrix ProofFile.Honest.IndexCommitterCoins TableKey Cells Unit Unit}
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFilling = .ok A)
    (hP : G.prover A.H = A.H) {Rel : FullSizeMatrix → ProofFile.Honest.IndexCommitterCoins → ProofFile.Inst → Prop}
    (Th : ∀ w₀ rc ξ, Rel w₀ rc ξ → ∀ k R, ready A.F A.B (G.prover A.H) w₀ rc ξ k = .ok R →
      ThreadsP A.F A.B (G.prover A.H) w₀ rc ξ k R)
    (shares : ∀ κ, ¬ Unlaid κ → KindShare A G A.H Rel Th κ) : ∀ κ, KindShare A G A.H Rel Th κ := by
  intro κ
  by_cases hκ : Unlaid κ
  · obtain ⟨a₁, a₂, a₃⟩ := base_unlaid _ _ _ _ made hκ
    obtain ⟨l₁, l₂, l₃⟩ := noList_of_prover G A.H hP a₁ a₂ a₃
    exact kindShare_of_noList l₁ l₂ l₃
  · exact shares κ hκ

/-- **Zero knowledge at theGOfReturn, the offline side given as three premises**: an implication, where the two sides meet.
Read it beside completeness at the same return and G, which is not shown here. -/
theorem zeroKnowledgeOnServedRequests_atTheG_ofOfflineLines {a : ℝ≥0∞}
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
    (shares : ∀ κ, ¬ Unlaid κ → KindShare A (theGOfReturn made h T K) A.H (BaseRel files hr) Th κ)
    (_start : ∃ z₀, A.F.okStart (instanceAsPlainRecord z₀) = true)
    (parts : Parts files) (offlineSimulator : Compile.Lifetime.SimOf (protocolAtFiles files).offline)
    (offlineTable : ∀ i r e, (offlineProver parts).ext (i, r, e) = (protocolAtFiles files).encodeIndex i r)
    (offline : ExactOutsideStops (offlineProver parts)
      (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y) (workAtFiles files).offline.cleared
      offlineSimulator)
    (offlineStops : PrivateStopsAtMost (offlineProver parts)
      (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y) (workAtFiles files).offline a) :
    ZeroKnowledgeOnServedRequests files hr (HonestProvers.ofThreeProvers (honestProvers files parts)) a 0
      (ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ))) :=
  have hd := headAt_theG made h T K asks one
  have madeThru : ProofFile.Honest.Term.onlineMaker files =
      .ok (A.thru id (ProofFile.Honest.Term.tableCoins files) matrixInput.dummy) :=
    ProofFile.Honest.atPure_through id (ProofFile.Honest.Term.tableCoins files) matrixInput.dummy hd.made dummy_inRange
  zeroKnowledgeOnServedRequests_fromTheBase files scope live hr hd
    (rowDebtsP_of_kinds (input_at_base_whole files scope live hr hd)
      (hst_at_base files scope live hr hd) Th
      (shares_of_laid made (theGOfReturn_prover made h T K) Th shares))
    (owns_base scope live hd)
    (hidSmall_of_window hr (AtPublicFiles.AtFiles.HonestTerm.window_at_term scope hr live madeThru)
      fun _ _ hs => AtPublicFiles.AtFiles.servedRequest_below committerCoinCountLessOne files scope hr hs)
    parts offlineSimulator offlineTable offline offlineStops

/-- **Zero knowledge on served requests at theGOfReturn**: an implication. -/
theorem zeroKnowledgeOnServedRequests_atTheG
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
    (shares : ∀ κ, ¬ Unlaid κ → KindShare A (theGOfReturn made h T K) A.H (BaseRel files hr) Th κ)
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
  have hd := headAt_theG made h T K asks one
  zeroKnowledgeOnServedRequests_atTheWindow scope live hr hd
    (rowDebtsP_of_kinds (input_at_base_whole files scope live hr hd)
      (hst_at_base files scope live hr hd) Th
      (shares_of_laid made (theGOfReturn_prover made h T K) Th shares)) _start parts _whole

/-- The same with a share at every kind. -/
theorem zeroKnowledgeOnServedRequests_atTheG_allKinds
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
    (shares : ∀ κ, KindShare A (theGOfReturn made h T K) A.H (BaseRel files hr) Th κ)
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
  zeroKnowledgeOnServedRequests_atTheG scope live hr made h T K asks one Th (fun κ _ => shares κ) _start
    parts _whole

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.zeroKnowledgeOnServedRequests_atTheG
#print axioms VerifiableInference.Compilation.zeroKnowledgeOnServedRequests_atTheG_ofOfflineLines
#print axioms VerifiableInference.Compilation.shares_of_laid
#print axioms VerifiableInference.Compilation.zeroKnowledgeOnServedRequests_atTheG_allKinds
