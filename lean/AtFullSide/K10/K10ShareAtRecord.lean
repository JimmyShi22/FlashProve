-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/K10ShareAtRecord.lean: THE KIND K10's THREE SHARES OF `RowDebtsP` (`KindShare`, Johnson/Desc/ProofFile/Honest/Law/RowDebtsByKind.lean) AT THE SIDES `theG` (E2E/TheG.lean) OVER THE ROWS THAT
THE KINDS LAY, wherever these rows hold the closings' lot, and so at the rows of record `theK` (E2E/TheKOfRecord.lean) at K10's entry.

  `closing_rows_of_kind`   a row of the kind in the first chain's rows is a closing's row `closingRow …`
  `k10Bud_theG`            the share of the bound: a closing's row bears `closeBud`, which asks nothing: the part sends no table
  `k10On_theG`             the share of On: a closing's row bears `closeOn true …`, which asks nothing
  **`k10Share_theG`**        the three shares at `theGOfReturn made h T K`, from `closingsSLotAt matrixInput Sz.ref ∈ K.lots`
  **`k10Share_at_record`**   the same at K := `theK E apart R`, from `E.k10 = k10Entry files A.Z A.G`

By what. The first share is `AtFullSide.M1.kindPays_K10_theG` (AtFullSide/M1/KindAtTheG.lean). In the two later chains no sub-protocol is of the kind (`cuts_kinds`, by Lean's kernel), so that no list of the kind is
seated there and the clauses on these chains hold for want of a side.

Limits. On and the bound of a closing's row ask nothing at the total form of the part, so the second and the third share say little: the weight lies in the first, whose limits are its own file's. The head, the scope,
`protocolDataWellFormed` and the base maker's return are premises. This file proves no property of a prover or a protocol; on zero knowledge and on hiding it says nothing.
-/
import AtFullSide.M1.KindAtTheG
import E2E.KindPaysOfALot
import AtFullSide.K10.K10Entry
import Johnson.Desc.ProofFile.Honest.Law.RowDebtsByKind

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (KindName)
open OnBytes (TableKey)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open AtPublicFiles.TheSides AtPublicFiles.TheG
open ProofFile.Honest.Term (matrixInput baseFilling)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open AtFullSide.M1 (lots_k10 no_side no_kind_of_cut cuts_at_return cuts_kinds kindPays_K10_theG)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} {Wt : Type}

/-- **A row of the kind in the first chain's rows is a closing's row.** -/
theorem closing_rows_of_kind (K : KindRows (baseFilling files) A.Z A.G)
    (hc : closingsSLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref ∈ K.lots) :
    ∀ u ∈ K.slots.rows.first, u.place.kind = KindName.K10 →
      (∀ a b c, u.bud a b c) ∧ ∀ m ca st fr, u.On m ca st fr := by
  intro u hu hk
  have hr := rows_of_overlay (Z := A.Z) (Gr := A.G) (lots := (baseFilling files).lots) K.apart
    (ls := [closingsSLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref])
    (fun l hl => by rw [List.mem_singleton.1 hl]; exact hc) K.lots_fit (κ := KindName.K10)
    (fun M hM => by
      by_cases hx : ∃ x ∈ M.halves A.Z A.G, x.place.kind = KindName.K10
      · obtain ⟨x, hxm, hxk⟩ := hx
        refine Or.inl ⟨_, List.mem_singleton.2 rfl, ?_⟩
        rw [lots_k10 A.Z A.G M hM x hxm hxk]
        rfl
      · exact Or.inr fun x hxm hxk => hx ⟨x, hxm, hxk⟩)
  obtain ⟨l, hl, hul⟩ := hr u hu hk
  rw [List.mem_singleton.1 hl] at hul
  cases hch : ProofFile.onlineFirstChainAt A.Z with
  | error e =>
    rw [closingsSLotAt_error matrixInput OnBytes.HonestTrace.Sz.ref A.G hch] at hul
    cases hul
  | ok c =>
    rw [closingsSLotAt_ok matrixInput OnBytes.HonestTrace.Sz.ref A.G hch] at hul
    obtain ⟨Q, -, rfl⟩ := List.mem_map.1 hul
    exact ⟨fun _ _ _ => trivial, fun _ _ _ _ hf => by cases hf⟩

/-- No sub-protocol of the two later chains is of the kind, at the head's description. -/
theorem later_chains_without (h : HeadAtReturn files A) (hS : VerifierAndGoals.InScope files = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL (baseFilling files) = .ok A) :
    (∀ b ∈ h.description.shared.blocksInOrder, b.place.kind ≠ KindName.K10) ∧
      ∀ b ∈ h.description.second.blocksInOrder, b.place.kind ≠ KindName.K10 := by
  obtain ⟨-, c₂, c₃⟩ := cuts_at_return hS hL made
  have e := (ProofFile.Honest.atPure_at_laid h.head.laid made).2
  rw [e] at c₂ c₃
  exact ⟨no_kind_of_cut c₂ cuts_kinds.2.1, no_kind_of_cut c₃ cuts_kinds.2.2⟩

section
variable (h : HeadAtReturn files A) (hS : VerifierAndGoals.InScope files = true)
  (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
  (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL (baseFilling files) = .ok A)
  (T : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G)
  (hc : closingsSLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref ∈ K.lots)
include hS hL made hc

/-- **The share of the bound.** -/
theorem k10Bud_theG : Johnson.M1.KindBud (theG h T K) KindName.K10 := by
  obtain ⟨n₂, n₃⟩ := later_chains_without h hS hL made
  refine ⟨fun L hLm hk _ _ _ _ _ _ _ _ _ _ _ => ?_, fun L _ hk σ hσ => (no_side n₂ hk hσ).elim,
    fun L _ hk σ hσ => (no_side n₃ hk hσ).elim⟩
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hLm
  exact (closing_rows_of_kind K hc u hu hk).1 _ _ _

/-- **The share of On**, at every prover, relation and family of invariants. -/
theorem k10On_theG (H : Prover FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit) (Rel : FullSizeMatrix → IndexCommitterCoins → ProofFile.Inst → Prop)
    (Th : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready h.description A.B ((theG h T K).prover H) w₀ rc x k = .ok R →
      ThreadsP h.description A.B ((theG h T K).prover H) w₀ rc x k R) :
    KindOnAtEveryRun (G := theG h T K) (H := H) Rel Th KindName.K10 := by
  obtain ⟨n₂, n₃⟩ := later_chains_without h hS hL made
  intro w₀ rc x hrel k R hR ρ r _ _ _
  refine ⟨fun L hLm hk => ?_, fun L _ hk σ hσ => (no_side n₂ hk hσ).elim,
    fun L _ hk σ hσ => (no_side n₃ hk hσ).elim⟩
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hLm
  exact onAtRun₁_of_always _ ρ r fun m ca st fr => (closing_rows_of_kind K hc u hu hk).2 m ca st fr

/-- **K10's three shares at the sides over the kinds' rows**, at the description that the return holds. -/
theorem k10Share_theG (H : Prover FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit) (Rel : FullSizeMatrix → IndexCommitterCoins → ProofFile.Inst → Prop)
    (Th : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R,
      ready A.F A.B ((theGOfReturn made h T K).prover H) w₀ rc x k = .ok R →
      ThreadsP A.F A.B ((theGOfReturn made h T K).prover H) w₀ rc x k R) :
    KindShare A (theGOfReturn made h T K) H Rel Th KindName.K10 := by
  have all : (fun (F₀ : VerifiableInference.Desc.FileDescription ProofFile.Inst)
      (G : Sides F₀ A.B FullSizeMatrix IndexCommitterCoins TableKey Cells Unit Unit) =>
      VerifiableInference.Compilation.KindPays G KindName.K10 ∧ Johnson.M1.KindBud G KindName.K10 ∧
        ∀ (H : Prover FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit) (Rel : FullSizeMatrix → IndexCommitterCoins → ProofFile.Inst → Prop)
          (Th : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F₀ A.B (G.prover H) w₀ rc x k = .ok R →
            ThreadsP F₀ A.B (G.prover H) w₀ rc x k R),
          KindOnAtEveryRun (G := G) (H := H) Rel Th KindName.K10) A.F (theGOfReturn made h T K) :=
    castSides_of (ProofFile.Honest.atPure_at_laid h.head.laid made).2
      (Q := fun F₀ G => VerifiableInference.Compilation.KindPays G KindName.K10 ∧ Johnson.M1.KindBud G KindName.K10 ∧
        ∀ (H : Prover FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit) (Rel : FullSizeMatrix → IndexCommitterCoins → ProofFile.Inst → Prop)
          (Th : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F₀ A.B (G.prover H) w₀ rc x k = .ok R →
            ThreadsP F₀ A.B (G.prover H) w₀ rc x k R),
          KindOnAtEveryRun (G := G) (H := H) Rel Th KindName.K10)
      ⟨kindPays_K10_theG h hS hL made T K hc, k10Bud_theG h hS hL made T K hc,
        fun H Rel Th => k10On_theG h hS hL made T K hc H Rel Th⟩
  exact ⟨all.1, all.2.1, all.2.2 H Rel Th⟩

end

/-- **K10's three shares at the rows of record.** -/
theorem k10Share_at_record (h : HeadAtReturn files A) (hS : VerifierAndGoals.InScope files = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL (baseFilling files) = .ok A)
    (T : ThreadParts A Wt) (E : TheThirteen (baseFilling files) A.Z A.G) (hE : E.k10 = k10Entry files A.Z A.G)
    (apart : (E.entries.map (·.slot.name)).Nodup) (R : LaterRows (baseFilling files) A.Z A.G)
    (H : Prover FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit) (Rel : FullSizeMatrix → IndexCommitterCoins → ProofFile.Inst → Prop)
    (Th : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R',
      ready A.F A.B ((theGOfReturn made h T (theK E apart R)).prover H) w₀ rc x k = .ok R' →
      ThreadsP A.F A.B ((theGOfReturn made h T (theK E apart R)).prover H) w₀ rc x k R') :
    KindShare A (theGOfReturn made h T (theK E apart R)) H Rel Th KindName.K10 :=
  k10Share_theG h hS hL made T (theK E apart R)
    (by
      have hm : E.k10 ∈ E.entries := by simp [TheThirteen.entries]
      have := mem_theK hm apart R
      rw [hE, k10Entry_slot] at this
      exact this) H Rel Th

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.closing_rows_of_kind
#print axioms ProofFile.Honest.K10.later_chains_without
#print axioms ProofFile.Honest.K10.k10Bud_theG
#print axioms ProofFile.Honest.K10.k10On_theG
#print axioms ProofFile.Honest.K10.k10Share_theG
#print axioms ProofFile.Honest.K10.k10Share_at_record
