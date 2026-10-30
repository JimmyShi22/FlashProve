-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/CellsAreTrace.lean: the proofs of the eight statements of
Johnson/FrontRoad/CellsAreTraceSpec.lean: under TraceOwn, at every tied request of Yes at which the
prover's trace function answers, the cells that the pinned part of the smallness test reads at the
list matsOf Zp.p.X l are the entries of the model's trace.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
  The steps   publicOf_laid: under LaidAt publicOf returns Zp.p.X. tl_is_plan: in scope the built
      segment number l has the list of matrices of the verifier's plan of sub-proof l (planMats,
      Johnson/HonestTrace/Full.lean), by ground_tails (Johnson/IMR/K8Seat.lean). plan_size: that
      list has as many members as matsOf Zp.p.X l: 8, 9 or 5 (matsOf_length,
      Johnson/HonestTrace/DigitsAtTrace.lean; size_head, size_even, size_odd,
      Johnson/Goal/Meaning/HidOwner.lean). fits_iff_length: smallFits at the description's own
      parameters says whether the list is as long as the list of the segment Xl (Xl.tl.mats), at
      every G₀, Xl and l; that this is the plan's list is tl_is_plan. parOwn_at: what parOwn names
      at the written place. empty_label: the empty string is no label, at the numbers of parts 3, 1,
      1, 4. signedOf_zero. owner_no: the owner of a member of a segment's list is a segment of the
      proof and has a number for the matrix.
  The eight proofs   matsOf_fits, reads_theTrace, cells_are_trace, sessionStops_of_tiedOwn_matsOf,
      cells_are_trace_speaks, matsOf_reads_ones, empty_names_fit_and_read_zero,
      short_names_do_not_fit.

How it fits. reads_theTrace is cellsAtOf_matsOf (Johnson/HonestTrace/DigitsAtTrace.lean) at
theTrace, with its two premises paid by namesFit_theTrace
(Johnson/Goal/HonestTrace/FromCellsInScope.lean) and meetsAll_theTrace
(Johnson/Goal/HonestTrace/FullPlanesInScope.lean). cells_are_trace goes by plain_of_own
(Johnson/FrontRoad/TracePremises.lean). cells_are_trace_speaks goes by servedTyped_exists
(Johnson/FrontRoad/ServedExists.lean), valid_of_holds and trace_there_of_model
(Johnson/FrontRoad/TracePremises.lean) and validTiedG_atFiles (E2E/BridgeLinkAtFiles.lean).
matsOf_reads_ones goes by cellOf_label (Johnson/HonestTrace/CellOfAt.lean), which holds at every
trace. All limits: the head of Johnson/FrontRoad/CellsAreTraceSpec.lean. Not one of the release's
goal statements.
-/
import Johnson.FrontRoad.CellsAreTraceSpec
import Johnson.FrontRoad.ParOwnChecks
import Johnson.FrontRoad.ServedExists
import Johnson.Goal.HonestTrace.FromCellsInScope
import Johnson.Goal.Meaning.HidOwner

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open AtPublicFiles.AtFiles AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Flat (RecFull)
open OnBytes.Params (Lines missedInTheChecks clog2)
open OnBytes.Maker (WholeD)
open OnBytes.Model.Verify (publicOf)
open OnBytes.HonestTrace (Tr cellsC matsOf planMats cellsSmall_cellOf ServesAt theTrace
  meetsAll_theTrace servesAt_iff_in_scope TraceHinge)
open Inst.Model (Instance ppref)
open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.First.K8 (Par)
open ProofFile.Honest (Prover ProverCoinCounts Sides Ready Coins ready)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (protocolDataWellFormed)
open P5J

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off within this namespace,
so that no statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) nonemptyPadZ_cellsAreTrace : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

/- The same of this one. -/
local instance (priority := high) nonemptyOfInhabited_cellsAreTrace {α : Type} [Inhabited α] :
    Nonempty α := ⟨default⟩

/-! ## The steps -/

section
variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
  (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)

/-- Under LaidAt publicOf returns Zp.p.X. -/
theorem publicOf_laid {D : WholeD} {r : LPFD.Full.RunPF}
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := by
  obtain ⟨Bs, base, O⟩ := L.opened
  exact O.W ▸ O.public

/-- In scope the built segment number l has the list of matrices of the verifier's plan of
sub-proof l. -/
theorem tl_is_plan (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    {D : WholeD} {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {G₀ : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) {l : ℕ} (hl : l < 25)
    {Xl : OnBytes.Model.Stages.LinkH} (hX : G₀.built[l]? = some Xl) :
    Xl.tl.mats = planMats Zp.p.X l := by
  have hW : G₀.W = Zp.p.X := ProofFile.Law.blankBy_W hG
  obtain ⟨tails, lh, eh, etl, -⟩ := IM.ground_tails scope hr L.pub hG
  unfold planMats
  rw [if_neg (by omega)]
  by_cases h24 : l = 24
  · subst h24
    obtain rfl : lh = Xl := Option.some.inj (eh.symm.trans hX)
    rw [if_pos rfl, etl, hW]
  · rw [if_neg h24]
    obtain ⟨hp, a, x, x', ehp, ea, e, et, -, -, -, -, e', et', -⟩ := tails (l / 2) (by omega)
    rw [hW] at ehp ea
    rcases Nat.mod_two_eq_zero_or_one l with h | h
    · have el : 2 * (l / 2) = l := by omega
      rw [el] at e
      obtain rfl : x = Xl := Option.some.inj (e.symm.trans hX)
      rw [if_pos h, ehp, et]
      rfl
    · have el : 2 * (l / 2) + 1 = l := by omega
      rw [el] at e'
      obtain rfl : x' = Xl := Option.some.inj (e'.symm.trans hX)
      rw [if_neg (by omega), ea, et']
      rfl

/-- In scope the plan's list of sub-proof l has as many members as matsOf Zp.p.X l. -/
theorem plan_size (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    {D : WholeD} {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {l : ℕ} (hl : l < 25) : (planMats Zp.p.X l).size = (matsOf Zp.p.X l).length := by
  have hX := publicOf_laid Z Zp Np cF L
  have C := OnBytes.Road.Hd.core_of_scope scope hr hX
  rw [OnBytes.HonestTrace.matsOf_length (OnBytes.HonestTrace.partsFit_in_scope scope hr hX) hl,
    OnBytes.HonestTrace.planMats_eq]
  by_cases h24 : l = 24
  · subst h24
    rw [if_pos rfl]
    exact Meaning.size_head hX C
  · rw [if_neg h24]
    rcases Nat.mod_two_eq_zero_or_one l with h | h
    · have el : 2 * (l / 2) = l := by omega
      rw [if_pos h, ← el]
      exact Meaning.size_even hX C (by omega)
    · have el : 2 * (l / 2) + 1 = l := by omega
      rw [if_neg (by omega), ← el]
      exact Meaning.size_odd hX C (by omega)

end

/-- smallFits at the description's own parameters says whether the list is as long as the segment's
plan's list. -/
theorem fits_iff_length (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) (Xl : OnBytes.Model.Stages.LinkH) (l : ℕ)
    (ms : List (ℕ × String × ℕ)) :
    ProofFile.Honest.K8.smallFits (ProofFile.k8Par Zp G₀ Xl l, ms) = (ms.length == Xl.tl.mats.size) := by
  unfold ProofFile.Honest.K8.smallFits
  show (ms.length == (Xl.tl.mats.toList.map (·.k)).length &&
    (Xl.tl.mats.toList.map (·.m)).length == (Xl.tl.mats.toList.map (·.k)).length) = _
  have e : Xl.tl.mats.toList.length = Xl.tl.mats.size := Array.length_toList
  rw [List.length_map, List.length_map, e, beq_self_eq_true, Bool.and_true]

/-- What parOwn names at the written place of the link l. -/
theorem parOwn_at (Zp : ProofFile.Pub) (mats : ℕ → List (ℕ × String × ℕ)) {G₀ : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) {l : ℕ}
    {Xl : OnBytes.Model.Stages.LinkH} (hX : G₀.built[l]? = some Xl) :
    parOwn Zp mats (k8PlaceAt l) = some (ProofFile.k8Par Zp G₀ Xl l, mats l) := by
  rw [parOwn_eq]
  show (if KindName.K8 = KindName.K8 then (some l).bind (ownAt Zp mats) else none) = _
  rw [if_pos rfl]
  show ownAt Zp mats l = _
  unfold ownAt
  rw [hG]
  show ((G₀.built[l]?).map fun Xl => (ProofFile.k8Par Zp G₀ Xl l, mats l)) = _
  rw [hX]
  rfl

/-- The empty string is no label, at the numbers of parts 3, 1, 1, 4. -/
theorem empty_label (σ : OnBytes.HonestTrace.Seg) :
    OnBytes.HonestTrace.MatName.ofLabel? 3 1 1 4 σ "" = none := by
  cases σ with
  | ff g =>
    exact (by decide : OnBytes.HonestTrace.MatName.ofLabel? 3 1 1 4 (.ff 0) "" = none)
  | att g =>
    exact (by decide : OnBytes.HonestTrace.MatName.ofLabel? 3 1 1 4 (.att 0) "" = none)
  | head => decide

theorem signedOf_zero : ProofFile.Honest.K8.signedOf 0 = 0 := by
  have h := OnBytes.HonestTrace.signedOf_cast 0 (by norm_num)
  rwa [Int.cast_zero] at h

/-- At the numbers of parts 3, 1, 1, 4, for a segment of a proof with twelve groups of layers: the
owner of a member of the segment's list is such a segment too, and has a number for the matrix in
its own list. -/
theorem owner_no {σ : OnBytes.HonestTrace.Seg} (hσ : σ.Below 12) {mu : ℕ}
    {μ : OnBytes.HonestTrace.MatName}
    (hμ : (OnBytes.HonestTrace.MatName.all 3 1 1 4 σ)[mu]? = some μ) :
    (OnBytes.HonestTrace.Sz.ref.owner σ μ).1.Below 12 ∧
      ∃ a, OnBytes.HonestTrace.MatName.no? 3 1 1 4 (OnBytes.HonestTrace.Sz.ref.owner σ μ).1
        (OnBytes.HonestTrace.Sz.ref.owner σ μ).2 = some a := by
  have hn := OnBytes.HonestTrace.all_no_ref σ hμ
  have own : OnBytes.HonestTrace.Sz.ref.owner σ μ = (σ, μ) →
      (OnBytes.HonestTrace.Sz.ref.owner σ μ).1.Below 12 ∧
      ∃ a, OnBytes.HonestTrace.MatName.no? 3 1 1 4 (OnBytes.HonestTrace.Sz.ref.owner σ μ).1
        (OnBytes.HonestTrace.Sz.ref.owner σ μ).2 = some a := fun e => by
    rw [e]
    exact ⟨hσ, mu, hn⟩
  cases σ with
  | ff g =>
    have hg : g < 12 := hσ
    cases μ <;> try exact own rfl
    · by_cases h0 : g = 0
      · exact own (if_pos h0)
      · have e : OnBytes.HonestTrace.Sz.ref.owner (.ff g) .xbI = (.ff (g - 1), .xbO) := if_neg h0
        rw [e]
        exact ⟨show g - 1 < 12 by omega, 7, rfl⟩
  | att g =>
    have hg : g < 12 := hσ
    cases μ <;> try exact own rfl
    · exact ⟨hg, 6, rfl⟩
  | head =>
    cases μ <;> try exact own rfl
    · exact ⟨show 11 < 12 by norm_num, 7, rfl⟩

/-! ## The eight -/

theorem matsOf_fits : Spec.matsOf_fits := by
  intro Z Zp Np cF scope pp hr D r L l hl
  obtain ⟨Bs, base, O⟩ := L.opened
  have hG := O.blank
  obtain ⟨Xl, hX⟩ := built_at Z Zp Np cF scope hr L hG l hl
  refine ⟨Bs.G₀, Xl, hG, hX, parOwn_at Zp _ hG hX, ?_⟩
  rw [fits_iff_length, tl_is_plan Z Zp Np cF scope hr L hG hl hX,
    plan_size Z Zp Np cF scope hr L hl]
  exact beq_self_eq_true _

theorem reads_theTrace : Spec.reads_theTrace := by
  intro Z Zp Np cF scope pp hr D r L i x S l hl mu r' c
  have hX := publicOf_laid Z Zp Np cF L
  exact OnBytes.HonestTrace.cellsAtOf_matsOf (OnBytes.HonestTrace.namesFit_theTrace scope hr hX S)
    (meetsAll_theTrace scope hr hX S) hl mu r' c

theorem cells_are_trace : Spec.cells_are_trace := by
  intro Z Zp Np cF R₂ R₃ _ _ _ _ run₂ run₃ X₀ Xh B G H Yes scope pp hr live D r L hO n w a ht tr htr
  obtain ⟨i, x, hi, hx, S, rfl⟩ :=
    plain_of_own Z Zp Np cF run₂ run₃ B G H Yes scope hr live L hO n w a ht tr htr
  exact ⟨i, x, hi, hx, S, fun l hl mu r' c =>
    reads_theTrace Z Zp Np cF scope hr L i x S l hl mu r' c⟩

theorem sessionStops_of_tiedOwn_matsOf : Spec.sessionStops_of_tiedOwn_matsOf := by
  intro Z Zp Np cF R₂ R₃ _ _ _ _ run₂ run₃ X₀ Xh B G H scope pp hr live D r L w₀ rc x₀ k₀ R hR hn
    Yes h₁ h₃ hO ok Gs
  exact sessionStops_of_tiedOwn_files Z Zp Np cF run₂ run₃ B G H scope hr live L hR hn Yes
    (matsOf Zp.p.X) h₁ h₃ hO ok Gs

theorem cells_are_trace_speaks : Spec.cells_are_trace_speaks := by
  intro Z Zp Np cF R₂ R₃ _ _ _ _ run₂ run₃ X₀ Xh B G H₀ scope pp hr live D r L
  obtain ⟨i, x', T⟩ := servedTyped_exists Z Zp Np cF scope hr live L
  obtain ⟨rc⟩ := (inferInstance : Nonempty (protocolAtFiles Z).EncodingRandomness)
  obtain ⟨s⟩ := (inferInstance : Nonempty (protocolAtFiles Z).OutOfDomainSeed)
  have hi : VerifiableInference.OnPublicFiles.Flat.Holds
      (VerifiableInference.OnPublicFiles.Flat.matrixOf i) i :=
    VerifiableInference.OnPublicFiles.Flat.holds_matrixOf i
  have hx : RyesZ Z (VerifiableInference.OnPublicFiles.Flat.matrixOf i) x' :=
    valid_of_holds Z Zp Np cF scope hr live L _ i x' hi T
  have ht : TiedYes Z Zp Np cF run₂ run₃ B G { H₀ with trace := viaIndex (modelTrace Zp.p.X) }
      (RyesZ Z) 0 (VerifiableInference.OnPublicFiles.Flat.matrixOf i, rc, s)
      (LPFD.Full.instanceAsPlainRecord (x', (protocolAtFiles Z).recOf (VerifiableInference.OnPublicFiles.Flat.matrixOf i) rc s)) :=
    ⟨⟨x', hx, rfl⟩, validTiedG_atFiles Z Zp Np cF run₂ run₃ B G _
      (AtPublicFiles.AtZero.itemsZero_of_data L.data) 0 _ rc s x' trivial trivial hx⟩
  obtain ⟨tr, htr⟩ := trace_there_of_model Z Zp Np cF run₂ run₃ B G
    { H₀ with trace := viaIndex (modelTrace Zp.p.X) } (RyesZ Z) scope hr live L
    (fun _ _ => rfl) 0 _ _ ht
  exact ⟨0, _, _, tr, ht, htr⟩

theorem matsOf_reads_ones : Spec.matsOf_reads_ones := by
  intro Z Zp Np cF scope pp hr D r L l hl mu hmu r' c
  have hP := OnBytes.HonestTrace.partsFit_in_scope scope hr (publicOf_laid Z Zp Np cF L)
  obtain ⟨σ, hσ⟩ := OnBytes.HonestTrace.seg_of_lt hl
  obtain ⟨hb, -⟩ := OnBytes.HonestTrace.Seg.of_ofNo hσ
  have p1 := (OnBytes.HonestTrace.parts_at hP hσ).1
  have hm : mu < (OnBytes.HonestTrace.MatName.all 3 1 1 4 σ).length := by
    unfold matsOf at hmu
    rw [hσ] at hmu
    simpa only [p1, List.length_map] using hmu
  have hμ := List.getElem?_eq_getElem hm
  obtain ⟨ob, a, on⟩ := owner_no hb hμ
  unfold ProofFile.Honest.K8.cellsAtOf matsOf
  rw [hσ]
  simp only [p1, List.getElem?_map, hμ, Option.map_some]
  show ProofFile.Honest.K8.signedOf (OnBytes.HonestTrace.cellOf Zp.p.X (fun _ _ _ _ => 1) _ _ r'
          (0 + c)) = 1
  rw [Nat.zero_add, OnBytes.HonestTrace.cellOf_label hP _ ob on]
  exact OnBytes.HonestTrace.signedOf_cast 1 (by norm_num)

theorem empty_names_fit_and_read_zero : Spec.empty_names_fit_and_read_zero := by
  intro Z Zp Np cF scope pp hr D r L l hl
  obtain ⟨Bs, base, O⟩ := L.opened
  have hG := O.blank
  obtain ⟨Xl, hX⟩ := built_at Z Zp Np cF scope hr L hG l hl
  have hP := OnBytes.HonestTrace.partsFit_in_scope scope hr (publicOf_laid Z Zp Np cF L)
  refine ⟨Bs.G₀, Xl, hG, hX, ?_, fun T mu r' c => ?_⟩
  · rw [fits_iff_length, tl_is_plan Z Zp Np cF scope hr L hG hl hX,
      plan_size Z Zp Np cF scope hr L hl]
    unfold emptyNames
    rw [List.length_replicate]
    exact beq_self_eq_true _
  · unfold ProofFile.Honest.K8.cellsAtOf emptyNames
    rw [List.getElem?_replicate]
    by_cases hmu : mu < (matsOf Zp.p.X l).length
    · rw [if_pos hmu]
      show ProofFile.Honest.K8.signedOf (OnBytes.HonestTrace.cellOf Zp.p.X T l "" r' (0 + c)) = 0
      obtain ⟨σ, hσ⟩ := OnBytes.HonestTrace.seg_of_lt hl
      unfold OnBytes.HonestTrace.cellOf
      rw [hσ]
      simp only
      rw [(OnBytes.HonestTrace.parts_at hP hσ).2.2, empty_label]
      exact signedOf_zero
    · rw [if_neg hmu]

theorem short_names_do_not_fit : Spec.short_names_do_not_fit := by
  intro Z Zp Np cF scope pp hr D r L l hl G₀ Xl hG hX
  have hP := OnBytes.HonestTrace.partsFit_in_scope scope hr (publicOf_laid Z Zp Np cF L)
  have hn := OnBytes.HonestTrace.matsOf_length hP hl
  have hpos : 0 < (matsOf Zp.p.X l).length := by
    rw [hn]
    split_ifs <;> omega
  rw [fits_iff_length, tl_is_plan Z Zp Np cF scope hr L hG hl hX,
    plan_size Z Zp Np cF scope hr L hl, List.length_dropLast]
  exact beq_false_of_ne (by omega)

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.nonemptyPadZ_cellsAreTrace
#print axioms OnBytes.FrontRoad.nonemptyOfInhabited_cellsAreTrace
#print axioms OnBytes.FrontRoad.publicOf_laid
#print axioms OnBytes.FrontRoad.tl_is_plan
#print axioms OnBytes.FrontRoad.plan_size
#print axioms OnBytes.FrontRoad.fits_iff_length
#print axioms OnBytes.FrontRoad.parOwn_at
#print axioms OnBytes.FrontRoad.empty_label
#print axioms OnBytes.FrontRoad.signedOf_zero
#print axioms OnBytes.FrontRoad.matsOf_fits
#print axioms OnBytes.FrontRoad.reads_theTrace
#print axioms OnBytes.FrontRoad.cells_are_trace
#print axioms OnBytes.FrontRoad.sessionStops_of_tiedOwn_matsOf
#print axioms OnBytes.FrontRoad.empty_names_fit_and_read_zero
#print axioms OnBytes.FrontRoad.short_names_do_not_fit
#print axioms OnBytes.FrontRoad.owner_no
#print axioms OnBytes.FrontRoad.cells_are_trace_speaks
#print axioms OnBytes.FrontRoad.matsOf_reads_ones
