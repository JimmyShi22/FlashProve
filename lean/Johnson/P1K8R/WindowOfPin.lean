-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/WindowOfPin.lean: the private stops of an online prover, at one number, from the pin.

The session's family onlineProversOfCommitter is made of a prover H of the frame. Its private stops have the measure
of the format's gate, where H's halves are pinned, its trace is the model's, and its preparation
returns at one input. The work is index-side: this file joins what Johnson/FrontRoad/ has proved.

  bare_prover_self   rows made of H's own halves, forgotten, leave a prover with these halves as it is
  window_of_pin      the measure at every copy's number, index, randomness, seed and request of the
                     relation RyesZ Z
  window_number_of_pin   the same at 2 ^ (-174), in scope
  hid_reads_no_randomness   the set is the same at every copy's number, table randomness and seed
  hid_iff_of_pin   which messages the set holds: where the request has a trace, at some member of the
                   first chain a combination leaves its window with no stop in front

Limits. The pins, the trace and the preparation are premises. Nothing on acceptance.
-/
import Johnson.FrontRoad.CellsOwnAt
import Johnson.FrontRoad.CarryThrough
import Johnson.FrontRoad.StopsAtFiles
import Johnson.P1K8R.WindowNumber
import Johnson.P1K8R.WindowSet

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped ENNReal

namespace P1K8
open Iop AtPublicFiles.AtFiles AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Flat (front₀ join₀)
open _root_.Run (ckP)
open TypedOracleCompiler.Iop (RoundsQueryLayout)
open TypedOracleCompiler.Compile.Batch.Cms (wBC)
open OnBytes.FrontRoad
open OnBytes.HonestTrace (cellsC)
open VerifiableInference.Desc (Block Place KindName)
open ProofFile.Honest (Prover ProverCoinCounts Sides Ready Coins ready Cells chainStopAt drawsLo)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (protocolDataWellFormed flashProveData)
open FlashProve (dataAtFiles)
open OnBytes.Maker (WholeD)
open P5J

attribute [-instance] Inst.Model.Scl.ref

local instance (priority := high) nonemptyPadZ_windowOfPin : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

local instance (priority := high) nonemptyOfInhabited_windowOfPin {α : Type} [Inhabited α] :
    Nonempty α := ⟨default⟩

/-- Rows made of H's own halves, forgotten to halves, leave a prover with these halves as it is. -/
theorem bare_prover_self {Xi W₀ Rc Ky Tr' X₀ X : Type} (F : VerifiableInference.Desc.FileDescription Xi)
    (Bk : ProverCoinCounts) (H H₁ : Prover W₀ Rc Xi Ky Tr' X₀ X) (h₁ : H₁.first = H.first)
    (h₂ : H₁.shared = H.shared) (h₃ : H₁.second = H.second) :
    (bareSides F Bk H).prover H₁ = H₁ := by
  obtain ⟨a, b, c⟩ := bare_forgets F Bk H H₁
  have e₁ := a.trans h₁.symm
  have e₂ := b.trans h₂.symm
  have e₃ := c.trans h₃.symm
  cases H₁
  simp only [Sides.prover] at e₁ e₂ e₃ ⊢
  rw [e₁, e₂, e₃]

section
variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
  (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) {X₀ Xh : Type} (B : ProverCoinCounts)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Cells X₀ Xh)

/-- **The measure of the private stops, from the pin.** -/
theorem window_of_pin (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {x₀ : ProofFile.Inst} {k₀ : Coins B}
    {R : Ready FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Cells X₀ Xh}
    (hR : ready (descZ Zp Np cF) B ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) w₀ rc x₀ k₀ =
      .ok R)
    (hn : ∀ g ∈ H.first, g.place.kind ≠ KindName.frame)
    (mats : ℕ → List (ℕ × String × ℕ))
    (h₁ : RowsPinned (parOwn Zp mats) id H.first (descZ Zp Np cF).first.blocksInOrder.dropLast)
    (h₃ : RowsPinned (fun _ => none) id H.second (descZ Zp Np cF).second.blocksInOrder)
    (hT : H.trace = modelAt Zp.p.X (cellsC Zp.p.X))
    (n : ℕ) (i : FullSizeMatrix) (ρ : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed) (x : LPFD.Full.XF) (hx : RyesZ Z i x) :
    prRho (((onlineProversOfCommitter Z Zp Np cF silInst run₂ run₃ B (dataAtFiles flashProveData Z).P H).at n).Hid (i, ρ, e)
      (x, (protocolAtFiles Z).recOf i ρ e)) ≤ windowBound Zp := by
  let G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Cells X₀ Xh :=
    bareSides (descZ Zp Np cF) B H
  have eG : G.prover H = H := bare_prover_self _ B H H rfl rfl rfl
  have eP : provG Z Zp Np cF B G H = (cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H :=
    bare_prover_self _ B H _ rfl rfl rfl
  have hn' : ∀ L ∈ G.first, L.place.kind ≠ KindName.frame := by
    intro L hL
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hL
    exact hn g hg
  have hO : CellsOwnAt Z Zp Np cF run₂ run₃ B G H (RyesZ Z) id := by
    have h := model_meets_ownAt Z Zp Np cF run₂ run₃ B G H (RyesZ Z) (cellsC Zp.p.X)
    rw [← hT] at h
    exact cellsOwn_of_ownAt Z Zp Np cF run₂ run₃ B G H (RyesZ Z) id (cellsC Zp.p.X)
      (readsAs_cells Zp.p.X) h
  have h₁' : RowsPinned (parOwn Zp mats) id (provG Z Zp Np cF B G H).first
      (descZ Zp Np cF).first.blocksInOrder.dropLast := by
    rw [eP]
    exact h₁
  have h₃' : RowsPinned (fun _ => none) id (provG Z Zp Np cF B G H).second
      (descZ Zp Np cF).second.blocksInOrder := by
    rw [eP]
    exact h₃
  have hR' : ready (descZ Zp Np cF) B (provG Z Zp Np cF B G H) w₀ rc x₀ k₀ = .ok R := by
    rw [eP]
    exact hR
  have hS := sessionStops_of_cellsOwn Z Zp Np cF run₂ run₃ B G H scope hr live L hR' hn'
    (RyesZ Z) mats id h₁' h₃' hO (fun _ => True) (fun _ => True)
  have hY := validYes Z Zp Np cF run₂ run₃ B G H (Yes := RyesZ Z) (fun _ _ h => h)
    (AtPublicFiles.AtZero.itemsZero_of_data L.data) n i ρ e x trivial trivial hx
  have hb := hS n (i, ρ, e) (x, (protocolAtFiles Z).recOf i ρ e) ⟨trivial, trivial, hY⟩
  rw [famG_eq, eG, add_zero] at hb
  exact hb

/-- **The same, in numbers.** -/
theorem window_number_of_pin (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {x₀ : ProofFile.Inst} {k₀ : Coins B}
    {R : Ready FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Cells X₀ Xh}
    (hR : ready (descZ Zp Np cF) B ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) w₀ rc x₀ k₀ =
      .ok R)
    (hn : ∀ g ∈ H.first, g.place.kind ≠ KindName.frame)
    (mats : ℕ → List (ℕ × String × ℕ))
    (h₁ : RowsPinned (parOwn Zp mats) id H.first (descZ Zp Np cF).first.blocksInOrder.dropLast)
    (h₃ : RowsPinned (fun _ => none) id H.second (descZ Zp Np cF).second.blocksInOrder)
    (hT : H.trace = modelAt Zp.p.X (cellsC Zp.p.X))
    (n : ℕ) (i : FullSizeMatrix) (ρ : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed) (x : LPFD.Full.XF) (hx : RyesZ Z i x) :
    prRho (((onlineProversOfCommitter Z Zp Np cF silInst run₂ run₃ B (dataAtFiles flashProveData Z).P H).at n).Hid (i, ρ, e)
      (x, (protocolAtFiles Z).recOf i ρ e)) ≤ ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ)) := by
  rw [← window_number scope hr L]
  exact window_of_pin Z Zp Np cF run₂ run₃ B H scope hr live L hR hn mats h₁ h₃ hT n i ρ e x hx

/-- **The set does not see the bits of proof of work**, at every digest and further reading. -/
theorem hid_zero_tied (c₀ : VerifiableInference.Digest) (m₀ : List (Iop.Dig 256)) :
    HidZero (onlineProversOfCommitter Z Zp Np cF silInst run₂ run₃ B (dataAtFiles flashProveData Z).P H)
      ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀).W := by
  unfold onlineProversOfCommitter
  exact hidZero_atFiles Z _ _ _ _ _ _ _ _ c₀ m₀

/-- **The measure at messages whose test bits are set to 0.** -/
theorem window_cleared_of_pin (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {x₀ : ProofFile.Inst} {k₀ : Coins B}
    {R : Ready FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Cells X₀ Xh}
    (hR : ready (descZ Zp Np cF) B ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) w₀ rc x₀ k₀ =
      .ok R)
    (hn : ∀ g ∈ H.first, g.place.kind ≠ KindName.frame)
    (mats : ℕ → List (ℕ × String × ℕ))
    (h₁ : RowsPinned (parOwn Zp mats) id H.first (descZ Zp Np cF).first.blocksInOrder.dropLast)
    (h₃ : RowsPinned (fun _ => none) id H.second (descZ Zp Np cF).second.blocksInOrder)
    (hT : H.trace = modelAt Zp.p.X (cellsC Zp.p.X))
    (c₀ : VerifiableInference.Digest) (m₀ : List (Iop.Dig 256))
    (n : ℕ) (i : FullSizeMatrix) (ρ : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed) (x : LPFD.Full.XF) (hx : RyesZ Z i x) :
    prRho {τ | RoundsQueryLayout.zero (protocolAtFiles Z).onlineBatch.loc.shape (protocolAtFiles Z).onlineBatch.ann
        (wBC ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀).W).sh τ ∈
      ((onlineProversOfCommitter Z Zp Np cF silInst run₂ run₃ B (dataAtFiles flashProveData Z).P H).at n).Hid (i, ρ, e)
        (x, (protocolAtFiles Z).recOf i ρ e)} ≤ ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ)) := by
  have hb := window_number_of_pin Z Zp Np cF run₂ run₃ B H scope hr live L hR hn mats h₁ h₃ hT
    n i ρ e x hx
  have hz := hid_zero_tied Z Zp Np cF run₂ run₃ B H c₀ m₀ n (i, ρ, e) (x, (protocolAtFiles Z).recOf i ρ e)
  have hs : {τ | RoundsQueryLayout.zero (protocolAtFiles Z).onlineBatch.loc.shape (protocolAtFiles Z).onlineBatch.ann
        (wBC ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀).W).sh τ ∈
      ((onlineProversOfCommitter Z Zp Np cF silInst run₂ run₃ B (dataAtFiles flashProveData Z).P H).at n).Hid (i, ρ, e)
        (x, (protocolAtFiles Z).recOf i ρ e)} =
      ((onlineProversOfCommitter Z Zp Np cF silInst run₂ run₃ B (dataAtFiles flashProveData Z).P H).at n).Hid (i, ρ, e)
        (x, (protocolAtFiles Z).recOf i ρ e) := Set.ext hz
  rw [hs]
  exact hb

/-- **The set reads no table randomness, no seed and no copy's number**: at one index and one request
it is one set of messages. -/
theorem hid_reads_no_randomness (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) {D : WholeD} {r : LPFD.Full.RunPF}
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (hn : ∀ g ∈ H.first, g.place.kind ≠ KindName.frame)
    (mats : ℕ → List (ℕ × String × ℕ))
    (h₁ : RowsPinned (parOwn Zp mats) id H.first (descZ Zp Np cF).first.blocksInOrder.dropLast)
    (h₃ : RowsPinned (fun _ => none) id H.second (descZ Zp Np cF).second.blocksInOrder)
    (hT : H.trace = modelAt Zp.p.X (cellsC Zp.p.X))
    (n n' : ℕ) (i : FullSizeMatrix) (ρ ρ' : (protocolAtFiles Z).EncodingRandomness) (e e' : (protocolAtFiles Z).OutOfDomainSeed) (x : LPFD.Full.XF) :
    ((onlineProversOfCommitter Z Zp Np cF silInst run₂ run₃ B (dataAtFiles flashProveData Z).P H).at n).Hid (i, ρ, e)
        (x, (protocolAtFiles Z).recOf i ρ e) =
      ((onlineProversOfCommitter Z Zp Np cF silInst run₂ run₃ B (dataAtFiles flashProveData Z).P H).at n').Hid (i, ρ', e')
        (x, (protocolAtFiles Z).recOf i ρ' e') := by
  let G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Cells X₀ Xh :=
    bareSides (descZ Zp Np cF) B H
  have eG : G.prover H = H := bare_prover_self _ B H H rfl rfl rfl
  have eP : provG Z Zp Np cF B G H = (cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H :=
    bare_prover_self _ B H _ rfl rfl rfl
  have hn' : ∀ L ∈ G.first, L.place.kind ≠ KindName.frame := by
    intro L hL
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hL
    exact hn g hg
  have h₁' : RowsPinned (parOwn Zp mats) id (provG Z Zp Np cF B G H).first
      (descZ Zp Np cF).first.blocksInOrder.dropLast := by
    rw [eP]
    exact h₁
  have h₃' : RowsPinned (fun _ => none) id (provG Z Zp Np cF B G H).second
      (descZ Zp Np cF).second.blocksInOrder := by
    rw [eP]
    exact h₃
  have hI : ∀ (a b : LPFD.Full.XF × OnBytes.Flat.RecFull), a.1 = b.1 →
      H.trace i (LPFD.Full.instanceAsPlainRecord a) = H.trace i (LPFD.Full.instanceAsPlainRecord b) := by
    intro a b hab
    rw [hT]
    show (viaIndex (modelTrace Zp.p.X) i (LPFD.Full.instanceAsPlainRecord a)).map _ =
      (viaIndex (modelTrace Zp.p.X) i (LPFD.Full.instanceAsPlainRecord b)).map _
    unfold viaIndex modelTrace readTrace
    rw [ProofFile.instOf_at_frame, ProofFile.instOf_at_frame, hab]
  have hfam : onlineProversOfCommitter Z Zp Np cF silInst run₂ run₃ B (dataAtFiles flashProveData Z).P H =
      famG Z Zp Np cF run₂ run₃ B G H := by
    rw [famG_eq, eG]
  rw [hfam]
  ext τ
  refine (mem_hid_famG Z Zp Np cF run₂ run₃ B G H n _ _ τ).trans (Iff.trans ?_
    (mem_hid_famG Z Zp Np cF run₂ run₃ B G H n' _ _ τ).symm)
  have hB : ∀ ds : List Fmt.Drawn × List Fmt.Drawn,
      ProofFile.Honest.hidB (descZ Zp Np cF) (provG Z Zp Np cF B G H) i ρ
          (LPFD.Full.instanceAsPlainRecord (x, (protocolAtFiles Z).recOf i ρ e)) ds =
        ProofFile.Honest.hidB (descZ Zp Np cF) (provG Z Zp Np cF B G H) i ρ'
          (LPFD.Full.instanceAsPlainRecord (x, (protocolAtFiles Z).recOf i ρ' e')) ds := by
    intro ds
    unfold ProofFile.Honest.hidB
    rw [trace_provG Z Zp Np cF B G H, hI (x, (protocolAtFiles Z).recOf i ρ e) (x, (protocolAtFiles Z).recOf i ρ' e') rfl]
    cases ht : H.trace i (LPFD.Full.instanceAsPlainRecord (x, (protocolAtFiles Z).recOf i ρ' e')) with
    | none => rfl
    | some tr =>
      obtain ⟨c₁, c₂⟩ := session_stops_read_cells Z Zp Np cF run₂ run₃ B G H scope hr L hn'
        (parOwn Zp mats) id h₁' h₃'
        ⟨i, ρ, LPFD.Full.instanceAsPlainRecord (x, (protocolAtFiles Z).recOf i ρ e), tr⟩
        ⟨i, ρ', LPFD.Full.instanceAsPlainRecord (x, (protocolAtFiles Z).recOf i ρ' e'), tr⟩ rfl
      simp only [Option.any_some]
      rw [c₁, c₂]
  exact iff_of_eq (congrArg (fun t => t = true) (hB _))

/-- **Which messages the set holds, in both directions.** -/
theorem hid_iff_of_pin (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) {D : WholeD} {r : LPFD.Full.RunPF}
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (hn : ∀ g ∈ H.first, g.place.kind ≠ KindName.frame)
    (mats : ℕ → List (ℕ × String × ℕ))
    (h₁ : RowsPinned (parOwn Zp mats) id H.first (descZ Zp Np cF).first.blocksInOrder.dropLast)
    (h₃ : RowsPinned (fun _ => none) id H.second (descZ Zp Np cF).second.blocksInOrder)
    (n : ℕ) (i : FullSizeMatrix) (ρ : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed) (x : LPFD.Full.XF)
    (τ : Rho (protocolAtFiles Z).onlineBatch.loc.shape) :
    τ ∈ ((onlineProversOfCommitter Z Zp Np cF silInst run₂ run₃ B (dataAtFiles flashProveData Z).P H).at n).Hid (i, ρ, e)
        (x, (protocolAtFiles Z).recOf i ρ e) ↔
      ∃ tr, H.trace i (LPFD.Full.instanceAsPlainRecord (x, (protocolAtFiles Z).recOf i ρ e)) = some tr ∧
        ∃ A b C P d, (descZ Zp Np cF).first.blocksInOrder = A ++ b :: C ∧
          chainStopAt (some ⟨i, ρ, LPFD.Full.instanceAsPlainRecord (x, (protocolAtFiles Z).recOf i ρ e), tr⟩) A H.first []
            (drawsLo (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
              (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty (Iop.Rho.lo _ τ)).1 = none ∧
          parOwn Zp mats b.place = some P ∧
          ((drawsLo (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
              (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty
              (Iop.Rho.lo _ τ)).1.drop (drawsOf A)).head? = some d ∧
          (VerifiableInference.Desc.First.K8.Honest.leaves P.1 (ProofFile.Honest.K8.cellsAtOf tr P.2)
            d.trits.toArray).isSome = true := by
  let G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Cells X₀ Xh :=
    bareSides (descZ Zp Np cF) B H
  have eG : G.prover H = H := bare_prover_self _ B H H rfl rfl rfl
  have eP : provG Z Zp Np cF B G H = (cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H :=
    bare_prover_self _ B H _ rfl rfl rfl
  obtain ⟨hpub, hpin⟩ := (pin_iff _ _ _ _).1 h₁
  have hs := (pin_second_iff Zp Np cF id H.second).1 h₃
  have hfit : ∀ b ∈ (descZ Zp Np cF).first.blocksInOrder.dropLast, ∀ P, parOwn Zp mats b.place = some P →
      ProofFile.Honest.K8.smallFits P = true ∧ b.rounds.length = 1 := by
    intro b hb P hp
    have h := hpub b hb
    rw [hp] at h
    exact ⟨h.1, by rw [h.2]; rfl⟩
  have hlast : ∀ a, (descZ Zp Np cF).first.blocksInOrder.getLast? = some a →
      (H.first.find? fun h => h.place == a.place) = none ∧ parOwn Zp mats a.place = none := by
    intro a ha
    have hk : a.place.kind = KindName.frame := by
      have h := (k8_places_front Z Zp Np cF scope hr L).2
      rw [ha] at h
      exact Option.some.inj h
    refine ⟨?_, parOwn_other Zp mats a.place (by rw [hk]; decide)⟩
    cases hf : H.first.find? (fun h => h.place == a.place) with
    | none => rfl
    | some g =>
      have hg : g ∈ H.first := List.mem_of_find?_eq_some hf
      have hb' := List.find?_some hf
      have hp : g.place = a.place := eq_of_beq hb'
      exact absurd (by rw [hp]; exact hk) (hn g hg)
  have hfam : onlineProversOfCommitter Z Zp Np cF silInst run₂ run₃ B (dataAtFiles flashProveData Z).P H =
      famG Z Zp Np cF run₂ run₃ B G H := by
    rw [famG_eq, eG]
  have hpf : (provG Z Zp Np cF B G H).first = H.first := (bare_forgets _ B H _).1
  have hps : (provG Z Zp Np cF B G H).second = H.second := (bare_forgets _ B H _).2.2
  rw [hfam]
  refine (mem_hid_famG Z Zp Np cF run₂ run₃ B G H n _ _ τ).trans ?_
  unfold ProofFile.Honest.hidB
  rw [trace_provG Z Zp Np cF B G H, hpf, hps]
  show Option.any _ (H.trace i (LPFD.Full.instanceAsPlainRecord (x, (protocolAtFiles Z).recOf i ρ e))) = true ↔ _
  cases ht : H.trace i (LPFD.Full.instanceAsPlainRecord (x, (protocolAtFiles Z).recOf i ρ e)) with
  | none =>
    exact ⟨fun h => absurd h Bool.false_ne_true, fun ⟨tr, h, _⟩ => by cases h⟩
  | some tr =>
    simp only [Option.any_some, Bool.or_eq_true, beq_iff_eq]
    constructor
    · rintro (h | h)
      · exact ⟨tr, rfl, (hid_first_iff (cells := id) (Zp := Zp) (mats := mats) H.first
          (descZ Zp Np cF).first.blocksInOrder _ hpin hfit hlast [] _).1 h⟩
      · exact absurd h (silent_not_hid H.second (descZ Zp Np cF).second.blocksInOrder _ hs _ _)
    · rintro ⟨tr', e', h⟩
      obtain rfl := Option.some.inj e'
      exact .inl ((hid_first_iff (cells := id) (Zp := Zp) (mats := mats) H.first
        (descZ Zp Np cF).first.blocksInOrder _ hpin hfit hlast [] _).2 h)

end

end P1K8

#print axioms P1K8.hid_zero_tied
#print axioms P1K8.window_cleared_of_pin
#print axioms P1K8.hid_iff_of_pin
#print axioms P1K8.hid_reads_no_randomness
#print axioms P1K8.bare_prover_self
#print axioms P1K8.window_of_pin
#print axioms P1K8.window_number_of_pin
