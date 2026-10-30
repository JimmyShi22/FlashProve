-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/WindowAtTerm.lean: the private stop of the online honest prover, and a bound on its
measure. Everything here is at public files in scope, which the reader reads and which pass the
library's test protocolDataWellFormed.

1. The smallness test asks that every combination of a row of hidden cells with a drawn matrix lies
   in a window (leaves, Johnson/Desc/K8/Honest/Window.lean). Where one leaves it the honest prover
   stops. This stop reads the hidden cells, so it is a second stop of the frame: the field hid of
   the kind's one part (smallHid, Honest/K8/Part.lean). It reaches the set Hid of the prover through
   chainStopAt (Honest/Rule.lean) and hidB (Honest/Record.lean). No new name is made for it.
2. The prover here is onlineProver of E2E/TheHonestProver.lean at the copy's number n, and, in the
   statements at the value, the honest provers under refuseUnserved at a served request.
3. PrivateStopsAtMost Z z: at every copy's number, index, table randomness, out-of-domain seed and
   request of the relation RyesZ Z, the verifier's messages at which Hid holds have measure at most
   z, over uniform messages. All but the messages are fixed first. privateNumber Z is its supremum,
   at messages that are not cleared.
4. The measure is over uniform verifier messages: an honest verifier's number. Of the private input
   the set reads the index alone, through the trace: at one index and one request it is one set at
   every table randomness, seed and copy's number (window_set_reads_no_randomness). Through «no stop
   in front» it reads earlier rounds' challenges too. Where the prover has no trace, Hid is empty by
   its definition: that a served request has a trace is another statement.
5. window_at_term: for one request the measure is at most 2 ^ (-174): a bound; the target of the
   format's gate on range checks (Johnson/P1K8R/WindowNumber.lean). Its one premise beside the
   public tests is that the maker returns (AtFullSide/K12/MakerReturnsAtLive.lean proves it in the
   side library). It asks nothing of a run: the set lies inside the set of a prover with the 25
   pinned halves alone (Johnson/P1K8R/WindowFree.lean).
6. window_set_iff: which messages the set holds, in both directions: the stop fires just where a
   combination leaves its window, with no stop in front.
7. At the value: private_stops_at_value, at the honest provers under refuseUnserved, at a served
   request; private_stops_cleared_at_value: at messages whose bits of proof of work are 0;
   window_stopsSmall: in the letters of the compiler's premise StopsSmall, field B; hid_small_at_rows:
   the debt on the private stops in the list of the online prover's debts.
8. return_pins: at the first chain without its last member and at the second chain, every part but
   the smallness test's has no second stop. So the bound is a bound on all of Hid while that stands.
9. This file's bound counts toward neither a kind's acceptance nor its simulator. Nothing here says
   that a proof is accepted outside these sets, or anything on soundness.
-/
import E2E.TheHonestProver
import Johnson.P1K8R.PinAtTerm
import Johnson.P1K8R.PinAtFill
import Johnson.P1K8R.WindowFree
import Johnson.HonestTrace.PlanOwnersInScope
import Johnson.ToldDescR.PureChainOfOpen
import Johnson.Prover.All.CompleteAsIOPForTheCompiler
import E2E.CompleteAsIOPAtFiles

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.AtFiles.HonestTerm
open Iop Prob AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed AtPublicFiles.Cut
open ProofFile.Honest (Ready ready Coins Placed HLot Local firstOf onlineProverFromPublicFiles OnlineProverWithDescription chainStopAt)
open ProofFile.Honest.Term (OnlineReturn onlineMaker onlineFilling matrixInput tableCoins)
open OnBytes.FrontRoad (parOwn RowsPinned PinHalvesAt modelAt viaIndex modelTrace pin_iff
  pin_second_iff)
open OnBytes.HonestTrace (cellsC)
open TypedOracleCompiler.Iop (RoundsQueryLayout)
open TypedOracleCompiler.Compile.Batch.Cms (wBC)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (protocolDataWellFormed flashProveData allZeroDigest)
open FlashProve (dataAtFiles)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (KindName)
open P5J
open P1K8 (windowBound)

attribute [-instance] Inst.Model.Scl.ref

local instance (priority := high) nonemptyPadZ_windowAtTerm : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

local instance (priority := high) : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) : Inhabited RunValue := ⟨fun _ => 0⟩

/-- **The online prover's private stops have measure at most z**, at every copy's number, every
index, table randomness and out-of-domain seed, and every request of the relation. -/
def PrivateStopsAtMost (Z : PublicFiles) (z : ℝ≥0∞) : Prop :=
  ∀ (n : ℕ) (i : FullSizeMatrix) (r : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed) (x : XF), RyesZ Z i x →
    prRho (((onlineProver Z).at n).Hid (i, r, e) (x, (protocolAtFiles Z).recOf i r e)) ≤ z

variable {Z : PublicFiles} {A : OnlineReturn Z}

/-- The blank ground of what the maker returned. -/
theorem return_ground (hA : onlineMaker Z = .ok A) :
    ProofFile.blankBy ProofFile.pureRoad.links A.Z = some A.G :=
  (ProofFile.Honest.atPure_ok hA).2.1

/-- **The trace of what the maker returned is the model's.** -/
theorem return_trace (hA : onlineMaker Z = .ok A) :
    A.H.trace = modelAt A.Z.p.X (cellsC A.Z.p.X) := by
  rw [(ProofFile.Honest.atPure_ok hA).2.2.2.1]
  funext M ξ
  show (VerifiableInference.OnPublicFiles.Flat.indexOf M).bind
      (fun i => ProofFile.Honest.fullIn.trace A.Z i ξ) =
    (viaIndex (modelTrace A.Z.p.X) M ξ).map (cellsC A.Z.p.X)
  unfold viaIndex
  cases VerifiableInference.OnPublicFiles.Flat.indexOf M with
  | none => rfl
  | some i => rfl

/-- The first chain's sides of what the maker returned. -/
theorem return_first (hA : onlineMaker Z = .ok A) :
    A.H.first = firstOf A.Z A.G (onlineFilling Z).lots :=
  (ProofFile.Honest.atPure_ok hA).2.2.2.2.2.2.2.1

/-- The last chain's sides of what the maker returned. -/
theorem return_second (hA : onlineMaker Z = .ok A) :
    A.H.second = (onlineFilling Z).second A.Z A.G :=
  (ProofFile.Honest.atPure_ok hA).2.2.2.2.2.2.2.2.2.1

/-- **The filling's lots, read through, sorted for the pin.** -/
theorem fill_lots (L : HLot (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst ProofFile.Honest.Cells)
    (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst ProofFile.Honest.Cells) Unit) (hL : L ∈ (onlineFilling Z).lots) :
    L = HLot.thru (Local.thru id (tableCoins Z)) (Local.thru id (tableCoins Z)) P1K8.termSmall ∨
      (P1K8.LotQuiet L ∧ ∀ Zq G, ∀ x ∈ L.halves Zq G, x.place.kind ≠ KindName.K8) := by
  obtain ⟨M, hM, rfl⟩ := List.mem_map.1 hL
  rcases P1K8.term_lots matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref ProofFile.Honest.openHonest
    M hM with rfl | ⟨hq, hk⟩
  · exact .inl rfl
  · refine .inr ⟨P1K8.K10K12.lotThru_quiet _ _ hq, fun Zq G x hx => ?_⟩
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact hk Zq G y hy

/-- **The pins at what the maker returned.** -/
theorem return_pins {pp : Inst.Model.ScalesAndPolicy} (scope : InScope Z = true) (hr : readFiles Z = .ok pp)
    (hA : onlineMaker Z = .ok A) {Np : H2U.Places4}
    {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl} {D : WholeD} {r : LPFD.Full.RunPF}
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r A.Z Np cF) :
    RowsPinned (parOwn A.Z fun l => ProofFile.Honest.K3.matsOwn A.G.W l) id A.H.first
        (descZ A.Z Np cF).first.blocksInOrder.dropLast ∧
      RowsPinned (fun _ => none) id A.H.second (descZ A.Z Np cF).second.blocksInOrder := by
  have hG := return_ground hA
  refine ⟨(pin_iff _ _ _ _).2 ⟨P1K8.pinPublic_own scope hr L hG, ?_⟩, ?_⟩
  · rw [return_first hA]
    refine P1K8.pinHalves_of_lots hG _
      (HLot.thru (Local.thru id (tableCoins Z)) (Local.thru id (tableCoins Z)) P1K8.termSmall)
      (List.mem_map_of_mem (P1K8.term_small_mem matrixInput OnBytes.secondHashFunction
        OnBytes.HonestTrace.Sz.ref ProofFile.Honest.openHonest))
      (P1K8.smallForm_thru id (tableCoins Z) _ _ (fun _ _ => rfl)
        fun l Xl h => P1K8.matsOwn_fits scope hr L hG h)
      (fun M hM => (fill_lots M hM).imp id fun h => h.1)
      (fun M hM hne => ((fill_lots M hM).resolve_left hne).2 A.Z A.G)
      _ (P1K8.place_at_member scope hr L hG) ?_
    intro b hb hp hk
    obtain ⟨P, hP, -⟩ := OnBytes.FrontRoad.pin_first_public Z A.Z Np cF scope hr L _ b hb hk
    rw [hp] at hP
    cases hP
  · refine (pin_second_iff A.Z Np cF id A.H.second).2 ?_
    rw [return_second hA]
    intro b _ g hg p hp
    exact P1K8.K10K12.through_second_quiet id (tableCoins Z) matrixInput.dummy _
      (fun Zq G x hx => P1K8.K10K12.secondW_quiet _ _ _ _ Zq G x hx) A.Z A.G g
      (List.mem_of_find?_eq_some hg) p hp

/-- No half of what the maker returned stands at a place of the kind frame. -/
theorem return_no_frame (hA : onlineMaker Z = .ok A) :
    ∀ g ∈ A.H.first, g.place.kind ≠ KindName.frame := by
  intro g hg
  rw [return_first hA] at hg
  obtain ⟨M, hM, hx⟩ := List.mem_flatMap.1 hg
  obtain ⟨M₀, hM₀, rfl⟩ := List.mem_map.1 hM
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  exact P1K8.term_no_frame matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref
    ProofFile.Honest.openHonest M₀ hM₀ A.Z A.G y hy

/-- The online prover is the family at what the maker returned: the definition, unfolded at these
three returns. That these returns hold wherever the files pass is another statement. -/
theorem online_at_return (hA : onlineMaker Z = .ok A) {Np : H2U.Places4}
    {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl} (hNp : H2U.placesOfMade A.Z.made = .ok Np)
    (hcF : ProofFile.onlineFirstChainAt A.Z = .ok cF) : onlineProver Z = onlineProverAt A Np cF := by
  unfold onlineProver
  rw [hA]
  dsimp only
  rw [hNp, hcF]

/-- **The set reads no table randomness, no seed and no copy's number.** -/
theorem window_set_reads_no_randomness {pp : Inst.Model.ScalesAndPolicy} (scope : InScope Z = true)
    (hr : readFiles Z = .ok pp) (hA : onlineMaker Z = .ok A) {Np : H2U.Places4}
    {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl} (hNp : H2U.placesOfMade A.Z.made = .ok Np)
    (hcF : ProofFile.onlineFirstChainAt A.Z = .ok cF) {D : WholeD} {r : LPFD.Full.RunPF}
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r A.Z Np cF) (n n' : ℕ) (i : FullSizeMatrix)
    (ρ ρ' : (protocolAtFiles Z).EncodingRandomness) (e e' : (protocolAtFiles Z).OutOfDomainSeed) (x : XF) :
    ((onlineProver Z).at n).Hid (i, ρ, e) (x, (protocolAtFiles Z).recOf i ρ e) =
      ((onlineProver Z).at n').Hid (i, ρ', e') (x, (protocolAtFiles Z).recOf i ρ' e') := by
  obtain ⟨h₁, h₃⟩ := return_pins scope hr hA L
  rw [online_at_return hA hNp hcF]
  exact P1K8.hid_reads_no_randomness Z A.Z Np cF runValueBytes runValueBytes A.B A.H scope hr L
    (return_no_frame hA) _ h₁ h₃ (return_trace hA) n n' i ρ ρ' e e' x

/-- **Which messages the set holds, in both directions**: where the request has a trace, at some
member of the first chain a combination leaves its window, with no stop in front. -/
theorem window_set_iff {pp : Inst.Model.ScalesAndPolicy} (scope : InScope Z = true)
    (hr : readFiles Z = .ok pp) (hA : onlineMaker Z = .ok A) {Np : H2U.Places4}
    {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl} (hNp : H2U.placesOfMade A.Z.made = .ok Np)
    (hcF : ProofFile.onlineFirstChainAt A.Z = .ok cF) {D : WholeD} {r : LPFD.Full.RunPF}
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r A.Z Np cF) (n : ℕ) (i : FullSizeMatrix)
    (ρ : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed) (x : XF) (τ : Rho (protocolAtFiles Z).onlineBatch.loc.shape) :
    τ ∈ ((onlineProver Z).at n).Hid (i, ρ, e) (x, (protocolAtFiles Z).recOf i ρ e) ↔
      ∃ tr, A.H.trace i (LPFD.Full.instanceAsPlainRecord (x, (protocolAtFiles Z).recOf i ρ e)) = some tr ∧
        ∃ Bf b C P d, (descZ A.Z Np cF).first.blocksInOrder = Bf ++ b :: C ∧
          chainStopAt (some ⟨i, ρ, LPFD.Full.instanceAsPlainRecord (x, (protocolAtFiles Z).recOf i ρ e), tr⟩) Bf A.H.first []
            (ProofFile.Honest.drawsLo (_root_.Run.ckP .two) (dataZ Z)
              (OnBytes.Flat.front₀ (dataAtFiles flashProveData Z).G.z₀.2)
              (OnBytes.Flat.join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty
              (Iop.Rho.lo _ τ)).1 = none ∧
          parOwn A.Z (fun l => ProofFile.Honest.K3.matsOwn A.G.W l) b.place = some P ∧
          ((ProofFile.Honest.drawsLo (_root_.Run.ckP .two) (dataZ Z)
              (OnBytes.Flat.front₀ (dataAtFiles flashProveData Z).G.z₀.2)
              (OnBytes.Flat.join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty
              (Iop.Rho.lo _ τ)).1.drop (P1K8.drawsOf Bf)).head? = some d ∧
          (VerifiableInference.Desc.First.K8.Honest.leaves P.1 (ProofFile.Honest.K8.cellsAtOf tr P.2)
            d.trits.toArray).isSome = true := by
  obtain ⟨h₁, h₃⟩ := return_pins scope hr hA L
  rw [online_at_return hA hNp hcF]
  exact P1K8.hid_iff_of_pin Z A.Z Np cF runValueBytes runValueBytes A.B A.H scope hr L
    (return_no_frame hA) _ h₁ h₃ n i ρ e x τ

/-- What the public tests give at what the maker returned. -/
theorem return_laid (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hA : onlineMaker Z = .ok A) :
    ∃ (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl) (D : WholeD)
      (r : LPFD.Full.RunPF), LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r A.Z Np cF ∧
      H2U.placesOfMade A.Z.made = .ok Np ∧ ProofFile.onlineFirstChainAt A.Z = .ok cF := by
  obtain ⟨Zp, Np, cF, L⟩ := laid_of_live Z live
  obtain rfl : Zp = A.Z := Except.ok.inj (L.pub.symm.trans (ProofFile.Honest.atPure_ok hA).1)
  obtain ⟨Bs, base, O⟩ := L.opened
  exact ⟨Np, cF, _, _, L, L.places, ToldDesc.pureChainAt_of_open O⟩

/-- The lists of matrices of the filling are the trace's, below 25. -/
theorem return_mats {pp : Inst.Model.ScalesAndPolicy} (scope : InScope Z = true) (hr : readFiles Z = .ok pp)
    (hA : onlineMaker Z = .ok A) {Np : H2U.Places4}
    {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl} {D : WholeD} {r : LPFD.Full.RunPF}
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r A.Z Np cF) :
    ∀ l < 25, ProofFile.Honest.K3.matsOwn A.G.W l = OnBytes.HonestTrace.matsOf A.Z.p.X l := by
  intro l hl
  rw [ProofFile.Law.blankBy_W (return_ground hA)]
  exact OnBytes.HonestTrace.planOwners_in_scope scope hr
    (OnBytes.FrontRoad.publicOf_laid Z A.Z Np cF L) l hl

/-- **THE PRIVATE STOPS AT THE TERM.** -/
theorem window_at_term {pp : Inst.Model.ScalesAndPolicy} (scope : InScope Z = true)
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (hA : onlineMaker Z = .ok A) :
    PrivateStopsAtMost Z (ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ))) := by
  intro n i ρ e x hx
  obtain ⟨Np, cF, D, r, L, hNp, hcF⟩ := return_laid live hA
  obtain ⟨h₁, h₃⟩ := return_pins scope hr hA L
  rw [online_at_return hA hNp hcF]
  exact P1K8.window_free_of_pin Z A.Z Np cF runValueBytes runValueBytes A.B A.H scope hr live L
    (return_no_frame hA) _ (return_mats scope hr hA L) h₁ h₃ (return_trace hA) n i ρ e x hx

/-- **The measure is the same at cleared messages**, at every digest and further reading. -/
theorem window_zero {pp : Inst.Model.ScalesAndPolicy} (scope : InScope Z = true)
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (hA : onlineMaker Z = .ok A) (c₀ : VerifiableInference.Digest) (m₀ : List (Iop.Dig 256))
    (n : ℕ) (i : FullSizeMatrix) (ρ : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed) (x : XF) (hx : RyesZ Z i x) :
    prRho {τ | RoundsQueryLayout.zero (protocolAtFiles Z).onlineBatch.loc.shape (protocolAtFiles Z).onlineBatch.ann
        (wBC ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀).W).sh τ ∈
      ((onlineProver Z).at n).Hid (i, ρ, e) (x, (protocolAtFiles Z).recOf i ρ e)} ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ)) := by
  have hb := window_at_term scope hr live hA n i ρ e x hx
  obtain ⟨Np, cF, D, r, L, hNp, hcF⟩ := return_laid live hA
  have hz := P1K8.hid_zero_tied Z A.Z Np cF runValueBytes runValueBytes A.B A.H c₀ m₀ n (i, ρ, e)
    (x, (protocolAtFiles Z).recOf i ρ e)
  rw [online_at_return hA hNp hcF] at hb ⊢
  have hs : {τ | RoundsQueryLayout.zero (protocolAtFiles Z).onlineBatch.loc.shape (protocolAtFiles Z).onlineBatch.ann
        (wBC ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀).W).sh τ ∈
      ((onlineProverAt A Np cF).at n).Hid (i, ρ, e) (x, (protocolAtFiles Z).recOf i ρ e)} =
      ((onlineProverAt A Np cF).at n).Hid (i, ρ, e) (x, (protocolAtFiles Z).recOf i ρ e) := Set.ext hz
  rw [hs]
  exact hb

/-- **The same in the form of the statements on completeness.** -/
theorem window_cleared {pp : Inst.Model.ScalesAndPolicy} (scope : InScope Z = true)
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (hA : onlineMaker Z = .ok A) (n : ℕ) (i : FullSizeMatrix) (ρ : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed) (x : XF)
    (hx : RyesZ Z i x) :
    chanceAtPassing (workAtFiles Z).online
      (fun τ => τ ∈ ((onlineProver Z).at n).Hid (i, ρ, e) (x, (protocolAtFiles Z).recOf i ρ e)) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ)) :=
  window_zero scope hr live hA allZeroDigest [] n i ρ e x hx

/-- **In the letters of the compiler's premise StopsSmall, field B**, at the honest provers' record,
at every digest and further reading. -/
theorem window_stopsSmall {pp : Inst.Model.ScalesAndPolicy} (scope : InScope Z = true)
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (hA : onlineMaker Z = .ok A) (P : Parts Z) (c₀ : VerifiableInference.Digest)
    (m₀ : List (Iop.Dig 256)) (n : ℕ) (i : FullSizeMatrix) (ρ : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed) (x : XF)
    (hx : RyesZ Z i x) :
    prRho {τ | RoundsQueryLayout.zero (protocolAtFiles Z).onlineBatch.loc.shape (protocolAtFiles Z).onlineBatch.ann
        (wBC ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀).W).sh τ ∈
      (OnBytes.WholeKey.sessionAt (honestProvers Z P) n).Hid (i, ρ, e)
        (x, (protocolAtFiles Z).recOf i ρ e)} ≤ ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ)) :=
  window_zero scope hr live hA c₀ m₀ n i ρ e x hx

/-- **The private number**: the supremum of the measure over the copy's number, index, table
randomness, seed and request of the relation, at messages that are not cleared, beneath
refuseUnserved. -/
def privateNumber (Z : PublicFiles) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (i : FullSizeMatrix) (r : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed) (x : XF) (_ : RyesZ Z i x),
    prRho (((onlineProver Z).at n).Hid (i, r, e) (x, (protocolAtFiles Z).recOf i r e))

/-- A bound at every point is a bound on the supremum. -/
theorem privateNumber_le {z : ℝ≥0∞} (h : PrivateStopsAtMost Z z) : privateNumber Z ≤ z :=
  iSup_le fun n => iSup_le fun i => iSup_le fun r => iSup_le fun e => iSup_le fun x =>
    iSup_le fun hx => h n i r e x hx

/-- **The private number at the term.** -/
theorem privateNumber_at_term {pp : Inst.Model.ScalesAndPolicy} (scope : InScope Z = true)
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (hA : onlineMaker Z = .ok A) :
    privateNumber Z ≤ ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ)) :=
  privateNumber_le (window_at_term scope hr live hA)

/-- The provers under refuseUnserved hold at a served request the set beneath. -/
theorem value_hid (P : Parts Z) {Served : FullSizeMatrix → XF → Prop} (n : ℕ)
    (w : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) (y : XF × (protocolAtFiles Z).Rec) (hs : Served w.1 y.1) :
    (((OnBytes.Prover.ofRecs (honestProvers Z P)).refuseUnserved Served).onlineAtCopy n).Hid w y =
      ((onlineProver Z).at n).Hid w y := by
  show {_ρ | ¬ Served w.1 y.1} ∪ _ = _
  ext τ
  constructor
  · rintro (h | h)
    · exact absurd hs h
    · exact h
  · exact Or.inr

/-- **At the value**: the honest provers under refuseUnserved, at a copy's number, at the requests
of a relation inside RyesZ Z. -/
theorem private_stops_at_value {pp : Inst.Model.ScalesAndPolicy} (scope : InScope Z = true)
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (hA : onlineMaker Z = .ok A) (P : Parts Z) {Served : FullSizeMatrix → XF → Prop}
    (hS : ∀ i x, Served i x → RyesZ Z i x) (n : ℕ) (w : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed)
    (y : XF × (protocolAtFiles Z).Rec) (hv : (protocolAtFiles Z).validB Served w y) :
    prRho ((((OnBytes.Prover.ofRecs (honestProvers Z P)).refuseUnserved Served).onlineAtCopy
      n).Hid w y) ≤ ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ)) := by
  obtain ⟨i, ρ, e⟩ := w
  obtain ⟨x, a⟩ := y
  obtain ⟨ea, hs⟩ := hv
  obtain rfl : a = (protocolAtFiles Z).recOf i ρ e := ea
  rw [value_hid P n _ _ hs]
  exact window_at_term scope hr live hA n i ρ e x (hS i x hs)

/-- **The same at cleared messages**: the form in which the statements on completeness and zero
knowledge read it. -/
theorem private_stops_cleared_at_value {pp : Inst.Model.ScalesAndPolicy} (scope : InScope Z = true)
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (hA : onlineMaker Z = .ok A) (P : Parts Z) {Served : FullSizeMatrix → XF → Prop}
    (hS : ∀ i x, Served i x → RyesZ Z i x) (n : ℕ) (w : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed)
    (y : XF × (protocolAtFiles Z).Rec) (hv : (protocolAtFiles Z).validB Served w y) :
    chanceAtPassing (workAtFiles Z).online
      (fun τ => τ ∈ (((OnBytes.Prover.ofRecs (honestProvers Z P)).refuseUnserved
        Served).onlineAtCopy n).Hid w y) ≤ ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ)) := by
  obtain ⟨i, ρ, e⟩ := w
  obtain ⟨x, a⟩ := y
  obtain ⟨ea, hs⟩ := hv
  obtain rfl : a = (protocolAtFiles Z).recOf i ρ e := ea
  simp only [value_hid P n _ _ hs]
  exact window_cleared scope hr live hA n i ρ e x (hS i x hs)

/-- **The debt on the private stops in the list of the online prover's debts**, at rows whose parts
are the prover's own. -/
theorem hid_small_at_rows {pp : Inst.Model.ScalesAndPolicy} (scope : InScope Z = true)
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (hA : onlineMaker Z = .ok A) {Np : H2U.Places4}
    {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl} (hNp : H2U.placesOfMade A.Z.made = .ok Np)
    (hcF : ProofFile.onlineFirstChainAt A.Z = .ok cF)
    (G : ProofFile.Honest.Sides (descZ A.Z Np cF) A.B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness OnBytes.TableKey
      ProofFile.Honest.Cells Unit Unit)
    (hG : G.prover A.H = A.H) {Relation : FullSizeMatrix → XF → Prop}
    (hb : ∀ i x, Relation i x → RyesZ Z i x) :
    HidSmall (famG Z A.Z Np cF runValueBytes runValueBytes A.B G A.H)
      (fun n w a => TiedYes Z A.Z Np cF runValueBytes runValueBytes A.B G A.H Relation n w
        (LPFD.Full.instanceAsPlainRecord a))
      (ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ))) := by
  rintro n ⟨i, ρ, e⟩ a ⟨⟨x', hx', ea⟩, -⟩
  have ef : ((famG Z A.Z Np cF runValueBytes runValueBytes A.B G A.H).at n).Hid (i, ρ, e) a =
      ((famG Z A.Z Np cF runValueBytes runValueBytes A.B G A.H).at n).Hid (i, ρ, e)
        (x', (protocolAtFiles Z).recOf i ρ e) := by
    rw [OnBytes.FrontRoad.hid_famG_eq, OnBytes.FrontRoad.hid_famG_eq, ea]
    rfl
  rw [ef, famG_eq, hG]
  have h := window_at_term scope hr live hA n i ρ e x' (hb i x' hx')
  rw [online_at_return hA hNp hcF] at h
  exact h

end AtPublicFiles.AtFiles.HonestTerm

#print axioms AtPublicFiles.AtFiles.HonestTerm.window_set_reads_no_randomness
#print axioms AtPublicFiles.AtFiles.HonestTerm.return_trace
#print axioms AtPublicFiles.AtFiles.HonestTerm.return_pins
#print axioms AtPublicFiles.AtFiles.HonestTerm.window_set_reads_no_randomness
#print axioms AtPublicFiles.AtFiles.HonestTerm.window_set_iff
#print axioms AtPublicFiles.AtFiles.HonestTerm.window_at_term
#print axioms AtPublicFiles.AtFiles.HonestTerm.window_zero
#print axioms AtPublicFiles.AtFiles.HonestTerm.window_cleared
#print axioms AtPublicFiles.AtFiles.HonestTerm.window_stopsSmall
#print axioms AtPublicFiles.AtFiles.HonestTerm.privateNumber_at_term
#print axioms AtPublicFiles.AtFiles.HonestTerm.private_stops_at_value
#print axioms AtPublicFiles.AtFiles.HonestTerm.private_stops_cleared_at_value
#print axioms AtPublicFiles.AtFiles.HonestTerm.hid_small_at_rows
