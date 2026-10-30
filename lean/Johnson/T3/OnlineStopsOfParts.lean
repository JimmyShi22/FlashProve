-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/T3/OnlineStopsOfParts.lean: the number of the online private stops, as the sum of what the parts state.

1.  online_hid_of_parts: the private stops of the online prover, at the valid pairs of ZeroKnowledgeOnServedRequests, are at most z₁ + z₃, from each part's own bound.
2.  onlinePrivateStopsAt: the number: the stated shares of the first and the last chain. It names no input.
3.  online_hid_at_files: the same at that number, for public files in scope, from one ready run and no row of kind frame in the first chain.
4.  online_stops_at_term: so the online prover under AtHonest meets PrivateStopsAtMost at that number.
5.  Nothing here says that any part meets its bound, or how large the number is.
-/
import Johnson.T3.OwedOfKinds
import Johnson.FrontRoad.SessionStopsAtFiles

set_option autoImplicit false
set_option maxRecDepth 100000
attribute [-instance] Inst.Model.Scl.ref
noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open Iop Prob AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.AtFiles AtPublicFiles.Committed
open ProofFile.Honest (Prover ProverCoinCounts Sides Local AtHonest OnlineProverWithDescription OnlineProverParts Coins Ready ready Face StopsFit)
open OnBytes.FrontRoad (PartsHeld sharesSum hidSmall_of_parts stopsFit_provG dropLast_of_cut)
open VerifiableInference.Desc (Chain KindName Block)
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD)
open LPFD.Full (instanceAsPlainRecord)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed committerCoinCountLessOne)
open P5J

local instance (priority := high) onlineStopsOfPartsInstance1 : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) onlineStopsOfPartsInstance2 {α : Type} [Inhabited α] : Nonempty α := ⟨default⟩

variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
  (run₃ : R₃ → ByteArray) {Tr X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)

/-- **The number**: the shares that the parts of the first chain, without its last member, and of the last chain state. -/
def onlinePrivateStopsAt : ℝ≥0∞ :=
  sharesSum (provG Z Zp Np cF B G H).first (descZ Zp Np cF).first.blocksInOrder.dropLast (dataZ Z).ds₁ +
    sharesSum (provG Z Zp Np cF B G H).second (descZ Zp Np cF).second.blocksInOrder (dataZ Z).ds₃

/-- **From each part's bound to the private stops of the online prover, at the statement's valid pairs.** -/
theorem online_hid_of_parts {pre₁ : List (Block (descZ Zp Np cF).S₁ (descZ Zp Np cF).Cl)}
    {e₁ : Block (descZ Zp Np cF).S₁ (descZ Zp Np cF).Cl}
    (Sf : StopsFit (descZ Zp Np cF) (provG Z Zp Np cF B G H) (dataZ Z) pre₁ e₁)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    (P : Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst Tr → Prop) (z₁ z₃ : ℝ≥0∞)
    (hP : ∀ w a, rangeAtFiles w.1 → (protocolAtFiles Z).validB (ServedRequest committerCoinCountLessOne Z hr) w a →
      ∀ tr, H.trace w.1 (instanceAsPlainRecord a) = some tr → P ⟨w.1, w.2.1, instanceAsPlainRecord a, tr⟩)
    (p₁ : PartsHeld P Face.own.sees (provG Z Zp Np cF B G H).first pre₁ (dataZ Z).ds₁)
    (s₁ : sharesSum (provG Z Zp Np cF B G H).first pre₁ (dataZ Z).ds₁ ≤ z₁)
    (p₃ : PartsHeld P Face.own.sees (provG Z Zp Np cF B G H).second (descZ Zp Np cF).second.blocksInOrder
      (dataZ Z).ds₃)
    (s₃ : sharesSum (provG Z Zp Np cF B G H).second (descZ Zp Np cF).second.blocksInOrder (dataZ Z).ds₃ ≤ z₃) :
    HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
      (fun _ w a => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validB (ServedRequest committerCoinCountLessOne Z hr) w a) (z₁ + z₃) :=
  hidSmall_of_parts Z Zp Np cF run₂ run₃ B G H Sf _ P z₁ z₃
    (fun _ w a h => hP w a h.1 h.2) p₁ s₁ p₃ s₃

/-- **The same at the number, for public files in scope.** -/
theorem online_hid_at_files (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {x : ProofFile.Inst} {k : Coins B}
    {R : Ready FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh}
    (hR : ready (descZ Zp Np cF) B (provG Z Zp Np cF B G H) w₀ rc x k = .ok R)
    (hn : ∀ L ∈ G.first, L.place.kind ≠ KindName.frame)
    (P : Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst Tr → Prop)
    (hP : ∀ w a, rangeAtFiles w.1 → (protocolAtFiles Z).validB (ServedRequest committerCoinCountLessOne Z hr) w a →
      ∀ tr, H.trace w.1 (instanceAsPlainRecord a) = some tr → P ⟨w.1, w.2.1, instanceAsPlainRecord a, tr⟩)
    (p₁ : PartsHeld P Face.own.sees (provG Z Zp Np cF B G H).first
      (descZ Zp Np cF).first.blocksInOrder.dropLast (dataZ Z).ds₁)
    (p₃ : PartsHeld P Face.own.sees (provG Z Zp Np cF B G H).second (descZ Zp Np cF).second.blocksInOrder
      (dataZ Z).ds₃) :
    HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
      (fun _ w a => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validB (ServedRequest committerCoinCountLessOne Z hr) w a)
      (onlinePrivateStopsAt Z Zp Np cF B G H) := by
  obtain ⟨pre, e, cut, -, Sf⟩ := stopsFit_provG Z Zp Np cF B G H scope hr live L hR hn
  obtain rfl := dropLast_of_cut cut
  exact online_hid_of_parts Z Zp Np cF run₂ run₃ B G H Sf hr P _ _ hP p₁ le_rfl p₃ le_rfl

section Term
variable {Z Zp Np cF run₂ run₃}
variable {D : WholeD} {r : LPFD.Full.RunPF}
  {x : VerifiableInference.Desc.First.Look.Place} {Fl : ProofFile.Honest.OnlineProverParts FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Tr X₀ Xh}
  {A : OnlineProverWithDescription FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Tr X₀ Xh} {G' : Sides A.F A.B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh}
  {more : List (String × Bool)}

/-- **The online prover of the term meets the private stops' line at the number.** -/
theorem online_stops_at_term (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (hd : AtHonest OnBytes.secondHashFunction Z D r Zp Np cF x Fl A G' more)
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {xx : ProofFile.Inst} {k : Coins A.B}
    {R : Ready FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh}
    (hR : ready (descZ Zp Np cF) A.B (provG Z Zp Np cF A.B (sidesAt hd.isTerm.2 G') A.H) w₀ rc xx k = .ok R)
    (hn : ∀ L ∈ (sidesAt hd.isTerm.2 G').first, L.place.kind ≠ KindName.frame)
    (Pr : Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst Tr → Prop)
    (hP : ∀ w a, rangeAtFiles w.1 → (protocolAtFiles Z).validB (ServedRequest committerCoinCountLessOne Z hr) w a →
      ∀ tr, A.H.trace w.1 (instanceAsPlainRecord a) = some tr → Pr ⟨w.1, w.2.1, instanceAsPlainRecord a, tr⟩)
    (p₁ : PartsHeld Pr Face.own.sees (provG Z Zp Np cF A.B (sidesAt hd.isTerm.2 G') A.H).first
      (descZ Zp Np cF).first.blocksInOrder.dropLast (dataZ Z).ds₁)
    (p₃ : PartsHeld Pr Face.own.sees (provG Z Zp Np cF A.B (sidesAt hd.isTerm.2 G') A.H).second
      (descZ Zp Np cF).second.blocksInOrder (dataZ Z).ds₃)
    (hT : Honest (protocolAtFiles Z).offline (FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed))
    (hL : Honest (protocolAtFiles Z).link (FullSizeMatrix × ((protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) × ((protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed)))
    (n : ℕ) :
    PrivateStopsAtMost
      ((HonestProvers.ofThreeProvers (proversOf hT hL (onlineProversOfCommitter Z Zp Np cF silInst run₂ run₃ A.B
                (dataAtFiles flashProveData Z).P A.H))).onlineAtCopy n)
      (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validB (ServedRequest committerCoinCountLessOne Z hr) w y)
      (workAtFiles Z).online (onlinePrivateStopsAt Z Zp Np cF A.B (sidesAt hd.isTerm.2 G') A.H) := by
  have h := online_hid_at_files Z Zp Np cF run₂ run₃ A.B (sidesAt hd.isTerm.2 G') A.H scope hr live
    hd.laid hR hn Pr hP p₁ p₃
  rw [famG_sidesAt Z Zp Np cF run₂ run₃ hd] at h
  exact online_stops_of_honest Z Zp Np cF run₂ run₃ hr hd h hT hL n

end Term

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.onlinePrivateStopsAt
#print axioms VerifiableInference.Compilation.online_hid_of_parts
#print axioms VerifiableInference.Compilation.online_hid_at_files
#print axioms VerifiableInference.Compilation.online_stops_at_term
