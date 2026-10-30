-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/T3/OnlineK8AtBase.lean: an implication: zero knowledge of the protocol's honest provers from the base filling, with the number of the private stops named: the parts' shares at the term, where only the kind K8
has a second stop and K8 meets its debt. The premises are stated at the term: its sides are the base's read through. No value of any premise is given here: this file proves zero knowledge of nothing.
-/
import AtFullSide.T3.AtNamedFiles
import Johnson.T3.OnlineStopsOfK8

set_option autoImplicit false
set_option maxRecDepth 100000
attribute [-instance] Inst.Model.Scl.ref
noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open Iop Prob AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.AtFiles AtPublicFiles.Committed AtPublicFiles.Cut
open AtPublicFiles.AtFiles.HonestTerm
open ProofFile.Honest (Prover Sides relAt AtHonest OnlineProverWithDescription Cells Coins Ready ready Local Face)
open ProofFile.Honest.Term (OnlineReturn onlineMaker matrixInput tableCoins)
open VerifiableInference.Desc (Chain KindName FileDescription)
open Compile.Lifetime (SimOf)
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD)
open LPFD.Full (instanceAsPlainRecord)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles NamedFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed committerCoinCountLessOne)
open P5J

local instance (priority := high) k8BasePad : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) k8BaseValue : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) k8BaseDefault : Inhabited RunValue := ⟨fun _ => 0⟩

section
variable {Xi W₀ Rc Ky Tr X₀ X : Type} {F F' : FileDescription Xi} {Bk : ProofFile.Honest.ProverCoinCounts}

theorem sidesAt_first_place (h : F = F') (G : Sides F Bk W₀ Rc Ky Tr X₀ X) {κ : KindName}
    (hn : ∀ L ∈ G.first, L.place.kind ≠ κ) : ∀ L ∈ (sidesAt h G).first, L.place.kind ≠ κ := by
  subst h
  exact hn

end

variable (files : PublicFiles) {D : WholeD} {r : LPFD.Full.RunPF}
  {x : VerifiableInference.Desc.First.Look.Place}
  {A : OnlineProverWithDescription FullSizeMatrix ProofFile.Honest.IndexCommitterCoins Cells Unit Unit} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {G : Sides A.F A.B FullSizeMatrix ProofFile.Honest.IndexCommitterCoins TableKey Cells Unit Unit} {more : List (String × Bool)}

/-- The prover of the term, at the base's return. -/
abbrev termProver (A : OnlineProverWithDescription FullSizeMatrix ProofFile.Honest.IndexCommitterCoins Cells Unit Unit) :
    Prover FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst TableKey Cells Unit Unit :=
  A.H.thru id (tableCoins files) matrixInput.dummy

/-- The rows of the term, at the base's rows. -/
abbrev termRows (hd : AtHonest OnBytes.secondHashFunction files D r A.Z Np cF x baseFilling A G more) :
    Sides (descZ A.Z Np cF) A.B FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey Cells Unit Unit :=
  sidesAt hd.isTerm.2 (G.thru id (tableCoins files))

/-- The online prover, at the base's return. -/
theorem onlineProver_of_base (hd : AtHonest OnBytes.secondHashFunction files D r A.Z Np cF x baseFilling A G more) :
    onlineProver files = onlineProverAt (A.thru id (tableCoins files) matrixInput.dummy) Np cF := by
  have made : onlineMaker files = .ok (A.thru id (tableCoins files) matrixInput.dummy) :=
    ProofFile.Honest.atPure_through id (tableCoins files) matrixInput.dummy hd.made dummy_inRange
  obtain ⟨Bs, base, O⟩ := hd.laid.opened
  exact onlineProver_of_seat files made hd.laid.places (ToldDesc.pureChainAt_of_open O)

theorem provG_first_base (hd : AtHonest OnBytes.secondHashFunction files D r A.Z Np cF x baseFilling A G more) :
    (provG files A.Z Np cF A.B (termRows files hd) (termProver files A)).first = (termProver files A).first := by
  have e := sidesAt_prover hd.isTerm.2 (G.thru id (tableCoins files))
    ((cmAlong (AZ files) PadZ (holdZ files)).proverAt 0 (termProver files A))
  show ((termRows files hd).prover ((cmAlong (AZ files) PadZ (holdZ files)).proverAt 0 (termProver files A))).first = _
  rw [e]
  exact (show ((G.thru id (tableCoins files)).prover
        ((cmAlong (AZ files) PadZ (holdZ files)).proverAt 0 (termProver files A))).first =
      ((G.thru id (tableCoins files)).prover (termProver files A)).first from rfl).trans
    (by rw [ProofFile.Honest.prover_thru, hd.ring])

theorem provG_second_base (hd : AtHonest OnBytes.secondHashFunction files D r A.Z Np cF x baseFilling A G more) :
    (provG files A.Z Np cF A.B (termRows files hd) (termProver files A)).second = (termProver files A).second := by
  have e := sidesAt_prover hd.isTerm.2 (G.thru id (tableCoins files))
    ((cmAlong (AZ files) PadZ (holdZ files)).proverAt 0 (termProver files A))
  show ((termRows files hd).prover ((cmAlong (AZ files) PadZ (holdZ files)).proverAt 0 (termProver files A))).second = _
  rw [e]
  exact (show ((G.thru id (tableCoins files)).prover
        ((cmAlong (AZ files) PadZ (holdZ files)).proverAt 0 (termProver files A))).second =
      ((G.thru id (tableCoins files)).prover (termProver files A)).second from rfl).trans
    (by rw [ProofFile.Honest.prover_thru, hd.ring])

/-- **The private stops of the online prover at the named number**, from K8's debt at the term. -/
theorem online_hid_of_k8_base (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp)
    (hd : AtHonest OnBytes.secondHashFunction files D r A.Z Np cF x baseFilling A G more)
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles files).EncodingRandomness} {xx : ProofFile.Inst} {k : Coins A.B}
    {R : Ready FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst TableKey Cells Unit Unit}
    (hR : ready (descZ A.Z Np cF) A.B (provG files A.Z Np cF A.B (termRows files hd) (termProver files A)) w₀ rc xx
      k = .ok R)
    (hn : ∀ L ∈ G.first, L.place.kind ≠ KindName.frame)
    (Pr : Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst Cells → Prop)
    (hP : ∀ w a, rangeAtFiles w.1 → (protocolAtFiles files).validB (ServedRequest committerCoinCountLessOne files hr) w a →
      ∀ tr, (termProver files A).trace w.1 (instanceAsPlainRecord a) = some tr → Pr ⟨w.1, w.2.1, instanceAsPlainRecord a, tr⟩)
    (quiet : ∀ side ∈ (termProver files A).first ++ (termProver files A).second,
      side.place.kind ≠ KindName.K8 → ∀ part ∈ side.parts, ∀ input front own,
        part.hid input front own = none)
    (k₁ : K8Clause Pr Face.own.sees (termProver files A).first (descZ A.Z Np cF).first.blocksInOrder.dropLast
      (dataZ files).ds₁)
    (k₃ : K8Clause Pr Face.own.sees (termProver files A).second (descZ A.Z Np cF).second.blocksInOrder
      (dataZ files).ds₃) :
    HidSmall (onlineProver files)
      (fun _ w a => rangeAtFiles w.1 ∧ (protocolAtFiles files).validB (ServedRequest committerCoinCountLessOne files hr) w a)
      (onlinePrivateStopsAt files A.Z Np cF A.B (termRows files hd) (termProver files A)) := by
  have hn' : ∀ L ∈ (termRows files hd).first, L.place.kind ≠ KindName.frame := by
    refine sidesAt_first_place hd.isTerm.2 _ fun L hL => ?_
    obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
    exact hn L₀ h₀
  have h := online_hid_at_files files A.Z Np cF runValueBytes runValueBytes A.B (termRows files hd)
    (termProver files A) scope hr live hd.laid hR hn' Pr hP
    (by
      rw [provG_first_base files hd]
      exact partsHeld_of_k8 (fun g hg => quiet g (List.mem_append_left _ hg)) k₁)
    (by
      rw [provG_second_base files hd]
      exact partsHeld_of_k8 (fun g hg => quiet g (List.mem_append_right _ hg)) k₃)
  rw [onlineProver_of_base files hd]
  rw [famG_thru files A.Z Np cF runValueBytes runValueBytes id (tableCoins files) matrixInput.dummy hd] at h
  exact h

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.onlineProver_of_base
#print axioms VerifiableInference.Compilation.provG_first_base
#print axioms VerifiableInference.Compilation.online_hid_of_k8_base
