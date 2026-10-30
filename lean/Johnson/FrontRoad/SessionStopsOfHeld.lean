-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/SessionStopsOfHeld.lean: if the chains' local bounds on private aborts hold at
every input that meets a named premise P, the stated shares add up to at most z₁ and z₃, and every
input of Td, with the trace that H.trace returns, meets P, then the condition HidSmall
(E2E/BridgePrivacy.lean) holds at the family famG, at Td, at z₁ + z₃. The measure is over the
verifier's messages; the bound is asked at every index and every value of the committer's
randomness. It is glue, with no bound of its own. It is idle at P := everything or nothing, at rows
that never abort privately, and so at rows that always abort publicly.
Terms of this folder: Johnson/FrontRoad/Front.lean and Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
hidSmall_of_held: let StopsFit (Johnson/Desc/ProofFile/Honest/Law/SharesStops.lean) hold at the
prover provG. Let P be a premise on an input with its trace: the index, the committer's randomness,
the instance instanceAsPlainRecord a, and the trace. Let every input of Td, with the trace that H.trace returns,
meet P (hP). At every v that meets P, let ChainHeld hold for the private aborts of the first and of
the second chain (h₁, h₃). Let the sums of the stated shares at the two chains' gates be at most z₁
and z₃ (s₁, s₃). Then HidSmall holds at famG, at Td, at z₁ + z₃.
  sharesSum, sharesSum_eq   the sum of the shares that a chain's parts state for their private
      aborts, as a term that names no input; at every input the sum of the numbers at the chain's
      gates is that sum (rowGates_p_any, memberGates_p_any, chainGates_p_any). So s₁ and s₃ do not
      stand under «at every v that meets P», and cannot be had for nothing at a P that holds of
      nothing.
  hidSmall_yes_of_held   the case Td := TiedYes (E2E/BridgeJoinAtFiles.lean): every request of the
      relation Yes, whatever the range of indices and the set of OOD seeds.
  sessionStops_of_held   from the same premises, by hidSmall_in, HidSmall at TiedIn, at every range
      ok and every set Gs, at the same number. At Gs := fun _ => True its conclusion is, to the
      letter, the field sessionStops of PremWDebts (E2E/BridgeDebts.lean) with hO' := z₁ + z₃. An
      example at the foot of the file lets Lean hold the field's type; premWDebts_stops
      (Johnson/FrontRoad/SessionStopsAtFiles.lean) lets Lean hold the match.

How it fits. One call of hid_held_on (Johnson/Desc/ProofFile/Honest/Law/SharesOn.lean). The
equalities that hid_famG_eq and trace_provG (Johnson/FrontRoad/SessionHid.lean) state hold by
definition, so no rewriting is needed. A proof of these premises at TiedYes would give the condition
on private aborts in two places: in the list of premises of the implication on index privacy (the
field sessionStops of PremWDebts), and in the bridge's theorems on acceptance
(E2E/BridgeAccept.lean, E2E/BridgeBothOfDebts.lean). Neither theorem that these premises serve is
concluded here. Lemmas toward the condition HidSmall; not one of the release's goal statements.

Limits.
  No parameters are known at which its premises hold at the IOP of the proof file as it is written
      in Lean.
  It proves no probability bound of its own: it passes on the bounds that its premises state. It is
      a union bound on one space: shares are added, and independence is not asked. z₁ + z₃ bounds a
      sum of the shares that the parts state; no value is given for it here. At z₁ + z₃ ≥ 1 the
      conclusion holds of every prover.
  P reads the hidden input. That every input of Td, with its trace, meets P is the premise hP, which
      is not proved here. At TiedYes it is asked at every request of Yes, whatever the index's
      range. The premises can hold in two degenerate ways. At P := fun _ => True hP is free, and h₁,
      h₃ are asked at every input. At P := fun _ => False h₁, h₃ are free, and hP says that no input
      of Td has a trace.
  G (the rows) and H (the prover of parts) are variables. Nothing asks which trace H.trace returns.
      At rows whose parts never abort HidSmall holds at 0 (hidSmall_famG, E2E/BridgeNoStop.lean). A
      part's public test is asked first (Part.stopAt, Johnson/Desc/ProofFile/Honest/Side.lean), so
      rows that always abort publicly never abort privately: they meet all premises, with HidSmall
      at 0 (by inspection, not proved). So the condition says something only when it holds together
      with the premises on acceptance at the same G and H.
  It bounds only the part of the abort set that may depend on the private input (Hid), not the
      public part (Bad). Which of a part's two abort tests is which is the choice of whoever writes
      the part; no statement sorts them.
-/
import Johnson.FrontRoad.SessionHid
import Johnson.Desc.ProofFile.Honest.Law.SharesOn
import E2E.BridgePrivacy
import E2E.BridgeDebts

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open AtPublicFiles.AtFiles AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Flat (front₀ join₀)
open _root_.Run (ckP)
open VerifiableInference.Desc (Block)
open ProofFile.Honest (Prover ProverCoinCounts Sides Local Face Why StopsFit ChainHeld chainGates hid_held_on Placed
  rowGates memberGates)
open OnBytes.Maker (RDT)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData)
open P5J

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off within this namespace,
so that no statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) nonemptyPadZ_ofHeld : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

/- The same of this one. -/
local instance (priority := high) nonemptyOfInhabited_ofHeld {α : Type} [Inhabited α] :
    Nonempty α := ⟨default⟩

/-! ## 1. The sum of the stated shares does not read the input -/

section
variable {S Cl V W Y : Type} (sp : Option Why → Bool) (v v' : Option V)
  (val : ProofFile.Honest.Part V W Y → ℝ≥0∞)

/-- The numbers at a row's gates do not read the input. -/
theorem rowGates_p_any : ∀ (ps : List (ProofFile.Honest.Part V W Y)) (ds : List RDT),
    (rowGates sp v val ps ds).map (·.p) = (rowGates sp v' val ps ds).map (·.p)
  | [], _ => rfl
  | p :: ps, ds => by
    show val p :: (rowGates sp v val ps (ds.drop p.moves.length)).map (·.p) =
      val p :: (rowGates sp v' val ps (ds.drop p.moves.length)).map (·.p)
    rw [rowGates_p_any ps]

/-- Nor do those at a member's gates. -/
theorem memberGates_p_any (hs : List (Placed V W Y)) (b : Block S Cl) (ds : List RDT) :
    (memberGates sp v val hs b ds).map (·.p) = (memberGates sp v' val hs b ds).map (·.p) := by
  unfold memberGates
  cases hs.find? fun h => h.place == b.place with
  | none => rfl
  | some h => exact rowGates_p_any sp v v' val h.parts ds

/-- Nor do those at a chain's gates. -/
theorem chainGates_p_any (hs : List (Placed V W Y)) : ∀ (bs : List (Block S Cl)) (ds : List RDT),
    (chainGates sp v val hs bs ds).map (·.p) = (chainGates sp v' val hs bs ds).map (·.p)
  | [], _ => rfl
  | b :: bs, ds => by
    show (memberGates sp v val hs b (ds.take b.rounds.length) ++
        chainGates sp v val hs bs (ds.drop b.rounds.length)).map (·.p) =
      (memberGates sp v' val hs b (ds.take b.rounds.length) ++
        chainGates sp v' val hs bs (ds.drop b.rounds.length)).map (·.p)
    rw [List.map_append, List.map_append, memberGates_p_any sp v v' val hs b,
      chainGates_p_any hs bs]

end

/-- **The sum of the shares that a chain's parts state for their private aborts.** It names no
input. -/
def sharesSum {S Cl V W Y : Type} (hs : List (Placed V W Y)) (bs : List (Block S Cl))
    (ds : List RDT) : ℝ≥0∞ :=
  ((chainGates (· == some Why.hid) (none : Option V) (·.hidShare.val) hs bs ds).map (·.p)).sum

/-- At every input the sum of the numbers at the chain's gates is that sum. -/
theorem sharesSum_eq {S Cl V W Y : Type} (v : Option V) (hs : List (Placed V W Y))
    (bs : List (Block S Cl)) (ds : List RDT) :
    ((chainGates (· == some Why.hid) v (·.hidShare.val) hs bs ds).map (·.p)).sum =
      sharesSum hs bs ds := by
  unfold sharesSum
  rw [chainGates_p_any _ v none]

/-! ## 2. From the chains' bounds to HidSmall -/

variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
  (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
  (run₃ : R₃ → ByteArray) {Tr X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)

/-- **An implication: from the chains' bounds on private aborts, at inputs that meet a named premise
P, to HidSmall at famG.** The measure is over the verifier's messages; the bound is asked at every
index and every value of the committer's randomness. It is glue, with no bound of its own. It is
idle at P := everything or nothing, at rows that never abort privately, and so at rows that always
abort publicly. -/
theorem hidSmall_of_held {pre₁ : List (Block (descZ Zp Np cF).S₁ (descZ Zp Np cF).Cl)}
    {e₁ : Block (descZ Zp Np cF).S₁ (descZ Zp Np cF).Cl}
    (Sf : StopsFit (descZ Zp Np cF) (provG Z Zp Np cF B G H) (dataZ Z) pre₁ e₁)
    (Td : ℕ → WZ Z → XF × (protocolAtFiles Z).Rec → Prop)
    (P : Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst Tr → Prop) (z₁ z₃ : ℝ≥0∞)
    (hP : ∀ n w a, Td n w a → ∀ tr, H.trace w.1 (LPFD.Full.instanceAsPlainRecord a) = some tr →
      P ⟨w.1, w.2.1, LPFD.Full.instanceAsPlainRecord a, tr⟩)
    (h₁ : ∀ v, P v →
      ChainHeld (· == some Why.hid) (Face.own.sees v) (·.hidShare.val)
        (provG Z Zp Np cF B G H).first (ckP .two) pre₁ (dataZ Z).ds₁)
    (s₁ : sharesSum (provG Z Zp Np cF B G H).first pre₁ (dataZ Z).ds₁ ≤ z₁)
    (h₃ : ∀ v, P v →
      ChainHeld (· == some Why.hid) (Face.own.sees v) (·.hidShare.val)
        (provG Z Zp Np cF B G H).second (ckP .two) (descZ Zp Np cF).second.blocksInOrder (dataZ Z).ds₃)
    (s₃ : sharesSum (provG Z Zp Np cF B G H).second (descZ Zp Np cF).second.blocksInOrder (dataZ Z).ds₃ ≤
      z₃) :
    HidSmall (famG Z Zp Np cF run₂ run₃ B G H) Td (z₁ + z₃) :=
  fun n w a h =>
    hid_held_on (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
      (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty (descZ Zp Np cF) silInst B
      (provG Z Zp Np cF B G H) (seamZ Z run₂ run₃ n) (shAt Zp Np cF) (extZ Z) Sf w
      (LPFD.Full.instanceAsPlainRecord a) z₁ z₃ P (hP n w a h)
      (fun v hv => ⟨h₁ v hv, (sharesSum_eq _ _ _ _).le.trans s₁⟩)
      fun v hv => ⟨h₃ v hv, (sharesSum_eq _ _ _ _).le.trans s₃⟩

/-- **The same at every request of Yes** (TiedYes, E2E/BridgeJoinAtFiles.lean), whatever the range
of indices and the set of OOD seeds. The measure, and the ways in which it is idle, are those of
hidSmall_of_held. -/
theorem hidSmall_yes_of_held {pre₁ : List (Block (descZ Zp Np cF).S₁ (descZ Zp Np cF).Cl)}
    {e₁ : Block (descZ Zp Np cF).S₁ (descZ Zp Np cF).Cl}
    (Sf : StopsFit (descZ Zp Np cF) (provG Z Zp Np cF B G H) (dataZ Z) pre₁ e₁)
    (Yes : FullSizeMatrix → XF → Prop) (P : Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst Tr → Prop) (z₁ z₃ : ℝ≥0∞)
    (hP : ∀ n w a, TiedYes Z Zp Np cF run₂ run₃ B G H Yes n w (LPFD.Full.instanceAsPlainRecord a) →
      ∀ tr, H.trace w.1 (LPFD.Full.instanceAsPlainRecord a) = some tr → P ⟨w.1, w.2.1, LPFD.Full.instanceAsPlainRecord a, tr⟩)
    (h₁ : ∀ v, P v →
      ChainHeld (· == some Why.hid) (Face.own.sees v) (·.hidShare.val)
        (provG Z Zp Np cF B G H).first (ckP .two) pre₁ (dataZ Z).ds₁)
    (s₁ : sharesSum (provG Z Zp Np cF B G H).first pre₁ (dataZ Z).ds₁ ≤ z₁)
    (h₃ : ∀ v, P v →
      ChainHeld (· == some Why.hid) (Face.own.sees v) (·.hidShare.val)
        (provG Z Zp Np cF B G H).second (ckP .two) (descZ Zp Np cF).second.blocksInOrder (dataZ Z).ds₃)
    (s₃ : sharesSum (provG Z Zp Np cF B G H).second (descZ Zp Np cF).second.blocksInOrder (dataZ Z).ds₃ ≤
      z₃) :
    HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
      (fun n w a => TiedYes Z Zp Np cF run₂ run₃ B G H Yes n w (LPFD.Full.instanceAsPlainRecord a)) (z₁ + z₃) :=
  hidSmall_of_held Z Zp Np cF run₂ run₃ B G H Sf _ P z₁ z₃ hP h₁ s₁ h₃ s₃

/-- **From the same premises, HidSmall at TiedIn**, at every range ok of indices and every set Gs of
OOD seeds, at the same number. At Gs := fun _ => True that is the field sessionStops of PremWDebts.
The measure, and the ways in which it is idle, are those of hidSmall_of_held. -/
theorem sessionStops_of_held {pre₁ : List (Block (descZ Zp Np cF).S₁ (descZ Zp Np cF).Cl)}
    {e₁ : Block (descZ Zp Np cF).S₁ (descZ Zp Np cF).Cl}
    (Sf : StopsFit (descZ Zp Np cF) (provG Z Zp Np cF B G H) (dataZ Z) pre₁ e₁)
    (Yes : FullSizeMatrix → XF → Prop) (P : Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst Tr → Prop) (z₁ z₃ : ℝ≥0∞)
    (hP : ∀ n w a, TiedYes Z Zp Np cF run₂ run₃ B G H Yes n w (LPFD.Full.instanceAsPlainRecord a) →
      ∀ tr, H.trace w.1 (LPFD.Full.instanceAsPlainRecord a) = some tr → P ⟨w.1, w.2.1, LPFD.Full.instanceAsPlainRecord a, tr⟩)
    (h₁ : ∀ v, P v →
      ChainHeld (· == some Why.hid) (Face.own.sees v) (·.hidShare.val)
        (provG Z Zp Np cF B G H).first (ckP .two) pre₁ (dataZ Z).ds₁)
    (s₁ : sharesSum (provG Z Zp Np cF B G H).first pre₁ (dataZ Z).ds₁ ≤ z₁)
    (h₃ : ∀ v, P v →
      ChainHeld (· == some Why.hid) (Face.own.sees v) (·.hidShare.val)
        (provG Z Zp Np cF B G H).second (ckP .two) (descZ Zp Np cF).second.blocksInOrder (dataZ Z).ds₃)
    (s₃ : sharesSum (provG Z Zp Np cF B G H).second (descZ Zp Np cF).second.blocksInOrder (dataZ Z).ds₃ ≤
      z₃)
    (ok : FullSizeMatrix → Prop) (Gs : (protocolAtFiles Z).OutOfDomainSeed → Prop) :
    HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
      (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok Gs n w (LPFD.Full.instanceAsPlainRecord a))
      (z₁ + z₃) :=
  hidSmall_in Z Zp Np cF run₂ run₃ B G H
    (hidSmall_yes_of_held Z Zp Np cF run₂ run₃ B G H Sf Yes P z₁ z₃ hP h₁ s₁ h₃ s₃)

/-- The type of the field sessionStops of PremWDebts is HidSmall at TiedIn, at Gs := fun _ => True.
That this is the conclusion of sessionStops_of_held at that Gs, with hO' := z₁ + z₃, is then seen by
comparing the two statements. -/
example (c₀ : VerifiableInference.Digest) (m₀ : List (Iop.Dig 256)) (b : PublicFiles → ℕ)
    (Fx : VerifiableInference.Desc.FileDescription KeyInst) {TrT X₀T XT Q₂ Q₃ : Type} (BT : ProverCoinCounts)
    [Fintype Q₂] [Nonempty Q₂] [Fintype Q₃] [Inhabited Q₃]
    (HT : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) KeyInst TableKey TrT X₀T XT)
    (val₂ : Q₂ → ByteArray) (val₃ : Q₃ → ByteArray) (shT : TableKey → Fx.S₂)
    (c : OnBytes.WholeKey.CoinNums (List Bool))
    (R₀ : RestOf 256 (List Bool) (filesAt Z).annT (filesAt Z).annL
      (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z))
    (okV : ByteArray × ByteArray → Prop) (v₀ : ByteArray × ByteArray)
    (startT startL startB : ByteArray × ByteArray → ℕ → Bool → Rom.Bits → Rom.Bits)
    (Yes : FullSizeMatrix → XF → Prop) (ok : FullSizeMatrix → Prop) (sT : AtPublicFiles.KeyBridge.SimT (protocolAtFiles Z)) (s1 : ℕ)
    (zT hT z : ℝ≥0∞)
    (d : PremWDebts c₀ m₀ b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT
      startL startB Yes ok sT s1 zT hT z) :
    HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
      (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok (fun _ => True) n w
        (LPFD.Full.instanceAsPlainRecord a)) z :=
  d.sessionStops

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.nonemptyPadZ_ofHeld
#print axioms OnBytes.FrontRoad.nonemptyOfInhabited_ofHeld
#print axioms OnBytes.FrontRoad.rowGates_p_any
#print axioms OnBytes.FrontRoad.memberGates_p_any
#print axioms OnBytes.FrontRoad.chainGates_p_any
#print axioms OnBytes.FrontRoad.sharesSum
#print axioms OnBytes.FrontRoad.sharesSum_eq
#print axioms OnBytes.FrontRoad.hidSmall_of_held
#print axioms OnBytes.FrontRoad.hidSmall_yes_of_held
#print axioms OnBytes.FrontRoad.sessionStops_of_held
