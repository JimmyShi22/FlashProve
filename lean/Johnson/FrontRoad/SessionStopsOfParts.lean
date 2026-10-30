-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/SessionStopsOfParts.lean: an implication, with four premises. StopsFit holds at
provG, the prover of the sessions. At every input that meets a named premise P, each part of that
prover either has a private abort test that never fires or meets its own local bound. The stated
shares at the gates of the first chain, without its last member, and of the second chain add up to
at most z₁ and z₃. Every input of the set Td, with the trace that H.trace returns, meets P. Then the
condition HidSmall (E2E/BridgePrivacy.lean) holds at the family famG, at Td, at z₁ + z₃. The measure
is over the verifier's messages; the bound is asked at every index and every value of the
committer's randomness. It is glue, with no bound of its own. It is idle at P := everything or
nothing, at rows that never abort privately, and so at rows that always abort publicly.
Terms of this folder: Johnson/FrontRoad/Front.lean and Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
A part's private abort test is the one that may read the hidden input with its trace (Part.hid), as
against its public one (Part.bad). A half is the prover's share of one sub-protocol, a list of
parts. A part's stretch is the data of its own rounds.
  PartsHeld   a premise's form, for one chain. At every v that meets P, at each member b of the
      chain, at the first half at b's place, at each part p of that half: either p's private abort
      test returns none at all arguments, or StopDebt
      (Johnson/Desc/ProofFile/Honest/Law/SharesParts.lean) holds for p's private aborts, at p's own
      stretch of the chain's data and at the share that p states.
  chainHeld_of_parts   PartsHeld gives ChainHeld at every v that meets P.
hidSmall_of_parts: hidSmall_of_held (Johnson/FrontRoad/SessionStopsOfHeld.lean) with its two
premises ChainHeld replaced by PartsHeld at the first chain without its last member and at the
second chain. The two sums of stated shares (sharesSum, which names no input) stay premises.

How it fits. chainHeld_of (SharesParts.lean) goes from the parts to a chain. stopDebt_no_hid
(Johnson/Desc/ProofFile/Honest/Law/SharesNoHid.lean) gives StopDebt for a part whose private test
never fires, whatever its public test does. So a local bound is asked only of the parts whose
private test can fire at some argument. Every part still adds its stated share to the two sums.
Lemmas toward the condition HidSmall; not one of the release's goal statements.

Limits.
  No parameters are known at which its premises hold at the IOP of the proof file as it is written
      in Lean. Which parts have a private test that never fires is proved here of no part.
  It proves no probability bound of its own: it passes on the bounds that its premises state.
  PartsHeld asks at least what ChainHeld asks (chainHeld_of_parts). It holds without content where P
      holds of no input, and at a chain with no half at any place or no private test that can fire.
      The prover then has no private abort in that chain, and HidSmall says only that.
  StopDebt is asked at every list of challenges in front of the part, of any length. A private test
      that reads that list may meet it only at the number 1 (SharesParts.lean, at StopDebt).
  All limits of Johnson/FrontRoad/SessionStopsOfHeld.lean hold, those on P among them.
-/
import Johnson.FrontRoad.SessionStopsOfHeld
import Johnson.Desc.ProofFile.Honest.Law.SharesParts
import Johnson.Desc.ProofFile.Honest.Law.SharesNoHid

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
open ProofFile.Honest (Prover ProverCoinCounts Sides Local Face Why StopsFit ChainHeld chainGates Placed StopDebt
  chainHeld_of stopDebt_no_hid)
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
local instance (priority := high) nonemptyPadZ_ofParts : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

/- The same of this one. -/
local instance (priority := high) nonemptyOfInhabited_ofParts {α : Type} [Inhabited α] :
    Nonempty α := ⟨default⟩

/-- **A premise's form, for one chain**: at every v that meets P, each part of each half either has
a private abort test that never fires, or meets StopDebt for its private aborts at its own stretch
of the chain's data and at the share that it states. -/
def PartsHeld {S Cl V W Y : Type} (P : V → Prop) (see : V → Option V) (hs : List (Placed V W Y))
    (bs : List (Block S Cl)) (ds : List RDT) : Prop :=
  ∀ v, P v → ∀ (A : List (Block S Cl)) (b : Block S Cl) (B : List (Block S Cl)), bs = A ++ b :: B →
    ∀ g, (hs.find? fun g => g.place == b.place) = some g →
    ∀ (A' : List (ProofFile.Honest.Part V W Y)) (p : ProofFile.Honest.Part V W Y) (B' : List (ProofFile.Honest.Part V
                  W Y)), g.parts = A' ++ p :: B' →
      (∀ u l o, p.hid u l o = none) ∨
        StopDebt (ckP .two) (· == some Why.hid) (see v) p
          ((((ds.drop (A.flatMap (·.rounds)).length).take b.rounds.length).drop
            (A'.map (·.moves.length)).sum).take p.moves.length) p.hidShare.val

/-- PartsHeld gives ChainHeld at every v that meets P. -/
theorem chainHeld_of_parts {S Cl V W Y : Type} {P : V → Prop} {see : V → Option V}
    {hs : List (Placed V W Y)} {bs : List (Block S Cl)} {ds : List RDT}
    (h : PartsHeld P see hs bs ds) (v : V) (hv : P v) :
    ChainHeld (· == some Why.hid) (see v) (·.hidShare.val) hs (ckP .two) bs ds :=
  chainHeld_of _ _ _ _ _ _ _ fun A b B e g hg A' p B' e' =>
    (h v hv A b B e g hg A' p B' e').elim (fun hh => stopDebt_no_hid _ _ p _ _ hh) id

variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
  (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
  (run₃ : R₃ → ByteArray) {Tr X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)

/-- **An implication: from one premise for each part of the sessions' prover, at inputs that meet a
named premise P, to HidSmall at famG.** The measure is over the verifier's messages; the bound is
asked at every index and every value of the committer's randomness. It is glue, with no bound of its
own. It is idle at P := everything or nothing, at rows that never abort privately, and so at rows
that always abort publicly. -/
theorem hidSmall_of_parts {pre₁ : List (Block (descZ Zp Np cF).S₁ (descZ Zp Np cF).Cl)}
    {e₁ : Block (descZ Zp Np cF).S₁ (descZ Zp Np cF).Cl}
    (Sf : StopsFit (descZ Zp Np cF) (provG Z Zp Np cF B G H) (dataZ Z) pre₁ e₁)
    (Td : ℕ → WZ Z → XF × (protocolAtFiles Z).Rec → Prop)
    (P : Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst Tr → Prop) (z₁ z₃ : ℝ≥0∞)
    (hP : ∀ n w a, Td n w a → ∀ tr, H.trace w.1 (LPFD.Full.instanceAsPlainRecord a) = some tr →
      P ⟨w.1, w.2.1, LPFD.Full.instanceAsPlainRecord a, tr⟩)
    (p₁ : PartsHeld P Face.own.sees (provG Z Zp Np cF B G H).first pre₁ (dataZ Z).ds₁)
    (s₁ : sharesSum (provG Z Zp Np cF B G H).first pre₁ (dataZ Z).ds₁ ≤ z₁)
    (p₃ : PartsHeld P Face.own.sees (provG Z Zp Np cF B G H).second (descZ Zp Np cF).second.blocksInOrder
      (dataZ Z).ds₃)
    (s₃ : sharesSum (provG Z Zp Np cF B G H).second (descZ Zp Np cF).second.blocksInOrder (dataZ Z).ds₃ ≤
      z₃) :
    HidSmall (famG Z Zp Np cF run₂ run₃ B G H) Td (z₁ + z₃) :=
  hidSmall_of_held Z Zp Np cF run₂ run₃ B G H Sf Td P z₁ z₃ hP
    (fun v hv => chainHeld_of_parts p₁ v hv) s₁ (fun v hv => chainHeld_of_parts p₃ v hv) s₃

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.nonemptyPadZ_ofParts
#print axioms OnBytes.FrontRoad.nonemptyOfInhabited_ofParts
#print axioms OnBytes.FrontRoad.PartsHeld
#print axioms OnBytes.FrontRoad.chainHeld_of_parts
#print axioms OnBytes.FrontRoad.hidSmall_of_parts
