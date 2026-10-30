--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyNoStop.lean: NO TYPED PART OF THE KEY FILE's PROVER OF PARTS EVER STOPS: `NoStopAll`
(E2E/NoStop.lean) at `keyProver K` (E2E/KeyProver.lean), from the texts of the halves that are laid
there. A sentence on these texts, part by part.

General.
  `QuietHalf h`: every part of a half is quiet.
  `quiet_lift`: a quiet part, seated in a wider input and state (`Part.lift`), is quiet.
  `quiet_empty`: a part that sees a value of the empty type is quiet where its first test never
speaks. On each text: both tests are the constant `none` (or the second is handed a value of the
empty type).
  `quiet_sumPart` (Johnson/Desc/ProofFile/Honest/Sum.lean) · `quiet_sendPart`, `quietHalf_send` (K1/
  Part.lean) · `quiet_partOf`, `quietHalf_look` (K3/Row.lean) · `quiet_partOfOwned`,
  `quietHalf_lookOwned` (K3/RowOwned.lean: the seat that `keyProver K` calls) · `quietHalf_k13` (K13/Part.lean; its
  row's first part is `quietPart`, Honest/ForKinds.lean) · `noStop_halves`, `noStop_sendHalves`
  (K14/Parts.lean, K14/Sendings.lean).
  `mem_weave`: a half of the woven list is one of either list.
**`noStopAll_keyProver`**: no part of `keyProver K` ever stops, WHERE THE FOUR PROXIMITY TESTS'
  HALVES ARE QUIET: these four are letters of `KeyParts`: no such half is written.

Limits.
- On the halves AS TYPED in the files named: a half of another text owes its own line.
- The four premises are shown of nothing.
- All limits of E2E/NoStop.lean stand: a fall is no stop; an empty abort set says that the honest
  side always sends, not that the verifier accepts.

-/
import E2E.NoStop
import E2E.KeyProver

set_option autoImplicit false

namespace AtPublicFiles.Stops
open ProofFile.Honest

section General
variable {V V' W W' X Y : Type}

/-- Every part of a half is quiet. -/
def QuietHalf (h : Placed V W X) : Prop := ∀ p ∈ h.parts, Quiet p

/-- A quiet part, seated in a wider input and state, is quiet. -/
theorem quiet_lift {p : Part V' W' Y} (h : Quiet p) (see : V → V') (wit : W → W') (get : X → Y)
    (set : X → Y → X) : Quiet (p.lift see wit get set) :=
  ⟨h.1, fun u => h.2 (see u)⟩

/-- A part that sees a value of the empty type is quiet where its first test never speaks. -/
theorem quiet_empty {p : Part Empty W X} (h : ∀ loc ds, p.bad loc ds = none) : Quiet p :=
  ⟨h, fun u => u.elim⟩

/-- The masked sumcheck's part. -/
theorem quiet_sumPart (name endName : String) (J : SumJob W X) :
    Quiet (sumPart name endName J : Part V W X) :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

end General

section Houses
variable {V W X : Type}

/-- A sending's part. -/
theorem quiet_sendPart (J : K1.SendJob W X) : Quiet (K1.sendPart J : Part V W X) :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- A sending's half. -/
theorem quietHalf_send (J : K1.SendJob W X) : QuietHalf (K1.proverSideOfSending J : Placed V W X) :=
  fun p hp => by
    have e : p = K1.sendPart J := List.mem_singleton.1 hp
    rw [e]
    exact quiet_sendPart J

/-- The part of a lookup's stage. -/
theorem quiet_partOf (R : K3.Reads) (J : K3.LookJobs W) (a : K3.At) (s : K3.Stage) (i : Nat) :
    Quiet (K3.partOf R J a s i : Part V W Unit) := by
  unfold K3.partOf
  split
  · exact quiet_sumPart _ _ _
  · exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- A lookup's half, seated in a chain's letters. -/
theorem quietHalf_look {V₁ W₁ X₁ : Type} (R : K3.Reads) (J : K3.LookJobs W) (wit : W₁ → W)
    (a : K3.At) : QuietHalf (K3.proverSideOfLookupInChainAtOneOwner R J wit a : Placed V₁ W₁ X₁) :=
  fun p hp => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hq
    exact quiet_lift (quiet_partOf R J a x.1 x.2) _ _ _ _

/-- The part of a lookup's stage, at a letter for the owners. -/
theorem quiet_partOfOwned (o : K3.Owners) (R : K3.Reads) (J : K3.LookJobs W) (a : K3.At)
    (s : K3.Stage) (i : Nat) : Quiet (K3.partOfOwned o R J a s i : Part V W Unit) := by
  unfold K3.partOfOwned
  split
  · exact quiet_sumPart _ _ _
  · exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- A lookup's half at a letter for the owners, seated in a chain's letters. -/
theorem quietHalf_lookOwned {V₁ W₁ X₁ : Type} (o : K3.Owners) (R : K3.Reads) (J : K3.LookJobs W)
    (wit : W₁ → W) (a : K3.At) : QuietHalf (K3.proverSideOfLookupInChain o R J wit a : Placed V₁ W₁ X₁) :=
  fun p hp => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hq
    exact quiet_lift (quiet_partOfOwned o R J a x.1 x.2) _ _ _ _

/-- The members' batching's half. -/
theorem quietHalf_k13 {W₀ Rc Xi Tr : Type} (weights : W₀ → Weights) (pile : K13.PileOf Xi)
    (p : VerifiableInference.Desc.K13.Where) :
    QuietHalf (K13.proverSideOfClaimCombination weights pile p :
      Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X) :=
  fun q hq => by
    rcases List.mem_cons.1 hq with rfl | hq
    · exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
    · have e := List.mem_singleton.1 hq
      rw [e]
      exact quiet_lift (quiet_sumPart _ _ _) _ _ _ _

/-- The shared chain's own halves. -/
theorem noStop_halves {W₀ Rc Ky : Type} (P : K14.Data) (weights : W₀ → Weights) :
    NoStop (K14.proverSidesOfSharedRounds P weights : List (Placed Empty (Common W₀ Rc Ky) X)) :=
  fun h hh p hp => quiet_empty fun loc ds => by
    unfold K14.proverSidesOfSharedRounds at hh
    rcases List.mem_append.1 hh with hh | hh
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
      rcases hh with rfl | rfl | rfl <;>
        · have e := List.mem_singleton.1 hp
          rw [e]
          rfl
    · split at hh
      · have e := List.mem_singleton.1 hh
        rw [e] at hp
        have e' := List.mem_singleton.1 hp
        rw [e']
        rfl
      · exact absurd hh List.not_mem_nil

/-- The shared chain's two sendings' halves. -/
theorem noStop_sendHalves {W₀ Rc Ky : Type} (A : K14.SendPub) (weights : W₀ → Weights)
    (rand : Rc → TableRand) :
    NoStop (K14.proverSidesOfSharedSendings A weights rand : List (Placed Empty (Common W₀ Rc Ky) X)) :=
  fun h hh p hp => quiet_empty fun loc ds => by
    unfold K14.proverSidesOfSharedSendings at hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl <;>
      · have e := List.mem_singleton.1 hp
        rw [e]
        rfl

end Houses

end AtPublicFiles.Stops

namespace AtPublicFiles.KeyFile
open ProofFile.Honest AtPublicFiles.Stops

variable {W₀ Rc X₀ X Wk : Type}

/-- A half of the woven list is one of either list. -/
theorem mem_weave {own send : List (Placed Empty (In2 W₀ Rc) X₀)}
    {h : Placed Empty (In2 W₀ Rc) X₀} (hm : h ∈ sharedChainProverSidesInOrder own send) : h ∈ own ∨ h ∈ send := by
  unfold sharedChainProverSidesInOrder at hm
  split at hm
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
    tauto
  · exact List.mem_append.1 hm

/-- **No part of the key file's prover of parts ever stops**, where the four proximity tests' halves
are quiet. -/
theorem noStopAll_keyProver (K : KeyParts W₀ Rc X₀ X Wk) (hr : QuietHalf K.rng)
    (hU : QuietHalf K.onU) (hO : QuietHalf K.onOmega) (hw : QuietHalf K.own) :
    NoStopAll (keyProver K) := by
  refine ⟨fun h hh => ?_, fun h hh => ?_, fun h hh => ?_⟩
  · have hh' : h ∈ [K1.proverSideOfSending K.idx, K1.proverSideOfSending K.msg,
        K3.proverSideOfLookupInChain (K3.keyOwners K.look0.face) K.reads K.jobs0 K.wit K.look0,
        K3.proverSideOfLookupInChain (K3.keyOwners K.look1.face) K.reads K.jobs1 K.wit K.look1, K.rng,
        K13.proverSideOfClaimCombination K.weights K.pile K.batt, K1.proverSideOfSending K.w] := hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh'
    rcases hh' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact quietHalf_send _
    · exact quietHalf_send _
    · exact quietHalf_lookOwned _ _ _ _ _
    · exact quietHalf_lookOwned _ _ _ _ _
    · exact hr
    · exact quietHalf_k13 _ _ _
    · exact quietHalf_send _
  · have hh' : h ∈ sharedChainProverSidesInOrder (K14.proverSidesOfSharedRounds K.lin K.weights)
        (K14.proverSidesOfSharedSendings K.send K.weights fun c => randK14 (K.rand c)) ++ [K.onU, K.onOmega] := hh
    rcases List.mem_append.1 hh' with hm | hm
    · rcases mem_weave hm with hm | hm
      · exact noStop_halves _ _ h hm
      · exact noStop_sendHalves _ _ _ h hm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact hU
      · exact hO
  · have hh' : h ∈ [K.own] := hh
    rw [List.mem_singleton.1 hh']
    exact hw

end AtPublicFiles.KeyFile

#print axioms AtPublicFiles.Stops.QuietHalf
#print axioms AtPublicFiles.Stops.quiet_lift
#print axioms AtPublicFiles.Stops.quiet_empty
#print axioms AtPublicFiles.Stops.quiet_sumPart
#print axioms AtPublicFiles.Stops.quiet_sendPart
#print axioms AtPublicFiles.Stops.quietHalf_send
#print axioms AtPublicFiles.Stops.quiet_partOf
#print axioms AtPublicFiles.Stops.quietHalf_look
#print axioms AtPublicFiles.Stops.quiet_partOfOwned
#print axioms AtPublicFiles.Stops.quietHalf_lookOwned
#print axioms AtPublicFiles.Stops.quietHalf_k13
#print axioms AtPublicFiles.Stops.noStop_halves
#print axioms AtPublicFiles.Stops.noStop_sendHalves
#print axioms AtPublicFiles.KeyFile.mem_weave
#print axioms AtPublicFiles.KeyFile.noStopAll_keyProver
