-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Reads/SevenAtLive.lean: where the description's test `protocolDataWellFormedAt o` says yes, the
further public reading at o asks seven strings, at every digest. Statements and proofs; no
definition.

Why. The verifier's text makes the plan's chains of the public files more than once: at the constant
`fixedConfigurationDigest` in the plan's seat (`plannedAtO o`) and in the key file's seat (`Key.madeAt`: `chainsOf`),
and, through `VerifierAndGoals.readMoreAtO o`, at the digest that the first reading returned. Where this last
call refuses one string is asked and not seven, and no test looks at the number. These laws say
that no test is needed: a yes of `protocolDataWellFormedAt o` holds a yes of the call at `fixedConfigurationDigest`, and the key
file's seat has asked that the seven strings of parameter bytes are short.

Main statements.
  `planned_of_live`: a yes of `protocolDataWellFormedAt o` gives a value p of the planner's text at `fixedConfigurationDigest` whose
    seven strings of parameter bytes have fewer than 2 ^ 64 bytes each.
  `seven_of_live`: so `par7O o G` has seven strings at every digest, at every ground G.
  `sevenRead_of_live`: and `readMoreAtO o G` returns seven digests, at every hash function.

Limits. Where `protocolDataWellFormedAt o` says no nothing is said: there the description's three gates are shut
(Johnson/Goal/Description/Gates.lean). Nothing on what the seven digests are used for. Nothing on
soundness.

-/
import Johnson.Goal.Reads.SevenAtSecondHashFunction
import Johnson.Goal.Description.Live
import Johnson.Desc.Key.SlotPassesFirstTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FlashProve
open VerifiableInference OnBytes.K.Arm.Pub
open OnBytes.Params OnBytes.Model OnBytes.Model.Verify OnBytes.Tie
open VerifiableInference.PlanWritten (plannedAtO publicOfO)
open _root_.Run (digToBytes)

/-- The chains in what the key file's maker returns are those of the one call of `chainsOf`. -/
theorem madeAt_chains {X : Public} {lay c : ByteArray} {m : Johnson.G.OfPlan.Made}
    (h : VerifiableInference.Desc.Key.madeAt X lay c = .ok m) :
    chainsOf X (some lay) c = .ok m.p.chains := by
  unfold VerifiableInference.Desc.Key.madeAt at h
  obtain ⟨ch, h1, h⟩ := exc_bind h
  obtain ⟨b, h2, h⟩ := exc_bind h
  obtain ⟨l, h3, h⟩ := exc_bind h
  split at h
  · obtain rfl : _ = m := Except.ok.inj h
    exact h1
  · cases h

/-- **A yes of the test gives the planner's yes at the constant, with short strings.** -/
theorem planned_of_live (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) (h : protocolDataWellFormedAt o Zk = true) :
    ∃ p : Verify.Planned, plannedAtO o Zk.pol Zk.KL (some Zk.lay) fixedConfigurationDigest = .ok p ∧
      ∀ n : ChainName, (p.chains.bytes n).size < 2 ^ 64 := by
  obtain ⟨K, P, hG, hK, -, -⟩ := theLiveAt_made o Zk h
  unfold filesParametersOrRefusalAt at hG
  cases hp : plannedAtO o Zk.pol Zk.KL (some Zk.lay) fixedConfigurationDigest with
  | error e => rw [hp] at hG; cases hG
  | ok p =>
    refine ⟨p, rfl, ?_⟩
    unfold keyDataAndDecisionOrRefusalAt at hK
    obtain ⟨X, hX, hL⟩ := exc_bind hK
    obtain ⟨m, hm, hb⟩ := VerifiableInference.Desc.Key.laidFixed_bytes (D := K.1) (r := K.2) hL
    have hc := madeAt_chains hm
    unfold plannedAtO at hp
    obtain ⟨X', hX', hp⟩ := exc_bind hp
    obtain ⟨chains, hch, hp⟩ := exc_bind hp
    obtain ⟨built, hbu, hp⟩ := exc_bind hp
    cases hp
    obtain rfl : X = X' := Except.ok.inj (hX.symm.trans hX')
    have e : m.p.chains = chains := Except.ok.inj (hc.symm.trans hch)
    intro n
    show (Chains.bytes chains n).size < 2 ^ 64
    rw [← e]
    exact hb n

/-- **Where the test says yes seven strings are asked, at every digest.** -/
theorem seven_of_live (o : VerifierAndGoals.SecondHashFunctionType) (G : EntryGround) (Zk : OnBytes.K.Pub)
    (h : protocolDataWellFormedAt o Zk = true) (c : Digest) :
    (VerifierAndGoals.par7O o G Zk.pol Zk.KL Zk.lay (digToBytes c)).length = 7 := by
  obtain ⟨p, hp, hb⟩ := planned_of_live o Zk h
  exact VerifierAndGoals.length_par7O_of_planned G VerifiableInference.Desc.theCfg_size hb hp c

/-- **And the further reading returns seven digests.** -/
theorem sevenRead_of_live (o : VerifierAndGoals.SecondHashFunctionType) (G : EntryGround) (Z : VerifierAndGoals.PublicFiles)
    (h : protocolDataWellFormedAt o (VerifierAndGoals.asDescriptionFiles Z) = true) (hash : VerifiableInference.Hash) (c : Digest) :
    ((VerifierAndGoals.readMoreAtO o G Z c).evaluate hash).length = 7 := by
  obtain ⟨p, hp, hb⟩ := planned_of_live o (VerifierAndGoals.asDescriptionFiles Z) h
  exact VerifierAndGoals.length_readMoreAtO_of_planned G Z VerifiableInference.Desc.theCfg_size hb hp hash c

end FlashProve

#print axioms FlashProve.madeAt_chains
#print axioms FlashProve.planned_of_live
#print axioms FlashProve.seven_of_live
#print axioms FlashProve.sevenRead_of_live
