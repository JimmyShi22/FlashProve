-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Reads/SevenAtSecondHashFunction.lean: where the planner's text at o says yes at ONE digest of 32
bytes, it says yes at EVERY digest of 32 bytes: so the further public reading at o asks seven
strings there, at every digest. Statements and proofs; no definition.

Why. `par7O o` (Johnson/Goal/Reads/ReadAtSecondHashFunction.lean) calls the planner's text at the bytes of the
digest that the first reading returned. Where that call refuses, one string is asked and not seven
(`length_par7O_error`), and nobody tests the number. A description that has called the same text at
a constant digest, and refuses where that call refused, need not test it: these laws say why.

Main statements.
  `plannedAtO_at`: what `plannedAtO o` returns at c it returns at c', with c' as its digest and the
    chains put at c'. The law `OnBytes.Tie.plannedAt_at` (OnBytes/Tie/ChainsAtCfg.lean), at o.
  `length_par7O_of_planned`: so from a yes at one c of 32 bytes: seven strings at every digest.
  `length_readMoreAtO_of_planned`: and the further reading returns seven digests.

Limits. That each of the seven strings of parameter bytes has fewer than 2 ^ 64 bytes is a premise,
as in `plannedAt_at`. Nothing says that a description calls the planner's text at a constant, nor
that it refuses where that call refuses. Nothing on what the seven digests are used for. Nothing on
soundness.

-/
import Johnson.Goal.Reads.ReadAtSecondHashFunction
import OnBytes.Tie.ChainsAtCfg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifierAndGoals
open VerifiableInference OnBytes.K.Arm.Pub
open OnBytes.Params OnBytes.Model OnBytes.Model.Verify OnBytes.Tie
open VerifiableInference.PlanWritten (plannedAtO)
open _root_.Run (digToBytes)

/-- What the planner's text at o returns at c it returns at c', with c' as its digest and the chains
put at c'. -/
theorem plannedAtO_at {o : SecondHashFunctionType} {pol KL : ByteArray} {layout : Option ByteArray}
    {c c' : ByteArray} {p : Verify.Planned} (hc : c.size = 32) (hc' : c'.size = 32)
    (hb : ∀ n : ChainName, (p.chains.bytes n).size < 2 ^ 64)
    (h : plannedAtO o pol KL layout c = .ok p) :
    plannedAtO o pol KL layout c' =
      .ok { p with cfg := c', chains := chainsAtCfg p.chains c' } := by
  unfold plannedAtO at h ⊢
  obtain ⟨X, hX, h⟩ := exc_bind h
  obtain ⟨chains, hch, h⟩ := exc_bind h
  obtain ⟨built, hbu, h⟩ := exc_bind h
  cases h
  refine (exc_step _ hX).trans ?_
  refine (exc_step _ (chainsOf_at hc hc' hb hch)).trans ?_
  refine (exc_step _ ((builtOf_at X chains c').trans hbu)).trans ?_
  rfl

/-- **From a yes of the planner's text at one digest of 32 bytes: seven strings at every one.** -/
theorem length_par7O_of_planned {o : SecondHashFunctionType} (G : EntryGround) {pol KL lay c₀ : ByteArray}
    {p : Verify.Planned} (h₀ : c₀.size = 32)
    (hb : ∀ n : ChainName, (p.chains.bytes n).size < 2 ^ 64)
    (h : plannedAtO o pol KL (some lay) c₀ = .ok p) (c : Digest) :
    (par7O o G pol KL lay (digToBytes c)).length = 7 :=
  length_par7O_ok o G pol KL lay (digToBytes c)
    (plannedAtO_at h₀ (_root_.Run.size_digToBytes c) hb h)

/-- **And the further reading returns seven digests.** -/
theorem length_readMoreAtO_of_planned {o : SecondHashFunctionType} (G : EntryGround) (Z : PublicFiles) {c₀ : ByteArray}
    {p : Verify.Planned} (h₀ : c₀.size = 32)
    (hb : ∀ n : ChainName, (p.chains.bytes n).size < 2 ^ 64)
    (h : plannedAtO o Z.pol Z.KL (some Z.lay) c₀ = .ok p) (hash : VerifiableInference.Hash)
    (c : Digest) : ((readMoreAtO o G Z c).evaluate hash).length = 7 := by
  rw [readMoreAtO_evaluate, List.length_map, List.length_map]
  exact length_par7O_of_planned G h₀ hb h c

end VerifierAndGoals

#print axioms VerifierAndGoals.plannedAtO_at
#print axioms VerifierAndGoals.length_par7O_of_planned
#print axioms VerifierAndGoals.length_readMoreAtO_of_planned
