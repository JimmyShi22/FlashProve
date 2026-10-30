-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/FallSilent.lean: WHERE THE FALLS AT A PLACE SAY NOTHING AS ONE,
EACH OF THEM SAYS NOTHING. The letter fall of the rule for acceptance is made of a chain's LIST of
falls: by the member's number `fallsBy` (Honest/Law/FallFree.lean), by its place `fallOf`
(Honest/Side.lean): what the first of the falls at that place that says something says. So falls of
several groups of authors can sit at one member (at a batching: one for each run whose condition can
fail). `fallOf_mem` (Honest/Law/CoverJoin.lean) goes from «it speaks» to «one of them speaks». Here
the other way: from «it is silent» to «each of them is silent»: what the member's owner spends, with
each group's lemma «where my fall is silent my run's condition holds».

WHAT THIS IS. Lemmas on definitions of ours. None of the library's goals.

  `fallOf_silent`, `fallOf_silent_iff`, `fallsBy_silent`

Limits. Nothing on how likely a fall is. This file proves nothing about soundness, completeness,
hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.FallFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl : Type}

/-- **Silent as one: each is silent.** -/
theorem fallOf_silent {fs : List (Fall S)} {a : Place} {s : S} {ds : List Fmt.Drawn}
    (h : fallOf fs a s ds = none) (f : Fall S) (hf : f ∈ fs) (hp : f.place = a) :
    f.test s ds = none := by
  unfold fallOf at h
  exact List.findSome?_eq_none_iff.1 h f
    (List.mem_filter.2 ⟨hf, by rw [hp]; exact beq_self_eq_true a⟩)

/-- Both ways. -/
theorem fallOf_silent_iff (fs : List (Fall S)) (a : Place) (s : S) (ds : List Fmt.Drawn) :
    fallOf fs a s ds = none ↔ ∀ f ∈ fs, f.place = a → f.test s ds = none := by
  refine ⟨fun h f hf hp => fallOf_silent h f hf hp, fun h => ?_⟩
  unfold fallOf
  refine List.findSome?_eq_none_iff.2 fun f hf => ?_
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hf
  exact h f h1 (eq_of_beq h2)

/-- **By the member's number.** -/
theorem fallsBy_silent {fs : List (Fall S)} {bs : List (Block S Cl)} {j : Nat} {b : Block S Cl}
    (hb : bs[j]? = some b) {s : S} {ds : List Fmt.Drawn} (h : fallsBy fs bs j s ds = none)
    (f : Fall S) (hf : f ∈ fs) (hp : f.place = b.place) : f.test s ds = none := by
  unfold fallsBy at h
  rw [hb] at h
  exact fallOf_silent h f hf hp

end ProofFile.Honest

#print axioms ProofFile.Honest.fallOf_silent
#print axioms ProofFile.Honest.fallOf_silent_iff
#print axioms ProofFile.Honest.fallsBy_silent
