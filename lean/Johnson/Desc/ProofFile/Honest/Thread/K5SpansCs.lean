-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/K5SpansCs.lean: the written list of rider clauses `csHead`
(Honest/Thread/CsHead.lean) meets the two hypotheses of Honest/Thread/K5RiderSpans.lean on a list of
rider clauses, whatever its three arguments are. No definition.

  1  `k5_hsp_csHead`   each clause of `csHead` has one of the four shapes that `k5_hcl_spans` asks:
     it begins after border 327, or it speaks at one border 14 l + 9, or it reaches from 28 k + 5
     to 28 k + 10, or it is a statement on the field `g` from 14 l + 4 to 14 l + 9
  2  `k5_hcl_csHead`   so the hypothesis `hcl` of `k5_hcs_laid_M` holds for `csHead`

The proof of lemma 1 is taken from the proof of lemma 2 in a file that is not in this library, which
showed lemma 1 without stating it. The verifier's state is written `S` here; `TS` is the library's
abbreviation of `S`.

Limits.
  * The three arguments of `csHead` are variables. The facts in its clauses are not looked at here,
    only the clauses' first and last borders and, in the fourth shape, their form.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.CsHead
import Johnson.Desc.ProofFile.Honest.Thread.K5RiderSpans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc.First (S)

/-- Each clause of `csHead` has one of the four shapes. -/
theorem k5_hsp_csHead {W : Type} (ν : Nat) (st : Nat → S → Prop)
    (R : Nat → Option OnBytes.Model.Forest.Heard → Prop) :
    ∀ c ∈ (csHead ν st R : List (RiderCl W S)), 327 < c.lo ∨ (c.hi = c.lo ∧ c.lo % 14 = 9) ∨
      (c.lo % 28 = 5 ∧ c.hi = c.lo + 5) ∨
      ∃ (l : Nat) (R : Option OnBytes.Model.Forest.Heard → Prop),
        c = riderAtt (14 * l + 4) (14 * l + 9) fun a => R a.g := by
  intro c hc
  unfold csHead at hc
  rcases List.mem_append.1 hc with hc | hc
  · rcases List.mem_append.1 hc with hc | hc
    · rcases List.mem_append.1 hc with hc | hc
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact Or.inl (show 327 < 342 by omega)
        · exact Or.inl (show 327 < 343 by omega)
        · exact Or.inl (show 327 < 347 by omega)
        · exact Or.inl (show 327 < 346 by omega)
        · exact Or.inl (show 327 < 344 by omega)
        · exact Or.inl (show 327 < 346 by omega)
        · exact Or.inl (show 327 < 346 by omega)
      · obtain ⟨l, -, rfl⟩ := List.mem_map.1 hc
        exact Or.inr (Or.inl ⟨rfl, (show (14 * l + 9) % 14 = 9 by omega)⟩)
    · obtain ⟨g, -, rfl⟩ := List.mem_map.1 hc
      exact Or.inr (Or.inr (Or.inr ⟨2 * g + 1, R g, rfl⟩))
  · obtain ⟨g, -, rfl⟩ := List.mem_map.1 hc
    exact Or.inr (Or.inr (Or.inl ⟨(show (28 * g + 5) % 28 = 5 by omega),
      (show 28 * g + 10 = 28 * g + 5 + 5 by omega)⟩))

/-- The hypothesis `hcl` on the list of rider clauses holds for `csHead`. -/
theorem k5_hcl_csHead {W : Type} (ν : Nat) (st : Nat → S → Prop)
    (R : Nat → Option OnBytes.Model.Forest.Heard → Prop) :
    ∀ c ∈ (csHead ν st R : List (RiderCl W S)),
      (∀ g, g < 12 → c.lo ≠ K5.borderOf g + 1) ∧
      ((∀ g, g < 12 → c.lo ≤ K5.borderOf g → c.hi ≤ K5.borderOf g) ∨
        ∃ (lo hi : Nat) (R : Option OnBytes.Model.Forest.Heard → Prop),
          c = riderAtt lo hi fun a => R a.g) :=
  k5_hcl_spans (k5_hsp_csHead ν st R)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k5_hsp_csHead
#print axioms ProofFile.Honest.FirstThread.k5_hcl_csHead
