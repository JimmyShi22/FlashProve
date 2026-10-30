-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/K5RiderSpans.lean: two lemmas on a list `hd` of riders' clauses
(`RiderCl`, Honest/Thread/Riders.lean) at the borders of kind K5's twelve sub-protocols. They stood
in Honest/Thread/K5ThroughLaidM.lean. They use nothing of that file's imports on the prover, so they
stand here over three files. No definition.

  1  `k5_hcs_laid_M`   at a list of which no clause begins right after a sub-protocol of the kind,
     and each clause either does not reach across such a sub-protocol or is a statement on what the
     lookup on the calls returned (`riderAtt` at a reading of the field `g`,
     Honest/Thread/RidersAtt.lean): each clause that speaks on both sides of the sub-protocol stays
     along the kind's clause of `keeps`, `K5KeepsM`. By the kind's authors' `k5KeepsM_here`
     (Johnson/Desc/K5/Honest/Law/KeepsM.lean)
  2  `k5_hcl_spans`   the hypothesis of 1 from the clauses' first and last borders alone, in four
     shapes

The statements and proofs are another file's [not in this library], but for one word: the verifier's
state is written `S` here, and `TS` is the library's abbreviation of `S`.

Limits.
  * The list `hd` is a variable. The list that the first chain's invariant bears is written in
    Honest/Thread/CsHead.lean.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.RidersAtt
import Johnson.Desc.ProofFile.Honest.K5.Law.Seated
import Johnson.Desc.K5.Honest.Law.KeepsM

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc.First (S)
open H2K5.Honest (K5KeepsM k5KeepsM_here)

/-- The riders' clauses stay along `K5KeepsM`, from their first and last borders and their shapes,
at whatever numbers `y` of a plan. -/
theorem k5_hcs_laid_M {W : Type} {hd : List (RiderCl W S)}
    (hcl : ∀ c ∈ hd, (∀ g, g < 12 → c.lo ≠ K5.borderOf g + 1) ∧
      ((∀ g, g < 12 → c.lo ≤ K5.borderOf g → c.hi ≤ K5.borderOf g) ∨
        ∃ (lo hi : Nat) (R : Option OnBytes.Model.Forest.Heard → Prop),
          c = riderAtt lo hi fun a => R a.g)) :
    ∀ g, g < 12 → ∀ y, ∀ c ∈ hd,
      c.lo ≠ K5.borderOf g + 1 ∧
        (c.lo ≤ K5.borderOf g → K5.borderOf g + 1 ≤ c.hi → ∀ v s s', K5KeepsM y s s' →
          c.prop (K5.borderOf g) v s → c.prop (K5.borderOf g + 1) v s') := by
  intro g hg y c hc
  obtain ⟨h1, h2⟩ := hcl c hc
  refine ⟨h1 g hg, fun hl hh v s s' hK h0 => ?_⟩
  rcases h2 with h2 | ⟨lo, hi, R, rfl⟩
  · exact absurd (h2 g hg hl) (by omega)
  · obtain ⟨a, ha, hR⟩ := h0
    obtain ⟨a₀, hd5, G, e, e'⟩ := k5KeepsM_here hK
    rw [ha] at e
    cases e
    exact ⟨_, e', hR⟩

/-- The hypothesis of `k5_hcs_laid_M` from the first and last borders alone, in four shapes: a
clause that begins after border 327, a clause of one border 14 l + 9, a clause from 28 k + 5 to
28 k + 10, and a statement on the field `g` from 14 l + 4 to 14 l + 9. The kind's sub-protocols
stand at the borders 28 g + 18. -/
theorem k5_hcl_spans {W : Type} {hd : List (RiderCl W S)}
    (h : ∀ c ∈ hd, 327 < c.lo ∨ (c.hi = c.lo ∧ c.lo % 14 = 9) ∨
      (c.lo % 28 = 5 ∧ c.hi = c.lo + 5) ∨
      ∃ (l : Nat) (R : Option OnBytes.Model.Forest.Heard → Prop),
        c = riderAtt (14 * l + 4) (14 * l + 9) fun a => R a.g) :
    ∀ c ∈ hd, (∀ g, g < 12 → c.lo ≠ K5.borderOf g + 1) ∧
      ((∀ g, g < 12 → c.lo ≤ K5.borderOf g → c.hi ≤ K5.borderOf g) ∨
        ∃ (lo hi : Nat) (R : Option OnBytes.Model.Forest.Heard → Prop),
          c = riderAtt lo hi fun a => R a.g) := by
  intro c hc
  rcases h c hc with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨l, R, rfl⟩
  · refine ⟨fun g hg => ?_, Or.inl fun g hg hl => ?_⟩ <;> unfold K5.borderOf at * <;> omega
  · refine ⟨fun g hg => ?_, Or.inl fun g hg hl => ?_⟩ <;> unfold K5.borderOf at * <;> omega
  · refine ⟨fun g hg => ?_, Or.inl fun g hg hl => ?_⟩ <;> unfold K5.borderOf at * <;> omega
  · refine ⟨fun g hg => ?_, Or.inr ⟨_, _, R, rfl⟩⟩
    show 14 * l + 4 ≠ K5.borderOf g + 1
    unfold K5.borderOf
    omega

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k5_hcs_laid_M
#print axioms ProofFile.Honest.FirstThread.k5_hcl_spans
