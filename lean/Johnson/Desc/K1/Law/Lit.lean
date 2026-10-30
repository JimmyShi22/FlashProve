-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/Lit.lean: the kind's one Boolean at the library's written-out list of the
full-size example's sendings (Johnson/G/PackLit.lean: packFullLit: for every sending its chain's
codes and its sampled messages' shapes, each with a radius).

Main names: cond_iff (the Boolean is the tests on the plan, the lengths, and the library's test on
numbers of the place's list); lit_lengths (at every element of the written-out list each code's
message length is a power of two); radFrom (the radii of a place's messages out of a list for the
sampled ones); FitsLit (a place is an element of the written-out list); cond_of_lit.
lit_lengths is by an evaluation in Lean's kernel (decide +kernel), as the library's own
packFullLit_meets is.

What is not claimed. That a place of a chain that is made of the public files is an element of the
written-out list (FitsLit) is a premise: the planner is not evaluated in the kernel. The limits of
Johnson/G/PackLit.lean and Johnson/G/PackList.lean on the map from a message to its radius stand.
Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.Caller
import Johnson.G.PackLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open Johnson.Pack

/-- **The one Boolean, taken apart.** -/
theorem cond_iff (P : Par) (rad : Nat → Nat) : condPort P rad = true ↔
    planOkOwn P = true ∧ P.codes.lengthsOk = true ∧
      allMeet P.codes (sampledList P rad) = true := by
  constructor
  · intro h
    exact ⟨(cond_parts P rad h).1, (cond_parts P rad h).2.1, cond_allMeet P rad h⟩
  · rintro ⟨h1, h2, h3⟩
    simp only [condPort, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨h1, h2⟩, fun k hk => ?_⟩
    unfold allMeet at h3
    exact List.all_eq_true.1 h3 (shapeAt P k, rad k.val) (List.mem_map.2
      ⟨k, List.mem_filter.2 ⟨List.mem_finRange k, decide_eq_true hk⟩, rfl⟩)

/-- At every element of the written-out list each code's message length is a power of two. -/
theorem lit_lengths : (Johnson.G.packFullLit.all fun x => x.1.lengthsOk) = true := by
  decide +kernel

/-- The radius of a place's message number n: that of its rank among the sampled ones in l. -/
def radFrom (P : Par) (l : List (OracleShape × Nat)) (n : Nat) : Nat :=
  ((l[(((shapesOf P).take n).filter fun s => s.answers != 0).length]?).map (·.2)).getD 0

/-- A place is the element x of a list of sendings: the codes are x's, the sampled messages' shapes
with the radii read off x are x's list, and the tests on the plan hold. -/
def FitsLit (P : Par) (x : Codes × List (OracleShape × Nat)) : Prop :=
  P.codes = x.1 ∧ sampledList P (radFrom P x.2) = x.2 ∧ planOkOwn P = true

/-- **At a place that is an element of the written-out list the one Boolean holds, at the list's own
radii.** -/
theorem cond_of_lit (P : Par) (x : Codes × List (OracleShape × Nat))
    (hx : x ∈ Johnson.G.packFullLit) (h : FitsLit P x) : condPort P (radFrom P x.2) = true := by
  obtain ⟨h1, h2, h3⟩ := h
  refine (cond_iff P _).2 ⟨h3, ?_, ?_⟩
  · rw [h1]
    exact List.all_eq_true.1 lit_lengths x hx
  · rw [h1, h2]
    exact List.all_eq_true.1 Johnson.G.packFullLit_meets x hx

end VerifiableInference.Desc.K1
