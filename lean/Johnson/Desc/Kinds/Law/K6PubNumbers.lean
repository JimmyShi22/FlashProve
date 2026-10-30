-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6PubNumbers.lean: THE FACTS ON PUBLIC PARAMETERS ALONE THAT
Law/K6PubMore.lean, Law/K6LookInMade.lean AND Law/K6FormsMade.lean ASK, AS ONE LIST OF TESTS WITH
CODE, EACH UNDER A NAME; and that the list's accept gives these premises in the letters in which
the three files ask them. Definitions with code, one statement with its proof.

  k6PubTests X     the twelve tests, each with its name; one failing entry where a place of segment
                   24's two lookups is not there or makes no shape.
  k6PubC X         all of them accept.
  k6Pub_says       MAIN: what an accept gives.

WHAT IT IS NOT. THE TESTS HAVE RUN AT NO PUBLIC PARAMETERS. Nothing on a state of the verifier.
Nothing on soundness. The test on the layout's array of the reads is not in this list: it reads the
layout and the list of arrays as well (Law/ReadsEntInT.lean: readsRoomC).
LETTERS. Under "there is" in k6Pub_says' conclusion: p8, sh8: pinned by the two equations.

-/
import Johnson.Desc.Kinds.Law.TakesAt
import Johnson.Desc.Kinds.Law.RowRides
import Johnson.Desc.First.Look.K3FillCode

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes.Model.Forest (elems)
open VerifiableInference.Desc.First.Look (placeAt k3SortAt)

/-- **The tests, each under a name.** -/
def k6PubTests (X : OnBytes.Model.Verify.Public) : List (String × Bool) :=
  match placeAt X 24 false, placeAt X 24 true with
  | some p3, some p8 =>
    match p3.shape, p8.shape with
    | some h3, some h8 =>
      [("piece 3 of segment 24 is the lookup on the calls", k3SortAt X 24 3 == some false),
        ("piece 8 of segment 24 is the lookup on the digits", k3SortAt X 24 8 == some true),
        ("the calls' slots and what the head's hearing takes end at the digits' first slot",
          p3.first + elems h3 + takesOf (parOf X.hS (workOf X)) == p8.first),
        ("the digits' hidden values have room", Decidable.decide (p8.first + elems h8 ≤ p3.ns)),
        ("the calls' first point has lt coordinates at least",
          Decidable.decide ((parOf X.hS (workOf X)).sizes.lt ≤ h3.dT)),
        ("the vector of reads is not empty", X.H.nU.getD 2 0 != 0),
        ("the planes' rows: 5 bits at least", Decidable.decide (5 ≤ X.hS.lmbH)),
        ("six calls, by the number", h3.NC == 6),
        ("six calls, by the list", h3.calls.size == 6),
        ("the planes' rows: kT + 5 bits at most", Decidable.decide (X.hS.lmbH ≤ h3.kT + 5)),
        ("call 0 has ls column bits at least, by the head's layout",
          Decidable.decide (X.hS.ls ≤ (X.HLy.calls.getD 0 default).lJ)),
        ("call 0's key point has ls coordinates at least",
          Decidable.decide (X.hS.ls ≤ ((h3.calls[0]?).map (·.n)).getD 0))]
    | _, _ => [("both places of segment 24's lookups make a shape", false)]
  | _, _ => [("both places of segment 24's lookups are there", false)]

/-- All of them accept. -/
def k6PubC (X : OnBytes.Model.Verify.Public) : Bool := (k6PubTests X).all (·.2)

/-- **WHAT AN ACCEPT GIVES**, in the letters of kept_lookOut, made_lookIn and made_forms. -/
theorem k6Pub_says (X : OnBytes.Model.Verify.Public) (h : k6PubC X = true) :
    k3SortAt X 24 3 = some false ∧ k3SortAt X 24 8 = some true ∧ X.H.nU.getD 2 0 ≠ 0 ∧
      5 ≤ X.hS.lmbH ∧
      (∀ p3 h3, placeAt X 24 false = some p3 → p3.shape = some h3 →
        h3.NC = 6 ∧ h3.calls.size = 6 ∧ X.hS.lmbH ≤ h3.kT + 5 ∧
          X.hS.ls ≤ (X.HLy.calls.getD 0 default).lJ ∧
          X.hS.ls ≤ ((h3.calls[0]?).map (·.n)).getD 0) ∧
      ∃ p8 sh8, placeAt X 24 true = some p8 ∧ p8.shape = some sh8 ∧
        ∀ p3 h3, placeAt X 24 false = some p3 → p3.shape = some h3 →
          p3.first + elems h3 + takesOf (parOf X.hS (workOf X)) = p8.first ∧
            p8.first + elems sh8 ≤ p3.ns ∧ (parOf X.hS (workOf X)).sizes.lt ≤ h3.dT := by
  unfold k6PubC k6PubTests at h
  cases e3 : placeAt X 24 false with
  | none =>
    rw [e3] at h
    cases h
  | some p3 =>
    cases e8 : placeAt X 24 true with
    | none =>
      rw [e3, e8] at h
      cases h
    | some p8 =>
      rw [e3, e8] at h
      cases s3 : p3.shape with
      | none =>
        simp only [s3] at h
        cases h
      | some h3 =>
        cases s8 : p8.shape with
        | none =>
          simp only [s3, s8] at h
          cases h
        | some h8 =>
          simp only [s3, s8, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
            beq_iff_eq, bne_iff_ne, decide_eq_true_eq] at h
          obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12⟩ := h
          refine ⟨t1, t2, t6, t7, fun q3 g3 a1 a2 => ?_, p8, h8, rfl, s8, fun q3 g3 a1 a2 => ?_⟩
          · obtain rfl : p3 = q3 := Option.some.inj a1
            obtain rfl : h3 = g3 := Option.some.inj (s3.symm.trans a2)
            exact ⟨t8, t9, t10, t11, t12⟩
          · obtain rfl : p3 = q3 := Option.some.inj a1
            obtain rfl : h3 = g3 := Option.some.inj (s3.symm.trans a2)
            exact ⟨t3, t4, t5⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6Pub_says
