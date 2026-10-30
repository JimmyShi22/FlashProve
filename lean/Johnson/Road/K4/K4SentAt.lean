-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4SentAt.lean: the test `k4SentB` as a function of the table of steps and the
declared rounds' entries alone.

What it is for. `k4SentB Z` (Johnson/Road/K4/K4BlockPlan.lean) is the one closed test that is left
of «K4's sub-protocol passes its own test on the plan». It takes the whole public part Z. Here
stands a twin, `k4SentOn cuts es`, that takes what the test reads and nothing else: the table of
steps and the list of the first chain's declared rounds' entries; and the law that the two are one
Bool. So Lean's kernel can evaluate the twin at written values of these two lists.

What it says.
  `k4Roots_eq`   the count of roots `ProofFile.k4Roots` reads the rounds' entries alone.
  `sentB_eq`     sentB Z name = sentOn Z.cuts (Z.D.1.map (·.entry)) name, at every Z and name.
  `k4SentB_eq`   k4SentB Z = k4SentOn Z.cuts (Z.D.1.map (·.entry)), at every Z.

Limits. Equations of tests: no test is shown true anywhere. Nothing on soundness.
-/
import Johnson.Road.K4.K4BlockPlan
import Johnson.G.Eager

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4

open VerifiableInference.Desc.First (Cut)

/-- The roots that a list of entries sends, added to a. `force` (Johnson/G/Eager.lean) makes Lean's
kernel evaluate the sum at each entry, so that no long chain of additions is left standing. -/
def rootsFrom : Nat → List Fmt.Entry → Nat
  | a, [] => a
  | a, e :: es => Johnson.G.force (a + e.roots) fun b => rootsFrom b es

/-- How many roots a list of entries sends. -/
def rootsOf (es : List Fmt.Entry) : Nat := rootsFrom 0 es

/-- `rootsFrom` is the plain sum. -/
theorem rootsFrom_eq : ∀ (es : List Fmt.Entry) (a : Nat),
    rootsFrom a es = es.foldl (fun a e => a + e.roots) a
  | [], _ => rfl
  | e :: es, a => by
    rw [rootsFrom, Johnson.G.force_eq, rootsFrom_eq es]
    all_goals rfl

/-- The rounds in front of the step of the name `look`, by the table of steps. -/
def beforeAt (cuts : List Cut) (look : String) : Nat :=
  (cuts.takeWhile fun c => c.look != look).foldl (fun n c => n + c.take) 0

/-- The rounds of all steps whose names begin «‹link›.0.». -/
def takeAt (cuts : List Cut) (link : String) : Nat :=
  (cuts.filter fun c => c.look.startsWith (link ++ ".0.")).foldl (· + ·.take) 0

/-- `sentB`, from the table of steps and the entries. -/
def sentOn (cuts : List Cut) (es : List Fmt.Entry) (link : String) : Bool :=
  (cuts.any fun c => c.look == link ++ ".0.call") &&
    decide (0 < rootsOf ((es.drop (beforeAt cuts (link ++ ".0.call"))).take (takeAt cuts link)))

/-- `k4SentB`, from the table of steps and the entries. -/
def k4SentOn (cuts : List Cut) (es : List Fmt.Entry) : Bool :=
  (List.range 12).all fun g => sentOn cuts es ("G" ++ toString g)

/-- The count of roots `ProofFile.k4Roots` reads the rounds' entries alone. -/
theorem k4Roots_eq (l : List Fmt.DeclaredRound) : ProofFile.k4Roots l = rootsOf (l.map (·.entry)) := by
  unfold ProofFile.k4Roots rootsOf
  rw [rootsFrom_eq, List.foldl_map]

/-- A list made from the numbers below r is not empty just if 0 < r. -/
theorem range_map_nonempty {α : Type} (f : Nat → α) (r : Nat) :
    (!((List.range r).map f).isEmpty) = decide (0 < r) := by
  cases r with
  | zero => rfl
  | succ n => simp [List.range_succ]

/-- **`sentB` is its twin**, at every public part and every name. -/
theorem sentB_eq (Z : ProofFile.Pub) (name : String) :
    sentB Z name = sentOn Z.cuts (Z.D.1.map (·.entry)) name := by
  unfold sentB sentOn ProofFile.k4Sent ProofFile.Pub.roundsBefore?
  by_cases h : (Z.cuts.any fun c => c.look == name ++ ".0.call") = true
  · rw [if_pos h, h, Bool.true_and]
    show (!((List.range (ProofFile.k4Roots ((Z.D.1.drop (Z.roundsBefore (name ++ ".0.call"))).take
            (takeAt Z.cuts name)))).map _).isEmpty) = _
    rw [range_map_nonempty, k4Roots_eq, List.map_take, List.map_drop]
    rfl
  · rw [if_neg h, eq_false_of_ne_true h, Bool.false_and]
    rfl

/-- **`k4SentB` is its twin**, at every public part. -/
theorem k4SentB_eq (Z : ProofFile.Pub) : k4SentB Z = k4SentOn Z.cuts (Z.D.1.map (·.entry)) := by
  unfold k4SentB k4SentOn
  simp only [sentB_eq]

#print axioms OnBytes.Road.K4.rootsFrom_eq
#print axioms OnBytes.Road.K4.k4Roots_eq
#print axioms OnBytes.Road.K4.range_map_nonempty
#print axioms OnBytes.Road.K4.sentB_eq
#print axioms OnBytes.Road.K4.k4SentB_eq

end OnBytes.Road.K4
