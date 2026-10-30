-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/KeptInGroup.lean: "WHAT THE NEXT SEGMENT KEEPS LIES IN ITS
OWN SEGMENT's GROUP", AS A TEST WITH CODE ON A TABLE's NUMBERS, AND BY THE KERNEL AT THE WRITTEN
CORE OF THE FULL SIZE (P5T.N0Full, Johnson/P5T/PlanSeatsFull.lean). Definitions with code; theorems.

Why a test. It is no fact of the numbers' make: numbersOf takes as kept every sampled seat of
segment m whose key the next segment keeps, at whatever moment it was sent; the group is what was
sent at the moments 0, 1 and 2; planSeats reads a sending's moment off its label, up to 16.

  keptInB N n      at each m < n every tenant of N.keptOf m stands in N.group m
  keptIn_of_B      a yes gives that, in the letters of AtMg.K10Left's field kept
  kept_full        **BY THE KERNEL: keptInB N0Full 25 = true**
  kept_count       BY THE KERNEL: it ranges over 36 tenants (so it is not idle; at m = 24 it is:
                   nothing is kept behind the last segment)
  kept_next_fails  a test that fails, by the kernel: "in the NEXT segment's group" is false
  k10Links_full, k10_link_lt   BY THE KERNEL: a place of the kind K10 in the written full list
                   bears a segment's number below 25

Limits. THE WRITTEN CORE ALONE: that the numbers in which a kind's law ends (At.N Zp cF) have this
core's sent and keptOf is another file's (P5J.AtMg.N_core, Johnson/P5T/CoreAtMg.lean, over the entry
tests' thirteen rows: GLOSSARY.md, "entry tests"). The full size alone. No soundness statement.

-/
import Johnson.P5T.PlanSeatsFull
import Johnson.Desc.Sound.AtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.First (Numbers flatPlacesOf)

/-- What the next segment keeps lies in its own segment's group: at the first n segments. -/
def keptInB (N : Numbers) (n : ℕ) : Bool :=
  (List.range n).all fun m => (N.keptOf m).all fun t => (N.group m).contains t

theorem keptIn_of_B {N : Numbers} {n : ℕ} (h : keptInB N n = true) :
    ∀ m < n, ∀ t ∈ N.keptOf m, t ∈ N.group m := by
  intro m hm t ht
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 h m (List.mem_range.2 hm)) t ht
  simpa using h1

set_option maxRecDepth 1000000 in
/-- **At the written core of the full size.** -/
theorem kept_full : keptInB P5T.N0Full 25 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- It ranges over 36 tenants. -/
theorem kept_count : ((List.range 25).map fun m => (P5T.N0Full.keptOf m).length).sum = 36 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- "In the next segment's group" is false. -/
theorem kept_next_fails : ((List.range 25).all fun m =>
    (P5T.N0Full.keptOf m).all fun t => (P5T.N0Full.group (m + 1)).contains t) = false := by
  decide +kernel

/-- A test with code: K10's places bear a segment's number below 25. -/
def k10LinksB : Bool :=
  (flatPlacesOf linksFull true).all fun a =>
    a.kind != KindName.K10 || decide (a.link.getD 0 < 25)

set_option maxRecDepth 1000000 in
theorem k10Links_full : k10LinksB = true := by decide +kernel

theorem k10_link_lt {a : Place} (ha : a ∈ flatPlacesOf linksFull true)
    (hk : a.kind = KindName.K10) : a.link.getD 0 < 25 := by
  have h := List.all_eq_true.1 k10Links_full a ha
  simpa [hk] using h

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.keptIn_of_B
#print axioms VerifiableInference.Desc.LinkJoin.kept_full
#print axioms VerifiableInference.Desc.LinkJoin.kept_count
#print axioms VerifiableInference.Desc.LinkJoin.kept_next_fails
#print axioms VerifiableInference.Desc.LinkJoin.k10_link_lt
