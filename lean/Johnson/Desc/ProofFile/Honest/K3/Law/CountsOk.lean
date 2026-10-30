-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/CountsOk.lean: every shape which a place's public parameters
fix passes the two public counts of `toHeard` (`countsOk`, Honest/K3/Law/Seated.lean). So the
statements of Honest/K3/Law/Seated.lean and Honest/K3/Law/Seats.lean that bear that hypothesis hold
without it at every place of a proof file; their other hypotheses stay. Theorems.

Terms. Honest/K3/GLOSSARY.md ("hearing", "place", "shape"). The seated hearing is `hearVia`.

What is shown.
  `le_pow_bitsFor`: n things are numbered by `bitsFor n` bits.
  `countsOk_of_shapeOwn`: the shape's own maker (Johnson/Desc/First/Look/ShapeOwn.lean) yields such
    shapes alone.
  `countsOk_of_shape`: so does `P.shape` (Johnson/Desc/First/Look/LookKind.lean).
  `hearVia_of_hearV`: the seated hearing returns where `hearV` returns, with no hypothesis on the
    counts; conditional on more than one call.
Helpers: `foldl_min_le_init`, `foldl_min_le` (on lists; the library has the array's form under the
same short name, OnBytes/Tie/Pv/Lookup/Ends/ShapePrem.lean), `le_foldl_pow`, `pow_le_foldl_pow`.

Hypotheses that remain.
  `hp`: (in `countsOk_of_shape`, `hearVia_of_hearV`) the place's parameters fix the shape h.
  `hN`, `hh`: (in `hearVia_of_hearV`) the shape has more than one call; `hearV` returns.
  `h`: (in `countsOk_of_shapeOwn`) the shape's own maker returns the shape. `hc`, `hi`: (in two
    helpers) a membership.

Users. This file is imported by Honest/K3/Law/SeatedAll.lean and Honest/K3/Law/Thread/Out.lean.

Limits. Public numbers alone.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Seated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes.Model (Fork Aff Call)
open OnBytes.Model.Forest (Shape)
open VerifiableInference.Desc.K3 (HeardV hearV faceOf toHeard toHeardG)
open VerifiableInference.Desc.K3.Law (hearVia)
open VerifiableInference.Desc.First.Look (P shapeOwn bitsFor)

theorem le_pow_bitsFor (n : Nat) : n ≤ 2 ^ bitsFor n := by
  unfold bitsFor
  split
  · simpa using ‹n ≤ 1›
  · have := Nat.lt_log2_self (n := n - 1)
    omega

theorem foldl_min_le_init (l : List Call) (m : Nat) : l.foldl (fun m c => min m c.n) m ≤ m := by
  induction l generalizing m with
  | nil => exact Nat.le_refl m
  | cons a l ih => exact Nat.le_trans (ih _) (Nat.min_le_left _ _)

theorem foldl_min_le (l : List Call) (m : Nat) (c : Call) (hc : c ∈ l) :
    l.foldl (fun m c => min m c.n) m ≤ c.n := by
  induction l generalizing m with
  | nil => simp at hc
  | cons a l ih =>
    rcases List.mem_cons.1 hc with rfl | h
    · exact Nat.le_trans (foldl_min_le_init l _) (Nat.min_le_right _ _)
    · exact ih _ h

theorem le_foldl_pow (l : List Nat) (s : Nat) : s ≤ l.foldl (fun s i => s + 2 ^ i) s := by
  induction l generalizing s with
  | nil => exact Nat.le_refl s
  | cons a l ih => exact Nat.le_trans (Nat.le_add_right _ _) (ih _)

theorem pow_le_foldl_pow (l : List Nat) (s i : Nat) (hi : i ∈ l) :
    2 ^ i ≤ l.foldl (fun s i => s + 2 ^ i) s := by
  induction l generalizing s with
  | nil => simp at hi
  | cons a l ih =>
    rcases List.mem_cons.1 hi with rfl | h
    · exact Nat.le_trans (Nat.le_add_left _ _) (le_foldl_pow l _)
    · exact ih _ h

/-- **The shape's own maker yields shapes that pass the two counts.** -/
theorem countsOk_of_shapeOwn {calls : Array Call} {lid : Nat} {h0 : Shape}
    (h : shapeOwn calls lid = some h0) : countsOk h0 = true := by
  unfold shapeOwn at h
  split at h
  · exact nomatch h
  · dsimp only at h
    split at h
    · obtain ⟨x, _, rfl⟩ := Option.map_eq_some_iff.1 h
      rw [countsOk_iff]
      refine ⟨fun i hi => ?_, fun c hc _ => ?_⟩
      · have h1 := pow_le_foldl_pow _ 0 i hi
        rw [Array.foldl_toList] at h1
        exact (Nat.pow_le_pow_iff_right (by omega)).1 (Nat.le_trans h1 (le_pow_bitsFor _))
      · have hc' : c < calls.size := hc
        have hd := foldl_min_le calls.toList lid calls[c] (Array.getElem_mem_toList hc')
        rw [Array.foldl_toList] at hd
        simp [Array.getD, hc']
        omega
    · exact nomatch h

/-- **So does the shape that a place's public parameters fix.** -/
theorem countsOk_of_shape {p : P} {h : Shape} (hp : p.shape = some h) : countsOk h = true := by
  unfold VerifiableInference.Desc.First.Look.P.shape at hp
  obtain ⟨h0, hs, hp⟩ := Option.bind_eq_some_iff.1 hp
  split at hp
  · obtain rfl := Option.some.inj hp
    have h1 : countsOk h0 = true := countsOk_of_shapeOwn hs
    exact h1
  · exact nomatch hp

/-- **The seated hearing returns where `hearV` returns.**
Conditional on the return of `hearV` and several calls. Instances:
Honest/K3/Law/SeatedGuards.lean [not in this library] (by evaluation). -/
theorem hearVia_of_hearV (p : P) (h : Shape) (hp : p.shape = some h) (hN : 1 < h.NC) {F G : Fork}
    {rs : List Fmt.RoundView} {g : HeardV} (hh : hearV (faceOf h) F rs = some (g, G)) :
    ∃ g', toHeard h (toHeardG g) = some g' ∧ hearVia p F rs = some (g', G) :=
  hearVia_returns p h hp hN (countsOk_of_shape hp) hh

#print axioms ProofFile.Honest.K3.Law.le_pow_bitsFor
#print axioms ProofFile.Honest.K3.Law.foldl_min_le_init
#print axioms ProofFile.Honest.K3.Law.foldl_min_le
#print axioms ProofFile.Honest.K3.Law.le_foldl_pow
#print axioms ProofFile.Honest.K3.Law.pow_le_foldl_pow
#print axioms ProofFile.Honest.K3.Law.countsOk_of_shapeOwn
#print axioms ProofFile.Honest.K3.Law.countsOk_of_shape
#print axioms ProofFile.Honest.K3.Law.hearVia_of_hearV

end ProofFile.Honest.K3.Law
