-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/Read.lean: the small sums of the honest prover's side of an attention
segment's own rounds, which compute in the program's type, READ IN A RING: each is a finite sum.
Statements with their proofs. rho: any reading (OnBytes/Model/HideLaws.lean), which is a map from
the program's elements to a commutative ring that takes 0, 1, sums, differences and products to the
ring's. No word is asked to be below the prime.

Main names:
  `read_foldl_add`   a fold that adds g i for each member i of a list
  `read_sumE`        the sum of a list (Johnson/Desc/K5/Honest/Terms.lean)
  `sumTo_succ`, `read_sumTo`, `read_under`, `read_limbs`
                     the three sums of Johnson/Desc/K5/Honest/Faces.lean
  `read_timesN`, `read_underN`, `read_overHeads`, `read_atTokens`
                     the four of Johnson/Desc/K5/Honest/Products.lean; the short cut at a factor 0
                     changes no reading
  `read_underN_under`  the sum with the short cut reads as the sum without it

Limits. Equations on these functions alone, unconditional. Nothing is said of what the summed values
are. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Products
import OnBytes.Model.HideLaws
import OnBytes.Tie.Pv.Lookup.Ends.FoNatVal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading)
open VerifiableInference.Desc.First.Att.P (Geo eqTab ofNat)

variable {K : Type} [CommRing K] (ρ : Reading K)

/-! ## Lists -/

/-- A fold that adds g i for each member i of a list, from a on. -/
theorem read_foldl_add {α : Type} (g : α → E) : ∀ (l : List α) (a : E),
    ρ.val (l.foldl (fun s i => addE s (g i)) a) = ρ.val a + (l.map fun i => ρ.val (g i)).sum
  | [], a => by simp
  | x :: l, a => by
    rw [List.foldl_cons, read_foldl_add g l, ρ.add, List.map_cons, List.sum_cons, add_assoc]

/-- The sum of a list of elements. -/
theorem read_sumE (l : List E) : ρ.val (sumE l) = (l.map ρ.val).sum := by
  have h := read_foldl_add ρ (fun x : E => x) l zeroE
  rw [ρ.zero, zero_add] at h
  exact h

/-! ## Sums over the numbers below n -/

theorem sumTo_succ (n : Nat) (f : Nat → E) : sumTo (n + 1) f = addE (sumTo n f) (f n) := by
  unfold sumTo
  rw [List.range_succ, List.foldl_append]
  rfl

/-- The sum of f 0, .., f (n - 1). -/
theorem read_sumTo (f : Nat → E) : ∀ n : Nat,
    ρ.val (sumTo n f) = ∑ i ∈ Finset.range n, ρ.val (f i)
  | 0 => by
    rw [Finset.range_zero, Finset.sum_empty]
    exact ρ.zero
  | n + 1 => by rw [sumTo_succ, ρ.add, read_sumTo f n, Finset.sum_range_succ]

/-- The sum of w[i] f i over w's entries. -/
theorem read_under (w : Array E) (f : Nat → E) :
    ρ.val (under w f) = ∑ i ∈ Finset.range w.size, ρ.val (w.getD i zeroE) * ρ.val (f i) := by
  unfold under
  rw [read_sumTo]
  exact Finset.sum_congr rfl fun i _ => ρ.mul _ _

/-- A value of n cells: the sum of 256 ^ l times cell l. -/
theorem read_limbs (n : Nat) (f : Nat → E) :
    ρ.val (limbs n f) = ∑ l ∈ Finset.range n, (256 : K) ^ l * ρ.val (f l) := by
  unfold limbs
  rw [read_sumTo]
  refine Finset.sum_congr rfl fun l _ => ?_
  have h : ρ.val (ofNat (256 ^ l)) = ((256 ^ l : Nat) : K) := Fo.ofNat_val ρ (256 ^ l)
  rw [ρ.mul, h, Nat.cast_pow]
  rfl

/-! ## The same with the short cut at a factor 0 -/

/-- a times f (): the short cut at a = 0 changes no reading. -/
theorem read_timesN (a : E) (f : Unit → E) : ρ.val (timesN a f) = ρ.val a * ρ.val (f ()) := by
  unfold timesN
  by_cases h : a = zeroE
  · rw [if_pos (by rw [h]; exact beq_self_eq_true _), h, ρ.zero, zero_mul]
  · rw [if_neg (by rw [beq_iff_eq]; exact h), ρ.mul]

/-- The sum of w[i] f i over w's entries. -/
theorem read_underN (w : Array E) (f : Nat → E) :
    ρ.val (underN w f) = ∑ i ∈ Finset.range w.size, ρ.val (w.getD i zeroE) * ρ.val (f i) := by
  unfold underN
  rw [read_sumTo]
  exact Finset.sum_congr rfl fun i _ => read_timesN ρ _ _

/-- The sum with the short cut reads as the sum without it. -/
theorem read_underN_under (w : Array E) (f : Nat → E) :
    ρ.val (underN w f) = ρ.val (under w f) := by
  rw [read_underN, read_under]

/-- The sum over the heads of keys and values. -/
theorem read_overHeads (g : Geo) (z : Array E) (f : Nat → E) :
    ρ.val (overHeads g z f) = ∑ hk ∈ Finset.range g.G,
      ρ.val ((eqTab (z.extract 0 g.lgk)).getD hk zeroE) * ρ.val (f hk) := by
  unfold overHeads
  rw [read_sumTo]
  exact Finset.sum_congr rfl fun i _ => read_timesN ρ _ _

/-- The sum over tokens and channels. -/
theorem read_atTokens (tk ec : Array E) (f : Nat → Nat → E) :
    ρ.val (atTokens tk ec f) = ∑ i ∈ Finset.range tk.size, ρ.val (tk.getD i zeroE) *
      ∑ n ∈ Finset.range ec.size, ρ.val (ec.getD n zeroE) * ρ.val (f i n) := by
  unfold atTokens
  rw [read_underN]
  exact Finset.sum_congr rfl fun i _ => by rw [read_underN]

end H2K5.Honest

#print axioms H2K5.Honest.read_foldl_add
#print axioms H2K5.Honest.read_sumE
#print axioms H2K5.Honest.sumTo_succ
#print axioms H2K5.Honest.read_sumTo
#print axioms H2K5.Honest.read_under
#print axioms H2K5.Honest.read_limbs
#print axioms H2K5.Honest.read_timesN
#print axioms H2K5.Honest.read_underN
#print axioms H2K5.Honest.read_underN_under
#print axioms H2K5.Honest.read_overHeads
#print axioms H2K5.Honest.read_atTokens
