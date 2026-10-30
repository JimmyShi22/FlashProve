-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/At/Sides.lean: the parameters of a batched sumcheck of inner products
(Cb/Pv/Lay/Inner.lean) whose summand is the product of two sides, each a sum of parts.

The summand of the batched sumcheck of a layers' sub-proof is a product A(X) * B(X). Each side is a
sum of parts. A part is a public coefficient, a function of the state and of the point, times a map
whose value at the last point is revealed. In each variable the degrees of a part's coefficient and
map add up to at most 1. The terms of the summand are then the products of a part of the first side
with a part of the second, and the conditions of the parameters on the terms' degrees hold for all
pairs at once.

Main names:
  `Side`: one side: the parts' names, coefficients, maps, degrees and their conditions.
  `Side.val`: the side at a point.
  `InnPar`: two sides, with the incoming form, the target and the places of the sumcheck's masks.
  `InnPar.inn`: the parameters of the sumcheck. No map is kept.
  `inn_val`: the summand at a point is the product of the two sides.
  `inn_cube`: if each side is the extension of a long vector, the sum of the summand over the cube
  is the inner product of the two vectors.
Limits: nothing is said on what the coefficients and maps are in a model. Nothing is said on an
honest prover, on completeness or on zero knowledge.


-/
import Cb.Pv.Lay.Inner
import Cb.Pv.Lay.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay.At
open Cb Finset

noncomputable section

/-- One side of the summand: a sum of parts. -/
structure Side (E : Type) [Field E] (St J : Type) (k : ℕ) where
  /-- the names of the parts -/
  I : Type
  [finI : Fintype I]
  /-- the public coefficient and the revealed map of a part -/
  c : I → St → (Fin k → E) → E
  F : St → (J → E) → I → (Fin k → E) → E
  /-- their degrees -/
  dc : I → Fin k → ℕ
  dF : I → Fin k → ℕ
  hc : ∀ i st, Alg.DegLE (dc i) (c i st)
  hF : ∀ st m i, Alg.DegLE (dF i) (F st m i)
  h1 : ∀ i v, dc i v + dF i v ≤ 1

attribute [instance] Side.finI

/-- The side at a point. -/
def Side.val {E : Type} [Field E] {St J : Type} {k : ℕ} (S : Side E St J k) (st : St) (m : J → E)
    (z : Fin k → E) : E := ∑ i, S.c i st z * S.F st m i z

/-- Two sides, and what the sumcheck adds. -/
structure InnPar (E : Type) [Field E] [Fintype E] where
  J : Type
  [finJ : Fintype J]
  k : ℕ
  St : Type
  a : Side E St J k
  b : Side E St J k
  inc : Slf E St J
  tg : St → E
  wAt : PIdx (ldPartFmt E k (fun _ => 2) ++ [pDummy E 2]) → J
  cAt : a.I ⊕ b.I → J

attribute [instance] InnPar.finJ

variable {E : Type} [Field E] [Fintype E]

namespace InnPar
variable (P : InnPar E)

/-- The term of a pair of parts. -/
def term (q : P.a.I × P.b.I) : LdPartTm E P.St (P.a.I ⊕ P.b.I) P.k :=
  ⟨fun st z => P.a.c q.1 st z * P.b.c q.2 st z, [.inl q.1, .inr q.2]⟩

/-- The parameters of the sumcheck. -/
def inn : InnL E where
  J := P.J
  k := P.k
  St := P.St
  A := P.a.I ⊕ P.b.I
  B := PEmpty
  F := fun st m x z => Sum.elim (fun i => P.a.F st m i z) (fun j => P.b.F st m j z) x
  Fb := fun _ _ b _ => b.elim
  da := Sum.elim P.a.dF P.b.dF
  db := fun b => b.elim
  hF := fun st m x => by
    rcases x with i | j
    · exact P.a.hF st m i
    · exact P.b.hF st m j
  hFb := fun _ _ b => b.elim
  t0 := (Finset.univ : Finset (P.a.I × P.b.I)).toList.map P.term
  tb := fun b => b.elim
  h0 := fun t ht => by
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 ht
    refine ⟨⟨fun v => P.a.dc q.1 v + P.b.dc q.2 v,
      fun st => (P.a.hc q.1 st).mul (P.b.hc q.2 st), fun v => ?_⟩, le_refl 2⟩
    have h1 := P.a.h1 q.1 v
    have h2 := P.b.h1 q.2 v
    show P.a.dc q.1 v + P.b.dc q.2 v + (P.a.dF q.1 v + (P.b.dF q.2 v + 0)) ≤ 2
    omega
  hb := fun b => b.elim
  inc := P.inc
  tg := P.tg
  wAt := P.wAt
  cAt := P.cAt
  Rd := fun _ _ => True

/-- The summand at a point is the product of the two sides. -/
theorem inn_val (st : P.St) (m : P.J → E) (z : Fin P.k → E) :
    P.inn.Kp.val st m z = P.a.val st m z * P.b.val st m z := by
  unfold KeptSm.val LdPartSm.val LdPartSm.pol Side.val
  rw [show (∑ b, P.inn.Kp.polB st z (fun a => P.inn.Sm.F st m a z) b * P.inn.Kp.Fb st m b z) = 0
    from Finset.sum_eq_zero fun b _ => PEmpty.elim b, add_zero]
  show (((Finset.univ : Finset (P.a.I × P.b.I)).toList.map P.term).map _).sum = _
  rw [List.map_map, Finset.sum_map_toList, Finset.sum_mul_sum, ← Finset.univ_product_univ,
    Finset.sum_product]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  show P.a.c i st z * P.b.c j st z * (P.a.F st m i z * (P.b.F st m j z * 1)) = _
  ring

/-- If each side is the extension of a long vector, the sum over the cube is the inner product of
the two vectors. -/
theorem inn_cube (st : P.St) (m : P.J → E) (VA VB : ℕ → E)
    (hA : ∀ z, P.a.val st m z = Blocks.ext P.k VA (Blocks.nat z))
    (hB : ∀ z, P.b.val st m z = Blocks.ext P.k VB (Blocks.nat z)) :
    ∑ b : Fin P.k → Bool, P.inn.Kp.val st m (Alg.corner b) =
      ∑ y ∈ range (2 ^ P.k), VA y * VB y := by
  rw [← Alg.sum_num fun y => VA y * VB y]
  exact sum_congr rfl fun b _ => by
    rw [inn_val, hA, hB]
    exact congrArg₂ (· * ·) (ext_corner P.k VA b) (ext_corner P.k VB b)

end InnPar

end
end Cb.Pv.Lay.At

#print axioms Cb.Pv.Lay.At.InnPar.inn_val
#print axioms Cb.Pv.Lay.At.InnPar.inn_cube
