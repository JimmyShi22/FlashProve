-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/KeyLevelF.lean: the summand of a level of a product tree, as a tower.

A level of a product tree claims the value of a multilinear map A at a point z. On the cube, A is
the product of the two halves F0, F1 of the next level's map. So A(z) is the sum over the cube of
the equality polynomial at z times F0 times F1, and a sumcheck on the product of two shown maps,
under equality weights at the coordinates of z, takes the claim to claims on F0 and F1
(OnBytes/Iop/Lkp.lean: levelChain, summandProduct). This file builds the tower of that summand
(OnBytes/Slice/KeyPscF.lean) for any two multilinear maps. No protocol occurs here.

Maps are functions on lists of field elements. A map is multilinear on lists of n elements (ML) if
it is affine in the first coordinate and, with the first coordinate fixed at any element,
multilinear on lists of n - 1 elements. Nothing is asked at lists of another length. The order of
the coordinates is the order of the sumcheck's rounds.

Main definitions: ML, bil (the sum over the cube of the equality polynomial times two maps), prodT
(the tower), CubeEq (on the cube one map is the product of two others).

Main theorems: ML.congr, bil_congr, bil_left, bil_right, tower_prodT (the tower, for all
multilinear F0, F1 and all mask entries), prodT_nil (its sum is bil), prodT_full (its value at a
full list of challenges), ml_eq_bil (its sum is A at z).

Not claimed. That a given table's extension is multilinear in this sense. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.KeyPscF

set_option autoImplicit false

namespace OnBytes.Slice.PscF
open Prob Cb

/-- F is multilinear on lists of n elements. -/
def ML : ℕ → (List GE → GE) → Prop
  | 0, _ => True
  | n + 1, F =>
    (∀ x q, q.length = n → F (x :: q) = (1 - x) * F (0 :: q) + x * F (1 :: q)) ∧
      ∀ x, ML n fun q => F (x :: q)

/-- Multilinearity reads a map at lists of n elements alone. -/
theorem ML.congr : ∀ {n : ℕ} {F F' : List GE → GE}, (∀ q, q.length = n → F q = F' q) → ML n F →
    ML n F'
  | 0, _, _, _, _ => trivial
  | n + 1, _, _, h, hF =>
    ⟨fun x q hq => by
        rw [← h (x :: q) (congrArg (· + 1) hq), ← h (0 :: q) (congrArg (· + 1) hq),
          ← h (1 :: q) (congrArg (· + 1) hq)]
        exact hF.1 x q hq,
      fun x => ML.congr (fun q hq => h (x :: q) (congrArg (· + 1) hq)) (hF.2 x)⟩

/-- The sum over the cube of the equality polynomial at zs times F0 times F1. -/
def bil : List GE → (List GE → GE) → (List GE → GE) → GE
  | [], F0, F1 => F0 [] * F1 []
  | z :: zs, F0, F1 =>
    (1 - z) * bil zs (fun q => F0 (0 :: q)) (fun q => F1 (0 :: q)) +
      z * bil zs (fun q => F0 (1 :: q)) fun q => F1 (1 :: q)

/-- The sum reads the two maps at lists of as many elements as the point has. -/
theorem bil_congr : ∀ (zs : List GE) {F F' G G' : List GE → GE},
    (∀ q, q.length = zs.length → F q = F' q) → (∀ q, q.length = zs.length → G q = G' q) →
    bil zs F G = bil zs F' G'
  | [], _, _, _, _, h, h' => by
    show _ * _ = _ * _
    rw [h [] rfl, h' [] rfl]
  | z :: zs, F, F', G, G', h, h' => by
    show (1 - z) * bil zs (fun q => F (0 :: q)) (fun q => G (0 :: q)) +
        z * bil zs (fun q => F (1 :: q)) (fun q => G (1 :: q)) =
      (1 - z) * bil zs (fun q => F' (0 :: q)) (fun q => G' (0 :: q)) +
        z * bil zs (fun q => F' (1 :: q)) fun q => G' (1 :: q)
    rw [bil_congr zs (fun q hq => h (0 :: q) (congrArg (· + 1) hq))
        fun q hq => h' (0 :: q) (congrArg (· + 1) hq),
      bil_congr zs (fun q hq => h (1 :: q) (congrArg (· + 1) hq))
        fun q hq => h' (1 :: q) (congrArg (· + 1) hq)]

/-- The sum is linear in the first map. -/
theorem bil_left (a b : GE) : ∀ (zs : List GE) (F F' G : List GE → GE),
    bil zs (fun q => a * F q + b * F' q) G = a * bil zs F G + b * bil zs F' G
  | [], F, F', G => by
    show (a * F [] + b * F' []) * G [] = a * (F [] * G []) + b * (F' [] * G [])
    ring
  | z :: zs, F, F', G => by
    show (1 - z) * bil zs (fun q => a * F (0 :: q) + b * F' (0 :: q)) (fun q => G (0 :: q)) +
        z * bil zs (fun q => a * F (1 :: q) + b * F' (1 :: q)) (fun q => G (1 :: q)) =
      a * ((1 - z) * bil zs (fun q => F (0 :: q)) (fun q => G (0 :: q)) +
        z * bil zs (fun q => F (1 :: q)) fun q => G (1 :: q)) +
      b * ((1 - z) * bil zs (fun q => F' (0 :: q)) (fun q => G (0 :: q)) +
        z * bil zs (fun q => F' (1 :: q)) fun q => G (1 :: q))
    rw [bil_left a b zs (fun q => F (0 :: q)) (fun q => F' (0 :: q)),
      bil_left a b zs (fun q => F (1 :: q)) (fun q => F' (1 :: q))]
    ring

/-- The sum is linear in the second map. -/
theorem bil_right (a b : GE) : ∀ (zs : List GE) (F G G' : List GE → GE),
    bil zs F (fun q => a * G q + b * G' q) = a * bil zs F G + b * bil zs F G'
  | [], F, G, G' => by
    show F [] * (a * G [] + b * G' []) = a * (F [] * G []) + b * (F [] * G' [])
    ring
  | z :: zs, F, G, G' => by
    show (1 - z) * bil zs (fun q => F (0 :: q)) (fun q => a * G (0 :: q) + b * G' (0 :: q)) +
        z * bil zs (fun q => F (1 :: q)) (fun q => a * G (1 :: q) + b * G' (1 :: q)) =
      a * ((1 - z) * bil zs (fun q => F (0 :: q)) (fun q => G (0 :: q)) +
        z * bil zs (fun q => F (1 :: q)) fun q => G (1 :: q)) +
      b * ((1 - z) * bil zs (fun q => F (0 :: q)) (fun q => G' (0 :: q)) +
        z * bil zs (fun q => F (1 :: q)) fun q => G' (1 :: q))
    rw [bil_right a b zs (fun q => F (0 :: q)) (fun q => G (0 :: q)),
      bil_right a b zs (fun q => F (1 :: q)) (fun q => G (1 :: q))]
    ring

/-! ## Polynomials with three coefficients -/

/-- Three coefficients. -/
def c3 (a b c : GE) : ℕ → GE := fun t => if t = 0 then a else if t = 1 then b else if t = 2 then c
  else 0

/-- The value of a polynomial with three coefficients. -/
theorem pv_c3 (a b c x : GE) : pv 3 (c3 a b c) x = a + b * x + c * x ^ 2 := by
  unfold pv c3
  simp [Finset.sum_range_succ]

/-- Its sum under a factor of the equality polynomial. -/
theorem sum_c3 (z a b c : GE) : (Weight.equality z 3).sum (c3 a b c) = a + z * b + z * c := by
  unfold Weight.sum c3 Weight.equality
  simp [Finset.sum_range_succ, List.replicate]

/-! ## The tower -/

/-- The tower of the product of two shown maps, under equality weights at zs and with the last
variable Y: each map's value has Y times its own mask entry (r0, r1) added, and Y is summed by
reading at 0. -/
def prodT (r0 r1 : GE) : List GE → (List GE → GE) → (List GE → GE) → List GE → GE
  | [], F0, F1, [] => F0 [] * F1 []
  | [], F0, F1, β :: _ => (F0 [] + β * r0) * (F1 [] + β * r1)
  | z :: zs, F0, F1, [] => bil (z :: zs) F0 F1
  | _ :: zs, F0, F1, x :: p => prodT r0 r1 zs (fun q => F0 (x :: q)) (fun q => F1 (x :: q)) p

/-- The tower's sum is the sum over the cube. -/
theorem prodT_nil (r0 r1 : GE) (zs : List GE) (F0 F1 : List GE → GE) :
    prodT r0 r1 zs F0 F1 [] = bil zs F0 F1 := by cases zs <;> rfl

/-- The product of two multilinear maps is a tower, whatever the two mask entries. -/
theorem tower_prodT (r0 r1 : GE) : ∀ (zs : List GE) (F0 F1 : List GE → GE), ML zs.length F0 →
    ML zs.length F1 →
    Tower (zs.map (Weight.equality · 3) ++ [Weight.atZero 3]) (prodT r0 r1 zs F0 F1)
  | [], F0, F1, _, _ => by
    refine ⟨⟨c3 (F0 [] * F1 []) (F0 [] * r1 + F1 [] * r0) (r0 * r1), ?_, fun x => ?_⟩,
      fun _ => trivial⟩
    · show (Weight.equality 0 3).sum _ = F0 [] * F1 []
      rw [sum_c3]
      ring
    · show pv 3 _ x = (F0 [] + x * r0) * (F1 [] + x * r1)
      rw [pv_c3]
      ring
  | z :: zs, F0, F1, h0, h1 => by
    refine ⟨⟨c3 (bil zs (fun q => F0 (0 :: q)) fun q => F1 (0 :: q))
        (bil zs (fun q => F0 (0 :: q)) (fun q => F1 (1 :: q)) +
          bil zs (fun q => F0 (1 :: q)) (fun q => F1 (0 :: q)) -
          2 * bil zs (fun q => F0 (0 :: q)) fun q => F1 (0 :: q))
        (bil zs (fun q => F0 (0 :: q)) (fun q => F1 (0 :: q)) -
          bil zs (fun q => F0 (0 :: q)) (fun q => F1 (1 :: q)) -
          bil zs (fun q => F0 (1 :: q)) (fun q => F1 (0 :: q)) +
          bil zs (fun q => F0 (1 :: q)) fun q => F1 (1 :: q)), ?_, fun x => ?_⟩, fun x => ?_⟩
    · show (Weight.equality z 3).sum _ =
        (1 - z) * bil zs (fun q => F0 (0 :: q)) (fun q => F1 (0 :: q)) +
          z * bil zs (fun q => F0 (1 :: q)) fun q => F1 (1 :: q)
      rw [sum_c3]
      ring
    · show pv 3 _ x = prodT r0 r1 zs (fun q => F0 (x :: q)) (fun q => F1 (x :: q)) []
      rw [prodT_nil, pv_c3, bil_congr zs (F' := fun q => (1 - x) * F0 (0 :: q) + x * F0 (1 :: q))
          (G' := fun q => (1 - x) * F1 (0 :: q) + x * F1 (1 :: q)) (h0.1 x) (h1.1 x),
        bil_left, bil_right, bil_right]
      ring
    · exact tower_prodT r0 r1 zs _ _ (h0.2 x) (h1.2 x)

/-- The tower's value at a full list of challenges. -/
theorem prodT_full (r0 r1 : GE) : ∀ (zs : List GE) (F0 F1 : List GE → GE) (γ : List GE) (β : GE),
    γ.length = zs.length →
    prodT r0 r1 zs F0 F1 (γ ++ [β]) = (F0 γ + β * r0) * (F1 γ + β * r1)
  | [], _, _, [], _, _ => rfl
  | _ :: zs, F0, F1, x :: γ, β, h =>
    prodT_full r0 r1 zs (fun q => F0 (x :: q)) (fun q => F1 (x :: q)) γ β (Nat.succ.inj h)

/-! ## The sum is the claim -/

/-- On the cube of n variables A is the product of F0 and F1. -/
def CubeEq : ℕ → (List GE → GE) → (List GE → GE) → (List GE → GE) → Prop
  | 0, A, F0, F1 => A [] = F0 [] * F1 []
  | n + 1, A, F0, F1 =>
    CubeEq n (fun q => A (0 :: q)) (fun q => F0 (0 :: q)) (fun q => F1 (0 :: q)) ∧
      CubeEq n (fun q => A (1 :: q)) (fun q => F0 (1 :: q)) fun q => F1 (1 :: q)

/-- A multilinear map that is the product of F0 and F1 on the cube has, at any point zs, the sum
over the cube as its value. -/
theorem ml_eq_bil : ∀ (zs : List GE) (A F0 F1 : List GE → GE), ML zs.length A →
    CubeEq zs.length A F0 F1 → A zs = bil zs F0 F1
  | [], _, _, _, _, h => h
  | z :: zs, A, F0, F1, hA, h => by
    show A (z :: zs) = (1 - z) * bil zs (fun q => F0 (0 :: q)) (fun q => F1 (0 :: q)) +
      z * bil zs (fun q => F0 (1 :: q)) fun q => F1 (1 :: q)
    rw [hA.1 z zs rfl, ml_eq_bil zs (fun q => A (0 :: q)) _ _ (hA.2 0) h.1,
      ml_eq_bil zs (fun q => A (1 :: q)) _ _ (hA.2 1) h.2]

end OnBytes.Slice.PscF
