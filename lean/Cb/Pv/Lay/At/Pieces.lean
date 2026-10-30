-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/At/Pieces.lean: a side of the batched sumcheck's summand whose parts are vectors laid as
blocks into a long vector.

A piece is a vector v of 2^g entries that is laid into R blocks of the long vector, one after the
other from block n0 on, in block n0 + e under the public factor κ e. The extension of the piece is
  (the sum over e of κ e times the equality weight of block n0 + e) * (the extension of v),
a public coefficient in the first variables times a map in the last g variables. So a family of
pieces is a side (Cb/Pv/Lay/At/Sides.lean), and the side at a point is the extension of the long
vector that the pieces make up.

Main names:
  `PSide`: a family of pieces. `PSide.vec`: the long vector. `PSide.side`: the side.
  `PSide.val_eq`: the side at a point is the extension of the long vector.
  `cube_eq`: for parameters made of two such sides, the sum of the summand over the cube is the
  inner product of the two long vectors.
Limits: nothing is said on what the pieces are in a model.


-/
import Cb.Pv.Lay.At.Sides
import Cb.Pv.Lay.At.Place

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay.At
open Cb Finset
open Blocks (eqN ext)

noncomputable section

/-- A family of pieces. -/
structure PSide (E : Type) [Field E] (St J : Type) (k : ℕ) where
  /-- the names of the pieces -/
  I : Type
  [finI : Fintype I]
  /-- the bits of a piece's vector; its first block; the number of its blocks -/
  g : I → ℕ
  n0 : I → ℕ
  R : I → ℕ
  /-- the public factors of its blocks; its vector -/
  κ : I → St → ℕ → E
  v : St → (J → E) → I → ℕ → E
  hg : ∀ i, g i ≤ k
  hn : ∀ i, n0 i + R i ≤ 2 ^ (k - g i)

attribute [instance] PSide.finI

namespace PSide
variable {E : Type} [Field E] {St J : Type} {k : ℕ} (S : PSide E St J k)

/-- The long vector that the pieces make up. -/
def vec (st : St) (m : J → E) (y : ℕ) : E :=
  ∑ i, ∑ e ∈ range (S.R i), S.κ i st e * blk (S.g i) (S.n0 i + e) (S.v st m i) y

/-- The side. -/
def side : Side E St J k where
  I := S.I
  c := fun i st z =>
    ∑ e ∈ range (S.R i), S.κ i st e * eqN (k - S.g i) 0 (Blocks.nat z) (S.n0 i + e)
  F := fun st m i z => extAt (S.g i) (k - S.g i) (S.v st m i) (Blocks.nat z)
  dc := fun i => win 0 (k - S.g i)
  dF := fun i => win (k - S.g i) (S.g i)
  hc := fun i st => Alg.DegLE.sum _ fun e _ =>
    (degLE_eqN (k - S.g i) 0 (S.n0 i + e) (by omega)).const_mul (S.κ i st e)
  hF := fun st m i => degLE_extAt (S.g i) (k - S.g i) (S.v st m i) (by have := S.hg i; omega)
  h1 := fun i v => win_add (k - S.g i) (S.g i) v

/-- The side at a point is the extension of the long vector. -/
theorem val_eq (st : St) (m : J → E) (z : Fin k → E) :
    S.side.val st m z = ext k (S.vec st m) (Blocks.nat z) := by
  unfold Side.val vec
  rw [Blocks.ext_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [Blocks.ext_sum]
  show (∑ e ∈ range (S.R i), S.κ i st e * eqN (k - S.g i) 0 (Blocks.nat z) (S.n0 i + e)) *
    extAt (S.g i) (k - S.g i) (S.v st m i) (Blocks.nat z) = _
  rw [sum_mul]
  refine sum_congr rfl fun e he => ?_
  have hlt : S.n0 i + e < 2 ^ (k - S.g i) := by
    have := S.hn i
    have := mem_range.mp he
    omega
  have h := ext_blk (k - S.g i) (S.g i) hlt (S.v st m i) (Blocks.nat z)
  rw [Nat.sub_add_cancel (S.hg i)] at h
  rw [Blocks.ext_smul, h]
  ring

end PSide

variable {E : Type} [Field E] [Fintype E]

/-- For parameters made of two families of pieces, the sum of the summand over the cube is the inner
product of the two long vectors. -/
theorem cube_eq (P : InnPar E) (A B : PSide E P.St P.J P.k) (hA : P.a = A.side)
    (hB : P.b = B.side) (st : P.St) (m : P.J → E) :
    ∑ b : Fin P.k → Bool, P.inn.Kp.val st m (Alg.corner b) =
      ∑ y ∈ range (2 ^ P.k), A.vec st m y * B.vec st m y :=
  P.inn_cube st m _ _ (fun z => by rw [hA]; exact A.val_eq st m z)
    fun z => by rw [hB]; exact B.val_eq st m z

end
end Cb.Pv.Lay.At

#print axioms Cb.Pv.Lay.At.PSide.val_eq
#print axioms Cb.Pv.Lay.At.cube_eq
