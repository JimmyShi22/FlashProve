-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/Starts.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4): the value (`Aff.value`) of the start form
of the squares' product layer, in a world whose slots hold the library's sums: it is one extension
of a table of products. One statement and its proof.

  **`squares_start`**    the start form of the squares' product layer. a: the layer's point: the
                       point over the norms' numbers, then lPd halves, then the norms' token point.

Not shown here. That any world meets the premises: no example is known. Anything on a sumcheck's
rounds or on its own claim. That the batching returns powers (hgp), that the program's inverse of
2 reads as a half (hhalf), and the public numbers: premises. ρ, W, the cells and the
points are free.
No property is claimed.
-/
import Johnson.Road.K4.NormsConsts
import Johnson.Road.K4.NormsReads
import OnBytes.Desc.First.NormBridge.BridgeJoints
import OnBytes.Desc.First.K4.NormsTarget

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.W
open Finset
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Lay Heard Pub normsStart)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell idnVal led bS npOf)
open Blocks (ext)
open OnBytes.Desc.First
open OnBytes.Desc.First.K4 (dataFF)

variable {K : Type} [Field K] {ρ : Reading K} {W : World K} {v : Env} {c : Cells K} {t : Cell → K}
  [scl : Scl] {D : Dim} {low u lowV uV uP uR lowE uE : ℕ → K}

/-- **The start form of the squares' product layer** is the extension, at the layer's point, of the
square of the squares' table. gam: the batching element. -/
theorem squares_start (y : Lay) (sW : ℕ) (gp rhoI PV : Array E) (lNI : ℕ) (gam : K) (a : ℕ → K)
    (hNS : ledNS y.h.xl = 9) (hNI : y.NI = D.nNu) (hhalf : ρ.val (invE (ofNat 2)) * 2 = 1)
    (hsz : rhoI.size = lNI) (hN : D.nNu ≤ 2 ^ lNI) (hd : D.d ≤ 2 ^ y.lPd)
    (hgp : ∀ s, s < 9 → ρ.val (gp.getD s zeroE) = gam ^ s)
    (ha1 : ∀ j, j < lNI → a j = pt ρ rhoI j)
    (ha2 : ∀ j, j < y.lPd → a (lNI + j) = ρ.val (invE (ofNat 2)))
    (ha3 : ∀ j, j < D.lT → a (lNI + y.lPd + j) = uP j)
    (hW : ∀ ν, ν < D.nNu → ∀ s, s < 9 → W.slot (sW + 9 * ν + s) = wHat D t ν uP s) :
    (normsStart y sW gp rhoI PV).1.value ρ W =
      ext (lNI + y.lPd + D.lT)
        (fun X => (dataFF D t lNI).sqTab y.lPd gam X * (dataFF D t lNI).sqTab y.lPd gam X) a := by
  have hh : 1 - ρ.val (invE (ofNat 2)) = ρ.val (invE (ofNat 2)) := by
    linear_combination (-1 : K) * hhalf
  have J : ρ.val (invE (ofNat 2)) ^ y.lPd * ∑ i ∈ range D.nNu, Blocks.eqN lNI 0 a i *
        ∑ s ∈ range 9, gam ^ s *
          (dataFF D t lNI).trueW (fun j => a (lNI + y.lPd + j)) (9 * i + s) =
      ext (lNI + y.lPd + D.lT)
        (fun X => (dataFF D t lNI).sqTab y.lPd gam X * (dataFF D t lNI).sqTab y.lPd gam X) a :=
    D6.Bridge.joint_squares (dataFF D t lNI) y.lPd hd hN gam (ρ.val (invE (ofNat 2))) hh a ha2
  rw [← J, normsStart_value, hNS, hNI, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i < D.nNu := mem_range.mp hi
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun s hs => ?_
  have hs' : s < 9 := mem_range.mp hs
  have e1 : (dataFF D t lNI).trueW (fun j => a (lNI + y.lPd + j)) (9 * i + s) =
      wHat D t i uP s := by
    unfold D6.Bridge.Data.trueW
    rw [show (9 * i + s) / 9 = i by omega, show (9 * i + s) % 9 = s by omega]
    exact Desc.First.K4.ext_pt _ ha3
  rw [e1, ρ.pow, hgp s hs', eqTab_value ρ rhoI i (by rw [hsz]; omega), hsz,
    Rows.eqN_same lNI 0 (a := pt ρ rhoI) (a' := a)
      (fun j hj => by rw [Nat.zero_add]; exact (ha1 j hj).symm) i, hW i hi' s hs']
  ring

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.squares_start
