-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/PointsOf.lean: the ties of points that Johnson/Road/K4/FrontDictOf.lean asks
(PointTies), and the three clauses on the verifier's tables of weights in SlotTies, from one tie for
each of the verifier's seven points: "the point, read, agrees with the library's, coordinate by
coordinate".

The records of true tables have the long tables' points as the last la coordinates of a product
layer's challenges (Z_V, Z_a, Z_b: lastOf), cut in the first ls and the others. The library's
records have the whole point and read it from an offset on. Here the offsets are counted.

Main names:
  `last_at`: a coordinate of the last la coordinates of a point, against a library's point that
    agrees with the whole.
  `pointTies_of`: PointTies at the letters that trueAt_of_holds, trueAt2_of_holds, trueAt3_of_holds
    and trueAt4_of_holds conclude.
  `sqW_of`, `gW_of`: the clause sqW, and the common form of the clauses g5W and g6W, on the tables
    of weights, by Johnson/Road/K4/WeightsMeet.lean.
Limits. The seven ties and the sizes are premises. Identities on public numbers: nothing on a
world, on a draw, on soundness or on hiding.


-/
import Johnson.Road.K4.FrontDictOf
import Johnson.Road.K4.NormsReadsHolds
import Johnson.Road.K4.WeightsMeet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open OnBytes.Model (Reading lastOf hiTab)
open Blocks (eqN)
open Inst.Model.FFSeg (Dim lF lFe)
open Cb.Pv.Lay.End (NormsE TermsE)
open Cb.Pv.Lay.End.Gated (GatedE)

variable {K : Type} [Field K] {ρ : Reading K}

/-- A coordinate of the last la coordinates of a point w of g + la coordinates. -/
theorem last_at {w Z : Array E} {la g : ℕ} (hZ : lastOf w la = .ok Z) (hs : w.size = g + la)
    {r : ℕ → K} (hr : ∀ j, j < w.size → pt ρ w j = r j) {j : ℕ} (hj : j < la) :
    pt ρ Z j = r (g + j) := by
  obtain ⟨_, e⟩ := Desc.First.K4.lastOf_pt (ρ := ρ) hZ hj
  have e2 : w.size - la + j = g + j := by omega
  rw [e, e2]
  exact hr _ (by omega)

/-- **PointTies**, from one tie for each of the verifier's seven points. wV, wA, wB: the challenges
of the three product layers; ZV, ZA, ZB: their last la coordinates; u: the lookup's token point, in
whatever letters the record of true tables has it. -/
theorem pointTies_of {D : Dim} {eN : NormsE K} {eT : TermsE K} {eG : GatedE K} {b sG la : ℕ}
    {wV wA wB ZV ZA ZB rt PV tV : Array E} {u : ℕ → K} (hla : la = sG + D.lT)
    (hZV : lastOf wV la = .ok ZV) (hZA : lastOf wA la = .ok ZA) (hZB : lastOf wB la = .ok ZB)
    (sV : wV.size = D.lL + 1 + b + la) (sA : wA.size = D.lL + lF D - sG + la)
    (sB : wB.size = D.lL - 1 + lFe D - sG + la)
    (r1 : ∀ j, j < wV.size → pt ρ wV j = eN.r1 j) (r5 : ∀ j, j < wA.size → pt ρ wA j = eG.r5 j)
    (r6 : ∀ j, j < wB.size → pt ρ wB j = eG.r6 j)
    (hzt : ∀ j, j < D.lT → u j = eN.zt j) (hrt : ∀ j, j < D.lT → pt ρ rt j = eT.rt j)
    (hPV : ∀ j, j < D.lT → pt ρ PV j = eN.pV j) (htV : ∀ j, j < D.lT → pt ρ tV j = eN.r2 j) :
    PointTies D eN eT eG b sG u (pt ρ rt) (pt ρ rt) (pt ρ ZV)
      (fun j => pt ρ ZV (sG + j)) (pt ρ PV) (pt ρ tV) (pt ρ ZA) (fun j => pt ρ ZA (sG + j))
      (pt ρ ZB) (fun j => pt ρ ZB (sG + j)) where
  zt := hzt
  rt := hrt
  rt' := hrt
  pV := hPV
  r2 := htV
  lowV := fun j hj => last_at hZV sV r1 (by omega)
  uV := fun j hj => by
    show pt ρ ZV (sG + j) = _
    rw [last_at hZV sV r1 (by omega)]
    congr 1
    omega
  lowA := fun j hj => last_at hZA sA r5 (by omega)
  uA := fun j hj => by
    show pt ρ ZA (sG + j) = _
    rw [last_at hZA sA r5 (by omega)]
    congr 1
    omega
  lowB := fun j hj => last_at hZB sB r6 (by omega)
  uB := fun j hj => by
    show pt ρ ZB (sG + j) = _
    rw [last_at hZB sB r6 (by omega)]
    congr 1
    omega

/-- The clause sqW. Pd, S2: the padded width of the stream and the features of a block. -/
theorem sqW_of {w : Array E} {la want a b n B Pd S2 : ℕ} {r : ℕ → K} (hw : want = a + b)
    (hr : ∀ j, j < a + b → pt ρ w j = r j) (hP : Pd = 2 ^ b * S2) (hS : 0 < S2) (hn : n ≤ 2 ^ a)
    (hB : B ≤ 2 ^ b) :
    ∀ e, (hiTab w la want).toOption = some e → ∀ i kh, i < n → kh < B →
      ρ.val (e.getD (i * Pd / S2 + kh) zeroE) = eqN (a + b) 0 r (i * 2 ^ b + kh) := by
  intro e he i kh hi hk
  rw [hw] at he
  have e1 : i * Pd / S2 = i * 2 ^ b := by
    rw [hP, ← Nat.mul_assoc]
    exact Nat.mul_div_cancel _ hS
  rw [e1]
  exact hiTab_rows he hr rfl (Nat.lt_of_lt_of_le hi hn) (Nat.lt_of_lt_of_le hk hB)

/-- The clauses g5W and g6W: rows * blocks = 2^want, and the stride is the number of blocks. -/
theorem gW_of {w : Array E} {la want want' rows blocks stride : ℕ} {r : ℕ → K}
    (hw : want = want') (hr : ∀ j, j < want' → pt ρ w j = r j) (hs : stride = blocks)
    (hx : rows * blocks = 2 ^ want') :
    ∀ e, (hiTab w la want).toOption = some e → ∀ x, x < rows * blocks →
      ρ.val (e.getD (x / blocks * stride + x % blocks) zeroE) = eqN want' 0 r x := by
  intro e he x h
  rw [hw] at he
  exact hiTab_flat he hr hs (by rw [← hx]; exact h)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.pointTies_of
#print axioms OnBytes.Road.K4.sqW_of
#print axioms OnBytes.Road.K4.gW_of
