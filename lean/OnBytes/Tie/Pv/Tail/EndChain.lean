-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndChain.lean: the premise `RawRows` of the theorems on what objectsF adds
(OnBytes/Tie/Pv/Tail/EndAll.lean, EndSpread.lean), from the verifier's own later steps.

Theorems with their proofs. The theorems on objectsF ask `RawRows` at the smallness test's state
before objectsF and at the sub-proof's state G that objectsF returns. The verifier sets the row
weights and tests them later, at a state F2. This file joins the two.

Main names:
  `unitRow_run`: after the routine that sets the row weights, a table's vector that is one row has
    the weight 1 on it (`UnitRow`, OnBytes/Tie/Pv/Tail/EndRaw.lean).
  `rawRows_before`: if objectsF returns, and later the test of the weights succeeds on a view, then
    `RawRows` holds as the theorems on objectsF ask it, in every world that reads the four kinds of
    virtual row at F2 as sums of the arrays' entries.

Limits: premises on the two states stay. The batching element at F2 is G's: the steps between the
two differ by the kind of sub-proof and are not followed here. The array of the digits has at F2 the
virtual rows that the first computation sets up. Each table's vector is at F2 one row of weight 1,
and at G it has a column for every place that a read names.


-/
import OnBytes.Tie.Pv.Tail.EndCarry
import OnBytes.Tie.Pv.Tail.EndCoef
import OnBytes.Tie.Pv.Tail.EndRaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail.Port Finset

/-- After the routine that sets the row weights, a table's vector that is one row has the weight
1. -/
theorem unitRow_run (tl : HTailF2) (n0 tU : Nat) (F1 F2 : Fork) (c c' : Ctx)
    (A : UApart tl n0 tU F1) (hR : (F1.trees.getD tU {}).R = 1)
    (h : tl.coefficientsF F1 c = .ok (((), F2), c')) : UnitRow F2 tU := by
  constructor
  · have e := (coefficientsF_shape tl F1 F2 c c' h).1 tU
    have e2 : (shapeAt F2 tU).2.1 = (shapeAt F1 tU).2.1 := by rw [e]
    exact e2.trans hR
  · have e := coefficientsF_unit tl n0 tU F1 F2 c c' A h
    unfold coefAt at e
    rw [e]
    rfl

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- `RawRows` as the theorems on objectsF ask it, from the later test of the weights. -/
theorem rawRows_before (tl tl' : HTailF2) (funs : Array HFun) (F G F2 F2' : Fork)
    (c c' c2 c2' : Ctx) (W : World K) (A : Nat → Nat → Nat → K)
    (h : tl.objectsF funs F c = .ok ((tl', G), c')) (hd : c2.ch.dry = false)
    (h2 : tl'.tileSelfTestF F2 c2 = .ok (((), F2'), c2')) (hth : F2.theta = G.theta)
    (hW : ReadsRaw ρ tl' funs F2 W A)
    (hrows : (F2.trees.getD tl'.ix.ZZ {}).rows.size = 2 * tl'.zzBlocks + 2)
    (hU : ∀ x ∈ readsList tl' funs, UnitRow F2 (uOf tl' x.1) ∧
      ∀ d, d < (tl'.mats.getD x.1.mat {}).k → posOf tl' x.1 x.2 d < colsU G (uOf tl' x.1)) :
    RawRows W tl G funs (ρ.val G.theta) A := by
  have r := rawRows_run ρ tl' F2 F2' G c2 c2' funs W A hW hd h2 hrows hU
  rw [hth] at r
  exact (rawRows_carry ρ W tl tl' funs F G G c c' h _ A).1 r

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.unitRow_run
#print axioms OnBytes.Tie.Pv.Tail.rawRows_before
