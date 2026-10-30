-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/LastJoin.lean: FOR THE CODE SWITCH's NAMED CONDITION AT THE CLOSED CONSTANT
    (`P5J.AtMgA.K2Cond`, Johnson/Goal/Skeleton/Kinds/K2Bridge.lean): TWO NUMBERINGS OF THE 25 PLACES
    OF THE KIND AGREE. One theorem. A law file: no sub-protocol imports it.

What is said. `k2No_mOf`: at a place of the kind with number k, the number of the
    switch into group mOf k + 1 (`k2NoAt`, Johnson/P1K2R/TiesOneFour.lean) is k. By the three sorts
    of places (`k2_spots`, Johnson/P1K2R/ThreeAtConst.lean).

Limits. A fact on numbers. No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K2R.TiesOneFour
import Johnson.P1K2R.ThirdAtConst

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2
open OnBytes.Maker
open VerifiableInference.Desc (Block Chain KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (codeSwitchKind)
open VerifiableInference.Desc.First.K2Caller (spotsFitB k2NoAt WayAt)
open H2K.JointK (Sits)
open ProofFile (Cl)

theorem k2No_mOf {k : ℕ} {pl : VerifiableInference.Desc.Place} (ha : P5J.At.ps[k]? = some pl) (hk :
    pl.kind = KindName.K2) : k2NoAt (mOf k) = k := by
  rcases k2_spots k pl ha hk with ⟨l, a1, a24, rfl⟩ | rfl | rfl
  · rw [mOf_link l a1 a24]
    unfold k2NoAt
    rw [if_pos (by omega)]
    omega
  · rfl
  · rfl

end P1K2

#print axioms P1K2.k2No_mOf
