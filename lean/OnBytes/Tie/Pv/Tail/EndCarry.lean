-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/EndCarry.lean: the premise `RawRows` (OnBytes/Tie/Pv/Tail/EndAll.lean) says the
same of the smallness test's state before objectsF runs and of the state that objectsF returns.

A statement and its proof.
Main names:
  `rawRows_carry`: if objectsF returns tl' from tl, then `RawRows` at tl' and at tl are equivalent.
Limits: the sub-proof's state, the batching element and the arrays' entries are the same letters on
both sides.
-/
import OnBytes.Tie.Pv.Tail.EndSpread

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Port

open OnBytes OnBytes.Model

open Finset

variable {K : Type} [CommRing K] (ρ : Reading K) (W : World K)

include ρ in
/-- `RawRows` reads no field of the smallness test's state that objectsF sets. -/
theorem rawRows_carry (tl tl' : HTailF2) (funs : Array HFun) (F G G' : Fork) (c c' : Ctx)
    (h : tl.objectsF funs F c = .ok ((tl', G), c')) (θ : K) (A : Nat → Nat → Nat → K) :
    RawRows W tl' G' funs θ A ↔ RawRows W tl G' funs θ A := by
  obtain ⟨_, Fa0, ca0, tla0, Fb0, cb0, tlb0, Fc0, cc0, tl1, F10, c10, _, _, hJ0, hB0, hWt0, _,
    etl, _, _, _⟩ := objectsF_total ρ W tl tl' funs F G c c' h
  have ea := linJoin9_spec tl tla0 Fa0 Fb0 ca0 cb0 hJ0
  have eb := linBits9_spec tla0 tlb0 Fb0 Fc0 cb0 cc0 hB0
  obtain ⟨_, _, _, e1⟩ := weightsF_spec tlb0 tl1 Fc0 F10 cc0 c10 hWt0
  have p1 := carry4 (fun t => ∀ c, W.entry t.ix.ZZ t.zzRowTies c =
    ∑ u ∈ range t.tau, θ ^ u * A t.ix.ZZ u c) ea rfl eb rfl e1 rfl etl rfl
  have p2 := carry4 (fun t => ∀ c, W.entry t.ix.ZZ t.zzRowReads c =
    ∑ u ∈ range t.tau, θ ^ u * A t.ix.ZZ u c) ea rfl eb rfl e1 rfl etl rfl
  have p3 := carry4 (fun t => ∀ mu, mu < t.NM → ∀ p, W.entry (t.gtTree.getD mu 0) 0 p =
    ∑ i' ∈ range (t.shp.getD mu {}).mS, θ ^ (t.stepF * i') * A (t.gtTree.getD mu 0) i' p)
    ea rfl eb rfl e1 rfl etl rfl
  have p4 := carry4 (fun t => ∀ x ∈ readsList t funs, ∀ d, d < (t.mats.getD x.1.mat {}).k →
    W.entry (uOf t x.1) (posOf t x.1 x.2 d / colsU G' (uOf t x.1))
      (posOf t x.1 x.2 d % colsU G' (uOf t x.1)) = A (uOf t x.1) 0 (posOf t x.1 x.2 d))
    ea rfl eb rfl e1 rfl etl rfl
  exact ⟨fun v => ⟨p1.mp v.ties, p2.mp v.reads, p3.mp v.syms, p4.mp v.tabs⟩,
    fun v => ⟨p1.mpr v.ties, p2.mpr v.reads, p3.mpr v.syms, p4.mpr v.tabs⟩⟩

end OnBytes.Tie.Pv.Tail.Port

#print axioms OnBytes.Tie.Pv.Tail.Port.rawRows_carry
