-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/KeyForests.lean: the two lookups of the key read as forests, and what that says of a
matrix in range: `partsIn_iff_inRange` and the lemmas under it.

E2E/KeyPlanesAtFull.lean, E2E/KeyPadding.lean and E2E/KeyMidAtWritten.lean use them.
-/
import Cb.Gen.WfKeys
import Cb.Gen.LkpAlg
import Alg.Mle
import Johnson.Top.H.KeyTemplate
import Johnson.Pack.KeyPort
import Johnson.Top.H.KeyPortAt
import Johnson.Top.H.KeyRangesThm
import Johnson.Top.H.KeyAny
import Johnson.Flat.LedgerClaim
import Johnson.Top.H.KeyMeaning

set_option autoImplicit false
set_option relaxedAutoImplicit false

set_option autoImplicit false

namespace Cb
open Finset Blocks Blocks.Rng

namespace Keys
variable {F : Type} [Field F] (K : Keys F) (E : Type) [Field E] [Algebra F E]

def oE (f u : ℕ) : E := algebraMap F E (K.off f u)
def coE (f u : ℕ) (r : Fin K.rows) : E := algebraMap F E (K.coeff f u r.val)
variable {E}

end Keys

namespace Spec

end Spec

end Cb

set_option autoImplicit false
set_option relaxedAutoImplicit false


namespace Johnson.Pack
open Inst.Model Inst.Model.All Iop Prob Hiop Cb Cb.Gl.Ref Cb.Gl.Bld Cb.Lkp Cm Cm.WfGl
open Blocks Blocks.Rng OnBytes.Slice
open Inst.Model.Layout (kRef hRef m2 units)
open OnBytes.Params (WfRun WfPart WfLookup)

/-! ### Live rows of keys -/

section Plan
variable {F : Type} [Field F] (h k D B lp m₂ : ℕ) (y0 y1 : ℕ → ℕ)

end Plan

/-! ### The value -/

section Val
variable (s : Scales) (l₀ l₁ : WfLookup)

variable {l₀ l₁}

/-- The first lookup covers the library's first forest. -/
theorem cover₀ (h : RangesOK l₀ l₁) :
    Covers 8 (fun u => ((u : ℕ) : Gl.E)) 22 l₀.parts.length (fun f => (partAt l₀ f).logPlaces)
      (keysGl.oE Gl.E 0) (keysGl.coE Gl.E 0) (fun f => oP l₀ (partAt l₀ f))
      (fun f => coP hRef l₀ (partAt l₀ f)) := by
  refine covers_first hRef 8 22 l₀ _ _ (covers_rows _ _ h.cov₀).1 h.runs₀ h.fit₀
    (covers_rows _ _ h.cov₀).2 h.pad₀ (by decide) (fun v hv => ⟨?_, ?_⟩) fun v hv => ⟨?_, 0, ?_, ?_⟩
  · unfold Keys.oE
    rw [(live0 v hv).1, toF_lit 128 _ h.off₀]
    norm_cast
  · funext r
    unfold Keys.coE
    rw [(live0 v hv).2]
    split <;> simp
  · funext r
    unfold Keys.coE
    rw [(idle0 v hv).2, map_zero]
  · exact Nat.pos_of_ne_zero (by positivity)
  · unfold Keys.oE
    rw [(idle0 v hv).1, map_zero, Nat.cast_zero]

/-- The second lookup covers the library's second forest. -/
theorem cover₁ (h : RangesOK l₀ l₁) :
    Covers 13 (fun u => ((u : ℕ) : Gl.E)) 22 l₁.parts.length (fun f => (partAt l₁ f).logPlaces)
      (keysGl.oE Gl.E 1) (keysGl.coE Gl.E 1) (fun f => oP l₁ (partAt l₁ f))
      (fun f => coP hRef l₁ (partAt l₁ f)) := by
  refine covers_gen hRef 13 22 1527800 l₁ _ _ pairY h.runs₁ h.pad₁ (by decide)
    (fun v hv => ⟨?_, ?_⟩) (fun v hv => ⟨?_, 0, ?_, ?_⟩) h.P1 h.P2
  · unfold Keys.oE
    rw [(live1 v hv).1, toF_lit 4096 _ h.off₁]
    norm_cast
  · funext r
    unfold Keys.coE
    rw [(live1 v hv).2, h.w₁]
    show _ = ∑ q ∈ Finset.range 2, _
    rw [Finset.sum_range_succ, Finset.sum_range_one, map_add]
    congr 1
    · show _ = algebraMap GF GE (toF 1) * if r.val = pairY v 0 then 1 else 0
      rw [toF_one, map_one, one_mul]
      unfold pairY
      rw [if_pos rfl]
      split <;> simp
    · show _ = algebraMap GF GE (toF 256) * if r.val = pairY v 1 then 1 else 0
      rw [toF_lit 256 256 rfl]
      unfold pairY
      rw [if_neg Nat.one_ne_zero]
      split <;> simp
  · funext r
    unfold Keys.coE
    rw [(idle1 v hv).2, map_zero]
  · exact Nat.pos_of_ne_zero (by positivity)
  · unfold Keys.oE
    rw [(idle1 v hv).1, map_zero, Nat.cast_zero]

end Val

end Johnson.Pack

set_option autoImplicit false
set_option relaxedAutoImplicit false


namespace Johnson.Pack
open Iop Prob Hiop Cb Cb.Lkp Cm Cm.WfGl OnBytes.Slice
open Inst.Model.Layout (hRef)
open OnBytes.Params (WfRun WfPart WfLookup)

/-- For every matrix: the parts lie in their tables if and only if the library's two forests do. -/
theorem parts_iff_forests {l₀ l₁ : WfLookup} (h : RangesOK l₀ l₁) (k : ℕ)
    (M : Fin hRef × (Fin k → Bool) → GE) :
    PartsIn l₀ l₁ k M ↔
      InTable (22 + k) 8 (keyOf k M (keysGl.oE GE 0) (keysGl.coE GE 0))
        (fun u => ((u : ℕ) : GE)) ∧
      InTable (22 + k) 13 (keyOf k M (keysGl.oE GE 1) (keysGl.coE GE 1))
        (fun u => ((u : ℕ) : GE)) := by
  rw [inT_cover k 8 _ M 22 _ _ _ _ _ _ (cover₀ h), inT_cover k 13 _ M 22 _ _ _ _ _ _ (cover₁ h),
    h.n₀, h.n₁]
  exact Iff.rfl

/-- At the two lookups at full size. -/
theorem full_iff_forests (k : ℕ) (M : Fin hRef × (Fin k → Bool) → GE) :
    PartsIn lk0Full lk1Full k M ↔
      InTable (22 + k) 8 (keyOf k M (keysGl.oE GE 0) (keysGl.coE GE 0))
        (fun u => ((u : ℕ) : GE)) ∧
      InTable (22 + k) 13 (keyOf k M (keysGl.oE GE 1) (keysGl.coE GE 1))
        (fun u => ((u : ℕ) : GE)) :=
  parts_iff_forests rangesOK_full k M

section Any
variable (C : ConfigurationWithOutOfDomainSample) (k : ℕ) (mat : C.Msg → Fin hRef × (Fin k → Bool) → GE)

variable (l₀ l₁ : WfLookup)

end Any
end Johnson.Pack

set_option autoImplicit false
set_option relaxedAutoImplicit false


namespace Johnson.Pack
open Inst.Model Inst.Model.All Cb Cb.Lkp Cm Cm.WfGl OnBytes.Slice Blocks Blocks.Rng
open Inst.Model.Layout (kRef hRef m2 units)

theorem liveE0 (v : ℕ) (hv : v < hRef) : keysGl.oE GE 0 v = 128 ∧
    keysGl.coE GE 0 v = fun r : Fin hRef => if r.val = v then (1 : GE) else 0 := by
  refine ⟨?_, ?_⟩
  · unfold Keys.oE
    rw [(live0 v hv).1]
    exact map_ofNat _ 128
  · funext r
    unfold Keys.coE
    rw [(live0 v hv).2]
    split <;> simp

theorem liveE1 (v : ℕ) (hv : v < 1527800) : keysGl.oE GE 1 v = 4096 ∧
    keysGl.coE GE 1 v = fun r : Fin hRef =>
      (if r.val = pairY v 0 then (1 : GE) else 0) + if r.val = pairY v 1 then 256 else 0 := by
  refine ⟨?_, ?_⟩
  · unfold Keys.oE
    rw [(live1 v hv).1]
    exact map_ofNat _ 4096
  · funext r
    unfold Keys.coE
    rw [(live1 v hv).2, map_add]
    congr 1
    · show _ = if r.val = Layout.Bridge.y0 ppref kRef v then (1 : GE) else 0
      by_cases h : r.val = Layout.Bridge.y0 ppref kRef v
      · rw [if_pos h, if_pos h, map_one]
      · rw [if_neg h, if_neg h, map_zero]
    · show _ = if r.val = Layout.Bridge.y1 ppref kRef v then (256 : GE) else 0
      by_cases h : r.val = Layout.Bridge.y1 ppref kRef v
      · rw [if_pos h, if_pos h]
        exact map_ofNat _ 256
      · rw [if_neg h, if_neg h, map_zero]

section
variable (k : ℕ) (M : Fin hRef × (Fin k → Bool) → GE)

/-- The first forest lies in its table if and only if 128 plus each entry is below 2^8. -/
theorem forest0_iff :
    InTable (22 + k) 8 (keyOf k M (keysGl.oE GE 0) (keysGl.coE GE 0)) (fun u => ((u : ℕ) : GE)) ↔
      ∀ (y : Fin hRef) (c : ℕ), c < 2 ^ k → InTab 8 (128 + M (y, Alg.bits k c)) := by
  rw [inTable_rowOK]
  constructor
  · intro h y c hc
    obtain ⟨t, ht, e⟩ := h y.val (lt_of_lt_of_le y.isLt (by decide)) c hc
    rw [(liveE0 y.val y.isLt).1, (liveE0 y.val y.isLt).2, sum_pick y.val y.isLt, one_mul] at e
    exact ⟨t, ht, e⟩
  · intro h v _
    by_cases hv : v < hRef
    · intro c hc
      obtain ⟨t, ht, e⟩ := h ⟨v, hv⟩ c hc
      refine ⟨t, ht, ?_⟩
      rw [(liveE0 v hv).1, (liveE0 v hv).2, sum_pick v hv, one_mul]
      exact e
    · have hi := idle0 v (Nat.le_of_not_lt hv)
      have e1 : keysGl.oE GE 0 v = 0 := by unfold Keys.oE; rw [hi.1, map_zero]
      have e2 : keysGl.coE GE 0 v = fun _ => 0 := by
        funext r
        unfold Keys.coE
        rw [hi.2, map_zero]
      rw [e1, e2]
      exact rowOK_pad k 8 _ M 0 ⟨0, Nat.pos_of_ne_zero (by positivity), Nat.cast_zero.symm⟩

/-- The second forest lies in its table if and only if 4096 plus each two-byte weight is below
2^13. -/
theorem forest1_iff :
    InTable (22 + k) 13 (keyOf k M (keysGl.oE GE 1) (keysGl.coE GE 1))
        (fun u => ((u : ℕ) : GE)) ↔
      ∀ (q : ℕ) (hq : q < 1527800) (c : ℕ), c < 2 ^ k →
        InTab 13 (4096 + M (⟨pairY q 0, (pairY_lt q hq).1⟩, Alg.bits k c) +
          256 * M (⟨pairY q 1, (pairY_lt q hq).2⟩, Alg.bits k c)) := by
  have key : ∀ (q : ℕ) (hq : q < 1527800) (c : ℕ),
      keysGl.oE GE 1 q + ∑ r, keysGl.coE GE 1 q r * M (r, Alg.bits k c) =
        4096 + M (⟨pairY q 0, (pairY_lt q hq).1⟩, Alg.bits k c) +
          256 * M (⟨pairY q 1, (pairY_lt q hq).2⟩, Alg.bits k c) := by
    intro q hq c
    rw [(liveE1 q hq).1, (liveE1 q hq).2]
    show (4096 : GE) + ∑ r : Fin hRef, ((if r.val = pairY q 0 then (1 : GE) else 0) +
      if r.val = pairY q 1 then 256 else 0) * M (r, Alg.bits k c) = _
    have e : ∀ r : Fin hRef, ((if r.val = pairY q 0 then (1 : GE) else 0) +
        if r.val = pairY q 1 then 256 else 0) * M (r, Alg.bits k c) =
        (if r.val = pairY q 0 then (1 : GE) else 0) * M (r, Alg.bits k c) +
          (if r.val = pairY q 1 then (256 : GE) else 0) * M (r, Alg.bits k c) :=
      fun r => add_mul _ _ _
    rw [Finset.sum_congr rfl fun r _ => e r, Finset.sum_add_distrib,
      sum_pick _ (pairY_lt q hq).1 1 fun r => M (r, Alg.bits k c),
      sum_pick _ (pairY_lt q hq).2 256 fun r => M (r, Alg.bits k c), one_mul, add_assoc]
  rw [inTable_rowOK]
  constructor
  · intro h q hq c hc
    obtain ⟨t, ht, e⟩ := h q (lt_of_lt_of_le hq (by decide)) c hc
    exact ⟨t, ht, (key q hq c).symm.trans e⟩
  · intro h v _
    by_cases hv : v < 1527800
    · intro c hc
      obtain ⟨t, ht, e⟩ := h v hv c hc
      exact ⟨t, ht, (key v hv c).trans e⟩
    · have hi := idle1 v (Nat.le_of_not_lt hv)
      have e1 : keysGl.oE GE 1 v = 0 := by unfold Keys.oE; rw [hi.1, map_zero]
      have e2 : keysGl.coE GE 1 v = fun _ => 0 := by
        funext r
        unfold Keys.coE
        rw [hi.2, map_zero]
      rw [e1, e2]
      exact rowOK_pad k 13 _ M 0 ⟨0, Nat.pos_of_ne_zero (by positivity), Nat.cast_zero.symm⟩

end
/-! ### From the cube to the matrix of rows and columns -/

section Mat
variable (M : Fin hRef → Fin (2 ^ kRef) → GE)

/-- The two forests lie in their tables if and only if the matrix is well formed in the sense of
Blocks/RngPlan.lean: every entry a signed byte, every two-byte weight in range. -/
theorem forests_iff_wfPairs :
    (InTable (22 + kRef) 8 (keyOf kRef (cubeOf M) (keysGl.oE GE 0) (keysGl.coE GE 0))
        (fun u => ((u : ℕ) : GE)) ∧
      InTable (22 + kRef) 13 (keyOf kRef (cubeOf M) (keysGl.oE GE 1) (keysGl.coE GE 1))
        (fun u => ((u : ℕ) : GE))) ↔
      WFPairs hRef kRef 1527800 (Layout.Bridge.y0 ppref kRef) (Layout.Bridge.y1 ppref kRef)
        (extE M) := by
  rw [forest0_iff, forest1_iff]
  constructor
  · rintro ⟨h0, h1⟩
    have hb : ∀ y, y < hRef → ∀ c, c < 2 ^ kRef → IsByte (extE M y c) := by
      intro y hy c hc
      have := h0 ⟨y, hy⟩ c hc
      rw [cubeOf_bits M _ c hc] at this
      rw [extE_in M y c hy hc]
      exact (inTab_byte_iff _).1 this
    refine ⟨hb, fun q hq c hc => ?_⟩
    have hl := pairY_lt q hq
    have := h1 q hq c hc
    rw [cubeOf_bits M _ c hc, cubeOf_bits M _ c hc] at this
    refine (inTab_pair_iff Gl.p p_big (hb _ hl.1 c hc) (hb _ hl.2 c hc)).1 ?_
    rw [extE_in M _ c hl.1 hc, extE_in M _ c hl.2 hc]
    exact this
  · rintro ⟨hb, hp⟩
    refine ⟨fun y c hc => ?_, fun q hq c hc => ?_⟩
    · rw [cubeOf_bits M _ c hc]
      have := hb y.val y.isLt c hc
      rw [extE_in M _ c y.isLt hc] at this
      exact (inTab_byte_iff _).2 this
    · have hl := pairY_lt q hq
      rw [cubeOf_bits M _ c hc, cubeOf_bits M _ c hc]
      have := (inTab_pair_iff Gl.p p_big (hb _ hl.1 c hc) (hb _ hl.2 c hc)).2 (hp q hq c hc)
      rw [extE_in M _ c hl.1 hc, extE_in M _ c hl.2 hc] at this
      exact this

/-- **The keys of all 24 parts of the two lookups at full size lie in their tables if and only if
the matrix holds an index.** -/
theorem partsIn_iff_inRange :
    PartsIn lk0Full lk1Full kRef (cubeOf M) ↔ VerifiableInference.OnPublicFiles.Flat.InRange M := by
  rw [full_iff_forests, forests_iff_wfPairs, wfPairs_iff_inRange]

end Mat

/-! ### Two controls: neither side is always true or always false -/

/-! ### The record's laws where "holds an index" is read off the matrix of rows and columns -/

section Any
variable (C : Hiop.ConfigurationWithOutOfDomainSample) (mat : C.Msg → Fin hRef → Fin (2 ^ kRef) → GE)
  (hd : ∀ U, (C.held U).isSome ↔ VerifiableInference.OnPublicFiles.Flat.InRange (mat U))
  (h1 : ∀ i η, C.held (C.hold i η) = some i)
  (h2 : ∀ m r s, C.dcd (C.enc m r) (s, C.smp s m) = some m)

end Any

end Johnson.Pack
