-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoPlaneClaims.lean.
The three claims of the byte-level verifier that read the planes of the counts, by value.

`Forest.planeClaims` (OnBytes/Model/Look.lean) makes three forms from what a lookup has left: the
claim of the leaves' sumcheck, with the planes' value at the leaves' point; the claim that the
planes' value at the bits' point is what the bits' sumcheck has shown; the claim that the counts sum
to the number of keys that are not padding. The caller hands in two families of forms, one for each
column of the planes' matrix.

This file states what a run that returns has done, and what the three forms are worth, for every
reading ρ of the byte-level field in a commutative ring K and in every world W. The values of the
caller's forms stand in the statements as letters.

Main names:
  `Quiet x`: the routine x, if it returns, turns neither the state of the sub-proof nor the context.
  `got x F c`: the form that x returns from F and c.
  `planesAff`, `countAff`: the forms that the routine folds up, as plain folds.
  `planesAt_ok`, `planeClaims_run`, `planeClaims_ok`: if the run returns and the caller's routines
    are quiet, then lm has passed the test, the context is as before, the state is turned by the
    leaves' claim alone
    (the slots of its hiding polynomial are filled), and the three forms are the named ones.
  `planesAff_value`: the planes' form is worth `planesK` at the point read by ρ.
  `countAff_value`: the third claim is worth `countK`, if a key's number has fewer than 64 bits.
  `neg_val`: ρ takes the negative to the negative.

Limits: what the values of the caller's forms are is the caller's to state. Not claimed: anything on
soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPin
import OnBytes.Tie.Pv.Lookup.Port.FoTwins
import OnBytes.Tie.Pv.Lookup.Forest.FoEv

set_option autoImplicit false

namespace Cb.Fo.PlaneClaims
open OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun _root_.Fo

/-! ### the negative under a reading -/

theorem negF_eq_sub (a : UInt64) : negF a = subF 0 a := by
  unfold negF subF
  have h0 : normF 0 = 0 := by decide
  simp only [h0]
  by_cases hy : normF a = 0
  · rw [if_pos hy, hy]
    rfl
  · have hp : (0 : UInt64) < normF a := by
      rw [UInt64.lt_iff_toNat_lt]
      have : (normF a).toNat ≠ 0 := fun e => hy (UInt64.toNat_inj.mp e)
      exact Nat.pos_of_ne_zero this
    rw [if_neg hy, if_pos hp, UInt64.zero_add]

theorem negE_eq_sub (a : E) : negE a = subE zeroE a := by
  show E.mk3 (negF a.c0) (negF a.c1) (negF a.c2) = E.mk3 (subF 0 a.c0) (subF 0 a.c1) (subF 0 a.c2)
  rw [negF_eq_sub, negF_eq_sub, negF_eq_sub]

section
variable {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K)

theorem neg_val (a : E) : ρ.val (negE a) = -ρ.val a := by
  rw [negE_eq_sub, ρ.sub, ρ.zero, zero_sub]

end

/-! ### routines that turn nothing -/

/-- If the routine returns, it turns neither the state of the sub-proof nor the context. -/
def Quiet (x : SubM Aff) : Prop := ∀ F c r, x F c = .ok r → r.1.2 = F ∧ r.2 = c

/-- The form that the routine returns. -/
def got (x : SubM Aff) (F : Fork) (c : Ctx) : Aff :=
  match x F c with
  | .ok r => r.1.1
  | .error _ => {}

theorem quiet_ok {x : SubM Aff} (hx : Quiet x) {F : Fork} {c : Ctx} {r : (Aff × Fork) × Ctx}
    (h : x F c = .ok r) : r = ((got x F c, F), c) := by
  obtain ⟨h1, h2⟩ := hx F c r h
  obtain ⟨⟨a, G⟩, c'⟩ := r
  have e : got x F c = a := by
    unfold got
    rw [h]
  simp only at h1 h2
  rw [e, h1, h2]

/-- A fold over quiet routines is a plain fold. -/
theorem fold_quiet (x : ℕ → SubM Aff) (hx : ∀ col, Quiet (x col)) (step : Aff → ℕ → Aff → Aff) :
    ∀ (l : List ℕ) (s : Aff) (F : Fork) (c : Ctx) (r : (Aff × Fork) × Ctx),
    (l.foldlM (fun f col => x col >>= fun a => pure (step f col a)) s) F c = .ok r →
    r = ((l.foldl (fun f col => step f col (got (x col) F c)) s, F), c)
  | [], s, F, c, r, h => (foldlM_nil_ok _ s F c r).1 h
  | col :: l, s, F, c, r, h => by
    obtain ⟨s₁, F₁, c₁, h1, h2⟩ := (foldlM_cons_ok _ s col l F c r).1 h
    obtain ⟨a, G, c2, h3, h4⟩ := (bind_ok _ _ F c _).1 h1
    have e3 := quiet_ok (hx col) h3
    have e4 := (pure_ok _ G c2 _).1 h4
    simp only [Prod.mk.injEq] at e3 e4
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e3
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e4
    exact fold_quiet x hx step l _ _ _ r h2

/-! ### the forms -/

/-- The form that `Forest.planesAt` folds up from the columns' forms B. -/
def planesAff (g : Heard) (lm e : ℕ) (B : ℕ → Aff) : Aff :=
  (List.range (g.shape.NC * 2 ^ (g.shape.kT + 5 - lm))).foldl
    (fun f col => Aff.addMul f (B col)
      (mulE ((eqTab ((g.zb e).extract g.shape.kT (g.shape.kT + g.shape.cK))).getD
          (col / 2 ^ (g.shape.kT + 5 - lm)) zeroE)
        ((eqTab ((g.zb e).extract 0 (g.shape.kT + 5 - lm))).getD
          (col % 2 ^ (g.shape.kT + 5 - lm)) zeroE)))
    (Aff.ofConst zeroE)

/-- The third claim, folded up from the columns' forms P. -/
def countAff (g : Heard) (lm : ℕ) (P : ℕ → Aff) : Aff :=
  (List.range (g.shape.NC * 2 ^ (g.shape.kT + 5 - lm))).foldl (fun f col => f + P col)
    (Aff.ofConst (negE (ofF (2 ^ g.shape.v - g.shape.padding).toUInt64)))

theorem planesAt_ok (g : Heard) (lm e : ℕ) (bit : ℕ → ℕ → SubM Aff) (hb : ∀ col, Quiet (bit e col))
    (F : Fork) (c : Ctx) (r : (Aff × Fork) × Ctx) (h : planesAt g lm e bit F c = .ok r) :
    r = ((planesAff g lm e fun col => got (bit e col) F c, F), c) :=
  fold_quiet (bit e) hb (fun f col a => Aff.addMul f a
    (mulE ((eqTab ((g.zb e).extract g.shape.kT (g.shape.kT + g.shape.cK))).getD
        (col / 2 ^ (g.shape.kT + 5 - lm)) zeroE)
      ((eqTab ((g.zb e).extract 0 (g.shape.kT + 5 - lm))).getD
        (col % 2 ^ (g.shape.kT + 5 - lm)) zeroE))) _ _ F c r h

/-- A run of `Forest.planeClaims` that returns is a run of the leaves' claim, from the same state
and context, with the planes' form at the leaves' point kept. -/
theorem planeClaims_run (g : Heard) (lm : ℕ) (bit : ℕ → ℕ → SubM Aff) (pin : ℕ → SubM Aff)
    (hb : ∀ e col, Quiet (bit e col)) (hp : ∀ col, Quiet (pin col))
    (F G : Fork) (c c' : Ctx) (rows : Array Aff)
    (h : planeClaims g lm bit pin F c = .ok ((rows, G), c')) :
    (planeCols g.shape lm).toBool = true ∧ ∃ row p',
      pscRow g.leaves oneE (Aff.scale (planesAff g lm 0 fun col => got (bit 0 col) F c) g.leavesA)
        F c = .ok (((row, p'), G), c') ∧
      rows = #[row, Aff.slot g.sBit - planesAff g lm 1 fun col => got (bit 1 col) F c,
        countAff g lm fun col => got (pin col) F c] := by
  unfold planeClaims at h
  obtain ⟨_, F1, c1, h1, k1⟩ := (bind_ok _ _ F c _).1 h
  obtain ⟨hm, e1⟩ := (must_ok _ F c _).1 h1
  simp only [Prod.mk.injEq] at e1
  obtain ⟨⟨_, hF1⟩, hc1⟩ := e1
  rw [hF1, hc1] at k1
  obtain ⟨at0, F2, c2, h2, k2⟩ := (bind_ok _ _ F c _).1 k1
  have e2 := planesAt_ok g lm 0 bit (hb 0) F c _ h2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨⟨ha0, hF2⟩, hc2⟩ := e2
  rw [hF2, hc2] at k2
  obtain ⟨at1, F3, c3, h3, k3⟩ := (bind_ok _ _ F c _).1 k2
  have e3 := planesAt_ok g lm 1 bit (hb 1) F c _ h3
  simp only [Prod.mk.injEq] at e3
  obtain ⟨⟨ha1, hF3⟩, hc3⟩ := e3
  rw [hF3, hc3] at k3
  obtain ⟨cnt, F4, c4, h4, k4⟩ := (bind_ok _ _ F c _).1 k3
  have e4 := fold_quiet pin hp (fun f _ a => f + a) _ _ F c _ h4
  simp only [Prod.mk.injEq] at e4
  obtain ⟨⟨hcn, hF4⟩, hc4⟩ := e4
  rw [hF4, hc4] at k4
  obtain ⟨⟨row, p'⟩, F5, c5, h5, k5⟩ := (bind_ok _ _ F c _).1 k4
  have e6 := (pure_ok _ F5 c5 _).1 k5
  simp only [Prod.mk.injEq] at e6
  obtain ⟨⟨hr, hG⟩, hc'⟩ := e6
  refine ⟨hm, row, p', ?_, ?_⟩
  · rw [hG, hc', ← ha0]
    exact h5
  · rw [hr, ha1, hcn]
    rfl

/-- **What a run of `Forest.planeClaims` that returns has done.** -/
theorem planeClaims_ok (g : Heard) (lm : ℕ) (bit : ℕ → ℕ → SubM Aff) (pin : ℕ → SubM Aff)
    (hb : ∀ e col, Quiet (bit e col)) (hp : ∀ col, Quiet (pin col))
    (F G : Fork) (c c' : Ctx) (rows : Array Aff)
    (h : planeClaims g lm bit pin F c = .ok ((rows, G), c')) :
    (planeCols g.shape lm).toBool = true ∧ c' = c ∧
      g.leaves.rowMade = false ∧ g.leaves.started = true ∧ g.leaves.vars.isEmpty = false ∧
      g.leaves.r.size = g.leaves.vars.size ∧
      F.hideRun g.leaves.first (Array.replicate g.leaves.walk.1.length zeroE) (subE zeroE oneE) =
        some G ∧
      rows = #[g.leaves.rowForm oneE
          (Aff.scale (planesAff g lm 0 fun col => got (bit 0 col) F c) g.leavesA),
        Aff.slot g.sBit - planesAff g lm 1 fun col => got (bit 1 col) F c,
        countAff g lm fun col => got (pin col) F c] := by
  obtain ⟨hm, row, p', h5, hr⟩ := planeClaims_run g lm bit pin hb hp F G c c' rows h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, _⟩ := pscRow_ok _ _ _ _ _ _ _ _ _ h5
  exact ⟨hm, a5, a1, a2, a3, a4, a6, by rw [hr, a7]⟩

/-! ### their values -/
section
variable {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K) (W : World K)

theorem foldl_addMul_value (B : ℕ → Aff) (k : ℕ → E) (κ : ℕ → K)
    (hk : ∀ col, ρ.val (k col) = κ col) : ∀ (l : List ℕ) (s : Aff),
    (l.foldl (fun f col => Aff.addMul f (B col) (k col)) s).value ρ W =
      l.foldl (fun f col => f + (B col).value ρ W * κ col) (s.value ρ W)
  | [], _ => rfl
  | col :: l, s => by
    rw [List.foldl_cons, List.foldl_cons, foldl_addMul_value B k κ hk l, Aff.value_addMul, hk,
      mul_comm]

theorem foldl_add_value (P : ℕ → Aff) : ∀ (l : List ℕ) (s : Aff),
    (l.foldl (fun f col => f + P col) s).value ρ W =
      l.foldl (fun f col => f + (P col).value ρ W) (s.value ρ W)
  | [], _ => rfl
  | col :: l, s => by
    rw [List.foldl_cons, List.foldl_cons, foldl_add_value P l, Aff.value_add]

/-- **The planes' form is worth the plain function at the point read by ρ.** -/
theorem planesAff_value (g : Heard) (lm e : ℕ) (B : ℕ → Aff) :
    (planesAff g lm e B).value ρ W =
      planesK g.shape lm (rdL ρ (g.zb e)) fun col => (B col).value ρ W := by
  unfold planesAff planesK
  rw [foldl_addMul_value ρ W B _ (fun col =>
    (eqTabK (exL (rdL ρ (g.zb e)) g.shape.kT (g.shape.kT + g.shape.cK))).getD
        (col / 2 ^ (g.shape.kT + 5 - lm)) 0 *
      (eqTabK (exL (rdL ρ (g.zb e)) 0 (g.shape.kT + 5 - lm))).getD
        (col % 2 ^ (g.shape.kT + 5 - lm)) 0) (fun col => by
      rw [ρ.mul, rdL_getD, rdL_getD, eqTab_val, eqTab_val, rdL_extract, rdL_extract]),
    Aff.value_ofConst, ρ.zero]

/-- **The third claim is worth the plain function.** -/
theorem countAff_value (g : Heard) (lm : ℕ) (P : ℕ → Aff) (hv : g.shape.v < 64) :
    (countAff g lm P).value ρ W = Pin.countK g.shape lm fun col => (P col).value ρ W := by
  unfold countAff Pin.countK
  have hn : 2 ^ g.shape.v - g.shape.padding < 2 ^ 64 :=
    lt_of_le_of_lt (Nat.sub_le _ _) (Nat.pow_lt_pow_right (by decide) hv)
  rw [foldl_add_value, Aff.value_ofConst, neg_val, ofF_val, toNat_word _ hn]

end
end Cb.Fo.PlaneClaims
