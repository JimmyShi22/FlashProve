-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoJoinRun.lean.
The byte-level verifier's routine Forest.join, run: what it returns.

Forest.join (OnBytes/Model/Look.lean) makes, from the record of a lookup's end values and the
caller's forms of the calls' key vectors, the one form that must be 0. This file says what a run of
it returns, and that the value of that form, under every reading of the byte-level field in a
commutative ring and in every world, is the value of the plain form Fo.joinK at the record's fields
read by the same reading.

Defines:
  joinForm g KF: the form that Forest.join returns, as a function (the routine's own text).
States:
  join_ok: if a run of Forest.join returns, the two arrays have as many entries as the shape has
    calls, the context is as it was, the state has the join's owed claim marked as added and is
    otherwise as it was, and the form returned is joinForm g KF.
  joinForm_value: the value of joinForm g KF, as two sums and the hidden value at the key side's
    end.
  join_val: it is the value of Fo.joinK's form, for any plain forms that have the values of the
    caller's forms and of the hidden value at the key side's end.
Premises: KF has NC entries; NC ≤ 2^64 (a call's number is turned into a word).
Not claimed: that a run returns.

-/
import OnBytes.Tie.Pv.Lookup.Port.FoTwins
import OnBytes.Tie.Pv.Lookup.Forest.FoEv

set_option autoImplicit false

namespace Fo
open TwV FoNums Finset OnBytes OnBytes.Model OnBytes.PscRun

/-- The form that Forest.join returns. -/
def joinForm (g : Forest.Heard) (KF : Array Aff) : Aff :=
  (List.range KF.size).foldl
      (fun (f : Aff) c =>
        Aff.addMul f
          (Aff.ofConst (subE g.alpha (scaleE c.toUInt64 g.theta)) -
            KF.getD c (Aff.ofConst zeroE))
          (g.e.getD c zeroE))
      (Aff.ofConst zeroE) +
    Aff.ofConst ((List.range (2 ^ g.shape.rK - g.shape.NT)).foldl
      (fun s i => addE s (mulE ((eqTab g.zy).getD (g.shape.NT + i) zeroE)
        (subE g.alpha (g.padKey 0)))) zeroE) -
    g.cEnd

/-- What a run of Forest.join returns. -/
theorem join_ok (g : Forest.Heard) (KF : Array Aff) (F G : Fork) (c c' : Ctx) (r : Aff)
    (h : Forest.join g KF F c = .ok ((r, G), c')) :
    KF.size = g.shape.calls.size ∧ g.e.size = g.shape.calls.size ∧ c' = c ∧
      G = F.paid g.owedJoin ∧ r = joinForm g KF := by
  unfold Forest.join at h
  rw [bind_ok] at h
  obtain ⟨_, F1, c1, h1, h⟩ := h
  obtain ⟨hb, e1⟩ := (mustAs_ok _ _ F c _).1 h1
  have a1 : F1 = F := congrArg (fun x : (Unit × Fork) × Ctx => x.1.2) e1
  have a2 : c1 = c := congrArg (fun x : (Unit × Fork) × Ctx => x.2) e1
  rw [a1, a2, bind_ok] at h
  obtain ⟨_, F2, c2, h2, h⟩ := h
  unfold Forest.joinAdded SubM.paid at h2
  obtain ⟨G2, hG, e2⟩ := (change_ok _ F c _).1 h2
  have b0 : F.paid g.owedJoin = G2 := Option.some.inj hG
  have b1 : F2 = G2 := congrArg (fun x : (Unit × Fork) × Ctx => x.1.2) e2
  have b2 : c2 = c := congrArg (fun x : (Unit × Fork) × Ctx => x.2) e2
  rw [b1, ← b0, b2] at h
  have e3 := (pure_ok _ _ _ _).1 h
  have d1 : r = _ := congrArg (fun x : (Aff × Fork) × Ctx => x.1.1) e3
  have d2 : G = _ := congrArg (fun x : (Aff × Fork) × Ctx => x.1.2) e3
  have d3 : c' = _ := congrArg (fun x : (Aff × Fork) × Ctx => x.2) e3
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  exact ⟨hb.1, hb.2, d3, d2, d1⟩

section
variable {K : Type} [CommRing K] (ρ : Reading K) (W : World K)

theorem foldl_addMul_value (A : ℕ → Aff) (e : ℕ → E) : ∀ (l : List ℕ) (f : Aff),
    (l.foldl (fun (f : Aff) c => Aff.addMul f (A c) (e c)) f).value ρ W =
      f.value ρ W + (l.map fun c => ρ.val (e c) * (A c).value ρ W).sum
  | [], f => by simp
  | c :: l, f => by
    rw [List.foldl_cons, foldl_addMul_value A e l, Aff.value_addMul, List.map_cons, List.sum_cons]
    ring

/-- The value of the form that Forest.join returns. -/
theorem joinForm_value (g : Forest.Heard) (KF : Array Aff) (hN : KF.size ≤ 2 ^ 64) :
    (joinForm g KF).value ρ W =
      ∑ c ∈ range KF.size, ρ.val (g.e.getD c zeroE) *
          (ρ.val g.alpha - (c : K) * ρ.val g.theta -
            (KF.getD c (Aff.ofConst zeroE)).value ρ W) +
        ∑ i ∈ range (2 ^ g.shape.rK - g.shape.NT),
          (eqTabK (rdL ρ g.zy)).getD (g.shape.NT + i) 0 *
            (ρ.val g.alpha - padKeyK g.shape (ρ.val g.theta) 0) -
        g.cEnd.value ρ W := by
  unfold joinForm
  rw [Aff.value_sub, Aff.value_add, Aff.value_ofConst, foldl_addMul_value, Aff.value_ofConst,
    ρ.zero, zero_add, lsum]
  congr 2
  · refine sum_congr rfl fun c hc => ?_
    have hc' : c < 2 ^ 64 := lt_of_lt_of_le (mem_range.mp hc) hN
    rw [Aff.value_sub, Aff.value_ofConst, ρ.sub, nat_scale ρ c hc']
  · rw [foldl_add_val ρ _ (fun i => (eqTabK (rdL ρ g.zy)).getD (g.shape.NT + i) 0 *
      (ρ.val g.alpha - padKeyK g.shape (ρ.val g.theta) 0)) _ _ (fun i _ => by
        rw [ρ.mul, ρ.sub, rdL_getD, eqTab_val]
        show _ * (_ - ρ.val (Forest.padKeyOf g.shape g.theta 0)) = _
        rw [padKey_val ρ g.shape g.theta 0 (by norm_num)]), ρ.zero, foldl_add, zero_add, lsum]

/-- **The byte-level form of the join has the value of the plain form.** -/
theorem join_val {P : Type} (g : Forest.Heard) (KF : Array Aff) (hs : KF.size = g.shape.NC)
    (hN : g.shape.NC ≤ 2 ^ 64) (KFk : ℕ → AffK P K) (cE : AffK P K) (μ : P → K)
    (hK : ∀ c < g.shape.NC, (KF.getD c (Aff.ofConst zeroE)).value ρ W = AffK.val (KFk c) μ)
    (hE : g.cEnd.value ρ W = AffK.val cE μ) :
    (joinForm g KF).value ρ W =
      AffK.val (joinK g.shape (ρ.val g.theta) (ρ.val g.alpha) (fun c => ρ.val (g.e.getD c zeroE))
        (rdL ρ g.zy) KFk cE) μ := by
  rw [joinForm_value ρ W g KF (hs ▸ hN), val_joinK, hs, hE]
  congr 2
  exact sum_congr rfl fun c hc => by rw [hK c (mem_range.mp hc)]

end
end Fo
