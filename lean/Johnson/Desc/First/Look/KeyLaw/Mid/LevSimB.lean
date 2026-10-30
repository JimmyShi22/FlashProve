-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Mid/LevSimB.lean: one level of a product tree: what the sumcheck over
the field hands on (`PscF.outOf` at the product of two shown values, under equality weights in an
order σ), followed by the join on a line, read by `rdMF`, is `Lev.stepSum` followed by
`Lev.stepLine`. `PscF` is our text of the program's sumcheck, over the field. That the program's
run, read in the field, is `PscF` is not shown here.

Main names:
  `clOf σ c` the sumcheck's claim from a claim c at a point: round j weighs at coordinate σ j.
  `hdOf`, `heardF_cons`, `heard_take` what is heard, from the first round and the others; it reads
    the first k + 3 rounds alone.
  `out_point`, `out_masks`, `out_maps`, `out_target`, `out_ends` the output's fields.
  `RelC sl c a` a claim of the course and what is read off a level's state go together.
  `sum_sim`, `line_sim` the two halves of a level.
  `fits_sent`, `fits_sum` what «the rounds fit» gives.
Limits: the rounds fit; 2 k + 5 fresh entries; the claim's point has k coordinates.

-/
import Johnson.Desc.First.Look.KeyLaw.Mid.LevSimA
import Johnson.Desc.First.Look.KeyLaw.Mid.Seams

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.Mid
open Lk6.PortSim
open OnBytes OnBytes.Slice Flat Lev

/-! ### lists -/

theorem chals_eq (k : ℕ) (G : List (RV GE)) (h : k + 1 ≤ G.length) :
    ((G.take (k + 1)).map pr).map (·.2) = (List.range (k + 1)).map (chC G) := by
  refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
  have hi : i < k + 1 := by simpa using h2
  have hG : i < G.length := by omega
  rw [List.getElem_map, List.getElem_map, List.getElem_take, List.getElem_map, List.getElem_range]
  show (G[i]).2.headD 0 = ((G.getD i ([], [])).2).headD 0
  rw [List.getD_eq_getElem _ _ hG]

theorem wts_len : ∀ (k : ℕ) (g : List (RV GE)), (wts k g).length = 2 * k + 3
  | 0, g => PscF.powers_length _ _ 3
  | k + 1, g => by
    show (PscF.powers (chC g 0) (chC g 0) 2 ++ wts k g.tail).length = _
    rw [List.length_append, PscF.powers_length, wts_len k g.tail]
    omega

theorem drop_two {α : Type} (d : α) : ∀ (n : ℕ) (l : List α), l.length = n + 2 →
    l.drop n = [l.getD n d, l.getD (n + 1) d]
  | 0, [_, _], _ => rfl
  | n + 1, _ :: l, h => drop_two d n l (by simpa using h)

theorem headD_getD {α : Type} (l : List α) (d : α) : l.headD d = l.getD 0 d := by
  cases l <;> rfl

theorem getD_take {α : Type} (d : α) (l : List α) (n i : ℕ) (h : i < n) :
    (l.take n).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, h]

/-! ### what is heard -/

/-- what a sumcheck on k variables that shows values hears, from the first round and the others -/
def hdOf (k : ℕ) (v0 : RV GE) (G : List (RV GE)) : PscF.Heard :=
  ⟨v0.1.headD 0, v0.2.headD 0, (G.take (k + 1)).map pr, (G.getD (k + 1) ([], [])).1⟩

theorem heardF_cons (k : ℕ) (v0 : RV GE) (G : List (RV GE)) :
    heardF k true (v0 :: G) = hdOf k v0 G := rfl

theorem heard_take (k : ℕ) (f : List (RV GE)) : heardF k true f = heardF k true (f.take (k + 3)) :=
    by
  cases f with
  | nil => rfl
  | cons v0 G =>
    show hdOf k v0 G = hdOf k v0 (G.take (k + 2))
    unfold hdOf
    rw [List.take_take, getD_take _ G (k + 2) (k + 1) (Nat.lt_succ_self _)]
    have e : min (k + 1) (k + 2) = k + 1 := by omega
    rw [e]

/-! ### the output, field by field -/

/-- the sumcheck's claim: round j weighs at coordinate σ j of the claim's point -/
def clOf {k : ℕ} (σ : Equiv.Perm (Fin k)) (c : PscF.PointClaim) : PscF.Claim :=
  ⟨(List.ofFn fun j => (σ j).val).map fun t => PscF.Weight.equality (c.point.getD t 0) 3, c.masks,
    c.value⟩

section
variable {k : ℕ} (σ : Equiv.Perm (Fin k)) (c : PscF.PointClaim) (fresh : List Slot) (v0 : RV GE)
  (G : List (RV GE))

theorem clOf_len : (clOf σ c).vars.length = k := by
  show ((List.ofFn fun j => (σ j).val).map _).length = k
  rw [List.length_map, List.length_ofFn]

theorem vars_clOf : PscF.varsOf (clOf σ c) sProd = wsOf fun j => c.point.getD (σ j).val 0 := by
  show (List.ofFn fun j => (σ j).val).map (fun t => PscF.Weight.equality (c.point.getD t 0) 3) ++
    [PscF.Weight.atZero 3] = _
  unfold wsOf
  rw [List.map_ofFn, List.map_ofFn]
  rfl

theorem out_point (hG : k + 1 ≤ G.length) :
    (PscF.outOf (clOf σ c) sProd fresh (hdOf k v0 G)).point = (List.range k).map (chC G) := by
  show (((G.take (k + 1)).map pr).map (·.2)).take (clOf σ c).vars.length = _
  rw [chals_eq k G hG, clOf_len, ← List.map_take, List.take_range]
  have e : min k (k + 1) = k := by omega
  rw [e]

theorem out_masks (hG : k + 1 ≤ G.length) :
    (PscF.outOf (clOf σ c) sProd fresh (hdOf k v0 G)).rowMasks =
      fresh.zip (wts k G) ++ PscF.scaleForm (v0.2.headD 0 * 1) c.masks := by
  show fresh.zip (PscF.hidingWalk ((PscF.varsOf (clOf σ c) sProd).zip
      (((G.take (k + 1)).map pr).map (·.2)))).1 ++
    PscF.scaleForm (v0.2.headD 0 * (PscF.hidingWalk ((PscF.varsOf (clOf σ c) sProd).zip
      (((G.take (k + 1)).map pr).map (·.2)))).2) c.masks = _
  rw [vars_clOf, walk_eq k _ G hG]

theorem out_maps : (PscF.outOf (clOf σ c) sProd fresh (hdOf k v0 G)).rowMaps = [] := rfl

theorem out_target (hG : k + 1 ≤ G.length) (h2 : ∀ j ≤ k, (G.getD j ([], [])).1.length = 2) :
    (PscF.outOf (clOf σ c) sProd fresh (hdOf k v0 G)).rowTarget =
      finC k (fun j => c.point.getD (σ j).val 0) (v0.1.headD 0 + v0.2.headD 0 * c.value) G -
        v0.2.headD 0 * (snt G (k + 1) 0 * snt G (k + 1) 1) := by
  show PscF.claimAfter (PscF.varsOf (clOf σ c) sProd) ((G.take (k + 1)).map pr)
      (v0.1.headD 0 + v0.2.headD 0 * c.value) -
    v0.2.headD 0 * ((G.getD (k + 1) ([], [])).1.getD 0 0 * (G.getD (k + 1) ([], [])).1.getD 1 0) = _
  rw [vars_clOf, claim_fin k _ _ G h2 hG]
  rfl

theorem out_ends (hG : k + 1 ≤ G.length) (hfr : fresh.length = 2 * k + 5)
    (hv : (G.getD (k + 1) ([], [])).1.length = 2) :
    (PscF.outOf (clOf σ c) sProd fresh (hdOf k v0 G)).ends =
      [⟨(List.range k).map (chC G), [(fresh.getD (2 * k + 3) ⟨0, 0⟩, chC G k)], snt G (k + 1) 0⟩,
        ⟨(List.range k).map (chC G), [(fresh.getD (2 * k + 4) ⟨0, 0⟩, chC G k)],
          snt G (k + 1) 1⟩] := by
  have hp := out_point σ c fresh v0 G hG
  have hb : (((G.take (k + 1)).map pr).map (·.2)).getLast? = some (chC G k) := by
    rw [chals_eq k G hG, List.range_succ, List.map_append]
    simp
  show ((fresh.drop (PscF.hidingWalk ((PscF.varsOf (clOf σ c) sProd).zip
      (((G.take (k + 1)).map pr).map (·.2)))).1.length).zip (G.getD (k + 1) ([], [])).1).map
    (fun p => (⟨(PscF.outOf (clOf σ c) sProd fresh (hdOf k v0 G)).point,
      [(p.1, ((((G.take (k + 1)).map pr).map (·.2)).getLast?).getD 0)], p.2⟩ : PscF.PointClaim)) = _
  rw [vars_clOf, walk_eq k _ G hG, hp, hb]
  show ((fresh.drop (wts k G).length).zip (G.getD (k + 1) ([], [])).1).map _ = _
  rw [wts_len, drop_two (⟨0, 0⟩ : Slot) (2 * k + 3) fresh (by omega), two_of_len _ hv]
  rfl

end

/-! ### a level -/

variable {J : Type} [DecidableEq J] (sl : Slot → J)

/-- A claim of the course and what is read off a level's state go together. -/
structure RelC (c : PscF.PointClaim) (a : Acc GE J) : Prop where
  pt : a.pt = c.point
  mf : a.mf = rdMF sl c.masks
  tg : a.tg = c.value

/-- The sumcheck of a level. F: its k + 3 rounds. -/
theorem sum_sim {k : ℕ} (σ : Equiv.Perm (Fin k)) (c : PscF.PointClaim) (a : Acc GE J)
    (h : RelC sl c a) (fresh : List Slot) (hfr : fresh.length = 2 * k + 5) (v0 : RV GE)
    (G : List (RV GE)) (hG : k + 1 ≤ G.length) (h2 : ∀ j ≤ k, (G.getD j ([], [])).1.length = 2) :
    stepSum k σ (wvF sl k fresh) (wcF sl k fresh) a (v0 :: G) =
      { pt := byVarF (PscF.outOf (clOf σ c) sProd fresh (hdOf k v0 G)).point
          (List.ofFn fun j => (σ j).val)
        be := chC G k
        v0 := snt G (k + 1) 0
        v1 := snt G (k + 1) 1
        rows := a.rows ++ [⟨rdMF sl (PscF.outOf (clOf σ c) sProd fresh (hdOf k v0 G)).rowMasks,
          (PscF.outOf (clOf σ c) sProd fresh (hdOf k v0 G)).rowTarget⟩] } := by
  have hlen : ((List.range k).map (chC G)).length = k := by
    rw [List.length_map, List.length_range]
  have e1 : byVarF ((List.range k).map (chC G)) (List.ofFn fun j => (σ j).val) =
      List.ofFn fun t : Fin k => chC (v0 :: G) ((σ.symm t).val + 1) := by
    rw [byVar_ofFn k σ _ hlen]
    refine congrArg List.ofFn (funext fun t => ?_)
    have ht : (σ.symm t).val < ((List.range k).map (chC G)).length := by
      rw [hlen]
      exact (σ.symm t).2
    rw [List.getD_eq_getElem _ _ ht, List.getElem_map, List.getElem_range]
    rfl
  have e2 : rdMF sl (fresh.zip (wts k G) ++ PscF.scaleForm (v0.2.headD 0 * 1) c.masks) =
      fun i => rowF k (wvF sl k fresh) (wcF sl k fresh) (fun j => chC (v0 :: G) (j + 1)) i +
        chC (v0 :: G) 0 * a.mf i := by
    funext i
    rw [rdMF_append, rdMF_scale, rd_wts sl k G fresh i (by omega), h.mf, mul_one]
    rfl
  rw [out_point σ c fresh v0 G hG, out_masks σ c fresh v0 G hG, out_target σ c fresh v0 G hG h2,
    e1, e2]
  show (⟨_, _, _, _, _⟩ : AccO GE J) = ⟨_, _, _, _, _⟩
  congr 1
  refine congrArg (fun r => a.rows ++ [r]) (congrArg (Cb.LdLkp.Row.mk _) ?_)
  show finC k (fun j => a.pt.getD (σ j).val 0) (v0.1.getD 0 0 + v0.2.headD 0 * a.tg) G - _ = _
  rw [h.pt, h.tg, headD_getD v0.1 0]
  rfl

/-- The join on a line behind it. -/
theorem line_sim (p : List GE) (s3 s4 : Slot) (be w0 w1 rho : GE)
    (rows : List (Cb.LdLkp.Row GE J))
    (f : List (RV GE)) (hr : chC f 0 = rho) :
    RelC sl (lineF rho ⟨p, [(s3, be)], w0⟩ ⟨p, [(s4, be)], w1⟩)
      (stepLine (sl s3) (sl s4) ⟨p, be, w0, w1, rows⟩ f) where
  pt := by
    show p ++ [chC f 0] = p ++ [rho]
    rw [hr]
  mf := by
    funext i
    rw [rdMF_lineF]
    show be * (Lev.one (sl s3) (1 - chC f 0) i + Lev.one (sl s4) (chC f 0) i) =
      (1 - rho) * rdMF sl [(s3, be)] i + rho * rdMF sl [(s4, be)] i
    rw [rdMF_cons, rdMF_cons, rdMF_nil, hr, one_eq, one_eq]
    unfold Lev.one
    split_ifs <;> ring
  tg := by
    show (1 - chC f 0) * w0 + chC f 0 * w1 = (1 - rho) * w0 + rho * w1
    rw [hr]

/-! ### what «the rounds fit» gives -/

theorem fits_sent (n : ℕ) : ∀ (fm : List Fm) (g : List (RV GE)), (∀ x ∈ fm, x.sent = n) →
    fitsAll fm g = true → ∀ j < fm.length, (g.getD j ([], [])).1.length = n
  | [], _, _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | _ :: _, [], _, h, _, _ => absurd h (by simp [fitsAll])
  | x :: fm, v :: g, ha, h, j, hj => by
    have h' : x.fits v = true ∧ fitsAll fm g = true := by simpa [fitsAll] using h
    cases j with
    | zero =>
      show v.1.length = n
      rw [((Fm.fits_iff x v).1 h'.1).1, ha x List.mem_cons_self]
    | succ j =>
      exact fits_sent n fm g (fun y hy => ha y (List.mem_cons_of_mem _ hy)) h'.2 j
        (Nat.lt_of_succ_lt_succ hj)

theorem fmSum_len (k : ℕ) : (fmSum k).length = k + 3 := by
  simp [fmSum]

/-- the formats behind the first round -/
def fmVars (k : ℕ) : List Fm := List.replicate k ⟨2, 1, false⟩ ++ [⟨2, 1, true⟩, ⟨2, 0, false⟩]

theorem fmVars_len (k : ℕ) : (fmVars k).length = k + 2 := by
  simp [fmVars]

theorem fmVars_sent (k : ℕ) : ∀ x ∈ fmVars k, x.sent = 2 := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · rw [List.eq_of_mem_replicate hx]
  · rcases List.mem_cons.1 hx with rfl | hx
    · rfl
    · rw [List.mem_singleton.1 hx]

/-- k + 3 rounds that fit a level's sumcheck. -/
theorem fits_sum (k : ℕ) (F : List (RV GE)) (h : fitsAll (fmSum k) F = true) :
    ∃ v0 G, F = v0 :: G ∧ G.length = k + 2 ∧ ∀ j ≤ k + 1, (G.getD j ([], [])).1.length = 2 := by
  cases F with
  | nil => exact absurd h (by simp [fmSum, fitsAll])
  | cons v0 G =>
    have h0 : (Fm.mk 1 1 false).fits v0 = true ∧ fitsAll (fmVars k) G = true := by
      simpa [fmSum, fmVars, fitsAll] using h
    refine ⟨v0, G, rfl, (fitsAll_len _ _ h0.2).trans (fmVars_len k), fun j hj => ?_⟩
    exact fits_sent 2 _ G (fmVars_sent k) h0.2 j (by rw [fmVars_len]; omega)

end Lk6.Mid

#print axioms Lk6.Mid.out_ends
#print axioms Lk6.Mid.sum_sim
#print axioms Lk6.Mid.line_sim
#print axioms Lk6.Mid.fits_sum
