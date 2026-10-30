-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/LookJobs.lean

The five sorts of sumcheck of a lookup argument, as jobs (tieJob, keyJob, tabJob, leavesJob,
bitsJob, Johnson/HonestTrace/LookDefs.lean): their true sums, and that their runs are lawful.

Notation. D : Data P K holds TwV's public numbers N (2^v keys, v = N.v' + 1; 2^d rows; 2^w planes,
of which n + 2 count), a joint key vector, bits and the point of comparison al. "MidP" is D.Mid:
Cb.Lkp.MidP v d w (n + 2) at D's key vector, table, padding, bits and al
(Cb/Pv/Lookup/Alg/PadAlg.lean).

Main theorems:
* "tieJob_lawful": under MidP the job of tie step s is lawful, for s ≤ n. It rests on "Z_eq" (under
  MidP, Z = a (P_1^2 G_0)) and "Pc_step" (for s ≤ n, P_s = P_(s+1)^2 G_s).
* "keyJob_sum", "tabJob_sum": for l < v (l < d) the true sum of the level's job at z is the
  extension of level l of the key side's (the table side's) tree at z. "leavesJob_sum": the true sum
  of the leaves' job at z is the extension of the table side's lowest level at z. "bitsJob_sum":
  under MidP the true sum of the bits' job is 0.
* "leavesJob_lawful", "bitsJob_lawful": at a point of w + d coordinates, if the job's order is a
  permutation of the numbers below w + d, the job is lawful.
That keyJob and tabJob are lawful is pj_lawful (Johnson/HonestTrace/LookCube.lean) as it stands.

Limits. D is arbitrary; the points and the challenges are arbitrary lists of the right length; the
orders are permutations where a theorem says so; MidP is assumed where it is named. The end values'
mask entries are an arbitrary list m. Nothing is said of the polynomial H of the mask entries, of
what is sent, or of a verifier.

Not claimed: that MidP holds of any keys and bits; anything on a prover or a verifier.

-/
import Johnson.HonestTrace.LookCube

set_option autoImplicit false

namespace OnBytes.HonestTrace.Look

open Finset TwV
open Cb.Lkp

section
variable {K : Type} [Field K] {P : Type}

/-! ## The tie -/

/-- For s ≤ n: P_s = P_(s+1)^2 G_s. -/
theorem Pc_step (D : Data P K) {s : ℕ} (hs : s ≤ D.N.n) : D.Pc s = D.Pc (s + 1) ^ 2 * D.G s := by
  have e : D.N.n + 1 - s = (D.N.n + 1 - (s + 1)) + 1 := by omega
  unfold Data.Pc
  rw [e]
  rfl

/-- Under MidP: Z = a (P_1^2 G_0). -/
theorem Z_eq (D : Data P K) (hM : D.Mid) : D.Z = D.a * (D.Pc 1 ^ 2 * D.G 0) := by
  rw [← Pc_step D (Nat.zero_le _)]
  have h := hM.2.2
  unfold Data.Pc
  rw [Alg.Lookup.chainFrom_eq_prod]
  simpa using h

/-- Under MidP every tie step's job is lawful (s ≤ n). -/
theorem tieJob_lawful (D : Data P K) (hM : D.Mid) {s : ℕ} (hs : s ≤ D.N.n) :
    (tieJob D s).Lawful := by
  refine ⟨fun xs hx => ?_, fun _ xs m β _ hm => ?_⟩
  · have e : xs = [] := List.length_eq_zero_iff.1 hx
    subst e
    exact rfl
  · by_cases h0 : s = 0
    · subst h0
      obtain ⟨m0, m1, m2, rfl⟩ : ∃ m0 m1 m2, m = [m0, m1, m2] := by
        match m, hm with
        | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
      have hZ := Z_eq D hM
      refine ⟨?_, ?_⟩
      · show (D.Z + -D.a * (D.Pc 1 ^ 2 * D.G 0)) + 0 * _ = 0
        rw [hZ]
        ring
      · show evalP [D.Z + -D.a * _, m0 + -D.a * _, -D.a * _, -D.a * _] β =
          (shownL β [D.Z, D.Pc 1, D.G 0] [m0, m1, m2]).getD 0 0 - D.a *
            ((shownL β [D.Z, D.Pc 1, D.G 0] [m0, m1, m2]).getD 1 0 ^ 2 *
              (shownL β [D.Z, D.Pc 1, D.G 0] [m0, m1, m2]).getD 2 0)
        simp only [evalP, evalGo, List.headD_cons, List.tail_cons, shownL,
          List.zipWith_cons_cons, List.getD_cons_zero, List.getD_cons_succ]
        ring
    · have hends : (tieJob D s).ends xs = [D.Pc (s + 1), D.G s] := if_neg h0
      rw [hends] at hm
      obtain ⟨m0, m1, rfl⟩ : ∃ m0 m1, m = [m0, m1] := by
        match m, hm with
        | [a, b], _ => exact ⟨a, b, rfl⟩
      have hY : (tieJob D s).inY xs [m0, m1] = sqMul (D.Pc (s + 1)) (D.G s) m0 m1 := if_neg h0
      have hfin : (tieJob D s).fin xs = D.Pc s := if_neg h0
      have hS : ∀ x, (tieJob D s).S0 x = x.getD 0 0 ^ 2 * x.getD 1 0 := fun x => if_neg h0
      rw [hY, hfin, hS, hends, Pc_step D hs]
      refine ⟨?_, ?_⟩
      · show D.Pc (s + 1) ^ 2 * D.G s + 0 * _ = _
        ring
      · simp only [sqMul, evalP, evalGo, List.headD_cons, List.tail_cons, shownL,
          List.zipWith_cons_cons, List.getD_cons_zero, List.getD_cons_succ]
        ring

/-! ## The true sums -/

/-- For l < v the true sum of key level l's job at z is the extension of level l of the key side's
tree at z. -/
theorem keyJob_sum (D : Data P K) {l : ℕ} (hl : l < D.v) (z : List K) :
    (keyJob D l z).sum = ext l (D.kLvl l) z := by
  show ∑ X ∈ range (2 ^ l), eqN z X * (0 + D.kLvl (l + 1) X * D.kLvl (l + 1) (X + 2 ^ l)) = _
  refine sum_congr rfl fun X _ => ?_
  have h := Blocks.lvl_step 0 D.v (facK D.key D.al) hl X
  rw [zero_add]
  exact congrArg _ h.symm

/-- For l < d the true sum of table level l's job at z is the extension, over w + l coordinates, of
level l of the table side's tree at z. -/
theorem tabJob_sum (D : Data P K) {l : ℕ} (hl : l < D.N.d) (z : List K) :
    (tabJob D l z).sum = ext (D.N.w + l) (D.tLvl l) z := by
  show ∑ X ∈ range (2 ^ (D.N.w + l)),
    eqN z X * (0 + D.tLvl (l + 1) X * D.tLvl (l + 1) (X + 2 ^ (D.N.w + l))) = _
  refine sum_congr rfl fun X _ => ?_
  have h := Blocks.lvl_step D.N.w D.N.d (facT D.N.w D.N.tab D.bits D.al) hl X
  rw [Nat.add_comm l D.N.w] at h
  rw [zero_add]
  exact congrArg _ h.symm

/-- The true sum of the leaves' job is the extension of the table side's lowest level. -/
theorem leavesJob_sum (D : Data P K) (z : List K) :
    (leavesJob D z).sum = ext (D.N.w + D.N.d) (D.tLvl D.N.d) z := by
  show ∑ X ∈ range (2 ^ (D.N.w + D.N.d)), eqN z X * (1 + D.bitAt X * D.rowAt X) = _
  refine sum_congr rfl fun X _ => ?_
  unfold Data.tLvl
  rw [Blocks.lvl_top]
  rfl

/-- Under MidP the true sum of the bits' job is 0. -/
theorem bitsJob_sum (D : Data P K) (hM : D.Mid) (z : List K) : (bitsJob D z).sum = 0 := by
  show ∑ X ∈ range (2 ^ (D.N.w + D.N.d)), eqN z X * (0 + D.bitAt X * (D.bitAt X - 1)) = 0
  refine sum_eq_zero fun X hX => ?_
  have hX' := mem_range.1 hX
  have hu : X / 2 ^ D.N.w < 2 ^ D.N.d := by
    apply Nat.div_lt_of_lt_mul
    rw [← pow_add]
    exact hX'
  have hb := hM.1 _ hu (X % 2 ^ D.N.w) (Nat.mod_lt _ (by positivity))
  have hb' : D.bitAt X * (D.bitAt X - 1) = 0 := hb
  rw [hb']
  ring

/-! ## The leaves' and the bits' jobs are lawful -/

/-- Two polynomials with the same sum under every pair of weights (1 - z, z) and the same values. -/
def Same (q q' : List K) : Prop :=
  (∀ z, wsum z q = wsum z q') ∧ ∀ x, evalP q x = evalP q' x

/-- A run stays a run if each polynomial gives way to one that is Same. -/
theorem Chained.congr : ∀ (σ : K) (zs : List K) (qs qs' : List (List K)) (xs : List K) (fin : K),
    List.Forall₂ Same qs qs' → Chained σ zs qs xs fin → Chained σ zs qs' xs fin
  | _, [], _, _, [], _, .nil, h => h
  | _, z :: zs, _, _, x :: xs, fin, .cons (a := q) (b := q') (l₁ := qs) (l₂ := qs') hq hr, h => by
    obtain ⟨h1, h2⟩ := h
    refine ⟨(hq.1 z).symm.trans h1, ?_⟩
    rw [← hq.2 x]
    exact Chained.congr _ zs qs qs' xs fin hr h2
  | _, [], _, _, _ :: _, _, .nil, h => h.elim
  | _, _ :: _, _, _, _, _, .nil, h => h.elim
  | _, [], _, _, _, _, .cons _ _, h => h.elim
  | _, _ :: _, _, _, [], _, .cons _ _, h => h.elim

/-- Putting a bit below w does not move X / 2^w. -/
theorem setBit_div : ∀ (w c : ℕ), c < w → ∀ (b : Bool) (X : ℕ),
    setBit c b X / 2 ^ w = X / 2 ^ w
  | 0, _, h, _, _ => by omega
  | w + 1, 0, _, b, X => by
    show (2 * (X / 2) + b.toNat) / 2 ^ (w + 1) = _
    have hb : b.toNat < 2 := by cases b <;> decide
    rw [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
    congr 1
    omega
  | w + 1, c + 1, h, b, X => by
    show (2 * setBit c b (X / 2) + X % 2) / 2 ^ (w + 1) = _
    rw [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
      ← setBit_div w c (by omega) b (X / 2)]
    congr 1
    omega

/-- leavesJob is lawful at a point of w + d coordinates, if the order lists the coordinates below
w + d, each once. -/
theorem leavesJob_lawful (D : Data P K) (z : List K) (hz : z.length = D.N.w + D.N.d)
    (ho : D.N.oE.Perm (List.range (D.N.w + D.N.d))) : (leavesJob D z).Lawful := by
  have hp := pj_lawful (D.N.w + D.N.d) 1 D.bitAt D.rowAt D.N.oE z ho hz
  have hlen : (inRounds D.N.oE z).length = D.N.w + D.N.d := by
    unfold inRounds
    rw [List.length_map, ho.length_eq, List.length_range]
  refine ⟨fun xs hx => ?_, fun h => Bool.noConfusion (show false = true from h)⟩
  refine Chained.congr _ _ _ _ _ _ ?_ (hp.1 xs hx)
  unfold Job.gs
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine List.forall₂_same.2 fun l hl => ?_
  have hl' : l < D.N.w + D.N.d := by
    have := List.mem_range.1 hl
    rwa [show (pj (D.N.w + D.N.d) 1 D.bitAt D.rowAt D.N.oE z).zs.length = D.N.w + D.N.d from
      hlen] at this
  have hxl : xs.length = D.N.w + D.N.d := hx.trans hlen
  have htl : (xs.take l).length = l := by rw [List.length_take, Nat.min_eq_left (by omega)]
  show Same (pjRound _ 1 D.bitAt D.rowAt D.N.oE z (xs.take l))
    ((pjRound _ 1 D.bitAt D.rowAt D.N.oE z (xs.take l)).take
      (if D.N.oE.getD (xs.take l).length 0 < D.N.w then 2 else 3))
  by_cases hc : D.N.oE.getD (xs.take l).length 0 < D.N.w
  · rw [if_pos hc]
    have h0 := pjRound_deg1 _ 1 D.bitAt D.rowAt D.N.oE z (xs.take l) ho (by rw [htl]; exact hl')
      fun b X => by
        unfold Data.rowAt
        rw [setBit_div _ _ hc]
    obtain ⟨q0, q1, q2, e⟩ : ∃ q0 q1 q2,
        pjRound (D.N.w + D.N.d) 1 D.bitAt D.rowAt D.N.oE z (xs.take l) = [q0, q1, q2] :=
      ⟨_, _, _, rfl⟩
    rw [e] at h0 ⊢
    have h2 : q2 = 0 := h0
    subst h2
    refine ⟨fun z => ?_, fun x => ?_⟩
    · simp [wsum]
    · simp [evalP, evalGo]
  · rw [if_neg hc]
    exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- For pt of m coordinates: the extension of f - 1 at pt is the extension of f at pt, less 1. -/
theorem ext_sub_one (m : ℕ) (f : ℕ → K) (pt : List K) (hp : pt.length = m) :
    ext m (fun X => f X - 1) pt = ext m f pt - 1 := by
  have h1 := _root_.Fo.eqN_total pt
  rw [hp] at h1
  unfold ext
  rw [sum_congr rfl fun X _ => show eqN pt X * (f X - 1) = eqN pt X * f X - eqN pt X by ring,
    sum_sub_distrib, h1]

/-- bitsJob is lawful at a point of w + d coordinates, if the order lists the coordinates below
w + d, each once. -/
theorem bitsJob_lawful (D : Data P K) (z : List K) (hz : z.length = D.N.w + D.N.d)
    (ho : D.N.oB.Perm (List.range (D.N.w + D.N.d))) : (bitsJob D z).Lawful := by
  have hp := pj_lawful (D.N.w + D.N.d) 0 D.bitAt (fun X => D.bitAt X - 1) D.N.oB z ho hz
  refine ⟨hp.1, fun _ xs m β _ hm => ?_⟩
  obtain ⟨m0, rfl⟩ : ∃ m0, m = [m0] := by
    match m, hm with
    | [a], _ => exact ⟨a, rfl⟩
  have hb : (byVar D.N.oB xs).length = D.N.w + D.N.d := by
    unfold byVar
    rw [List.length_map, List.length_range, ho.length_eq, List.length_range]
  refine ⟨?_, ?_⟩
  · show _ * (_ - 1) + 0 * _ = 0 + ext _ D.bitAt _ * ext _ (fun X => D.bitAt X - 1) _
    rw [ext_sub_one _ _ _ hb]
    ring
  · show evalP [_, _, _] β = (shownL β [_] [m0]).getD 0 0 * ((shownL β [_] [m0]).getD 0 0 - 1)
    simp only [evalP, evalGo, List.headD_cons, List.tail_cons, shownL, List.zipWith_cons_cons,
      List.getD_cons_zero]
    ring

end

end OnBytes.HonestTrace.Look

#print axioms OnBytes.HonestTrace.Look.Pc_step
#print axioms OnBytes.HonestTrace.Look.Z_eq
#print axioms OnBytes.HonestTrace.Look.tieJob_lawful
#print axioms OnBytes.HonestTrace.Look.keyJob_sum
#print axioms OnBytes.HonestTrace.Look.tabJob_sum
#print axioms OnBytes.HonestTrace.Look.leavesJob_sum
#print axioms OnBytes.HonestTrace.Look.bitsJob_sum
#print axioms OnBytes.HonestTrace.Look.Chained.congr
#print axioms OnBytes.HonestTrace.Look.setBit_div
#print axioms OnBytes.HonestTrace.Look.leavesJob_lawful
#print axioms OnBytes.HonestTrace.Look.ext_sub_one
#print axioms OnBytes.HonestTrace.Look.bitsJob_lawful
