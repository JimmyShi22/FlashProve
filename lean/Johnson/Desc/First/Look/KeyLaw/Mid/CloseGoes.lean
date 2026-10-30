-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Mid/CloseGoes.lean: the course over the field goes with the plain
functions of the described lookup at the join point and at the zero point.

The course over the field is our text of the program's lookup, over the field
(Johnson/Desc/First/Look/KeyLaw/Mid/Course.lean). That the program's run, read in the field, is this
course is shown in files that are not in this library yet.

It imports Johnson/Desc/First/Look/KeyLaw/Mid/Relation.lean (`Sim`: how a stand of the course is
read as a state; `Goes` is that of Johnson/Desc/First/Look/KeyLaw/Mid/Seams.lean; `cJoin`, `cZero`
those of Johnson/Desc/First/Look/KeyLaw/Mid/Course.lean) and CloseRun.lean (`joinRun`, `zeroRun`).
Main names:
  `eqW_numLE` the equality weight over the field at the number of a corner is the library's
    `Alg.eqk`.
  `pairsAt_eq` a vector of product form made of a point's pairs (1 − a, a) has that weight as its
    entry number n.
  `sum_range_list` a sum over a range, as a list's sum.
  `zero_goes` `Goes` from seam 6 to seam 7, for `cZero` and `zeroRun`.
  `join_goes` `Goes` from seam 2 to seam 3, for `cJoin` and `joinRun`.
Both under one condition: the course's public record is that of the data (D.S = A.toPub).
Limits: nothing on the program's blocks on machine words.

-/
import Johnson.Desc.First.Look.KeyLaw.Mid.Relation
import Cb.Pv.KeyLookup.CloseRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.Mid.Clo
open Lk6.PortSim Lk6.Clo

open OnBytes OnBytes.Slice Flat Cb Cb.LdLkp Finset Lk6.PortSim

/-! ### the equality weight -/

theorem eqW_mul : ∀ (xs : List GE) (j : ℕ) (r : GE), eqW xs j r = r * eqW xs j 1
  | [], _, r => (mul_one r).symm
  | x :: xs, j, r => by
    show eqW xs (j / 2) (r * _) = r * eqW xs (j / 2) (1 * _)
    rw [eqW_mul xs (j / 2) (r * _), eqW_mul xs (j / 2) (1 * _)]
    ring

theorem numLE_succ {k : ℕ} (θ : Fin (k + 1) → Bool) :
    numLE θ = (if θ 0 then 1 else 0) + 2 * numLE fun i : Fin k => θ i.succ := by
  unfold numLE
  rw [Fin.sum_univ_succ, Finset.mul_sum]
  refine congrArg₂ (· + ·) (by simp) (Finset.sum_congr rfl fun i _ => ?_)
  show (if θ i.succ then 2 ^ (i.val + 1) else 0) = 2 * if θ i.succ then 2 ^ i.val else 0
  split
  · rw [pow_succ, Nat.mul_comm]
  · rfl

theorem eqW_numLE : ∀ (k : ℕ) (z : Fin k → GE) (θ : Fin k → Bool),
    eqW (List.ofFn z) (numLE θ) 1 = Alg.eqk z θ
  | 0, _, _ => by
    rw [List.ofFn_zero]
    show (1 : GE) = ∏ v : Fin 0, _
    simp
  | k + 1, z, θ => by
    rw [List.ofFn_succ]
    show eqW (List.ofFn fun i : Fin k => z i.succ) (numLE θ / 2)
      (1 * if numLE θ % 2 == 1 then z 0 else 1 - z 0) = ∏ v, if θ v then z v else 1 - z v
    rw [eqW_mul, Fin.prod_univ_succ, numLE_succ θ]
    have ih := eqW_numLE k (fun i => z i.succ) fun i => θ i.succ
    cases h : θ 0
    · have e1 : ((if false = true then 1 else 0) + 2 * numLE fun i : Fin k => θ i.succ) / 2 =
          numLE fun i : Fin k => θ i.succ := by
        rw [if_neg Bool.false_ne_true]
        omega
      have e2 : ((if false = true then 1 else 0) + 2 * numLE fun i : Fin k => θ i.succ) % 2 =
          0 := by
        rw [if_neg Bool.false_ne_true]
        omega
      rw [e1, e2, ih]
      simp [Alg.eqk]
    · have e1 : ((if true = true then 1 else 0) + 2 * numLE fun i : Fin k => θ i.succ) / 2 =
          numLE fun i : Fin k => θ i.succ := by
        rw [if_pos rfl]
        omega
      have e2 : ((if true = true then 1 else 0) + 2 * numLE fun i : Fin k => θ i.succ) % 2 =
          1 := by
        rw [if_pos rfl]
        omega
      rw [e1, e2, ih]
      simp [Alg.eqk]

theorem pairsAt_eq : ∀ (xs : List GE) (n : ℕ), pairsAt (eqPairsF xs) n = eqW xs n 1
  | [], _ => rfl
  | x :: xs, n => by
    show (if n % 2 = 1 then x else 1 - x) * pairsAt (eqPairsF xs) (n / 2) =
      eqW xs (n / 2) (1 * if n % 2 == 1 then x else 1 - x)
    rw [eqW_mul, pairsAt_eq xs (n / 2), _root_.one_mul]
    by_cases h : n % 2 = 1
    · simp [h]
    · simp [h]

theorem sum_range_list (f : ℕ → GE) : ∀ n : ℕ, ((List.range n).map f).sum = ∑ i ∈ range n, f i
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_range_list f n,
      Finset.sum_range_succ]
    simp

/-! ### one round that only draws -/

theorem fits_one {n : ℕ} {l : List (RV GE)} (h : fitsAll [(⟨0, n, false⟩ : Fm)] (l.take 1) = true) :
    ∃ r rest, l = r :: rest ∧ r.2.length = n := by
  cases l with
  | nil => exact absurd h (by simp [fitsAll])
  | cons r rest =>
    have h' : (⟨0, n, false⟩ : Fm).fits r = true := by
      have : ((⟨0, n, false⟩ : Fm).fits r && fitsAll [] ([] : List (RV GE))) = true := h
      simpa [fitsAll] using this
    exact ⟨r, rest, rfl, ((Fm.fits_iff _ r).1 h').2.1⟩

theorem ownAt_7 (S : Pub) : ownAt S 7 = ownAt S 6 := by
  first | rfl | simp [ownAt]

theorem ownAt_3 (S : Pub) : ownAt S 3 = ownAt S 2 := by
  first | rfl | simp [ownAt]

variable (A : Dat GE) (sl : Slot → A.J) (st : A.St) (own idx : ℕ)

theorem zero_goes (D : Dt) (hD : D.S = A.toPub) :
    Goes (Sim A sl st own idx 6) (Sim A sl st own idx 7) (cZero D) A.zeroRun
      [⟨0, A.mu + A.d, false⟩] := by
  intro s x h hf
  obtain ⟨r, rest, hr, hl⟩ := fits_one hf
  refine ⟨?_, by
    show s.rounds.tail = s.rounds.drop 1
    rw [hr]
    rfl⟩
  refine ⟨h.st, h.al, h.rows, h.own.trans (by rw [ownAt_7]), h.idx, fun e => absurd e (by decide),
    fun e => absurd e (by decide), fun _ e => absurd e (by decide),
    fun _ e => absurd e (by decide), fun _ => h.cls (by decide), fun _ => ?_⟩
  have hd : (cZero D s).zt = r.2 := by
    show (s.rounds.headD ([], [])).2 = r.2
    rw [hr]
    rfl
  rw [hd]
  refine ⟨hl, fun t ht => ?_⟩
  show (if h : t < A.mu + A.d then _ else _) = _
  rw [dif_pos ht, hr]
  rfl

theorem planes_get (pl : ℕ) (f : ℕ → PscF.PointClaim) (n : ℕ) :
    ((List.range pl).map f)[n]? = if n < pl then some (f n) else none := by
  by_cases h : n < pl
  · rw [if_pos h, List.getElem?_map, List.getElem?_range h]
    rfl
  · rw [if_neg h, List.getElem?_eq_none (by simpa using h)]

theorem join_goes (D : Dt) (hD : D.S = A.toPub) :
    Goes (Sim A sl st own idx 2) (Sim A sl st own idx 3) (cJoin D) A.joinRun
      [⟨0, A.mu, false⟩] := by
  intro s x h hf
  obtain ⟨r, rest, hr, hl⟩ := fits_one hf
  refine ⟨?_, by
    show s.rounds.tail = s.rounds.drop 1
    rw [hr]
    rfl⟩
  have hof : List.ofFn (fun t : Fin A.mu => r.2.getD t.val 0) = r.2 := ofFn_getD r.2 A.mu hl
  have htop : (cJoin D s).top = joinF A.mu r.2 ((List.range A.pl).map s.planes) := by
    show joinF D.S.mu (s.rounds.headD ([], [])).2 ((List.range D.S.pl).map s.planes) = _
    rw [hD, hr]
    rfl
  have hrun : A.joinRun x (s.rounds.take [(⟨0, A.mu, false⟩ : Fm)].length) =
      A.joinNx x fun t => r.2.getD t.val 0 := by
    rw [hr]
    rfl
  have hk : ∀ θ : Fin A.mu → Bool,
      Alg.eqk (fun t : Fin A.mu => r.2.getD t.val 0) θ = eqW r.2 (numLE θ) 1 := fun θ => by
    rw [← eqW_numLE, hof]
  rw [hrun]
  refine ⟨h.st, h.al, h.rows, h.own.trans (by rw [ownAt_3]), h.idx,
    fun e => absurd e (by decide), fun e => absurd e (by decide),
    fun _ _ => h.roots (by decide) (by decide), fun _ _ => ?_, fun e => absurd e (by decide),
    fun e => absurd e (by decide)⟩
  rw [htop]
  refine ⟨?_, ?_, ?_⟩
  · refine congrArg₂ SCl.mk (funext fun j => ?_) ?_
    · show ∑ θ, Alg.eqk (fun t : Fin A.mu => r.2.getD t.val 0) θ * A.formAt x θ j = _
      rw [rdMF_joinF, sum_range_list,
        ← ldLkpNum_sum GE A.mu (planeMF sl r.2 ((List.range A.pl).map s.planes) j)]
      refine Finset.sum_congr rfl fun θ _ => ?_
      unfold planeMF Dat.formAt
      rw [hk, planes_get]
      by_cases hn : numLE θ < A.pl
      · rw [if_pos hn, if_pos hn, h.planes (by decide) _ hn]
        rfl
      · rw [if_neg hn, if_neg hn]
        exact mul_zero _
    · show ∑ θ, Alg.eqk (fun t : Fin A.mu => r.2.getD t.val 0) θ * A.tgtAt x θ = _
      rw [joinF_value, sum_range_list,
        ← ldLkpNum_sum GE A.mu (planeVal r.2 ((List.range A.pl).map s.planes))]
      refine Finset.sum_congr rfl fun θ _ => ?_
      unfold planeVal Dat.tgtAt
      rw [hk, planes_get]
      by_cases hn : numLE θ < A.pl
      · rw [if_pos hn, if_pos hn, h.planes (by decide) _ hn]
        rfl
      · rw [if_neg hn, if_neg hn]
        exact mul_one _
  · rw [joinF_point, hl]
    rfl
  · intro t ht
    rw [joinF_point] at ht ⊢
    show (if h : t < A.mu then _ else _) = _
    rw [dif_pos (hl ▸ ht)]

end Lk6.Mid.Clo

#print axioms Lk6.Mid.Clo.eqW_numLE
#print axioms Lk6.Mid.Clo.pairsAt_eq
#print axioms Lk6.Mid.Clo.zero_goes
#print axioms Lk6.Mid.Clo.join_goes
