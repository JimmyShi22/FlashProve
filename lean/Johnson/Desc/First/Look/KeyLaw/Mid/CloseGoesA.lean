-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Mid/CloseGoesA.lean: lemmas that the closing and the test of the bits
share, for holding the course over the field against the plain functions of the described lookup.

The course over the field is our text of the program's lookup, over the field
(Johnson/Desc/First/Look/KeyLaw/Mid/Course.lean). That the program's run, read in the field, is this
course is shown in files that are not in this library yet.

It imports CloseGoes.lean (the equality weight), CloseSim.lean and CloseCf.lean (`cellW`); `onCell`,
`pairsAt` are those of Johnson/Desc/First/Look/KeyLaw/Mid/Relation.lean, `byVarF` that of
OnBytes/Tie/Pv/KeyLookup/PortRead.lean, `ordDown`, `eqPairsF` those of
Johnson/Desc/First/Look/KeyLaw/Mid/Course.lean.
Main names:
  `fits_mix` flat rounds that fit k formats (dg i scalars, one draw) are a list of pairs (scalars,
    challenge), written flat.
  `fits_head` a first round that fits (1 scalar, 1 draw) is ([μ], [ε]).
  `byVarF_down` at the order from the highest variable down, putting a point back by variable is
    reversing it.
  `cellW_onCell` if pl ≤ 2^mu: the weight `A.cellW π j` of an entry in the extension of the bits is
    `onCell` of the point's pairs.
Limits: statements on lists and sums over the field.

-/
import Johnson.Desc.First.Look.KeyLaw.Mid.CloseGoes
import OnBytes.Tie.Pv.KeyLookup.CloseSim
import Cb.Pv.KeyLookup.CloseCf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.Mid.Clo
open Lk6.PortSim Lk6.Clo

open OnBytes OnBytes.Slice Flat Cb Cb.LdLkp Finset Lk6.PortSim

/-! ### rounds that fit -/

theorem fits_nil {l : List (RV GE)} (h : fitsAll [] l = true) : l = [] := by
  cases l with
  | nil => rfl
  | cons _ _ => exact absurd h (by simp [fitsAll])

theorem fits_cons {x : Fm} {a : List Fm} {l : List (RV GE)} (h : fitsAll (x :: a) l = true) :
    ∃ v l', l = v :: l' ∧ x.fits v = true ∧ fitsAll a l' = true := by
  cases l with
  | nil => exact absurd h (by simp [fitsAll])
  | cons v l' =>
    have h' : x.fits v = true ∧ fitsAll a l' = true := by simpa [fitsAll] using h
    exact ⟨v, l', rfl, h'.1, h'.2⟩

theorem len_one {l : List GE} (h : l.length = 1) : l = [l.headD 0] := (one_headD l h).symm

theorem fits_head {a : List Fm} {l : List (RV GE)}
    (h : fitsAll ((⟨1, 1, false⟩ : Fm) :: a) l = true) :
    ∃ m e l', l = ([m], [e]) :: l' ∧ fitsAll a l' = true := by
  obtain ⟨v, l', rfl, hv, hl⟩ := fits_cons h
  obtain ⟨h1, h2, _⟩ := (Fm.fits_iff _ v).1 hv
  exact ⟨v.1.headD 0, v.2.headD 0, l', by rw [← len_one h1, ← len_one h2], hl⟩

theorem fits_mix : ∀ (k : ℕ) (dg : Fin k → ℕ) (l : List (RV GE)), fitsAll (fmM k dg) l = true →
    ∃ rs : List (List GE × GE), l = rs.map (fun r => (r.1, [r.2])) ∧ rs.length = k ∧
      ∀ i : Fin k, (rs.getD i.val ([], 0)).1.length = dg i
  | 0, _, _, h => ⟨[], fits_nil h, rfl, fun i => i.elim0⟩
  | k + 1, dg, l, h => by
    obtain ⟨v, l', rfl, hv, hl⟩ := fits_cons (x := ⟨dg 0, 1, false⟩) h
    obtain ⟨h1, h2, _⟩ := (Fm.fits_iff _ v).1 hv
    obtain ⟨rs, rfl, hk, hq⟩ := fits_mix k (fun i => dg i.succ) l' hl
    refine ⟨(v.1, v.2.headD 0) :: rs, ?_, by rw [List.length_cons, hk], fun i => ?_⟩
    · show v :: _ = (v.1, [v.2.headD 0]) :: _
      rw [← len_one h2]
    · refine Fin.cases h1 (fun i => ?_) i
      exact hq i

theorem fmM_length : ∀ (k : ℕ) (dg : Fin k → ℕ), (fmM k dg).length = k
  | 0, _ => rfl
  | k + 1, dg => congrArg Nat.succ (fmM_length k fun i => dg i.succ)

/-! ### a point put back by variable -/

theorem lookup_zip' {α : Type} : ∀ (l : List ℕ) (g : List α) (i : ℕ) (hi : i < l.length)
    (hg : i < g.length), l.Nodup → (l.zip g).lookup l[i] = some g[i]
  | [], _, _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | _ :: _, [], _, _, hg, _ => absurd hg (Nat.not_lt_zero _)
  | a :: l, b :: g, 0, _, _, _ => by simp
  | a :: l, b :: g, i + 1, hi, hg, hn => by
    have hi' : i < l.length := Nat.lt_of_succ_lt_succ hi
    have hg' : i < g.length := Nat.lt_of_succ_lt_succ hg
    have hne : l[i] ≠ a := fun h => (List.nodup_cons.1 hn).1 (h ▸ List.getElem_mem hi')
    show List.lookup l[i] ((a, b) :: l.zip g) = some g[i]
    rw [List.lookup_cons, beq_false_of_ne hne]
    exact lookup_zip' l g i hi' hg' (List.nodup_cons.1 hn).2

theorem byVarF_down (g : List GE) : byVarF g (ordDown g.length) = g.reverse := by
  unfold byVarF ordDown
  apply List.ext_getElem
  · simp
  · intro t h1 h2
    have ht : t < g.length := by simpa using h1
    rw [List.getElem_map, List.getElem_range, List.getElem_reverse]
    have hl : g.length - 1 - t < (List.range g.length).reverse.length := by simp; omega
    have he : (List.range g.length).reverse[g.length - 1 - t]'hl = t := by
      rw [List.getElem_reverse, List.getElem_range]
      simp
      omega
    have h := lookup_zip' (List.range g.length).reverse g (g.length - 1 - t) hl (by omega)
      (List.nodup_reverse.2 List.nodup_range)
    rw [he] at h
    rw [h]
    rfl

/-! ### the weight of an entry in the extension of the bits -/

theorem cellW_onCell (A : Dat GE) (hr : A.pl ≤ 2 ^ A.mu) (π : Fin (A.mu + A.d) → GE) (j : A.J) :
    A.cellW π j = onCell A (eqPairsF (List.ofFn π)) j := by
  obtain ⟨F, hF⟩ : ∃ F : ℕ → GE, F = fun n : ℕ =>
      if n % 2 ^ A.mu < A.pl ∧ A.bAt (n / 2 ^ A.mu) (n % 2 ^ A.mu) = j then
        eqW (List.ofFn π) n 1 else 0 := ⟨_, rfl⟩
  have h1 : ∀ c : Fin (A.mu + A.d) → Bool,
      (if A.cell c = some j then Alg.eqk π c else 0) = F (numLE c) := fun c => by
    rw [hF]
    show _ = if numLE c % 2 ^ A.mu < A.pl ∧ A.bAt (numLE c / 2 ^ A.mu) (numLE c % 2 ^ A.mu) = j then
      eqW (List.ofFn π) (numLE c) 1 else 0
    rw [eqW_numLE]
    by_cases hl : numLE c % 2 ^ A.mu < A.pl
    · rw [A.cell_live c hl]
      by_cases e : A.bAt (numLE c / 2 ^ A.mu) (numLE c % 2 ^ A.mu) = j
      · rw [if_pos (congrArg some e), if_pos ⟨hl, e⟩]
      · rw [if_neg fun e' => e (Option.some.inj e'), if_neg fun e' => e e'.2]
    · rw [(A.cell_none_iff c).2 (Nat.le_of_not_lt hl), if_neg (by simp), if_neg fun e' => hl e'.1]
  have e0 : 2 ^ (A.mu + A.d) = 2 ^ A.d * 2 ^ A.mu := by rw [Nat.add_comm, pow_add]
  rw [A.cellW_eq, Finset.sum_congr rfl fun c _ => h1 c, ldLkpNum_sum GE (A.mu + A.d) F, e0,
    Alg.sum_range_mul_add, hF]
  unfold onCell
  refine Finset.sum_congr rfl fun u _ => ?_
  have e1 : ∀ p ∈ range (2 ^ A.mu),
      (if (u * 2 ^ A.mu + p) % 2 ^ A.mu < A.pl ∧
          A.bAt ((u * 2 ^ A.mu + p) / 2 ^ A.mu) ((u * 2 ^ A.mu + p) % 2 ^ A.mu) = j then
        eqW (List.ofFn π) (u * 2 ^ A.mu + p) 1 else 0) =
      if p < A.pl then (if A.bAt u p = j then pairsAt (eqPairsF (List.ofFn π)) (p + 2 ^ A.mu * u)
        else 0) else 0 := fun p hp => by
    have hp' : p < 2 ^ A.mu := Finset.mem_range.1 hp
    have m1 : (u * 2 ^ A.mu + p) % 2 ^ A.mu = p := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp']
    have m2 : (u * 2 ^ A.mu + p) / 2 ^ A.mu = u := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide)),
        Nat.div_eq_of_lt hp', Nat.zero_add]
    rw [m1, m2, pairsAt_eq, Nat.add_comm p, Nat.mul_comm (2 ^ A.mu) u]
    by_cases a : p < A.pl
    · rw [if_pos a]
      by_cases b : A.bAt u p = j
      · rw [if_pos ⟨a, b⟩, if_pos b]
      · rw [if_neg fun e => b e.2, if_neg b]
    · rw [if_neg a, if_neg fun e => a e.1]
  rw [Finset.sum_congr rfl e1, ← Finset.sum_filter]
  have e2 : (range (2 ^ A.mu)).filter (fun b => b < A.pl) = range A.pl := by
    ext b
    simp only [mem_filter, mem_range]
    exact ⟨fun h => h.2, fun h => ⟨Nat.lt_of_lt_of_le h hr, h⟩⟩
  rw [e2]

end Lk6.Mid.Clo

#print axioms Lk6.Mid.Clo.fits_mix
#print axioms Lk6.Mid.Clo.byVarF_down
#print axioms Lk6.Mid.Clo.cellW_onCell
