-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/Call.lean: THE LAW OF A CALL'S KEY VECTOR, PROVED: CallStatement and
CallPointStatement of HeadCallLaw.lean. From the law of fromLookup (an entry's weight is the equality
weight of its column; wsum is the sum of the weights), the law of a call's columns (the caller's sum
with its padding term is a sum over columns), and: the equality weights of a point add up to 1.
-/
import Mathlib
import Johnson.Desc.Kinds.HeadCallLaw
import Johnson.Desc.Kinds.Law.Columns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open OnBytes (E)
open Norm (lt ls d S2 T)

theorem slot_mem {keys : List PlaceKey} {s : Nat} (h : s < keys.length) : slot keys s ∈ keys := by
  unfold slot
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

theorem sum_map_slot (v : PlaceKey → K) : ∀ keys : List PlaceKey,
    (keys.map v).sum = (Finset.range keys.length).sum fun s => v (slot keys s)
  | [] => by simp
  | k :: ks => by
    rw [List.map_cons, List.sum_cons, sum_map_slot v ks, List.length_cons,
      Finset.sum_range_succ']
    exact add_comm _ _

theorem size_extract0 {z : Point} {J b : Nat} (h : z.size = J + b) : (z.extract 0 J).size = J := by
  rw [← Array.length_toList, toList_extract, List.length_take, List.length_drop,
    Array.length_toList, h]
  exact Nat.min_eq_left (by omega)

section Sized
variable [Sizes]

theorem getD_lens {keys : List PlaceKey} {s : Nat} (h : s < keys.length) :
    (keys.map lenOf).getD s 0 = lenOf (slot keys s) := by
  unfold slot
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem h]
  rfl

/-- The law at one call, of its parts. H: the keys' places are this call's; hpad: the padding's term.
-/
theorem call_core {floor : Nat} {zx : Point} {zk : Nat → Point} {i : FromLookup}
    (L : LettersOk floor zk i) (hP : PointsOk floor zx zk) (hlen : ∀ k, lenOf k < 2 ^ 41)
    {c : Nat} {keys : List PlaceKey} (hc : callList[c]? = some keys)
    (H : ∀ s, s < keys.length → placeOf (slot keys s) = (c, s) ∧ keysOf (slot keys s) = keys)
    (padE : E) (pad : K)
    (hpad : rd padE = pad * (1 - (Finset.range keys.length).sum fun s =>
      rd (wsumOf i (slot keys s))))
    (v : PlaceKey → K) (G : PlaceKey → Nat → Nat → K)
    (hv : ∀ s, s < keys.length → SpreadAt i G (slot keys s) (v (slot keys s))) :
    rd padE + (Finset.range keys.length).sum (fun s => v (slot keys s))
      = (Finset.range (2 ^ lJ floor keys)).sum fun col => (Finset.range T).sum fun t =>
          rd (eq ((zk c).extract 0 (lJ floor keys)) col) * rd (eq i.norm.zt t)
            * tableOf (keys.map lenOf) (fun s x => G (slot keys s) x t) pad col := by
  obtain ⟨hsz, _⟩ := hP c keys hc
  have hlenl : (keys.map lenOf).length = keys.length := List.length_map ..
  have hw : (Finset.range (2 ^ lJ floor keys)).sum
      (fun col => rd (eq ((zk c).extract 0 (lJ floor keys)) col)) = 1 := by
    have h0 := sum_rd_eq ((zk c).extract 0 (lJ floor keys))
    rwa [size_extract0 hsz] at h0
  have hWt : (Finset.range T).sum (fun t => rd (eq i.norm.zt t)) = 1 := by
    have h0 := sum_rd_eq i.norm.zt
    rwa [L.zt] at h0
  have hN : (keys.map lenOf).sum ≤ 2 ^ lJ floor keys :=
    le_trans (le_two_pow_clog2 _) (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
  have hl41 : ∀ n ∈ keys.map lenOf, n < 2 ^ 41 := by
    intro n hn
    obtain ⟨k, _, rfl⟩ := List.mem_map.1 hn
    exact hlen k
  have hew : ∀ s, s < keys.length → ∀ x, x < lenOf (slot keys s) →
      rd (ewOf i (slot keys s) x)
        = rd (eq ((zk c).extract 0 (lJ floor keys)) (column (keys.map lenOf) s x)) := by
    intro s hs x hx
    rw [L.column _ x hx]
    unfold onColumns columnOf
    rw [(H s hs).1, (H s hs).2]
  have oc := fun t => over_columns K (keys.map lenOf) (2 ^ lJ floor keys)
    (fun col => rd (eq ((zk c).extract 0 (lJ floor keys)) col))
    (fun s x => G (slot keys s) x t) pad hl41 hN hw
  have hB : ((Finset.range keys.length).sum fun s => rd (wsumOf i (slot keys s)))
      = (Finset.range (keys.map lenOf).length).sum fun s =>
          (Finset.range ((keys.map lenOf).getD s 0)).sum fun x =>
            rd (eq ((zk c).extract 0 (lJ floor keys)) (column (keys.map lenOf) s x)) := by
    rw [hlenl]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' := Finset.mem_range.1 hs
    rw [L.wsum, rd_sumTo, getD_lens hs']
    exact Finset.sum_congr rfl fun x hx => hew s hs' x (Finset.mem_range.1 hx)
  have hV : ((Finset.range keys.length).sum fun s => v (slot keys s))
      = (Finset.range T).sum fun t => rd (eq i.norm.zt t) *
          (Finset.range (keys.map lenOf).length).sum fun s =>
            (Finset.range ((keys.map lenOf).getD s 0)).sum fun x =>
              rd (eq ((zk c).extract 0 (lJ floor keys)) (column (keys.map lenOf) s x))
                * G (slot keys s) x t := by
    calc ((Finset.range keys.length).sum fun s => v (slot keys s))
        = (Finset.range (keys.map lenOf).length).sum fun s =>
            (Finset.range ((keys.map lenOf).getD s 0)).sum fun x => (Finset.range T).sum fun t =>
              rd (eq i.norm.zt t) *
                (rd (eq ((zk c).extract 0 (lJ floor keys)) (column (keys.map lenOf) s x))
                  * G (slot keys s) x t) := by
          rw [hlenl]
          refine Finset.sum_congr rfl fun s hs => ?_
          have hs' := Finset.mem_range.1 hs
          rw [hv s hs', getD_lens hs']
          refine Finset.sum_congr rfl fun x hx => ?_
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [hew s hs' x (Finset.mem_range.1 hx)]
          ring
      _ = (Finset.range (keys.map lenOf).length).sum fun s => (Finset.range T).sum fun t =>
            (Finset.range ((keys.map lenOf).getD s 0)).sum fun x =>
              rd (eq i.norm.zt t) *
                (rd (eq ((zk c).extract 0 (lJ floor keys)) (column (keys.map lenOf) s x))
                  * G (slot keys s) x t) :=
          Finset.sum_congr rfl fun s _ => Finset.sum_comm
      _ = (Finset.range T).sum fun t => (Finset.range (keys.map lenOf).length).sum fun s =>
            (Finset.range ((keys.map lenOf).getD s 0)).sum fun x =>
              rd (eq i.norm.zt t) *
                (rd (eq ((zk c).extract 0 (lJ floor keys)) (column (keys.map lenOf) s x))
                  * G (slot keys s) x t) := Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.mul_sum]
  have hR : ((Finset.range (2 ^ lJ floor keys)).sum fun col => (Finset.range T).sum fun t =>
      rd (eq ((zk c).extract 0 (lJ floor keys)) col) * rd (eq i.norm.zt t)
        * tableOf (keys.map lenOf) (fun s x => G (slot keys s) x t) pad col)
      = (Finset.range T).sum fun t => rd (eq i.norm.zt t) *
          (Finset.range (2 ^ lJ floor keys)).sum fun col =>
            rd (eq ((zk c).extract 0 (lJ floor keys)) col)
              * tableOf (keys.map lenOf) (fun s x => G (slot keys s) x t) pad col := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun col _ => ?_
    ring
  rw [hR, hpad, hB, hV]
  have oc' := fun t => (oc t).symm
  simp only [oc', mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hWt, one_mul]
  ring

theorem rd_foldl_add : ∀ (l : List E) (s : E), rd (l.foldl (· + ·) s) = rd s + (l.map rd).sum
  | [], s => by simp
  | a :: l, s => by
    rw [List.foldl_cons, rd_foldl_add l, rd_add, List.map_cons, List.sum_cons]
    ring

/-- The padding's term of a call, as fromLookup makes it. -/
def padOf (floor : Nat) (zk : Nat → Point) (c : Nat) : E :=
  padKey c * (1 - ((callKeys c).map fun k => (made floor zk k).wsum).foldl (· + ·) 0)

theorem pad_made (floor : Nat) (zx : Point) (zk : Nat → Point) {c : Nat} (hc : c < 6) :
    ((fromLookup floor zx zk).calls.getD c (0, [])).1 = padOf floor zk c := by
  interval_cases c <;> rfl

/-- The padding's term of each call. -/
theorem pad_spec (floor : Nat) (zx : Point) (zk : Nat → Point) {c : Nat} (hc : c < 6) :
    rd ((fromLookup floor zx zk).calls.getD c (0, [])).1
      = (padKey c : K) * (1 - (Finset.range (callKeys c).length).sum fun s =>
          rd (wsumOf (fromLookup floor zx zk) (slot (callKeys c) s))) := by
  rw [pad_made floor zx zk hc]
  unfold padOf
  rw [rd_mul, rd_natCast, rd_sub, rd_one, rd_foldl_add, rd_zero, zero_add, List.map_map, sum_map_slot]
  simp only [Function.comp, wsum_made]

end Sized

theorem call_get {c : Nat} (hc : c < 6) : callList[c]? = some (callKeys c) := by
  interval_cases c <;> rfl

theorem call_places {c : Nat} (hc : c < 6) : ∀ s, s < (callKeys c).length →
    placeOf (slot (callKeys c) s) = (c, s) ∧ keysOf (slot (callKeys c) s) = callKeys c := by
  interval_cases c
  · intro s hs
    have h3 : s < 3 := hs
    interval_cases s <;> exact ⟨rfl, rfl⟩
  · intro s hs
    have h3 : s < 1 := hs
    interval_cases s <;> exact ⟨rfl, rfl⟩
  · intro s hs
    have h3 : s < 2 := hs
    interval_cases s <;> exact ⟨rfl, rfl⟩
  · intro s hs
    have h3 : s < 1 := hs
    interval_cases s <;> exact ⟨rfl, rfl⟩
  · intro s hs
    have h3 : s < 1 := hs
    interval_cases s <;> exact ⟨rfl, rfl⟩
  · intro s hs
    have h3 : s < 1 := hs
    interval_cases s <;> exact ⟨rfl, rfl⟩

/-- **THE LAW OF A CALL'S KEY VECTOR.** -/
theorem call_law : CallStatement := by
  intro _ floor zx zk hV hlen hP c hc v G hv
  rw [sum_map_slot]
  exact call_core (fromLookup_law floor zx zk hV hlen hP) hP hlen (call_get hc) (call_places hc) _ _
    (pad_spec floor zx zk hc) v G fun s hs => hv _ (slot_mem hs)

/-- **The same at the call's key point.** -/
theorem call_point_law : CallPointStatement := by
  intro _ floor zx zk hV hlen hP c hc v G hv
  have L := fromLookup_law floor zx zk hV hlen hP
  obtain ⟨hsz, _⟩ := hP c _ (call_get hc)
  have hTe : (2 : Nat) ^ lt = T := rfl
  rw [call_law floor zx zk hV hlen hP c hc v G hv, hsz, pow_add, hTe,
    ← sum_blocks T _ (2 ^ lJ floor (callKeys c))]
  refine Finset.sum_congr rfl fun col _ => ?_
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' : t < 2 ^ (fromLookup floor zx zk).norm.zt.size := by
    rw [L.zt]
    exact Finset.mem_range.1 ht
  have hs := eq_split (L.tail c _ (call_get hc)) col t ht'
  rw [L.zt] at hs
  have hT : 0 < T := by
    unfold T
    positivity
  have h1 : (T * col + t) / T = col := by
    rw [Nat.mul_add_div hT, Nat.div_eq_of_lt (Finset.mem_range.1 ht), Nat.add_zero]
  have h2 : (T * col + t) % T = t := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (Finset.mem_range.1 ht)]
  have hs' : eq (zk c) (T * col + t)
      = eq ((zk c).extract 0 (lJ floor (callKeys c))) col * eq (fromLookup floor zx zk).norm.zt t :=
    hs
  rw [h1, h2, hs', rd_mul]

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.call_law
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.call_point_law
