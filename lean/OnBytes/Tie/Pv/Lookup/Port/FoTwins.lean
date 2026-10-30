-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Port/FoTwins.lean.
The pure functions of the byte-level verifier's lookup, read in a commutative ring: each is its
plain twin.

The routine OnBytes.Model.Forest.pad computes some fields of its record without a message: the
padding's public factor, the calls' weights, the tables at a point, the joined table, the calls'
points. This file shows, for every reading ρ of the byte-level field E in a
commutative ring K (OnBytes.Model.Reading: a map that takes 0, 1, sums, differences and products to
those of K), that each of these functions, read by ρ, is the plain function of the same shape on
lists over K.

Words under a reading.
  ofF_val: ρ (ofF w) = (w.toNat : K), for every word w, below the prime or not. prime_zero: the
    prime is 0 in K. scale_val: ρ (scaleE w x) = (w.toNat : K) * ρ x. nat_scale: the same at
    n.toUInt64 for n < 2^64 (toNat_word).
The functions.
  eqTab_val: the table of equality weights: (eqTab z).toList.map ρ = eqTabK (z.toList.map ρ).
  padKey_val: Forest.padKeyOf. weight_val, e_val: Forest.callWeight. fac_val: the fold by which
    Forest.draws makes the public factor a (that this fold is the plain function's factor at the
    list of pads: OnBytes/Tie/Pv/Lookup/Forest/FoTwinsFac.lean).
  table_val: Forest.tableAt. joined_val: Forest.joinedTableAt. tT_val, leavesA_val, zk_val: the
    three last fields that pad computes.
Premises: numbers that are turned into words are below 2^64: c < 2^64 for a call's number (in
  fac_val: of the trees below NT), k ≤ 64 for a table's bits.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoTab
import OnBytes.Tie.Pv.Lookup.Port.FoJoin
import OnBytes.Model.HideLaws
import OnBytes.Model.Look
import OnBytes.Field.WordEq
import OnBytes.Field.ExtEq
import Fmt.FieldEFast

set_option autoImplicit false

namespace Fo
open TwV FoNums OnBytes OnBytes.Model

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-! ### words -/

theorem addE_ofF (a b : UInt64) : addE (ofF a) (ofF b) = ofF (addF a b) := by
  apply triple_inj
  rw [addE_triple, ofF_triple, ofF_triple, ofF_triple, addF_eq]
  rfl

theorem ofF_zero : ofF 0 = zeroE := rfl
theorem ofF_one : ofF 1 = oneE := rfl

/-- below the prime -/
theorem ofF_small : ∀ (n : ℕ) (w : UInt64), w.toNat = n → n < 18446744069414584321 → ρ.val (ofF w) =
    (n : K)
  | 0, w, hw, _ => by
    have : w = 0 := UInt64.toNat_inj.1 hw
    rw [this, ofF_zero, ρ.zero, Nat.cast_zero]
  | n + 1, w, hw, hn => by
    have h64 : n < 2 ^ 64 := by omega
    have hv : (UInt64.ofNat n).toNat = n := by rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt h64
    have e : w = addF (UInt64.ofNat n) 1 := by
      apply UInt64.toNat_inj.1
      rw [toNat_addF, hv, hw]
      have : (1 : UInt64).toNat = 1 := rfl
      rw [this, Nat.mod_eq_of_lt hn]
    rw [e, ← addE_ofF, ρ.add, ofF_small n _ hv (by omega), ofF_one, ρ.one, Nat.cast_succ]

include ρ in
/-- The prime is 0 in K. -/
theorem prime_zero : ((18446744069414584321 : ℕ) : K) = 0 := by
  have hv : (UInt64.ofNat 18446744069414584320).toNat = 18446744069414584320 := by decide
  have e : addF (UInt64.ofNat 18446744069414584320) 1 = 0 := by decide
  have h := ρ.add (ofF (UInt64.ofNat 18446744069414584320)) (ofF 1)
  rw [addE_ofF, e, ofF_zero, ρ.zero, ofF_small ρ _ _ hv (by norm_num), ofF_one, ρ.one] at h
  have : ((18446744069414584321 : ℕ) : K) = ((18446744069414584320 : ℕ) : K) + 1 := by
    push_cast; norm_num
  rw [this, ← h]

/-- Every word. -/
theorem ofF_val (w : UInt64) : ρ.val (ofF w) = (w.toNat : K) := by
  have h := ρ.add (ofF w) (ofF 0)
  rw [addE_ofF, ofF_zero, ρ.zero, add_zero] at h
  have hz : (0 : UInt64).toNat = 0 := rfl
  have hv : (addF w 0).toNat = w.toNat % 18446744069414584321 := by
    rw [toNat_addF, hz, Nat.add_zero]
  rw [← h, ofF_small ρ _ _ hv (Nat.mod_lt _ (by norm_num))]
  conv_rhs => rw [← Nat.div_add_mod w.toNat 18446744069414584321]
  rw [Nat.cast_add, Nat.cast_mul, prime_zero ρ, zero_mul, zero_add]

theorem scale_val (s : UInt64) (a : E) : ρ.val (scaleE s a) = (s.toNat : K) * ρ.val a := by
  have e : scaleE s a = mulE (ofF s) a := by
    apply triple_inj
    rw [scaleE_triple, mulE_triple, ofF_triple, Fmt.mulE_ofF]
  rw [e, ρ.mul, ofF_val]

theorem toNat_word (n : ℕ) (hn : n < 2 ^ 64) : n.toUInt64.toNat = n := by
  show (UInt64.ofNat n).toNat = n
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt hn

theorem nat_scale (n : ℕ) (hn : n < 2 ^ 64) (a : E) : ρ.val (scaleE n.toUInt64 a) = (n : K) * ρ.val
    a := by
  rw [scale_val, toNat_word n hn]

/-! ### arrays -/

/-- An array of field elements, read. -/
def rdL (z : Array E) : List K := z.toList.map ρ.val

theorem rdL_getD (z : Array E) (i : ℕ) : ρ.val (z.getD i zeroE) = (rdL ρ z).getD i 0 := by
  unfold rdL
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
      Array.getD_eq_getD_getElem?]
  cases z[i]? with
  | none => exact ρ.zero
  | some x => rfl

theorem rdL_push (z : Array E) (x : E) : rdL ρ (z.push x) = rdL ρ z ++ [ρ.val x] := by
  simp [rdL]

theorem rdL_length (z : Array E) : (rdL ρ z).length = z.size := by simp [rdL]

theorem rdL_extract (z : Array E) (a b : ℕ) : rdL ρ (z.extract a b) = exL (rdL ρ z) a b := by
  unfold rdL exL
  rw [Array.toList_extract, List.extract_eq_take_drop, List.map_take, List.map_drop]

theorem rdL_append (y z : Array E) : rdL ρ (y ++ z) = rdL ρ y ++ rdL ρ z := by simp [rdL]

/-! ### folds -/

theorem foldl_mul_val (g : ℕ → E) (G : ℕ → K) : ∀ (l : List ℕ) (e : E),
    (∀ i ∈ l, ρ.val (g i) = G i) →
    ρ.val (l.foldl (fun e i => mulE e (g i)) e) = l.foldl (fun e i => e * G i) (ρ.val e)
  | [], _, _ => rfl
  | i :: l, e, h => by
    rw [List.foldl_cons, List.foldl_cons,
      foldl_mul_val g G l _ fun j hj => h j (List.mem_cons_of_mem _ hj), ρ.mul,
      h i List.mem_cons_self]

/-- with the equation asked of the list's members alone -/
theorem foldl_add_val (g : ℕ → E) (G : ℕ → K) : ∀ (l : List ℕ) (s : E),
    (∀ i ∈ l, ρ.val (g i) = G i) →
    ρ.val (l.foldl (fun s i => addE s (g i)) s) = l.foldl (fun s i => s + G i) (ρ.val s)
  | [], _, _ => rfl
  | i :: l, s, h => by
    rw [List.foldl_cons, List.foldl_cons, foldl_add_val g G l _ fun j hj => h j
        (List.mem_cons_of_mem _ hj), ρ.add,
      h i List.mem_cons_self]

/-! ### the table of equality weights -/

theorem step_go (zv : E) : ∀ (l : List E) (n : Array E),
    rdL ρ (l.foldl (fun n a => (n.push (subE a (mulE a zv))).push (mulE a zv)) n) =
      rdL ρ n ++ eqTabStepK (l.map ρ.val) (ρ.val zv)
  | [], n => by simp [eqTabStepK]
  | a :: l, n => by
    rw [List.foldl_cons, step_go zv l, rdL_push, rdL_push, ρ.sub, ρ.mul]
    simp [eqTabStepK]

theorem step_val (t : Array E) (zv : E) : rdL ρ (eqTabStep t zv) = eqTabStepK (rdL ρ t) (ρ.val zv)
    := by
  unfold eqTabStep
  rw [← Array.foldl_toList]
  refine (step_go ρ zv t.toList _).trans ?_
  simp [rdL]

theorem eqTab_go : ∀ (l : List E) (t : Array E),
    rdL ρ (l.foldl eqTabStep t) = (l.map ρ.val).foldl eqTabStepK (rdL ρ t)
  | [], _ => rfl
  | zv :: l, t => by
    rw [List.foldl_cons, eqTab_go l, step_val]
    rfl

/-- The table of equality weights. -/
theorem eqTab_val (z : Array E) : rdL ρ (eqTab z) = eqTabK (rdL ρ z) := by
  unfold eqTab eqTabK
  rw [← Array.foldl_toList, eqTab_go]
  simp [rdL, ρ.one]

/-! ### the padding key, the calls' weights, the public factor -/

/-- Forest.padKeyOf. -/
theorem padKey_val (h : Sh) (θ : E) (c : ℕ) (hc : c < 2 ^ 64) :
    ρ.val (Forest.padKeyOf h θ c) = padKeyK h (ρ.val θ) c := by
  unfold Forest.padKeyOf padKeyK OnBytes.Ends.tauN FoNums.t0Of
  rw [ρ.add, ofF_val, nat_scale ρ c hc]
  cases h.calls[c]? <;> rfl

/-- Forest.callWeight. -/
theorem weight_val (h : Sh) (zy : Array E) (c : ℕ) : ρ.val (Forest.callWeight h zy c) = eK h
    (rdL ρ zy) c := by
  unfold Forest.callWeight eK
  refine (foldl_mul_val ρ _ (fun i => if (FoNums.fst h c / 2 ^ FoNums.io h c / 2 ^
      (h.rK - FoNums.io h c - 1 - i)) % 2 = 1
    then (rdL ρ zy).getD i 0 else 1 - (rdL ρ zy).getD i 0) _ _ (fun i _ => ?_)).trans ?_
  · show ρ.val (if (h.first.getD c 0 / 2 ^ h.iota.getD c 0 / 2 ^ (h.rK - h.iota.getD c 0 - 1 - i)) %
      2 = 1 then zy.getD i zeroE
      else subE oneE (zy.getD i zeroE)) =
      if (h.first.getD c 0 / 2 ^ h.iota.getD c 0 / 2 ^ (h.rK - h.iota.getD c 0 - 1 - i)) % 2 = 1
          then (rdL ρ zy).getD i 0
      else 1 - (rdL ρ zy).getD i 0
    by_cases hb : (h.first.getD c 0 / 2 ^ h.iota.getD c 0 / 2 ^ (h.rK - h.iota.getD c 0 - 1 - i)) %
        2 = 1
    · rw [if_pos hb, if_pos hb, rdL_getD]
    · rw [if_neg hb, if_neg hb, ρ.sub, ρ.one, rdL_getD]
  · rw [ρ.one]
    rfl

/-- The fold by which Forest.draws makes the public factor. -/
theorem fac_val (h : Sh) (θ α : E) (hc : ∀ y, y < h.NT → h.callOf.getD y 0 < 2 ^ 64) :
    ρ.val ((List.range h.NT).foldl
      (fun a y => mulE a (powE (subE α (Forest.padKeyOf h θ (h.callOf.getD y 0))) (h.pub.getD y 0)))
      (powE (subE α (Forest.padKeyOf h θ 0)) h.emptyKeys)) =
    (List.range h.NT).foldl (fun a y => a * (ρ.val α - padKeyK h (ρ.val θ) (FoNums.co h y)) ^
        h.pub.getD y 0)
      ((ρ.val α - padKeyK h (ρ.val θ) 0) ^ h.emptyKeys) := by
  refine (foldl_mul_val ρ _ (fun y => (ρ.val α - padKeyK h (ρ.val θ) (FoNums.co h y)) ^ h.pub.getD y
      0) _ _
    (fun y hy => ?_)).trans ?_
  · rw [ρ.pow, ρ.sub, padKey_val ρ h θ _ (hc y (List.mem_range.1 hy))]
    rfl
  · rw [ρ.pow, ρ.sub, padKey_val ρ h θ 0 (by norm_num)]

/-! ### the tables -/

/-- Forest.tableAt. -/
theorem table_val (c : Call) (u : Array E) (hk : c.k ≤ 64) : ρ.val (Forest.tableAt c u) = tableK c
    (rdL ρ u) := by
  unfold Forest.tableAt tableK
  cases c.tau with
  | none =>
    refine (foldl_add_val ρ _ (fun i => ((2 ^ (c.k - 1 - i) : ℕ) : K) * (rdL ρ u).getD i 0) _ _ fun
        i hi => ?_).trans ?_
    · have hi' : i < c.k := List.mem_range.1 hi
      rw [nat_scale ρ _ (Nat.pow_lt_pow_right (by norm_num) (by omega)), rdL_getD]
    · rw [ρ.zero]
  | some rows =>
    show ρ.val ((List.range (eqTab u).size).foldl (fun s t => addE s
        (scaleE (rows.getD t 0) ((eqTab u).getD t zeroE))) zeroE) = _
    refine (foldl_add_val ρ _ (fun t => (((rows.getD t 0).toNat : ℕ) : K) * (eqTabK (rdL ρ u)).getD
        t 0) _ _ fun t _ => ?_).trans ?_
    · rw [scale_val, rdL_getD, eqTab_val]
    · rw [ρ.zero, ← eqTab_val, rdL_length]

/-- Forest.joinedTableAt. -/
theorem joined_val (h : Sh) (θ : E) (tT zc : Array E) (hN : h.NC ≤ 2 ^ 64) :
    ρ.val (Forest.joinedTableAt h θ tT zc) = joinedK h (ρ.val θ) (rdL ρ tT) (rdL ρ zc) := by
  unfold Forest.joinedTableAt joinedK
  refine (foldl_add_val ρ _ (fun c => (eqTabK (rdL ρ zc)).getD c 0 *
    ((rdL ρ tT).getD (min c (h.NC - 1)) 0 + ((min c (h.NC - 1) : ℕ) : K) * ρ.val θ)) _ _ fun c _ =>
        ?_).trans ?_
  · have hm : min c (h.NC - 1) < 2 ^ 64 := by
      have : min c (h.NC - 1) ≤ h.NC - 1 := Nat.min_le_right _ _
      have : 0 < 2 ^ 64 := by norm_num
      omega
    rw [ρ.mul, ρ.add, nat_scale ρ _ hm, rdL_getD, rdL_getD, eqTab_val]
  · rw [ρ.zero]

/-- The calls' tables at the leaves' point. -/
theorem tT_val (h : Sh) (zb0 : Array E) (hk : ∀ k ∈ h.calls.toList, k.k ≤ 64) :
    rdL ρ (h.calls.map fun k => Forest.tableAt k (zb0.extract (h.kT - k.k) h.kT)) = tTK h
        (rdL ρ zb0) := by
  unfold rdL tTK
  rw [Array.toList_map, List.map_map]
  refine List.map_congr_left fun k hkm => ?_
  show ρ.val (Forest.tableAt k (zb0.extract (h.kT - k.k) h.kT)) = _
  rw [table_val ρ k _ (hk k hkm), rdL_extract]
  rfl

/-- alpha - 1 - (the joined table at the leaves' point). -/
theorem leavesA_val (h : Sh) (θ α : E) (zb0 : Array E) (hN : h.NC ≤ 2 ^ 64)
    (hk : ∀ k ∈ h.calls.toList, k.k ≤ 64) :
    ρ.val (subE (subE α oneE) (Forest.joinedTableAt h θ
        (h.calls.map fun k => Forest.tableAt k (zb0.extract (h.kT - k.k) h.kT))
      (zb0.extract h.kT (h.kT + h.cK)))) = leavesAK h (ρ.val θ) (ρ.val α) (rdL ρ zb0) := by
  unfold leavesAK
  rw [ρ.sub, ρ.sub, ρ.one, joined_val ρ h θ _ _ hN, tT_val ρ h zb0 hk, rdL_extract]

/-- The calls' weights. -/
theorem e_val (h : Sh) (zy : Array E) :
    rdL ρ ((Array.range h.NC).map (Forest.callWeight h zy)) = (List.range h.NC).map
        (eK h (rdL ρ zy)) := by
  unfold rdL
  rw [Array.toList_map, Array.toList_range, List.map_map]
  exact List.map_congr_left fun c _ => weight_val ρ h zy c

/-- The calls' points. -/
theorem zk_val (h : Sh) (zx zy : Array E) :
    ((Array.range h.NC).map fun c => zy.extract (h.rK - h.iota.getD c 0) zy.size ++ zx).toList.map
        (rdL ρ) =
      (List.range h.NC).map fun c => zk h.rK (FoNums.io h c) (rdL ρ zx) (rdL ρ zy) := by
  rw [Array.toList_map, Array.toList_range, List.map_map]
  refine List.map_congr_left fun c _ => ?_
  show rdL ρ (zy.extract (h.rK - h.iota.getD c 0) zy.size ++ zx) = _
  rw [rdL_append, rdL_extract]
  unfold zk exL FoNums.io
  rw [← rdL_length ρ zy, ← List.length_drop, List.take_length]

end
end Fo
