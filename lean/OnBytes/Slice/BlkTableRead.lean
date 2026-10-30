-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/BlkTableRead.lean: the table's side of a lookup of a key file's first chain: the
program's public values, read in the field.

`Wf.lookupOf` (OnBytes/Iop/Wf.lean) hands a lookup to the block of OnBytes/Iop/Lkp.lean with one
range table, without a shift, and with padding that holds one row, the padding key's. This file
reads, at these public inputs, the three functions of that block that compute elements from the
table:
 `Lkp.tableAt`: the table's extension at a point is the sum of 2 ^ i times coordinate i;
 `Lkp.leavesFactor`: the factor of a bit in a leaf is alpha - 1 - that sum at the coordinates above
 the plane's;
 `Lkp.factorOf`: the public factor is alpha less what a place of padding holds, to the number of
 places of padding.
It also has two public facts on the planes: there are at most 2 ^ mu real planes, and the bit that
the program's vectors read at a plane that is not real is 0.

Main theorems: `read_bitsLoop`, `tableAt_lookupOf`, `read_tableAt`, `read_leavesFactor`,
`read_factorLoop`, `read_factorOf`, `planesOf_le`, `bitsOf_real`.

Not claimed. Nothing on tables that are written out, on a shift, or on several blocks of keys.
Nothing on a run on a view, on soundness or on hiding.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.BlkLeavesTop
import OnBytes.Slice.BlkPlanesAt
import OnBytes.Slice.KeyPlanesVals

set_option autoImplicit false

namespace OnBytes.Slice.Planes
open Prob Cb
open OnBytes.Params (WfLookup WfPublic)
open OnBytes.Slice.Leaves (read_natE)

/-! ## The table's extension -/

/-- The loop of a range table's extension, from any variable and any running value. -/
theorem read_bitsLoop : ∀ (z : List E) (s : ℕ) (r : E), s + z.length ≤ 64 →
    readE (((List.range' s z.length).zip z).foldl
      (fun r p => addE r (mulE (Lkp.natE (2 ^ p.1)) p.2)) r) =
      readE r + 2 ^ s * bitsVal (z.map readE)
  | [], _, r, _ => by simp [bitsVal]
  | x :: z, s, r, h => by
    rw [List.length_cons] at h
    rw [List.length_cons, List.range'_succ, List.zip_cons_cons, List.foldl_cons,
      read_bitsLoop z (s + 1) _ (by omega), readE_add, readE_mul,
      read_natE _ (Nat.pow_lt_pow_right (by decide) (by omega)), List.map_cons, bitsVal, pow_succ]
    push_cast
    ring

/-- What stands behind the other list's length does not enter the list of pairs. -/
theorem zip_append_short {α β : Type} (b : List β) : ∀ (a : List β) (z : List α),
    z.length ≤ a.length → (a ++ b).zip z = a.zip z
  | _, [], _ => by simp
  | [], _ :: _, h => by simp at h
  | x :: a, y :: z, h => by
    rw [List.cons_append, List.zip_cons_cons, List.zip_cons_cons,
      zip_append_short b a z (by simpa using h)]

/-- Numbers beyond a list's length do not enter the list of pairs. -/
theorem zip_range_le {α : Type} (z : List α) (n : ℕ) (h : z.length ≤ n) :
    (List.range n).zip z = (List.range z.length).zip z := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.range_add, zip_append_short _ _ _ (by rw [List.length_range])]

/-- The program's text for the table's extension, at a lookup's one range table: the loop over the
tables has one step; the conditions on closed values are decided. By definition. -/
theorem tableAt_lookupOf (id : ℕ) (m : Wf.Matrix) (l : WfLookup) (θ : E) (point : List E) :
    Lkp.tableAt (Wf.lookupOf id m l) θ point =
      addE zeroE (mulE
        ((List.range (l.d - l.d)).foldl (fun w i =>
          mulE w (Lkp.pick (Nat.testBit 0 (l.d + i)) (point.getD (l.d + i) zeroE))) oneE)
        (addE
          (((List.range l.d).zip ((point.drop 0).take l.d)).foldl
            (fun r p => addE r (mulE (Lkp.natE (2 ^ p.1)) p.2)) zeroE)
          (mulE (Lkp.natE 0) θ))) := rfl

/-- The extension of a lookup's range table at a point is the sum of 2 ^ i times coordinate i,
over the first d coordinates. -/
theorem read_tableAt (id : ℕ) (m : Wf.Matrix) (l : WfLookup) (θ : E) (point : List E)
    (hd : l.d ≤ 64) :
    readE (Lkp.tableAt (Wf.lookupOf id m l) θ point) = bitsVal ((point.map readE).take l.d) := by
  have hl : (point.take l.d).length ≤ l.d := by rw [List.length_take]; omega
  have e : Lkp.tableAt (Wf.lookupOf id m l) θ point =
      addE zeroE (mulE oneE (addE
        (((List.range l.d).zip (point.take l.d)).foldl
          (fun r p => addE r (mulE (Lkp.natE (2 ^ p.1)) p.2)) zeroE)
        (mulE (Lkp.natE 0) θ))) := by
    rw [tableAt_lookupOf, Nat.sub_self]
    rfl
  have hb := read_bitsLoop (point.take l.d) 0 zeroE (by omega)
  rw [← List.range_eq_range', ← zip_range_le _ _ hl] at hb
  rw [e, readE_add, readE_mul, readE_add, readE_mul, hb, read_natE 0 (by decide), readE_zero,
    readE_one, List.map_take]
  push_cast
  ring

/-- The factor of a bit in a leaf. -/
theorem read_leavesFactor (id : ℕ) (m : Wf.Matrix) (l : WfLookup) (θ α : E) (point : List E)
    (hd : l.d ≤ 64) :
    readE (Lkp.leavesFactor (Wf.lookupOf id m l) θ α point) =
      readE α - 1 - bitsVal (((point.map readE).drop l.mu).take l.d) := by
  unfold Lkp.leavesFactor
  rw [readE_sub, readE_sub, readE_one]
  show _ - readE (Lkp.tableAt (Wf.lookupOf id m l) θ (point.drop l.mu)) = _
  rw [read_tableAt id m l θ _ hd, List.map_drop]

/-! ## The public factor -/

/-- The loop of the public factor, where all padding holds one row. -/
theorem read_factorLoop (S : Lkp.Public) (θ α : E) (row : ℕ) : ∀ (ps : List (ℕ × ℕ)) (a : E),
    (∀ p ∈ ps, p.2 = row) →
    readE (ps.foldl (fun a p => mulE a (powE (subE α (Lkp.rowAt S θ p.2)) p.1)) a) =
      readE a * (readE α - readE (Lkp.rowAt S θ row)) ^ (ps.map (·.1)).sum
  | [], a, _ => by simp
  | p :: ps, a, h => by
    rw [List.foldl_cons, read_factorLoop S θ α row ps _ fun x hx => h x (List.mem_cons_of_mem _ hx),
      readE_mul, readE_pow, readE_sub, h p List.mem_cons_self, List.map_cons, List.sum_cons,
      pow_add, mul_assoc]

/-- Every run of padding of a lookup holds the padding key's row. -/
theorem padding_row (id : ℕ) (m : Wf.Matrix) (l : WfLookup) :
    ∀ q ∈ (Wf.lookupOf id m l).padding, q.row = l.paddingKey.toNat := by
  intro q hq
  have hq' : q ∈ (l.parts.zipIdx 0).flatMap fun x =>
      (Wf.paddingFrom m.kCol x.2 l.paddingKey.toNat x.1.logPlaces 0 x.1.runs #[]).toList := hq
  obtain ⟨x, _, hqx⟩ := List.mem_flatMap.1 hq'
  rw [Leaves.paddingFrom_eq] at hqx
  rcases List.mem_append.1 hqx with h | h
  · cases h
  obtain ⟨g, _, hs⟩ := List.mem_flatMap.1 h
  unfold Wf.stretch at hs
  split at hs
  · rw [List.mem_singleton.1 hs]
  · cases hs

/-- The public factor is alpha less what a place of padding holds, to the number of places of
padding. -/
theorem read_factorOf (id : ℕ) (m : Wf.Matrix) (l : WfLookup) (θ α : E) :
    readE (Lkp.factorOf (Wf.lookupOf id m l) θ α) =
      (readE α - Leaves.padOf id m l θ) ^ Lkp.paddingCount (Wf.lookupOf id m l) := by
  unfold Lkp.factorOf Lkp.paddingCount Leaves.padOf
  rw [read_factorLoop _ θ α l.paddingKey.toNat _ _ fun p hp => ?_, readE_one, one_mul]
  unfold Lkp.paddingList at hp
  rcases List.mem_append.1 hp with h | h
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h
    exact padding_row id m l q hq
  · have hn : (Wf.lookupOf id m l).keys.filter (·.function.isNone) = [] := rfl
    rw [hn] at h
    cases h

/-! ## Two public facts on the planes -/

/-- There are at most 2 ^ mu real planes. -/
theorem planesOf_le {l : WfLookup} (hl : Wf.lookupOk Wf.fBits l = true) :
    Wf.planesOf l ≤ 2 ^ l.mu := by
  simp only [Wf.lookupOk, Bool.and_eq_true, decide_eq_true_eq] at hl
  have h5 : l.live < 2 ^ l.mu := hl.1.1.1.1.1.1.1.1.1.1.1.2
  unfold Wf.planesOf
  split
  · exact le_refl _
  · omega

/-- At a plane that is not real the bit that the program's vectors read is 0: no block holds the
plane. -/
theorem bitsOf_real {K : Type} [CommRing K] (x : WfPublic) (codes : Codes) (i : ℕ) (l : WfLookup)
    (hi : x.lookups[i]? = some l) (T : ℕ → K) (t j : ℕ) (hj : Wf.planesOf l ≤ j) :
    bitsOf x codes i T t j = 0 := by
  unfold bitsOf bitAt
  refine List.sum_eq_zero fun v hv => ?_
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hv
  obtain ⟨hb1, hb2⟩ := List.mem_filter.1 hb
  have hbi : b.lookup = i := by simpa using hb2
  obtain ⟨l', h1, h2, _⟩ := layout_mem _ _ b hb1
  rw [hbi, hi] at h1
  obtain rfl := Option.some.inj h1
  obtain ⟨_, g2⟩ := liveLoop_spec (Wf.planesOf l) 64 0 _ h2
  have g2' : b.first + 2 ^ b.logPlanes ≤ Wf.planesOf l := g2
  exact if_neg (by omega)

end OnBytes.Slice.Planes
