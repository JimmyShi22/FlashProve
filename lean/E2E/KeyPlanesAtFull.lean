-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyPlanesAtFull.lean: E2E/KeyPlanes.lean at the two lookups of the full size
(`lk0Full`, `lk1Full`, Johnson/Top/H/KeyRangesFull.lean) and at a matrix of the full size's shape.
Definitions, statements and proofs.

What is defined.
  `entryOf M`: the reader of a matrix M of 3,076,096 rows and 2^18 columns over the extension field:
    the first coordinate of the cell; 0 outside the shape.
What is shown.
  `card_full`: a lookup's positions, padding counted: 12 · 2^36 and 12 · 2^35.
  **`counts_fit_full`**: AT EVERY READER, in range or not: a multiplicity of the first lookup is
    below 2^40, one of the second below 2^39: the numbers of real planes that the two lookups name.
  `key_tie`: where every cell of M lies in the base field, a key of E2E/KeyPlanes.lean, read in the
    extension field, is the library's key (`keyOf` with `oP`, `coP`, Johnson/Pack/KeyRuns.lean,
    KeyPort.lean) over `cubeOf M` at the same place and column number.
  **`keysIn_full`**: for M in range (`Flat.InRange`) every live key of both lookups is a row of its
    table: from the library's `partsIn_iff_inRange` (Johnson/Top/H/KeyMeaning.lean).
  **`planes_valid_full`**: so for M in range, at every alpha of the extension field, both lookups
    have the identity of `planes_valid`, with 40 and 39 planes.
  `count_sum_full`: and the multiplicities add up to the live positions.
  **`layout_full`**: where the planes lie in two main rows of 2^18 places: the library's `Wf.layout`
    at the two lookups is `sixBlocks`, six blocks written out.

Limits. Those of E2E/KeyPlanes.lean. The two lookups are the library's written values; that they are
the lookups of a key file's item at any public files is not shown here. The number 2^18 of a main
row's places is set by hand; Lean's evaluator printed it for the written sizes of the key. How many
positions are live is not computed. Nothing on hiding follows from this file.


-/
import E2E.KeyPlanes
import Johnson.Top.H.KeyMeaning
import Johnson.Top.H.KeyForests

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.Key
open Finset
open OnBytes.Slice (GF GE toF)
open OnBytes.Params (WfRun WfPart WfLookup)
open Johnson.Pack (runIn rowOf oP coP partAt keyOf PartsIn cubeOf lk0Full lk1Full)
open Inst.Model.Layout (kRef hRef)
open Cb.Lkp (InTable)

/-! ## 1. The numbers -/

theorem sum_get {α : Type} (g : α → ℕ) :
    ∀ l : List α, ∑ f : Fin l.length, g (l.get f) = (l.map g).sum
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, List.sum_cons, ← sum_get g l]
    exact Fin.sum_univ_succ fun f : Fin (l.length + 1) => g ((a :: l).get f)

set_option maxRecDepth 1000000 in
theorem places_full : lk0Full.parts.map (·.logPlaces) = List.replicate 12 18 ∧
    lk1Full.parts.map (·.logPlaces) = List.replicate 12 17 := by decide +kernel

/-- The positions of the two lookups, padding counted. -/
theorem card_full : Fintype.card (Pos lk0Full kRef) = 12 * 2 ^ 36 ∧
    Fintype.card (Pos lk1Full kRef) = 12 * 2 ^ 35 := by
  have e : ∀ ps : List WfPart, ps.map (fun p : WfPart => 2 ^ p.logPlaces * 2 ^ kRef) =
      (ps.map (·.logPlaces)).map fun n => 2 ^ n * 2 ^ kRef := fun ps => by
    rw [List.map_map]
    rfl
  constructor
  · rw [card_pos, sum_get (fun p : WfPart => 2 ^ p.logPlaces * 2 ^ kRef), e, places_full.1,
      List.map_replicate, List.sum_replicate, smul_eq_mul]
    show 12 * (2 ^ 18 * 2 ^ 18) = 12 * 2 ^ 36
    norm_num
  · rw [card_pos, sum_get (fun p : WfPart => 2 ^ p.logPlaces * 2 ^ kRef), e, places_full.2,
      List.map_replicate, List.sum_replicate, smul_eq_mul]
    show 12 * (2 ^ 17 * 2 ^ 18) = 12 * 2 ^ 35
    norm_num

/-- **At every reader the multiplicities fit the lookups' real planes.** -/
theorem counts_fit_full (entry : ℕ → ℕ → GF) (t : ℕ) :
    countOf entry kRef lk0Full t < 2 ^ 40 ∧ countOf entry kRef lk1Full t < 2 ^ 39 :=
  ⟨count_fits entry kRef lk0Full (by rw [card_full.1]; norm_num) t,
    count_fits entry kRef lk1Full (by rw [card_full.2]; norm_num) t⟩

/-! ## 2. The keys are the library's -/

section
variable (M : Fin hRef → Fin (2 ^ kRef) → GE)

/-- The reader of a matrix. -/
def entryOf (y c : ℕ) : GF := if h : y < hRef ∧ c < 2 ^ kRef then (M ⟨y, h.1⟩ ⟨c, h.2⟩).c0 else 0

/-- Every cell lies in the base field. -/
def InBase : Prop := ∀ y c, M y c = algebraMap GF GE (M y c).c0

omit M in
theorem c0_map (x : GF) : (algebraMap GF GE x).c0 = x := rfl

theorem inBase_of_inRange (h : VerifiableInference.OnPublicFiles.Flat.InRange M) : InBase M := by
  obtain ⟨i, hS, -⟩ := h
  intro y c
  rw [hS y c, ← map_intCast (algebraMap GF GE), c0_map]

theorem pick (v : ℕ) (g : Fin hRef → GE) :
    ∑ r : Fin hRef, (if r.val = v then (1 : GE) else 0) * g r =
      if hv : v < hRef then g ⟨v, hv⟩ else 0 := by
  by_cases hv : v < hRef
  · rw [dif_pos hv, Fintype.sum_eq_single ⟨v, hv⟩]
    · rw [if_pos rfl, one_mul]
    · intro r hr
      rw [if_neg fun e => hr (Fin.ext e), zero_mul]
  · rw [dif_neg hv]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [if_neg fun e : r.val = v => hv (e ▸ r.isLt), zero_mul]

/-- **A key, read in the extension field, is the library's key.** -/
theorem key_tie (hb : InBase M) (l : WfLookup) (p : WfPart) (u c : ℕ) (hc : c < 2 ^ kRef) :
    algebraMap GF GE (keyOfPlace (entryOf M) l p u c) =
      keyOf kRef (cubeOf M) (oP l p) (coP hRef l p) (u * 2 ^ kRef + c) := by
  rw [Johnson.Pack.keyOf_row kRef (cubeOf M) (oP l p) (coP hRef l p) u c hc]
  unfold keyOfPlace oP coP
  cases runIn p.runs u with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, if_false, zero_mul, Finset.sum_const_zero,
      add_zero]
  | some r =>
    simp only [Option.isSome_some, if_true]
    rw [map_add, map_sum, add_right_inj]
    simp only [Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← Finset.mul_sum, map_mul, pick]
    refine congrArg (fun z => algebraMap GF GE (toF (l.digitWeight.getD q 0)) * z) ?_
    unfold entryOf
    by_cases hv : rowOf r u q < hRef
    · rw [dif_pos hv, dif_pos ⟨hv, hc⟩, Johnson.Pack.cubeOf_bits M _ c hc]
      exact (hb _ _).symm
    · rw [dif_neg hv, dif_neg fun h => hv h.1, map_zero]

/-- Every live key is a row of the table, if the library's keys of all parts are. -/
theorem keysIn_of_inTable (hb : InBase M) (l : WfLookup)
    (h : ∀ f, f < l.parts.length → InTable ((partAt l f).logPlaces + kRef) l.d
      (keyOf kRef (cubeOf M) (oP l (partAt l f)) (coP hRef l (partAt l f)))
      fun u => ((u : ℕ) : GE)) : KeysIn (entryOf M) kRef l := by
  rintro ⟨f, u, c⟩ -
  have ep : partAt l f.val = l.parts.get f := by
    unfold partAt
    rw [List.getD_eq_getElem _ _ f.isLt]
    rfl
  have hlt : u.val * 2 ^ kRef + c.val < 2 ^ ((partAt l f.val).logPlaces + kRef) := by
    rw [ep, pow_add]
    have hu := u.isLt
    have hc := c.isLt
    calc u.val * 2 ^ kRef + c.val < u.val * 2 ^ kRef + 2 ^ kRef := Nat.add_lt_add_left hc _
      _ = (u.val + 1) * 2 ^ kRef := by ring
      _ ≤ 2 ^ (l.parts.get f).logPlaces * 2 ^ kRef := Nat.mul_le_mul_right _ hu
  obtain ⟨t, ht, e⟩ := h f.val f.isLt _ hlt
  refine ⟨t, ht, (algebraMap GF GE).injective ?_⟩
  rw [map_natCast]
  rw [ep, ← key_tie M hb l (l.parts.get f) u.val c.val c.isLt] at e
  exact e

end

/-! ## 3. In range -/

theorem cast_inj {d : ℕ} (hd : 2 ^ d ≤ 2 ^ 17) (t t' : ℕ) (h : t < 2 ^ d) (h' : t' < 2 ^ d)
    (e : (t : GF) = (t' : GF)) : t = t' := by
  have hp := Johnson.Pack.p_big
  have e' := (ZMod.natCast_eq_natCast_iff' t t' Cb.Gl.p).1 e
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at e'

theorem inj₀ : ∀ t t' : ℕ, t < 2 ^ lk0Full.d → t' < 2 ^ lk0Full.d → (t : GF) = (t' : GF) → t = t' :=
  cast_inj (d := lk0Full.d) (by show 2 ^ 8 ≤ 2 ^ 17; norm_num)

theorem inj₁ : ∀ t t' : ℕ, t < 2 ^ lk1Full.d → t' < 2 ^ lk1Full.d → (t : GF) = (t' : GF) → t = t' :=
  cast_inj (d := lk1Full.d) (by show 2 ^ 13 ≤ 2 ^ 17; norm_num)

section
variable (M : Fin hRef → Fin (2 ^ kRef) → GE) (hM : VerifiableInference.OnPublicFiles.Flat.InRange M)
include hM

/-- **For a matrix in range every live key of both lookups is a row of its table.** -/
theorem keysIn_full : KeysIn (entryOf M) kRef lk0Full ∧ KeysIn (entryOf M) kRef lk1Full := by
  have P := (Johnson.Pack.partsIn_iff_inRange M).2 hM
  have hb := inBase_of_inRange M hM
  exact ⟨keysIn_of_inTable M hb lk0Full fun f hf => P.1 f hf,
    keysIn_of_inTable M hb lk1Full fun f hf => P.2 f hf⟩

/-- **For a matrix in range: the identity of the two products at the honest planes of both lookups,
at every alpha.** -/
theorem planes_valid_full (al : GE) :
    (∏ i : Pos lk0Full kRef, (al - algebraMap GF GE (keyAt (entryOf M) kRef lk0Full i)) =
      (al - algebraMap GF GE (toF lk0Full.paddingKey)) ^ paddingCount kRef lk0Full *
        ∏ j ∈ range 40, (∏ t : Fin (2 ^ lk0Full.d),
          (1 + algebraMap GF GE (bitOf (entryOf M) kRef lk0Full t.val j) *
            (al - 1 - algebraMap GF GE (t.val : GF)))) ^ 2 ^ j) ∧
    (∏ i : Pos lk1Full kRef, (al - algebraMap GF GE (keyAt (entryOf M) kRef lk1Full i)) =
      (al - algebraMap GF GE (toF lk1Full.paddingKey)) ^ paddingCount kRef lk1Full *
        ∏ j ∈ range 39, (∏ t : Fin (2 ^ lk1Full.d),
          (1 + algebraMap GF GE (bitOf (entryOf M) kRef lk1Full t.val j) *
            (al - 1 - algebraMap GF GE (t.val : GF)))) ^ 2 ^ j) :=
  ⟨planes_valid (entryOf M) kRef lk0Full (algebraMap GF GE) (keysIn_full M hM).1
      ⟨0, Nat.two_pow_pos _, OnBytes.Slice.toF_zero.trans Nat.cast_zero.symm⟩
      inj₀ (by rw [card_full.1]; norm_num) al,
    planes_valid (entryOf M) kRef lk1Full (algebraMap GF GE) (keysIn_full M hM).2
      ⟨0, Nat.two_pow_pos _, OnBytes.Slice.toF_zero.trans Nat.cast_zero.symm⟩
      inj₁ (by rw [card_full.2]; norm_num) al⟩

/-- And the multiplicities add up to the live positions. -/
theorem count_sum_full :
    ∑ t : Fin (2 ^ lk0Full.d), countOf (entryOf M) kRef lk0Full t.val = liveCount kRef lk0Full ∧
      ∑ t : Fin (2 ^ lk1Full.d), countOf (entryOf M) kRef lk1Full t.val =
        liveCount kRef lk1Full :=
  ⟨count_sum (entryOf M) kRef lk0Full (keysIn_full M hM).1 inj₀,
    count_sum (entryOf M) kRef lk1Full (keysIn_full M hM).2
      inj₁⟩

end

/-! ## 4. Where the planes lie -/

set_option maxRecDepth 1000000 in
/-- The blocks of real planes of the two lookups, in the lookups' order, before they are placed. -/
theorem blocks_full : ([lk0Full, lk1Full].zipIdx.flatMap fun x =>
      (OnBytes.Lkp.liveBlocks (OnBytes.Wf.planesOf x.1)).map fun b =>
        (⟨x.2, b.1, b.2, b.2 + x.1.d, 0, 0⟩ : OnBytes.Wf.Block)) =
    [⟨0, 0, 5, 13, 0, 0⟩, ⟨0, 32, 3, 11, 0, 0⟩, ⟨1, 0, 5, 18, 0, 0⟩, ⟨1, 32, 2, 15, 0, 0⟩,
      ⟨1, 36, 1, 14, 0, 0⟩, ⟨1, 38, 0, 13, 0, 0⟩] := by decide +kernel

/-- Sorted, the largest first. (Lean's kernel does not reduce the library's sort; the simplifier
unfolds it.) -/
theorem sorted_full : ([⟨0, 0, 5, 13, 0, 0⟩, ⟨0, 32, 3, 11, 0, 0⟩, ⟨1, 0, 5, 18, 0, 0⟩,
      ⟨1, 32, 2, 15, 0, 0⟩, ⟨1, 36, 1, 14, 0, 0⟩, ⟨1, 38, 0, 13, 0, 0⟩] :
      List OnBytes.Wf.Block).mergeSort (fun a b => decide (b.bits ≤ a.bits)) =
    [⟨1, 0, 5, 18, 0, 0⟩, ⟨1, 32, 2, 15, 0, 0⟩, ⟨1, 36, 1, 14, 0, 0⟩, ⟨0, 0, 5, 13, 0, 0⟩,
      ⟨1, 38, 0, 13, 0, 0⟩, ⟨0, 32, 3, 11, 0, 0⟩] := by
  simp [List.mergeSort, List.MergeSort.Internal.splitInTwo]

/-- The six blocks: lookup, first plane, logarithm of the number of planes, logarithm of the number
of entries, main row, first place. -/
def sixBlocks : List OnBytes.Wf.Block :=
  [⟨1, 0, 5, 18, 0, 0⟩, ⟨1, 32, 2, 15, 1, 0⟩, ⟨1, 36, 1, 14, 1, 32768⟩, ⟨0, 0, 5, 13, 1, 49152⟩,
    ⟨1, 38, 0, 13, 1, 57344⟩, ⟨0, 32, 3, 11, 1, 65536⟩]

theorem placed_full : OnBytes.Wf.layFrom (2 ^ 18) 0 0 [⟨1, 0, 5, 18, 0, 0⟩, ⟨1, 32, 2, 15, 0, 0⟩,
      ⟨1, 36, 1, 14, 0, 0⟩, ⟨0, 0, 5, 13, 0, 0⟩, ⟨1, 38, 0, 13, 0, 0⟩, ⟨0, 32, 3, 11, 0, 0⟩] =
    sixBlocks := by decide +kernel

/-- **Where the planes lie in two main rows of 2^18 places.** -/
theorem layout_full : OnBytes.Wf.layout [lk0Full, lk1Full] (2 ^ 18) = sixBlocks := by
  unfold OnBytes.Wf.layout
  dsimp only
  rw [blocks_full, sorted_full, placed_full]

end AtPublicFiles.Key

#print axioms AtPublicFiles.Key.card_full
#print axioms AtPublicFiles.Key.counts_fit_full
#print axioms AtPublicFiles.Key.inBase_of_inRange
#print axioms AtPublicFiles.Key.key_tie
#print axioms AtPublicFiles.Key.keysIn_of_inTable
#print axioms AtPublicFiles.Key.cast_inj
#print axioms AtPublicFiles.Key.keysIn_full
#print axioms AtPublicFiles.Key.planes_valid_full
#print axioms AtPublicFiles.Key.count_sum_full
#print axioms AtPublicFiles.Key.layout_full
