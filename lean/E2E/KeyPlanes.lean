-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyPlanes.lean: the multiplicities of a key file's lookups, in bits, as a function of the
committed matrix alone: what an honest committer lays into the main rows of the oracle message of
the multiplicities. Definitions, statements and proofs. General in the lookup, in the number of
column variables and in the matrix; plain mathematics and a table of places: no protocol.

The setting (OnBytes/Key/Ranges.lean's head). A lookup of the item "ranges" has parts; a part has
places; runs cover places; a key stands at a place and a column: the lookup's offset plus the
digits' weights times the matrix's entries at the place's rows. A place without a run is padding;
there a public key stands, and it is not counted. The prover sends, for each row t of the range
table 0 .. 2^d - 1, how many keys equal t, in bits; bit j of all these numbers is plane j. The words
part, place, run, plane and block of planes are the library's own (there; `Wf.Block`).

What is defined. The matrix is a reader `entry : row → column → GF`.
  `Pos l k`: a part, a place of it and a column. `live`, `keyAt`: a run covers the place; the key
    there (at padding: the public key). With the library's `runIn`, `rowOf`
    (Johnson/Pack/KeyPort.lean).
  `countOf entry k l t`: the number of live positions whose key is t.
  `bitOf entry k l t j`: bit j of that number, as 0 or 1 in the base field.
  `planesData entry k lookups ell row place`: what stands at a place of a main row: by the library's
    table of where the planes lie (`Wf.layout`, OnBytes/Key/Ranges.lean); nothing where no block of
    planes lies.
What is shown.
  `count_le`, **`count_fits`**: AT EVERY MATRIX a count is at most the number of live positions; so
    W bits write it if all positions together are fewer than 2^W. `bits_write`: then the bits below
    W, each with its weight 2^j, add up to the count.
  `bit_is_bit`: a bit is 0 or 1.
  **`planes_valid`**: if every live key is a row of the table, the padding key too, the table's rows
    are distinct in the field and the counts fit W bits, then AT EVERY alpha of every commutative
    ring over the base field: the product of alpha - key over ALL positions is
    (alpha - padding key)^(padding positions) times the product over the planes j below W of
    (the product over t of 1 + bit · (alpha - 1 - t))^(2^j). From the library's
    `Alg.Lookup.keySide_eq_tableSide`, `planes_eq`, `mult_testBit`.
  `count_sum`, `bits_sum`: under the same premises the counts add up to the number of live
    positions; and so do, in the ring, the bits below W, each with its weight 2^j.
    `live_add_padding`: live positions and positions of padding are all positions.

Limits.
- Mathematics on one lookup. No round, no sumcheck, no oracle message, no mask, no coin: what a
  prover sends about these bits beyond the bits is not here.
- That the verifier's text of a lookup asks the identity of `planes_valid` in this form is a reading
  of its head (Johnson/Desc/First/Look/K3LookupGeneral.lean: the public factor; the factor of a bit in a
  leaf); no theorem ties the two here.
- `planesData` follows `Wf.layout`; that the verifier reads a plane's bit at that place is the
  library's text, not shown here.
- Out of range a key may be no row of the table; it is then counted nowhere.
- At the full size nothing here can be evaluated: a lookup has some 2^39 positions.
- Nothing on hiding follows from this file.


-/
import Johnson.Pack.KeyPort
import Alg.Lookup

set_option autoImplicit false

namespace AtPublicFiles.Key
open Finset
open OnBytes.Slice (GF toF)
open OnBytes.Params (WfRun WfPart WfLookup)
open Johnson.Pack (runIn rowOf)

/-! ## 1. Positions, keys, counts -/

/-- A part of the lookup, a place of it, a column. -/
abbrev Pos (l : WfLookup) (k : ℕ) : Type :=
  (f : Fin l.parts.length) × Fin (2 ^ (l.parts.get f).logPlaces) × Fin (2 ^ k)

section
variable (entry : ℕ → ℕ → GF) (k : ℕ) (l : WfLookup)

/-- A run covers the position's place. -/
def live (i : Pos l k) : Bool := (runIn (l.parts.get i.1).runs i.2.1.val).isSome

/-- The key at a place u of a part p and a column c. -/
def keyOfPlace (p : WfPart) (u c : ℕ) : GF :=
  match runIn p.runs u with
  | none => toF l.paddingKey
  | some r => toF l.offset +
      ∑ q ∈ range l.digitWeight.length, toF (l.digitWeight.getD q 0) * entry (rowOf r u q) c

/-- The key at a position. -/
def keyAt (i : Pos l k) : GF := keyOfPlace entry l (l.parts.get i.1) i.2.1.val i.2.2.val

/-- **The multiplicity of the table's row t**: the number of live positions whose key is t. -/
def countOf (t : ℕ) : ℕ :=
  (univ.filter fun i : Pos l k => live k l i = true ∧ keyAt entry k l i = (t : GF)).card

/-- **Bit j of the multiplicity of t**, in the base field. -/
def bitOf (t j : ℕ) : GF := if (countOf entry k l t).testBit j then 1 else 0

/-- The live positions, and the positions of padding. -/
def liveCount : ℕ := (univ.filter fun i : Pos l k => live k l i = true).card
def paddingCount : ℕ := (univ.filter fun i : Pos l k => ¬ live k l i = true).card

end

/-! ## 2. Where a bit lies -/

/-- **What stands at a place of a main row of the oracle message of the multiplicities.** ell: the
places of a main row. -/
def planesData (entry : ℕ → ℕ → GF) (k : ℕ) (lookups : List WfLookup) (ell row place : ℕ) :
    Option GF :=
  ((OnBytes.Wf.layout lookups ell).find? fun b =>
      b.row == row && decide (b.firstPlace ≤ place) &&
        decide (place < b.firstPlace + 2 ^ b.bits)).map fun b =>
    bitOf entry k (lookups.getD b.lookup default) ((place - b.firstPlace) / 2 ^ b.logPlanes)
      (b.first + (place - b.firstPlace) % 2 ^ b.logPlanes)

/-! ## 3. The counts fit their bits, at every matrix -/

section
variable (entry : ℕ → ℕ → GF) (k : ℕ) (l : WfLookup)

theorem count_le (t : ℕ) : countOf entry k l t ≤ liveCount k l :=
  card_le_card fun i hi => mem_filter.2 ⟨mem_univ i, (mem_filter.1 hi).2.1⟩

/-- The number of all positions. -/
theorem card_pos : Fintype.card (Pos l k) =
    ∑ f : Fin l.parts.length, 2 ^ (l.parts.get f).logPlaces * 2 ^ k := by
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

theorem liveCount_le : liveCount k l ≤ Fintype.card (Pos l k) := card_le_univ _

/-- Live positions and positions of padding are all positions. -/
theorem live_add_padding : liveCount k l + paddingCount k l = Fintype.card (Pos l k) := by
  unfold liveCount paddingCount
  rw [Finset.card_filter_add_card_filter_not, Finset.card_univ]

/-- **At every matrix the counts fit W bits**, if all positions together are fewer than 2^W. -/
theorem count_fits {W : ℕ} (h : Fintype.card (Pos l k) < 2 ^ W) (t : ℕ) :
    countOf entry k l t < 2 ^ W :=
  lt_of_le_of_lt ((count_le entry k l t).trans (liveCount_le k l)) h

/-- Then the bits below W write the count. -/
theorem bits_write {W : ℕ} (h : Fintype.card (Pos l k) < 2 ^ W) (t : ℕ) :
    Alg.Lookup.mult W (fun t j => (countOf entry k l t).testBit j) t = countOf entry k l t :=
  Alg.Lookup.mult_testBit W (countOf entry k l) t (count_fits entry k l h t)

theorem bit_is_bit (t j : ℕ) : bitOf entry k l t j = 0 ∨ bitOf entry k l t j = 1 := by
  unfold bitOf
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

end

/-! ## 4. In range: the identity of the two products, at every alpha -/

section
variable (entry : ℕ → ℕ → GF) (k : ℕ) (l : WfLookup)

/-- Every live key is a row of the table. -/
def KeysIn : Prop :=
  ∀ i : Pos l k, live k l i = true → ∃ t : ℕ, t < 2 ^ l.d ∧ keyAt entry k l i = (t : GF)

/-- At padding the key is the public key. -/
theorem key_padding (i : Pos l k) (h : ¬ live k l i = true) :
    keyAt entry k l i = toF l.paddingKey := by
  unfold live at h
  unfold keyAt keyOfPlace
  cases hr : runIn (l.parts.get i.1).runs i.2.1.val with
  | none => rfl
  | some r => rw [hr] at h; exact absurd rfl h

open Classical in
/-- The table's row of a live position's key; row 0 at padding. -/
noncomputable def rowAt (hin : KeysIn entry k l) (i : Pos l k) : Fin (2 ^ l.d) :=
  if h : live k l i = true then ⟨(hin i h).choose, (hin i h).choose_spec.1⟩
  else ⟨0, Nat.two_pow_pos _⟩

theorem rowAt_key (hin : KeysIn entry k l) (i : Pos l k) (h : live k l i = true) :
    keyAt entry k l i = ((rowAt entry k l hin i).val : GF) := by
  unfold rowAt
  rw [dif_pos h]
  exact (hin i h).choose_spec.2

/-- The live positions with the row t are those that are counted at t. -/
theorem fibre_eq (hin : KeysIn entry k l)
    (hinj : ∀ t t' : ℕ, t < 2 ^ l.d → t' < 2 ^ l.d → (t : GF) = (t' : GF) → t = t')
    (t : Fin (2 ^ l.d)) (i : Pos l k) :
    (live k l i = true ∧ rowAt entry k l hin i = t) ↔
      (live k l i = true ∧ keyAt entry k l i = (t.val : GF)) := by
  constructor
  · rintro ⟨h, e⟩
    exact ⟨h, by rw [rowAt_key entry k l hin i h, e]⟩
  · rintro ⟨h, e⟩
    refine ⟨h, Fin.ext (hinj _ _ (rowAt entry k l hin i).isLt t.isLt ?_)⟩
    rw [← rowAt_key entry k l hin i h, e]

/-- **In range the counts add up to the number of live positions.** -/
theorem count_sum (hin : KeysIn entry k l)
    (hinj : ∀ t t' : ℕ, t < 2 ^ l.d → t' < 2 ^ l.d → (t : GF) = (t' : GF) → t = t') :
    ∑ t : Fin (2 ^ l.d), countOf entry k l t.val = liveCount k l := by
  classical
  unfold liveCount
  rw [Finset.card_eq_sum_card_fiberwise (f := rowAt entry k l hin) (t := univ)
    fun _ _ => mem_coe.2 (mem_univ _)]
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold countOf
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and]
  exact (fibre_eq entry k l hin hinj t i).symm

variable {A : Type} [CommRing A] (φ : GF →+* A)

/-- **The bits, each with its weight 2^j, add up IN THE RING to the number of live positions**: the
sum over the table's rows and the planes below W. -/
theorem bits_sum {W : ℕ} (hin : KeysIn entry k l)
    (hinj : ∀ t t' : ℕ, t < 2 ^ l.d → t' < 2 ^ l.d → (t : GF) = (t' : GF) → t = t')
    (hW : Fintype.card (Pos l k) < 2 ^ W) :
    ∑ t : Fin (2 ^ l.d), ∑ j ∈ range W, (2 : A) ^ j * φ (bitOf entry k l t.val j) =
      (liveCount k l : A) := by
  rw [← count_sum entry k l hin hinj, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← bits_write entry k l hW t.val]
  unfold Alg.Lookup.mult
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold bitOf
  split
  · rw [map_one, mul_one, Nat.cast_pow, Nat.cast_ofNat]
  · rw [map_zero, mul_zero, Nat.cast_zero]

/-- **The identity of the two products at the honest planes.** -/
theorem planes_valid {W : ℕ} (hin : KeysIn entry k l)
    (hpad : ∃ t₀ : ℕ, t₀ < 2 ^ l.d ∧ toF l.paddingKey = (t₀ : GF))
    (hinj : ∀ t t' : ℕ, t < 2 ^ l.d → t' < 2 ^ l.d → (t : GF) = (t' : GF) → t = t')
    (hW : Fintype.card (Pos l k) < 2 ^ W) (al : A) :
    ∏ i : Pos l k, (al - φ (keyAt entry k l i)) =
      (al - φ (toF l.paddingKey)) ^ paddingCount k l *
        ∏ j ∈ range W, (∏ t : Fin (2 ^ l.d),
          (1 + φ (bitOf entry k l t.val j) * (al - 1 - φ (t.val : GF)))) ^ 2 ^ j := by
  classical
  obtain ⟨t₀, ht₀, e₀⟩ := hpad
  have key := congrArg (Polynomial.eval al)
    (Alg.Lookup.keySide_eq_tableSide (fun i : Pos l k => φ (keyAt entry k l i))
      (fun t : Fin (2 ^ l.d) => φ (t.val : GF)) ⟨t₀, ht₀⟩ (fun i => ¬ live k l i = true)
      (rowAt entry k l hin)
      (fun i h => congrArg φ ((key_padding entry k l i h).trans e₀))
      (fun i h => congrArg φ (rowAt_key entry k l hin i (not_not.1 h))))
  rw [Alg.Lookup.keySide_eval, Alg.Lookup.tableSide_eval] at key
  rw [key, ← e₀]
  congr 1
  -- the planes
  have hb : ∀ (t : Fin (2 ^ l.d)) (j : ℕ), φ (bitOf entry k l t.val j) =
      if (countOf entry k l t.val).testBit j then (1 : A) else 0 := fun t j => by
    unfold bitOf
    split
    · exact map_one φ
    · exact map_zero φ
  simp only [hb]
  rw [Alg.Lookup.planes_eq W (fun (t : Fin (2 ^ l.d)) j => (countOf entry k l t.val).testBit j)
    (fun t : Fin (2 ^ l.d) => φ (t.val : GF)) al]
  refine Finset.prod_congr rfl fun t _ => ?_
  congr 1
  rw [Alg.Lookup.mult_testBit W (fun t : Fin (2 ^ l.d) => countOf entry k l t.val) t
    (count_fits entry k l hW t.val)]
  unfold countOf
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, not_not]
  exact fibre_eq entry k l hin hinj t i

end

end AtPublicFiles.Key

#print axioms AtPublicFiles.Key.count_le
#print axioms AtPublicFiles.Key.card_pos
#print axioms AtPublicFiles.Key.count_fits
#print axioms AtPublicFiles.Key.bits_write
#print axioms AtPublicFiles.Key.bit_is_bit
#print axioms AtPublicFiles.Key.key_padding
#print axioms AtPublicFiles.Key.rowAt_key
#print axioms AtPublicFiles.Key.fibre_eq
#print axioms AtPublicFiles.Key.count_sum
#print axioms AtPublicFiles.Key.live_add_padding
#print axioms AtPublicFiles.Key.bits_sum
#print axioms AtPublicFiles.Key.planes_valid
