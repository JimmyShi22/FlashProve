-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/RowsCarry.lean: "a row holds" (RowHolds, Johnson/Desc/Key/KeyWords.lean, at same := "ρ a = ρ b") carried from a later statement back to an
earlier one, and from a renamed row back to the row. Theorems. It reads no block and no record of a chain.
  rowHolds_extends   a row that has passed the tests at S holds at a later statement S' just where it holds at S.
  rowIn_names_members   a row that has passed the tests at a group names members of that group alone.
  has_same           two messages of one shape have the same tables.
  offTables_renamed  a row that names o alone and reads as 0 off T's tables, renamed to n, reads as 0 off T''s tables, where the two messages have one shape.
  rowHolds_renamed   a row that has passed the tests at T, at the group of o alone, holds at T under val just where the row renamed to n holds at T' under val',
                     where the two messages have one shape, the statements one codes, and val' reads at n as val reads at o.
  tableBits_same     two messages of one shape, in two statements with one codes, have tables of one number of index bits.
  placeOk_renamed    a summand that fits its place at T, at the group of o alone, fits the like place of n at T', at the group of n alone.
  rowIn_renamed      a row that has passed the tests at T, at the group of o alone, has, renamed to n, passed them at T', at the group of n alone.
Limits. Nothing on which rows have passed the tests. Nothing on soundness or on hiding.
-/
import Johnson.Desc.Key.RowHoldsSays
import Johnson.Desc.Third.Law.Renamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key
open OnBytes
open VerifiableInference.Desc.Third.Law (oracles_renamed coefficient_renamed coefficient_off_names tableSize_same says_renamed)

variable {K : Type} [CommRing K] (ρ : Model.Reading K)

theorem rowHolds_extends {S S' : Statement} {G : OnBytes.Group} {row : OnBytes.Row} (hE : Means.Extends S S')
    (hr : Means.RowIn S G row) (val : Nat → Part → Nat → E) :
    RowHolds (fun a b => ρ.val a = ρ.val b) S' val row ↔ RowHolds (fun a b => ρ.val a = ρ.val b) S val row := by
  rw [rowHolds_iff_says_of_rowIn ρ S' G val row (Means.RowIn.extends hE (fun _ h => h) hr),
    rowHolds_iff_says_of_rowIn ρ S G val row hr]
  exact Means.says_extends ρ hE hr _

theorem rowIn_names_members {S : Statement} {G : OnBytes.Group} {row : OnBytes.Row} (hr : Means.RowIn S G row) :
    ∀ x ∈ row.oracles, x ∈ G.members.toList := by
  intro x hx
  simp only [Row.oracles, List.mem_append, Array.toList_map, List.mem_map] at hx
  rcases hx with ((⟨t, ht, rfl⟩ | ⟨u, hu, rfl⟩) | ⟨w, hw, rfl⟩) | ⟨f, hf, rfl⟩
  · exact ((Means.placeOk_iff _ _ _ _ _ _).1 (hr.terms t ht)).1
  · exact ((Means.placeOk_iff _ _ _ _ _ _).1 (hr.units u hu)).1
  · exact ((Means.placeOk_iff _ _ _ _ _ _).1 (hr.runs w hw).2.2).1
  · exact ((Means.placeOk_iff _ _ _ _ _ _).1 (hr.forms f hf).1).1

theorem has_same (T T' : Statement) (o n : Nat) (x x' : OnBytes.Oracle) (hx : T.oracles[o]? = some x)
    (hx' : T'.oracles[n]? = some x') (hs : x'.shape = x.shape) (pt : Part) : T'.has n pt = T.has o pt := by
  simp [Statement.has, hx, hx', hs]

theorem offTables_renamed (T T' : Statement) (r : OnBytes.Row) (o n : Nat) (hr : ∀ x ∈ r.oracles, x = o)
    (hh : ∀ pt, T'.has n pt = T.has o pt) (hoff : OffTables ρ T r) : OffTables ρ T' (r.renamed n) := by
  intro o' pt i h'
  by_cases e : o' = n
  · subst e
    rw [coefficient_renamed ρ r o o' hr pt i]
    exact hoff o pt i ((hh pt).symm.trans h')
  · exact coefficient_off_names ρ (r.renamed n) o' (fun hm => e (oracles_renamed r n o' hm)) pt i

theorem rowHolds_renamed (T T' : Statement) (r : OnBytes.Row) (o n c : Nat) (x x' : OnBytes.Oracle)
    (hx : T.oracles[o]? = some x) (hx' : T'.oracles[n]? = some x') (hs : x'.shape = x.shape) (hc : T'.codes = T.codes)
    (hr : Means.RowIn T { code := c, members := #[o] } r) (val val' : Nat → Part → Nat → E)
    (hv : ∀ pt i, ρ.val (val' n pt i) = ρ.val (val o pt i)) :
    RowHolds (fun a b => ρ.val a = ρ.val b) T' val' (r.renamed n) ↔ RowHolds (fun a b => ρ.val a = ρ.val b) T val r := by
  have alone : ∀ z ∈ r.oracles, z = o := fun z hz => by
    have := rowIn_names_members hr z hz
    simpa using this
  have hoff := offTables_of_rowIn ρ T _ r hr
  rw [rowHolds_iff_says ρ T' val' (r.renamed n) (offTables_renamed ρ T T' r o n alone (has_same T T' o n x x' hx hx' hs) hoff),
    rowHolds_iff_says ρ T val r hoff]
  exact says_renamed ρ T T' r o n (Array.getElem?_eq_some_iff.1 hx).1 (Array.getElem?_eq_some_iff.1 hx').1 alone
    (tableSize_same T T' o n x x' hx hx' hs hc) _ _ hv

theorem tableBits_same (T T' : Statement) (o n : Nat) (x x' : OnBytes.Oracle) (hx : T.oracles[o]? = some x)
    (hx' : T'.oracles[n]? = some x') (hs : x'.shape = x.shape) (hc : T'.codes = T.codes) (pt : Part) :
    T'.tableBits n pt = T.tableBits o pt := by
  simp [Statement.tableBits, Statement.rowBits, Statement.placeBits, hx, hx', hs, hc]

theorem placeOk_renamed (T T' : Statement) (o n c c' : Nat) (x x' : OnBytes.Oracle) (hx : T.oracles[o]? = some x)
    (hx' : T'.oracles[n]? = some x') (hs : x'.shape = x.shape) (hc : T'.codes = T.codes) (o' : Nat) (pt : Part) (vars idx : Nat)
    (h : Blk.placeOk T { code := c, members := #[o] } o' pt vars idx = true) :
    o' = o ∧ Blk.placeOk T' { code := c', members := #[n] } n pt vars idx = true := by
  obtain ⟨hm, hh, hv, hi⟩ := (Means.placeOk_iff _ _ _ _ _ _).1 h
  have e : o' = o := by simpa using hm
  subst e
  have tb := tableBits_same T T' o' n x x' hx hx' hs hc pt
  refine ⟨rfl, (Means.placeOk_iff _ _ _ _ _ _).2 ⟨by simp, (has_same T T' o' n x x' hx hx' hs pt).trans hh, hv.trans tb.symm, ?_⟩⟩
  rw [tb]
  exact hi

theorem rowIn_renamed (T T' : Statement) (r : OnBytes.Row) (o n c c' : Nat) (x x' : OnBytes.Oracle)
    (hx : T.oracles[o]? = some x) (hx' : T'.oracles[n]? = some x') (hs : x'.shape = x.shape) (hc : T'.codes = T.codes)
    (hr : Means.RowIn T { code := c, members := #[o] } r) :
    Means.RowIn T' { code := c', members := #[n] } (r.renamed n) := by
  have P := placeOk_renamed T T' o n c c' x x' hx hx' hs hc
  have tb := tableBits_same T T' o n x x' hx hx' hs hc
  refine ⟨fun t ht => ?_, fun u hu => ?_, fun w hw => ?_, fun f hf => ?_⟩
  · simp only [Row.renamed, Array.toList_map, List.mem_map] at ht
    obtain ⟨t0, ht0, rfl⟩ := ht
    exact (P _ _ _ _ (hr.terms t0 ht0)).2
  · simp only [Row.renamed, Array.toList_map, List.mem_map] at hu
    obtain ⟨u0, hu0, rfl⟩ := hu
    obtain ⟨e, h⟩ := P _ _ _ _ (hr.units u0 hu0)
    show Blk.placeOk T' _ n u0.part (T'.tableBits n u0.part) u0.index = true
    rw [tb, ← e]
    exact h
  · simp only [Row.renamed, Array.toList_map, List.mem_map] at hw
    obtain ⟨w0, hw0, rfl⟩ := hw
    obtain ⟨h0, h1, h2⟩ := hr.runs w0 hw0
    obtain ⟨e, h⟩ := P _ _ _ _ h2
    refine ⟨h0, h1, ?_⟩
    show Blk.placeOk T' _ n w0.part (T'.tableBits n w0.part) (w0.first + w0.step * (w0.coeffs.size - 1)) = true
    rw [tb, ← e]
    exact h
  · simp only [Row.renamed, Array.toList_map, List.mem_map] at hf
    obtain ⟨f0, hf0, rfl⟩ := hf
    obtain ⟨h1, h2⟩ := hr.forms f0 hf0
    obtain ⟨e, h⟩ := P _ _ _ _ h1
    show Blk.placeOk T' _ n .main (T'.tableBits n .main) 0 = true ∧ f0.c.fits (T'.tableBits n .main) = true
    rw [tb, ← e]
    exact ⟨h, h2⟩

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.rowIn_renamed
#print axioms VerifiableInference.Desc.Key.rowHolds_extends
#print axioms VerifiableInference.Desc.Key.rowHolds_renamed
