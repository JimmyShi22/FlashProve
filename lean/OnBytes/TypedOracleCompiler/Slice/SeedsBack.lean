-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/SeedsBack.lean: the seeds of a table's record as a typed value holds them, written
back as the program's lists; and that the seeds which the program draws come back as they were.

Why. The commitment ID's string holds the record's seeds (R4.11). The statement word of a typed
value (`stmtId`, OnBytes/TypedOracleCompiler/Slice/EntryRunMain.lean) is a function of the value alone, so it writes
the seeds that the value holds. A converter reads the program's lists of seeds into the value
(`seedOfC`, OnBytes/TypedOracleCompiler/Slice/EntryConv.lean). That the word is the program's own ID needs the way
back.

Definitions, statements and proofs. Main names (namespace `TypedOracleCompiler.Slice`):
  `seedsL sd`: for each seed in its order the list of its point's coordinates and its factor, each
    written as the program's element with words below the prime (`writeE`,
    OnBytes/Slice/KeyOfRec.lean).
  `seedsFlat sd`: the same as one flat list of triples of words: seed by seed, the coordinates and
    then
    the factor: as the ID's string has them.
  `seedsL_seedOfC`: THE WAY BACK: a list of s seeds, each with lg coordinates and in order
    (`SeedOK`, OnBytes/Slice/SeedWords.lean), read into a value and written back, is the list.
  `recordSeeds_sizes`: what the program's `recordSeeds` gives has `count` seeds of `bits`
    coordinates each.
  `seedsL_of_drawn`: so the seeds that the program draws come back as they were.

Limits. Values alone. A list that is not in order, or of other sizes, need not come back: `seedOfC`
fills what lacks and takes the factor 1 for a factor that reads as 0. Nothing on where a value's
seeds come from: that they are the drawn ones is a test of the judge, not a property of these lists.
Nothing on what an ID fixes, on soundness or on hiding.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryConv
import OnBytes.Slice.SeedWords
import OnBytes.Slice.KeyOfRecBack

set_option autoImplicit false

namespace TypedOracleCompiler.Slice

open OnBytes OnBytes.Slice

/-- The seeds that a typed value holds, as the program's lists: seed by seed, the point's
coordinates and the factor, each written with words below the prime. -/
def seedsL {lg s : ℕ} (sd : Sd1 lg s) : List (List OnBytes.E × OnBytes.E) :=
  List.ofFn fun i : Fin s => (List.ofFn fun t : Fin lg => writeE ((sd i).1 t), writeE (sd i).2.val)

/-- The same as one flat list of triples of words: seed by seed, the coordinates and then the
factor. -/
def seedsFlat {lg s : ℕ} (sd : Sd1 lg s) : AnsT :=
  ((seedsL sd).flatMap fun y => y.1 ++ [y.2]).map OnBytes.E.triple

/-- One seed in order, with lg coordinates, read and written back. -/
theorem seedL1_back (lg : ℕ) (y : List OnBytes.E × OnBytes.E) (hl : y.1.length = lg) (hy : SeedOK y) :
    ((List.ofFn fun t : Fin lg => writeE ((seedOf1C lg y).1 t), writeE (seedOf1C lg y).2.val) :
      List OnBytes.E × OnBytes.E) = y := by
  obtain ⟨h1, h2, -, h4⟩ := hy
  refine Prod.ext ?_ ?_
  · show (List.ofFn fun t : Fin lg => writeE (readE (y.1.getD t.val zeroE))) = y.1
    refine List.ext_getElem (by rw [List.length_ofFn, hl]) fun n a b => ?_
    rw [List.getElem_ofFn, List.getD_eq_getElem _ _ b]
    exact writeE_readE _ (h1 _ (List.getElem_mem b))
  · show writeE (seedOf1C lg y).2.val = y.2
    unfold seedOf1C
    rw [dif_neg h4]
    exact writeE_readE _ h2

/-- **The way back**: a list of s seeds, each with lg coordinates and in order, read into a value
and written back, is the list. -/
theorem seedsL_seedOfC (lg s : ℕ) (l : List (List OnBytes.E × OnBytes.E)) (hn : l.length = s)
    (hl : ∀ y ∈ l, y.1.length = lg) (hok : ∀ y ∈ l, SeedOK y) : seedsL (seedOfC lg s l) = l := by
  unfold seedsL
  refine List.ext_getElem (by rw [List.length_ofFn, hn]) fun n a b => ?_
  rw [List.getElem_ofFn]
  show ((List.ofFn fun t : Fin lg => writeE ((seedOf1C lg (l.getD n ([], oneE))).1 t),
    writeE (seedOf1C lg (l.getD n ([], oneE))).2.val) : List OnBytes.E × OnBytes.E) = l[n]
  rw [List.getD_eq_getElem _ _ b]
  exact seedL1_back lg _ (hl _ (List.getElem_mem b)) (hok _ (List.getElem_mem b))

/-- What the text of `recordSeeds` gives, at every plain hash, has `count` seeds of `bits`
coordinates each. -/
theorem recordSeedsW_sizes (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → Id ByteArray)
    (name : ByteArray) (bits count : ℕ) (l : List (List OnBytes.E × OnBytes.E))
    (hl : recordSeedsW (m := Id) h .two name bits count = some l) :
    l.length = count ∧ ∀ y ∈ l, y.1.length = bits := by
  rw [recordSeedsW_pure] at hl
  obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.1 hl
  rw [timesT_eq]
  refine ⟨by rw [List.length_map, times_length], fun y hy => ?_⟩
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hy
  rw [List.length_map]
  exact times_all (Fmt.drawSeed .two bits) (fun t => t.1.length = bits) _
    (fun c => times_length _ (Fmt.drawE .two) bits c) count 0 t ht

/-- So has what the program's `recordSeeds` gives. -/
theorem recordSeeds_sizes (name : ByteArray) (bits count : ℕ) (l : List (List OnBytes.E × OnBytes.E))
    (hl : recordSeeds .two name bits count = some l) :
    l.length = count ∧ ∀ y ∈ l, y.1.length = bits :=
  recordSeedsW_sizes Fmt.formatHash name bits count l ((recordSeedsW_H .two name bits count).trans hl)

/-- **The seeds that the program draws come back as they were.** -/
theorem seedsL_of_drawn (name : ByteArray) (lg s : ℕ) (l : List (List OnBytes.E × OnBytes.E))
    (hl : recordSeeds .two name lg s = some l) : seedsL (seedOfC lg s l) = l :=
  seedsL_seedOfC lg s l (recordSeeds_sizes name lg s l hl).1 (recordSeeds_sizes name lg s l hl).2
    (seedOK_recordSeeds name lg s l hl)

end TypedOracleCompiler.Slice

#print axioms TypedOracleCompiler.Slice.seedsL_seedOfC
#print axioms TypedOracleCompiler.Slice.recordSeeds_sizes
#print axioms TypedOracleCompiler.Slice.seedsL_of_drawn
