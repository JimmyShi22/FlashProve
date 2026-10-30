-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SeedWords.lean: the seeds of a stored table's record, as the program has them, have
words below the prime, and their factors are not 0: neither in their words nor in the field.

WHY. The program tests "no seed's factor is 0" by comparing WORDS with 0 (`isZeroE`,
OnBytes/Field/Ext.lean). A coordinate whose word spells the prime itself is read as 0 in the field
and passes that test. On words below the prime the two agree (`isZeroE_iff`,
OnBytes/Slice/ProgField.lean). Here: drawn seeds have such words.

HOW. The library's `drawTie_read` (Run/DrawTieProofs.lean) says that what a draw of the format gives
is the view of a typed value: for an element, `toU3` of three numbers below p; for an element that
is not 0, of three that are not all 0. `okE_toU3` (OnBytes/Slice/Draws.lean) says that such words
are below p.

Main definition.
 `SeedOK y`             a seed of the program is in order: the words of each coordinate of its point
                        and of its factor are below p; the factor is not 0 in its words, and not 0
                        in the field.
Main theorems.
 `drawE_toU3`, `drawNZ_toU3`   what `Fmt.drawE` and `Fmt.drawNZ` give, in the second field, at every
                        row of words and every place.
 `okE_drawE`, `good_drawNZ`   a drawn element has words below p; a drawn factor too, and it is not 0
                        in either sense.
 `seedOK_drawSeed`      a seed that `Fmt.drawSeed` gives is in order. With `times_all`.
 `seedOK_recordSeedsW`, `seedOK_recordSeeds`   EVERY SEED THAT THE TEXT OF `recordSeeds` GIVES IS IN
                        ORDER, at every plain hash; so every seed that the program's `recordSeeds`
                        gives.

What is not claimed. The field is the second. Seeds that stand in a file or in a key and were not
drawn: nothing. How the seeds are distributed (OnBytes/Slice/SeedBias.lean). That there are as many
seeds as asked, or that a point has as many coordinates (`times_length`, `seed_points`,
OnBytes/Slice/SeedTie.lean). Nothing on any hash function.

-/
import OnBytes.Slice.SeedTie
import OnBytes.Slice.Draws

set_option autoImplicit false

namespace OnBytes.Slice
open _root_.Iop _root_.Run

/-! ## What a draw of an element gives -/

/-- What the format's draw of an element gives is the triple of words of three numbers below p. -/
theorem drawE_toU3 (row : Fmt.Row) (c : ℕ) : ∃ e : EV .two, (Fmt.drawE .two row c).1 = toU3 e :=
  ⟨_, Fmt.Val.ext.inj (congrArg Prod.fst (drawTie_read .two .elem row c))⟩

/-- What the format's draw of an element that is not 0 gives is the triple of words of three numbers
below p that are not all 0. -/
theorem drawNZ_toU3 (row : Fmt.Row) (c : ℕ) :
    ∃ e : Run.NZ .two, (Fmt.drawNZ .two row c).1 = toU3 e.1 :=
  ⟨_, Fmt.Val.ext.inj (congrArg Prod.fst (drawTie_read .two .elemNZ row c))⟩

/-- **A drawn element, as the program has it, has words below p.** -/
theorem okE_drawE (row : Fmt.Row) (c : ℕ) : okE (E.ofTriple (Fmt.drawE .two row c).1) = true := by
  obtain ⟨e, he⟩ := drawE_toU3 row c
  rw [okE_triple, E.triple_ofTriple, he]
  exact okE_toU3 e

/-- **A drawn factor, as the program has it, has words below p, and it is not 0: neither in its
words nor in the field.** -/
theorem good_drawNZ (row : Fmt.Row) (c : ℕ) :
    okE (E.ofTriple (Fmt.drawNZ .two row c).1) = true ∧
      isZeroE (E.ofTriple (Fmt.drawNZ .two row c).1) = false ∧
      readE (E.ofTriple (Fmt.drawNZ .two row c).1) ≠ 0 := by
  obtain ⟨e, he⟩ := drawNZ_toU3 row c
  have hok : okE (E.ofTriple (Fmt.drawNZ .two row c).1) = true := by
    rw [okE_triple, E.triple_ofTriple, he]
    exact okE_toU3 e.1
  have hne : readE (E.ofTriple (Fmt.drawNZ .two row c).1) ≠ 0 := by
    rw [readE_ofTriple, he, toE_toU3, ← eE_zero]
    exact fun h => e.2 (eE.injective h)
  refine ⟨hok, ?_, hne⟩
  cases hz : isZeroE (E.ofTriple (Fmt.drawNZ .two row c).1) with
  | false => rfl
  | true => exact absurd ((isZeroE_iff _ hok).1 hz) hne

/-! ## Seeds -/

/-- **A seed of the program is in order**: the words of each coordinate of its point and of its
factor are below p, and the factor is not 0, neither in its words (`isZeroE`) nor in the field (the
last follows from the two before it; kept for callers). -/
def SeedOK (y : List E × E) : Prop :=
  (∀ x ∈ y.1, okE x = true) ∧ okE y.2 = true ∧ isZeroE y.2 = false ∧ readE y.2 ≠ 0

/-- What holds of every value of a draw holds of every member of "the draw, n times". -/
theorem times_all {α : Type} (x : Fmt.Dr α) (P : α → Prop) (row : Fmt.Row)
    (h : ∀ c, P (x row c).1) : ∀ (n c : ℕ), ∀ a ∈ ((x.times n) row c).1, P a
  | 0, _, _, ha => absurd ha List.not_mem_nil
  | n + 1, c, a, ha => by
    have ha' : a ∈ (x row c).1 :: ((x.times n) row (x row c).2).1 := ha
    rcases List.mem_cons.1 ha' with rfl | h2
    · exact h c
    · exact times_all x P row h n _ a h2

/-- **A drawn seed, as the program has it, is in order.** -/
theorem seedOK_drawSeed (lg : ℕ) (row : Fmt.Row) (c : ℕ) :
    SeedOK (((Fmt.drawSeed .two lg row c).1.1).map E.ofTriple,
      E.ofTriple (Fmt.drawSeed .two lg row c).1.2) := by
  refine ⟨fun x hx => ?_, good_drawNZ row _⟩
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
  exact times_all (Fmt.drawE .two) (fun t => okE (E.ofTriple t) = true) row (okE_drawE row) lg c t
    ht

/-- **Every seed that the text of `recordSeeds` gives is in order, at every plain hash.** The hash
is a variable. -/
theorem seedOK_recordSeedsW (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → Id ByteArray)
    (name : ByteArray) (bits count : ℕ) (l : List (List E × E))
    (hl : recordSeedsW (m := Id) h .two name bits count = some l) : ∀ y ∈ l, SeedOK y := by
  rw [recordSeedsW_pure] at hl
  obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.1 hl
  intro y hy
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hy
  rw [timesT_eq] at ht
  exact times_all (Fmt.drawSeed .two bits)
    (fun t => SeedOK (t.1.map E.ofTriple, E.ofTriple t.2)) _
    (fun c => seedOK_drawSeed bits _ c) count 0 t ht

/-- **Every seed that the program's `recordSeeds` gives is in order.** -/
theorem seedOK_recordSeeds (name : ByteArray) (bits count : ℕ) (l : List (List E × E))
    (hl : recordSeeds .two name bits count = some l) : ∀ y ∈ l, SeedOK y :=
  seedOK_recordSeedsW Fmt.formatHash name bits count l ((recordSeedsW_H .two name bits count).trans hl)

end OnBytes.Slice

#print axioms OnBytes.Slice.drawE_toU3
#print axioms OnBytes.Slice.drawNZ_toU3
#print axioms OnBytes.Slice.okE_drawE
#print axioms OnBytes.Slice.good_drawNZ
#print axioms OnBytes.Slice.times_all
#print axioms OnBytes.Slice.seedOK_drawSeed
#print axioms OnBytes.Slice.seedOK_recordSeedsW
#print axioms OnBytes.Slice.seedOK_recordSeeds
