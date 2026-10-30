-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/FastLaw/Read.lean: the honest side of the kind "lookup" (K3). Small
facts by which a list of the program's elements is shown to be a list of elements of the library's
field, laid into words. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: `up` reads one of the program's elements in the
library's field; it abbreviates `readE`. `down` lays an element of the library's field into words,
that is, into one of the program's elements; `downs` does so for a list (all three in
Honest/K3/JobsSpec.lean).

What is shown.
  `ok_add`, `ok_sub`, `ok_mul`, `ok_fold`, `ok_zero`, `ok_one`, `ok_down`: the results of these
    operations have words below the prime, whatever the arguments' words are.
  `down_up`: an element with words below the prime, read and laid back into words, is itself.
  `eq_downs`, the closing lemma: a list whose entries have words below the prime, and which reads
    as L, is L laid into words.
  `tab_size`, `tab_getD`, `readV_tab`: of a table made by a rule: its size, its entries, its
    reading.

Hypotheses that remain.
  `h`: in `down_up`: the element's words are below the prime; in `eq_downs`: the list reads as L; in
    `tab_getD` and `readV_tab`: i < n.
  `hok`: (in `eq_downs`) the entries' words are below the prime.

Users. Two fillings of a lookup's summands are to be shown equal: one computes on the program's
elements (Honest/K3/JobsFast.lean); the other computes in the library's field and lays the result
into words (JobsSpec.lean, by `down`). Every lemma on the first is stated in two halves: what its
list is when read in the field, and that its entries' words are below the prime. `eq_downs` joins
the two halves. The files Levels.lean and Round.lean of Honest/K3/FastLaw/ import this file.

Limits. No statement of this file speaks of a lookup.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.JobsSpecPoints
import Johnson.Desc.ProofFile.Honest.K3.JobsFast

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.FastLaw
open OnBytes (E addE subE mulE zeroE oneE foldPairE okE)
open OnBytes.Slice (readE readV)

theorem ok_add (a b : E) : okE (addE a b) = true := by
  rw [OnBytes.okE_triple, OnBytes.addE_triple]
  simp only [Fmt.Fld.okE, Fmt.Fld.addE, Fmt.Fld.ok_add, Bool.and_self]

theorem ok_sub (a b : E) : okE (subE a b) = true := by
  rw [OnBytes.okE_triple, OnBytes.subE_triple]
  simp only [Fmt.Fld.okE, Fmt.Fld.subE, Fmt.Fld.ok_sub, Bool.and_self]

theorem ok_mul (a b : E) : okE (mulE a b) = true := by
  rw [OnBytes.okE_triple, OnBytes.mulE_triple]
  simp only [Fmt.Fld.okE, Fmt.Fld.mulE, Fmt.Fld.ok_add, Bool.and_self]

theorem ok_fold (a b g : E) : okE (foldPairE a b g) = true := by
  rw [OnBytes.foldPairE_def]
  exact ok_add _ _

theorem ok_zero : okE zeroE = true := rfl

theorem ok_one : okE oneE = true := rfl

theorem ok_down (x : KE) : okE (down x) = true := by
  unfold down
  rw [OnBytes.okE_triple, OnBytes.E.triple_ofTriple]
  simp only [Fmt.Fld.okE, OnBytes.Slice.ofE, OnBytes.Slice.ok_ofF, Bool.and_self]

/-- An element with words below the prime, read and laid back, is itself. -/
theorem down_up (x : E) (h : okE x = true) : down (up x) = x :=
  OnBytes.Slice.readE_inj _ _ (ok_down _) h (up_down _)

/-- **The closing lemma.** A list whose entries have words below the prime, and which reads as L, is
L laid into words. -/
theorem eq_downs {l : List E} {L : List KE} (hok : ∀ x ∈ l, okE x = true) (h : l.map readE = L) :
    l = downs L := by
  subst h
  unfold downs
  rw [List.map_map]
  conv_lhs => rw [← List.map_id l]
  exact List.map_congr_left fun x hx => (down_up x (hok x hx)).symm

/-- A table made by a rule has as many entries as asked. -/
theorem tab_size (n : Nat) (g : Nat → E) : ((Array.range n).map g).size = n := by
  simp

/-- The entry number i of such a table, for i below the size. -/
theorem tab_getD (n : Nat) (g : Nat → E) {i : Nat} (h : i < n) :
    ((Array.range n).map g).getD i zeroE = g i := by
  simp [Array.getD, h]

/-- The reading of that entry. -/
theorem readV_tab (n : Nat) (g : Nat → E) {i : Nat} (h : i < n) :
    readV ((Array.range n).map g) i = readE (g i) := by
  unfold OnBytes.Slice.readV
  rw [tab_getD n g h]

end ProofFile.Honest.K3.FastLaw

#print axioms ProofFile.Honest.K3.FastLaw.ok_add
#print axioms ProofFile.Honest.K3.FastLaw.ok_sub
#print axioms ProofFile.Honest.K3.FastLaw.ok_mul
#print axioms ProofFile.Honest.K3.FastLaw.ok_fold
#print axioms ProofFile.Honest.K3.FastLaw.ok_zero
#print axioms ProofFile.Honest.K3.FastLaw.ok_one
#print axioms ProofFile.Honest.K3.FastLaw.ok_down
#print axioms ProofFile.Honest.K3.FastLaw.down_up
#print axioms ProofFile.Honest.K3.FastLaw.eq_downs
#print axioms ProofFile.Honest.K3.FastLaw.tab_size
#print axioms ProofFile.Honest.K3.FastLaw.tab_getD
#print axioms ProofFile.Honest.K3.FastLaw.readV_tab
