-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/DecoderRec.lean: one decoder of a stored table WITH A RECORD, and three languages on
raw strings and records.

NOTHING IS SHOWN IN THIS FILE. Definitions, and one lemma of logic.

Why. `Sz.dcd` (OnBytes/Slice/LinkAt.lean) decodes a stored table at the empty sample map:
the nearest table of code words within a radius; below half the code's
distance there is at most one. At a larger radius (up to Johnson's bound) a LIST of tables of code
words can lie within it (`coll` counts their message parts: two tables that part in the tails alone
count as one). The format then stores a RECORD with the table: for each row its answers to a sample
whose seed follows from the table's name by the hash. The library's decoder of an encoded index
takes such a record (`Cb.LdIx.dec`); `Sz.dcd` uses it at `Sample.nil`. This file uses it at a
sample map Z.

Main definitions.
 `DecR` `Dec`, the sample map Z of one row, and the number of entries of a row's message before its
     pads.
 `DecR.Rec` a record: a seed, and the answers of every row.
 `DecR.dcd`, `dcdRaw` the decoder on a table, on a raw string: of all tables of full messages that
     have the record's answers at its seed the nearest, if it is within the radius.
 `DecR.coll`, `collRaw` THE RECORD DOES NOT SINGLE ONE OUT: at the seed two members of the table's
     list with different message parts have the same answers (the library's `LdIx.Coll`). It depends
     on table and seed, not on the answers.
 `DecR.Agree` two decoded tables agree in every entry before the pads.
 `DecR.Claims` what the statements read of a decoded table: data, with one law: the
     matrix reads no pad.
 `DecR.Way`, `wayColl`, `wayNone` a way out of the entry's and the proof's languages. TWO
     FORMS, BOTH NAMED; the languages and the path take either.
 `DecR.LangK`, `LangE`, `LangP` the three languages. The first table and its copy have each a record
     of its own, AND PADS OF ITS OWN: the entry's language compares the two decoded tables before
     the pads alone (a copy is made under fresh coins; the program's entry claims no more).
Main theorem: `DecR.path`.

The two forms. `wayColl`: the entry's and the proof's languages let a string pass whose record
does not single one table out; the key's language shuts that for the first table, the entry's for
the copy. The rare event "a seed at which the record does not single one table out" is then paid
once a table. `wayNone`: no way out; each part whose soundness needs it pays for that event itself.
Which is right depends on how the three protocols' soundness is shown at that radius: not known; the
library's count for the fold has the first's shape ("a table without a collision at the record's
seed"). A THIRD (written as a form in OnBytes/Slice/JoinDecRec2.lean): every language has the way
out for each table that it touches, and that both ways out are shut comes from the verifier's yes
outside ONE rare event over the one oracle; then no part speaks of where a seed comes from; its
price: the join's `Good` must see the second raw string too.

What is not claimed. NO PROTOCOL IS SHOWN SOUND FOR ANY OF THESE LANGUAGES, at any radius. (For a
wider language than `LangE`, in which the copy's way out is open too, the link of an entry file is
shown sound at two sizes, under a statement on codes that is taken as given: `fr_family`,
`sr_family`, OnBytes/Slice/LinkFamily.lean, for `Sz.LangE2T`; that is `LangE2` of
OnBytes/Slice/JoinDecRec2.lean at `wayColl`, at the raw forms of the two tables: `Sz.langE2T_iff`,
OnBytes/Slice/LinkSoundRec.lean.) No condition on the radius is written. Of proof of work nothing is
said: it would stand in the checkers and in the parts'
bounds, which are variables. By a reading of the program's text the chain on which a record's seeds
are drawn has none, whatever the parameter file says (the call is written with work 0): whoever
tries many roots for a seed at which a record does not single one table out pays one try a root,
without a factor for work. Z is a variable: the format's sample is not written here (by a reading of
the program's text it is the library's `Sample.padPow`: for each answer a point of the cube and a
factor other than 0; the equality kernel at the point on a row's entries, the factor on that
answer's three pad entries). That the seed in a record is the hash's answer at the table's name is
said nowhere in this file: a record is any pair. At `wayColl` the key's part, and the entry's for
the copy, can have a bound below 1 only if its checker reads the seed from the oracle at the table's
name; its bound then holds one try for each name that the maker asks. That collisions are rare: not
shown in this file (the library has lemmas on `Coll`; none is used). OnBytes/Slice/RecordColl.lean
counts the seeds with a collision, for one table (`coll_count`); OnBytes/Flat/EntryRecord.lean has a
probability over uniform blocks at two sizes (`entryFull_seedLaw`, `entrySmall_seedLaw`), with the
limits that its head names. With `Claims` whose `inRange` and `Rel` always hold the key's language
says "decodes" and the proof's nothing. That `cut` is where the format's pads begin: not asked. A
raw string that has not exactly 2^a symbols does not decode.

-/
import OnBytes.Slice.Decoder

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood

/-! ## The decoder with a record -/

/-- **What a decoder of a stored table with a record is made of.** The three data of `Dec` (the
table's code, the number of row variables, the radius in columns) and Z: the sample map of one row:
its seeds, the names of its answers, and the matrix that a seed gives. cut: the number of entries of
a row's message before its pads. -/
structure DecR extends Dec where
  /-- the sample map of one row -/
  Z : Sample GE (Fin T.l)
  /-- the number of entries of a row's message before its pads -/
  cut : ℕ

namespace DecR
variable (D : DecR)

/-- The format of a stored table with a record: as `Sz.ix`, with the sample map Z in the place of
`Sample.nil`. -/
@[reducible] noncomputable def ix : LdIx GE D.toDec.Pos D.toDec.Co D.toDec.En where
  v := D.v
  G := genOf D.T
  pl := fun j => Fin.natAdd D.T.r j
  Z := D.Z
  eM := D.eM
  rank := fun M => (Fintype.equivFin _ M).val

/-- **A record**: a seed, and the answers of every row (the library's `LdIx.Rec`). -/
abbrev Rec : Type := D.ix.Rec

/-- A stored table as a table over the extension field. -/
def tab (f : D.toDec.Pos → Run.PQ.SgX) : D.ix.Row → D.toDec.Pos → GE :=
  fun r j => D.toDec.up (f j) r

/-- **The decoder** (the library's `LdIx.dec`, a constrained minimum): of ALL tables of full
messages whose message parts have the record's answers at the record's seed, the one whose code
words are nearest to the table, ties broken by a fixed order (`ix.rank`); its message parts, if it
is within eM columns; else nothing. Beyond half the code's distance several tables of code words can
lie within eM columns; whether the record tells them apart: `coll`. -/
noncomputable def dcd (f : D.toDec.Pos → Run.PQ.SgX) (rec : D.Rec) :
    Option (D.ix.Row × D.toDec.En → GE) :=
  D.ix.dec (D.tab f) rec

/-- **The record does not single one out**: at the seed ρ two members of the table's list WITH
DIFFERENT MESSAGE PARTS (pads counted in; two that part in the random tails alone count as one) have
the same answers (the library's `LdIx.Coll`). It depends on the table and the seed, not on the
answers. -/
def coll (f : D.toDec.Pos → Run.PQ.SgX) (ρ : D.Z.D) : Prop := D.ix.Coll (D.tab f) ρ

open Classical in
/-- The decoder on a raw string: nothing, unless the string has exactly 2^a symbols. -/
noncomputable def dcdRaw (f : Raw Run.PQ.SgX) (rec : D.Rec) :
    Option (D.ix.Row × D.toDec.En → GE) :=
  if Raw.HasLen f (2 ^ D.T.a) then D.dcd (fun p => (f p.val).getD (0, [])) rec else none

/-- `coll` on a raw string: false, unless the string has exactly 2^a symbols. -/
def collRaw (f : Raw Run.PQ.SgX) (ρ : D.Z.D) : Prop :=
  Raw.HasLen f (2 ^ D.T.a) ∧ D.coll (fun p => (f p.val).getD (0, [])) ρ

/-- **Two decoded tables agree before the pads**: in every row, at every entry before the cut. -/
def Agree (u u' : D.ix.Row × D.toDec.En → GE) : Prop :=
  ∀ r (j : D.toDec.En), j.val < D.cut → u (r, j) = u' (r, j)

/-- **What a key's and a proof's statements read of a decoded table**, for instances in X. Data,
with one law: THE MATRIX READS NO PAD. -/
structure Claims (X : Type) where
  /-- the matrices -/
  Mat : Type
  /-- the matrix of a decoded table -/
  mat : (D.ix.Row × D.toDec.En → GE) → Mat
  /-- its entries are in range -/
  inRange : Mat → Prop
  /-- the claim of an instance on the matrix -/
  Rel : Mat → X → Prop
  /-- the matrix reads no pad -/
  mat_cut : ∀ u u', D.Agree u u' → mat u = mat u'

/-! ## The three languages, with a way out as a parameter, and the path through them -/

variable {D} {X : Type}

/-- A way out of the entry's and the proof's languages, which the key's language closes: a property
of a raw string and a seed. TWO FORMS: `collRaw` (`wayColl`) and "never" (`wayNone`). -/
abbrev Way (D : DecR) : Type := Raw Run.PQ.SgX → D.Z.D → Prop

/-- FIRST FORM: the entry's and the proof's languages let a string pass whose record does not
single one table out; the key's language, and the entry's for the copy, say that it does. Then the
rare event "a seed at which the record does not single one table out" is paid ONCE for each table:
in the key's bound for the first, in the entry's for the copy. -/
def wayColl (D : DecR) : Way D := D.collRaw

/-- SECOND FORM: no way out. The decoder is a function in any case (the nearest, then a fixed
order), so the languages are well formed; each part whose soundness needs that the record singles
one table out pays for that event in its own bound. -/
def wayNone (D : DecR) : Way D := fun _ _ => False

/-- The key's language: with its record the string decodes, the way out is shut, and the matrix is
in range. -/
def LangK (A : D.Claims X) (w : Way D) (rec : D.Rec) (y : Raw Run.PQ.SgX) : Prop :=
  ∃ u, D.dcdRaw y rec = some u ∧ ¬ w y rec.1 ∧ A.inRange (A.mat u)

/-- The entry's language: the first string with its record does not decode, or its way out is open,
or the second string with ITS OWN record decodes, to a table that AGREES WITH THE FIRST's BEFORE THE
PADS, and its way out is shut. A copy is made under fresh coins: its pads are its own. -/
def LangE (w : Way D) (rec₀ rec₁ : D.Rec) (y₀ y₁ : Raw Run.PQ.SgX) : Prop :=
  D.dcdRaw y₀ rec₀ = none ∨ w y₀ rec₀.1 ∨
    ∃ u₀ u₁, D.dcdRaw y₀ rec₀ = some u₀ ∧ D.dcdRaw y₁ rec₁ = some u₁ ∧ D.Agree u₁ u₀ ∧
      ¬ w y₁ rec₁.1

/-- The proof's language: the string with its record does not decode, or its way out is open, or
the claim of x holds of its matrix. -/
def LangP (A : D.Claims X) (w : Way D) (x : X) (rec : D.Rec) (y : Raw Run.PQ.SgX) : Prop :=
  D.dcdRaw y rec = none ∨ w y rec.1 ∨ ∃ u, D.dcdRaw y rec = some u ∧ A.Rel (A.mat u) x

/-- **The path**, for either way out. If the first string with the record rec₀ is in the key's
language, the pair with rec₀ and rec₁ in the entry's, and x with the second string and rec₁ in the
proof's, then the first string with rec₀ decodes, its matrix is in range, and the claim of x holds
of that matrix. ONE record rec₀ stands in the first two hypotheses and ONE record rec₁ in the last
two. -/
theorem path (A : D.Claims X) (w : Way D) {rec₀ rec₁ : D.Rec} {y₀ y₁ : Raw Run.PQ.SgX} {x : X}
    (hK : LangK A w rec₀ y₀) (hE : LangE w rec₀ rec₁ y₀ y₁) (hP : LangP A w x rec₁ y₁) :
    ∃ u, D.dcdRaw y₀ rec₀ = some u ∧ A.inRange (A.mat u) ∧ A.Rel (A.mat u) x := by
  obtain ⟨u, hu, hw, hr⟩ := hK
  obtain ⟨u₁, h1, hag, hw1⟩ : ∃ u₁, D.dcdRaw y₁ rec₁ = some u₁ ∧ D.Agree u₁ u ∧ ¬ w y₁ rec₁.1 := by
    rcases hE with h | h | ⟨u₀, u₁, h0, h1, hag, h'⟩
    · rw [hu] at h
      cases h
    · exact absurd h hw
    · rw [hu] at h0
      cases h0
      exact ⟨u₁, h1, hag, h'⟩
  rcases hP with h | h | ⟨u', hu', hrel⟩
  · rw [h1] at h
    cases h
  · exact absurd h hw1
  · rw [h1] at hu'
    cases hu'
    rw [A.mat_cut u₁ u hag] at hrel
    exact ⟨u, hu, hr, hrel⟩

end DecR

end OnBytes.Slice
