-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/SameReadSig.lean: THREE OF THE PROMISE's CLAUSES ON THE READING OF THE ORACLES, AND
THE PIN, AT THE LIBRARY's OWN NOTIONS, HOLD AT A STATEMENT y EXACTLY IF AT A STATEMENT x, WHEREVER
`SameRead base x y` (RidesBack.lean): "the record holds the sample" (`smpHeld`,
Johnson/Desc/SmpRows.lean) at every seat; "every leaf is shown" (`shownJT`), "no collision"
(`noCollJT`) and "the tenant is pinned" (`pinJT`, Johnson/Desc/Sound/MeaningSig.lean) AT A SEAT IN A
TREE WHOSE NUMBER IS BELOW base. GENERAL IN THE BLOCK: no block, no kind and no yes stands in a
statement. Statements and proofs, by unfolding.

  `col_same`: a tree below base has the same columns at y as at x (`colAt` goes through `posL`, of
    whose finds `SameRead.trees` speaks). `word_same`: so each of its tenants has the same committed
    word.
  `shownAt_iff` (`shownAt_same`: its way from x to y), `wordsOf_same`: so, for a member whose seat
    lies in such a tree, "every leaf shows its symbol" and the member's word (`ShownAt`, `wordsOf`,
    MsgSig.lean) are the same.
  `cell_same`: the stored table has the same symbols at y as at x.
  **`held_same`**: `smpHeld` reads the record's st and book alone: the same Bool at y as at x, at
    every (j, t).
  **`shown_iff`** (`shown_same`: its way from x to y): j < base: `shownJT cs G ms j t` at y's
    strings exactly if at x's.
  **`noColl_iff`** (`noColl_same`), **`pin_iff`**: j < base, AND smp GIVES ONE THING AT THE TWO
    RECORDS (hs: a premise: smp is a letter on the record): `noCollJT cs G smp ms j t`, and
    `pinJT cs G arr smp ms j t` at every witness, at y exactly if at x.

Limits. AT A TREE AT OR ABOVE base NOTHING IS SAID: `SameRead` says nothing of it. hs is paid
nowhere here. That two statements of a chain stand in `SameRead` is `sameRead_of_yes`'s, at K4's
piece alone. Nothing on soundness.
-/
import Johnson.Road.K4.RidesBack
import Johnson.Desc.Sound.MeaningSig
import Johnson.Desc.SmpRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes.Maker
open VerifiableInference.Desc (FileDescription Strs Wit wordOf smpHeld)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Frame strsOf colAt cellAt Sending Mem ShownAt wordsOf wordAt
CfAt
  SitsAt shownJT noCollJT pinJT MsgT)
open Johnson.Pack (sigOf)

variable {Fr : Frame} {base : ℕ} {x y : S × Fr.E.Str}

/-- A tree below base has the same columns. -/
theorem col_same (h : SameRead base x y) {j : ℕ} (hj : j < base) (l : ℕ) :
    (strsOf Fr y.2).col j l = (strsOf Fr x.2).col j l := by
  show colAt Fr y.2 j l = colAt Fr x.2 j l
  unfold colAt
  cases hq : posL Fr.all j l with
  | none => rfl
  | some q =>
    simp only [Option.map_some, Option.getD_some]
    exact h.trees j l q hq hj

/-- The stored table has the same symbols. -/
theorem cell_same (h : SameRead base x y) : (strsOf Fr y.2).cell = (strsOf Fr x.2).cell := by
  show cellAt Fr y.2 = cellAt Fr x.2
  unfold cellAt
  rw [h.table]

variable {Xi : Type} (G : FileDescription Xi)

/-- Each tenant of a tree below base has the same committed word. -/
theorem word_same (h : SameRead base x y) {j : ℕ} (hj : j < base) (t l : ℕ) :
    wordOf G (strsOf Fr y.2) j t l = wordOf G (strsOf Fr x.2) j t l := by
  unfold wordOf
  rw [col_same h hj]

variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ)

/-- "Every leaf shows its symbol", for a member that sits in a tree below base: at y exactly if at
x. -/
theorem shownAt_iff (h : SameRead base x y) (i : Fin l.length) (hj : (seat i).1 < base) :
    ShownAt G cs l seat (strsOf Fr y.2) i ↔ ShownAt G cs l seat (strsOf Fr x.2) i := by
  constructor
  · intro hy k hk
    rw [← word_same G h hj]
    exact hy k hk
  · intro hx k hk
    rw [word_same G h hj]
    exact hx k hk

/-- From x to y. -/
theorem shownAt_same (h : SameRead base x y) (i : Fin l.length) (hj : (seat i).1 < base)
    (hx : ShownAt G cs l seat (strsOf Fr x.2) i) : ShownAt G cs l seat (strsOf Fr y.2) i :=
  (shownAt_iff G cs l seat h i hj).mpr hx

/-- The word of a member that sits in a tree below base. -/
theorem wordsOf_same (h : SameRead base x y) (i : Fin l.length) (hj : (seat i).1 < base) :
    wordsOf G cs l seat (strsOf Fr y.2) i = wordsOf G cs l seat (strsOf Fr x.2) i := by
  unfold wordsOf
  funext p
  cases p with
  | inl k =>
    funext r
    simp only [wordAt, word_same G h hj]
  | inr k =>
    funext r
    simp only [wordAt, word_same G h hj]

/-- **"The record holds the sample" is the same Bool.** -/
theorem held_same (h : SameRead base x y) (j t : ℕ) :
    smpHeld y.1.st y.1.book j t = smpHeld x.1.st x.1.book j t := by
  rw [h.rest.st, h.rest.book]

/-- A member that sits at (j, t), j below base, sits in a tree below base. -/
theorem sits_below {m : Mem} {j t : ℕ} (hs : SitsAt m j t) (hj : j < base) :
    (m.1.seat m.2).1 < base := by
  have e' : m.1.seat m.2 = (j, t) := hs
  rw [e']
  exact hj

/-- **"Every leaf is shown", at a seat in a tree below base: at y exactly if at x.** -/
theorem shown_iff (ms : List Mem) (h : SameRead base x y) {j : ℕ} (hj : j < base) (t : ℕ) :
    shownJT cs G ms j t (strsOf Fr y.2) ↔ shownJT cs G ms j t (strsOf Fr x.2) :=
  ⟨fun hy => ⟨hy.1, fun m hm hs =>
      (shownAt_iff G cs m.1.l m.1.seat h m.2 (sits_below hs hj)).mp (hy.2 m hm hs)⟩,
    fun hx => ⟨hx.1, fun m hm hs =>
      (shownAt_iff G cs m.1.l m.1.seat h m.2 (sits_below hs hj)).mpr (hx.2 m hm hs)⟩⟩

/-- From x to y. -/
theorem shown_same (ms : List Mem) (h : SameRead base x y) {j : ℕ} (hj : j < base) (t : ℕ)
    (hx : shownJT cs G ms j t (strsOf Fr x.2)) : shownJT cs G ms j t (strsOf Fr y.2) :=
  (shown_iff G cs ms h hj t).mpr hx

variable {P : Type}
  (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)

/-- **"No collision", at a seat in a tree below base, if smp gives one thing at the two records: at
y exactly if at x.** -/
theorem noColl_iff (ms : List Mem) (Z : P) (h : SameRead base x y)
    (hs : ∀ s i, smp (Z, y.1) s i = smp (Z, x.1) s i) {j : ℕ} (hj : j < base) (t : ℕ) :
    noCollJT cs G smp ms j t (Z, y.1) (strsOf Fr y.2) ↔
      noCollJT cs G smp ms j t (Z, x.1) (strsOf Fr x.2) := by
  constructor
  · intro hy m hm hsit
    have e := sits_below hsit hj
    obtain ⟨z, hz, hsh, hc⟩ := hy m hm hsit
    refine ⟨z, (hs m.1 m.2).symm.trans hz, (shownAt_iff G cs m.1.l m.1.seat h m.2 e).mp hsh, ?_⟩
    rw [← wordsOf_same G cs m.1.l m.1.seat h m.2 e]
    exact hc
  · intro hx m hm hsit
    have e := sits_below hsit hj
    obtain ⟨z, hz, hsh, hc⟩ := hx m hm hsit
    refine ⟨z, (hs m.1 m.2).trans hz, (shownAt_iff G cs m.1.l m.1.seat h m.2 e).mpr hsh, ?_⟩
    rw [wordsOf_same G cs m.1.l m.1.seat h m.2 e]
    exact hc

/-- From x to y. -/
theorem noColl_same (ms : List Mem) (Z : P) (h : SameRead base x y)
    (hs : ∀ s i, smp (Z, y.1) s i = smp (Z, x.1) s i) {j : ℕ} (hj : j < base) (t : ℕ)
    (hx : noCollJT cs G smp ms j t (Z, x.1) (strsOf Fr x.2)) :
    noCollJT cs G smp ms j t (Z, y.1) (strsOf Fr y.2) :=
  (noColl_iff G cs smp ms Z h hs hj t).mpr hx

/-- **"The tenant is pinned" (`pinJT`), at a seat in a tree below base, if smp gives one thing at
the
two records: at y exactly if at x, at every witness.** -/
theorem pin_iff {Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (ms : List Mem) (Z : P)
    (h : SameRead base x y) (hs : ∀ s i, smp (Z, y.1) s i = smp (Z, x.1) s i) {j : ℕ}
    (hj : j < base) (t : ℕ) (w : Wit Cells Tok MsgT) :
    pinJT cs G arr smp ms j t (Z, y.1) (strsOf Fr y.2) w ↔
      pinJT cs G arr smp ms j t (Z, x.1) (strsOf Fr x.2) w := by
  constructor
  · intro hy
    refine ⟨hy.1, fun m hm hsit => ?_⟩
    have e := sits_below hsit hj
    obtain ⟨z, hz, hsh, hd⟩ := hy.2 m hm hsit
    refine ⟨z, (hs m.1 m.2).symm.trans hz, (shownAt_iff G cs m.1.l m.1.seat h m.2 e).mp hsh, ?_⟩
    rw [← wordsOf_same G cs m.1.l m.1.seat h m.2 e]
    exact hd
  · intro hx
    refine ⟨hx.1, fun m hm hsit => ?_⟩
    have e := sits_below hsit hj
    obtain ⟨z, hz, hsh, hd⟩ := hx.2 m hm hsit
    refine ⟨z, (hs m.1 m.2).trans hz, (shownAt_iff G cs m.1.l m.1.seat h m.2 e).mpr hsh, ?_⟩
    rw [wordsOf_same G cs m.1.l m.1.seat h m.2 e]
    exact hd

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.held_same
#print axioms OnBytes.Road.K4.shown_same
#print axioms OnBytes.Road.K4.noColl_same
#print axioms OnBytes.Road.K4.pin_iff
