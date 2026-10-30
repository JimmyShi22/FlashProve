-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/DecoderRecTyped.lean: the decoder with a record, and "the record does not single one
out", at the raw form of a typed string; and from the languages of a typed world, record by record
and with the way out, to the languages that the join takes.

WHY. The join (OnBytes/Slice/JoinDecRec.lean) speaks of raw strings: what each part reads off the
one log. A compiled part has an interface of its own: its strings are typed, of a length n and with
symbols in a type S that is matched with the shared symbols by u. Its interactive theorem is stated
record by record, for "the way out is open, or the language" (`LangK2`, `LangE2`,
OnBytes/Slice/JoinDecRec2.lean), the instance being the record, answers AND seeds; a second lane of
the compiled part says that the way out is shut. Here the two are put together.

Main definitions.
 `DecR.ofTyped u hn y`  a typed string of n = 2^a symbols as a stored table.
 `DecR.LgK`, `DecR.LgE`, `DecR.LgP`   the key's, the entry's and the proof's language of a typed
                        world: `LangK2`, `LangE2`, `LangP` at `wayColl`, at the raw forms; a record
                        is (answers, seeds), read by `an` and `sd`.
 `DecR.badK`            the test of a second lane, with the values true and false: at the seed the
                        record does not single one table out of the string's list.
Main theorems.
 `DecR.dcdRaw_rawOf`, `DecR.collRaw_rawOf`   on the raw form of a typed string of 2^a symbols
                        `dcdRaw` is `dcd` and `collRaw` is `coll`, at `ofTyped`. With `getD_rawOf`.
 `DecR.langK_of_typed`, `DecR.langK_of_lang_one`   FROM A TYPED WORLD TO THE JOIN'S LANGUAGE OF THE
                        KEY: `LgK` of record and string, and `badK` false of the string and the
                        record's seeds, give `LangK` at `wayColl`; the same from a list of one raw
                        string, in the form of the language of a part over the one oracle.
 `DecR.langE_of_typed`, `DecR.langE_of_lang_two`   the like for the entry: the test is false of the
                        COPY and its seeds.
 `DecR.badK_false`, `DecR.badK_iff`, `DecR.lgK_iff`, `DecR.lgE_iff`, `DecR.lgP_iff`   the test and
                        the three languages on tables.
 `DecR.badK_of_len`, `DecR.not_lgK_of_len`   at another length than 2^a the test is false of
                        everything and the key's language holds of nothing.
 `DecR.lgE_of_len`, `DecR.lgP_of_len`   BUT THE ENTRY'S AND THE PROOF'S LANGUAGE HOLD OF EVERYTHING
                        THERE (nothing decodes: `dcdRaw_of_len`): a statement with one of them as
                        its language is true for free at another length.

What is not claimed. NO PART, NO INTERFACE, NO JUDGE IS GIVEN HERE; a judge whose language has the
shape of the hypothesis of `langK_of_typed`: `judgeOff` (OnBytes/TypedOracleCompiler/Slice/JudgeOff.lean). A judge
on two strings: `judgeE` (OnBytes/TypedOracleCompiler/Slice/JudgeE.lean). n, S, u and the readers `an`, `sd` of
answers and seeds are variables. That an interactive theorem holds for `LgK`, `LgE` or `LgP`; that a
second lane holds for `badK`. `badK` is decided classically: no program computes it. The caller owes
both hypotheses at the string that its part reads AT THE END of a log and at the seed IN ITS
CHECKER'S RECORD. NOTHING ON SOUNDNESS IS SHOWN. Nothing on any hash function.

-/
import OnBytes.Slice.JoinDecRec2

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood

namespace DecR
variable (D : DecR) {n : ℕ} {S : Type} (u : S ≃ Run.PQ.SgX) (hn : n = 2 ^ D.T.a)

/-! ## The decoder and the collision at the raw form of a typed string -/

/-- A typed string of n = 2^a symbols as a stored table: its symbols read through u. -/
def ofTyped (y : Fin n → S) : D.toDec.Pos → Run.PQ.SgX := fun p => u (y (Fin.cast hn.symm p))

/-- What the decoder on raw strings reads of the raw form of a typed string is that table. -/
theorem getD_rawOf (y : Fin n → S) :
    (fun p : D.toDec.Pos => ((rawOf u y) p.val).getD (0, [])) = D.ofTyped u hn y := by
  funext p
  have hp : p.val < n := by
    rw [hn]
    exact p.isLt
  unfold rawOf ofTyped
  rw [dif_pos hp]
  rfl

/-- **On the raw form of a typed string of 2^a symbols the decoder on raw strings is the decoder.**
-/
theorem dcdRaw_rawOf (y : Fin n → S) (rec : D.Rec) :
    D.dcdRaw (rawOf u y) rec = D.dcd (D.ofTyped u hn y) rec := by
  unfold dcdRaw
  rw [if_pos (hn ▸ rawOf_hasLen u y), D.getD_rawOf u hn y]

/-- **And "the record does not single one out" on raw strings is that on tables.** -/
theorem collRaw_rawOf (y : Fin n → S) (ρ : D.Z.D) :
    D.collRaw (rawOf u y) ρ ↔ D.coll (D.ofTyped u hn y) ρ := by
  unfold collRaw
  rw [D.getD_rawOf u hn y]
  exact ⟨fun h => h.2, fun h => ⟨hn ▸ rawOf_hasLen u y, h⟩⟩

/-! ## The languages of a typed world, and what they give over the one oracle -/

variable {D} {X An Sd : Type} (an : An → D.ix.Row × D.Z.S → GE) (sd : Sd → D.Z.D)

/-- **The key's language of a typed world, record by record, with the way out**: the instance is the
record, answers and seeds; the string is typed. `LangK2` at `wayColl`, at the raw form of the
string. -/
def LgK (A : D.Claims X) (x : An × Sd) (y : Fin n → S) : Prop :=
  LangK2 A (wayColl D) (sd x.2, an x.1) (rawOf u y)

open Classical in
/-- **The test of a second lane**: at the seed the record does not single one table out of the
string's list. -/
noncomputable def badK (y : Fin n → S) (s : Sd) : Bool := decide (D.collRaw (rawOf u y) (sd s))

open Classical in
/-- The test is false exactly where the record singles one out. -/
theorem badK_false (y : Fin n → S) (s : Sd) :
    badK u sd y s = false ↔ ¬ D.collRaw (rawOf u y) (sd s) := by
  unfold badK
  exact decide_eq_false_iff_not

/-- **FROM A TYPED WORLD TO THE JOIN'S LANGUAGE OF THE KEY**: if the key's language with the way out
holds of the record and the string, and the second lane's test is false of the string and the
record's seeds, then the raw form of the string is in `LangK` at `wayColl`, with that record. -/
theorem langK_of_typed (A : D.Claims X) (x : An × Sd) (y : Fin n → S)
    (h : LgK u an sd A x y ∧ badK u sd y x.2 = false) :
    LangK A (wayColl D) (sd x.2, an x.1) (rawOf u y) :=
  langK_of_langK2 A (wayColl D) ((badK_false u sd _ _).1 h.2) h.1

/-- **The same from a list of raw strings**: in the form of the language of a part over the one
oracle whose judge's language is "`LgK` of the instance and the string, and `badK` false". -/
theorem langK_of_lang_one (A : D.Claims X) (x : An × Sd) (Y : Raw Run.PQ.SgX)
    (h : ∃ ys : List (Fin n → S), [Y] = ys.map (rawOf u) ∧
      ∀ y, ys = [y] → LgK u an sd A x y ∧ badK u sd y x.2 = false) :
    LangK A (wayColl D) (sd x.2, an x.1) Y := by
  obtain ⟨ys, e, h⟩ := h
  match ys, e, h with
  | [y], e, h =>
    rw [(List.cons.inj e).1]
    exact langK_of_typed u an sd A x y (h y rfl)

/-- The entry's language of a typed world, with the way out for both tables: the instance is the two
records. -/
def LgE (x₀ x₁ : An × Sd) (y₀ y₁ : Fin n → S) : Prop :=
  LangE2 (wayColl D) (sd x₀.2, an x₀.1) (sd x₁.2, an x₁.1) (rawOf u y₀) (rawOf u y₁)

/-- **The like for the entry**: the second lane's test is false of the COPY and its seeds. -/
theorem langE_of_typed (x₀ x₁ : An × Sd) (y₀ y₁ : Fin n → S)
    (h : LgE u an sd x₀ x₁ y₀ y₁ ∧ badK u sd y₁ x₁.2 = false) :
    LangE (wayColl D) (sd x₀.2, an x₀.1) (sd x₁.2, an x₁.1) (rawOf u y₀) (rawOf u y₁) :=
  langE_of_langE2 (wayColl D) ((badK_false u sd _ _).1 h.2) h.1

/-- **The same from a list of two raw strings.** -/
theorem langE_of_lang_two (x₀ x₁ : An × Sd) (Y₀ Y₁ : Raw Run.PQ.SgX)
    (h : ∃ ys : List (Fin n → S), [Y₀, Y₁] = ys.map (rawOf u) ∧
      ∀ y₀ y₁, ys = [y₀, y₁] → LgE u an sd x₀ x₁ y₀ y₁ ∧ badK u sd y₁ x₁.2 = false) :
    LangE (wayColl D) (sd x₀.2, an x₀.1) (sd x₁.2, an x₁.1) Y₀ Y₁ := by
  obtain ⟨ys, e, h⟩ := h
  match ys, e, h with
  | [y₀, y₁], e, h =>
    rw [(List.cons.inj e).1, (List.cons.inj (List.cons.inj e).2).1]
    exact langE_of_typed u an sd x₀ x₁ y₀ y₁ (h y₀ y₁ rfl)

/-- The proof's language of a typed world: `LangP` at `wayColl`, which has the way out already, at
the raw form of the string. xi: the instance of the claim; x: the record. -/
def LgP (A : D.Claims X) (xi : X) (x : An × Sd) (y : Fin n → S) : Prop :=
  LangP A (wayColl D) xi (sd x.2, an x.1) (rawOf u y)

/-- The test, on tables: for a string of 2^a symbols. -/
theorem badK_iff (hn : n = 2 ^ D.T.a) (y : Fin n → S) (s : Sd) :
    badK u sd y s = true ↔ D.coll (D.ofTyped u hn y) (sd s) := by
  rw [← D.collRaw_rawOf u hn y (sd s), ← not_iff_not, ← badK_false u sd y s, Bool.not_eq_true]

/-- The key's language of a typed world, on tables: for a string of 2^a symbols. -/
theorem lgK_iff (hn : n = 2 ^ D.T.a) (A : D.Claims X) (x : An × Sd) (y : Fin n → S) :
    LgK u an sd A x y ↔ D.coll (D.ofTyped u hn y) (sd x.2) ∨
      ∃ t, D.dcd (D.ofTyped u hn y) (sd x.2, an x.1) = some t ∧ A.inRange (A.mat t) := by
  unfold LgK LangK2 wayColl
  rw [D.collRaw_rawOf u hn y, D.dcdRaw_rawOf u hn y]

/-- The entry's language of a typed world, on tables. -/
theorem lgE_iff (hn : n = 2 ^ D.T.a) (x₀ x₁ : An × Sd) (y₀ y₁ : Fin n → S) :
    LgE u an sd x₀ x₁ y₀ y₁ ↔
      D.dcd (D.ofTyped u hn y₀) (sd x₀.2, an x₀.1) = none ∨ D.coll (D.ofTyped u hn y₀) (sd x₀.2) ∨
        D.coll (D.ofTyped u hn y₁) (sd x₁.2) ∨
        ∃ t₀ t₁, D.dcd (D.ofTyped u hn y₀) (sd x₀.2, an x₀.1) = some t₀ ∧
          D.dcd (D.ofTyped u hn y₁) (sd x₁.2, an x₁.1) = some t₁ ∧ D.Agree t₁ t₀ := by
  unfold LgE LangE2 wayColl
  rw [D.collRaw_rawOf u hn y₀, D.collRaw_rawOf u hn y₁, D.dcdRaw_rawOf u hn y₀,
    D.dcdRaw_rawOf u hn y₁]

/-- The proof's language of a typed world, on tables. -/
theorem lgP_iff (hn : n = 2 ^ D.T.a) (A : D.Claims X) (xi : X) (x : An × Sd) (y : Fin n → S) :
    LgP u an sd A xi x y ↔
      D.dcd (D.ofTyped u hn y) (sd x.2, an x.1) = none ∨ D.coll (D.ofTyped u hn y) (sd x.2) ∨
        ∃ t, D.dcd (D.ofTyped u hn y) (sd x.2, an x.1) = some t ∧ A.Rel (A.mat t) xi := by
  unfold LgP LangP wayColl
  rw [D.collRaw_rawOf u hn y, D.dcdRaw_rawOf u hn y]

/-- **At another length than 2^a the test is false of every string and every seed.** -/
theorem badK_of_len (hn : n ≠ 2 ^ D.T.a) (y : Fin n → S) (s : Sd) : badK u sd y s = false :=
  (badK_false u sd y s).2 fun h => hn ((rawOf_hasLen u y).unique h.1)

/-- **And the key's language holds of nothing.** -/
theorem not_lgK_of_len (hn : n ≠ 2 ^ D.T.a) (A : D.Claims X) (x : An × Sd) (y : Fin n → S) :
    ¬ LgK u an sd A x y := by
  rintro (h | ⟨t, ht, -⟩)
  · exact hn ((rawOf_hasLen u y).unique h.1)
  · unfold dcdRaw at ht
    rw [if_neg fun h => hn ((rawOf_hasLen u y).unique h)] at ht
    cases ht

/-- At another length than 2^a no string with a record decodes. -/
theorem dcdRaw_of_len (hn : n ≠ 2 ^ D.T.a) (y : Fin n → S) (rec : D.Rec) :
    D.dcdRaw (rawOf u y) rec = none := by
  unfold dcdRaw
  rw [if_neg fun h => hn ((rawOf_hasLen u y).unique h)]

/-- **BUT THE ENTRY'S LANGUAGE HOLDS OF EVERYTHING THERE**: the first table does not decode, which
is its first clause. So a statement that has `LgE` as its language is true for free at another
length: whoever uses one asks that the length is 2^a. -/
theorem lgE_of_len (hn : n ≠ 2 ^ D.T.a) (x₀ x₁ : An × Sd) (y₀ y₁ : Fin n → S) :
    LgE u an sd x₀ x₁ y₀ y₁ :=
  Or.inl (dcdRaw_of_len u hn y₀ _)

/-- **AND SO DOES THE PROOF'S.** -/
theorem lgP_of_len (hn : n ≠ 2 ^ D.T.a) (A : D.Claims X) (xi : X) (x : An × Sd) (y : Fin n → S) :
    LgP u an sd A xi x y :=
  Or.inl (dcdRaw_of_len u hn y _)

end DecR

end OnBytes.Slice
