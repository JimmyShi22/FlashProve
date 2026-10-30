-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/IndexLaws.lean: the shape of the stored tables that is read from a spelled item "the
test on the table" or "the link" is a function of the spelled tables' shape alone.

Both items begin with the spelling of a stored table's shape, six words (`spellIndex`,
OnBytes/Params/Spell.lean), and both readers begin with the reader of that shape (`indexShape`,
OnBytes/Params/Items.lean). So two items that were spelled from the same shape of the tables are
read back with the same shape of the tables, if both are read back at all, whatever else they hold
and whatever the six numbers are.

Main definition: `indexAt`. Main theorems: `readLink_table`, `readLin_index`.

What is not claimed. That the shape which is read back is the shape that was spelled: a number from
2^64 on is spelled modulo 2^64. Nothing on the other fields of the two items. Nothing if a reader
refuses. For proofs only; the program does not import this file.
-/
import Fmt.Rules1Laws
import OnBytes.Params.Spell

set_option autoImplicit false

namespace OnBytes.Params

/-- If two readers in a row return a value, the first has returned a value and a place, and the
second has returned its value from there. -/
theorem cut_bind {α β : Type} {x : Cut α} {f : α → Cut β} {b : ByteArray} {i k : Nat} {r : β}
    (h : (x >>= f) b i = some (r, k)) : ∃ a j, x b i = some (a, j) ∧ f a b j = some (r, k) := by
  cases hx : x b i with
  | none =>
    have : (x >>= f) b i = none := by
      show (x b i >>= fun y => f y.1 b y.2) = none
      rw [hx]
      rfl
    rw [this] at h
    cases h
  | some y =>
    refine ⟨y.1, y.2, rfl, ?_⟩
    have : (x >>= f) b i = f y.1 b y.2 := by
      show (x b i >>= fun y => f y.1 b y.2) = _
      rw [hx]
      rfl
    rw [← this]
    exact h

/-- What the reader of a word returns: the word at its place, and the place eight bytes on. -/
theorem word_at {b : ByteArray} {i k n : Nat} (h : word b i = some (n, k)) :
    n = (Fmt.wordAt b i).toNat ∧ k = i + 8 := by
  unfold word cut Fmt.rdWord at h
  dsimp only at h
  split at h
  · cases h
    exact ⟨rfl, rfl⟩
  · cases h

/-- The shape of a stored table that the six words at the beginning of b spell. -/
def indexAt (b : ByteArray) : IndexShape :=
  ⟨⟨(Fmt.wordAt b 0).toNat, (Fmt.wordAt b 8).toNat, (Fmt.wordAt b 16).toNat⟩,
    (Fmt.wordAt b 24).toNat, (Fmt.wordAt b 32).toNat, (Fmt.wordAt b 40).toNat⟩

/-- What the reader of a stored table's shape returns at the beginning of b is `indexAt b`. -/
theorem indexShape_at {b : ByteArray} {k : Nat} {x : IndexShape}
    (h : indexShape b 0 = some (x, k)) : x = indexAt b := by
  unfold indexShape code at h
  obtain ⟨c, j, hc, h⟩ := cut_bind h
  obtain ⟨n1, j1, h1, hc⟩ := cut_bind hc
  obtain ⟨n2, j2, h2, hc⟩ := cut_bind hc
  obtain ⟨n3, j3, h3, hc⟩ := cut_bind hc
  cases hc
  obtain ⟨n4, j4, h4, h⟩ := cut_bind h
  obtain ⟨n5, j5, h5, h⟩ := cut_bind h
  obtain ⟨n6, j6, h6, h⟩ := cut_bind h
  cases h
  obtain ⟨rfl, rfl⟩ := word_at h1
  obtain ⟨rfl, rfl⟩ := word_at h2
  obtain ⟨rfl, rfl⟩ := word_at h3
  obtain ⟨rfl, rfl⟩ := word_at h4
  obtain ⟨rfl, rfl⟩ := word_at h5
  obtain ⟨rfl, rfl⟩ := word_at h6
  rfl

/-- The six words at the beginning of a string that begins with 48 bytes a are those of a. -/
theorem indexAt_append (a rest : ByteArray) (h : a.size = 48) :
    indexAt (a ++ rest) = indexAt a := by
  have w : ∀ j, j + 8 ≤ a.size → Fmt.wordAt (a ++ rest) j = Fmt.wordAt a j := by
    intro j hj
    have := Fmt.wordAt_mid ByteArray.empty a rest j hj
    simpa using this
  unfold indexAt
  rw [w 0 (by omega), w 8 (by omega), w 16 (by omega), w 24 (by omega), w 32 (by omega),
    w 40 (by omega)]

/-- The spelling of a stored table's shape has 48 bytes. -/
theorem spellIndex_size (I : IndexShape) : (spellIndex I).size = 48 := by
  simp [spellIndex, spellCode, spellRow, spellWord, Fmt.cat_cons, Fmt.cat_nil, Fmt.u64n,
    ByteArray.size_append, Fmt.size_u64]

/-- The tables' shape in what is read from an item "the link" that was spelled from S depends on the
tables' shape in S alone. -/
theorem readLink_table {S L : LinkShape} (h : readLink (spellLink S) = some L) :
    L.table = indexAt (spellIndex S.table) := by
  have e : ∃ rest, spellLink S = spellIndex S.table ++ rest :=
    ⟨_, by simp only [spellLink, ByteArray.append_assoc]; rfl⟩
  obtain ⟨rest, e⟩ := e
  rw [e] at h
  unfold readLink Cut.whole Fmt.whole Cut.rd at h
  split at h
  · rename_i x j hx
    split at h
    · cases h
      unfold linkShape at hx
      obtain ⟨t, j0, ht, hx⟩ := cut_bind hx
      obtain ⟨_, _, _, hx⟩ := cut_bind hx
      obtain ⟨_, _, _, hx⟩ := cut_bind hx
      obtain ⟨_, _, _, hx⟩ := cut_bind hx
      obtain ⟨_, _, _, hx⟩ := cut_bind hx
      obtain ⟨_, _, _, hx⟩ := cut_bind hx
      obtain ⟨_, _, _, hx⟩ := cut_bind hx
      obtain ⟨_, _, _, hx⟩ := cut_bind hx
      obtain ⟨_, _, _, hx⟩ := cut_bind hx
      obtain ⟨_, _, _, hx⟩ := cut_bind hx
      obtain ⟨_, _, _, hx⟩ := cut_bind hx
      cases hx
      rw [← indexAt_append _ rest (spellIndex_size _)]
      exact indexShape_at ht
    · cases h
  · cases h

/-- The tables' shape in what is read from an item "the test on the table" that was spelled from S
depends on the tables' shape in S alone. -/
theorem readLin_index {S X : LinShape} (h : readLin (spellLin S) = some X) :
    X.fold.index = indexAt (spellIndex S.fold.index) := by
  have e : ∃ rest, spellLin S = spellIndex S.fold.index ++ rest :=
    ⟨_, by simp only [spellLin, spellFoldeq, ByteArray.append_assoc]; rfl⟩
  obtain ⟨rest, e⟩ := e
  rw [e] at h
  unfold readLin Cut.whole Fmt.whole Cut.rd at h
  split at h
  · rename_i x j hx
    split at h
    · cases h
      unfold linShape at hx
      obtain ⟨fold, j0, hf, hx⟩ := cut_bind hx
      have hfold : X.fold = fold := by
        iterate 20 obtain ⟨_, _, _, hx⟩ := cut_bind hx
        cases hx
        rfl
      rw [hfold]
      unfold foldeqShape at hf
      obtain ⟨t, j1, ht, hf⟩ := cut_bind hf
      obtain ⟨_, _, _, hf⟩ := cut_bind hf
      obtain ⟨_, _, _, hf⟩ := cut_bind hf
      obtain ⟨_, _, _, hf⟩ := cut_bind hf
      obtain ⟨_, _, _, hf⟩ := cut_bind hf
      cases hf
      rw [← indexAt_append _ rest (spellIndex_size _)]
      exact indexShape_at ht
    · cases h
  · cases h

end OnBytes.Params

#print axioms OnBytes.Params.readLink_table
#print axioms OnBytes.Params.readLin_index
