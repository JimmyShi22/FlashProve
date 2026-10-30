-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/ChainStmLaws.lean: for the statement of each chain of a key file and of a proof file: the reader
(Fmt/ChainStmRead.lean) gives a value exactly on the bytes that the writer writes of that value, and
exactly where the value has its form and the statement has fewer than 2 ^ 64 bytes. So such a
statement's bytes fix the values of which they are written.
It stands on Fmt/ChainStm.lean, Fmt/ChainStmRead.lean, Fmt/ParsedLaws.lean and
Fmt/ParsedReadCut.lean.

How: by the library's frame for "a reader undoes a spelling, whatever stands before and behind"
(`Undoes`, Fmt/Rules1Laws.lean) and, for the other law, "what a reader accepts is the spelling of
what it returns", by the frame `Cuts` (Fmt/ParsedReadLaws.lean), part by part. Both laws of a
reader, with one and the same form ok, give the law of the reader on a whole string (`whole_both`,
`wholeStm_both`). No Mathlib, neither directly nor through the imports.

1. What the file contains. Theorems. No definition.

2. What is checked when the file compiles. The proofs; the axioms of every theorem are printed.
Tests: Fmt/TestChainStm.lean.

3. Theorems.
   The other law of the library's reader of an item: `toNat_ofNat_byte`, `byte_of_isName`,
     `toList_nameOf`, `okName_nameOf`, `ascii_nameOf` (the bytes of a name, read as a string and
     spelled again, are the bytes), `only_rdItem`. The library has the first law (`undoes_item`,
     Fmt/ParamsReadLawsProofs.lean). Of the reader of the whole parameter bytes, which calls
     `rdItem`, the head of Fmt/ParamsRead.lean (3) says that the second half is only tested.
   The frame: `undoes_if`, `cuts_if`; `undoes_named` (asked: the name is a name of fewer than 2 ^ 64
     bytes), `cuts_named`; `whole_both`, `wholeStm_both`.
   A table: `size_exts`, `TableSt.value_size`, `TableSt.ok_iff`, `TableShape.fitsWord_iff`,
     `TableShape.fitsWord_of_ok`, `TableSt.value_size_ok`, `one_le_ext`, `undoes_tableRaw`,
     `undoes_tableValue`, `cuts_tableValue`, `undoes_tableItem`, `cuts_tableItem`.
   The other items: `undoes_digestItem`, `cuts_digestItem`; `copyOf_toNat`, `toNat_of_copyOf`,
     `undoes_copyItem`, `cuts_copyItem`; `size_text`, `undoes_requestItem`, `cuts_requestItem`,
     `undoes_wordsItem`, `cuts_wordsItem`.
   The statements' lengths: `item_size_eq`; `sealItem_name`, `sealItems_two`, `ProofStm.bytes_pair`;
     `TableSt.item_size`, `sharedStm_size`, `sealItems_size`, `ProofStm.bytes_size`,
     `EntryStm.bytes_size`; for tables with the form: `ProofStm.bytes_size_ok`,
     `EntryStm.bytes_size_ok`; `TableSt.item_size_lt`, `sharedStm_size_lt` (asked of both:
     `TableShape.fitsWord`).
   BOTH LAWS IN ONE, without a premise, for any string b:
     `TableSt.readItem_iff`, `rdSharedStm_iff`, `rdSealItems_iff`, `ProofStm.read_iff`:
     the reader gives x on b exactly where x has its form, b has fewer than 2 ^ 64 bytes (for two
     seals that follows), and b is the writing of x.
   "read (bytes x) = some x exactly where ...", without a premise: `TableSt.readItem_item_iff`,
     `rdSharedStm_bytes_iff` (the form, and the statement's length as a number is below 2 ^ 64),
     `rdSealItems_bytes`, `ProofStm.read_bytes`.
   "... exactly where ok x": `TableSt.readItem_item`, `rdSharedStm_bytes` (asked of both:
     `TableShape.fitsWord`).
   The same at the names of Fmt/ChainStm.lean, three chains at once: `keyStmAt_read` (asked:
     `TableShape.fitsWord`), `proofStmAt_read` (nothing asked), over `sealsOk_iff`,
     `ProofStm.ok_iff`. `ProofStm.sharedStm_size_lt`.
   `rdSharedStm_items`: the tie to the library's readers of a statement's items.
   One-to-one on what has the form: `TableSt.item_inj`, `sharedStm_inj` (asked of both:
     `TableShape.fitsWord`; a term for them: `TableSt.ok_fits`), `sealItems_inj`,
     `ProofStm.bytes_inj`; `ProofStm.bytes_reply`. Out of `ProofStm.bytes_inj`:
     `ProofStm.bytes_words` (the same statement: the same field `words`, which is to hold the
     request file's bytes);
     `ProofStm.bytes_swap` (with the item "request"'s value and the request file's bytes in each
     other's places the statement is another, unless the two are one string).
   The first item's name: `firstName_item`, `okItem_table`, `okItem_seal`, `keyStmAt_firstName`
     and `proofStmAt_firstName` (asked: the table's item's value and the first seal have fewer than
     2 ^ 64 bytes), `Which.firstName_second`, `Which.firstName_first`.
   A first chain's statement against a shared chain's: `keyStmAt_shared` (nothing asked);
     `TableSt.item_ne_sharedStm` (asked: both tables have the form, under one field and one shape);
     `ProofStm.bytes_ne_sharedStm` (asked: the same, and the root has fewer than 2 ^ 64 bytes).

4. What is not claimed.
   "Form" means here `TableSt.ok`, `ProofStm.ok`, `sealsOk`. `TableShape.fitsWord` is no form: it is
   a test on the shape that no reader and no form calls; the closed forms of Fmt/ChainStm.lean ask
   it. The half "only where x has its form" holds for a table because the reader tests `TableSt.ok`,
   and the clause "fewer than 2 ^ 64 bytes" because the reader tests it (`wholeStm`).
   WHICH STATEMENTS THE FORMS BOUND. `ProofStm.ok` gives "fewer than 2 ^ 64 bytes" for a proof's
   first chain (`ProofStm.bytes_size_ok`), `sealsOk` for a second chain (152 bytes:
   `sealItems_size`). For a key's one-time chain and for the shared chain of a key NO FORM GIVES IT:
   `TableSt.ok` bounds no length. The last clause of `ProofStm.ok` bounds a proof's shared chain's
   140 + 24 for each answer too (`ProofStm.sharedStm_size_lt`): 140 is below 183. What gives it for
   these two is the premise hs, `TableShape.fitsWord` (`TableSt.item_size_lt`, `sharedStm_size_lt`).
   Beside the forms: the library's `Spec.small` bounds every statement under which a chain is read
   by `readChainX`, at the format page's 2 ^ 32 - 144 (R2.3, R2.7): `Declared.spec_ok_small`,
   Fmt/ChainStmSmall.lean.
   hs stands in eight theorems. No theorem here but `TableShape.fitsWord_of_ok` has `TableShape.ok`
   as a premise; with it hs follows from `TableShape.ok`. hs asks more than these theorems need (it
   is the bound for an entry's statement, the longest); what exactly is needed: the two laws
   `..._iff` without a premise.
   The one-to-one laws and the last two theorems tie both values to one field and one shape.
   Of a proof's statement the laws speak of four fields (`ProofStm.hashed`). The reply is not hashed
   with the statement: two values that differ in the reply alone have the same bytes
   (`ProofStm.bytes_reply`; `ProofStm.bytes_inj` gives the four fields and no more). That the value
   of the item "request" is what Fmt/RequestItem.lean's function makes of the request file's bytes
   in the fourth item is said by no law here: the two fields are free of each other.
   `ProofStm.words` ITSELF IS A FREE FIELD: that it holds a request file's bytes is held by nothing
   here or below. In `proofStmAt_read` the clause of `ProofStm.ok` on the reply stands on the left
   side by itself.
   From "the same string is hashed in the first query" to "the same statement" is the library's law
   (`firstBytes_inj`, Fmt/Rules4Laws.lean), which asks among other things that both statements have
   fewer than 2 ^ 64 bytes: see above for what gives that. The two laws are joined in
   Fmt/ChainStmJoin.lean.
   The first item's name tells a second chain's statement from the two others. It does not tell a
   first chain's from a shared chain's: both begin with the item "table", and in a key file the
   first chain's statement is the beginning of the shared chain's (`keyStmAt_shared`). As strings
   the two differ, under the premises of the last two theorems. What enters the hash call beside the
   statement is the label and the parameters' digest (`firstValueW`, Fmt/Rules4.lean); the tests on
   the declared structure hold each of the three labels against a constant (`Declared.keyFormOk`,
   `Declared.proofFormOk`, over `Declared.chainsFormOk`, Fmt/Parsed.lean). No theorem here speaks of
   labels.
   Nothing on soundness follows: no verifier calls these readers.
   Here is no law for the statement of an entry's link (`EntryStm.bytes`; its length alone), nor for
   `recordStm` (Fmt/ChainStm.lean): Fmt/ChainStmMore.lean has both.
   Fmt/Rules23In.lean is imported for one lemma on strings (`append_cancel`); with it the library's
   laws on the hash's input lie below this module.

-/
import Fmt.ChainStmRead
import Fmt.ParsedReadCut
import Fmt.Rules23In

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fmt

/-! ## 1. The other law of the library's reader of an item -/

/-- The character of a number below 256 has that number. -/
theorem toNat_ofNat_byte : ∀ n, n < 256 → (Char.ofNat n).toNat = n := by decide +kernel

/-- The bytes of a string that passes the reader's test on names lie from 0x20 to 0x7E. -/
theorem byte_of_isName (b : ByteArray) (h : isName b = true) (x : UInt8) (hx : x ∈ b.data.toList) :
    32 ≤ x.toNat ∧ x.toNat ≤ 126 := by
  unfold isName at h
  rw [← Array.all_toList] at h
  have a := List.all_eq_true.1 h x hx
  simp only [Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le] at a
  exact a

/-- The characters of the string that `nameOf` makes of bytes. -/
theorem toList_nameOf (b : ByteArray) :
    (nameOf b).toList = b.data.toList.map fun x => Char.ofNat x.toNat := by
  unfold nameOf
  simp

/-- Bytes that pass the reader's test on names are read as a string within the page's rule. -/
theorem okName_nameOf (b : ByteArray) (h : isName b = true) : okName (nameOf b) = true := by
  unfold okName
  rw [toList_nameOf, List.all_map]
  refine List.all_eq_true.2 fun x hx => ?_
  have a := byte_of_isName b h x hx
  simp only [Function.comp, Bool.and_eq_true, decide_eq_true_eq]
  rw [toNat_ofNat_byte x.toNat (by omega)]
  exact a

/-- Bytes that pass the reader's test on names, read as a string and spelled again, are the bytes.
(The other way round: `nameOf_ascii`, Fmt/ParamsReadLawsProofs.lean.) -/
theorem ascii_nameOf (b : ByteArray) (h : isName b = true) : ascii (nameOf b) = b := by
  apply ByteArray.ext
  apply Array.toList_inj.1
  rw [ascii_data _ (okName_nameOf b h), toList_nameOf, List.map_map]
  have e : ∀ x ∈ b.data.toList,
      ((fun c : Char => UInt8.ofNat c.toNat) ∘ fun x : UInt8 => Char.ofNat x.toNat) x = id x := by
    intro x hx
    have a := byte_of_isName b h x hx
    show UInt8.ofNat (Char.ofNat x.toNat).toNat = x
    rw [toNat_ofNat_byte x.toNat (by omega), UInt8.ofNat_toNat]
  rw [List.map_congr_left e, List.map_id]

/-- What the library's reader of an item accepts is the spelling of the item that it returns, and
that item is within the bounds. (That it undoes the spelling: `undoes_item`,
Fmt/ParamsReadLawsProofs.lean.) -/
theorem only_rdItem : Only rdItem (fun x => item x.1 x.2) okItem := by
  intro b i x l h
  unfold rdItem at h
  rcases h1 : rdName b i with _ | ⟨n, j⟩
  · rw [h1] at h
    exact absurd h (by simp)
  · rw [h1] at h
    simp only at h
    rcases h2 : rdText b j with _ | ⟨v, k⟩
    · rw [h2] at h
      exact absurd h (by simp)
    · rw [h2] at h
      simp only [Option.map_some] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨⟨a0, a1⟩, a2, -, a4⟩ := only_name b i n j h1
      obtain ⟨c1, c2, c3, c4⟩ := only_text b j v k h2
      have en := ascii_nameOf n a1
      have ei : item (nameOf n) v = text n ++ text v := by
        simp only [item, textS, text, en, ByteArray.append_assoc]
      refine ⟨⟨okName_nameOf n a1, ?_, c1⟩, ?_, c3, ?_⟩
      · show (ascii (nameOf n)).size < 2 ^ 64
        rw [en]
        exact a0
      · show k = i + (item (nameOf n) v).size
        rw [ei, ByteArray.size_append]
        omega
      · show b.extract i k = item (nameOf n) v
        rw [ei, ByteArray.extract_eq_extract_append_extract j (by omega) (by omega), a4, c4]

/-! ## 2. The frame -/

/-- The reader with a test undoes the spelling on the values that pass the test. -/
theorem undoes_if {α : Type} {r : Rd α} {sp : α → ByteArray} {ok : α → Prop} (h : Undoes r sp ok)
    (p : α → Bool) : Undoes (rdIf p r) sp fun x => ok x ∧ p x = true := by
  intro x hx pre post
  unfold rdIf
  rw [h x hx.1 pre post]
  simp only
  rw [if_pos hx.2]

/-- What the reader with a test accepts passes the test. -/
theorem cuts_if {α : Type} {r : Rd α} {sp : α → ByteArray} {ok : α → Prop} (h : Cuts r sp ok)
    (p : α → Bool) : Cuts (rdIf p r) sp fun x => ok x ∧ p x = true := by
  intro b i x j hr
  unfold rdIf at hr
  rcases h1 : r b i with _ | ⟨y, k⟩
  · rw [h1] at hr
    exact absurd hr (by simp)
  · rw [h1] at hr
    simp only at hr
    by_cases hp : p y = true
    · rw [if_pos hp] at hr
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hr)
      obtain ⟨a1, a2, a4⟩ := h b i y k h1
      exact ⟨⟨a1, hp⟩, a2, a4⟩
    · rw [if_neg hp] at hr
      exact absurd hr (by simp)

/-- An item of a given name, with a value that r reads: asked, that the name is within the page's
rule and has fewer than 2 ^ 64 bytes; ok: the value's, and its spelling has fewer than 2 ^ 64 bytes.
-/
theorem undoes_named {α : Type} {r : Rd α} {sp : α → ByteArray} {ok : α → Prop} (name : String)
    (h1 : okName name = true) (h2 : (ascii name).size < 2 ^ 64) (h : Undoes r sp ok) :
    Undoes (rdNamed name r) (fun x => item name (sp x)) fun x => ok x ∧ (sp x).size < 2 ^ 64 := by
  intro x hx pre post
  have a : rdItem (pre ++ item name (sp x) ++ post) pre.size =
      some ((name, sp x), pre.size + (item name (sp x)).size) :=
    undoes_item (name, sp x) ⟨h1, h2, hx.2⟩ pre post
  show rdNamed name r (pre ++ item name (sp x) ++ post) pre.size =
    some (x, pre.size + (item name (sp x)).size)
  unfold rdNamed
  rw [a]
  simp only [beq_self_eq_true, if_true, whole_of_undoes h x hx.1, Option.map_some]

/-- What the reader of an item of a given name accepts is such an item. -/
theorem cuts_named {α : Type} {r : Rd α} {sp : α → ByteArray} {ok : α → Prop} (name : String)
    (h : Cuts r sp ok) :
    Cuts (rdNamed name r) (fun x => item name (sp x)) fun x => ok x ∧ (sp x).size < 2 ^ 64 := by
  intro b i y j hr
  unfold rdNamed at hr
  rcases h1 : rdItem b i with _ | ⟨x, k⟩
  · rw [h1] at hr
    exact absurd hr (by simp)
  · rw [h1] at hr
    simp only at hr
    by_cases hn : (x.1 == name) = true
    · rw [if_pos hn] at hr
      rcases h2 : whole r x.2 with _ | z
      · rw [h2] at hr
        exact absurd hr (by simp)
      · rw [h2] at hr
        simp only [Option.map_some] at hr
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hr)
        obtain ⟨a1, a2, -, a4⟩ := only_rdItem b i x k h1
        obtain ⟨c1, c2⟩ := whole_cuts h x.2 z h2
        have en : x.1 = name := eq_of_beq hn
        have a2' : k = i + (item x.1 x.2).size := a2
        have a4' : b.extract i k = item x.1 x.2 := a4
        have a3' : x.2.size < 2 ^ 64 := a1.2.2
        rw [en, c1] at a2' a4'
        rw [c1] at a3'
        exact ⟨⟨c2, a3'⟩, a2', a4'⟩
    · rw [if_neg hn] at hr
      exact absurd hr (by simp)

/-- BOTH LAWS OF A READER, ON A WHOLE STRING. If r undoes sp on the values with ok, and accepts
nothing but spellings of values with ok, then r reads x out of the whole string b exactly where x
has ok and b is the spelling of x. -/
theorem whole_both {α : Type} {r : Rd α} {sp : α → ByteArray} {ok : α → Prop} (hu : Undoes r sp ok)
    (hc : Cuts r sp ok) (b : ByteArray) (x : α) : whole r b = some x ↔ ok x ∧ b = sp x := by
  constructor
  · intro h
    exact ⟨(whole_cuts hc b x h).2, (whole_cuts hc b x h).1⟩
  · rintro ⟨h1, rfl⟩
    exact whole_of_undoes hu x h1

/-- The same for a whole statement: and b has fewer than 2 ^ 64 bytes. -/
theorem wholeStm_both {α : Type} {r : Rd α} {sp : α → ByteArray} {ok : α → Prop}
    (hu : Undoes r sp ok) (hc : Cuts r sp ok) (b : ByteArray) (x : α) :
    wholeStm r b = some x ↔ (ok x ∧ b.size < 2 ^ 64) ∧ b = sp x := by
  unfold wholeStm
  by_cases hb : b.size < 2 ^ 64
  · rw [if_pos hb, whole_both hu hc]
    exact ⟨fun h => ⟨⟨h.1, hb⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
  · rw [if_neg hb]
    exact ⟨fun h => absurd h (by simp), fun h => absurd h.1.2 hb⟩

/-! ## 3. A table -/

/-- Elements of E, spelled one after the other, have 24 bytes each. -/
theorem size_exts (l : List Ext) : (cat (l.map ext)).size = 24 * l.length := by
  induction l with
  | nil => simp [cat_nil]
  | cons e l ih =>
    rw [List.map_cons, cat_cons, ByteArray.size_append, ih, List.length_cons]
    unfold ext
    rw [ByteArray.size_append, ByteArray.size_append, size_u64, size_u64, size_u64]
    omega

/-- The length of the value of a table's item. -/
theorem TableSt.value_size (t : TableSt) :
    t.value.size = 16 + t.root.size + 24 * t.answers.length := by
  simp only [TableSt.value, text, list, u64n, ByteArray.size_append, size_u64, size_exts]
  omega

/-- `TableSt.ok` as three statements. -/
theorem TableSt.ok_iff (f : Fld) (s : TableShape) (t : TableSt) :
    t.ok f s = true ↔
      t.root.size = 32 ∧ t.answers.length = s.count ∧ ∀ e ∈ t.answers, f.okE e = true := by
  simp only [TableSt.ok, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, and_assoc]

/-- `TableShape.fitsWord` as an inequality. -/
theorem TableShape.fitsWord_iff (s : TableShape) :
    s.fitsWord = true ↔ 160 + 48 * s.count < 2 ^ 64 := by
  simp only [TableShape.fitsWord, decide_eq_true_eq]

/-- `TableShape.ok` (Fmt/Parsed.lean) gives `TableShape.fitsWord`: it is its last clause. -/
theorem TableShape.fitsWord_of_ok (s : TableShape) (h : s.ok = true) : s.fitsWord = true := by
  simp only [TableShape.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [TableShape.fitsWord_iff]
  exact h.2

/-- The length of the value of the item of a table with the form. -/
theorem TableSt.value_size_ok (f : Fld) (s : TableShape) (t : TableSt) (h : t.ok f s = true) :
    t.value.size = 48 + 24 * s.count := by
  obtain ⟨a, c, -⟩ := (TableSt.ok_iff f s t).1 h
  have e := TableSt.value_size t
  omega

/-- An element of E is spelled with at least one byte. -/
theorem one_le_ext (e : Ext) : 1 ≤ (ext e).size := by
  unfold ext
  rw [ByteArray.size_append, ByteArray.size_append, size_u64, size_u64, size_u64]
  omega

/-- The value of a table's item, before the test of the form: a root and a list of answers, each of
fewer than 2 ^ 64 members; canonical answers. -/
theorem undoes_tableRaw (f : Fld) :
    Undoes
      (rdMap (fun x : ByteArray × List Ext => (⟨x.1, x.2⟩ : TableSt))
        (rdPair rdText (rdList (rdExt f))))
      TableSt.value fun t =>
        t.root.size < 2 ^ 64 ∧ t.answers.length < 2 ^ 64 ∧ ∀ e ∈ t.answers, f.okE e = true :=
  undoes_map (β := TableSt)
    (undoes_pair undoes_text (undoes_list (undoes_ext f) fun e _ => one_le_ext e))
    (fun x => ⟨x.1, x.2⟩) (fun t => (t.root, t.answers)) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ h => ⟨h.1, h.2.1, fun e he => lt_of_okE f e (h.2.2 e he)⟩)

/-- The value of a table's item (ok: the table has the form, and the value has fewer than 2 ^ 64
bytes). -/
theorem undoes_tableValue (f : Fld) (s : TableShape) :
    Undoes (rdTableValue f s) TableSt.value fun t => t.ok f s = true ∧ t.value.size < 2 ^ 64 := by
  intro t ht
  obtain ⟨a, -, d⟩ := (TableSt.ok_iff f s t).1 ht.1
  have hw : t.value.size < 2 ^ 64 := ht.2
  rw [TableSt.value_size] at hw
  have h1 : t.root.size < 2 ^ 64 := by omega
  have h2 : t.answers.length < 2 ^ 64 := by omega
  exact undoes_if (undoes_tableRaw f) (TableSt.ok f s) t ⟨⟨h1, h2, d⟩, ht.1⟩

/-- What the reader of a table's value accepts has the form, because it tests the form. -/
theorem cuts_tableValue (f : Fld) (s : TableShape) :
    Cuts (rdTableValue f s) TableSt.value fun t => t.ok f s = true := by
  have h0 := cuts_pair (cuts_of_only only_text) (cuts_of_only (only_list (only_ext f)))
  have h1 : Cuts
      (rdMap (fun x : ByteArray × List Ext => (⟨x.1, x.2⟩ : TableSt))
        (rdPair rdText (rdList (rdExt f))))
      TableSt.value fun _ => True :=
    cuts_map h0 _ (fun _ _ => rfl) (fun _ _ => trivial)
  exact cuts_of (cuts_if h1 (TableSt.ok f s)) (fun _ _ => rfl) (fun _ h => h.2)

/-- A table's item under a name (asked: the name is within the page's rule and has fewer than 2 ^ 64
bytes; ok: the table has the form, and the item's value has fewer than 2 ^ 64 bytes). -/
theorem undoes_tableItem (name : String) (h1 : okName name = true)
    (h2 : (ascii name).size < 2 ^ 64) (f : Fld) (s : TableShape) :
    Undoes (rdTableItem name f s) (fun t => tableItem name t.root t.answers) fun t =>
      t.ok f s = true ∧ t.value.size < 2 ^ 64 := by
  intro t ht
  exact undoes_named name h1 h2 (undoes_tableValue f s) t ⟨ht, ht.2⟩

/-- What the reader of a table's item accepts: a table with the form, whose item's value has fewer
than 2 ^ 64 bytes. -/
theorem cuts_tableItem (name : String) (f : Fld) (s : TableShape) :
    Cuts (rdTableItem name f s) (fun t => tableItem name t.root t.answers) fun t =>
      t.ok f s = true ∧ t.value.size < 2 ^ 64 :=
  cuts_of (cuts_named name (cuts_tableValue f s)) (fun _ _ => rfl) (fun _ h => h)

/-! ## 4. The other items -/

/-- An item whose value is 32 bytes (asked: the name is within the page's rule and has fewer than
2 ^ 64 bytes). -/
theorem undoes_digestItem (name : String) (h1 : okName name = true)
    (h2 : (ascii name).size < 2 ^ 64) :
    Undoes (rdNamed name rdDigest) (item name) fun x => x.size = 32 := by
  intro x hx
  have hx' : x.size = 32 := hx
  exact undoes_named name h1 h2 undoes_digest x ⟨hx, by show x.size < 2 ^ 64; omega⟩

/-- What its reader accepts is such an item. -/
theorem cuts_digestItem (name : String) :
    Cuts (rdNamed name rdDigest) (item name) fun x => x.size = 32 :=
  cuts_of (cuts_named name (cuts_of_only only_digest)) (fun _ _ => rfl) (fun _ h => h.1)

/-- The number of a stored copy is read back from its word. -/
theorem copyOf_toNat (c : UInt32) : copyOf c.toNat = some c := by
  unfold copyOf
  rw [if_pos c.toNat_lt, UInt32.ofNat_toNat]

/-- `copyOf` gives c at no number but c's own. -/
theorem toNat_of_copyOf (n : Nat) (c : UInt32) (h : copyOf n = some c) : c.toNat = n := by
  unfold copyOf at h
  by_cases hn : n < 2 ^ 32
  · rw [if_pos hn] at h
    obtain rfl := Option.some.inj h
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hn]
  · rw [if_neg hn] at h
    exact absurd h (by simp)

/-- The item "stored copy". -/
theorem undoes_copyItem :
    Undoes (rdNamed "stored copy" rdStoredCopy) (fun c : UInt32 => item
        "stored copy" (u64n c.toNat))
      fun _ => True := by
  intro c _
  have hc := c.toNat_lt
  exact undoes_named "stored copy" (by decide) (by decide) (undoes_enum UInt32.toNat copyOf) c
    ⟨⟨by omega, copyOf_toNat c⟩, by
      show (u64 (UInt64.ofNat c.toNat)).size < 2 ^ 64
      rw [size_u64]
      omega⟩

/-- What its reader accepts is such an item. -/
theorem cuts_copyItem :
    Cuts (rdNamed "stored copy" rdStoredCopy) (fun c : UInt32 => item "stored copy" (u64n c.toNat))
      fun _ => True :=
  cuts_of (cuts_named "stored copy" (cuts_of_only (only_enum UInt32.toNat copyOf toNat_of_copyOf)))
    (fun _ _ => rfl) (fun _ _ => trivial)

/-- A string of bytes is spelled with 8 bytes more. -/
theorem size_text (q : ByteArray) : (text q).size = 8 + q.size := by
  simp only [text, u64n, ByteArray.size_append, size_u64]

/-- The item "request": what it holds is spelled as a string of bytes, so that has at most
2 ^ 64 - 9 bytes. -/
theorem undoes_requestItem :
    Undoes (rdNamed "request" rdText) (fun q => item "request" (text q)) fun q =>
      q.size + 8 < 2 ^ 64 := by
  intro q hq
  have hq' : q.size + 8 < 2 ^ 64 := hq
  exact undoes_named "request" (by decide) (by decide) undoes_text q
    ⟨by show q.size < 2 ^ 64; omega, by rw [size_text]; omega⟩

/-- What its reader accepts is such an item, of a string of at most 2 ^ 64 - 9 bytes. -/
theorem cuts_requestItem :
    Cuts (rdNamed "request" rdText) (fun q => item "request" (text q)) fun q =>
      q.size + 8 < 2 ^ 64 :=
  cuts_of (cuts_named "request" (cuts_of_only only_text)) (fun _ _ => rfl) (fun q h => by
    have a : (text q).size < 2 ^ 64 := h.2
    rw [size_text] at a
    omega)

/-- The fourth item of a proof's first statement: its value is the request file's own bytes as a
string of bytes, so these are at most 2 ^ 64 - 9. -/
theorem undoes_wordsItem :
    Undoes (rdNamed wordsName rdText) (fun q => item wordsName (text q)) fun q =>
      q.size + 8 < 2 ^ 64 := by
  intro q hq
  have hq' : q.size + 8 < 2 ^ 64 := hq
  exact undoes_named wordsName (by decide) (by decide) undoes_text q
    ⟨by show q.size < 2 ^ 64; omega, by rw [size_text]; omega⟩

/-- What its reader accepts is such an item, of at most 2 ^ 64 - 9 bytes. -/
theorem cuts_wordsItem :
    Cuts (rdNamed wordsName rdText) (fun q => item wordsName (text q)) fun q =>
      q.size + 8 < 2 ^ 64 :=
  cuts_of (cuts_named wordsName (cuts_of_only only_text)) (fun _ _ => rfl) (fun q h => by
    have a : (text q).size < 2 ^ 64 := h.2
    rw [size_text] at a
    omega)

/-! ## 5. The statements' lengths -/

/-- The length of an item: two words, the name, the value. -/
theorem item_size_eq (name : String) (v : ByteArray) :
    (item name v).size = 16 + (ascii name).size + v.size := by
  simp only [item, textS, text, u64n, ByteArray.size_append, size_u64]
  omega

/-- The library's item of a seal has the name `sealName`. -/
theorem sealItem_name (x : ByteArray) : sealItem x = item sealName x := rfl

/-- Two seals' items as a pair. -/
theorem sealItems_two (s1 s2 : ByteArray) :
    sealItems [s1, s2] = pair (item sealName) (item sealName) (s1, s2) := by
  simp only [sealItems, List.map_cons, List.map_nil, cat_cons, cat_nil, ByteArray.append_empty,
    pair, sealItem_name]

/-- The statement of a proof's first chain as a pair of pairs, of the four fields that are hashed.
The fourth item's name in `ProofStm.bytes` (Fmt/Parsed.lean) is `wordsName`. -/
theorem ProofStm.bytes_pair (x : ProofStm) :
    x.bytes =
      pair (fun t : TableSt => tableItem "table" t.root t.answers)
        (pair (fun c : UInt32 => item "stored copy" (u64n c.toNat))
          (pair (fun q => item "request" (text q)) (fun q => item wordsName (text q))))
        x.hashed := by
  simp only [ProofStm.bytes, ProofStm.hashed, pair, TableSt.item, ByteArray.append_assoc,
    wordsName]

/-- The length of the statement of a key's one-time chain. -/
theorem TableSt.item_size (t : TableSt) : t.item.size = 21 + t.value.size := by
  show (Fmt.item "table" t.value).size = _
  have n : (ascii "table").size = 5 := by decide
  rw [item_size_eq, n]

/-- The length of the statement of a shared chain. -/
theorem sharedStm_size (t : TableSt) (r : ByteArray) :
    (sharedStm t r).size = 60 + t.value.size + r.size := by
  have n : (ascii bindRootName).size = 23 := by decide
  unfold sharedStm
  rw [ByteArray.size_append, TableSt.item_size, item_size_eq, n]
  omega

/-- The length of the statement of a second chain. -/
theorem sealItems_size (s1 s2 : ByteArray) :
    (sealItems [s1, s2]).size = 88 + s1.size + s2.size := by
  have n : (ascii sealName).size = 28 := by decide
  rw [sealItems_two]
  show (item sealName s1 ++ item sealName s2).size = _
  rw [ByteArray.size_append, item_size_eq, item_size_eq, n]
  omega

/-- The length of the statement of a proof's first chain. -/
theorem ProofStm.bytes_size (x : ProofStm) :
    x.bytes.size = 135 + x.table.value.size + x.request.size + x.words.size := by
  have n1 : (ascii "stored copy").size = 11 := by decide
  have n2 : (ascii "request").size = 7 := by decide
  have n3 : (u64n x.copy.toNat).size = 8 := rfl
  have n4 : (ascii wordsName).size = 24 := by decide
  unfold wordsName at n4
  unfold ProofStm.bytes
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_append, TableSt.item_size,
    item_size_eq, item_size_eq, item_size_eq, n1, n2, n3, n4, size_text, size_text]
  omega

/-- The length of the statement of an entry's link (`EntryStm.bytes`, Fmt/Parsed.lean). -/
theorem EntryStm.bytes_size (x : EntryStm) :
    x.bytes.size = 64 + x.first.value.size + x.further.value.size := by
  have n1 : (ascii "the first table").size = 15 := by decide
  have n2 : (ascii "the further table").size = 17 := by decide
  unfold EntryStm.bytes
  rw [tableItem_value, tableItem_value, ByteArray.size_append, item_size_eq, item_size_eq, n1, n2]
  omega

/-- The same for a table with the form: the number in the last clause of `ProofStm.ok`. -/
theorem ProofStm.bytes_size_ok (f : Fld) (s : TableShape) (x : ProofStm)
    (h : x.table.ok f s = true) :
    x.bytes.size = 183 + 24 * s.count + x.request.size + x.words.size := by
  rw [ProofStm.bytes_size, TableSt.value_size_ok f s x.table h]
  omega

/-- The same for two tables with the form: the number in `TableShape.fitsWord`. -/
theorem EntryStm.bytes_size_ok (f : Fld) (s : TableShape) (x : EntryStm)
    (h0 : x.first.ok f s = true) (h1 : x.further.ok f s = true) :
    x.bytes.size = 160 + 48 * s.count := by
  rw [EntryStm.bytes_size, TableSt.value_size_ok f s x.first h0,
    TableSt.value_size_ok f s x.further h1]
  omega

/-- Asked: `TableShape.fitsWord`. The statement of a key's one-time chain, of a table with the form,
has fewer than 2 ^ 64 bytes. -/
theorem TableSt.item_size_lt (f : Fld) (s : TableShape) (hs : s.fitsWord = true) (t : TableSt)
    (h : t.ok f s = true) : t.item.size < 2 ^ 64 := by
  have w := (TableShape.fitsWord_iff s).1 hs
  rw [TableSt.item_size, TableSt.value_size_ok f s t h]
  omega

/-- Asked: `TableShape.fitsWord`. The statement of a shared chain, of a table with the form and a
root of 32 bytes, has fewer than 2 ^ 64 bytes. -/
theorem sharedStm_size_lt (f : Fld) (s : TableShape) (hs : s.fitsWord = true) (t : TableSt)
    (r : ByteArray) (h : t.ok f s = true) (hr : r.size = 32) : (sharedStm t r).size < 2 ^ 64 := by
  have w := (TableShape.fitsWord_iff s).1 hs
  rw [sharedStm_size, TableSt.value_size_ok f s t h, hr]
  omega

/-! ## 6. The four statements: both laws in one -/

/-- A KEY's ONE-TIME CHAIN. The reader gives t on b exactly where t has the form, b has fewer than
2 ^ 64 bytes, and b is the statement written of t. -/
theorem TableSt.readItem_iff (f : Fld) (s : TableShape) (b : ByteArray) (t : TableSt) :
    TableSt.readItem f s b = some t ↔ (t.ok f s = true ∧ b.size < 2 ^ 64) ∧ b = t.item := by
  have h := wholeStm_both (undoes_tableItem "table" (by decide) (by decide) f s)
    (cuts_tableItem "table" f s) b t
  constructor
  · intro g
    obtain ⟨⟨⟨a, -⟩, c⟩, e⟩ := h.1 g
    exact ⟨⟨a, c⟩, e⟩
  · rintro ⟨⟨a, c⟩, e⟩
    have z := TableSt.item_size t
    rw [e] at c
    have v : t.value.size < 2 ^ 64 := by omega
    exact h.2 ⟨⟨⟨a, v⟩, by rw [e]; exact c⟩, e⟩

/-- A SHARED CHAIN. The reader gives t and r on b exactly where t has the form, r has 32 bytes, b
has fewer than 2 ^ 64 bytes, and b is the statement written of t and r. -/
theorem rdSharedStm_iff (f : Fld) (s : TableShape) (b : ByteArray) (t : TableSt) (r : ByteArray) :
    rdSharedStm f s b = some (t, r) ↔
      ((t.ok f s = true ∧ r.size = 32) ∧ b.size < 2 ^ 64) ∧ b = sharedStm t r := by
  have h := wholeStm_both
    (undoes_pair (undoes_tableItem "table" (by decide) (by decide) f s)
      (undoes_digestItem bindRootName (by decide) (by decide)))
    (cuts_pair (cuts_tableItem "table" f s) (cuts_digestItem bindRootName)) b (t, r)
  constructor
  · intro g
    obtain ⟨⟨⟨⟨a, -⟩, d⟩, c⟩, e⟩ := h.1 g
    exact ⟨⟨⟨a, d⟩, c⟩, e⟩
  · rintro ⟨⟨⟨a, d⟩, c⟩, e⟩
    have z := sharedStm_size t r
    rw [e] at c
    have v : t.value.size < 2 ^ 64 := by omega
    exact h.2 ⟨⟨⟨⟨a, v⟩, d⟩, by rw [e]; exact c⟩, e⟩

/-- A SECOND CHAIN. The reader gives s1 and s2 on b exactly where both have 32 bytes and b is the
statement written of them. (It has 152 bytes then.) -/
theorem rdSealItems_iff (b s1 s2 : ByteArray) :
    rdSealItems b = some (s1, s2) ↔ (s1.size = 32 ∧ s2.size = 32) ∧ b = sealItems [s1, s2] := by
  have z := sealItems_size s1 s2
  rw [sealItems_two] at z ⊢
  have h := wholeStm_both
    (undoes_pair (undoes_digestItem sealName (by decide) (by decide))
      (undoes_digestItem sealName (by decide) (by decide)))
    (cuts_pair (cuts_digestItem sealName) (cuts_digestItem sealName)) b (s1, s2)
  constructor
  · intro g
    exact ⟨(h.1 g).1.1, (h.1 g).2⟩
  · rintro ⟨⟨a, c⟩, e⟩
    exact h.2 ⟨⟨⟨a, c⟩, by rw [e, z]; omega⟩, e⟩

/-- A PROOF's FIRST CHAIN. The reader gives the four hashed fields of x on b exactly where the
table has the form, b has fewer than 2 ^ 64 bytes, and b is the statement written of x. (Every
such tuple is `ProofStm.hashed` of some x; the reply of x stands on neither side.) -/
theorem ProofStm.read_iff (f : Fld) (s : TableShape) (b : ByteArray) (x : ProofStm) :
    ProofStm.read f s b = some x.hashed ↔
      (x.table.ok f s = true ∧ b.size < 2 ^ 64) ∧ b = x.bytes := by
  have z := ProofStm.bytes_size x
  rw [ProofStm.bytes_pair] at z ⊢
  have h := wholeStm_both
    (undoes_pair (undoes_tableItem "table" (by decide) (by decide) f s)
      (undoes_pair undoes_copyItem (undoes_pair undoes_requestItem undoes_wordsItem)))
    (cuts_pair (cuts_tableItem "table" f s)
      (cuts_pair cuts_copyItem (cuts_pair cuts_requestItem cuts_wordsItem))) b x.hashed
  constructor
  · intro g
    obtain ⟨⟨⟨⟨a, -⟩, -⟩, c⟩, e⟩ := h.1 g
    exact ⟨⟨a, c⟩, e⟩
  · rintro ⟨⟨a, c⟩, e⟩
    have c' := c
    rw [e, z] at c'
    have v : x.table.value.size < 2 ^ 64 := by omega
    have q : x.request.size + 8 < 2 ^ 64 := by omega
    have w : x.words.size + 8 < 2 ^ 64 := by omega
    exact h.2 ⟨⟨⟨⟨a, v⟩, trivial, q, w⟩, c⟩, e⟩

/-! ## 7. "read (bytes x) = some x exactly where ok x" -/

/-- A KEY's ONE-TIME CHAIN, without a premise. From the statement written of t the reader gives t
back exactly where t has the form `TableSt.ok` and the statement's length, 69 + 24 for each answer,
is below 2 ^ 64. -/
theorem TableSt.readItem_item_iff (f : Fld) (s : TableShape) (t : TableSt) :
    TableSt.readItem f s t.item = some t ↔ t.ok f s = true ∧ 69 + 24 * s.count < 2 ^ 64 := by
  rw [TableSt.readItem_iff]
  constructor
  · rintro ⟨⟨a, c⟩, -⟩
    rw [TableSt.item_size, TableSt.value_size_ok f s t a] at c
    exact ⟨a, by omega⟩
  · rintro ⟨a, c⟩
    refine ⟨⟨a, ?_⟩, rfl⟩
    rw [TableSt.item_size, TableSt.value_size_ok f s t a]
    omega

/-- A KEY's ONE-TIME CHAIN. Asked: `TableShape.fitsWord`. From the statement written of t the reader
gives t back exactly where t has the form `TableSt.ok`. -/
theorem TableSt.readItem_item (f : Fld) (s : TableShape) (hs : s.fitsWord = true) (t : TableSt) :
    TableSt.readItem f s t.item = some t ↔ t.ok f s = true := by
  have w := (TableShape.fitsWord_iff s).1 hs
  rw [TableSt.readItem_item_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, by omega⟩⟩

/-- A SHARED CHAIN, without a premise. From the statement written of t and r the reader gives them
back exactly where t has the form `TableSt.ok`, r has 32 bytes, and the statement's length, 140 + 24
for each answer, is below 2 ^ 64. -/
theorem rdSharedStm_bytes_iff (f : Fld) (s : TableShape) (t : TableSt) (r : ByteArray) :
    rdSharedStm f s (sharedStm t r) = some (t, r) ↔
      (t.ok f s = true ∧ r.size = 32) ∧ 140 + 24 * s.count < 2 ^ 64 := by
  rw [rdSharedStm_iff]
  constructor
  · rintro ⟨⟨a, c⟩, -⟩
    rw [sharedStm_size, TableSt.value_size_ok f s t a.1, a.2] at c
    exact ⟨a, by omega⟩
  · rintro ⟨a, c⟩
    refine ⟨⟨a, ?_⟩, rfl⟩
    rw [sharedStm_size, TableSt.value_size_ok f s t a.1, a.2]
    omega

/-- A SHARED CHAIN. Asked: `TableShape.fitsWord`. From the statement written of t and r the reader
gives them back exactly where t has the form `TableSt.ok` and r has 32 bytes. -/
theorem rdSharedStm_bytes (f : Fld) (s : TableShape) (hs : s.fitsWord = true) (t : TableSt)
    (r : ByteArray) :
    rdSharedStm f s (sharedStm t r) = some (t, r) ↔ t.ok f s = true ∧ r.size = 32 := by
  have w := (TableShape.fitsWord_iff s).1 hs
  rw [rdSharedStm_bytes_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, by omega⟩⟩

/-- A SECOND CHAIN. From the statement written of two seals the reader gives them back exactly where
both have 32 bytes. -/
theorem rdSealItems_bytes (s1 s2 : ByteArray) :
    rdSealItems (sealItems [s1, s2]) = some (s1, s2) ↔ s1.size = 32 ∧ s2.size = 32 := by
  rw [rdSealItems_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩

/-- A PROOF's FIRST CHAIN. No premise. From the statement written of x the reader gives the four
hashed fields back exactly where the table has the form `TableSt.ok` and the last clause of
`ProofStm.ok` holds. -/
theorem ProofStm.read_bytes (f : Fld) (s : TableShape) (x : ProofStm) :
    ProofStm.read f s x.bytes = some x.hashed ↔
      x.table.ok f s = true ∧ 183 + 24 * s.count + x.request.size + x.words.size < 2 ^ 64 := by
  rw [ProofStm.read_iff]
  constructor
  · rintro ⟨⟨a, c⟩, -⟩
    rw [ProofStm.bytes_size_ok f s x a] at c
    exact ⟨a, c⟩
  · rintro ⟨a, c⟩
    exact ⟨⟨a, by rw [ProofStm.bytes_size_ok f s x a]; exact c⟩, rfl⟩

/-- `sealsOk` as three statements. -/
theorem sealsOk_iff (s1 r s2 : ByteArray) :
    sealsOk s1 r s2 = true ↔ s1.size = 32 ∧ r.size = 32 ∧ s2.size = 32 := by
  simp only [sealsOk, Bool.and_eq_true, beq_iff_eq, and_assoc]

/-- `ProofStm.ok` as three statements. -/
theorem ProofStm.ok_iff (D : Declared) (x : ProofStm) :
    x.ok D = true ↔
      x.table.ok D.setting.field D.table = true ∧ D.setting.field.okE x.reply = true ∧
        183 + 24 * D.table.count + x.request.size + x.words.size < 2 ^ 64 := by
  simp only [ProofStm.ok, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- Asked: r has 32 bytes. For x with the form `ProofStm.ok`, the shared chain's statement has fewer
than 2 ^ 64 bytes too: it has 140 and 24 for each answer, the first chain's at least 183 and 24 for
each answer. -/
theorem ProofStm.sharedStm_size_lt (D : Declared) (x : ProofStm) (r : ByteArray)
    (hx : x.ok D = true) (hr : r.size = 32) :
    (sharedStm x.table r).size < 2 ^ 64 := by
  obtain ⟨a, -, c⟩ := (ProofStm.ok_iff D x).1 hx
  rw [sharedStm_size, TableSt.value_size_ok _ _ x.table a, hr]
  omega

/-- THE THREE CHAINS OF A KEY FILE. Asked: `TableShape.fitsWord`. Each chain's reader gives back,
from that chain's statement, the values of which it was written, exactly where the table has its
form and the two seals and the binding tree's root have 32 bytes. -/
theorem keyStmAt_read (f : Fld) (s : TableShape) (hs : s.fitsWord = true) (t : TableSt)
    (s1 r s2 : ByteArray) :
    (TableSt.readItem f s (keyStmAt t s1 r s2 .first) = some t ∧
      rdSharedStm f s (keyStmAt t s1 r s2 .shared) = some (t, r) ∧
      rdSealItems (keyStmAt t s1 r s2 .second) = some (s1, s2)) ↔
      t.ok f s = true ∧ sealsOk s1 r s2 = true := by
  show (TableSt.readItem f s t.item = some t ∧ rdSharedStm f s (sharedStm t r) = some (t, r) ∧
    rdSealItems (sealItems [s1, s2]) = some (s1, s2)) ↔ _
  rw [TableSt.readItem_item f s hs, rdSharedStm_bytes f s hs, rdSealItems_bytes, sealsOk_iff]
  exact ⟨fun h => ⟨h.1, h.2.2.1, h.2.1.2, h.2.2.2⟩, fun h => ⟨h.1, ⟨h.1, h.2.2.1⟩, h.2.1, h.2.2.2⟩⟩

/-- THE THREE CHAINS OF A PROOF FILE. Nothing is asked. Each chain's reader gives back, from that
chain's statement, the values of which it was written, and the reply is canonical, exactly where x
has its form and the two seals and the binding tree's root have 32 bytes. The reply is in no
statement: its clause of `ProofStm.ok` stands on the left side as it is. -/
theorem proofStmAt_read (D : Declared) (x : ProofStm) (s1 r s2 : ByteArray) :
    ((ProofStm.read D.setting.field D.table (proofStmAt x s1 r s2 .first) = some x.hashed ∧
      rdSharedStm D.setting.field D.table (proofStmAt x s1 r s2 .shared) = some (x.table, r) ∧
      rdSealItems (proofStmAt x s1 r s2 .second) = some (s1, s2)) ∧
      D.setting.field.okE x.reply = true) ↔
      x.ok D = true ∧ sealsOk s1 r s2 = true := by
  show ((ProofStm.read D.setting.field D.table x.bytes = some x.hashed ∧
    rdSharedStm D.setting.field D.table (sharedStm x.table r) = some (x.table, r) ∧
    rdSealItems (sealItems [s1, s2]) = some (s1, s2)) ∧ _) ↔ _
  rw [ProofStm.read_bytes, rdSharedStm_bytes_iff, rdSealItems_bytes, sealsOk_iff,
    ProofStm.ok_iff]
  exact ⟨fun h => ⟨⟨h.1.1.1, h.2, h.1.1.2⟩, h.1.2.2.1, h.1.2.1.1.2, h.1.2.2.2⟩,
    fun h => ⟨⟨⟨h.1.1, h.1.2.2⟩, ⟨⟨h.1.1, h.2.2.1⟩, by have := h.1.2.2; omega⟩, h.2.1, h.2.2.2⟩,
      h.1.2.1⟩⟩

/-- What the reader of a shared chain's statement gives is what the library's readers of a
statement's items take out of the same string: the root in item 0 (`itemRoot`, Fmt/Rules8X.lean) and
the value of item 1 (`itemValue`, Fmt/Parsed.lean). Over `sharedStm_root`,
`sharedStm_item`. -/
theorem rdSharedStm_items (f : Fld) (s : TableShape) (b : ByteArray) (t : TableSt) (r : ByteArray)
    (h : rdSharedStm f s b = some (t, r)) :
    itemRoot b 0 = some t.root ∧ itemValue b 1 = some r := by
  obtain ⟨⟨⟨-, d⟩, c⟩, rfl⟩ := (rdSharedStm_iff f s b t r).1 h
  rw [sharedStm_size] at c
  exact ⟨sharedStm_root t r (by omega) (by omega), sharedStm_item t r (by omega) (by omega)⟩

/-! ## 8. One-to-one on what has the form -/

/-- For a table with the form, under a shape with `TableShape.fitsWord`: the frame's ok. -/
theorem TableSt.ok_fits (f : Fld) (s : TableShape) (hs : s.fitsWord = true) (t : TableSt)
    (h : t.ok f s = true) : t.ok f s = true ∧ t.value.size < 2 ^ 64 := by
  have w := (TableShape.fitsWord_iff s).1 hs
  refine ⟨h, ?_⟩
  rw [TableSt.value_size_ok f s t h]
  omega

/-- Asked: `TableShape.fitsWord`. Two tables with the form, under one field and one shape, and the
same item "table" are the same. -/
theorem TableSt.item_inj (f : Fld) (s : TableShape) (hs : s.fitsWord = true) (t u : TableSt)
    (ht : t.ok f s = true) (hu : u.ok f s = true) (e : t.item = u.item) : t = u :=
  inj_of_undoes (undoes_tableItem "table" (by decide) (by decide) f s) t u
    (TableSt.ok_fits f s hs t ht) (TableSt.ok_fits f s hs u hu) e

/-- Asked: `TableShape.fitsWord`. The same for a shared chain's statement, of two tables with the
form and two roots of 32 bytes. -/
theorem sharedStm_inj (f : Fld) (s : TableShape) (hs : s.fitsWord = true) (t u : TableSt)
    (r q : ByteArray) (ht : t.ok f s = true) (hu : u.ok f s = true) (hr : r.size = 32)
    (hq : q.size = 32) (e : sharedStm t r = sharedStm u q) : t = u ∧ r = q := by
  have a := inj_of_undoes
    (undoes_pair (undoes_tableItem "table" (by decide) (by decide) f s)
      (undoes_digestItem bindRootName (by decide) (by decide)))
    (t, r) (u, q) ⟨TableSt.ok_fits f s hs t ht, hr⟩ ⟨TableSt.ok_fits f s hs u hu, hq⟩ e
  exact ⟨congrArg Prod.fst a, congrArg Prod.snd a⟩

/-- The same for a second chain's statement, of seals of 32 bytes. -/
theorem sealItems_inj (s1 s2 u1 u2 : ByteArray) (h1 : s1.size = 32) (h2 : s2.size = 32)
    (g1 : u1.size = 32) (g2 : u2.size = 32) (e : sealItems [s1, s2] = sealItems [u1, u2]) :
    s1 = u1 ∧ s2 = u2 := by
  rw [sealItems_two, sealItems_two] at e
  have a := inj_of_undoes
    (undoes_pair (undoes_digestItem sealName (by decide) (by decide))
      (undoes_digestItem sealName (by decide) (by decide)))
    (s1, s2) (u1, u2) ⟨h1, h2⟩ ⟨g1, g2⟩ e
  exact ⟨congrArg Prod.fst a, congrArg Prod.snd a⟩

/-- Two values with the form `ProofStm.ok`, under one declared structure, and the same statement
have the same table, number of the stored copy, value of the item "request" and bytes of the request
file. No premise on the shape. Of the replies nothing follows. -/
theorem ProofStm.bytes_inj (D : Declared) (x y : ProofStm) (hx : x.ok D = true)
    (hy : y.ok D = true) (e : x.bytes = y.bytes) : x.hashed = y.hashed := by
  obtain ⟨a1, -, a3⟩ := (ProofStm.ok_iff D x).1 hx
  obtain ⟨c1, -, c3⟩ := (ProofStm.ok_iff D y).1 hy
  have a := (ProofStm.read_bytes _ _ x).2 ⟨a1, a3⟩
  rw [e, (ProofStm.read_bytes _ _ y).2 ⟨c1, c3⟩] at a
  exact (Option.some.inj a).symm

/-- The statement does not hang on the reply. -/
theorem ProofStm.bytes_reply (x : ProofStm) (e : Ext) :
    ({ x with reply := e } : ProofStm).bytes = x.bytes := rfl

/-- The same statement: the same field `words`, which is to hold the request file's bytes (whoever
builds x fills it: nothing here holds it against a file). Asked: both values have the form, under
one declared structure. No hash stands in this law. -/
theorem ProofStm.bytes_words (D : Declared) (x y : ProofStm) (hx : x.ok D = true)
    (hy : y.ok D = true) (e : x.bytes = y.bytes) : x.words = y.words :=
  congrArg (fun z => z.2.2.2) (ProofStm.bytes_inj D x y hx hy e)

/-- With the item "request"'s value (`request`) and the request file's own bytes (`words`) in each
other's places the statement is another, unless the two are one string. Both fields are strings of
bytes: the types do not catch such a swap. -/
theorem ProofStm.bytes_swap (D : Declared) (x : ProofStm) (hx : x.ok D = true)
    (e : ({ x with request := x.words, words := x.request } : ProofStm).bytes = x.bytes) :
    x.request = x.words := by
  have hy : ({ x with request := x.words, words := x.request } : ProofStm).ok D = true := by
    obtain ⟨a, b, c⟩ := (ProofStm.ok_iff D x).1 hx
    refine (ProofStm.ok_iff D _).2 ⟨a, b, ?_⟩
    show 183 + 24 * D.table.count + x.words.size + x.request.size < 2 ^ 64
    omega
  exact ProofStm.bytes_words D _ x hy hx e

/-! ## 9. The first item's name; a first chain's statement against a shared chain's -/

/-- The name of an item at the beginning of a string (asked: the item is within the library's
bounds, `okItem`). -/
theorem firstName_item (name : String) (v post : ByteArray) (h : okItem (name, v)) :
    firstName (item name v ++ post) = some name := by
  have a := undoes_item (name, v) h ByteArray.empty post
  rw [ByteArray.empty_append, ByteArray.size_empty] at a
  have a' : rdItem (item name v ++ post) 0 = some ((name, v), 0 + (item name v).size) := a
  unfold firstName
  rw [a']
  rfl

/-- An item "table" within the library's bounds. -/
theorem okItem_table (v : ByteArray) (h : v.size < 2 ^ 64) : okItem ("table", v) :=
  ⟨(by decide : okName "table" = true), (by decide : (ascii "table").size < 2 ^ 64), h⟩

/-- An item of a seal within the library's bounds. -/
theorem okItem_seal (v : ByteArray) (h : v.size < 2 ^ 64) : okItem (sealName, v) :=
  ⟨(by decide : okName sealName = true), (by decide : (ascii sealName).size < 2 ^ 64), h⟩

/-- The first item's name in the statements of a key file's chains. Asked: the value of the table's
item and the first seal have fewer than 2 ^ 64 bytes. -/
theorem keyStmAt_firstName (t : TableSt) (s1 r s2 : ByteArray) (ht : t.value.size < 2 ^ 64)
    (h1 : s1.size < 2 ^ 64) (w : Which) :
    firstName (keyStmAt t s1 r s2 w) = some w.firstName := by
  cases w with
  | first =>
    show firstName t.item = some "table"
    rw [← ByteArray.append_empty (b := t.item)]
    exact firstName_item "table" t.value _ (okItem_table t.value ht)
  | shared => exact firstName_item "table" t.value _ (okItem_table t.value ht)
  | second =>
    show firstName (sealItems [s1, s2]) = some sealName
    rw [sealItems_two]
    exact firstName_item sealName s1 _ (okItem_seal s1 h1)

/-- The same for a proof file's chains, with the same two premises. -/
theorem proofStmAt_firstName (x : ProofStm) (s1 r s2 : ByteArray)
    (ht : x.table.value.size < 2 ^ 64) (h1 : s1.size < 2 ^ 64) (w : Which) :
    firstName (proofStmAt x s1 r s2 w) = some w.firstName := by
  cases w with
  | first =>
    show firstName x.bytes = some "table"
    rw [ProofStm.bytes_pair]
    exact firstName_item "table" x.table.value _ (okItem_table x.table.value ht)
  | shared => exact firstName_item "table" x.table.value _ (okItem_table x.table.value ht)
  | second =>
    show firstName (sealItems [s1, s2]) = some sealName
    rw [sealItems_two]
    exact firstName_item sealName s1 _ (okItem_seal s1 h1)

/-- Of the three names (`Which.firstName`), the second chain's is its own. With the two theorems
above: the first item's name tells a second chain's statement from the two others. -/
theorem Which.firstName_second (w : Which) :
    w.firstName = Which.second.firstName ↔ w = .second := by
  cases w <;> decide

/-- The first chain's and the shared chain's are one name: the first item's name does not tell
these two statements apart. -/
theorem Which.firstName_first : Which.first.firstName = Which.shared.firstName := rfl

/-- In a key file the shared chain's statement is the first chain's with one item more. -/
theorem keyStmAt_shared (t : TableSt) (s1 r s2 : ByteArray) :
    keyStmAt t s1 r s2 .shared = keyStmAt t s1 r s2 .first ++ item bindRootName r := rfl

/-- The statement of a key's one-time chain is no shared chain's statement, of whatever two tables
with the form under one field and one shape, and whatever r: the second is longer. -/
theorem TableSt.item_ne_sharedStm (f : Fld) (s : TableShape) (t u : TableSt) (r : ByteArray)
    (ht : t.ok f s = true) (hu : u.ok f s = true) : t.item ≠ sharedStm u r := by
  intro e
  have a := congrArg ByteArray.size e
  rw [TableSt.item_size, sharedStm_size, TableSt.value_size_ok f s t ht,
    TableSt.value_size_ok f s u hu] at a
  omega

/-- Asked: r has fewer than 2 ^ 64 bytes. The statement of a proof's first chain is no shared
chain's statement, of whatever two tables with the form under one field and one shape: the two items
"table" have one length, and behind them the names differ. Over the library's `append_cancel`
(Fmt/Rules23In.lean). -/
theorem ProofStm.bytes_ne_sharedStm (f : Fld) (s : TableShape) (x : ProofStm) (u : TableSt)
    (r : ByteArray) (hx : x.table.ok f s = true) (hu : u.ok f s = true) (hr : r.size < 2 ^ 64) :
    x.bytes ≠ sharedStm u r := by
  intro e
  rw [ProofStm.bytes_pair] at e
  have e' : x.table.item ++
      (Fmt.item "stored copy" (u64n x.copy.toNat) ++
        (Fmt.item "request" (text x.request) ++ Fmt.item wordsName (text x.words))) =
      u.item ++ Fmt.item bindRootName r := e
  have z : x.table.item.size = u.item.size := by
    rw [TableSt.item_size, TableSt.item_size, TableSt.value_size_ok f s x.table hx,
      TableSt.value_size_ok f s u hu]
  have a := (append_cancel _ _ _ _ z e').2
  have n1 := firstName_item "stored copy" (u64n x.copy.toNat)
    (Fmt.item "request" (text x.request) ++ Fmt.item wordsName (text x.words))
    ⟨(by decide : okName "stored copy" = true),
      (by decide : (ascii "stored copy").size < 2 ^ 64), (by decide : 8 < 2 ^ 64)⟩
  have n2 := firstName_item bindRootName r ByteArray.empty
    ⟨(by decide : okName bindRootName = true),
      (by decide : (ascii bindRootName).size < 2 ^ 64), hr⟩
  rw [ByteArray.append_empty] at n2
  rw [a, n2] at n1
  exact absurd n1 (by decide)

end Fmt

#print axioms Fmt.toNat_ofNat_byte
#print axioms Fmt.byte_of_isName
#print axioms Fmt.toList_nameOf
#print axioms Fmt.okName_nameOf
#print axioms Fmt.ascii_nameOf
#print axioms Fmt.only_rdItem
#print axioms Fmt.undoes_if
#print axioms Fmt.cuts_if
#print axioms Fmt.undoes_named
#print axioms Fmt.cuts_named
#print axioms Fmt.whole_both
#print axioms Fmt.wholeStm_both
#print axioms Fmt.size_exts
#print axioms Fmt.TableSt.value_size
#print axioms Fmt.TableSt.ok_iff
#print axioms Fmt.TableShape.fitsWord_iff
#print axioms Fmt.TableShape.fitsWord_of_ok
#print axioms Fmt.TableSt.value_size_ok
#print axioms Fmt.one_le_ext
#print axioms Fmt.undoes_tableRaw
#print axioms Fmt.undoes_tableValue
#print axioms Fmt.cuts_tableValue
#print axioms Fmt.undoes_tableItem
#print axioms Fmt.cuts_tableItem
#print axioms Fmt.undoes_digestItem
#print axioms Fmt.cuts_digestItem
#print axioms Fmt.copyOf_toNat
#print axioms Fmt.toNat_of_copyOf
#print axioms Fmt.undoes_copyItem
#print axioms Fmt.cuts_copyItem
#print axioms Fmt.size_text
#print axioms Fmt.undoes_requestItem
#print axioms Fmt.cuts_requestItem
#print axioms Fmt.undoes_wordsItem
#print axioms Fmt.cuts_wordsItem
#print axioms Fmt.item_size_eq
#print axioms Fmt.sealItem_name
#print axioms Fmt.sealItems_two
#print axioms Fmt.ProofStm.bytes_pair
#print axioms Fmt.TableSt.item_size
#print axioms Fmt.sharedStm_size
#print axioms Fmt.sealItems_size
#print axioms Fmt.ProofStm.bytes_size
#print axioms Fmt.EntryStm.bytes_size
#print axioms Fmt.ProofStm.bytes_size_ok
#print axioms Fmt.EntryStm.bytes_size_ok
#print axioms Fmt.TableSt.item_size_lt
#print axioms Fmt.sharedStm_size_lt
#print axioms Fmt.TableSt.readItem_iff
#print axioms Fmt.rdSharedStm_iff
#print axioms Fmt.rdSealItems_iff
#print axioms Fmt.ProofStm.read_iff
#print axioms Fmt.TableSt.readItem_item_iff
#print axioms Fmt.TableSt.readItem_item
#print axioms Fmt.rdSharedStm_bytes_iff
#print axioms Fmt.rdSharedStm_bytes
#print axioms Fmt.rdSealItems_bytes
#print axioms Fmt.ProofStm.read_bytes
#print axioms Fmt.sealsOk_iff
#print axioms Fmt.ProofStm.ok_iff
#print axioms Fmt.ProofStm.sharedStm_size_lt
#print axioms Fmt.keyStmAt_read
#print axioms Fmt.proofStmAt_read
#print axioms Fmt.rdSharedStm_items
#print axioms Fmt.TableSt.ok_fits
#print axioms Fmt.TableSt.item_inj
#print axioms Fmt.sharedStm_inj
#print axioms Fmt.sealItems_inj
#print axioms Fmt.ProofStm.bytes_inj
#print axioms Fmt.ProofStm.bytes_reply
#print axioms Fmt.ProofStm.bytes_words
#print axioms Fmt.ProofStm.bytes_swap
#print axioms Fmt.firstName_item
#print axioms Fmt.okItem_table
#print axioms Fmt.okItem_seal
#print axioms Fmt.keyStmAt_firstName
#print axioms Fmt.proofStmAt_firstName
#print axioms Fmt.Which.firstName_second
#print axioms Fmt.Which.firstName_first
#print axioms Fmt.keyStmAt_shared
#print axioms Fmt.TableSt.item_ne_sharedStm
#print axioms Fmt.ProofStm.bytes_ne_sharedStm
