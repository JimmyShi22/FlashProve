-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/ParsedReadLaws.lean: for one chain, without a hash: the reader by the numbers
(Fmt/ParsedRead.lean) and the writer `ChainParsed.bytes` (Fmt/Parsed.lean) are inverse to each other
on the records that fit, once the numbers are given. So the bytes and the numbers fix the record:
the statement `Spec.bytes_inj` of Fmt/ParsedLaws.lean, proved.

A parsed record holds what stands in a file (Fmt/ParsedTypes.lean). A file has no lengths in it: how
many positions a round lists, and how many columns and given digests an opening has, follows from
the draws. So "reading the written bytes gives the record back", for every record that fits, is true
only of a reader that is told these numbers (`ChainParsed.counts`): two records that fit one
declared chain can have the same bytes and other numbers (a test in Fmt/ParsedReadKnown.lean
[not in this library]; so here read: not tested in this library). With the numbers it is true, and
it is proved here, for an opening, for a round and for a chain, at any place in a longer string. In
these laws the numbers are the record's own: the reader is handed the lengths of its answer.

How: by the library's frame for "a reader undoes a spelling, whatever stands before and behind"
(`Undoes`, Fmt/Rules1Laws.lean), part by part. The numbers are fixed first: the law of a part says
that the reader at the numbers n undoes the writer on the values that fit and have the numbers n.
The other law goes by the frame of Fmt/Rules1Only.lean (`Only`) without its clause "the place behind
is inside the string" (`Cuts`), since a part without a byte is read at every place. No Mathlib,
neither directly nor through the imports.

1. What the file contains. Theorems; four small definitions for them (`spNonce`, `okNonce`,
`okRand`, `Cuts`).

2. What is checked when the file compiles. The proofs. Tests: Fmt/ParsedReadKnown.lean
[not in this library]; so here read: not tested in this library.

3. Theorems.
   The frame: `undoes_map`, `undoes_give`, `rdFit_some`, `rdFit_of`, `undoes_fit` (a reader under a
     test), `undoes_count`, `zip_back`, `undoes_zip`; `mem_zip_swap`.
   `zipLoop_eq`, `rdZipL_eq`: the loop by which a chain's rounds and a round's openings are read is
     `rdZip`, of which the laws are proved.
   n low bytes: `leNat_of`, `byteAt_u64`, `size_lowBytes`, `byteAt_lowBytes`, `lt_word`,
     `undoes_readLE`, `undoes_low` (asked: n is at most 8; ok: below 256 ^ n).
   `undoes_column`, `undoes_open`: an opening (ok: it fits, and has the numbers n).
   `lt_of_okE`, `undoes_got`, `undoes_items`, `undoes_nonce`, `undoes_round`: a round (asked: the
     plan under which it is written has the setting's two widths, and both are at most 8; ok: it
     fits the declared round, and has the numbers n).
   `undoes_rand`, `undoes_chain`: a chain (asked: the same; ok: it fits the declared chain, and has
     the numbers N).
   `ChainParsed.read_bytes`: the same, said of one chain X at its own numbers.
     `Declared.read_bytes`: at a declared structure, where the two widths agree by definition.
   `ChainParsed.readFit_bytes`: the reader that tests the form gives X back at X's own numbers
     exactly where X fits. (The half "only where X fits" holds because that reader tests `fits`.)
   `bytes_inj`: `Spec.bytes_inj`: one string, with numbers, is the writing of at most one record
     that fits.
   The other law. The frame: `cuts_of_only`, `cuts_of`, `cuts_map`, `cuts_give`, `cuts_pair`,
     `cuts_count`, `cuts_zip`, `cuts_fit`; `extract_same`, `le_of_cut`; on a whole string:
     `whole_cuts`, `whole_iff_both`.
   n low bytes: `leNat_lt`, `leNat_digit`, `byteAt_extract`, `lowBytes_leNat`, `only_readLE`,
     `cuts_low` (asked: n is at most 8).
   `cuts_column`, `cuts_open`, `okE_of_lt`, `cuts_got`, `cuts_items`, `cuts_nonceAt`, `cuts_round`,
     `cuts_rand`, `cuts_chain`: what a reader accepts at given numbers has these numbers, and its
     writing is the bytes that were read (asked for a round and a chain: the two widths, as above).
     Of an opening, an item, a message and a nonce also: it has the form that `fits` asks of it,
     but for the bounds on an opening's number of columns.
   `cuts_chainFit`: the same of the reader that tests the form; what it accepts fits too.
   `ChainParsed.readFit_iff`, `Declared.readFit_iff`: both laws in one. At a place i up to the end
     of b: readFit S c N b i = some (X, j) exactly where X fits c, has the numbers N, j is i + the
     number of X's bytes, j is at most b's length, and b's bytes from i to j are X's.

4. What is not claimed.
   The laws speak of ONE CHAIN, under a setting, a plan's two widths, a declared chain and numbers.
   A file's head, table and slot are in no chain: the readers and laws of a file's record
   (`EntryParsed`, `KeyParsed`, `ProofParsed`) are in Fmt/ParsedReadFile.lean and
   Fmt/ParsedReadFileLaws.lean. No law is stated with the declared structure alone: without the
   numbers it is false.
   A declared round's message is cut into answers, roots and elements of E alone, in this order
   (`Entry.cut`, `DeclaredRound.items`, Decl/Declared.lean). So the laws of a round and of a chain,
   which speak of declared rounds, say nothing of a message with an element of F or a plain word, or
   in another order. The laws of an item and of a message (`undoes_got`, `undoes_items`, `cuts_got`,
   `cuts_items`) hold for every cut.
   Which numbers are the right ones is not said here: they are given to the reader, not derived. A
   converter that picks other numbers can get another fitting record of the same bytes. For the
   numbers of the lenient cut, which draws with the hash: Run/ParsedCutLaws.lean
   [not in this library]; so here read: not proved in this library.
   `bytes_inj` says that one string with numbers has at most one fitting record. It does not say
   that two files give two typed proofs: that needs that a file's record, written back, is the file
   (for the lenient cut: `cut_back`, Run/ParsedCutLaws.lean [not in this library]), and that the
   step from a record to the typed value is one-to-one on fitting records, of which nothing is said
   anywhere here.
   Of `ChainParsed.read`, which does not test the whole form, the other law gives the numbers and
   the bytes alone: it can accept a record that does not fit (an opening without a column, listed
   positions that do not increase).
   One string can be read at several numbers, each time as another record.
   The two bounds (at most eight bytes) are needed for the reader's laws (two tests). For
   `bytes_inj` they are more than is needed: above eight the writer writes a word's eight bytes.
   `fits` does not test the declared chain, and neither do these laws: they hold for every setting
   with the two bounds and every declared chain, also for one that no public files give. The test
   on a declared structure that gives the two bounds is `Declared.settingOk` (Fmt/Parsed.lean;
   `Declared.bounds`, Fmt/ParsedReadFileLaws.lean).
   Nothing on soundness follows: no verifier calls this reader, and a record is a converter's value.
   The other law of a message's items stands a second time in this library, for the compiler's side
   and over Mathlib (Run/PageIsChain.lean: `only_item`, `items_only`, `extract_self`). Files of
   Fmt/ import no such file.

Terms: lean/GLOSSARY.md.

-/
import Fmt.ParsedRead
import Fmt.ParsedLaws
import Fmt.Rules1Only

namespace Fmt

/-! ## 1. The frame: three more ways to get one law from another -/

/-- From a law to the law of the turned reader: g takes a value apart, f puts it together. -/
theorem undoes_map {α β : Type} {r : Rd α} {sp : α → ByteArray} {ok : α → Prop}
    (h : Undoes r sp ok) (f : α → β) (g : β → α) {sp' : β → ByteArray} {ok' : β → Prop}
    (hf : ∀ y, ok' y → f (g y) = y) (hs : ∀ y, ok' y → sp' y = sp (g y))
    (ho : ∀ y, ok' y → ok (g y)) : Undoes (rdMap f r) sp' ok' := by
  intro y hy pre post
  show (r (pre ++ sp' y ++ post) pre.size).map (fun x => (f x.1, x.2)) = _
  rw [hs y hy, h (g y) (ho y hy) pre post]
  simp only [Option.map_some, hf y hy]

/-- The reader that reads no byte undoes the spelling without a byte. -/
theorem undoes_give {α : Type} (x : α) :
    Undoes (rdGive x) (fun _ => ByteArray.empty) fun y => y = x := by
  intro y hy pre post
  subst hy
  show some (y, pre.size) = some (y, pre.size + ByteArray.empty.size)
  rw [ByteArray.size_empty, Nat.add_zero]

/-- What a reader under a test gives passes the test, and the reader itself gives it. -/
theorem rdFit_some {α : Type} {fit : α → Bool} {r : Rd α} {b : ByteArray} {i j : Nat} {x : α}
    (h : rdFit fit r b i = some (x, j)) : fit x = true ∧ r b i = some (x, j) := by
  unfold rdFit at h
  rcases h1 : r b i with _ | ⟨y, k⟩
  · rw [h1] at h
    exact absurd h (by simp)
  · rw [h1] at h
    simp only at h
    by_cases hf : fit y = true
    · rw [if_pos hf] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨hf, rfl⟩
    · rw [if_neg hf] at h
      exact absurd h (by simp)

/-- What a reader gives, and passes the test, the reader under the test gives. -/
theorem rdFit_of {α : Type} {fit : α → Bool} {r : Rd α} {b : ByteArray} {i j : Nat} {x : α}
    (h : r b i = some (x, j)) (hf : fit x = true) : rdFit fit r b i = some (x, j) := by
  unfold rdFit
  rw [h]
  simp only
  rw [if_pos hf]

/-- A reader under a test still undoes the spelling, where ok gives the test. -/
theorem undoes_fit {α : Type} {r : Rd α} {sp : α → ByteArray} {ok : α → Prop} (fit : α → Bool)
    (h : Undoes r sp ok) (hf : ∀ x, ok x → fit x = true) : Undoes (rdFit fit r) sp ok :=
  fun x hx pre post => rdFit_of (h x hx pre post) (hf x hx)

/-- `undoes_many` in the frame's own form: n values. -/
theorem undoes_count {α : Type} {r : Rd α} {sp : α → ByteArray} {ok : α → Prop}
    (h : Undoes r sp ok) (n : Nat) :
    Undoes (rdMany r n) (fun l => cat (l.map sp)) fun l => l.length = n ∧ ∀ x ∈ l, ok x := by
  intro l hl pre post
  obtain ⟨rfl, h2⟩ := hl
  exact undoes_many h l h2 pre post

/-- A list of values, each by its own reader: what `rdZip` gives at the values' own numbers. -/
theorem zip_back {δ ν α : Type} {R : δ → ν → Rd α} {sp : α → ByteArray} {good : δ → α → Prop}
    {cnt : α → ν} (h : ∀ d n, Undoes (R d n) sp fun x => good d x ∧ cnt x = n) (l : List α) :
    ∀ (ds : List δ) (pre post : ByteArray), l.length = ds.length →
      (∀ y ∈ l.zip ds, good y.2 y.1) →
      rdZip R ds (l.map cnt) (pre ++ cat (l.map sp) ++ post) pre.size =
        some (l, pre.size + (cat (l.map sp)).size) := by
  induction l with
  | nil =>
    intro ds pre post h1 _
    cases ds with
    | nil => simp [rdZip, cat_nil]
    | cons d ds => simp at h1
  | cons x l ih =>
    intro ds pre post h1 h3
    cases ds with
    | nil => simp at h1
    | cons d ds =>
      rw [List.map_cons, List.map_cons, cat_cons]
      have e1 : pre ++ (sp x ++ cat (l.map sp)) ++ post =
          pre ++ sp x ++ (cat (l.map sp) ++ post) := by
        simp only [ByteArray.append_assoc]
      have e2 : pre ++ (sp x ++ cat (l.map sp)) ++ post =
          (pre ++ sp x) ++ cat (l.map sp) ++ post := by
        simp only [ByteArray.append_assoc]
      have a := h d (cnt x) x ⟨h3 (x, d) (by simp), rfl⟩ pre (cat (l.map sp) ++ post)
      rw [← e1] at a
      have b := ih ds (pre ++ sp x) post (by simpa using h1) fun y hy => h3 y (by simp [hy])
      rw [ByteArray.size_append, ← e2] at b
      unfold rdZip
      rw [a]
      simp only
      rw [b, ByteArray.size_append, Nat.add_assoc]

/-- The same in the frame's own form. -/
theorem undoes_zip {δ ν α : Type} {R : δ → ν → Rd α} {sp : α → ByteArray} {good : δ → α → Prop}
    {cnt : α → ν} (h : ∀ d n, Undoes (R d n) sp fun x => good d x ∧ cnt x = n) (ds : List δ)
    (ns : List ν) :
    Undoes (rdZip R ds ns) (fun l => cat (l.map sp)) fun l =>
      l.length = ds.length ∧ (∀ y ∈ l.zip ds, good y.2 y.1) ∧ l.map cnt = ns := by
  intro l hl pre post
  obtain ⟨h1, h2, rfl⟩ := hl
  exact zip_back h l ds pre post h1 h2

/-- The loop gives the members of acc, then what `rdZip` gives. -/
theorem zipLoop_eq {δ ν α : Type} (R : δ → ν → Rd α) (b : ByteArray) :
    ∀ (ds : List δ) (ns : List ν) (i : Nat) (acc : Array α),
      zipLoop R b ds ns i acc = (rdZip R ds ns b i).map fun y => (acc.toList ++ y.1, y.2)
  | [], [], i, acc => by simp [zipLoop, rdZip]
  | [], _ :: _, i, acc => by simp [zipLoop, rdZip]
  | _ :: _, [], i, acc => by simp [zipLoop, rdZip]
  | d :: ds, n :: ns, i, acc => by
    simp only [zipLoop, rdZip]
    cases R d n b i with
    | none => rfl
    | some y =>
      obtain ⟨x, j⟩ := y
      simp only [zipLoop_eq R b ds ns j (acc.push x)]
      cases rdZip R ds ns b j with
      | none => rfl
      | some z =>
        obtain ⟨l, k⟩ := z
        simp

/-- The loop is `rdZip`. -/
theorem rdZipL_eq {δ ν α : Type} (R : δ → ν → Rd α) (ds : List δ) (ns : List ν) :
    rdZipL R ds ns = rdZip R ds ns := by
  funext b i
  unfold rdZipL
  rw [zipLoop_eq]
  cases rdZip R ds ns b i with
  | none => rfl
  | some y => rfl

/-- A pair of the one zip is, turned, a pair of the other. -/
theorem mem_zip_swap {α β : Type} : ∀ (l : List α) (m : List β) (x : α) (y : β),
    (x, y) ∈ l.zip m → (y, x) ∈ m.zip l
  | [], _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: l, c :: m, x, y, h => by
    simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h ⊢
    rcases h with ⟨h1, h2⟩ | h
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr (mem_zip_swap l m x y h)

/-! ## 2. n low bytes -/

/-- n bytes whose values are the digits of v to the base 256, the lowest first, are read as v
modulo 256 ^ n. -/
theorem leNat_of (b : ByteArray) : ∀ (n i v : Nat),
    (∀ k, k < n → (byteAt b (i + k)).toNat = v / 256 ^ k % 256) → leNat b i n = v % 256 ^ n
  | 0, _, v, _ => by rw [Nat.pow_zero, Nat.mod_one]; rfl
  | n + 1, i, v, h => by
    have h0 := h 0 (Nat.succ_pos n)
    rw [Nat.add_zero, Nat.pow_zero, Nat.div_one] at h0
    have ih := leNat_of b n (i + 1) (v / 256) fun k hk => by
      have a := h (k + 1) (Nat.succ_lt_succ hk)
      rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul] at a
      rw [← a]
      congr 2
      omega
    show (byteAt b i).toNat + 256 * leNat b (i + 1) n = _
    rw [h0, ih, Nat.pow_succ', Nat.mod_mul]

/-- The bytes of a word are its digits to the base 256, the lowest first. -/
theorem byteAt_u64 (x : UInt64) (k : Nat) (hk : k < 8) :
    (byteAt (u64 x) k).toNat = x.toNat / 256 ^ k % 256 := by
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [byteAt_eq, u64, Nat.shiftRight_eq_div_pow]

/-- n low bytes are n bytes, for n up to 8. -/
theorem size_lowBytes (n x : Nat) (h : n ≤ 8) : (lowBytes n x).size = n := by
  unfold lowBytes u64n
  rw [ByteArray.size_extract, size_u64]
  omega

/-- The n low bytes of a number are the first n bytes of its word. -/
theorem byteAt_lowBytes (n x k : Nat) (hk : k < n) (h : n ≤ 8) :
    byteAt (lowBytes n x) k = byteAt (u64n x) k := by
  have s : (u64n x).data.size = 8 := rfl
  have hc : k < min n (u64n x).data.size - 0 := by omega
  unfold lowBytes
  rw [byteAt_eq, byteAt_eq, ByteArray.data_extract]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_extract, Nat.zero_add]
  rw [if_pos hc]

/-- A number below 256 ^ n, for n up to 8, is a word. -/
theorem lt_word (n v : Nat) (hn : n ≤ 8) (h : v < 256 ^ n) : v < 2 ^ 64 :=
  Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) hn)

/-- The library's reader of n bytes as a number (`readLE`, Fmt/Rules8.lean) undoes `lowBytes` on the
numbers below 256 ^ n, for n up to 8. -/
theorem undoes_readLE (n : Nat) (hn : n ≤ 8) :
    Undoes (readLE n) (lowBytes n) fun v => v < 256 ^ n := by
  intro v hv pre post
  have s := size_lowBytes n v hn
  have e : leNat (pre ++ lowBytes n v ++ post) pre.size n = v % 256 ^ n :=
    leNat_of _ n pre.size v fun k hk => by
      rw [byteAt_mid pre _ post k (by rw [s]; exact hk), byteAt_lowBytes n _ k hk hn]
      show (byteAt (u64 (UInt64.ofNat v)) k).toNat = _
      rw [byteAt_u64 _ k (by omega), toNat_ofNat_lt v (lt_word n v hn hv)]
  unfold readLE
  rw [if_pos (by rw [ByteArray.size_append, ByteArray.size_append, s]; omega), e,
    Nat.mod_eq_of_lt hv, s]

/-- The same as a word: the reader of n low bytes undoes their spelling on the words below 256 ^ n,
for n up to 8. -/
theorem undoes_low (n : Nat) (hn : n ≤ 8) :
    Undoes (rdLow n) (fun x => lowBytes n x.toNat) fun x => x.toNat < 256 ^ n :=
  undoes_map (undoes_readLE n hn) UInt64.ofNat (fun x => x.toNat) (fun _ _ => UInt64.ofNat_toNat)
    (fun _ _ => rfl) fun _ h => h

/-! ## 3. An opening -/

/-- A column with its salt (ok: W elements, each below p; salt bytes). -/
theorem undoes_column (f : Fld) (W salt : Nat) :
    Undoes (rdColumn f W salt) (fun c => colBytes c.1 ++ c.2) fun c =>
      (c.1.length = W ∧ ∀ x ∈ c.1, x.toNat < f.p) ∧ c.2.size = salt :=
  undoes_pair (undoes_count (undoes_elt f) W) (undoes_bytes salt)

/-- THE LAW OF AN OPENING. The reader at the numbers n undoes the writer on the openings that fit
and have the numbers n. -/
theorem undoes_open (f : Fld) (W salt most : Nat) (n : Nat × Nat) :
    Undoes (OpenParsed.read f W salt n) OpenParsed.bytes fun o =>
      o.fits f W salt most = true ∧ o.counts = n := by
  unfold OpenParsed.read
  exact undoes_map (β := OpenParsed)
    (undoes_pair (undoes_count (undoes_column f W salt) n.1) (undoes_count undoes_digest n.2))
    (fun x => ⟨x.1, x.2⟩) (fun o => (o.cols, o.given)) (fun _ _ => rfl)
    (fun o _ => by simp only [OpenParsed.bytes, pair, List.map_id])
    (fun o ho => by
      obtain ⟨h, hc⟩ := ho
      simp only [OpenParsed.fits, Fld.ok, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
        decide_eq_true_eq] at h
      obtain ⟨⟨-, h3⟩, h4⟩ := h
      subst hc
      exact ⟨⟨rfl, fun c hc => ⟨⟨(h3 c hc).1.1, (h3 c hc).1.2⟩, (h3 c hc).2⟩⟩, ⟨rfl, h4⟩⟩)

/-! ## 4. A round -/

/-- `Fld.okE` as three inequalities. -/
theorem lt_of_okE (f : Fld) (e : Ext) (h : f.okE e = true) :
    e.1.toNat < f.p ∧ e.2.1.toNat < f.p ∧ e.2.2.toNat < f.p := by
  simp only [Fld.okE, Fld.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- One item of a message, of the kind t. -/
theorem undoes_got (f : Fld) (t : Item) :
    Undoes (readItem f t) spellGot fun g => g.fitsItem f t = true := by
  intro g hg pre post
  cases t with
  | f =>
    cases g with
    | f x =>
      exact congrArg (Option.map fun y => (ItemValue.f y.1, y.2))
        (undoes_elt f x (of_decide_eq_true hg) pre post)
    | _ => exact absurd hg Bool.false_ne_true
  | e =>
    cases g with
    | e x =>
      exact congrArg (Option.map fun y => (ItemValue.e y.1, y.2))
        (undoes_ext f x (lt_of_okE f x hg) pre post)
    | _ => exact absurd hg Bool.false_ne_true
  | word =>
    cases g with
    | word x =>
      exact congrArg (Option.map fun y => (ItemValue.word y.1, y.2)) (undoes_word x trivial pre post)
    | _ => exact absurd hg Bool.false_ne_true
  | root =>
    cases g with
    | root d =>
      exact congrArg (Option.map fun y => (ItemValue.root y.1, y.2))
        (undoes_digest d (beq_iff_eq.1 hg) pre post)
    | _ => exact absurd hg Bool.false_ne_true
  | answer =>
    cases g with
    | answer x =>
      exact congrArg (Option.map fun y => (ItemValue.answer y.1, y.2))
        (undoes_ext f x (lt_of_okE f x hg) pre post)
    | _ => exact absurd hg Bool.false_ne_true

/-- A message, cut into the items ts. -/
theorem undoes_items (f : Fld) (ts : List Item) :
    Undoes (readItems f ts) (fun l => cat (l.map spellGot)) fun l =>
      l.length = ts.length ∧ ∀ y ∈ l.zip ts, y.1.fitsItem f y.2 = true := by
  intro l
  induction l generalizing ts with
  | nil =>
    intro hl pre post
    cases ts with
    | nil => simp [readItems, cat_nil]
    | cons t ts => simp at hl
  | cons x l ih =>
    intro hl pre post
    obtain ⟨h1, h3⟩ := hl
    cases ts with
    | nil => simp at h1
    | cons t ts =>
      show readItems f (t :: ts) (pre ++ cat ((x :: l).map spellGot) ++ post) pre.size =
        some (x :: l, pre.size + (cat ((x :: l).map spellGot)).size)
      rw [List.map_cons, cat_cons]
      have e1 : pre ++ (spellGot x ++ cat (l.map spellGot)) ++ post =
          pre ++ spellGot x ++ (cat (l.map spellGot) ++ post) := by
        simp only [ByteArray.append_assoc]
      have e2 : pre ++ (spellGot x ++ cat (l.map spellGot)) ++ post =
          (pre ++ spellGot x) ++ cat (l.map spellGot) ++ post := by
        simp only [ByteArray.append_assoc]
      have a := undoes_got f t x (h3 (x, t) (by simp)) pre (cat (l.map spellGot) ++ post)
      rw [← e1] at a
      have b : readItems f ts (pre ++ spellGot x ++ cat (l.map spellGot) ++ post)
          (pre ++ spellGot x).size =
            some (l, (pre ++ spellGot x).size + (cat (l.map spellGot)).size) :=
        ih ts ⟨by simpa using h1, fun y hy => h3 y (by simp [hy])⟩ (pre ++ spellGot x) post
      rw [ByteArray.size_append, ← e2] at b
      unfold readItems
      rw [a]
      simp only
      rw [b, ByteArray.size_append, Nat.add_assoc]

/-- a nonce's bytes in a file, at the width n: none where there is no nonce -/
def spNonce (n : Nat) : Option UInt64 → ByteArray
  | none => ByteArray.empty
  | some x => lowBytes n x.toNat

/-- there is a nonce exactly where there is work, and it is below 256 ^ n -/
def okNonce (n work : Nat) : Option UInt64 → Prop
  | none => work = 0
  | some x => work ≠ 0 ∧ x.toNat < 256 ^ n

/-- A round's nonce, at a width n up to 8. -/
theorem undoes_nonce (n work : Nat) (hn : n ≤ 8) :
    Undoes (rdNonceAt n work) (spNonce n) (okNonce n work) := by
  intro o ho pre post
  cases o with
  | none =>
    have hw : work = 0 := ho
    subst hw
    exact undoes_give none none rfl pre post
  | some x =>
    have hw : (work == 0) = false := beq_eq_false_iff_ne.2 ho.1
    unfold rdNonceAt
    rw [hw]
    exact congrArg (Option.map fun y => (some y.1, y.2)) (undoes_low n hn x ho.2 pre post)

/-- THE LAW OF A ROUND. The reader at the numbers n undoes the writer, under a plan with the
setting's two widths, on the rounds that fit the declared round r and have the numbers n. -/
theorem undoes_round (S : PlanSetting) (P : Plan) (hN : P.nonce = S.nonce) (hB : P.posB = S.posB)
    (h1 : S.nonce ≤ 8) (h2 : S.posB ≤ 8) (r : DeclaredRound) (n : Nat × List (Nat × Nat)) :
    Undoes (RoundParsed.read S r n) (RoundParsed.bytes P) fun x =>
      x.fits S r = true ∧ x.counts = n := by
  have O := undoes_zip (R := fun w m => OpenParsed.read S.field w.1 w.2.1 m)
    (good := fun w o => o.fits S.field w.1 w.2.1 w.2.2 = true) (cnt := OpenParsed.counts)
    (fun w m => undoes_open S.field w.1 w.2.1 w.2.2 m) (wantOpens S r) n.2
  have A := undoes_pair (undoes_items S.field r.items)
    (undoes_pair (undoes_nonce S.nonce r.entry.work h1)
      (undoes_pair (undoes_count (undoes_low S.posB h2) n.1) O))
  unfold RoundParsed.read
  rw [rdZipL_eq]
  refine undoes_map A _ (fun x => (x.vals, x.nonce, x.listed, x.opens)) ?_ ?_ ?_
  · intro _ _
    rfl
  · intro x _
    obtain ⟨vals, nonce, listed, opens⟩ := x
    cases nonce <;>
      simp only [RoundParsed.bytes, pair, spNonce, hN, hB, ByteArray.append_assoc]
  · intro x hx
    obtain ⟨h, hc⟩ := hx
    subst hc
    obtain ⟨vals, nonce, listed, opens⟩ := x
    simp only [RoundParsed.fits, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := h
    refine ⟨⟨beq_iff_eq.1 a1, List.all_eq_true.1 a2⟩, ?_, ⟨rfl, ?_⟩,
      beq_iff_eq.1 a5, List.all_eq_true.1 a6, rfl⟩
    · cases nonce with
      | none => exact beq_iff_eq.1 a3
      | some v =>
        simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at a3
        exact a3
    · by_cases hc : (S.posB == 0 || r.entry.poss == 0) = true
      · rw [if_pos hc] at a4
        intro p hp
        rw [List.isEmpty_iff.1 a4] at hp
        cases hp
      · rw [if_neg hc] at a4
        simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at a4
        exact fun p hp => (a4.2 p hp).2

/-! ## 5. A chain -/

/-- the random bytes stand in the file exactly in case (a) of R4.5, and are 32 -/
def okRand (c : RandAt) : Option ByteArray → Prop
  | none => c ≠ .inFile
  | some b => c = .inFile ∧ b.size = 32

/-- A chain's random bytes. -/
theorem undoes_rand (c : RandAt) :
    Undoes (rdRand c) (fun o => o.getD ByteArray.empty) (okRand c) := by
  intro o ho pre post
  cases o with
  | none =>
    cases c with
    | inFile => exact absurd rfl ho
    | item k => exact undoes_give none none rfl pre post
    | none => exact undoes_give none none rfl pre post
  | some b =>
    obtain ⟨rfl, hb⟩ := ho
    exact congrArg (Option.map fun y => (some y.1, y.2)) (undoes_bytes 32 b hb pre post)

/-- THE LAW OF A CHAIN, in the frame's form. The reader at the numbers N undoes the writer, under a
plan with the setting's two widths, on the chains that fit the declared chain c and have the numbers
N. -/
theorem undoes_chain (S : PlanSetting) (P : Plan) (hN : P.nonce = S.nonce) (hB : P.posB = S.posB)
    (h1 : S.nonce ≤ 8) (h2 : S.posB ≤ 8) (c : ChainDecl) (N : List (Nat × List (Nat × Nat))) :
    Undoes (ChainParsed.read S c N) (ChainParsed.bytes P) fun X =>
      X.fits S c = true ∧ X.counts = N := by
  unfold ChainParsed.read
  rw [rdZipL_eq]
  exact undoes_map (β := ChainParsed)
    (undoes_pair (undoes_rand c.rand)
      (undoes_zip (R := RoundParsed.read S) (good := fun r x => x.fits S r = true)
        (cnt := RoundParsed.counts) (undoes_round S P hN hB h1 h2) c.rounds N))
    (fun x => ⟨x.1, x.2⟩) (fun X => (X.rand, X.rounds)) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun X hX => by
      obtain ⟨h, hc⟩ := hX
      obtain ⟨rand, rounds⟩ := X
      simp only [ChainParsed.fits, Bool.and_eq_true] at h
      obtain ⟨⟨a1, a2⟩, a3⟩ := h
      refine ⟨?_, beq_iff_eq.1 a2,
        fun y hy => List.all_eq_true.1 a3 (y.2, y.1) (mem_zip_swap _ _ _ _ hy), hc⟩
      cases rand with
      | none => exact bne_iff_ne.1 a1
      | some b =>
        simp only [Bool.and_eq_true, beq_iff_eq] at a1
        exact a1)

/-- THE LAW OF A CHAIN. A chain X that fits the declared chain c under the setting S is written
under a plan with the setting's two widths, of at most eight bytes each; whatever bytes stand before
and behind: the reader, told X's own numbers, gives X and the place behind X's bytes. -/
theorem ChainParsed.read_bytes (S : PlanSetting) (P : Plan) (c : ChainDecl) (X : ChainParsed)
    (hN : P.nonce = S.nonce) (hB : P.posB = S.posB) (h1 : S.nonce ≤ 8) (h2 : S.posB ≤ 8)
    (hX : X.fits S c = true) (pre post : ByteArray) :
    ChainParsed.read S c X.counts (pre ++ X.bytes P ++ post) pre.size =
      some (X, pre.size + (X.bytes P).size) :=
  undoes_chain S P hN hB h1 h2 c X.counts X ⟨hX, rfl⟩ pre post

/-- THE SAME, EXACTLY WHERE X FITS. The reader that tests the form behind the cut, told X's own
numbers, gives X back from X's bytes if X fits the declared chain (by `ChainParsed.read_bytes`), and
only then (because it tests `fits` itself: this half would hold of any reader under that test). -/
theorem ChainParsed.readFit_bytes (S : PlanSetting) (P : Plan) (c : ChainDecl) (X : ChainParsed)
    (hN : P.nonce = S.nonce) (hB : P.posB = S.posB) (h1 : S.nonce ≤ 8) (h2 : S.posB ≤ 8)
    (pre post : ByteArray) :
    ChainParsed.readFit S c X.counts (pre ++ X.bytes P ++ post) pre.size =
      some (X, pre.size + (X.bytes P).size) ↔ X.fits S c = true :=
  ⟨fun h => (rdFit_some h).1,
    fun hX => rdFit_of (ChainParsed.read_bytes S P c X hN hB h1 h2 hX pre post) hX⟩

/-- So the writer is one-to-one where form and numbers are fixed: the statement of
Fmt/ParsedLaws.lean. -/
theorem bytes_inj : Spec.bytes_inj := by
  intro S P c X Y hN hB h1 h2 hX hY hc e
  exact inj_of_undoes (undoes_chain S P hN hB h1 h2 c X.counts) X Y ⟨hX, rfl⟩ ⟨hY, hc.symm⟩ e

/-- The same at a declared structure: the plan is the chain's own (`Declared.plan`), so its two
widths are the setting's by definition. -/
theorem Declared.read_bytes (D : Declared) (c : ChainDecl) (X : ChainParsed)
    (h1 : D.setting.nonce ≤ 8) (h2 : D.setting.posB ≤ 8) (hX : X.fits D.setting c = true)
    (pre post : ByteArray) :
    ChainParsed.read D.setting c X.counts (pre ++ X.bytes (D.plan c) ++ post) pre.size =
      some (X, pre.size + (X.bytes (D.plan c)).size) :=
  ChainParsed.read_bytes D.setting (D.plan c) c X rfl rfl h1 h2 hX pre post

/-! ## 6. The other law: what the reader accepts is the writing of what it returns -/

/-- What the reader r accepts, at whatever place, is the spelling sp of what it returns, and that
value has ok. (`Only`, Fmt/Rules1Only.lean, without "the place behind it is inside the string",
which a reader that reads no byte does not give beyond the string's end: `le_of_cut`.) -/
def Cuts {α : Type} (r : Rd α) (sp : α → ByteArray) (ok : α → Prop) : Prop :=
  ∀ (b : ByteArray) (i : Nat) (x : α) (j : Nat), r b i = some (x, j) →
    ok x ∧ j = i + (sp x).size ∧ b.extract i j = sp x

/-- From the library's frame. -/
theorem cuts_of_only {α : Type} {r : Rd α} {sp : α → ByteArray} {ok : α → Prop}
    (h : Only r sp ok) : Cuts r sp ok := fun b i x j hr =>
  ⟨(h b i x j hr).1, (h b i x j hr).2.1, (h b i x j hr).2.2.2⟩

/-- Another spelling that agrees on the values with ok, and a weaker ok. -/
theorem cuts_of {α : Type} {r : Rd α} {sp sp' : α → ByteArray} {ok ok' : α → Prop}
    (h : Cuts r sp ok) (hs : ∀ x, ok x → sp' x = sp x) (ho : ∀ x, ok x → ok' x) :
    Cuts r sp' ok' := by
  intro b i x j hr
  obtain ⟨a1, a2, a4⟩ := h b i x j hr
  exact ⟨ho x a1, by rw [hs x a1]; exact a2, by rw [hs x a1]; exact a4⟩

/-- The turned reader. -/
theorem cuts_map {α β : Type} {r : Rd α} {sp : α → ByteArray} {ok : α → Prop}
    (h : Cuts r sp ok) (f : α → β) {sp' : β → ByteArray} {ok' : β → Prop}
    (hs : ∀ x, ok x → sp' (f x) = sp x) (ho : ∀ x, ok x → ok' (f x)) :
    Cuts (rdMap f r) sp' ok' := by
  intro b i y j hr
  unfold rdMap at hr
  rcases h1 : r b i with _ | ⟨x, k⟩
  · rw [h1] at hr
    exact absurd hr (by simp)
  · rw [h1] at hr
    simp only [Option.map_some] at hr
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hr)
    obtain ⟨a1, a2, a4⟩ := h b i x k h1
    exact ⟨ho x a1, by rw [hs x a1]; exact a2, by rw [hs x a1]; exact a4⟩

/-- No byte lies from a place to itself. -/
theorem extract_same (b : ByteArray) (i : Nat) : b.extract i i = ByteArray.empty := by
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  simp
  exact Nat.min_le_left _ _

/-- The reader that reads no byte. -/
theorem cuts_give {α : Type} (x : α) :
    Cuts (rdGive x) (fun _ => ByteArray.empty) fun y => y = x := by
  intro b i y j hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hr)
  exact ⟨rfl, rfl, extract_same b i⟩

/-- A pair. -/
theorem cuts_pair {α β : Type} {ra : Rd α} {rb : Rd β} {sa : α → ByteArray} {sb : β → ByteArray}
    {oa : α → Prop} {ob : β → Prop} (ha : Cuts ra sa oa) (hb : Cuts rb sb ob) :
    Cuts (rdPair ra rb) (pair sa sb) fun x => oa x.1 ∧ ob x.2 := by
  intro b i x j h
  unfold rdPair at h
  rcases h1 : ra b i with _ | ⟨u, k⟩
  · rw [h1] at h
    exact absurd h (by simp)
  · rw [h1] at h
    simp only at h
    rcases h2 : rb b k with _ | ⟨v, l⟩
    · rw [h2] at h
      exact absurd h (by simp)
    · rw [h2] at h
      simp only at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨a1, a2, a4⟩ := ha b i u k h1
      obtain ⟨c1, c2, c4⟩ := hb b k v l h2
      refine ⟨⟨a1, c1⟩, ?_, ?_⟩
      · unfold pair
        rw [ByteArray.size_append]
        simp only
        omega
      · unfold pair
        rw [ByteArray.extract_eq_extract_append_extract k (by omega) (by omega), a4, c4]

/-- n values. -/
theorem cuts_count {α : Type} {r : Rd α} {sp : α → ByteArray} {ok : α → Prop}
    (hr : Cuts r sp ok) (n : Nat) :
    Cuts (rdMany r n) (fun l => cat (l.map sp)) fun l => l.length = n ∧ ∀ x ∈ l, ok x := by
  induction n with
  | zero =>
    intro b i l j h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨⟨rfl, fun _ hx => absurd hx (by simp)⟩, rfl, extract_same b i⟩
  | succ n ih =>
    intro b i l j h
    unfold rdMany at h
    rcases h1 : r b i with _ | ⟨x, k⟩
    · rw [h1] at h
      exact absurd h (by simp)
    · rw [h1] at h
      simp only at h
      rcases h2 : rdMany r n b k with _ | ⟨l', m⟩
      · rw [h2] at h
        exact absurd h (by simp)
      · rw [h2] at h
        simp only at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        obtain ⟨a1, a2, a4⟩ := hr b i x k h1
        obtain ⟨⟨c0, c1⟩, c2, c4⟩ := ih b k l' m h2
        have c2' : m = k + (cat (l'.map sp)).size := c2
        have c4' : b.extract k m = cat (l'.map sp) := c4
        refine ⟨⟨by rw [List.length_cons, c0], ?_⟩, ?_, ?_⟩
        · intro y hy
          rcases List.mem_cons.1 hy with rfl | hy
          · exact a1
          · exact c1 y hy
        · show m = i + (cat ((x :: l').map sp)).size
          rw [List.map_cons, cat_cons, ByteArray.size_append]
          omega
        · show b.extract i m = cat ((x :: l').map sp)
          rw [List.map_cons, cat_cons,
            ByteArray.extract_eq_extract_append_extract k (by omega) (by omega), a4, c4']

/-- A list of values, each by its own reader: what is accepted has the numbers that were told. -/
theorem cuts_zip {δ ν α : Type} {R : δ → ν → Rd α} {sp : α → ByteArray} {cnt : α → ν}
    (h : ∀ d n, Cuts (R d n) sp fun x => cnt x = n) :
    ∀ (ds : List δ) (ns : List ν),
      Cuts (rdZip R ds ns) (fun l => cat (l.map sp)) fun l => l.map cnt = ns
  | [], [] => fun b i l j hr => by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hr)
    exact ⟨rfl, rfl, extract_same b i⟩
  | [], _ :: _ => fun b i l j hr => by simp [rdZip] at hr
  | _ :: _, [] => fun b i l j hr => by simp [rdZip] at hr
  | d :: ds, n :: ns => fun b i l j hr => by
    unfold rdZip at hr
    rcases h1 : R d n b i with _ | ⟨x, k⟩
    · rw [h1] at hr
      exact absurd hr (by simp)
    · rw [h1] at hr
      simp only at hr
      rcases h2 : rdZip R ds ns b k with _ | ⟨l', m⟩
      · rw [h2] at hr
        exact absurd hr (by simp)
      · rw [h2] at hr
        simp only at hr
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hr)
        obtain ⟨a1, a2, a4⟩ := h d n b i x k h1
        obtain ⟨c1, c2, c4⟩ := cuts_zip h ds ns b k l' m h2
        have a1' : cnt x = n := a1
        have c1' : l'.map cnt = ns := c1
        have c2' : m = k + (cat (l'.map sp)).size := c2
        have c4' : b.extract k m = cat (l'.map sp) := c4
        refine ⟨?_, ?_, ?_⟩
        · show (x :: l').map cnt = n :: ns
          rw [List.map_cons, a1', c1']
        · show m = i + (cat ((x :: l').map sp)).size
          rw [List.map_cons, cat_cons, ByteArray.size_append]
          omega
        · show b.extract i m = cat ((x :: l').map sp)
          rw [List.map_cons, cat_cons,
            ByteArray.extract_eq_extract_append_extract k (by omega) (by omega), a4, c4']

/-- From a place up to the string's end, what was cut ends inside the string. -/
theorem le_of_cut (b s : ByteArray) (i j : Nat) (hi : i ≤ b.size) (h1 : j = i + s.size)
    (h2 : b.extract i j = s) : j ≤ b.size := by
  have g := congrArg ByteArray.size h2
  rw [ByteArray.size_extract] at g
  omega

/-- What a reader under a test accepts passes the test. -/
theorem cuts_fit {α : Type} {r : Rd α} {sp : α → ByteArray} {ok : α → Prop} (fit : α → Bool)
    (h : Cuts r sp ok) : Cuts (rdFit fit r) sp fun x => fit x = true ∧ ok x :=
  fun b i x j hr =>
    ⟨⟨(rdFit_some hr).1, (h b i x j (rdFit_some hr).2).1⟩, (h b i x j (rdFit_some hr).2).2⟩

/-- Under `Cuts r sp ok`: what r reads out of a whole string is spelled by that string. -/
theorem whole_cuts {α : Type} {r : Rd α} {sp : α → ByteArray} {ok : α → Prop} (hr : Cuts r sp ok)
    (b : ByteArray) (x : α) (h : whole r b = some x) : b = sp x ∧ ok x := by
  unfold whole at h
  rcases h1 : r b 0 with _ | ⟨y, j⟩
  · rw [h1] at h
    exact absurd h (by simp)
  · rw [h1] at h
    simp only at h
    by_cases hj : j = b.size
    · rw [if_pos hj] at h
      obtain rfl := Option.some.inj h
      obtain ⟨a1, -, a4⟩ := hr b 0 y j h1
      rw [hj, ByteArray.extract_zero_size] at a4
      exact ⟨a4, a1⟩
    · rw [if_neg hj] at h
      exact absurd h (by simp)

/-- Both laws of a reader, on a whole string: it gives x exactly where x has ok and the string is
x's spelling. -/
theorem whole_iff_both {α : Type} {r : Rd α} {sp : α → ByteArray} {ok : α → Prop}
    (hu : Undoes r sp ok) (hc : Cuts r sp ok) (b : ByteArray) (x : α) :
    whole r b = some x ↔ ok x ∧ b = sp x := by
  constructor
  · intro h
    obtain ⟨a, c⟩ := whole_cuts hc b x h
    exact ⟨c, a⟩
  · rintro ⟨h1, rfl⟩
    exact whole_of_undoes hu x h1

/-- n bytes, read as a number, give a number below 256 ^ n. -/
theorem leNat_lt (b : ByteArray) : ∀ (n i : Nat), leNat b i n < 256 ^ n
  | 0, _ => Nat.zero_lt_one
  | n + 1, i => by
    have a := (byteAt b i).toNat_lt
    have c := leNat_lt b n (i + 1)
    show (byteAt b i).toNat + 256 * leNat b (i + 1) n < 256 ^ (n + 1)
    rw [Nat.pow_succ']
    generalize 256 ^ n = M at c ⊢
    omega

/-- The digits to the base 256 of n bytes read as a number are these bytes. -/
theorem leNat_digit (b : ByteArray) : ∀ (n i k : Nat), k < n →
    leNat b i n / 256 ^ k % 256 = (byteAt b (i + k)).toNat
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, i, 0, _ => by
    have a := (byteAt b i).toNat_lt
    show ((byteAt b i).toNat + 256 * leNat b (i + 1) n) / 256 ^ 0 % 256 = (byteAt b i).toNat
    rw [Nat.pow_zero, Nat.div_one]
    omega
  | n + 1, i, k + 1, h => by
    have a := (byteAt b i).toNat_lt
    have ih := leNat_digit b n (i + 1) k (Nat.lt_of_succ_lt_succ h)
    have e : ((byteAt b i).toNat + 256 * leNat b (i + 1) n) / 256 = leNat b (i + 1) n := by omega
    show ((byteAt b i).toNat + 256 * leNat b (i + 1) n) / 256 ^ (k + 1) % 256 =
      (byteAt b (i + (k + 1))).toNat
    rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul, e, ih, show i + (k + 1) = i + 1 + k from by omega]

/-- Byte k of the bytes from i to j is byte i + k. -/
theorem byteAt_extract (b : ByteArray) (i j k : Nat) (hk : i + k < j) (hj : j ≤ b.size) :
    byteAt (b.extract i j) k = byteAt b (i + k) := by
  have hs : b.data.size = b.size := ByteArray.size_data
  have hc : k < min j b.data.size - i := by omega
  rw [byteAt_eq, byteAt_eq, ByteArray.data_extract]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  rw [if_pos hc]

/-- n bytes of a string, read as a number and written as n low bytes, are these bytes. -/
theorem lowBytes_leNat (b : ByteArray) (i n : Nat) (hn : n ≤ 8) (h : i + n ≤ b.size) :
    lowBytes n (leNat b i n) = b.extract i (i + n) := by
  have hv : leNat b i n < 2 ^ 64 := lt_word n _ hn (leNat_lt b n i)
  have s1 : (lowBytes n (leNat b i n)).data.size = n := by
    rw [ByteArray.size_data, size_lowBytes n _ hn]
  have s2 : (b.extract i (i + n)).data.size = n := by
    rw [ByteArray.size_data, ByteArray.size_extract]
    omega
  apply ByteArray.ext
  apply Array.ext
  · rw [s1, s2]
  · intro k hk1 hk2
    have hk : k < n := by omega
    rw [← byteAt_in _ k hk1, ← byteAt_in _ k hk2, byteAt_lowBytes n _ k hk hn,
      byteAt_extract b i (i + n) k (by omega) h]
    apply UInt8.toNat_inj.1
    show (byteAt (u64 (UInt64.ofNat (leNat b i n))) k).toNat = _
    rw [byteAt_u64 _ k (by omega), toNat_ofNat_lt _ hv, leNat_digit b n i k hk]

/-- The library's reader of n bytes as a number (`readLE`, Fmt/Rules8.lean), for n up to 8. -/
theorem only_readLE (n : Nat) (hn : n ≤ 8) :
    Only (readLE n) (lowBytes n) fun v => v < 256 ^ n := by
  intro b i x j h
  unfold readLE at h
  by_cases hb : i + n ≤ b.size
  · rw [if_pos hb] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨leNat_lt b n i, by rw [size_lowBytes n _ hn], hb, (lowBytes_leNat b i n hn hb).symm⟩
  · rw [if_neg hb] at h
    exact absurd h (by simp)

/-- The same as a word. -/
theorem cuts_low (n : Nat) (hn : n ≤ 8) :
    Cuts (rdLow n) (fun x => lowBytes n x.toNat) fun x => x.toNat < 256 ^ n :=
  cuts_map (cuts_of_only (only_readLE n hn)) UInt64.ofNat
    (fun v hv => by
      show lowBytes n (UInt64.ofNat v).toNat = lowBytes n v
      rw [toNat_ofNat_lt v (lt_word n v hn hv)])
    (fun v hv => by
      show (UInt64.ofNat v).toNat < 256 ^ n
      rw [toNat_ofNat_lt v (lt_word n v hn hv)]
      exact hv)

/-- A column with its salt: what is accepted has the form that `OpenParsed.fits` asks of it. -/
theorem cuts_column (f : Fld) (W salt : Nat) :
    Cuts (rdColumn f W salt) (fun c => colBytes c.1 ++ c.2) fun c =>
      (c.1.length = W ∧ ∀ x ∈ c.1, x.toNat < f.p) ∧ c.2.size = salt :=
  cuts_pair (cuts_count (cuts_of_only (only_elt f)) W) (cuts_of_only (only_bytes salt))

/-- What the reader of an opening accepts at the numbers n has the numbers n; its columns, salts and
given digests have their form; and its writing is the bytes that were read. -/
theorem cuts_open (f : Fld) (W salt : Nat) (n : Nat × Nat) :
    Cuts (OpenParsed.read f W salt n) OpenParsed.bytes fun o =>
      o.counts = n ∧
        (∀ c ∈ o.cols, (c.1.length = W ∧ ∀ x ∈ c.1, x.toNat < f.p) ∧ c.2.size = salt) ∧
        ∀ d ∈ o.given, d.size = 32 := by
  unfold OpenParsed.read
  refine cuts_map
    (cuts_pair (cuts_count (cuts_column f W salt) n.1)
      (cuts_count (cuts_of_only only_digest) n.2)) _ ?_ ?_
  · intro x _
    simp only [OpenParsed.bytes, pair, List.map_id]
  · intro x hx
    exact ⟨Prod.ext hx.1.1 hx.2.1, hx.1.2, hx.2.2⟩

/-- Three inequalities as `Fld.okE`. -/
theorem okE_of_lt (f : Fld) (e : Ext)
    (h : e.1.toNat < f.p ∧ e.2.1.toNat < f.p ∧ e.2.2.toNat < f.p) : f.okE e = true := by
  simp only [Fld.okE, Fld.ok, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

/-- One item of a message: what is accepted is of the kind t, in its one spelling. -/
theorem cuts_got (f : Fld) (t : Item) :
    Cuts (readItem f t) spellGot fun g => g.fitsItem f t = true := by
  cases t with
  | f =>
    exact cuts_map (cuts_of_only (only_elt f)) ItemValue.f (fun _ _ => rfl) fun _ h => decide_eq_true h
  | e =>
    exact cuts_map (cuts_of_only (only_ext f)) ItemValue.e (fun _ _ => rfl) fun x h => okE_of_lt f x h
  | word => exact cuts_map (cuts_of_only only_word) ItemValue.word (fun _ _ => rfl) fun _ _ => rfl
  | root =>
    exact cuts_map (cuts_of_only only_digest) ItemValue.root (fun _ _ => rfl) fun _ h => beq_iff_eq.2 h
  | answer =>
    exact cuts_map (cuts_of_only (only_ext f)) ItemValue.answer (fun _ _ => rfl)
      fun x h => okE_of_lt f x h

/-- A message, cut into the items ts. -/
theorem cuts_items (f : Fld) :
    ∀ ts : List Item, Cuts (readItems f ts) (fun l => cat (l.map spellGot)) fun l =>
      l.length = ts.length ∧ ∀ y ∈ l.zip ts, y.1.fitsItem f y.2 = true
  | [] => fun b i l j hr => by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hr)
    exact ⟨⟨rfl, fun _ hy => absurd hy (by simp)⟩, rfl, extract_same b i⟩
  | t :: ts => fun b i l j hr => by
    unfold readItems at hr
    rcases h1 : readItem f t b i with _ | ⟨x, k⟩
    · rw [h1] at hr
      exact absurd hr (by simp)
    · rw [h1] at hr
      simp only at hr
      rcases h2 : readItems f ts b k with _ | ⟨l', m⟩
      · rw [h2] at hr
        exact absurd hr (by simp)
      · rw [h2] at hr
        simp only at hr
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hr)
        obtain ⟨a1, a2, a4⟩ := cuts_got f t b i x k h1
        obtain ⟨⟨c0, c1⟩, c2, c4⟩ := cuts_items f ts b k l' m h2
        have c2' : m = k + (cat (l'.map spellGot)).size := c2
        have c4' : b.extract k m = cat (l'.map spellGot) := c4
        refine ⟨⟨by rw [List.length_cons, List.length_cons, c0], ?_⟩, ?_, ?_⟩
        · intro y hy
          rw [List.zip_cons_cons] at hy
          rcases List.mem_cons.1 hy with rfl | hy
          · exact a1
          · exact c1 y hy
        · show m = i + (cat ((x :: l').map spellGot)).size
          rw [List.map_cons, cat_cons, ByteArray.size_append]
          omega
        · show b.extract i m = cat ((x :: l').map spellGot)
          rw [List.map_cons, cat_cons,
            ByteArray.extract_eq_extract_append_extract k (by omega) (by omega), a4, c4']

/-- A round's nonce, at a width n up to 8. -/
theorem cuts_nonceAt (n work : Nat) (hn : n ≤ 8) :
    Cuts (rdNonceAt n work) (spNonce n) (okNonce n work) := by
  unfold rdNonceAt
  by_cases hw : (work == 0) = true
  · rw [if_pos hw]
    exact cuts_of (cuts_give none) (fun x hx => by subst hx; rfl)
      fun x hx => by subst hx; exact beq_iff_eq.1 hw
  · rw [if_neg hw]
    exact cuts_map (cuts_low n hn) some (fun _ _ => rfl)
      fun _ hx => ⟨fun h0 => hw (beq_iff_eq.2 h0), hx⟩

/-- What the reader of a round accepts at the numbers n has the numbers n, and its writing, under a
plan with the setting's two widths, is the bytes that were read. -/
theorem cuts_round (S : PlanSetting) (P : Plan) (hN : P.nonce = S.nonce) (hB : P.posB = S.posB)
    (h1 : S.nonce ≤ 8) (h2 : S.posB ≤ 8) (r : DeclaredRound) (n : Nat × List (Nat × Nat)) :
    Cuts (RoundParsed.read S r n) (RoundParsed.bytes P) fun x => x.counts = n := by
  have O := cuts_zip (R := fun w m => OpenParsed.read S.field w.1 w.2.1 m)
    (cnt := OpenParsed.counts)
    (fun w m => cuts_of (cuts_open S.field w.1 w.2.1 m) (fun _ _ => rfl) fun _ h => h.1)
    (wantOpens S r) n.2
  have A := cuts_pair (cuts_items S.field r.items)
    (cuts_pair (cuts_nonceAt S.nonce r.entry.work h1)
      (cuts_pair (cuts_count (cuts_low S.posB h2) n.1) O))
  unfold RoundParsed.read
  rw [rdZipL_eq]
  refine cuts_map A _ ?_ ?_
  · intro x _
    obtain ⟨vals, nonce, listed, opens⟩ := x
    cases nonce <;>
      simp only [RoundParsed.bytes, pair, spNonce, hN, hB, ByteArray.append_assoc]
  · intro x hx
    exact Prod.ext hx.2.2.1.1 hx.2.2.2

/-- A chain's random bytes. -/
theorem cuts_rand (c : RandAt) :
    Cuts (rdRand c) (fun o => o.getD ByteArray.empty) fun _ => True := by
  cases c with
  | inFile =>
    exact cuts_map (cuts_of_only (only_bytes 32)) some (fun _ _ => rfl) fun _ _ => trivial
  | item k =>
    exact cuts_of (cuts_give none) (fun x hx => by subst hx; rfl) fun _ _ => trivial
  | none =>
    exact cuts_of (cuts_give none) (fun x hx => by subst hx; rfl) fun _ _ => trivial

/-- THE OTHER LAW OF A CHAIN. What the reader accepts at the numbers N has the numbers N, and its
writing, under a plan with the setting's two widths, is the bytes that were read. -/
theorem cuts_chain (S : PlanSetting) (P : Plan) (hN : P.nonce = S.nonce) (hB : P.posB = S.posB)
    (h1 : S.nonce ≤ 8) (h2 : S.posB ≤ 8) (c : ChainDecl) (N : List (Nat × List (Nat × Nat))) :
    Cuts (ChainParsed.read S c N) (ChainParsed.bytes P) fun X => X.counts = N := by
  unfold ChainParsed.read
  rw [rdZipL_eq]
  refine cuts_map
    (cuts_pair (cuts_rand c.rand)
      (cuts_zip (R := RoundParsed.read S) (cnt := RoundParsed.counts)
        (cuts_round S P hN hB h1 h2) c.rounds N)) _ ?_ ?_
  · intro _ _
    rfl
  · intro x hx
    exact hx.2

/-- The same of the reader that tests the form: what it accepts fits too. -/
theorem cuts_chainFit (S : PlanSetting) (P : Plan) (hN : P.nonce = S.nonce)
    (hB : P.posB = S.posB) (h1 : S.nonce ≤ 8) (h2 : S.posB ≤ 8) (c : ChainDecl)
    (N : List (Nat × List (Nat × Nat))) :
    Cuts (ChainParsed.readFit S c N) (ChainParsed.bytes P) fun X =>
      X.fits S c = true ∧ X.counts = N :=
  cuts_fit _ (cuts_chain S P hN hB h1 h2 c N)

/-- BOTH LAWS IN ONE. At a place i up to the end of a string b, the reader that tests the form, told
the numbers N, gives X and the place j exactly where X fits the declared chain, has the numbers N,
and is written to the bytes of b from i to j. -/
theorem ChainParsed.readFit_iff (S : PlanSetting) (P : Plan) (c : ChainDecl)
    (N : List (Nat × List (Nat × Nat))) (hN : P.nonce = S.nonce) (hB : P.posB = S.posB)
    (h1 : S.nonce ≤ 8) (h2 : S.posB ≤ 8) (b : ByteArray) (i j : Nat) (X : ChainParsed)
    (hi : i ≤ b.size) :
    ChainParsed.readFit S c N b i = some (X, j) ↔
      X.fits S c = true ∧ X.counts = N ∧ j = i + (X.bytes P).size ∧ j ≤ b.size ∧
        b.extract i j = X.bytes P := by
  constructor
  · intro h
    obtain ⟨⟨a0, a1⟩, a2, a4⟩ := cuts_chainFit S P hN hB h1 h2 c N b i X j h
    exact ⟨a0, a1, a2, le_of_cut b _ i j hi a2 a4, a4⟩
  · rintro ⟨hf, rfl, hs, hj, he⟩
    have e : b.extract 0 i ++ b.extract i j ++ b.extract j b.size = b := by
      rw [← ByteArray.extract_eq_extract_append_extract i (by omega) (by omega),
        ← ByteArray.extract_eq_extract_append_extract j (by omega) (by omega),
        ByteArray.extract_zero_size]
    have sz : (b.extract 0 i).size = i := by
      rw [ByteArray.size_extract]
      omega
    have u := (ChainParsed.readFit_bytes S P c X hN hB h1 h2 (b.extract 0 i)
      (b.extract j b.size)).2 hf
    rw [sz, ← hs, ← he, e] at u
    exact u

/-- The same at a declared structure. -/
theorem Declared.readFit_iff (D : Declared) (c : ChainDecl) (N : List (Nat × List (Nat × Nat)))
    (h1 : D.setting.nonce ≤ 8) (h2 : D.setting.posB ≤ 8) (b : ByteArray) (i j : Nat)
    (X : ChainParsed) (hi : i ≤ b.size) :
    ChainParsed.readFit D.setting c N b i = some (X, j) ↔
      X.fits D.setting c = true ∧ X.counts = N ∧ j = i + (X.bytes (D.plan c)).size ∧
        j ≤ b.size ∧ b.extract i j = X.bytes (D.plan c) :=
  ChainParsed.readFit_iff D.setting (D.plan c) c N rfl rfl h1 h2 b i j X hi

end Fmt

#print axioms Fmt.undoes_open
#print axioms Fmt.undoes_round
#print axioms Fmt.undoes_chain
#print axioms Fmt.ChainParsed.read_bytes
#print axioms Fmt.ChainParsed.readFit_bytes
#print axioms Fmt.bytes_inj
#print axioms Fmt.cuts_chain
#print axioms Fmt.ChainParsed.readFit_iff
#print axioms Fmt.Declared.readFit_iff
