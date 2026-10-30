-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/ReadBackAt.lean: parameter bytes, fewer than 2^64, that are read back at one digest
of 32 bytes are read back at every other digest of 32 bytes, with the same result but for the digest
and the bytes.

The program spells a chain's parameter bytes from a plan, the digest of the public files and further
items (`Fmt.paramsBytes`), and reads them back before it uses them (`Given.read`, and the readers of
OnBytes/Params/Chains.lean). A bound under a random oracle for a verifier that forms that digest by
the oracle speaks of these readers at every value of the digest. No such verifier and no such bound
for the program stand in OnBytes/: the program forms the digest by BLAKE2b. The library proves that
reading undoes spelling for parameters that fit bounds on every number and name (`Fmt.params_back`);
no such bounds are shown of the plans that the planner makes, but for the entry's plan at typed
lines, among them those typed for the full-size example with a record and with work
(`Tie.record_read_at`, OnBytes/Tie/EntryAtCfgRecord.lean, on the typed plan;
that the planner's plan is that one:
`Tie.configure_record_at`, the same file). Of
the plan this file asks only what the bound on the bytes' length holds. It continues
OnBytes/Params/ReadBackLaws.lean, which follows where each part of the reader ends.

How. The version's item and the plan are spelled before the digest. Every test on a length in the
plan's part of the reader is settled by the plan's own spelling, so what the reader returns there is
the same whatever bytes stand behind (`rdEntry_post`, `rdEntries_post`, `rdPlan_post`). The plan
that it returns need not be the plan that was spelled, but it has the same field and spells the same
bytes (`rdEntry_bytes`, `rdEntries_bytes`, `rdPlan_bytes`, with `ascii_nameOf`). The digest's item
and the further items are read by the library's laws at any bytes before them.

Main definition: `Given.atCfg`.
Main theorems. P is a plan, c and c' digests of 32 bytes, I a list of items.
- `paramsRead_form`: the library's reader on `Fmt.paramsBytes P c I`, written out in what `rdPlan`
  returns.
- `Given.read_spells`, `Given.read_own`: if `Given.read` returns g on `Fmt.paramsBytes P c I`, then
  g's plan and items spell, at every digest, the bytes that P and I spell; and g's bytes are spelled
  from g's own plan, digest and items.
- `paramsRead_at`, `Given.read_at`: then on `Fmt.paramsBytes P c' I` it returns `g.atCfg c'`: g with
  c' as its digest and the bytes spelled anew.
- `Link.read_at`, `Shared.read_at`, `Second.read_at`, `OneTime.read_at`, `First.read_at`,
  `KeyChains.read_at`, `ProofChains.read_at`: the same for the five readers of a chain's parameter
  bytes and the two readers of three chains. `Shared.read_given`, `Second.read_given`: what these
  two readers return holds what `Given.read` returns on the same bytes.

What is asked. The bytes at c are fewer than 2^64 (Lean proves of no byte string that it is shorter;
the proofs take from it that the plan has fewer than 2^64 entries and that each name and value has
fewer than 2^64 bytes; whether the theorems hold without it is not looked at); both digests have 32
bytes; the items' names are within the format's rule for names (`Fmt.okName`). The first condition
does not hang on the digest: the bytes have one length at all digests of one length
(`size_paramsBytes_at`).

What is not claimed. Nothing if the reader refuses at c: the theorems on what a reader returns at c'
are implications, and that it then refuses at c' follows only by turning them round, under the same
conditions. Nothing on bytes that `Fmt.paramsBytes` has not spelled. Nothing on what the plan that
is read back is, beyond its field and its bytes. No probability and nothing on soundness. For proofs
only; the program does not import this file.

-/
import OnBytes.Params.ReadBackLaws
import OnBytes.Params.Chains
import OnBytes.Params.ConfigureLaws

set_option autoImplicit false

namespace OnBytes.Params

open Fmt

/-- The reader of an entry at the place where an entry's spelling begins, written out: nothing if
the name's bytes are outside the range for names; else the entry that is made of the name's bytes
and the eleven words, and the place where the spelling ends. No byte behind the spelling enters.
Condition: the name has fewer than 2^64 bytes. -/
theorem rdEntry_form (e : Entry) (pre q : ByteArray) (hn : (ascii e.name).size < 2 ^ 64) :
    rdEntry (pre ++ e.bytes ++ q) pre.size =
      if isName (ascii e.name) = true then
        (entryOf (nameOf (ascii e.name)) (e.words.map UInt64.ofNat)).map fun x =>
          (x, pre.size + (text (ascii e.name)).size +
            (cat ((e.words.map UInt64.ofNat).map u64)).size)
      else none := by
  rw [entry_bytes]
  have a := undoes_text (ascii e.name) hn pre (cat ((e.words.map UInt64.ofNat).map u64) ++ q)
  have b := undoes_many undoes_word (e.words.map UInt64.ofNat) (fun _ _ => trivial)
    (pre ++ text (ascii e.name)) q
  rw [ByteArray.size_append] at b
  have e1 : pre ++ (text (ascii e.name) ++ cat ((e.words.map UInt64.ofNat).map u64)) ++ q =
      pre ++ text (ascii e.name) ++ (cat ((e.words.map UInt64.ofNat).map u64) ++ q) := by
    simp only [ByteArray.append_assoc]
  have e2 : pre ++ text (ascii e.name) ++ (cat ((e.words.map UInt64.ofNat).map u64) ++ q) =
      pre ++ text (ascii e.name) ++ cat ((e.words.map UInt64.ofNat).map u64) ++ q := by
    simp only [ByteArray.append_assoc]
  have hl : (e.words.map UInt64.ofNat).length = 11 := rfl
  rw [hl] at b
  unfold rdEntry rdName
  rw [e1, a]
  simp only
  by_cases hc : isName (ascii e.name) = true
  · rw [if_pos hc, if_pos hc]
    simp only
    rw [e2, b]
  · rw [if_neg hc, if_neg hc]

/-- What the reader of an entry returns where an entry's spelling begins is the same whatever bytes
stand behind the spelling. -/
theorem rdEntry_post (e : Entry) (pre post post' : ByteArray)
    (hn : (ascii e.name).size < 2 ^ 64) :
    rdEntry (pre ++ e.bytes ++ post) pre.size = rdEntry (pre ++ e.bytes ++ post') pre.size := by
  rw [rdEntry_form e pre post hn, rdEntry_form e pre post' hn]

/-- The same for several entries in a row. -/
theorem rdEntries_post : ∀ (es : List Entry) (pre post post' : ByteArray),
    (∀ e ∈ es, (ascii e.name).size < 2 ^ 64) →
    rdMany rdEntry es.length (pre ++ cat (es.map Entry.bytes) ++ post) pre.size =
      rdMany rdEntry es.length (pre ++ cat (es.map Entry.bytes) ++ post') pre.size
  | [], pre, post, post', _ => by
    simp only [List.length_nil, rdMany]
  | x :: es, pre, post, post', hn => by
    rw [List.map_cons, cat_cons, List.length_cons]
    have e1 : ∀ q : ByteArray, pre ++ (x.bytes ++ cat (es.map Entry.bytes)) ++ q =
        pre ++ x.bytes ++ (cat (es.map Entry.bytes) ++ q) := by
      intro q
      simp only [ByteArray.append_assoc]
    have e2 : ∀ q : ByteArray, pre ++ x.bytes ++ (cat (es.map Entry.bytes) ++ q) =
        (pre ++ x.bytes) ++ cat (es.map Entry.bytes) ++ q := by
      intro q
      simp only [ByteArray.append_assoc]
    unfold rdMany
    rw [e1 post, e1 post']
    have hx := rdEntry_post x pre (cat (es.map Entry.bytes) ++ post)
      (cat (es.map Entry.bytes) ++ post') (hn x List.mem_cons_self)
    cases hr : rdEntry (pre ++ x.bytes ++ (cat (es.map Entry.bytes) ++ post')) pre.size with
    | none =>
      rw [hr] at hx
      rw [hx]
    | some y =>
      obtain ⟨x', j⟩ := y
      rw [hr] at hx
      rw [hx]
      have hj := rdEntry_end (hn x List.mem_cons_self) hr
      simp only
      rw [e2 post, e2 post', hj, ← ByteArray.size_append,
        rdEntries_post es (pre ++ x.bytes) post post'
          (fun e he => hn e (List.mem_cons_of_mem _ he))]

/-- What the reader of a plan returns where a plan's spelling begins is the same whatever bytes
stand behind the spelling. The reader tests that as many bytes are left as the plan has entries;
each entry takes at least one byte of the plan's own spelling, so the test passes whatever follows.
Conditions: the plan has fewer than 2^64 entries, and each entry's name fewer than 2^64 bytes. -/
theorem rdPlan_post (P : Plan) (pre post post' : ByteArray) (hl : P.entries.length < 2 ^ 64)
    (hn : ∀ e ∈ P.entries, (ascii e.name).size < 2 ^ 64) :
    rdPlan (pre ++ P.bytes ++ post) pre.size = rdPlan (pre ++ P.bytes ++ post') pre.size := by
  rw [plan_bytes]
  have a : ∀ q : ByteArray, _ := fun q =>
    undoes_many undoes_word (P.words.map UInt64.ofNat) (fun _ _ => trivial) pre
      (cat (P.entries.map Entry.bytes) ++ q)
  have e1 : ∀ q : ByteArray, pre ++
        (cat ((P.words.map UInt64.ofNat).map u64) ++ cat (P.entries.map Entry.bytes)) ++ q =
      pre ++ cat ((P.words.map UInt64.ofNat).map u64) ++
        (cat (P.entries.map Entry.bytes) ++ q) := by
    intro q
    simp only [ByteArray.append_assoc]
  have e2 : ∀ q : ByteArray, pre ++ cat ((P.words.map UInt64.ofNat).map u64) ++
        (cat (P.entries.map Entry.bytes) ++ q) =
      pre ++ cat ((P.words.map UInt64.ofNat).map u64) ++
        cat (P.entries.map Entry.bytes) ++ q := by
    intro q
    simp only [ByteArray.append_assoc]
  have hw : (P.words.map UInt64.ofNat).length = 8 := rfl
  rw [hw] at a
  have hle : P.entries.length ≤ (cat (P.entries.map Entry.bytes)).size :=
    length_le_cat P.entries fun e _ => entry_size e
  generalize cat ((P.words.map UInt64.ofNat).map u64) = W at a e1 e2 ⊢
  unfold rdPlan
  rw [e1 post, e1 post', a post, a post']
  simp only [Plan.words, List.map_cons, List.map_nil, fldOf_num, toNat_ofNat_lt _ hl]
  have hc : ∀ q : ByteArray, (UInt64.ofNat 1 == 1 &&
        decide (pre.size + W.size + P.entries.length ≤
            (pre ++ W ++ (cat (P.entries.map Entry.bytes) ++ q)).size)) = true := by
    intro q
    simp only [ByteArray.size_append, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨rfl, by omega⟩
  rw [if_pos (hc post), if_pos (hc post'), e2 post, e2 post', ← ByteArray.size_append,
    rdEntries_post P.entries (pre ++ W) post post' hn]

/-- A byte of at most 126, taken as a character and back, is itself. -/
theorem char_back (x : UInt8) (h : x.toNat ≤ 126) :
    UInt8.ofNat (Char.ofNat x.toNat).toNat = x := by
  have hv : (Char.ofNat x.toNat).toNat = x.toNat := by
    have : Nat.isValidChar x.toNat := Or.inl (by omega)
    simp [Char.ofNat, this, Char.toNat, Char.ofNatAux]
  rw [hv]
  exact UInt8.ofNat_toNat

/-- Bytes within the range for names, read as a name and spelled again, are themselves. The library
has the converse (`Fmt.nameOf_ascii`). -/
theorem ascii_nameOf {b : ByteArray} (h : isName b = true) : ascii (nameOf b) = b := by
  have hx : ∀ x ∈ b.data.toList, x.toNat ≤ 126 := by
    intro x hx
    unfold isName at h
    have := (Array.all_eq_true_iff_forall_mem.1 h) x (Array.mem_toList_iff.1 hx)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.2
  have hl : ∀ c ∈ b.data.toList.map (fun x => Char.ofNat x.toNat), c.toNat ≤ 126 := by
    intro c hc
    obtain ⟨x, hxm, rfl⟩ := List.mem_map.1 hc
    have h1 := hx x hxm
    have hv : (Char.ofNat x.toNat).toNat = x.toNat := by
      have : Nat.isValidChar x.toNat := Or.inl (by omega)
      simp [Char.ofNat, this, Char.toNat, Char.ofNatAux]
    omega
  unfold nameOf
  show (String.ofList _).toByteArray = b
  rw [String.toByteArray_ofList, List.utf8Encode, enc_ascii _ hl, List.map_map]
  have e : b.data.toList.map ((fun c : Char => UInt8.ofNat c.toNat) ∘ fun x : UInt8 =>
      Char.ofNat x.toNat) = b.data.toList := by
    have : ∀ x ∈ b.data.toList, ((fun c : Char => UInt8.ofNat c.toNat) ∘ fun x : UInt8 =>
        Char.ofNat x.toNat) x = id x := fun x hxm => char_back x (hx x hxm)
    rw [List.map_congr_left this, List.map_id]
  rw [e]
  exact ByteArray.ext (by simp)

/-- The entry that the reader returns where an entry's spelling begins spells the same bytes. It
need not be the same entry: a number from 2^64 on is read back reduced. -/
theorem rdEntry_bytes {e e' : Entry} {pre post : ByteArray} {k : Nat}
    (hn : (ascii e.name).size < 2 ^ 64)
    (h : rdEntry (pre ++ e.bytes ++ post) pre.size = some (e', k)) : e'.bytes = e.bytes := by
  rw [rdEntry_form e pre post hn] at h
  split at h
  · rename_i hc
    obtain ⟨y, hy, h2⟩ := Option.map_eq_some_iff.1 h
    cases h2
    simp only [Entry.words, List.map_cons, List.map_nil, entryOf] at hy
    cases hy
    rw [entry_bytes, entry_bytes]
    simp only [Entry.words, List.map_cons, List.map_nil, UInt64.ofNat_toNat, ascii_nameOf hc]
  · cases h

/-- The same for several entries in a row, entry by entry. -/
theorem rdEntries_bytes : ∀ (es : List Entry) (pre post : ByteArray) (l : List Entry) (k : Nat),
    (∀ e ∈ es, (ascii e.name).size < 2 ^ 64) →
    rdMany rdEntry es.length (pre ++ cat (es.map Entry.bytes) ++ post) pre.size = some (l, k) →
    l.map Entry.bytes = es.map Entry.bytes
  | [], pre, post, l, k, _, h => by
    simp only [List.length_nil, rdMany] at h
    cases h
    rfl
  | x :: es, pre, post, l, k, hn, h => by
    rw [List.map_cons, cat_cons, List.length_cons] at h
    unfold rdMany at h
    have e1 : pre ++ (x.bytes ++ cat (es.map Entry.bytes)) ++ post =
        pre ++ x.bytes ++ (cat (es.map Entry.bytes) ++ post) := by
      simp only [ByteArray.append_assoc]
    have e2 : pre ++ x.bytes ++ (cat (es.map Entry.bytes) ++ post) =
        (pre ++ x.bytes) ++ cat (es.map Entry.bytes) ++ post := by
      simp only [ByteArray.append_assoc]
    rw [e1] at h
    split at h
    · rename_i x' j hx
      have hj := rdEntry_end (hn x List.mem_cons_self) hx
      have hb := rdEntry_bytes (hn x List.mem_cons_self) hx
      split at h
      · rename_i l' k' hr
        cases h
        rw [e2, hj, ← ByteArray.size_append] at hr
        have := rdEntries_bytes es (pre ++ x.bytes) post l' k
          (fun e he => hn e (List.mem_cons_of_mem _ he)) hr
        rw [List.map_cons, List.map_cons, hb, this]
      · cases h
    · cases h

/-- The plan that the reader returns where a plan's spelling begins has the same field and spells
the same bytes. It need not be the same plan. -/
theorem rdPlan_bytes {P P' : Plan} {pre post : ByteArray} {k : Nat}
    (hl : P.entries.length < 2 ^ 64) (hn : ∀ e ∈ P.entries, (ascii e.name).size < 2 ^ 64)
    (h : rdPlan (pre ++ P.bytes ++ post) pre.size = some (P', k)) :
    P'.field = P.field ∧ P'.bytes = P.bytes := by
  rw [plan_bytes] at h
  have a := undoes_many undoes_word (P.words.map UInt64.ofNat) (fun _ _ => trivial) pre
    (cat (P.entries.map Entry.bytes) ++ post)
  have e1 : pre ++
        (cat ((P.words.map UInt64.ofNat).map u64) ++ cat (P.entries.map Entry.bytes)) ++ post =
      pre ++ cat ((P.words.map UInt64.ofNat).map u64) ++
        (cat (P.entries.map Entry.bytes) ++ post) := by
    simp only [ByteArray.append_assoc]
  have e2 : pre ++ cat ((P.words.map UInt64.ofNat).map u64) ++
        (cat (P.entries.map Entry.bytes) ++ post) =
      pre ++ cat ((P.words.map UInt64.ofNat).map u64) ++
        cat (P.entries.map Entry.bytes) ++ post := by
    simp only [ByteArray.append_assoc]
  have hw : (P.words.map UInt64.ofNat).length = 8 := rfl
  rw [hw] at a
  generalize hW : cat ((P.words.map UInt64.ofNat).map u64) = W at a e1 e2 h
  unfold rdPlan at h
  rw [e1, a] at h
  simp only [Plan.words, List.map_cons, List.map_nil, fldOf_num, toNat_ofNat_lt _ hl] at h
  split at h
  · obtain ⟨x, hx, h2⟩ := Option.map_eq_some_iff.1 h
    cases h2
    rw [e2, ← ByteArray.size_append] at hx
    have hm := rdEntries_bytes P.entries (pre ++ W) post x.1 x.2 hn hx
    have hlen : x.1.length = P.entries.length := by
      have := congrArg List.length hm
      simpa using this
    refine ⟨rfl, ?_⟩
    rw [plan_bytes, plan_bytes]
    simp only [Plan.words, List.map_cons, List.map_nil, UInt64.ofNat_toNat, hm, hlen]
  · cases h

/-- The library's reader of parameter bytes on bytes that were spelled from a plan, a digest of 32
bytes and items, written out: what `rdPlan` returns behind the version's item; the test of the
version against that plan's field; then that plan with the digest and the items as they were
spelled. Conditions: fewer than 2^64 bytes; names within the format's rule. -/
theorem paramsRead_form {P : Plan} {cfg : ByteArray} {others : List (String × ByteArray)}
    (hb : (paramsBytes P cfg others).size < 2 ^ 64) (hc : cfg.size = 32)
    (ho : ∀ y ∈ others, okName y.1 = true) :
    paramsRead (paramsBytes P cfg others) =
      (rdPlan (item versionName (versionValue P.field) ++ P.bytes ++
          (item configName cfg ++ items others))
        (item versionName (versionValue P.field)).size).bind fun y =>
        if (versionName == versionName && versionValue P.field == versionValue y.1.field) = true
        then some ⟨y.1, cfg, others⟩ else none := by
  have hs : (cat (P.entries.map Entry.bytes)).size ≤ (paramsBytes P cfg others).size := by
    simp only [paramsBytes, paramsHead, plan_bytes, ByteArray.size_append]
    omega
  have hl : P.entries.length < 2 ^ 64 := by
    have := length_le_cat P.entries fun e _ => entry_size e
    omega
  have hn : ∀ e ∈ P.entries, (ascii e.name).size < 2 ^ 64 := by
    intro e he
    have h1 := size_le_cat (sp := Entry.bytes) P.entries e he
    have h2 : (ascii e.name).size ≤ e.bytes.size := by
      rw [entry_bytes]
      simp only [text, ByteArray.size_append]
      omega
    omega
  have hi : (items others).size ≤ (paramsBytes P cfg others).size := by
    simp only [paramsBytes, ByteArray.size_append]
    omega
  have hO : ∀ y ∈ others, okItem y := by
    intro y hy
    have h1 : (item y.1 y.2).size ≤
        (cat (others.map fun z : String × ByteArray => item z.1 z.2)).size :=
      size_le_cat (sp := fun z : String × ByteArray => item z.1 z.2) others y hy
    have h2 : (ascii y.1).size + y.2.size ≤ (item y.1 y.2).size := by
      simp only [item, textS, text, ByteArray.size_append]
      omega
    have h3 : (cat (others.map fun z : String × ByteArray => item z.1 z.2)).size =
        (items others).size := rfl
    exact ⟨ho y hy, by omega, by omega⟩
  have hC : okItem (configName, cfg) :=
    ⟨(by decide : okName configName = true),
      (by decide : (ascii configName).size < 2 ^ 64),
      by show cfg.size < 2 ^ 64; omega⟩
  generalize hv : item versionName (versionValue P.field) = V
  generalize hcf : item configName cfg = Cf
  have eb : paramsBytes P cfg others = V ++ P.bytes ++ Cf ++ items others := by
    simp only [paramsBytes, paramsHead, hv, hcf]
  have a :=
    undoes_item _ (version_ok P.field) ByteArray.empty (P.bytes ++ Cf ++ items others)
  simp only [hv, ByteArray.empty_append, ByteArray.size_empty, Nat.zero_add] at a
  have c := undoes_item _ hC (V ++ P.bytes) (items others)
  simp only [hcf, ByteArray.size_append] at c
  have d := items_back others hO (V ++ P.bytes ++ Cf ++ items others).size (by
    have := length_le_cat (sp := fun z : String × ByteArray => item z.1 z.2)
      others fun z _ => item_size z
    simp only [ByteArray.size_append, items]; omega) (V ++ P.bytes ++ Cf)
  simp only [ByteArray.size_append] at d
  have e1 : V ++ P.bytes ++ Cf ++ items others = V ++ (P.bytes ++ Cf ++ items others) := by
    simp only [ByteArray.append_assoc]
  have e2 : V ++ P.bytes ++ Cf ++ items others = V ++ P.bytes ++ (Cf ++ items others) := by
    simp only [ByteArray.append_assoc]
  rw [← e1] at a
  rw [eb]
  unfold paramsRead
  rw [a]
  simp only
  rw [← e2]
  cases hP : rdPlan (V ++ P.bytes ++ Cf ++ items others) V.size with
  | none => rfl
  | some y =>
    obtain ⟨P', j⟩ := y
    have hj : j = V.size + P.bytes.size := by
      rw [e2] at hP
      exact rdPlan_end hl hn hP
    simp only [Option.bind_some]
    by_cases hq : (versionName == versionName && versionValue P.field == versionValue P'.field)
        = true
    · rw [if_pos hq, if_pos hq, hj, c]
      simp only
      have h32 : (configName == configName && cfg.size == 32) = true := by
        rw [hc]
        rfl
      rw [if_pos h32]
      simp only [ByteArray.size_append]
      rw [d]
      rfl
    · rw [if_neg hq, if_neg hq]

/-- Parameter bytes that are spelled at two digests of one length have one length. -/
theorem size_paramsBytes_at (P : Plan) (c c' : ByteArray) (I : List (String × ByteArray))
    (h : c'.size = c.size) : (paramsBytes P c' I).size = (paramsBytes P c I).size := by
  simp only [paramsBytes, item, u64n, ByteArray.size_append, size_u64, h]

/-- If the library's reader returns x on the bytes spelled at c, it returns x with the digest c' on
the bytes spelled at c'. Conditions: fewer than 2^64 bytes at c; both digests have 32 bytes; names
within the format's rule. -/
theorem paramsRead_at {P : Plan} {c c' : ByteArray} {I : List (String × ByteArray)}
    {x : Fmt.Params} (hb : (paramsBytes P c I).size < 2 ^ 64) (hc : c.size = 32)
    (hc' : c'.size = 32) (ho : ∀ y ∈ I, okName y.1 = true)
    (h : paramsRead (paramsBytes P c I) = some x) :
    paramsRead (paramsBytes P c' I) = some { x with cfg := c' } := by
  have hb' : (paramsBytes P c' I).size < 2 ^ 64 := by
    rw [size_paramsBytes_at P c c' I (hc'.trans hc.symm)]
    exact hb
  have hs : (cat (P.entries.map Entry.bytes)).size ≤ (paramsBytes P c I).size := by
    simp only [paramsBytes, paramsHead, plan_bytes, ByteArray.size_append]
    omega
  have hl : P.entries.length < 2 ^ 64 := by
    have := length_le_cat P.entries fun e _ => entry_size e
    omega
  have hn : ∀ e ∈ P.entries, (ascii e.name).size < 2 ^ 64 := by
    intro e he
    have h1 := size_le_cat (sp := Entry.bytes) P.entries e he
    have h2 : (ascii e.name).size ≤ e.bytes.size := by
      rw [entry_bytes]
      simp only [text, ByteArray.size_append]
      omega
    omega
  rw [paramsRead_form hb hc ho] at h
  rw [paramsRead_form hb' hc' ho,
    rdPlan_post P _ (item configName c' ++ items I) (item configName c ++ items I) hl hn]
  obtain ⟨y, hy, h2⟩ := Option.bind_eq_some_iff.1 h
  rw [hy]
  simp only [Option.bind_some]
  split at h2
  · rename_i hq
    rw [if_pos hq]
    cases h2
    rfl
  · cases h2

/-- What the library's reader returns on the bytes spelled from P, c and I spells, at every digest,
the bytes that P and I spell. Conditions as in `paramsRead_form`. -/
theorem paramsRead_spells {P : Plan} {c : ByteArray} {I : List (String × ByteArray)}
    {x : Fmt.Params} (hb : (paramsBytes P c I).size < 2 ^ 64) (hc : c.size = 32)
    (ho : ∀ y ∈ I, okName y.1 = true) (h : paramsRead (paramsBytes P c I) = some x)
    (c' : ByteArray) : paramsBytes x.plan c' x.others = paramsBytes P c' I := by
  have hs : (cat (P.entries.map Entry.bytes)).size ≤ (paramsBytes P c I).size := by
    simp only [paramsBytes, paramsHead, plan_bytes, ByteArray.size_append]
    omega
  have hl : P.entries.length < 2 ^ 64 := by
    have := length_le_cat P.entries fun e _ => entry_size e
    omega
  have hn : ∀ e ∈ P.entries, (ascii e.name).size < 2 ^ 64 := by
    intro e he
    have h1 := size_le_cat (sp := Entry.bytes) P.entries e he
    have h2 : (ascii e.name).size ≤ e.bytes.size := by
      rw [entry_bytes]
      simp only [text, ByteArray.size_append]
      omega
    omega
  rw [paramsRead_form hb hc ho] at h
  obtain ⟨y, hy, h2⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨hf, hbs⟩ := rdPlan_bytes (P' := y.1) (k := y.2) hl hn hy
  split at h2
  · cases h2
    simp only [paramsBytes, paramsHead, hf, hbs]
  · cases h2

/-- What parameter bytes hold, with c' in the place of the digest and the bytes spelled anew from
the plan, c' and the items. -/
def Given.atCfg (g : Given) (c' : ByteArray) : Given :=
  { g with cfg := c', bytes := paramsBytes g.plan c' g.items }

/-- What `Given.read`, the program's reader of parameter bytes, returns on the bytes spelled from P,
c and I spells, at every digest, the bytes that P and I spell. Conditions as in `paramsRead_form`.
-/
theorem Given.read_spells {P : Plan} {c : ByteArray} {I : List (String × ByteArray)} {g : Given}
    (hb : (paramsBytes P c I).size < 2 ^ 64) (hc : c.size = 32)
    (ho : ∀ y ∈ I, okName y.1 = true) (h : Given.read (paramsBytes P c I) = some g)
    (c' : ByteArray) : paramsBytes g.plan c' g.items = paramsBytes P c' I := by
  unfold Given.read at h
  rw [paramsReadT_eq] at h
  cases hp : paramsRead (paramsBytes P c I) with
  | none =>
    rw [hp] at h
    cases h
  | some x =>
    rw [hp] at h
    simp only [Option.bind_some] at h
    split at h
    · cases h
      exact paramsRead_spells hb hc ho hp c'
    · cases h

/-- What `Given.read` returns on spelled bytes holds bytes that are spelled from its own plan,
digest and items. -/
theorem Given.read_own {P : Plan} {c : ByteArray} {I : List (String × ByteArray)} {g : Given}
    (hb : (paramsBytes P c I).size < 2 ^ 64) (hc : c.size = 32)
    (ho : ∀ y ∈ I, okName y.1 = true) (h : Given.read (paramsBytes P c I) = some g) :
    g.bytes = paramsBytes g.plan g.cfg g.items := by
  rw [Given.read_bytes h, Given.read_cfg hb hc h, Given.read_spells hb hc ho h c]

/-- **Read at c, so read at c'.** If `Given.read` returns g on the bytes spelled from P, c and I, it
returns `g.atCfg c'` on the bytes spelled from P, c' and I. Of P nothing is asked but the bound on
the bytes' length. -/
theorem Given.read_at {P : Plan} {c c' : ByteArray} {I : List (String × ByteArray)} {g : Given}
    (hb : (paramsBytes P c I).size < 2 ^ 64) (hc : c.size = 32) (hc' : c'.size = 32)
    (ho : ∀ y ∈ I, okName y.1 = true) (h : Given.read (paramsBytes P c I) = some g) :
    Given.read (paramsBytes P c' I) = some (g.atCfg c') := by
  have hsp := Given.read_spells hb hc ho h c'
  unfold Given.atCfg
  rw [hsp]
  unfold Given.read at h ⊢
  rw [paramsReadT_eq] at h ⊢
  cases hp : paramsRead (paramsBytes P c I) with
  | none =>
    rw [hp] at h
    cases h
  | some x =>
    rw [hp] at h
    rw [paramsRead_at hb hc hc' ho hp]
    simp only [Option.bind_some] at h ⊢
    split at h
    · rename_i hq
      rw [if_pos hq]
      cases h
      rfl
    · cases h

/-- The same for the reader of a link's chain: what it returns at c' is what it returned at c, with
`given` at c'. -/
theorem Link.read_at {P : Plan} {c c' : ByteArray} {I : List (String × ByteArray)} {q : Link}
    (hb : (paramsBytes P c I).size < 2 ^ 64) (hc : c.size = 32) (hc' : c'.size = 32)
    (ho : ∀ y ∈ I, okName y.1 = true) (h : Link.read (paramsBytes P c I) = some q) :
    Link.read (paramsBytes P c' I) =
      some { q with given := q.given.atCfg c' } := by
  unfold Link.read at h ⊢
  cases hg : Given.read (paramsBytes P c I) with
  | none =>
    rw [hg] at h
    cases h
  | some g =>
    rw [hg] at h
    rw [Given.read_at hb hc hc' ho hg]
    obtain ⟨gb, gp, gc, gi⟩ := g
    simp only [Given.atCfg, Option.bind_eq_bind, Option.bind_some] at h ⊢
    split at h
    · rename_i cc ll
      cases h1 : readCodes cc with
      | none =>
        rw [h1] at h
        cases h
      | some x =>
        cases h2 : readLink ll with
        | none =>
          rw [h1, h2] at h
          cases h
        | some y =>
          rw [h1, h2] at h
          cases h
          rfl
    · cases h

/-- The same for the reader of a shared chain. -/
theorem Shared.read_at {P : Plan} {c c' : ByteArray} {I : List (String × ByteArray)} {q : Shared}
    (hb : (paramsBytes P c I).size < 2 ^ 64) (hc : c.size = 32) (hc' : c'.size = 32)
    (ho : ∀ y ∈ I, okName y.1 = true) (h : Shared.read (paramsBytes P c I) = some q) :
    Shared.read (paramsBytes P c' I) =
      some { q with given := q.given.atCfg c' } := by
  unfold Shared.read at h ⊢
  cases hg : Given.read (paramsBytes P c I) with
  | none =>
    rw [hg] at h
    cases h
  | some g =>
    rw [hg] at h
    rw [Given.read_at hb hc hc' ho hg]
    obtain ⟨gb, gp, gc, gi⟩ := g
    simp only [Given.atCfg, Option.bind_eq_bind, Option.bind_some] at h ⊢
    split at h
    · rename_i cc ll
      cases h1 : readCodes cc with
      | none =>
        rw [h1] at h
        cases h
      | some x =>
        cases h2 : readLin ll with
        | none =>
          rw [h1, h2] at h
          cases h
        | some y =>
          rw [h1, h2] at h
          cases h
          rfl
    · cases h

/-- The same for the reader of a second chain. -/
theorem Second.read_at {P : Plan} {c c' : ByteArray} {I : List (String × ByteArray)} {q : Second}
    (hb : (paramsBytes P c I).size < 2 ^ 64) (hc : c.size = 32) (hc' : c'.size = 32)
    (ho : ∀ y ∈ I, okName y.1 = true) (h : Second.read (paramsBytes P c I) = some q) :
    Second.read (paramsBytes P c' I) =
      some { q with given := q.given.atCfg c' } := by
  unfold Second.read at h ⊢
  cases hg : Given.read (paramsBytes P c I) with
  | none =>
    rw [hg] at h
    cases h
  | some g =>
    rw [hg] at h
    rw [Given.read_at hb hc hc' ho hg]
    simp only [Given.atCfg, Option.bind_eq_bind, Option.bind_some] at h ⊢
    split at h
    · rename_i hq
      rw [if_pos hq]
      cases h
      rfl
    · cases h

/-- The same for the reader of a key's one-time chain. -/
theorem OneTime.read_at {P : Plan} {c c' : ByteArray} {I : List (String × ByteArray)}
    {q : OneTime} (hb : (paramsBytes P c I).size < 2 ^ 64) (hc : c.size = 32)
    (hc' : c'.size = 32) (ho : ∀ y ∈ I, okName y.1 = true)
    (h : OneTime.read (paramsBytes P c I) = some q) :
    OneTime.read (paramsBytes P c' I) =
      some { q with given := q.given.atCfg c' } := by
  unfold OneTime.read at h ⊢
  cases hg : Given.read (paramsBytes P c I) with
  | none =>
    rw [hg] at h
    cases h
  | some g =>
    rw [hg] at h
    rw [Given.read_at hb hc hc' ho hg]
    obtain ⟨gb, gp, gc, gi⟩ := g
    simp only [Given.atCfg, Option.bind_eq_bind, Option.bind_some] at h ⊢
    split at h
    · rename_i mm rr tt cc ll
      cases h1 : readNotice mm with
      | none => rw [h1] at h; cases h
      | some x1 =>
        cases h2 : readRanges rr with
        | none => rw [h1, h2] at h; cases h
        | some x2 =>
          cases h3 : readBinding tt with
          | none => rw [h1, h2, h3] at h; cases h
          | some x3 =>
            cases h4 : readCodes cc with
            | none => rw [h1, h2, h3, h4] at h; cases h
            | some x4 =>
              cases h5 : readLin ll with
              | none => rw [h1, h2, h3, h4, h5] at h; cases h
              | some x5 =>
                rw [h1, h2, h3, h4, h5] at h
                cases h
                rfl
    · cases h

/-- The same for the reader of a proof's first chain. Its last test reads the shape, the layout, the
identifiers, the pending rows and the plan's entry for a table's own sample, none of which hangs on
the digest. -/
theorem First.read_at {P : Plan} {c c' : ByteArray} {I : List (String × ByteArray)} {q : First}
    (hb : (paramsBytes P c I).size < 2 ^ 64) (hc : c.size = 32) (hc' : c'.size = 32)
    (ho : ∀ y ∈ I, okName y.1 = true) (h : First.read (paramsBytes P c I) = some q) :
    First.read (paramsBytes P c' I) =
      some { q with given := q.given.atCfg c' } := by
  unfold First.read at h ⊢
  cases hg : Given.read (paramsBytes P c I) with
  | none =>
    rw [hg] at h
    cases h
  | some g =>
    rw [hg] at h
    rw [Given.read_at hb hc hc' ho hg]
    obtain ⟨gb, gp, gc, gi⟩ := g
    simp only [Given.atCfg, Option.bind_eq_bind, Option.bind_some] at h ⊢
    split at h
    · rename_i cc ll ss yy ii nn tt more
      cases h1 : readCodes cc with
      | none => rw [h1] at h; cases h
      | some x1 =>
        cases h2 : readLin ll with
        | none => rw [h1, h2] at h; cases h
        | some x2 =>
          cases h3 : readReq ss with
          | none => rw [h1, h2, h3] at h; cases h
          | some x3 =>
            cases h4 : readLayout yy with
            | none => rw [h1, h2, h3, h4] at h; cases h
            | some x4 =>
              cases h5 : readWords ii with
              | none => rw [h1, h2, h3, h4, h5] at h; cases h
              | some x5 =>
                cases h6 : readWord nn with
                | none => rw [h1, h2, h3, h4, h5, h6] at h; cases h
                | some x6 =>
                  cases h7 : readBinding tt with
                  | none => rw [h1, h2, h3, h4, h5, h6, h7] at h; cases h
                  | some x7 =>
                    rw [h1, h2, h3, h4, h5, h6, h7] at h
                    simp only [Option.bind_some] at h ⊢
                    split at h
                    · rename_i hq
                      cases h
                      split
                      · rfl
                      · rename_i hno
                        exact absurd hq hno
                    · cases h
    · cases h

/-- The test `==` finds a byte string equal to itself. -/
theorem beq_self_bytes (a : ByteArray) : (a == a) = true := by
  cases a with
  | mk x =>
    show (x == x) = true
    exact beq_self_eq_true x

/-- Two chains with the same setting have the same setting when both are put at c'. `sameSetting` is
the one place in the readers of OnBytes/Params/Chains.lean where a digest's value is read: it
compares the two chains' digests. -/
theorem sameSetting_atCfg (a b : Given) (c' : ByteArray) (h : sameSetting a b = true) :
    sameSetting (a.atCfg c') (b.atCfg c') = true := by
  unfold sameSetting at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨h.1, beq_self_bytes c'⟩

/-- The same for the reader of a key's three chains: three plans and three lists of items, one
digest. -/
theorem KeyChains.read_at {P1 P2 P3 : Plan} {c c' : ByteArray}
    {I1 I2 I3 : List (String × ByteArray)} {q : KeyChains}
    (hb1 : (paramsBytes P1 c I1).size < 2 ^ 64) (hb2 : (paramsBytes P2 c I2).size < 2 ^ 64)
    (hb3 : (paramsBytes P3 c I3).size < 2 ^ 64) (hc : c.size = 32) (hc' : c'.size = 32)
    (ho1 : ∀ y ∈ I1, okName y.1 = true) (ho2 : ∀ y ∈ I2, okName y.1 = true)
    (ho3 : ∀ y ∈ I3, okName y.1 = true)
    (h : KeyChains.read (paramsBytes P1 c I1) (paramsBytes P2 c I2) (paramsBytes P3 c I3) =
      some q) :
    KeyChains.read (paramsBytes P1 c' I1) (paramsBytes P2 c' I2) (paramsBytes P3 c' I3) =
      some ⟨{ q.oneTime with given := q.oneTime.given.atCfg c' },
        { q.shared with given := q.shared.given.atCfg c' },
        { q.second with given := q.second.given.atCfg c' }⟩ := by
  unfold KeyChains.read at h ⊢
  cases h1 : OneTime.read (paramsBytes P1 c I1) with
  | none => rw [h1] at h; cases h
  | some a =>
    cases h2 : Shared.read (paramsBytes P2 c I2) with
    | none => rw [h1, h2] at h; cases h
    | some b =>
      cases h3 : Second.read (paramsBytes P3 c I3) with
      | none => rw [h1, h2, h3] at h; cases h
      | some d =>
        rw [h1, h2, h3] at h
        rw [OneTime.read_at hb1 hc hc' ho1 h1, Shared.read_at hb2 hc hc' ho2 h2,
          Second.read_at hb3 hc hc' ho3 h3]
        simp only [Option.bind_eq_bind, Option.bind_some] at h ⊢
        split at h
        · rename_i hq
          simp only [Bool.and_eq_true] at hq
          obtain ⟨⟨⟨⟨⟨s1, s2⟩, s3⟩, s4⟩, s5⟩, s6⟩ := hq
          cases h
          split
          · rfl
          · rename_i hno
            refine absurd ?_ hno
            simp only [Bool.and_eq_true]
            exact ⟨⟨⟨⟨⟨sameSetting_atCfg _ _ _ s1, sameSetting_atCfg _ _ _ s2⟩, s3⟩, s4⟩,
              s5⟩, s6⟩
        · cases h

/-- The same for the reader of a proof's three chains. -/
theorem ProofChains.read_at {P1 P2 P3 : Plan} {c c' : ByteArray}
    {I1 I2 I3 : List (String × ByteArray)} {q : ProofChains}
    (hb1 : (paramsBytes P1 c I1).size < 2 ^ 64) (hb2 : (paramsBytes P2 c I2).size < 2 ^ 64)
    (hb3 : (paramsBytes P3 c I3).size < 2 ^ 64) (hc : c.size = 32) (hc' : c'.size = 32)
    (ho1 : ∀ y ∈ I1, okName y.1 = true) (ho2 : ∀ y ∈ I2, okName y.1 = true)
    (ho3 : ∀ y ∈ I3, okName y.1 = true)
    (h : ProofChains.read (paramsBytes P1 c I1) (paramsBytes P2 c I2) (paramsBytes P3 c I3) =
      some q) :
    ProofChains.read (paramsBytes P1 c' I1) (paramsBytes P2 c' I2) (paramsBytes P3 c' I3) =
      some ⟨{ q.first with given := q.first.given.atCfg c' },
        { q.shared with given := q.shared.given.atCfg c' },
        { q.second with given := q.second.given.atCfg c' }⟩ := by
  unfold ProofChains.read at h ⊢
  cases h1 : First.read (paramsBytes P1 c I1) with
  | none => rw [h1] at h; cases h
  | some a =>
    cases h2 : Shared.read (paramsBytes P2 c I2) with
    | none => rw [h1, h2] at h; cases h
    | some b =>
      cases h3 : Second.read (paramsBytes P3 c I3) with
      | none => rw [h1, h2, h3] at h; cases h
      | some d =>
        rw [h1, h2, h3] at h
        rw [First.read_at hb1 hc hc' ho1 h1, Shared.read_at hb2 hc hc' ho2 h2,
          Second.read_at hb3 hc hc' ho3 h3]
        simp only [Option.bind_eq_bind, Option.bind_some] at h ⊢
        split at h
        · rename_i hq
          simp only [Bool.and_eq_true] at hq
          obtain ⟨⟨⟨⟨⟨s1, s2⟩, s3⟩, s4⟩, s5⟩, s6⟩ := hq
          cases h
          split
          · rfl
          · rename_i hno
            refine absurd ?_ hno
            simp only [Bool.and_eq_true]
            exact ⟨⟨⟨⟨⟨sameSetting_atCfg _ _ _ s1, sameSetting_atCfg _ _ _ s2⟩, s3⟩, s4⟩,
              s5⟩, s6⟩
        · cases h

/-- What `Shared.read` returns holds what `Given.read` returns on the same bytes. -/
theorem Shared.read_given {b : ByteArray} {q : Shared} (h : Shared.read b = some q) :
    Given.read b = some q.given := by
  unfold Shared.read at h
  obtain ⟨g, hg, h⟩ := opt_bind h
  rw [hg]
  split at h
  · obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    cases h
    rfl
  · cases h

/-- What `Second.read` returns holds what `Given.read` returns on the same bytes. -/
theorem Second.read_given {b : ByteArray} {q : Second} (h : Second.read b = some q) :
    Given.read b = some q.given := by
  unfold Second.read at h
  obtain ⟨g, hg, h⟩ := opt_bind h
  rw [hg]
  split at h
  · cases h
    rfl
  · cases h

end OnBytes.Params
