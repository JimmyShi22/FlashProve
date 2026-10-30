-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/ReadBackLaws.lean: parameter bytes that were spelled under a digest and with further
items are read back with that digest and these items.

The program spells a chain's parameter bytes from a plan, the digest of the public files (for a call
on a model's files: the three configuration files) and further items (`Fmt.paramsBytes`), and reads
them back before it uses them (`Given.read`). The library proves that reading undoes spelling for
parameters within bounds on every number and name (`Fmt.params_back`). This file proves another
statement under other conditions: if the bytes are fewer than 2^64, the digest has 32 bytes, and the
reader returns a value at all, then the digest in that value is the digest under which the bytes
were spelled; and the further items in it are those that were spelled, if their names are within the
format's rule for names. For the plan the proof follows where each part of the reader ends, not what
it returns.

Main theorems: `paramsRead_cfg`, `paramsRead_others`, `Given.read_cfg`, `Given.read_items`.

What is not claimed. Nothing on the plan that is read back. Nothing on bytes that `Fmt.paramsBytes`
has not spelled, and nothing from 2^64 bytes on. Nothing if the reader refuses. For proofs only; the
program does not import this file.
-/
import Fmt.ParamsReadLawsProofs
import OnBytes.Params.Laws

set_option autoImplicit false

namespace OnBytes.Params

open Fmt

/-- If the reader of an entry returns a value at the place where an entry's spelling begins, it ends
where that spelling ends. Condition: the entry's name has fewer than 2^64 bytes. -/
theorem rdEntry_end {e e' : Entry} {pre post : ByteArray} {k : Nat}
    (hn : (ascii e.name).size < 2 ^ 64)
    (h : rdEntry (pre ++ e.bytes ++ post) pre.size = some (e', k)) :
    k = pre.size + e.bytes.size := by
  rw [entry_bytes] at h ⊢
  have a := undoes_text (ascii e.name) hn pre (cat ((e.words.map UInt64.ofNat).map u64) ++ post)
  have b := undoes_many undoes_word (e.words.map UInt64.ofNat) (fun _ _ => trivial)
    (pre ++ text (ascii e.name)) post
  rw [ByteArray.size_append] at b
  have e1 : pre ++ (text (ascii e.name) ++ cat ((e.words.map UInt64.ofNat).map u64)) ++ post =
      pre ++ text (ascii e.name) ++ (cat ((e.words.map UInt64.ofNat).map u64) ++ post) := by
    simp only [ByteArray.append_assoc]
  have e2 : pre ++ text (ascii e.name) ++ (cat ((e.words.map UInt64.ofNat).map u64) ++ post) =
      pre ++ text (ascii e.name) ++ cat ((e.words.map UInt64.ofNat).map u64) ++ post := by
    simp only [ByteArray.append_assoc]
  have hl : (e.words.map UInt64.ofNat).length = 11 := rfl
  rw [hl] at b
  unfold rdEntry rdName at h
  rw [e1, a] at h
  simp only at h
  split at h
  · rename_i n j hj
    split at hj
    · cases hj
      rw [e2, b] at h
      simp only at h
      obtain ⟨_, _, h2⟩ := Option.map_eq_some_iff.1 h
      cases h2
      simp only [ByteArray.size_append, Nat.add_assoc]
    · cases hj
  · cases h

/-- The same for several entries in a row. -/
theorem rdEntries_end : ∀ (es : List Entry) (pre post : ByteArray) (l : List Entry) (k : Nat),
    (∀ e ∈ es, (ascii e.name).size < 2 ^ 64) →
    rdMany rdEntry es.length (pre ++ cat (es.map Entry.bytes) ++ post) pre.size = some (l, k) →
    k = pre.size + (cat (es.map Entry.bytes)).size
  | [], pre, post, l, k, _, h => by
    simp only [List.length_nil, rdMany] at h
    cases h
    simp [cat_nil]
  | x :: es, pre, post, l, k, hn, h => by
    rw [List.map_cons, cat_cons, List.length_cons] at h
    rw [List.map_cons, cat_cons]
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
      split at h
      · rename_i l' k' hr
        cases h
        rw [e2, hj, ← ByteArray.size_append] at hr
        have := rdEntries_end es (pre ++ x.bytes) post l' k
          (fun e he => hn e (List.mem_cons_of_mem _ he)) hr
        rw [this]
        simp only [ByteArray.size_append, Nat.add_assoc]
      · cases h
    · cases h

/-- If the reader of a plan returns a value at the place where a plan's spelling begins, it ends
where that spelling ends. Conditions: the plan has fewer than 2^64 entries, and each entry's name
fewer than 2^64 bytes. -/
theorem rdPlan_end {P P' : Plan} {pre post : ByteArray} {k : Nat}
    (hl : P.entries.length < 2 ^ 64) (hn : ∀ e ∈ P.entries, (ascii e.name).size < 2 ^ 64)
    (h : rdPlan (pre ++ P.bytes ++ post) pre.size = some (P', k)) :
    k = pre.size + P.bytes.size := by
  rw [plan_bytes] at h ⊢
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
  generalize cat ((P.words.map UInt64.ofNat).map u64) = W at a e1 e2 h ⊢
  unfold rdPlan at h
  rw [e1, a] at h
  simp only [Plan.words, List.map_cons, List.map_nil, fldOf_num, toNat_ofNat_lt _ hl] at h
  split at h
  · obtain ⟨x, hx, h2⟩ := Option.map_eq_some_iff.1 h
    cases h2
    rw [e2, ← ByteArray.size_append] at hx
    have := rdEntries_end P.entries (pre ++ W) post x.1 x.2 hn hx
    rw [this]
    simp only [ByteArray.size_append, Nat.add_assoc]
  · cases h

/-- If the reader of parameter bytes returns a value on bytes that were spelled from a plan, a
digest of 32 bytes and further items, the digest in that value is that digest. Conditions: the plan
has fewer than 2^64 entries, and each entry's name fewer than 2^64 bytes. -/
theorem paramsRead_cfg_of {P : Plan} {cfg : ByteArray} {others : List (String × ByteArray)}
    {x : Fmt.Params} (hl : P.entries.length < 2 ^ 64)
    (hn : ∀ e ∈ P.entries, (ascii e.name).size < 2 ^ 64) (hc : cfg.size = 32)
    (h : paramsRead (paramsBytes P cfg others) = some x) : x.cfg = cfg := by
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
  have e1 : V ++ P.bytes ++ Cf ++ items others = V ++ (P.bytes ++ Cf ++ items others) := by
    simp only [ByteArray.append_assoc]
  have e2 : V ++ P.bytes ++ Cf ++ items others = V ++ P.bytes ++ (Cf ++ items others) := by
    simp only [ByteArray.append_assoc]
  rw [← e1] at a
  rw [eb] at h
  unfold paramsRead at h
  rw [a] at h
  simp only at h
  split at h
  · rename_i P' j hP
    rw [e2] at hP
    have hj := rdPlan_end hl hn hP
    split at h
    · rw [hj, c] at h
      simp only at h
      split at h
      · obtain ⟨_, _, h2⟩ := Option.map_eq_some_iff.1 h
        cases h2
        rfl
      · cases h
    · cases h
  · cases h

/-- A member's spelling is no longer than the whole row's. -/
theorem size_le_cat {α : Type} {sp : α → ByteArray} : ∀ (l : List α) (x : α), x ∈ l →
    (sp x).size ≤ (cat (l.map sp)).size
  | y :: l, x, hx => by
    rw [List.map_cons, cat_cons, ByteArray.size_append]
    rcases List.mem_cons.1 hx with rfl | hx'
    · omega
    · have := size_le_cat (sp := sp) l x hx'
      omega

/-- If the reader of parameter bytes returns a value on bytes that were spelled from a plan, a
digest of 32 bytes and further items, and these bytes are fewer than 2^64, the digest in that value
is that digest. -/
theorem paramsRead_cfg {P : Plan} {cfg : ByteArray} {others : List (String × ByteArray)}
    {x : Fmt.Params} (hb : (paramsBytes P cfg others).size < 2 ^ 64) (hc : cfg.size = 32)
    (h : paramsRead (paramsBytes P cfg others) = some x) : x.cfg = cfg := by
  have hs : (cat (P.entries.map Entry.bytes)).size ≤ (paramsBytes P cfg others).size := by
    simp only [paramsBytes, paramsHead, plan_bytes, ByteArray.size_append]
    omega
  refine paramsRead_cfg_of ?_ (fun e he => ?_) hc h
  · have := length_le_cat P.entries fun e _ => entry_size e
    omega
  · have h1 := size_le_cat (sp := Entry.bytes) P.entries e he
    have h2 : (ascii e.name).size ≤ e.bytes.size := by
      rw [entry_bytes]
      simp only [text, ByteArray.size_append]
      omega
    omega

/-- On such bytes the further items are read back as they were spelled, if their names are within
the format's rule for names. -/
theorem paramsRead_others {P : Plan} {cfg : ByteArray} {others : List (String × ByteArray)}
    {x : Fmt.Params} (hb : (paramsBytes P cfg others).size < 2 ^ 64) (hc : cfg.size = 32)
    (ho : ∀ y ∈ others, okName y.1 = true)
    (h : paramsRead (paramsBytes P cfg others) = some x) : x.others = others := by
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
  rw [eb] at h
  unfold paramsRead at h
  rw [a] at h
  simp only at h
  split at h
  · rename_i P' j hP
    rw [e2] at hP
    have hj := rdPlan_end hl hn hP
    split at h
    · rw [hj, c] at h
      simp only at h
      split at h
      · simp only [ByteArray.size_append] at h
        rw [d] at h
        cases h
        rfl
      · cases h
    · cases h
  · cases h

/-- The digest, for `Given.read`, the program's reader of parameter bytes: under the conditions of
`paramsRead_cfg` the digest in what it returns is the digest under which the bytes were spelled. -/
theorem Given.read_cfg {P : Plan} {cfg : ByteArray} {others : List (String × ByteArray)}
    {g : Given} (hb : (paramsBytes P cfg others).size < 2 ^ 64) (hc : cfg.size = 32)
    (h : Given.read (paramsBytes P cfg others) = some g) : g.cfg = cfg := by
  unfold Given.read at h
  rw [paramsReadT_eq] at h
  cases hp : paramsRead (paramsBytes P cfg others) with
  | none =>
    rw [hp] at h
    cases h
  | some x =>
    rw [hp] at h
    simp only [Option.bind_some] at h
    split at h
    · cases h
      exact paramsRead_cfg hb hc hp
    · cases h

/-- `Given.read` returns the further items as they were spelled, under the same conditions and if
their names are within the format's rule for names. -/
theorem Given.read_items {P : Plan} {cfg : ByteArray} {others : List (String × ByteArray)}
    {g : Given} (hb : (paramsBytes P cfg others).size < 2 ^ 64) (hc : cfg.size = 32)
    (ho : ∀ y ∈ others, okName y.1 = true)
    (h : Given.read (paramsBytes P cfg others) = some g) : g.items = others := by
  unfold Given.read at h
  rw [paramsReadT_eq] at h
  cases hp : paramsRead (paramsBytes P cfg others) with
  | none =>
    rw [hp] at h
    cases h
  | some x =>
    rw [hp] at h
    simp only [Option.bind_some] at h
    split at h
    · cases h
      exact paramsRead_others hb hc ho hp
    · cases h

end OnBytes.Params

#print axioms OnBytes.Params.Given.read_cfg
#print axioms OnBytes.Params.Given.read_items
