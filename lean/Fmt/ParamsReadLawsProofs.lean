-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/ParamsReadLawsProofs.lean: the proof of Fmt/ParamsReadLaws.lean's `Spec.params_back` (reading
the parameter bytes undoes their spelling): p.fit = true → paramsRead p.bytes = some p.

Proofs, and four small definitions for them. No Mathlib.
How: by the tools for "a reader undoes a spelling, whatever stands before and behind"
(Fmt/Rules1Laws.lean: `Undoes`), part by part. A spelling is an encoding as bytes, a reader (`Rd α`,
Fmt/Rules1.lean) a decoder that may refuse.

Main names:
  `enc_ascii`, `ascii_data`: the bytes of a name with `okName` (`enc_ascii`: of characters below
    0x7F) are its characters' numbers, one byte each.
  `nameOf_ascii`, `isName_ascii`: so, for a name with `okName`, the name that is read back from
    these bytes is the name, and the bytes pass the reader's test on names.
  `undoes_item`: an item (`okItem`: the name has `okName`, name and value have fewer than 2^64
    bytes).
  `entry_bytes`, `undoes_entry`: an entry of a plan (`okEntry`).
  `plan_bytes`, `undoes_plan`: a plan (`okPlan`); the reader's test "no more entries than bytes are
    left" holds since an entry has at least one byte.
  `items_back`: the further items, each with `okItem`, up to the end of the bytes, at any fuel that
    is no less than their number.
  `params_back`: the theorem.

What is not claimed: the head of Fmt/ParamsReadLaws.lean, 4.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Fmt.ParamsReadLaws
import Fmt.Rules1Laws

namespace Fmt

theorem enc_ascii (l : List Char) (h : ∀ c ∈ l, c.toNat ≤ 126) :
    l.flatMap String.utf8EncodeChar = l.map fun c => UInt8.ofNat c.toNat := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    have hc : c.toNat ≤ 126 := h c (by simp)
    have e : String.utf8EncodeChar c = [UInt8.ofNat c.toNat] := by
      have : c.val.toNat ≤ 127 := by have : c.val.toNat = c.toNat := rfl; omega
      simp only [String.utf8EncodeChar, this, if_true]; rfl
    rw [List.flatMap_cons, e, ih fun x hx => h x (by simp [hx])]; rfl

theorem ascii_data (s : String) (h : okName s = true) :
    (ascii s).data.toList = s.toList.map fun c => UInt8.ofNat c.toNat := by
  have hl : ∀ c ∈ s.toList, c.toNat ≤ 126 := fun c hc => by
    have := List.all_eq_true.1 h c hc; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact this.2
  have e : (ascii s) = s.toList.utf8Encode := by
    show s.toByteArray = _
    conv => lhs; rw [← String.ofList_toList (s := s)]
    exact String.toByteArray_ofList
  rw [e, List.utf8Encode, enc_ascii _ hl]
  simp

theorem nameOf_ascii (s : String) (h : okName s = true) : nameOf (ascii s) = s := by
  have hl : ∀ c ∈ s.toList, c.toNat ≤ 126 := fun c hc => by
    have := List.all_eq_true.1 h c hc; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact this.2
  unfold nameOf
  rw [ascii_data s h, List.map_map]
  have : s.toList.map
        ((fun x : UInt8 => Char.ofNat x.toNat) ∘ fun c : Char => UInt8.ofNat c.toNat) =
      s.toList := by
    have : ∀ c ∈ s.toList,
        ((fun x : UInt8 => Char.ofNat x.toNat) ∘ fun c : Char => UInt8.ofNat c.toNat) c =
          id c := fun c hc => by
      have h1 := hl c hc
      show Char.ofNat (UInt8.ofNat c.toNat).toNat = c
      rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
      exact Char.ofNat_toNat c
    rw [List.map_congr_left this, List.map_id]
  rw [this, String.ofList_toList]

theorem isName_ascii (s : String) (h : okName s = true) : isName (ascii s) = true := by
  unfold isName
  rw [← Array.all_toList, ascii_data s h, List.all_map]
  refine List.all_eq_true.2 fun c hc => ?_
  have := List.all_eq_true.1 h c hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  simp only [Function.comp, Bool.and_eq_true, decide_eq_true_eq,
    UInt8.le_iff_toNat_le, UInt8.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (by omega)]
  exact this

/-- an item within the bounds -/
def okItem (x : String × ByteArray) : Prop :=
  okName x.1 = true ∧ (ascii x.1).size < 2 ^ 64 ∧ x.2.size < 2 ^ 64

theorem undoes_item : Undoes rdItem (fun x => item x.1 x.2) okItem := by
  intro x hx pre post
  obtain ⟨h1, h2, h3⟩ := hx
  have e : pre ++ item x.1 x.2 ++ post = pre ++ text (ascii x.1) ++ (text x.2 ++ post) := by
    simp only [item, textS, text, ByteArray.append_assoc]
  have a := undoes_name (ascii x.1) ⟨h2, isName_ascii _ h1⟩ pre (text x.2 ++ post)
  have e2 : pre ++ text (ascii x.1) ++ (text x.2 ++ post) =
      (pre ++ text (ascii x.1)) ++ text x.2 ++ post := by
    simp only [ByteArray.append_assoc]
  have b := undoes_text x.2 h3 (pre ++ text (ascii x.1)) post
  rw [ByteArray.size_append] at b
  have sz : (item x.1 x.2).size = (text (ascii x.1)).size + (text x.2).size := by
    simp only [item, textS, text, ByteArray.size_append]; omega
  unfold rdItem
  rw [e, a]
  simp only
  rw [e2, b, sz, nameOf_ascii _ h1]
  simp only [Option.map_some, Nat.add_assoc]

theorem toNat_ofNat_lt (n : Nat) (h : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n := by
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt h]

/-- an entry within the bounds -/
def okEntry (e : Entry) : Prop :=
  okName e.name = true ∧ (ascii e.name).size < 2 ^ 64 ∧ ∀ n ∈ e.words, n < 2 ^ 64

theorem entry_bytes (e : Entry) :
    e.bytes = text (ascii e.name) ++ cat ((e.words.map UInt64.ofNat).map u64) := by
  simp only [Entry.bytes, Entry.words, textS, u64n, List.map_cons, List.map_nil, cat_cons, cat_nil,
    ByteArray.append_assoc, ByteArray.append_empty]

theorem undoes_entry : Undoes rdEntry Entry.bytes okEntry := by
  intro e he pre post
  obtain ⟨h1, h2, h3⟩ := he
  rw [entry_bytes]
  have a := undoes_name (ascii e.name) ⟨h2, isName_ascii _ h1⟩ pre
    (cat ((e.words.map UInt64.ofNat).map u64) ++ post)
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
  unfold rdEntry
  rw [e1, a]
  simp only
  rw [e2, b]
  simp only [nameOf_ascii _ h1]
  have hw : entryOf e.name (e.words.map UInt64.ofNat) = some e := by
    simp only [Entry.words, List.map_cons, List.map_nil, entryOf]
    have g : ∀ n ∈ e.words, (UInt64.ofNat n).toNat = n := fun n hn => toNat_ofNat_lt n (h3 n hn)
    simp only [Entry.words, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at g
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩ := g
    rw [g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11]
  rw [hw]
  simp only [Option.map_some, ByteArray.size_append, Nat.add_assoc]

/-- the eight words of a plan -/
def Plan.words (P : Plan) : List Nat :=
  [P.field.num, 1, P.salt, P.nonce, P.posB, P.samples, P.saved, P.entries.length]

theorem plan_bytes (P : Plan) :
    P.bytes = cat ((P.words.map UInt64.ofNat).map u64) ++ cat (P.entries.map Entry.bytes) := by
  simp only [Plan.bytes, Plan.words, u64n, List.map_cons, List.map_nil, cat_cons, cat_nil,
    ByteArray.append_assoc, ByteArray.append_empty]

theorem entry_size (e : Entry) : 1 ≤ e.bytes.size := by
  rw [entry_bytes]; simp only [text, u64n, ByteArray.size_append, size_u64]; omega

/-- a plan within the bounds -/
def okPlan (P : Plan) : Prop :=
  (∀ n ∈ [P.salt, P.nonce, P.posB, P.samples, P.saved, P.entries.length], n < 2 ^ 64) ∧
  ∀ e ∈ P.entries, okEntry e

theorem fldOf_num (f : Fld) : fldOf (UInt64.ofNat f.num).toNat = some f := by cases f <;> rfl

theorem undoes_plan : Undoes rdPlan Plan.bytes okPlan := by
  intro P hP pre post
  obtain ⟨h1, h2⟩ := hP
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h1
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := h1
  rw [plan_bytes]
  have a := undoes_many undoes_word (P.words.map UInt64.ofNat) (fun _ _ => trivial) pre
    (cat (P.entries.map Entry.bytes) ++ post)
  have b :=
    undoes_many undoes_entry P.entries h2 (pre ++ cat ((P.words.map UInt64.ofNat).map u64)) post
  rw [ByteArray.size_append] at b
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
  have hl : (P.words.map UInt64.ofNat).length = 8 := rfl
  rw [hl] at a
  have hle : P.entries.length ≤ (cat (P.entries.map Entry.bytes)).size :=
    length_le_cat P.entries fun e _ => entry_size e
  generalize cat ((P.words.map UInt64.ofNat).map u64) = W at a b e1 e2 ⊢
  unfold rdPlan
  rw [e1, a]
  simp only [Plan.words, List.map_cons, List.map_nil, fldOf_num, toNat_ofNat_lt _ g1,
    toNat_ofNat_lt _ g2, toNat_ofNat_lt _ g3, toNat_ofNat_lt _ g4,
    toNat_ofNat_lt _ g5, toNat_ofNat_lt _ g6]
  have hc : (UInt64.ofNat 1 == 1 &&
        decide (pre.size + W.size + P.entries.length ≤
            (pre ++ W ++ (cat (P.entries.map Entry.bytes) ++ post)).size)) = true := by
    simp only [ByteArray.size_append, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨rfl, by omega⟩
  rw [if_pos hc, e2, b]
  simp only [Option.map_some, ByteArray.size_append, Nat.add_assoc]

theorem item_size (x : String × ByteArray) : 1 ≤ (item x.1 x.2).size := by
  simp only [item, textS, text, u64n, ByteArray.size_append, size_u64]; omega

theorem items_cons (x : String × ByteArray) (l : List (String × ByteArray)) :
    items (x :: l) = item x.1 x.2 ++ items l := by
  simp only [items, List.map_cons, cat_cons]

theorem items_back (l : List (String × ByteArray)) :
    ∀ (_ : ∀ x ∈ l, okItem x) (fuel : Nat) (_ : l.length ≤ fuel) (pre : ByteArray),
      rdItems fuel (pre ++ items l) pre.size = some (l, (pre ++ items l).size) := by
  induction l with
  | nil =>
    intro _ fuel _ pre
    have e : pre ++ items [] = pre := by
      simp only [items, List.map_nil, cat_nil, ByteArray.append_empty]
    rw [e]
    cases fuel <;> simp [rdItems]
  | cons x l ih =>
    intro hl fuel hf pre
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp only [List.length_cons] at hf; omega⟩
    have hx : okItem x := hl x (by simp)
    have a := undoes_item x hx pre (items l)
    have e : pre ++ items (x :: l) = pre ++ item x.1 x.2 ++ items l := by
      rw [items_cons, ByteArray.append_assoc]
    have hne : (pre.size == (pre ++ item x.1 x.2 ++ items l).size) = false := by
      have := item_size x
      simp only [ByteArray.size_append, beq_eq_false_iff_ne, ne_eq]; omega
    have b := ih (fun y hy => hl y (by simp [hy])) f
      (by simp only [List.length_cons] at hf; omega) (pre ++ item x.1 x.2)
    rw [ByteArray.size_append] at b
    rw [e]
    unfold rdItems
    simp only [hne, Bool.false_eq_true, if_false]
    rw [a]
    simp only
    rw [b]
    simp only [Option.map_some]

theorem nameFit_iff (s : String) :
    nameFit s = true ↔ okName s = true ∧ (ascii s).size < 2 ^ 64 := by
  simp only [nameFit, Bool.and_eq_true, decide_eq_true_eq]

theorem okEntry_of_fit (e : Entry) (h : e.fit = true) : okEntry e := by
  simp only [Entry.fit, Bool.and_eq_true, nameFit_iff, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem okPlan_of_fit (P : Plan) (h : P.fit = true) : okPlan P := by
  simp only [Plan.fit, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, fun e he => okEntry_of_fit e (h.2 e he)⟩

theorem version_ok (f : Fld) : okItem (versionName, versionValue f) := by
  refine ⟨(by decide : okName versionName = true),
    (by decide : (ascii versionName).size < 2 ^ 64),
    ?_⟩
  cases f <;> decide

theorem version_beq (f : Fld) : (versionValue f == versionValue f) = true := by cases f <;> decide

theorem params_back : Spec.params_back := by
  intro p hp
  simp only [Params.fit, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    nameFit_iff, decide_eq_true_eq] at hp
  obtain ⟨⟨h1, h2⟩, h3⟩ := hp
  have hP := okPlan_of_fit _ h1
  have hO : ∀ x ∈ p.others, okItem x := fun x hx => ⟨(h3 x hx).1.1, (h3 x hx).1.2, (h3 x hx).2⟩
  have hC : okItem (configName, p.cfg) :=
    ⟨(by decide : okName configName = true),
      (by decide : (ascii configName).size < 2 ^ 64),
      by show p.cfg.size < 2 ^ 64; omega⟩
  generalize hv : item versionName (versionValue p.plan.field) = V
  generalize hc : item configName p.cfg = Cf
  have eb : p.bytes = V ++ p.plan.bytes ++ Cf ++ items p.others := by
    simp only [Params.bytes, paramsBytes, paramsHead, hv, hc]
  have a :=
    undoes_item _ (version_ok p.plan.field) ByteArray.empty (p.plan.bytes ++ Cf ++ items p.others)
  simp only [hv, ByteArray.empty_append, ByteArray.size_empty, Nat.zero_add] at a
  have b := undoes_plan p.plan hP V (Cf ++ items p.others)
  have c := undoes_item _ hC (V ++ p.plan.bytes) (items p.others)
  simp only [hc, ByteArray.size_append] at c
  have d := items_back p.others hO (V ++ p.plan.bytes ++ Cf ++ items p.others).size (by
    have := length_le_cat (sp := fun x : String × ByteArray => item x.1 x.2)
      p.others fun x _ => item_size x
    simp only [ByteArray.size_append, items]; omega) (V ++ p.plan.bytes ++ Cf)
  simp only [ByteArray.size_append] at d
  have e1 : V ++ p.plan.bytes ++ Cf ++ items p.others =
      V ++ (p.plan.bytes ++ Cf ++ items p.others) := by
    simp only [ByteArray.append_assoc]
  have e2 : V ++ p.plan.bytes ++ Cf ++ items p.others =
      V ++ p.plan.bytes ++ (Cf ++ items p.others) := by
    simp only [ByteArray.append_assoc]
  rw [← e1] at a
  rw [← e2] at b
  rw [eb]
  unfold paramsRead
  rw [a]
  simp only
  rw [b]
  simp only [beq_self_eq_true, version_beq, Bool.and_self, if_true]
  rw [c]
  simp only [beq_self_eq_true, h2, Bool.and_self, if_true, ByteArray.size_append]
  rw [d]
  simp only [Option.map_some]

end Fmt
