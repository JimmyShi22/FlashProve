-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/KeyLookup/ScanText.lean: how the reader by name of a parameter file
(Config.findWord over Config.linesOf, OnBytes/Model/Config.lean) goes through a text that is known
in pieces: whole lines that are written out, lines "name number" whose number is a letter, and a
rest of which nothing is known.

Main names.
  loop_nl, loop_other, loop_acc   one step of the cutting into lines; the finished lines come first.
  linesOf_append    behind a text that ends in a line feed the cutting begins anew.
  valLine nm n      the line: the name, a space, n in decimal, a line feed. linesOf_valLine: it is
                    one line, if the name holds no line feed.
  bytes_append      the bytes of two texts, one after the other.
  decimal_noFeed    the bytes of a number in decimal hold no line feed.
  missB n line      the line does not begin with the name n and a space. findWord_miss,
                    findWord_append_miss: the search passes over such lines.
  findWord_append_some   what the search finds in a list of lines it finds in every longer list.
  missB_head        a line valLine nm k whose name begins with another byte than n is passed over.

Limits. Nothing on any file. Nothing on soundness.

-/
import OnBytes.Model.ConfigReadersBehind
import Fmt.ParamsReadLawsProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.AtPlan
open OnBytes OnBytes.Model OnBytes.Model.Config

/-! ## 1. The cutting into lines -/

theorem loop_nl (t cur : List UInt8) (acc : List (List UInt8)) :
    linesLoop (0x0A :: t) cur acc = linesLoop t [] ((0x0A :: cur).reverse :: acc) := by
  rw [linesLoop, if_pos (by decide)]

theorem loop_other {c : UInt8} (hc : c ≠ 0x0A) (t cur : List UInt8) (acc : List (List UInt8)) :
    linesLoop (c :: t) cur acc = linesLoop t (c :: cur) acc := by
  rw [linesLoop, if_neg (by simpa using hc)]

/-- The lines that are complete come first. -/
theorem loop_acc : ∀ (t cur : List UInt8) (acc : List (List UInt8)),
    linesLoop t cur acc = acc.reverse ++ linesLoop t cur []
  | [], cur, acc => by cases cur <;> simp [linesLoop]
  | c :: t, cur, acc => by
    by_cases hc : c = 0x0A
    · subst hc
      rw [loop_nl, loop_nl, loop_acc t [] ((0x0A :: cur).reverse :: acc),
        loop_acc t [] [(0x0A :: cur).reverse]]
      simp
    · rw [loop_other hc, loop_other hc]
      exact loop_acc t (c :: cur) acc

/-- Behind a text that ends in a line feed the cutting begins anew. -/
theorem loop_append (y : List UInt8) : ∀ (t cur : List UInt8), t.getLast? = some 0x0A →
    linesLoop (t ++ y) cur [] = linesLoop t cur [] ++ linesLoop y [] []
  | [], _, h => by simp at h
  | [c], cur, h => by
    have hc : c = 0x0A := by simpa using h
    subst hc
    rw [List.singleton_append, loop_nl, loop_nl, loop_acc y [] [(0x0A :: cur).reverse]]
    simp [linesLoop]
  | c :: d :: t, cur, h => by
    have h' : (d :: t).getLast? = some 0x0A := by simpa using h
    rw [List.cons_append]
    by_cases hc : c = 0x0A
    · subst hc
      rw [loop_nl, loop_nl, loop_acc ((d :: t) ++ y) [] [(0x0A :: cur).reverse],
        loop_acc (d :: t) [] [(0x0A :: cur).reverse], loop_append y (d :: t) [] h',
        List.append_assoc]
    · rw [loop_other hc, loop_other hc]
      exact loop_append y (d :: t) (c :: cur) h'

theorem linesOf_append {t : List UInt8} (h : t.getLast? = some 0x0A) (y : List UInt8) :
    linesOf (t ++ y) = linesOf t ++ linesOf y := loop_append y t [] h

/-- A stretch without a line feed, and then a line feed, is the rest of the current line. -/
theorem loop_line : ∀ (x : List UInt8), (∀ c ∈ x, c ≠ 0x0A) → ∀ (y cur : List UInt8),
    linesLoop (x ++ 0x0A :: y) cur [] = (cur.reverse ++ x ++ [0x0A]) :: linesLoop y [] []
  | [], _, y, cur => by
    rw [List.nil_append, loop_nl, loop_acc y [] [(0x0A :: cur).reverse]]
    simp
  | c :: x, h, y, cur => by
    rw [List.cons_append, loop_other (h c (List.mem_cons_self ..)),
      loop_line x (fun a ha => h a (List.mem_cons_of_mem _ ha)) y (c :: cur)]
    simp

/-! ## 2. Bytes of texts -/

theorem bytes_append (a b : String) : bytesOf (a ++ b) = bytesOf a ++ bytesOf b := by
  rw [ConfigReaders.bytesOf_data, ConfigReaders.bytesOf_data, ConfigReaders.bytesOf_data]
  show (a ++ b).toByteArray.data.toList = a.toByteArray.data.toList ++ b.toByteArray.data.toList
  rw [String.toByteArray_append, ByteArray.data_append, Array.toList_append]

/-- The bytes of a text of characters below 127. -/
theorem bytes_ascii (s : String) (hl : ∀ c ∈ s.toList, c.toNat ≤ 126) :
    bytesOf s = s.toList.map fun c => UInt8.ofNat c.toNat := by
  have e : s.toUTF8 = s.toList.utf8Encode := by
    show s.toByteArray = _
    conv => lhs; rw [← String.ofList_toList (s := s)]
    exact String.toByteArray_ofList
  rw [ConfigReaders.bytesOf_data, e, List.utf8Encode, Fmt.enc_ascii _ hl]
  simp

/-- A character of a number in decimal. -/
theorem decimal_char (n : Nat) {c : Char} (h : c ∈ (toString n).toList) :
    48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList] at h
  have hd := Nat.isDigit_of_mem_toDigits (by decide) (by decide) h
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq, ge_iff_le,
    UInt32.le_iff_toNat_le] at hd
  exact hd

/-- The bytes of a number in decimal hold no line feed. -/
theorem decimal_noFeed (n : Nat) : ∀ b ∈ bytesOf (toString n), b ≠ 0x0A := by
  intro b hb
  rw [bytes_ascii _ fun c hc => by have := decimal_char n hc; omega] at hb
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
  have h1 := decimal_char n hc
  intro e
  have e2 := congrArg UInt8.toNat e
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at e2
  have e3 : (0x0A : UInt8).toNat = 10 := rfl
  omega

/-- The line: a name, a space, a number in decimal, a line feed. -/
def valLine (nm : String) (n : Nat) : List UInt8 :=
  bytesOf nm ++ ([0x20] ++ (bytesOf (toString n) ++ [0x0A]))

/-- It is one line. -/
theorem linesOf_valLine {nm : String} (hn : ∀ c ∈ bytesOf nm, c ≠ 0x0A) (n : Nat)
    (y : List UInt8) : linesOf (valLine nm n ++ y) = valLine nm n :: linesOf y := by
  have e : valLine nm n ++ y = (bytesOf nm ++ ([0x20] ++ bytesOf (toString n))) ++ 0x0A :: y := by
    simp [valLine, List.append_assoc]
  have hx : ∀ c ∈ bytesOf nm ++ ([0x20] ++ bytesOf (toString n)), c ≠ 0x0A := by
    intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact hn c hc
    · rcases List.mem_append.1 hc with hc | hc
      · rw [List.mem_singleton.1 hc]
        decide
      · exact decimal_noFeed n c hc
  unfold linesOf
  rw [e, loop_line _ hx]
  simp [valLine, List.append_assoc]

/-! ## 3. The search by name -/

/-- The line does not begin with the name and a space. -/
def missB (n : String) (line : List UInt8) : Bool :=
  (Params.behind (bytesOf n ++ [0x20]) (line.filter fun c => c != 0x0A)).isNone

theorem findWord_miss {n : String} {line : List UInt8} (rest : List (List UInt8))
    (h : missB n line = true) : findWord n (line :: rest) = findWord n rest := by
  have h' : Params.behind (bytesOf n ++ [0x20]) (line.filter fun c => c != 0x0A) = none :=
    Option.isNone_iff_eq_none.1 h
  simp only [findWord, h']

theorem findWord_append_miss (n : String) (L' : List (List UInt8)) :
    ∀ L : List (List UInt8), L.all (missB n) = true → findWord n (L ++ L') = findWord n L'
  | [], _ => rfl
  | line :: L, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    rw [List.cons_append, findWord_miss _ h.1]
    exact findWord_append_miss n L' L h.2

theorem findWord_append_some (n : String) (L' : List (List UInt8)) :
    ∀ (L : List (List UInt8)) (v : Nat), findWord n L = some v → findWord n (L ++ L') = some v
  | [], v, h => by simp [findWord] at h
  | line :: rest, v, h => by
    rw [List.cons_append]
    cases hb : Params.behind (bytesOf n ++ [0x20]) (line.filter fun c => c != 0x0A) with
    | none =>
      simp only [findWord, hb] at h ⊢
      exact findWord_append_some n L' rest v h
    | some w =>
      simp only [findWord, hb] at h ⊢
      by_cases hw : w.isEmpty = true
      · rw [if_pos hw] at h ⊢
        exact findWord_append_some n L' rest v h
      · rw [if_neg hw] at h ⊢
        exact h

/-- A line whose name begins with another byte than the name that is searched. -/
theorem missB_head {n nm : String} {a b : UInt8} {p q : List UInt8} (hn : bytesOf n = a :: p)
    (hm : bytesOf nm = b :: q) (hb : b ≠ 0x0A) (hab : a ≠ b) (k : Nat) :
    missB n (valLine nm k) = true := by
  unfold missB valLine
  rw [hn, hm, List.cons_append, List.cons_append, List.filter_cons_of_pos (by simpa using hb),
    Params.behind, if_neg (by simpa using hab)]
  rfl

end Lk6.AtPlan

#print axioms Lk6.AtPlan.linesOf_append
#print axioms Lk6.AtPlan.linesOf_valLine
#print axioms Lk6.AtPlan.decimal_noFeed
#print axioms Lk6.AtPlan.findWord_append_miss
#print axioms Lk6.AtPlan.findWord_append_some
#print axioms Lk6.AtPlan.missB_head
