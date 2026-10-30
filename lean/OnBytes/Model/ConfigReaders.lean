-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/ConfigReaders.lean: on every parameter file that the strict scan admits, the
verifier's two readers of the value lines give the same numbers.

The verifier's Lean text reads the value lines of the parameter file (the lines from prof to F) in
two ways. Before the stages, `Verify.cpPolicyHeld` (OnBytes/Model/VerifyHeads.lean) asks for seven
of them by name: lt, and six of the acceptance policy's seven lines, C, theta, cap, s, sh and sT;
the seventh, F, it does not read. The reader by name is `Config.polWord`. Among the lines after the
frame's lines it gives the number on the first line that begins with the name, a space and a further
byte, and nothing if what follows the space there is not one to ten digits. The stages use the
strict scan `polScan`, which admits one order and one spelling of the lines, and the record `P.h`
that it makes of them. Both readers are in OnBytes/Model/Config.lean, and the words frame's lines,
one spelling, lax reading and due are used as there. This file proves that the readers agree in one
direction: if the scan returns P on a file, then `Config.polWord` on that whole file finds every
name of the scan's value lines, with the scan's value.

Why they agree. Both readers go through the same list of lines. While names are due, a line that the
scan passes is the due name, one space, one to ten digits and a line feed. A name holds no space, so
the searched name with a space begins such a line only if it is the line's own name. The names are
distinct. So the first line that the search by name stops at is the line from which the scan took
the value, and both take the value of the same digits. Lines after F come later in the list.

Main definitions: `NameOK`, `IsValueLine`. Main theorems: `polWord_of_scan`, and its seven uses
`polWord_C`, `polWord_theta`, `polWord_cap`, `polWord_s`, `polWord_sh`, `polWord_sT`, `polWord_lt`.
On the way: `polStep_value`, `polStep_after`, `findWord_cons_hit`, `findWord_cons_miss`,
`findWord_of_fold`. The other lemmas are in the namespace `ConfigReaders`.

What is not claimed. Every main theorem has the hypothesis that the scan returns. On a file that the
scan refuses, nothing is said, and the reader by name can still give numbers. The converse is not
stated. Nothing is said here of `Config.polWord` at the bytes after the frame's lines alone, where
`polScan` itself asks it for prof, toksrc and lt: OnBytes/Model/ConfigReadersBehind.lean carries the
law there. Nothing is said of the lines outside prof to F: the frame's lines, the optional lines,
the tables' lines, the call lines. That a value is below 2^32 and has no leading zero, which the
scan tests, is not kept. No theorem here is about `Verify.cpPolicyHeld`, a stage or a whole call:
the equations are not used in this file. Nothing is said of the C++ verifier's readers (polWord
and polScan, verifier/src/cp_verify.cpp). Nothing on soundness. For proofs only; the program does
not import this file.


-/
import OnBytes.Model.Config
import OnBytes.Params.ConfigureLaws

set_option autoImplicit false

namespace OnBytes.Model

open Config
open OnBytes.Params (exc_bind exc_either)

/-- True if the name's bytes are printable, none is a space, and there are at most 63 of them. The
empty name passes. -/
def NameOK (name : String) : Bool :=
  ((bytesOf name).all fun c => 0x20 < c && c < 0x7F) && decide ((bytesOf name).length ≤ 63)

/-- The line is the name, one space, one to ten decimal digits that spell val, and a line feed.
Leading zeros are not excluded here, and val can be 2^32 or more. -/
def IsValueLine (name : String) (val : Nat) (line : List UInt8) : Prop :=
  ∃ digits, line = bytesOf name ++ 0x20 :: digits ++ [0x0A] ∧ digits ≠ [] ∧ digits.length ≤ 10 ∧
    digits.all isDigit = true ∧ digitsValue digits = val

namespace ConfigReaders

/-! ## Lists -/

/-- Dropping as many members as `takeWhile` takes is `dropWhile`. -/
theorem drop_length_takeWhile {α : Type} (p : α → Bool) :
    ∀ l : List α, l.drop (l.takeWhile p).length = l.dropWhile p
  | [] => rfl
  | a :: l => by
    cases h : p a
    · simp [h]
    · simp [h, drop_length_takeWhile p l]

/-- `takeWhile` takes a first part whose members all pass, if the member after it fails. -/
theorem takeWhile_stop {α : Type} {p : α → Bool} {l r : List α} {x : α}
    (hl : l.all p = true) (hx : p x = false) : (l ++ x :: r).takeWhile p = l := by
  rw [List.takeWhile_append_of_pos (List.all_eq_true.1 hl),
    List.takeWhile_cons_of_neg (by simp [hx]), List.append_nil]

/-- What stands after a member that fails is still there after `dropWhile`. -/
theorem mem_dropWhile_behind {α : Type} {p : α → Bool} {r : List α} {x y : α}
    (hx : p x = false) (hy : y ∈ r) : ∀ l : List α, y ∈ (l ++ x :: r).dropWhile p
  | [] => by
    rw [List.nil_append, List.dropWhile_cons_of_neg (by simp [hx])]
    exact List.mem_cons_of_mem _ hy
  | a :: l => by
    rw [List.cons_append, List.dropWhile_cons]
    split
    · exact mem_dropWhile_behind hx hy l
    · simp [hy]

/-- If `dropWhile` leaves nothing, every member passes. -/
theorem all_of_dropWhile_nil {α : Type} {p : α → Bool} :
    ∀ {l : List α}, l.dropWhile p = [] → ∀ y ∈ l, p y = true
  | [], _, y, hy => by cases hy
  | a :: l, h, y, hy => by
    rw [List.dropWhile_cons] at h
    split at h
    · rename_i ha
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ha
      · exact all_of_dropWhile_nil h y hy
    · cases h

/-- If x is in neither a nor b, and a ++ x :: c is b ++ x :: d, then a is b. -/
theorem append_cons_inj {α : Type} [BEq α] [LawfulBEq α] {a b c d : List α} {x : α}
    (ha : x ∉ a) (hb : x ∉ b) (h : a ++ x :: c = b ++ x :: d) : a = b := by
  have e : ∀ l r : List α, x ∉ l → (l ++ x :: r).takeWhile (fun y => y != x) = l := by
    intro l r hl
    apply takeWhile_stop
    · rw [List.all_eq_true]
      intro y hy
      simp only [bne_iff_ne, ne_eq]
      rintro rfl
      exact hl hy
    · simp
  rw [← e a c ha, h, e b d hb]

/-! ## Bytes -/

/-- A printable byte other than the space is no white space. -/
theorem notSpace_of_printable {c : UInt8} (h : (decide (0x20 < c) && decide (c < 0x7F)) = true) :
    isSpace c = false := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, UInt8.lt_iff_toNat_lt] at h
  simp only [isSpace, Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
    decide_eq_false_iff_not, UInt8.le_iff_toNat_le, ← UInt8.toNat_inj]
  have e1 : (0x20 : UInt8).toNat = 32 := rfl
  have e2 : (0x0D : UInt8).toNat = 13 := rfl
  rw [e1] at h
  rw [e1, e2]
  omega

/-- A decimal digit is a byte from 48 to 57. -/
theorem digit_toNat {c : UInt8} (h : isDigit c = true) : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le] at h
  exact h

/-- A decimal digit is no byte below 48. The space, the line feed and the two signs are below. -/
theorem digit_ne {c x : UInt8} (h : isDigit c = true) (hx : x.toNat < 48) : c ≠ x := by
  rintro rfl
  have := digit_toNat h
  omega

/-- A decimal digit is no white space. -/
theorem notSpace_of_digit {c : UInt8} (h : isDigit c = true) : isSpace c = false := by
  apply notSpace_of_printable
  have := digit_toNat h
  simp only [Bool.and_eq_true, decide_eq_true_eq, UInt8.lt_iff_toNat_lt]
  have e1 : (0x20 : UInt8).toNat = 32 := rfl
  have e2 : (0x7F : UInt8).toNat = 127 := rfl
  rw [e1, e2]
  omega

/-- The walk of `ByteArray.toList`: what was gathered, then the bytes from place i on.
OnBytes/K/Left/SaysLinesPrefix.lean proves the same, above many files that this one does not
import. -/
theorem toList_loop (bs : ByteArray) : ∀ (k i : Nat) (r : List UInt8), bs.size - i = k →
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i
  | 0, i, r, h => by
    have hi : bs.data.toList.length ≤ i := by
      rw [Array.length_toList]
      show bs.size ≤ i
      omega
    rw [ByteArray.toList.loop.eq_def, if_neg (by omega), List.drop_of_length_le hi,
      List.append_nil]
  | k + 1, i, r, h => by
    have hi : i < bs.size := by omega
    have hi' : i < bs.data.toList.length := by
      rw [Array.length_toList]
      exact hi
    have e : bs.get! i = bs.data.toList[i] := by
      show bs.data[i]! = _
      rw [getElem!_pos bs.data i hi, Array.getElem_toList]
      rfl
    rw [ByteArray.toList.loop.eq_def, if_pos hi, toList_loop bs k (i + 1) _ (by omega),
      List.drop_eq_getElem_cons hi', List.reverse_cons, List.append_assoc, e]
    rfl

/-- Two texts with the same bytes are the same text. -/
theorem bytesOf_inj {n m : String} (h : bytesOf n = bytesOf m) : n = m := by
  unfold bytesOf ByteArray.toList at h
  rw [toList_loop _ _ 0 [] rfl, toList_loop _ _ 0 [] rfl] at h
  exact String.toByteArray_inj.1 (ByteArray.ext (Array.toList_inj.1 h))

/-- A name that `NameOK` admits holds no byte up to 32. The space and the line feed are such. -/
theorem not_mem_name {n : String} (hn : NameOK n = true) {x : UInt8} (hx : x.toNat ≤ 32) :
    x ∉ bytesOf n := by
  intro hm
  simp only [NameOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    UInt8.lt_iff_toNat_lt] at hn
  have := (hn.1 x hm).1
  have e1 : (0x20 : UInt8).toNat = 32 := rfl
  rw [e1] at this
  omega

/-! ## A line that passes both tests of the scan -/

/-- A line in the one spelling is a name of printable bytes other than the space, a space, one to
ten digits and a line feed. The spelling's other two conditions are not kept. -/
theorem wordLineForm_form {line : List UInt8} (h : wordLineForm line = true) :
    ∃ name digits, line = name ++ 0x20 :: digits ++ [0x0A] ∧
      (name.all fun c => 0x20 < c && c < 0x7F) = true ∧ name ≠ [] ∧ digits ≠ [] ∧
      digits.length ≤ 10 ∧ digits.all isDigit = true := by
  unfold wordLineForm at h
  dsimp only at h
  split at h
  · rename_i rest heq
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, decide_eq_true_eq,
      beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, _⟩, _⟩, h6⟩ := h
    refine ⟨_, _, ?_, List.all_takeWhile, h1, h2, h3, List.all_takeWhile⟩
    rw [drop_length_takeWhile] at heq h6
    rw [List.append_assoc, List.cons_append, ← h6, List.takeWhile_append_dropWhile, ← heq,
      List.takeWhile_append_dropWhile]
  · cases h

/-- On a line of that form whose name has at most 63 bytes, the lax reading gives the name and the
digits' value. -/
theorem scanLine_short {name digits : List UInt8}
    (hn : (name.all fun c => 0x20 < c && c < 0x7F) = true) (hne : name ≠ [])
    (hlen : name.length ≤ 63) (hd : digits.all isDigit = true) (hde : digits ≠ []) :
    scanLine (name ++ 0x20 :: digits ++ [0x0A]) = some (name, digitsValue digits) := by
  obtain ⟨c, nm, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_ne_nil hde
  have hns : ((c :: nm).all fun x => !isSpace x) = true := by
    rw [List.all_eq_true] at hn ⊢
    intro x hx
    rw [notSpace_of_printable (hn x hx)]
    rfl
  have hc : isSpace c = false := notSpace_of_printable (List.all_eq_true.1 hn c (by simp))
  have hdd : isDigit d = true := List.all_eq_true.1 hd d (by simp)
  generalize hL : (c :: nm) ++ 0x20 :: (d :: ds) ++ [0x0A] = line
  have hL' : line = (c :: nm) ++ 0x20 :: d :: (ds ++ [0x0A]) := by
    rw [← hL]
    simp
  have ha : line.dropWhile isSpace = line := by
    rw [hL', List.cons_append, List.dropWhile_cons_of_neg (by simp [hc])]
  have ht : line.takeWhile (fun x => !isSpace x) = c :: nm := by
    rw [hL']
    exact takeWhile_stop hns (by decide)
  have hk : (c :: nm).take 63 = c :: nm := List.take_of_length_le hlen
  have hdr : line.drop (c :: nm).length = 0x20 :: d :: (ds ++ [0x0A]) := by
    rw [hL', List.drop_left]
  have hb : (0x20 :: d :: (ds ++ [0x0A])).dropWhile isSpace = d :: (ds ++ [0x0A]) := by
    rw [List.dropWhile_cons_of_pos (by decide),
      List.dropWhile_cons_of_neg (by simp [notSpace_of_digit hdd])]
  have hw : (d :: (ds ++ [0x0A])).takeWhile isDigit = d :: ds := by
    rw [← List.cons_append]
    exact takeWhile_stop hd (by decide)
  have hr : (d :: (ds ++ [0x0A])).drop (d :: ds).length = [0x0A] := by
    rw [← List.cons_append, List.drop_left]
  have hz : ([0x0A] : List UInt8).dropWhile isSpace = [] := by decide
  unfold scanLine
  simp only [ha, ht, hk, hdr, hb]
  -- the three cases of the sign: the first digit is neither a minus nor a plus
  split
  · rename_i r h
    injection h with h _
    exact absurd h (digit_ne hdd (by decide))
  · rename_i r h
    injection h with h _
    exact absurd h (digit_ne hdd (by decide))
  · simp only [hw, hr, hz]
    rfl

/-- On a line of that form whose name has more than 63 bytes, the lax reading gives nothing: it
takes 63 bytes as the name, and after the number that it then looks for, the line's own digits are
left over. -/
theorem scanLine_long {name digits : List UInt8}
    (hn : (name.all fun c => 0x20 < c && c < 0x7F) = true) (hlen : 63 < name.length)
    (hd : digits.all isDigit = true) (hde : digits ≠ []) :
    scanLine (name ++ 0x20 :: digits ++ [0x0A]) = none := by
  obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_ne_nil hde
  have hsp : ∀ x ∈ name, isSpace x = false := fun x hx =>
    notSpace_of_printable (List.all_eq_true.1 hn x hx)
  have hns : (name.all fun x => !isSpace x) = true := by
    rw [List.all_eq_true]
    intro x hx
    rw [hsp x hx]
    rfl
  have hdd : isDigit d = true := List.all_eq_true.1 hd d (by simp)
  obtain ⟨c, nm, hcn⟩ : ∃ c nm, name = c :: nm := List.exists_cons_of_ne_nil (by
    rintro rfl
    simp at hlen)
  obtain ⟨e, es, hes⟩ : ∃ e es, name.drop 63 = e :: es := List.exists_cons_of_ne_nil (by
    intro h
    have := congrArg List.length h
    simp only [List.length_drop, List.length_nil] at this
    omega)
  have hc : isSpace c = false := hsp c (by simp [hcn])
  have he : isSpace e = false := hsp e (List.mem_of_mem_drop (by rw [hes]; simp))
  generalize hL : name ++ 0x20 :: (d :: ds) ++ [0x0A] = line
  have hL' : line = name ++ 0x20 :: d :: (ds ++ [0x0A]) := by
    rw [← hL]
    simp
  have ha : line.dropWhile isSpace = line := by
    rw [hL', hcn, List.cons_append, List.dropWhile_cons_of_neg (by simp [hc])]
  have ht : line.takeWhile (fun x => !isSpace x) = name := by
    rw [hL']
    exact takeWhile_stop hns (by decide)
  have hkl : (name.take 63).length = 63 := by
    rw [List.length_take]
    omega
  have hdr : line.drop 63 = e :: (es ++ 0x20 :: d :: (ds ++ [0x0A])) := by
    rw [hL', List.drop_append_of_le_length (by omega), hes]
    rfl
  have hb : (e :: (es ++ 0x20 :: d :: (ds ++ [0x0A]))).dropWhile isSpace =
      e :: (es ++ 0x20 :: d :: (ds ++ [0x0A])) := List.dropWhile_cons_of_neg (by simp [he])
  -- whatever stands before the space: behind the digits and the white space, d is left
  have key : ∀ u : List UInt8, (List.dropWhile isSpace
      (List.dropWhile isDigit (u ++ 0x20 :: d :: (ds ++ [0x0A])))).isEmpty = false := by
    intro u
    cases hq : List.dropWhile isSpace (List.dropWhile isDigit (u ++ 0x20 :: d :: (ds ++ [0x0A])))
    · have := all_of_dropWhile_nil hq d (mem_dropWhile_behind (by decide) (by simp) u)
      rw [notSpace_of_digit hdd] at this
      cases this
    · rfl
  unfold scanLine
  simp only [ha, ht, hkl, hdr, hb, drop_length_takeWhile]
  -- the three cases of the sign
  split
  · rename_i r h
    injection h with _ h
    subst h
    simp only [key, Bool.not_false, Bool.or_true, if_true]
  · rename_i r h
    injection h with _ h
    subst h
    simp only [key, Bool.not_false, Bool.or_true, if_true]
  · rw [← List.cons_append]
    simp only [key, Bool.not_false, Bool.or_true, if_true]

/-- A line that is in the one spelling, and of which the lax reading gives a name and a number, is
that name, a space, one to ten digits that spell that number, and a line feed. The name's bytes are
printable, none is a space, and there are at most 63. -/
theorem valueLine_of_tests {line name : List UInt8} {val : Nat}
    (hs : scanLine line = some (name, val)) (hw : wordLineForm line = true) :
    ∃ digits, line = name ++ 0x20 :: digits ++ [0x0A] ∧ digits ≠ [] ∧ digits.length ≤ 10 ∧
      digits.all isDigit = true ∧ digitsValue digits = val ∧
      (name.all fun c => 0x20 < c && c < 0x7F) = true ∧ name.length ≤ 63 := by
  obtain ⟨nm, ds, rfl, hn, hne, hde, hlen, hd⟩ := wordLineForm_form hw
  by_cases h63 : nm.length ≤ 63
  · rw [scanLine_short hn hne h63 hd hde] at hs
    cases hs
    exact ⟨ds, rfl, hde, hlen, hd, rfl, hn, h63⟩
  · rw [scanLine_long hn (by omega) hd hde] at hs
    cases hs

/-! ## The search by name at one line -/

/-- What is left of p ++ r after the prefix p is r. -/
theorem behind_append : ∀ p r : List UInt8, Params.behind p (p ++ r) = some r
  | [], r => by simp [Params.behind]
  | a :: p, r => by simp [Params.behind, behind_append p r]

/-- If r is left of l after the prefix p, then l is p ++ r. -/
theorem behind_some : ∀ {p l r : List UInt8}, Params.behind p l = some r → l = p ++ r
  | [], l, r, h => by
    simp only [Params.behind, Option.some.injEq] at h
    simp [h]
  | a :: p, [], r, h => by simp [Params.behind] at h
  | a :: p, b :: l, r, h => by
    simp only [Params.behind] at h
    split at h
    · rename_i hab
      rw [behind_some h, eq_of_beq hab]
      rfl
    · cases h

/-- The search by name strikes the line feeds from a line first. Of a value line whose name
`NameOK` admits, that leaves the name, the space and the digits. -/
theorem filter_valueLine {n : String} (hn : NameOK n = true) {digits : List UInt8}
    (hd : digits.all isDigit = true) :
    (bytesOf n ++ 0x20 :: digits ++ [0x0A]).filter (fun c => c != 0x0A) =
      bytesOf n ++ 0x20 :: digits := by
  have h1 : (bytesOf n).filter (fun c => c != 0x0A) = bytesOf n := by
    rw [List.filter_eq_self]
    intro a ha
    simp only [bne_iff_ne, ne_eq]
    rintro rfl
    exact not_mem_name hn (by decide) ha
  have h2 : (0x20 :: digits).filter (fun c => c != 0x0A) = 0x20 :: digits := by
    rw [List.filter_eq_self]
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · decide
    · simp only [bne_iff_ne, ne_eq]
      exact digit_ne (List.all_eq_true.1 hd a ha) (by decide)
  rw [List.filter_append, List.filter_append, h1, h2]
  simp

end ConfigReaders

open ConfigReaders

/-- The search by name stops at a value line with the searched name and gives its value. Some
hypothesis on n is needed: a name with a line feed in it is not found in its own line. `NameOK n`
asks more than that. -/
theorem findWord_cons_hit {n : String} {val : Nat} {line : List UInt8} {rest : List (List UInt8)}
    (h : IsValueLine n val line) (hn : NameOK n = true) :
    findWord n (line :: rest) = some val := by
  obtain ⟨digits, rfl, hne, hlen, hall, rfl⟩ := h
  have hb : Params.behind (bytesOf n ++ [0x20]) (bytesOf n ++ 0x20 :: digits) = some digits := by
    have := behind_append (bytesOf n ++ [0x20]) digits
    simpa using this
  unfold findWord
  simp only [filter_valueLine hn hall, hb]
  simp [hne, hall, Nat.not_lt.2 hlen]

/-- The search by name passes over a value line with another name, if `NameOK` admits the line's
name. Of the searched name nothing more is asked. -/
theorem findWord_cons_miss {n m : String} {val : Nat} {line : List UInt8}
    {rest : List (List UInt8)} (h : IsValueLine m val line) (hne : n ≠ m)
    (hm : NameOK m = true) : findWord n (line :: rest) = findWord n rest := by
  obtain ⟨digits, rfl, _, _, hall, _⟩ := h
  have hb : Params.behind (bytesOf n ++ [0x20]) (bytesOf m ++ 0x20 :: digits) = none := by
    cases hb : Params.behind (bytesOf n ++ [0x20]) (bytesOf m ++ 0x20 :: digits) with
    | none => rfl
    | some r =>
      have e := behind_some hb
      rw [List.append_assoc, List.singleton_append] at e
      -- a space in the searched name would put a space among the line's digits
      have hn : (0x20 : UInt8) ∉ bytesOf n := by
        intro hmem
        obtain ⟨a, b, hab, ha⟩ := List.eq_append_cons_of_mem hmem
        rw [hab, List.append_assoc, List.cons_append] at e
        have e1 := append_cons_inj (not_mem_name hm (by decide)) ha e
        rw [e1] at e
        have e2 := List.cons.inj (List.append_cancel_left e)
        have hsp : (0x20 : UInt8) ∈ digits := by
          rw [e2.2]
          simp
        exact digit_ne (List.all_eq_true.1 hall _ hsp) (by decide) rfl
      exact absurd (bytesOf_inj (append_cons_inj (not_mem_name hm (by decide)) hn e)).symm hne
  rw [findWord]
  simp only [filter_valueLine hm hall, hb]

/-! ## One step of the scan -/

namespace ConfigReaders

/-- A test that has passed had the condition false. Johnson/Flat/SizesPlanned.lean proves the same,
above many files that this one does not import. -/
theorem refuseIf_ok {b : Bool} {name : String} {u : Unit} (h : refuseIf b name = .ok u) :
    b = false := by
  cases b
  · rfl
  · cases h

/-- What `scanned` returns is the lax reading of the line. -/
theorem scanned_ok {line : List UInt8} {x : Option (List UInt8 × Nat)}
    (h : scanned line = .ok x) : scanLine line = x := by
  unfold scanned at h
  split at h
  · cases h
  · cases h
    rfl

/-- A line that `oneSpelling` passes is in the one spelling. -/
theorem oneSpelling_ok {line : List UInt8} {u : Unit} (h : oneSpelling line = .ok u) :
    wordLineForm line = true := by
  unfold oneSpelling at h
  split at h
  · assumption
  · cases h

/-- Reading a call line leaves the values read as they are. Johnson/Road/HeadScan.lean has the same
statement, above many files that this one does not import. -/
theorem callLine_vals {prof : Nat} {s s' : PolState} {line : List UInt8}
    (h : callLine prof s line = .ok s') : s'.vals = s.vals := by
  unfold callLine at h
  repeat' first
    | (obtain ⟨_, _, h⟩ := exc_bind h)
    | (split at h)
  all_goals first
    | (cases h; rfl)
    | cases h

/-- Reading a line after the line F leaves the values read as they are. Johnson/Road/HeadScan.lean
has the same statement. -/
theorem lineAfterF_vals {prof : Nat} {afterTbl : Bool} {s s' : PolState} {line : List UInt8}
    (h : lineAfterF prof afterTbl s line = .ok s') : s'.vals = s.vals := by
  unfold lineAfterF at h
  repeat' first
    | (obtain ⟨_, _, h⟩ := exc_bind h)
    | (split at h)
  all_goals first
    | (cases h; rfl)
    | exact callLine_vals h
    | cases h

end ConfigReaders

/-- While a name is due, a line that the scan's step passes is a value line with that name, the step
adds the line's value to the values read, and `NameOK` admits the name. -/
theorem polStep_value {frame : Params.Lines} {prof : Nat} {names : Array String} {s s' : PolState}
    {line : List UInt8} {due : String} (hd : names[s.vals.size]? = some due)
    (h : polStep frame prof names s line = .ok s') :
    NameOK due = true ∧ ∃ val, s'.vals = s.vals.push val ∧ IsValueLine due val line := by
  unfold polStep at h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  dsimp only at h
  rw [hd] at h
  dsimp only at h
  obtain ⟨x, hx, h⟩ := exc_bind h
  cases x with
  | none => cases h
  | some y =>
    obtain ⟨name, val⟩ := y
    dsimp only at h
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, hname, h⟩ := exc_bind h
    obtain ⟨_, hsp, h⟩ := exc_bind h
    obtain ⟨_, h⟩ := exc_either h
    cases h
    have hname' : name = bytesOf due := by simpa using refuseIf_ok hname
    subst hname'
    obtain ⟨digits, hl, h1, h2, h3, h4, h5, h6⟩ :=
      valueLine_of_tests (scanned_ok hx) (oneSpelling_ok hsp)
    refine ⟨?_, val, rfl, digits, hl, h1, h2, h3, h4⟩
    simp only [NameOK, h5, h6, decide_true, Bool.and_self]

/-- When no name is due any more, the scan's step leaves the values read as they are. -/
theorem polStep_after {frame : Params.Lines} {prof : Nat} {names : Array String} {s s' : PolState}
    {line : List UInt8} (hd : names[s.vals.size]? = none)
    (h : polStep frame prof names s line = .ok s') : s'.vals = s.vals := by
  unfold polStep at h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  dsimp only at h
  rw [hd] at h
  have e := lineAfterF_vals h
  exact e

/-! ## The whole scan -/

/-- The scan's steps over a list of lines. due: the names that are still due before the first of
these lines; that they are distinct is a hypothesis. The steps add values to those read before. For
every name that got one of the added values, `NameOK` admits it, and the search by name in these
lines finds that value. -/
theorem findWord_of_fold {frame : Params.Lines} {prof : Nat} {names : Array String} :
    ∀ {lines : List (List UInt8)} {s s' : PolState} {due : List String},
    names.toList.drop s.vals.size = due → due.Nodup →
    lines.foldlM (polStep frame prof names) s = .ok s' →
    ∃ added, s'.vals.toList = s.vals.toList ++ added ∧
      ∀ n ∈ (due.zip added).map Prod.fst, NameOK n = true ∧
        ∃ val, findWord n lines = some val ∧ (due.zip added).lookup n = some val
  | [], s, s', due, _, _, h => by
    cases h
    exact ⟨[], by simp, by simp⟩
  | line :: lines, s, s', due, hdue, hnd, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨s1, h1, h⟩ := exc_bind h
    have hhead : names[s.vals.size]? = due.head? := by
      rw [← hdue, List.head?_drop, Array.getElem?_toList]
    cases due with
    | nil =>
      have e := polStep_after hhead h1
      obtain ⟨added, ha, _⟩ := findWord_of_fold (due := []) (by rw [e]; exact hdue) hnd h
      exact ⟨added, by rw [ha, e], by simp⟩
    | cons d due =>
      obtain ⟨hok, val, e, hv⟩ := polStep_value hhead h1
      have hdue1 : names.toList.drop s1.vals.size = due := by
        rw [e, Array.size_push, ← List.tail_drop, hdue]
        rfl
      obtain ⟨hnot, hnd1⟩ := List.nodup_cons.1 hnd
      obtain ⟨added, ha, hall⟩ := findWord_of_fold hdue1 hnd1 h
      refine ⟨val :: added, by rw [ha, e]; simp, ?_⟩
      intro n hn
      simp only [List.zip_cons_cons, List.map_cons, List.mem_cons] at hn
      rcases hn with rfl | hn
      · exact ⟨hok, val, findWord_cons_hit hv hok, by
          rw [List.zip_cons_cons, List.lookup_cons_self]⟩
      · obtain ⟨hokn, v, hf, hl⟩ := hall n hn
        have hne : n ≠ d := by
          rintro rfl
          obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.1 hn
          exact hnot (List.of_mem_zip hab).1
        refine ⟨hokn, v, by rw [findWord_cons_miss hv hne hok, hf], ?_⟩
        rw [List.zip_cons_cons, List.lookup_cons, beq_false_of_ne hne]
        exact hl

namespace ConfigReaders

/-- The names of the value lines are distinct, at every profile. Shown by evaluating the test on
each of the list's two forms. -/
theorem valueNames_nodup (prof : Nat) : (valueNames prof).Nodup := by
  unfold valueNames
  split <;> decide

/-- What a scan that returns has done: it has read the frame's lines, has taken the profile from
what the reader by name finds for prof in the bytes after them, has made its steps over the lines
after them with that profile's names, has one value for each name, pairs names and values in their
order, and makes its record from these pairs. -/
theorem polScan_parts {pol : ByteArray} {P : PolScan} (h : polScan pol = .ok P) :
    ∃ frame rest prof s, Params.readLines pol = .ok (frame, rest) ∧ P.frame = frame ∧
      prof = (polWord rest "prof").getD 0 % 16 ∧
      (linesOf rest.toList).foldlM (polStep frame prof (valueNames prof).toArray) {} = .ok s ∧
      s.vals.size = (valueNames prof).length ∧
      P.values = (valueNames prof).zip s.vals.toList ∧ P.h = hdrOf P.value := by
  unfold polScan at h
  cases hr : Params.readLines pol with
  | error e =>
    rw [hr] at h
    cases h
  | ok x =>
    rw [hr] at h
    obtain ⟨frame, rest⟩ := x
    dsimp only at h
    obtain ⟨w, hw, h⟩ := exc_bind h
    cases hw
    dsimp only at h
    obtain ⟨_, _, h⟩ := exc_bind h
    split at h
    · obtain ⟨_, _, h⟩ := exc_bind h
      obtain ⟨_, _, h⟩ := exc_bind h
      obtain ⟨s, hs, h⟩ := exc_bind h
      obtain ⟨_, hsize, h⟩ := exc_bind h
      obtain ⟨_, _, h⟩ := exc_bind h
      cases h
      exact ⟨frame, rest, _, s, rfl, rfl, rfl, hs, by simpa using refuseIf_ok hsize, rfl, rfl⟩
    · cases h

end ConfigReaders

/-- If the strict scan returns P on a parameter file, the reader by name finds on that whole file
every name of the scan's value lines, with the scan's value. -/
theorem polWord_of_scan {pol : ByteArray} {P : PolScan} (h : polScan pol = .ok P) {n : String}
    (hn : n ∈ P.values.map Prod.fst) : Config.polWord pol n = some (P.value n) := by
  obtain ⟨frame, rest, prof, s, hr, _, _, hs, _, hv, _⟩ := polScan_parts h
  obtain ⟨added, ha, hall⟩ :=
    findWord_of_fold (due := valueNames prof) rfl (valueNames_nodup prof) hs
  have ea : s.vals.toList = added := ha
  rw [hv, ea] at hn
  obtain ⟨_, val, hf, hl⟩ := hall n hn
  unfold polWord PolScan.value
  rw [hr, hv, ea, hl]
  exact hf

namespace ConfigReaders

/-- `polWord_of_scan` for a name that is a value line's name at every profile. -/
theorem polWord_of_name {pol : ByteArray} {P : PolScan} (h : polScan pol = .ok P) {n : String}
    (hn : ∀ prof, n ∈ valueNames prof) : Config.polWord pol n = some (P.value n) := by
  apply polWord_of_scan h
  obtain ⟨_, _, prof, s, _, _, _, _, hsize, hv, _⟩ := polScan_parts h
  rw [hv, List.map_fst_zip (by simp [hsize])]
  exact hn prof

/-- The record of a scan that returns is made from the scan's values by name. -/
theorem polScan_h {pol : ByteArray} {P : PolScan} (h : polScan pol = .ok P) :
    P.h = hdrOf P.value := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hh⟩ := polScan_parts h
  exact hh

end ConfigReaders

/-! ## The seven lines that `Verify.cpPolicyHeld` reads by name

Each theorem has the hypothesis that the strict scan returns P on the file. -/

/-- The line C by name is the clip in the scan's record. -/
theorem polWord_C {pol : ByteArray} {P : PolScan} (h : polScan pol = .ok P) :
    Config.polWord pol "C" = some P.h.clipC := by
  rw [polScan_h h]
  exact polWord_of_name h (by simp [valueNames])

/-- The line theta by name is the bound on the mean in the scan's record. -/
theorem polWord_theta {pol : ByteArray} {P : PolScan} (h : polScan pol = .ok P) :
    Config.polWord pol "theta" = some P.h.theta := by
  rw [polScan_h h]
  exact polWord_of_name h (by simp [valueNames])

/-- The line cap by name is the cap in the scan's record. -/
theorem polWord_cap {pol : ByteArray} {P : PolScan} (h : polScan pol = .ok P) :
    Config.polWord pol "cap" = some P.h.cap := by
  rw [polScan_h h]
  exact polWord_of_name h (by simp [valueNames])

/-- The line s by name is the stated scale of the logits in the scan's record. -/
theorem polWord_s {pol : ByteArray} {P : PolScan} (h : polScan pol = .ok P) :
    Config.polWord pol "s" = some P.h.logS := by
  rw [polScan_h h]
  exact polWord_of_name h (by simp [valueNames])

/-- The line sh by name is the field digSh of the scan's record. -/
theorem polWord_sh {pol : ByteArray} {P : PolScan} (h : polScan pol = .ok P) :
    Config.polWord pol "sh" = some P.h.digSh := by
  rw [polScan_h h]
  exact polWord_of_name h (by simp [valueNames])

/-- The line sT by name is the field tabS of the scan's record. -/
theorem polWord_sT {pol : ByteArray} {P : PolScan} (h : polScan pol = .ok P) :
    Config.polWord pol "sT" = some P.h.tabS := by
  rw [polScan_h h]
  exact polWord_of_name h (by simp [valueNames])

/-- The line lt by name is the field lt of the scan's record. -/
theorem polWord_lt {pol : ByteArray} {P : PolScan} (h : polScan pol = .ok P) :
    Config.polWord pol "lt" = some P.h.lt := by
  rw [polScan_h h]
  exact polWord_of_name h (by simp [valueNames])

end OnBytes.Model

#print axioms OnBytes.Model.polStep_value
#print axioms OnBytes.Model.polStep_after
#print axioms OnBytes.Model.findWord_cons_hit
#print axioms OnBytes.Model.findWord_cons_miss
#print axioms OnBytes.Model.findWord_of_fold
#print axioms OnBytes.Model.polWord_of_scan
#print axioms OnBytes.Model.polWord_C
#print axioms OnBytes.Model.polWord_theta
#print axioms OnBytes.Model.polWord_cap
#print axioms OnBytes.Model.polWord_s
#print axioms OnBytes.Model.polWord_sh
#print axioms OnBytes.Model.polWord_sT
#print axioms OnBytes.Model.polWord_lt
