-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/CodingSeq.lean: partial codes of strings that are made of fields.

Definitions that compute, with their laws. Generic: no format, but for the last item, a word of the
programs' format (rule R1.1-like: eight bytes, the lowest first).
A partial code (`PCode`, Run/CodingPart.lean) writes some points of a type as bit strings,
injectively, with a parser.

Main names: `PCode.Len`, `PCode.pull`, `PCode.pre`, `PCode.cons`, `PCode.ins`, `pBits`, `pWord`.

Limits: this file does not say which format.

Terms: lean/GLOSSARY.md.
-/
import Run.CodingPage164
import Fmt.Rules1Laws
import Fmt.Rules1Only

set_option autoImplicit false

namespace Run
open Rom

namespace PCode
variable {A B : Type}

/-- Every string that is written has n bits. -/
def Len (p : PCode A) (n : ℕ) : Prop := ∀ a s, p.put a = some s → s.length = n

/-- A partial code carried to another type along two partial maps that undo each other (`h1`, `h2`).
-/
def pull (p : PCode A) (f : B → Option A) (g : A → Option B)
    (h1 : ∀ b a, f b = some a → g a = some b) (h2 : ∀ a b, g a = some b → f b = some a) :
    PCode B where
  put := fun b => (f b).bind p.put
  parse := fun s => (p.parse s).bind g
  parse_put := fun b s h => by
    cases hf : f b with
    | none => rw [hf] at h; cases h
    | some a =>
        rw [hf] at h
        rw [p.parse_put a s h]
        exact h1 b a hf
  put_parse := fun s b h => by
    cases hp : p.parse s with
    | none => rw [hp] at h; cases h
    | some a =>
        rw [hp] at h
        rw [h2 a b h]
        exact p.put_parse s a hp

/-- A constant string in front. -/
def pre (c : List Bool) (p : PCode A) : PCode A where
  put := fun a => (p.put a).map (c ++ ·)
  parse := fun s => (strip c s).bind p.parse
  parse_put := fun a s h => by
    cases hp : p.put a with
    | none => rw [hp] at h; cases h
    | some u =>
        rw [hp] at h
        rw [← Option.some.inj h, strip_append]
        exact p.parse_put a u hp
  put_parse := fun s a h => by
    cases hs : strip c s with
    | none => rw [hs] at h; cases h
    | some u =>
        rw [hs] at h
        rw [p.put_parse u a h, eq_of_strip c s u hs]
        rfl

theorem pre_put (c : List Bool) (p : PCode A) (a : A)
    (s : List Bool) (h : (p.pre c).put a = some s) : ∃ r, s = c ++ r := by
  cases hp : p.put a with
  | none =>
      have h0 : (p.put a).map (c ++ ·) = some s := h
      rw [hp] at h0
      cases h0
  | some u =>
      have h0 : (p.put a).map (c ++ ·) = some s := h
      rw [hp] at h0
      exact ⟨u, (Option.some.inj h0).symm⟩

/-- A field of n bits (`ha`), then a code that may depend on its value. -/
def cons (a : PCode A) (n : ℕ) (ha : a.Len n) (p : A → PCode B) : PCode (A × B) where
  put := fun x => (a.put x.1).bind fun u => ((p x.1).put x.2).map (u ++ ·)
  parse := fun s => (a.parse (s.take n)).bind fun x => ((p x).parse (s.drop n)).map (x, ·)
  parse_put := fun x s h => by
    obtain ⟨x, y⟩ := x
    cases hu : a.put x with
    | none => simp only [hu] at h; cases h
    | some u =>
        simp only [hu] at h
        cases hv : (p x).put y with
        | none =>
            have h0 : ((p x).put y).map (u ++ ·) = some s := h
            rw [hv] at h0
            cases h0
        | some v =>
            have h0 : ((p x).put y).map (u ++ ·) = some s := h
            rw [hv] at h0
            rw [← Option.some.inj h0]
            show (a.parse ((u ++ v).take n)).bind
                (fun x => ((p x).parse ((u ++ v).drop n)).map (x, ·)) = some (x, y)
            rw [List.take_left' (ha x u hu), List.drop_left' (ha x u hu), a.parse_put x u hu]
            show ((p x).parse v).map (x, ·) = some (x, y)
            rw [(p x).parse_put y v hv]
            rfl
  put_parse := fun s x h => by
    cases hx : a.parse (s.take n) with
    | none => simp only [hx] at h; cases h
    | some x0 =>
        simp only [hx] at h
        cases hy : (p x0).parse (s.drop n) with
        | none =>
            have h0 : ((p x0).parse (s.drop n)).map (x0, ·) = some x := h
            rw [hy] at h0
            cases h0
        | some y0 =>
            have h0 : ((p x0).parse (s.drop n)).map (x0, ·) = some x := h
            rw [hy] at h0
            rw [← Option.some.inj h0]
            show (a.put x0).bind (fun u => ((p x0).put y0).map (u ++ ·)) = some s
            rw [a.put_parse _ x0 hx]
            show ((p x0).put y0).map (s.take n ++ ·) = some s
            rw [(p x0).put_parse _ y0 hy]
            show some (s.take n ++ s.drop n) = some s
            rw [List.take_append_drop]

/-- A field of n bits (`ha`) in front of the last k bits of p's string, which has at least k bits
(`hp`). -/
def ins (p : PCode B) (a : PCode A) (k n : ℕ) (ha : a.Len n)
    (hp : ∀ y s, p.put y = some s → k ≤ s.length) : PCode (B × A) where
  put := fun x =>
    (p.put x.1).bind fun s =>
      (a.put x.2).map fun w => s.take (s.length - k) ++ (w ++ s.drop (s.length - k))
  parse := fun t =>
    if n + k ≤ t.length then
      (p.parse (t.take (t.length - n - k) ++ t.drop (t.length - k))).bind fun y =>
        (a.parse ((t.drop (t.length - n - k)).take n)).map (y, ·)
    else none
  parse_put := fun x t h => by
    obtain ⟨y, x⟩ := x
    cases hs : p.put y with
    | none => simp only [hs] at h; cases h
    | some s =>
        simp only [hs] at h
        cases hw : a.put x with
        | none =>
            have h0 : (a.put x).map
                  (fun w => s.take (s.length - k) ++ (w ++ s.drop (s.length - k))) = some t := h
            rw [hw] at h0
            cases h0
        | some w =>
            have h0 : (a.put x).map
                  (fun w => s.take (s.length - k) ++ (w ++ s.drop (s.length - k))) = some t := h
            rw [hw] at h0
            have hk := hp y s hs
            have hn := ha x w hw
            have e1 : (s.take (s.length - k)).length = s.length - k := by
              rw [List.length_take]; omega
            have e2 : (s.drop (s.length - k)).length = k := by rw [List.length_drop]; omega
            have et : t = s.take (s.length - k) ++ (w ++ s.drop (s.length - k)) :=
              (Option.some.inj h0).symm
            have el : t.length = (s.length - k) + (n + k) := by
              rw [et, List.length_append, List.length_append, e1, e2, hn]
            have f1 : t.length - n - k = s.length - k := by omega
            have f2 : t.length - k = (s.length - k) + n := by omega
            show (if n + k ≤ t.length then _ else none) = some (y, x)
            rw [if_pos (by omega), f1, f2]
            have g1 : t.take (s.length - k) = s.take (s.length - k) := by
              rw [et]; exact List.take_left' e1
            have g2 : t.drop (s.length - k) = w ++ s.drop (s.length - k) := by
              rw [et]; exact List.drop_left' e1
            have g3 : t.drop ((s.length - k) + n) = s.drop (s.length - k) := by
              rw [← List.drop_drop, g2]
              exact List.drop_left' hn
            rw [g1, g2, g3, List.take_append_drop, p.parse_put y s hs, List.take_left' hn]
            show (a.parse w).map (y, ·) = some (y, x)
            rw [a.parse_put x w hw]
            rfl
  put_parse := fun t x h => by
    by_cases ht : n + k ≤ t.length
    · rw [if_pos ht] at h
      cases hy : p.parse (t.take (t.length - n - k) ++ t.drop (t.length - k)) with
      | none => simp only [hy] at h; cases h
      | some y =>
          simp only [hy] at h
          cases hx : a.parse ((t.drop (t.length - n - k)).take n) with
          | none =>
              have h0 : (a.parse ((t.drop (t.length - n - k)).take n)).map (y, ·) = some x := h
              rw [hx] at h0
              cases h0
          | some x0 =>
              have h0 : (a.parse ((t.drop (t.length - n - k)).take n)).map (y, ·) = some x := h
              rw [hx] at h0
              rw [← Option.some.inj h0]
              show (p.put y).bind (fun s =>
                  (a.put x0).map fun w => s.take (s.length - k) ++ (w ++ s.drop (s.length - k))) =
                some t
              rw [p.put_parse _ y hy]
              show (a.put x0).map (fun w =>
                  (t.take (t.length - n - k) ++ t.drop (t.length - k)).take
                      ((t.take (t.length - n - k) ++ t.drop (t.length - k)).length - k) ++
                    (w ++ (t.take (t.length - n - k) ++ t.drop (t.length - k)).drop
                        ((t.take (t.length - n - k) ++ t.drop (t.length - k)).length - k))) = some t
              rw [a.put_parse _ x0 hx]
              have e1 : (t.take (t.length - n - k)).length = t.length - n - k := by
                rw [List.length_take]; omega
              have e2 : (t.drop (t.length - k)).length = k := by rw [List.length_drop]; omega
              have e3 : (t.take (t.length - n - k) ++ t.drop (t.length - k)).length - k =
                  t.length - n - k := by
                rw [List.length_append, e1, e2]; omega
              show some ((t.take (t.length - n - k) ++ t.drop (t.length - k)).take
                      ((t.take (t.length - n - k) ++ t.drop (t.length - k)).length - k) ++
                    ((t.drop (t.length - n - k)).take n ++
                      (t.take (t.length - n - k) ++ t.drop (t.length - k)).drop
                        ((t.take (t.length - n - k) ++ t.drop (t.length - k)).length - k))) = some t
              rw [e3, List.take_left' e1, List.drop_left' e1]
              have e4 : t.drop (t.length - k) = (t.drop (t.length - n - k)).drop n := by
                rw [List.drop_drop]
                congr 1
                omega
              rw [e4, List.take_append_drop, List.take_append_drop]
    · rw [if_neg ht] at h
      cases h

end PCode

/-- A bit string of exactly n bits. -/
def pBits (n : ℕ) : PCode (List Bool) where
  put := fun l => if l.length = n then some l else none
  parse := fun l => if l.length = n then some l else none
  parse_put := fun l s h => by
    by_cases hl : l.length = n
    · rw [if_pos hl] at h
      rw [← Option.some.inj h, if_pos hl]
    · rw [if_neg hl] at h
      cases h
  put_parse := fun s l h => by
    by_cases hl : s.length = n
    · rw [if_pos hl] at h
      rw [← Option.some.inj h, if_pos hl]
    · rw [if_neg hl] at h
      cases h

theorem pBits_len (n : ℕ) : (pBits n).Len n := fun l s h => by
  by_cases hl : l.length = n
  · have h0 : (if l.length = n then some l else none) = some s := h
    rw [if_pos hl] at h0
    rw [← Option.some.inj h0]
    exact hl
  · have h0 : (if l.length = n then some l else none) = some s := h
    rw [if_neg hl] at h0
    cases h0

theorem extract_all (b : ByteArray) (n : ℕ) (h : b.size = n) : b.extract 0 n = b := by
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  have h' : b.data.size = n := h
  rw [← h']
  exact Array.extract_size

/-- A number below 2^64 as the 64 bits of its word. -/
def pWord : PCode ℕ where
  put := fun x => if x < 2 ^ 64 then some (bytesToBits (_root_.Fmt.u64n x)) else none
  parse := fun s => if s.length = 64 then some (_root_.Fmt.wordAt (bitsToBytes s) 0).toNat else none
  parse_put := fun x s h => by
    by_cases hx : x < 2 ^ 64
    · rw [if_pos hx] at h
      rw [← Option.some.inj h, if_pos (by rw [length_bytesToBits]; rfl), bitsToBytes_bytesToBits]
      show some (_root_.Fmt.wordAt (_root_.Fmt.u64 (UInt64.ofNat x)) 0).toNat = some x
      rw [_root_.Fmt.wordAt_u64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hx]
    · rw [if_neg hx] at h
      cases h
  put_parse := fun s x h => by
    by_cases hs : s.length = 64
    · rw [if_pos hs] at h
      rw [← Option.some.inj h, if_pos (UInt64.toNat_lt _)]
      have h8 : (bitsToBytes s).size = 8 := size_bitsToBytes s 8 hs
      show some (bytesToBits
            (_root_.Fmt.u64 (UInt64.ofNat (_root_.Fmt.wordAt (bitsToBytes s) 0).toNat))) = some s
      rw [UInt64.ofNat_toNat, _root_.Fmt.u64_wordAt (bitsToBytes s) 0 (by omega),
        extract_all _ _ h8, bytesToBits_bitsToBytes s ((whole_iff s).2 ⟨8, hs⟩)]
    · rw [if_neg hs] at h
      cases h

theorem pWord_len : pWord.Len 64 := fun x s h => by
  by_cases hx : x < 2 ^ 64
  · have h0 : (if x < 2 ^ 64 then some (bytesToBits (_root_.Fmt.u64n x)) else none) = some s := h
    rw [if_pos hx] at h0
    rw [← Option.some.inj h0, length_bytesToBits]
    rfl
  · have h0 : (if x < 2 ^ 64 then some (bytesToBits (_root_.Fmt.u64n x)) else none) = some s := h
    rw [if_neg hx] at h0
    cases h0

theorem pWord_put (x : ℕ) (hx : x < 2 ^ 64) :
    pWord.put x = some (bytesToBits (_root_.Fmt.u64n x)) := if_pos hx

end Run
