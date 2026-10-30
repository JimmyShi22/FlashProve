-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/CodingAtoms.lean: small partial codes: a word, an element of the large field as three words, a
digest, a constant.

Definitions that compute, with their laws. After the format page's section 1 (a word: eight bytes,
the lowest first; an element of E: its three coordinates in order; a digest: its 32 bytes), in an
edition that is not the one that ships. A partial code (`PCode`, Run/CodingPart.lean) writes some
points of a type as bit strings,
injectively, with a parser.

Main names: `pUnit`, `pU64`, `pE3`, `pDig`, `pFinAt`.

Limits: it is not tested here that a word is below the field's prime: every triple of words has a
string (the format's readers refuse a word that is no element; that is a parser's test, and an
encoding may write more than a format's files hold).
This file says nothing on a hash.

Terms: lean/GLOSSARY.md.
-/
import Run.CodingPage162
import Run.CodingPage160

set_option autoImplicit false

namespace Run
open Rom Iop

/-- The one point, as a constant string. -/
def pUnit (c : List Bool) : PCode Unit where
  put := fun _ => some c
  parse := fun s => if s = c then some () else none
  parse_put := fun _ s h => by rw [← Option.some.inj h]; exact if_pos rfl
  put_parse := fun s _ h => by
    by_cases hs : s = c
    · rw [hs]
    · rw [if_neg hs] at h
      cases h

theorem pUnit_len (c : List Bool) : (pUnit c).Len c.length :=
  fun _ s h => by rw [← Option.some.inj h]

def u64To (x : UInt64) : Option ℕ := some x.toNat
def u64Of (n : ℕ) : Option UInt64 := if n < 2 ^ 64 then some (UInt64.ofNat n) else none

theorem u64Of_u64To (x : UInt64) (n : ℕ) (h : u64To x = some n) : u64Of n = some x := by
  unfold u64To at h
  unfold u64Of
  rw [← Option.some.inj h, if_pos (UInt64.toNat_lt x), UInt64.ofNat_toNat]

theorem u64To_u64Of (n : ℕ) (x : UInt64) (h : u64Of n = some x) : u64To x = some n := by
  unfold u64Of at h
  unfold u64To
  by_cases hn : n < 2 ^ 64
  · rw [if_pos hn] at h
    rw [← Option.some.inj h, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hn]
  · rw [if_neg hn] at h
    cases h

/-- A word, as its 64 bits. -/
def pU64 : PCode UInt64 := pWord.pull u64To u64Of u64Of_u64To u64To_u64Of

theorem pU64_len : pU64.Len 64 := PCode.pull_len _ _ _ _ _ 64 pWord_len

theorem pU64_put (x : UInt64) : pU64.put x = some (bytesToBits (_root_.Fmt.u64 x)) := by
  show pWord.put x.toNat = _
  rw [pWord_put _ (UInt64.toNat_lt x)]
  show some (bytesToBits (_root_.Fmt.u64 (UInt64.ofNat x.toNat))) = _
  rw [UInt64.ofNat_toNat]

namespace PCode
variable {A B : Type}

theorem cons_len (a : PCode A) (n : ℕ) (ha : a.Len n) (p : A → PCode B)
    (k : ℕ) (hp : ∀ x, (p x).Len k) :
    (a.cons n ha p).Len (n + k) := fun x s h => by
  obtain ⟨u, v, hu, hv, rfl⟩ := cons_put a n ha p x s h
  rw [List.length_append, ha _ u hu, hp _ _ v hv]

theorem pre_len (c : List Bool) (p : PCode A) (k : ℕ) (hp : p.Len k) :
    (p.pre c).Len (c.length + k) := fun a s h => by
  obtain ⟨u, hu, rfl⟩ := pre_put' c p a s h
  rw [List.length_append, hp a u hu]

end PCode

/-- Three words. -/
def pE3 : PCode (UInt64 × UInt64 × UInt64) :=
  pU64.cons 64 pU64_len fun _ => pU64.cons 64 pU64_len fun _ => pU64

theorem pE3_len : pE3.Len 192 :=
  PCode.cons_len _ _ _ _ 128 fun _ => PCode.cons_len _ _ _ _ 64 fun _ => pU64_len

def digTo (d : Dig 256) : Option (List Bool) := some (List.ofFn d)
def digBack (l : List Bool) : Option (Dig 256) := if l.length = 256 then some (digOf l) else none

theorem digBack_digTo (d : Dig 256) (l : List Bool) (h : digTo d = some l) :
    digBack l = some d := by
  unfold digTo at h
  unfold digBack
  rw [← Option.some.inj h, if_pos (List.length_ofFn), digOf_ofFn]

theorem digTo_digBack (l : List Bool) (d : Dig 256) (h : digBack l = some d) :
    digTo d = some l := by
  unfold digBack at h
  unfold digTo
  by_cases hl : l.length = 256
  · rw [if_pos hl] at h
    rw [← Option.some.inj h, ofFn_digOf l hl]
  · rw [if_neg hl] at h
    cases h

/-- A digest of 256 bits, as these bits. -/
def pDig : PCode (Dig 256) := (pBits 256).pull digTo digBack digBack_digTo digTo_digBack

theorem pDig_len : pDig.Len 256 := PCode.pull_len _ _ _ _ _ 256 (pBits_len 256)

def finTo (lo n : ℕ) (x : Fin n) : Option ℕ := some (lo + x.val)
def finOf (lo n : ℕ) (v : ℕ) : Option (Fin n) :=
  if h : lo ≤ v ∧ v - lo < n then some ⟨v - lo, h.2⟩ else none

theorem finOf_finTo (lo n : ℕ) (x : Fin n) (v : ℕ) (h : finTo lo n x = some v) :
    finOf lo n v = some x := by
  unfold finTo at h
  unfold finOf
  rw [← Option.some.inj h, dif_pos ⟨by omega, by have := x.isLt; omega⟩]
  exact congrArg some (Fin.ext (by show lo + x.val - lo = x.val; omega))

theorem finTo_finOf (lo n : ℕ) (v : ℕ) (x : Fin n) (h : finOf lo n v = some x) :
    finTo lo n x = some v := by
  unfold finOf at h
  unfold finTo
  by_cases hv : lo ≤ v ∧ v - lo < n
  · rw [dif_pos hv] at h
    rw [← Option.some.inj h]
    exact congrArg some (by show lo + (v - lo) = v; omega)
  · rw [dif_neg hv] at h
    cases h

/-- A number below n, as the word lo + it. -/
def pFinAt (lo n : ℕ) : PCode (Fin n) :=
  pWord.pull (finTo lo n) (finOf lo n) (finOf_finTo lo n) (finTo_finOf lo n)

theorem pFinAt_len (lo n : ℕ) : (pFinAt lo n).Len 64 := PCode.pull_len _ _ _ _ _ 64 pWord_len

end Run
