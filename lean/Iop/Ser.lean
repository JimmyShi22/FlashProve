-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/Ser.lean: explicit, self-delimiting serialization to bit strings.

Generic combinators; the file imports only Mathlib. The compiled scheme queries typed oracles
(lean/GLOSSARY.md). Where one hash function on bit strings implements them (Rom/Family.lean), a
typed query has to be encoded as a string (Compile/Batch/Ser.lean). This file gives the tools to
define the encoding as an explicit term: no serializer is obtained from a statement of existence.
(Lean's list of axioms does not show this: for seven of this file's definitions (`list`, `nat`,
`fin`, `natEquivBits`, `natG`, `lenList`, `ofFinEnum`) Lean's list of axioms has `Classical.choice`
because of the proofs of the two laws that a serializer carries (for the bijection `natEquivBits`:
of its own two laws). It is seen by reading the bodies of the definitions that the scheme uses.)
  Part 1: `Ser α`, an encoder `put` and a parser `get` for the type α, with the two round-trip laws.
      The parser returns the rest of the string, so serializers compose. Numbers in fixed width and
      in binary (`natG`), finite types, lists with a length prefix (`lenList`).
  Part 2: whole strings: `parse`, and the two laws `parse_put`, `put_of_parse`.
  Part 3: the lengths of the encodings.
-/
import Mathlib.Data.FinEnum
import Mathlib.Data.Nat.Log
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Iop

/-! ## Part 1. Serializers -/

/-- A serializer of the type α: `put` encodes an element as a string of bits; `get` parses an
element off the beginning of a string and returns it with the rest of the string, or fails. The two
laws: an encoding is parsed back, whatever follows it; and whatever is parsed was encoded in exactly
this way (so no element has two encodings, and it is decidable whether a string begins with an
encoding). -/
structure Ser (α : Type) where
  put : α → List Bool
  get : List Bool → Option (α × List Bool)
  get_put : ∀ (a : α) (rest : List Bool), get (put a ++ rest) = some (a, rest)
  put_get : ∀ (s : List Bool) (a : α) (rest : List Bool), get s = some (a, rest) → s = put a ++ rest

namespace Ser

variable {α β : Type}

/-- The one element of Unit has the empty encoding. -/
def unit : Ser Unit where
  put _ := []
  get s := some ((), s)
  get_put _ _ := rfl
  put_get s _ rest h := by cases h; rfl

/-- the empty type -/
def empty : Ser Empty where
  put e := e.elim
  get _ := none
  get_put e _ := e.elim
  put_get _ e _ _ := e.elim

/-- one bit -/
def bool : Ser Bool where
  put b := [b]
  get s := match s with
    | [] => none
    | b :: r => some (b, r)
  get_put _ _ := rfl
  put_get s b rest h := by
    cases s with
    | nil => cases h
    | cons c r => cases h; rfl

/-- The first component, then the second. -/
def prod (A : Ser α) (B : Ser β) : Ser (α × β) where
  put x := A.put x.1 ++ B.put x.2
  get s := (A.get s).bind fun x => (B.get x.2).map fun y => ((x.1, y.1), y.2)
  get_put x rest := by
    rw [List.append_assoc, A.get_put, Option.bind_some, B.get_put, Option.map_some]
  put_get s x rest h := by
    obtain ⟨⟨a, r⟩, ha, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨⟨b, r'⟩, hb, h⟩ := Option.map_eq_some_iff.1 h
    cases h
    rw [A.put_get s a r ha, B.put_get r b r' hb, List.append_assoc]

/-- One bit that says which summand, then the element. -/
def sum (A : Ser α) (B : Ser β) : Ser (α ⊕ β) where
  put x := match x with
    | .inl a => false :: A.put a
    | .inr b => true :: B.put b
  get s := match s with
    | [] => none
    | false :: r => (A.get r).map fun x => (.inl x.1, x.2)
    | true :: r => (B.get r).map fun x => (.inr x.1, x.2)
  get_put x rest := by
    cases x with
    | inl a => show (A.get (A.put a ++ rest)).map _ = _; rw [A.get_put]; rfl
    | inr b => show (B.get (B.put b ++ rest)).map _ = _; rw [B.get_put]; rfl
  put_get s x rest h := by
    match s, h with
    | false :: r, h =>
      obtain ⟨⟨a, r'⟩, ha, h⟩ := Option.map_eq_some_iff.1 h
      cases h
      rw [A.put_get r a r' ha]; rfl
    | true :: r, h =>
      obtain ⟨⟨b, r'⟩, hb, h⟩ := Option.map_eq_some_iff.1 h
      cases h
      rw [B.put_get r b r' hb]; rfl

/-- one bit that says whether there is an element, then the element -/
def option (A : Ser α) : Ser (Option α) where
  put x := match x with
    | none => [false]
    | some a => true :: A.put a
  get s := match s with
    | [] => none
    | false :: r => some (none, r)
    | true :: r => (A.get r).map fun x => (some x.1, x.2)
  get_put x rest := by
    cases x with
    | none => rfl
    | some a => show (A.get (A.put a ++ rest)).map _ = _; rw [A.get_put]; rfl
  put_get s x rest h := by
    match s, h with
    | false :: r, h => cases h; rfl
    | true :: r, h =>
      obtain ⟨⟨a, r'⟩, ha, h⟩ := Option.map_eq_some_iff.1 h
      cases h
      rw [A.put_get r a r' ha]; rfl

/-- a dependent pair: first the index, then the element of its type -/
def sigma {ι : Type} {γ : ι → Type} (A : Ser ι) (B : ∀ i, Ser (γ i)) : Ser (Σ i, γ i) where
  put x := A.put x.1 ++ (B x.1).put x.2
  get s := (A.get s).bind fun x => ((B x.1).get x.2).map fun y => (⟨x.1, y.1⟩, y.2)
  get_put x rest := by
    rw [List.append_assoc, A.get_put, Option.bind_some, (B x.1).get_put, Option.map_some]
  put_get s x rest h := by
    obtain ⟨⟨i, r⟩, hi, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨⟨b, r'⟩, hb, h⟩ := Option.map_eq_some_iff.1 h
    cases h
    rw [A.put_get s i r hi, (B i).put_get r b r' hb, List.append_assoc]

/-- along a bijection -/
def ofEquiv (e : α ≃ β) (B : Ser β) : Ser α where
  put a := B.put (e a)
  get s := (B.get s).map fun x => (e.symm x.1, x.2)
  get_put a rest := by rw [B.get_put, Option.map_some, e.symm_apply_apply]
  put_get s a rest h := by
    obtain ⟨⟨b, r⟩, hb, h⟩ := Option.map_eq_some_iff.1 h
    cases h
    rw [e.apply_symm_apply, B.put_get s b r hb]

/-- A fixed bit before the encoding. -/
def lead (b : Bool) (A : Ser α) : Ser α where
  put a := b :: A.put a
  get s := match s with
    | [] => none
    | c :: r => if c = b then A.get r else none
  get_put a rest := by
    show (if b = b then A.get (A.put a ++ rest) else none) = _
    rw [if_pos rfl, A.get_put]
  put_get s a rest h := by
    match s, h with
    | c :: r, h =>
      have h' : (if c = b then A.get r else none) = some (a, rest) := h
      by_cases hc : c = b
      · rw [if_pos hc] at h'
        rw [hc, A.put_get r a rest h']; rfl
      · rw [if_neg hc] at h'
        cases h'

/-- A fixed string before the encoding (for instance a tag for the parameter set). -/
def tagged : List Bool → Ser α → Ser α
  | [], A => A
  | b :: pre, A => lead b (tagged pre A)

theorem put_tagged (A : Ser α) : ∀ (pre : List Bool) (a : α), (tagged pre A).put a = pre ++ A.put a
  | [], _ => rfl
  | b :: pre, a => congrArg (b :: ·) (put_tagged A pre a)

/-- The encoding of a list: before each element the bit 1, at the end the bit 0. -/
def putList (A : Ser α) : List α → List Bool
  | [] => [false]
  | a :: l => true :: (A.put a ++ putList A l)

/-- The parser of lists, with fuel: it parses at most n elements. -/
def getList (A : Ser α) : ℕ → List Bool → Option (List α × List Bool)
  | _, [] => none
  | _, false :: r => some ([], r)
  | 0, true :: _ => none
  | n + 1, true :: r => (A.get r).bind fun x => (getList A n x.2).map fun y => (x.1 :: y.1, y.2)

theorem getList_putList (A : Ser α) : ∀ (l : List α) (n : ℕ) (rest : List Bool), l.length ≤ n →
    getList A n (putList A l ++ rest) = some (l, rest)
  | [], 0, _, _ => rfl
  | [], _ + 1, _, _ => rfl
  | a :: l, 0, _, h => by simp at h
  | a :: l, n + 1, rest, h => by
      show (A.get ((A.put a ++ putList A l) ++ rest)).bind _ = _
      rw [List.append_assoc, A.get_put, Option.bind_some,
        getList_putList A l n rest (by simpa using h), Option.map_some]

theorem putList_of_getList (A : Ser α) : ∀ (n : ℕ) (s : List Bool) (l : List α) (rest : List Bool),
    getList A n s = some (l, rest) → s = putList A l ++ rest
  | 0, [], _, _, h => by cases h
  | _ + 1, [], _, _, h => by cases h
  | 0, false :: r, l, rest, h => by cases h; rfl
  | _ + 1, false :: r, l, rest, h => by cases h; rfl
  | 0, true :: _, _, _, h => by cases h
  | n + 1, true :: r, l, rest, h => by
      obtain ⟨⟨a, r1⟩, ha, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨⟨l', r2⟩, hl, h⟩ := Option.map_eq_some_iff.1 h
      cases h
      rw [A.put_get r a r1 ha, putList_of_getList A n r1 l' r2 hl]
      simp [putList]

theorem length_le_length_putList (A : Ser α) : ∀ l : List α, l.length ≤ (putList A l).length
  | [] => Nat.zero_le _
  | a :: l => by
      have := length_le_length_putList A l
      simp only [putList, List.length_cons, List.length_append]
      omega

/-- a list, element by element -/
def list (A : Ser α) : Ser (List α) where
  put := putList A
  get s := getList A s.length s
  get_put l rest := getList_putList A l _ rest (by
    have := length_le_length_putList A l
    rw [List.length_append]; omega)
  put_get s l rest h := putList_of_getList A _ s l rest h

/-- a natural number n in unary: n times the bit 1, then the bit 0. (Used in Compile/ for the number
of a round and the k of a ghost name `fbw t k`, Compile/Batch/Oracles.lean.) -/
def nat : Ser ℕ :=
  ofEquiv ⟨fun n => List.replicate n (), List.length, fun n => by simp, fun l => by
    refine List.ext_getElem (by simp) fun _ _ _ => rfl⟩ (list unit)

/-! ### Numbers in fixed width -/

/-- the w lowest binary digits of v, the most significant first -/
def toBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | w + 1, v => toBits w (v / 2) ++ [decide (v % 2 = 1)]

/-- the number with the given binary digits, the most significant first -/
def fromBits (l : List Bool) : ℕ := l.foldl (fun a b => 2 * a + cond b 1 0) 0

theorem length_toBits : ∀ (w v : ℕ), (toBits w v).length = w
  | 0, _ => rfl
  | w + 1, v => by simp [toBits, length_toBits w]

theorem fromBits_concat (l : List Bool) (b : Bool) :
    fromBits (l ++ [b]) = 2 * fromBits l + cond b 1 0 := by
  simp [fromBits, List.foldl_append]

theorem fromBits_toBits : ∀ (w v : ℕ), v < 2 ^ w → fromBits (toBits w v) = v
  | 0, v, h => by
      have : v = 0 := by simpa using h
      subst this; rfl
  | w + 1, v, h => by
      have h2 : v / 2 < 2 ^ w := Nat.div_lt_of_lt_mul (by rw [pow_succ, Nat.mul_comm] at h; exact h)
      rw [toBits, fromBits_concat, fromBits_toBits w _ h2]
      by_cases hb : v % 2 = 1
      · simp only [hb, decide_true, cond_true]; omega
      · simp only [hb, decide_false, cond_false]; omega

theorem toBits_fromBits (l : List Bool) : toBits l.length (fromBits l) = l := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l b ih =>
    rw [List.length_append, List.length_singleton, toBits, fromBits_concat]
    have h1 : (2 * fromBits l + cond b 1 0) / 2 = fromBits l := by
      cases b
      · simp
      · simp only [cond_true]; omega
    have h2 : decide ((2 * fromBits l + cond b 1 0) % 2 = 1) = b := by
      cases b
      · simp
      · simp only [cond_true, decide_eq_true_eq]; omega
    rw [h1, h2, ih]

/-- A number below n, in ⌈log₂ n⌉ binary digits, the most significant first; values of n or more are
not encodings. -/
def fin (n : ℕ) : Ser (Fin n) where
  put i := toBits (Nat.clog 2 n) i.val
  get s :=
    if Nat.clog 2 n ≤ s.length then
      if h : fromBits (s.take (Nat.clog 2 n)) < n then
        some (⟨fromBits (s.take (Nat.clog 2 n)), h⟩, s.drop (Nat.clog 2 n))
      else none
    else none
  get_put i rest := by
    have hl := length_toBits (Nat.clog 2 n) i.val
    have hlt : i.val < 2 ^ Nat.clog 2 n := lt_of_lt_of_le i.isLt (Nat.le_pow_clog (by decide) n)
    have ht : (toBits (Nat.clog 2 n) i.val ++ rest).take (Nat.clog 2 n) =
        toBits (Nat.clog 2 n) i.val := by
      rw [List.take_append_of_le_length (by rw [hl]), List.take_of_length_le (by rw [hl])]
    have hd : (toBits (Nat.clog 2 n) i.val ++ rest).drop (Nat.clog 2 n) = rest := List.drop_left' hl
    rw [if_pos (by rw [List.length_append, hl]; omega)]
    simp only [ht, hd, fromBits_toBits _ _ hlt, i.isLt, dif_pos]
  put_get s i rest h := by
    by_cases h1 : Nat.clog 2 n ≤ s.length
    · rw [if_pos h1] at h
      by_cases h2 : fromBits (s.take (Nat.clog 2 n)) < n
      · rw [dif_pos h2] at h
        cases h
        have hl : (s.take (Nat.clog 2 n)).length = Nat.clog 2 n := by rw [List.length_take]; omega
        have := toBits_fromBits (s.take (Nat.clog 2 n))
        rw [hl] at this
        show s = toBits (Nat.clog 2 n) (fromBits (s.take (Nat.clog 2 n))) ++ _
        rw [this, List.take_append_drop]
      · rw [dif_neg h2] at h; cases h
    · rw [if_neg h1] at h; cases h

/-! ### Natural numbers in binary, and lists with a length prefix -/

theorem fromBits_cons (b : Bool) (l : List Bool) :
    fromBits (b :: l) = cond b 1 0 * 2 ^ l.length + fromBits l := by
  induction l using List.reverseRecOn with
  | nil => cases b <;> rfl
  | append_singleton l c ih =>
    rw [← List.cons_append, fromBits_concat, fromBits_concat, ih, List.length_append,
      List.length_singleton, pow_succ]
    ring

theorem fromBits_lt (l : List Bool) : fromBits l < 2 ^ l.length := by
  induction l using List.reverseRecOn with
  | nil => exact Nat.one_pos
  | append_singleton l c ih =>
    rw [fromBits_concat, List.length_append, List.length_singleton, pow_succ]
    cases c <;> simp only [cond_true, cond_false] <;> omega

/-- Numbers and strings: n corresponds to the binary digits of n + 1 without the leading 1. -/
def natEquivBits : ℕ ≃ List Bool where
  toFun n := toBits (Nat.log 2 (n + 1)) (n + 1 - 2 ^ Nat.log 2 (n + 1))
  invFun l := 2 ^ l.length + fromBits l - 1
  left_inv n := by
    have h1 : 2 ^ Nat.log 2 (n + 1) ≤ n + 1 := Nat.pow_log_le_self 2 (Nat.succ_ne_zero n)
    have h2 : n + 1 < 2 ^ (Nat.log 2 (n + 1) + 1) := Nat.lt_pow_succ_log_self (by decide) (n + 1)
    rw [pow_succ] at h2
    show 2 ^ (toBits _ _).length + fromBits (toBits _ _) - 1 = n
    rw [length_toBits, fromBits_toBits _ _ (by omega)]
    omega
  right_inv l := by
    have h1 := fromBits_lt l
    have h0 : 0 < 2 ^ l.length := Nat.two_pow_pos _
    have e : 2 ^ l.length + fromBits l - 1 + 1 = 2 ^ l.length + fromBits l := by omega
    have hlog : Nat.log 2 (2 ^ l.length + fromBits l) = l.length :=
      (Nat.log_eq_iff (Or.inr ⟨by decide, by omega⟩)).2 ⟨by omega, by rw [pow_succ]; omega⟩
    show toBits (Nat.log 2 (2 ^ l.length + fromBits l - 1 + 1))
        (2 ^ l.length + fromBits l - 1 + 1 - 2 ^ Nat.log 2 _) = l
    rw [e, hlog, Nat.add_sub_cancel_left, toBits_fromBits]

/-- a natural number in binary, self-delimiting (Elias' gamma code, interleaved): 2 ⌊log₂ (n + 1)⌋ +
1 bits -/
def natG : Ser ℕ := ofEquiv natEquivBits (list bool)

/-- the elements of a list, one after the other -/
def putAll (A : Ser α) : List α → List Bool
  | [] => []
  | a :: l => A.put a ++ putAll A l

/-- read exactly n elements -/
def getN (A : Ser α) : ℕ → List Bool → Option (List α × List Bool)
  | 0, s => some ([], s)
  | n + 1, s => (A.get s).bind fun x => (getN A n x.2).map fun y => (x.1 :: y.1, y.2)

theorem getN_putAll (A : Ser α) :
    ∀ (l : List α) (rest : List Bool), getN A l.length (putAll A l ++ rest) = some (l, rest)
  | [], _ => rfl
  | a :: l, rest => by
      show (A.get ((A.put a ++ putAll A l) ++ rest)).bind _ = _
      rw [List.append_assoc, A.get_put, Option.bind_some, getN_putAll A l rest, Option.map_some]

theorem putAll_of_getN (A : Ser α) : ∀ (n : ℕ) (s : List Bool) (l : List α) (rest : List Bool),
    getN A n s = some (l, rest) → s = putAll A l ++ rest ∧ l.length = n
  | 0, s, l, rest, h => by cases h; exact ⟨rfl, rfl⟩
  | n + 1, s, l, rest, h => by
      obtain ⟨⟨a, r1⟩, ha, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨⟨l', r2⟩, hl, h⟩ := Option.map_eq_some_iff.1 h
      cases h
      obtain ⟨e1, e2⟩ := putAll_of_getN A n r1 l' r2 hl
      exact ⟨by rw [A.put_get s a r1 ha, e1, putAll, List.append_assoc],
        by rw [List.length_cons, e2]⟩

/-- a list with a length prefix: the number of its elements (natG), then the elements one after the
other -/
def lenList (A : Ser α) : Ser (List α) where
  put l := natG.put l.length ++ putAll A l
  get s := (natG.get s).bind fun x => getN A x.1 x.2
  get_put l rest := by
    rw [List.append_assoc, natG.get_put, Option.bind_some, getN_putAll]
  put_get s l rest h := by
    obtain ⟨⟨n, r⟩, hn, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e1, e2⟩ := putAll_of_getN A n r l rest h
    rw [natG.put_get s n r hn, e1, e2, List.append_assoc]

/-- an element of a finite type with a numbering: its number, in fixed width -/
def ofFinEnum (α : Type) [FinEnum α] : Ser α := ofEquiv FinEnum.equiv (fin (FinEnum.card α))

/-- n raw bits -/
def bits (n : ℕ) : Ser (Fin n → Bool) where
  put v := List.ofFn v
  get s :=
    if h : n ≤ s.length then some (fun i => s[i.val]'(lt_of_lt_of_le i.isLt h), s.drop n) else none
  get_put v rest := by
    have hl : (List.ofFn v).length = n := List.length_ofFn
    rw [dif_pos (by rw [List.length_append, hl]; omega)]
    congr 2
    · funext i
      rw [List.getElem_append_left (by rw [hl]; exact i.isLt), List.getElem_ofFn]
    · exact List.drop_left' hl
  put_get s v rest h := by
    by_cases h1 : n ≤ s.length
    · rw [dif_pos h1] at h
      cases h
      conv_lhs => rw [← List.take_append_drop n s]
      congr 1
      refine List.ext_getElem (by simp [h1]) fun j hj1 hj2 => ?_
      rw [List.getElem_take, List.getElem_ofFn]
    · rw [dif_neg h1] at h; cases h

/-! ## Part 2. Whole strings -/

/-- Parse a whole string: an element, and nothing after it. -/
def parse (A : Ser α) (s : List Bool) : Option α :=
  match A.get s with
  | some (a, []) => some a
  | _ => none

theorem parse_put (A : Ser α) (a : α) : A.parse (A.put a) = some a := by
  have h := A.get_put a []
  rw [List.append_nil] at h
  simp only [parse, h]

theorem put_of_parse (A : Ser α) {s : List Bool} {a : α} (h : A.parse s = some a) :
    A.put a = s := by
  unfold parse at h
  split at h
  · rename_i a' heq
    cases h
    rw [A.put_get s _ [] heq, List.append_nil]
  · cases h

theorem put_injective (A : Ser α) : Function.Injective A.put := fun a b h => by
  have := A.parse_put a
  rw [h, A.parse_put] at this
  exact (Option.some.inj this).symm

/-! ## Part 3. Lengths -/

theorem length_put_prod (A : Ser α) (B : Ser β) (x : α × β) :
    ((prod A B).put x).length = (A.put x.1).length + (B.put x.2).length :=
  List.length_append

theorem length_put_sigma {ι : Type} {γ : ι → Type} (A : Ser ι) (B : ∀ i, Ser (γ i)) (x : Σ i, γ i) :
    ((sigma A B).put x).length = (A.put x.1).length + ((B x.1).put x.2).length := List.length_append

theorem length_put_ofEquiv (e : α ≃ β) (B : Ser β) (a : α) :
    ((ofEquiv e B).put a).length = (B.put (e a)).length := rfl

theorem length_put_none (A : Ser α) : ((option A).put none).length = 1 := rfl

theorem length_put_some (A : Ser α) (a : α) :
    ((option A).put (some a)).length = (A.put a).length + 1 := rfl

theorem length_put_inl (A : Ser α) (B : Ser β) (a : α) :
    ((sum A B).put (.inl a)).length = (A.put a).length + 1 := rfl

theorem length_put_inr (A : Ser α) (B : Ser β) (b : β) :
    ((sum A B).put (.inr b)).length = (B.put b).length + 1 := rfl

theorem length_put_fin (n : ℕ) (i : Fin n) : ((fin n).put i).length = Nat.clog 2 n :=
  length_toBits _ _

theorem length_put_ofFinEnum (α : Type) [FinEnum α] (a : α) :
    ((ofFinEnum α).put a).length = Nat.clog 2 (FinEnum.card α) :=
  length_toBits _ _

theorem length_put_bits (n : ℕ) (v : Fin n → Bool) : ((bits n).put v).length = n := List.length_ofFn

theorem length_put_bool (b : Bool) : (bool.put b).length = 1 := rfl

theorem length_put_tagged (A : Ser α) (pre : List Bool) (a : α) :
    ((tagged pre A).put a).length = pre.length + (A.put a).length := by
  rw [put_tagged, List.length_append]

theorem length_putList_bool : ∀ l : List Bool, (putList bool l).length = 2 * l.length + 1
  | [] => rfl
  | b :: l => by
      show ((b :: putList bool l).length + 1) = _
      rw [List.length_cons, length_putList_bool l, List.length_cons]
      omega

/-- The length of the self-delimiting binary encoding of n. -/
theorem length_put_natG (n : ℕ) : (natG.put n).length = 2 * Nat.log 2 (n + 1) + 1 := by
  show (putList bool (toBits _ _)).length = _
  rw [length_putList_bool, length_toBits]

theorem length_put_natG_le {n b : ℕ} (h : n + 1 < 2 ^ (b + 1)) :
    (natG.put n).length ≤ 2 * b + 1 := by
  rw [length_put_natG]
  have : Nat.log 2 (n + 1) < b + 1 := Nat.log_lt_of_lt_pow (Nat.succ_ne_zero n) h
  omega

/-- If every element is encoded in at most w bits: at most `l.length * w` bits. -/
theorem length_putAll_le (A : Ser α) (w : ℕ) :
    ∀ l : List α, (∀ a ∈ l, (A.put a).length ≤ w) → (putAll A l).length ≤ l.length * w
  | [], _ => Nat.zero_le _
  | a :: l, h => by
      have h1 := h a List.mem_cons_self
      have h2 := length_putAll_le A w l fun b hb => h b (List.mem_cons_of_mem _ hb)
      rw [putAll, List.length_append, List.length_cons, Nat.succ_mul]
      omega

theorem length_put_lenList (A : Ser α) (l : List α) :
    ((lenList A).put l).length = (natG.put l.length).length + (putAll A l).length :=
  List.length_append

/-- a list of at most n elements, each encoded in at most w bits, where n + 1 < 2^(b+1) -/
theorem length_put_lenList_le (A : Ser α) {l : List α} {n w b : ℕ} (hl : l.length ≤ n)
    (hn : n + 1 < 2 ^ (b + 1)) (hw : ∀ a ∈ l, (A.put a).length ≤ w) :
    ((lenList A).put l).length ≤ 2 * b + 1 + n * w := by
  rw [length_put_lenList]
  exact Nat.add_le_add (length_put_natG_le (lt_of_le_of_lt (by omega) hn))
    (le_trans (length_putAll_le A w l hw) (Nat.mul_le_mul_right w hl))

/-- The number of bits of the self-delimiting binary encoding of n. -/
def gam (n : ℕ) : ℕ := 2 * Nat.log 2 (n + 1) + 1

theorem gam_eq {n b : ℕ} (h1 : 2 ^ b ≤ n + 1) (h2 : n + 1 < 2 ^ (b + 1)) : gam n = 2 * b + 1 := by
  unfold gam
  rw [(Nat.log_eq_iff (Or.inr ⟨by decide, Nat.succ_ne_zero n⟩)).2 ⟨h1, h2⟩]

theorem length_put_natG_eq_gam (n : ℕ) : (natG.put n).length = gam n := length_put_natG n

theorem gam_mono {m n : ℕ} (h : m ≤ n) : gam m ≤ gam n := by
  have h1 : Nat.log 2 (m + 1) ≤ Nat.log 2 (n + 1) := Nat.log_mono_right (Nat.add_le_add_right h 1)
  unfold gam
  omega

/-- a list of at most n elements, each encoded in at most w bits -/
theorem length_put_lenList_le_gam
    (A : Ser α) {l : List α} {n w : ℕ} (hl : l.length ≤ n) (hw : ∀ a ∈ l, (A.put a).length ≤ w) :
    ((lenList A).put l).length ≤ gam n + n * w := by
  rw [length_put_lenList, length_put_natG_eq_gam]
  exact Nat.add_le_add (gam_mono hl)
    (le_trans (length_putAll_le A w l hw) (Nat.mul_le_mul_right w hl))

end Ser

end Iop
