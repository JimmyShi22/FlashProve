-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SimBase.lean: what the written base test computes, in the field.

Fmt/M1Fold.lean holds the last step of the written verifier of the proximity test as three functions
on words: `baseB1` (one equation on the two shown messages), `baseB2At` (two equations at one
position) and `baseOK` (the lengths, the first equation, and the two at every listed position). This
file reads each of them in the field `GE`.

First each function is given as a closed form: it returns true exactly if equations hold whose sides
have only the inputs as they are read in the field, finite sums, products and powers. Then the whole
test is compared with the decision of the library's base case, `Cb.LdwAccept`
(Cb/Ld/LdBaseWords.lean), at these parameters. The code is `baseCode C Z`: one row under the code C
beside one row under the mask code Z, both read at the positions of C. What is encoded is
`baseMs`: the two shown messages and the two shown tails. The linear form is `baseForm`: the two
vectors of coefficients. The two words are any two that show, at the listed positions, what the
opened columns hold; `lastWord` and `maskWord` are two such words, made from the columns.

Why words can be compared in the field. The written functions compare triples of words. Each side of
each comparison is the result of an addition or of an evaluation, so its words are below the base
field's prime p, and on such triples the reading `toE` is injective.

Main definitions: `symV`, `baseCode`, `baseMs`, `baseForm`, `baseVec`, `lastWord`, `maskWord`.
Main theorems: `baseB1_iff`, `baseB2At_iff`, `baseOK_iff_parts`, `baseOK_congr`,
`baseOK_iff_accept`, `baseOK_iff_accept_cols`.

Not claimed. Nothing on a protocol, on soundness or on how the columns were opened. Nothing on the
other field of the format.
-/
import OnBytes.Slice.SimBasic
import Fmt.M1Fold
import Cb.Ld.LdBase

set_option autoImplicit false

namespace OnBytes.Slice
open Fmt.M1 Cb

/-! ## Results have words below p -/

/-- The triple of zeros has words below p. -/
theorem okE_zeroE : Fmt.Fld.two.okE Fmt.Fld.zeroE = true := by decide

/-- A sum of the format has words below p. -/
theorem okE_addE (a b : E) : Fmt.Fld.two.okE (Fmt.Fld.two.addE a b) = true := by
  simp only [Fmt.Fld.okE, Fmt.Fld.addE, Fmt.Fld.ok_add, Bool.and_self]

/-- A symbol of a word of a code has words below p. -/
theorem okE_symE (C : Code) (x : ℕ) (m rho : List E) :
    Fmt.Fld.two.okE (symE C x m rho) = true := by
  unfold symE hornerE
  cases fitL Fmt.Fld.zeroE C.r rho ++ fitL Fmt.Fld.zeroE C.l m with
  | nil => exact okE_zeroE
  | cons c t => exact okE_addE _ _

/-- Two triples with words below p are equal exactly if they are equal in the field. -/
theorem eq_iff_toE (a b : E) (ha : Fmt.Fld.two.okE a = true) (hb : Fmt.Fld.two.okE b = true) :
    a = b ↔ toE a = toE b :=
  ⟨congrArg toE, toE_inj a b ha hb⟩

/-! ## The three functions as closed forms -/

/-- The first equation: the two vectors of coefficients on the two shown messages give the masking
word's target plus lam times the target. n0 and n1 are any numbers that the messages' lengths do not
pass: entries beyond an end count as 0. -/
theorem baseB1_iff (c d : Array E) (tau tauS lam : E) (M0 M1 : List E) (n0 n1 : ℕ)
    (h0 : M0.length ≤ n0) (h1 : M1.length ≤ n1) :
    baseB1 .two c d tau tauS lam M0 M1 = true ↔
      (∑ i ∈ Finset.range n0, vec c i * lst M0 i) +
          ∑ i ∈ Finset.range n1, vec d i * lst M1 i = toE tauS + toE lam * toE tau := by
  have e0 : toE (dot .two c M0.toArray) = ∑ i ∈ Finset.range n0, vec c i * lst M0 i := by
    rw [toE_dot_of_le c M0.toArray n0 (le_trans (min_le_right _ _) (by simpa using h0))]
    exact Finset.sum_congr rfl fun i _ => by rw [vec_toArray M0 i]
  have e1 : toE (dot .two d M1.toArray) = ∑ i ∈ Finset.range n1, vec d i * lst M1 i := by
    rw [toE_dot_of_le d M1.toArray n1 (le_trans (min_le_right _ _) (by simpa using h1))]
    exact Finset.sum_congr rfl fun i _ => by rw [vec_toArray M1 i]
  unfold baseB1
  rw [decide_eq_true_iff, eq_iff_toE _ _ (okE_addE _ _) (okE_addE _ _), toE_addE, toE_addE,
    toE_mulE, e0, e1]

/-- The value, at the point of position x, of the polynomial whose coefficients are the r entries of
the tail and then the l entries of the message. -/
def symV (C : Code) (x : ℕ) (m rho : List E) : GE :=
  (∑ q ∈ Finset.range C.r, algebraMap GF GE (toF (point C.a x) ^ q) * lst rho q) +
    ∑ j ∈ Finset.range C.l, algebraMap GF GE (toF (point C.a x) ^ (C.r + j)) * lst m j

/-- The two equations at one position. Under C at x: the code word of what was shown (M0 with the
tail R0) has the value o.2.1 + lam * o.1, where o.1 is the main symbol of the last message and o.2.1
that of the masking word. Under Z at x modulo the length of Z: the same for M1 with R1 and the two
mask symbols o.2.2.1 and o.2.2.2. -/
theorem baseB2At_iff (C Z : Code) (lam : E) (M0 M1 R0 R1 : List E) (x : ℕ)
    (o : E × E × E × E) :
    baseB2At .two C Z lam M0 M1 R0 R1 x o = true ↔
      symV C x M0 R0 = toE o.2.1 + toE lam * toE o.1 ∧
        symV Z (x % 2 ^ Z.a) M1 R1 = toE o.2.2.2 + toE lam * toE o.2.2.1 := by
  unfold baseB2At
  rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff,
    eq_iff_toE _ _ (okE_symE _ _ _ _) (okE_addE _ _),
    eq_iff_toE _ _ (okE_symE _ _ _ _) (okE_addE _ _), toE_addE, toE_addE, toE_mulE, toE_mulE,
    toE_symE, toE_symE]
  rfl

/-- The whole test: the four shown lists have their codes' lengths, the first equation holds, and
every listed position has a column at which the two equations hold. -/
theorem baseOK_iff_parts (C Z : Code) (c d : Array E) (tau tauS lam : E) (M0 M1 R0 R1 : List E)
    (xs : List ℕ) (col : ℕ → Option (E × E × E × E)) :
    baseOK .two C Z c d tau tauS lam M0 M1 R0 R1 xs col = true ↔
      (M0.length = C.l ∧ M1.length = Z.l ∧ R0.length = C.r ∧ R1.length = Z.r) ∧
        baseB1 .two c d tau tauS lam M0 M1 = true ∧
          ∀ x ∈ xs, ∃ o, col x = some o ∧ baseB2At .two C Z lam M0 M1 R0 R1 x o = true := by
  unfold baseOK
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true, and_assoc]
  refine and_congr_right fun _ => and_congr_right fun _ => forall₂_congr fun x _ => ?_
  cases col x with
  | none => simp
  | some o => simp

/-- The test reads the columns at the listed positions alone. It holds in both fields. -/
theorem baseOK_congr (f : Fmt.Fld) (C Z : Code) (c d : Array E) (tau tauS lam : E)
    (M0 M1 R0 R1 : List E) (xs : List ℕ) (col col' : ℕ → Option (E × E × E × E))
    (h : ∀ x ∈ xs, col x = col' x) :
    baseOK f C Z c d tau tauS lam M0 M1 R0 R1 xs col =
      baseOK f C Z c d tau tauS lam M0 M1 R0 R1 xs col' := by
  unfold baseOK
  congr 1
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact forall₂_congr fun x hx => by rw [h x hx]

/-! ## The parameters of the library's base case -/

/-- The code of the base test: one row under C beside one row under Z, read at the positions of C. A
position of C is read in Z modulo the length of Z. Only its code words as they are read are used
here. The words f and g below are any functions on the positions of C. -/
@[reducible] def baseCode (C Z : Code) : LdCode GE (Fin (2 ^ C.a)) :=
  (ldOf C C.a).pair (ldOf Z C.a)

/-- What the prover shows in full: the two messages and the two tails. -/
def baseMs (C Z : Code) (M0 M1 R0 R1 : List E) : (baseCode C Z).MR :=
  (Sum.elim (fun j => lst M0 j.val) (fun j => lst M1 j.val),
    Sum.elim (fun q => lst R0 q.val) (fun q => lst R1 q.val))

/-- The linear form of the claim: c on the main row's message, d on the mask row's. -/
def baseForm (C Z : Code) (c d : Array E) : (baseCode C Z).MR → GE :=
  fun w =>
    ∑ j, Sum.elim (fun j : Fin C.l => vec c j.val) (fun j : Fin Z.l => vec d j.val) j * w.1 j

/-- The coefficients of the claim as one vector: c on the main row's message, d on the mask
row's. -/
def baseVec (C Z : Code) (c d : Array E) : (baseCode C Z).J → GE :=
  Sum.elim (fun j : Fin C.l => vec c j.val) (fun j : Fin Z.l => vec d j.val)

/-- The form of the library's statement (target, vector of coefficients) is `baseForm`. -/
theorem ldForm_baseVec (C Z : Code) (tg : GE) (c d : Array E) :
    ldForm (Slf.idf (E := GE) (J := (baseCode C Z).J)) (tg, baseVec C Z c d) =
      baseForm C Z c d := rfl

/-- `symV` is the library's encoder. -/
theorem symV_enc (C : Code) (x : Fin (2 ^ C.a)) (m rho : List E) :
    symV C x.val m rho =
      (ldOf C C.a).enc (fun j => lst m j.val) (fun q => lst rho q.val) x () := by
  rw [← toE_symE_enc, toE_symE]
  rfl

/-- The main symbol of the encoding of what is shown. -/
theorem ldCw_base_inl (C Z : Code) (M0 M1 R0 R1 : List E) (x : Fin (2 ^ C.a)) :
    ldCw (baseCode C Z) (baseMs C Z M0 M1 R0 R1) x (Sum.inl ()) = symV C x.val M0 R0 := by
  have hx : posIn C x = x := Fin.ext (Nat.mod_eq_of_lt x.isLt)
  rw [symV_enc]
  show (ldOf C C.a).enc _ _ (posIn C x) () = _
  rw [hx]
  rfl

/-- The mask symbol of the encoding of what is shown. -/
theorem ldCw_base_inr (C Z : Code) (M0 M1 R0 R1 : List E) (x : Fin (2 ^ C.a)) :
    ldCw (baseCode C Z) (baseMs C Z M0 M1 R0 R1) x (Sum.inr ()) =
      symV Z (x.val % 2 ^ Z.a) M1 R1 := by
  rw [show x.val % 2 ^ Z.a = (posIn Z x).val from rfl, symV_enc]
  rfl

/-- The form at what is shown. -/
theorem baseForm_ms (C Z : Code) (c d : Array E) (M0 M1 R0 R1 : List E) :
    baseForm C Z c d (baseMs C Z M0 M1 R0 R1) =
      (∑ i ∈ Finset.range C.l, vec c i * lst M0 i) +
        ∑ i ∈ Finset.range Z.l, vec d i * lst M1 i := by
  unfold baseForm baseMs
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [Fin.sum_univ_eq_sum_range (fun i => vec c i * lst M0 i) C.l,
    Fin.sum_univ_eq_sum_range (fun i => vec d i * lst M1 i) Z.l]

/-! ## The written test is the library's decision -/

/-- The written base test decides as the library's base case. Q lists the positions. f is the
word of which the claim is made and g the masking word, as long words: any two functions that show,
at each listed position, what the column of that position holds. Then `baseOK` returns true exactly
if the four shown lists have their codes' lengths and `LdwAccept` holds. -/
theorem baseOK_iff_accept (C Z : Code) (c d : Array E) (tau tauS lam : E) (M0 M1 R0 R1 : List E)
    {t : ℕ} (Q : Fin t → Fin (2 ^ C.a)) (col : ℕ → Option (E × E × E × E))
    (f g : Fin (2 ^ C.a) → Unit ⊕ Unit → GE)
    (hcol : ∀ i, ∃ o, col (Q i).val = some o ∧
      f (Q i) (Sum.inl ()) = toE o.1 ∧ g (Q i) (Sum.inl ()) = toE o.2.1 ∧
      f (Q i) (Sum.inr ()) = toE o.2.2.1 ∧ g (Q i) (Sum.inr ()) = toE o.2.2.2) :
    baseOK .two C Z c d tau tauS lam M0 M1 R0 R1 ((List.finRange t).map fun i => (Q i).val) col
        = true ↔
      (M0.length = C.l ∧ M1.length = Z.l ∧ R0.length = C.r ∧ R1.length = Z.r) ∧
        LdwAccept (ldCw (baseCode C Z)) (baseForm C Z c d) (toE tau) f g (toE tauS) (toE lam)
          (baseMs C Z M0 M1 R0 R1) Q := by
  rw [baseOK_iff_parts]
  refine and_congr_right fun hl => ?_
  unfold LdwAccept
  refine and_congr ?_ ?_
  · rw [baseB1_iff c d tau tauS lam M0 M1 C.l Z.l (le_of_eq hl.1) (le_of_eq hl.2.1), baseForm_ms]
  · constructor
    · intro h i
      obtain ⟨o, ho, h1, h2, h3, h4⟩ := hcol i
      obtain ⟨o', ho', hb⟩ := h (Q i).val (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩)
      have : o' = o := Option.some.inj (ho'.symm.trans ho)
      subst this
      have hb' := (baseB2At_iff C Z lam M0 M1 R0 R1 (Q i).val o').1 hb
      funext α
      rcases α with ⟨⟩ | ⟨⟩
      · rw [ldCw_base_inl, hb'.1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1, h2]
      · rw [ldCw_base_inr, hb'.2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h3, h4]
    · intro h x hx
      obtain ⟨i, _, rfl⟩ := List.mem_map.1 hx
      obtain ⟨o, ho, h1, h2, h3, h4⟩ := hcol i
      refine ⟨o, ho, (baseB2At_iff C Z lam M0 M1 R0 R1 (Q i).val o).2 ⟨?_, ?_⟩⟩
      · have := congrFun (h i) (Sum.inl ())
        rwa [ldCw_base_inl, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1, h2] at this
      · have := congrFun (h i) (Sum.inr ())
        rwa [ldCw_base_inr, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h3, h4] at this

/-- The word of which the claim is made, as the columns show it: the last message's main symbol and
its mask symbol. It is 0 at a position without a column. -/
def lastWord (a : ℕ) (col : ℕ → Option (E × E × E × E)) : Fin (2 ^ a) → Unit ⊕ Unit → GE :=
  fun x α =>
    match col x.val with
    | some o => Sum.elim (fun _ => toE o.1) (fun _ => toE o.2.2.1) α
    | none => 0

/-- The masking word, as the columns show it: its main symbol and its mask symbol. It is 0 at a
position without a column. -/
def maskWord (a : ℕ) (col : ℕ → Option (E × E × E × E)) : Fin (2 ^ a) → Unit ⊕ Unit → GE :=
  fun x α =>
    match col x.val with
    | some o => Sum.elim (fun _ => toE o.2.1) (fun _ => toE o.2.2.2) α
    | none => 0

/-- The same without a hypothesis. `baseOK` returns true exactly if the four shown lists have
their codes' lengths, every listed position has a column, and `LdwAccept` holds of the two words
that the columns show. -/
theorem baseOK_iff_accept_cols (C Z : Code) (c d : Array E) (tau tauS lam : E)
    (M0 M1 R0 R1 : List E) {t : ℕ} (Q : Fin t → Fin (2 ^ C.a))
    (col : ℕ → Option (E × E × E × E)) :
    baseOK .two C Z c d tau tauS lam M0 M1 R0 R1 ((List.finRange t).map fun i => (Q i).val) col
        = true ↔
      (M0.length = C.l ∧ M1.length = Z.l ∧ R0.length = C.r ∧ R1.length = Z.r) ∧
        (∀ i, (col (Q i).val).isSome = true) ∧
          LdwAccept (ldCw (baseCode C Z)) (baseForm C Z c d) (toE tau) (lastWord C.a col)
            (maskWord C.a col) (toE tauS) (toE lam) (baseMs C Z M0 M1 R0 R1) Q := by
  by_cases hall : ∀ i, (col (Q i).val).isSome = true
  · have hcol : ∀ i, ∃ o, col (Q i).val = some o ∧
        lastWord C.a col (Q i) (Sum.inl ()) = toE o.1 ∧
        maskWord C.a col (Q i) (Sum.inl ()) = toE o.2.1 ∧
        lastWord C.a col (Q i) (Sum.inr ()) = toE o.2.2.1 ∧
        maskWord C.a col (Q i) (Sum.inr ()) = toE o.2.2.2 := by
      intro i
      obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 (hall i)
      refine ⟨o, ho, ?_, ?_, ?_, ?_⟩ <;>
        simp only [lastWord, maskWord, ho, Sum.elim_inl, Sum.elim_inr]
    rw [baseOK_iff_accept C Z c d tau tauS lam M0 M1 R0 R1 Q col _ _ hcol]
    exact ⟨fun h => ⟨h.1, hall, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  · constructor
    · intro h
      refine absurd (fun i => ?_) hall
      obtain ⟨o, ho, _⟩ := ((baseOK_iff_parts C Z c d tau tauS lam M0 M1 R0 R1 _ col).1 h).2.2
        (Q i).val (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩)
      rw [ho]
      rfl
    · intro h
      exact absurd h.2.1 hall

end OnBytes.Slice

#print axioms OnBytes.Slice.baseB1_iff
#print axioms OnBytes.Slice.baseB2At_iff
#print axioms OnBytes.Slice.baseOK_iff_parts
#print axioms OnBytes.Slice.baseOK_congr
#print axioms OnBytes.Slice.baseOK_iff_accept
#print axioms OnBytes.Slice.baseOK_iff_accept_cols
