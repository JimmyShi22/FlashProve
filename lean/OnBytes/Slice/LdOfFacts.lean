-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/LdOfFacts.lean: one row under a code of the format has the laws and the distance that
the library's proximity blocks ask of a code.

The library's blocks take a code as a record `Cb.LdCode`: an encoder from a message and a random
tail to a word, and a way to read a word at the positions of a group. `ldOf C a`
(OnBytes/Slice/LinkAt.lean) is that record for one row under the code C = (C.a, l, r) of the format,
read at 2^a positions: the position x of the group shows the word's symbol at x modulo 2^C.a.
`ldRep C a` is the record for one row under C repeated to 2^a positions: a word has a symbol of its
own at each position of the group, and a code word has at x the symbol of C's word at x modulo
2^C.a.

The conditions are C.a ≤ 32, under which the points of the code are different, and r + l ≤ 2^C.a;
for `ldRep` also C.a ≤ a.

Main theorems.
 `ldOf_enc`    a symbol of the encoder's word is the row of `genOf` at that position, times the list
               of coefficients: the tail's entries, then the message's.
 `ldOf_laws`   for every a: the encoder and the reading are linear, only the message 0 with the
               tail 0 has the word 0, and the reading at x depends only on the symbol that it names.
 `ldOf_dist`   for a = C.a: if the message or the tail is not 0, then the word that is read is not 0
               at 2^C.a - (r + l) + 1 positions or more.
 `ldRep_eq`    for a = C.a the repeated code is `ldOf C a`.
 `ldRep_laws`  the same laws for the repeated code.
 `ldRep_dist`  the repeated code's distance: 2^C.a - (r + l) + 1, the number of `ldOf_dist`, times
               the 2^(a - C.a) copies.

Not claimed. No distance of `ldOf C a` for a other than C.a. Nothing on lists, on agreement, or on
how many positions of a word are hidden. Nothing on protocols.
-/
import OnBytes.Slice.LinkAt
import OnBytes.Slice.CodeFacts
import Cb.Gen.CodeRepProofs

set_option autoImplicit false

namespace OnBytes.Slice
open Cb Prob

/-- A position of the code itself is read at that position. -/
theorem posIn_self (C : Fmt.M1.Code) (x : Fin (2 ^ C.a)) : posIn C x = x :=
  Fin.ext (Nat.mod_eq_of_lt x.isLt)

/-- The encoder is the generator matrix, applied to the tail's entries followed by the
message's. -/
theorem ldOf_enc (C : Fmt.M1.Code) (a : ℕ) (m : Fin C.l → GE) (r : Fin C.r → GE)
    (p : Fin (2 ^ C.a)) (s : Unit) :
    (ldOf C a).enc m r p s = (genOf C).mulVec (Fin.append r m) p := by
  show (∑ q, genOf C p (Fin.castAdd C.l q) * r q) + ∑ j, genOf C p (Fin.natAdd C.r j) * m j
    = ∑ k, genOf C p k * Fin.append r m k
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- If the list of coefficients is 0, so are the message and the tail. -/
theorem append_eq_zero {l r : ℕ} {m : Fin l → GE} {t : Fin r → GE}
    (h : Fin.append t m = 0) : m = 0 ∧ t = 0 := by
  constructor
  · funext j
    have hj := congrFun h (Fin.natAdd r j)
    rwa [Fin.append_right] at hj
  · funext q
    have hq := congrFun h (Fin.castAdd l q)
    rwa [Fin.append_left] at hq

/-- The encoder is linear in (message, tail). -/
theorem ldOf_encLin (C : Fmt.M1.Code) (a : ℕ) :
    IsLinearMap GE fun w : (Fin C.l → GE) × (Fin C.r → GE) => (ldOf C a).enc w.1 w.2 where
  map_add u w := by
    funext p s
    show (∑ q, genOf C p (Fin.castAdd C.l q) * (u.2 q + w.2 q))
        + ∑ j, genOf C p (Fin.natAdd C.r j) * (u.1 j + w.1 j)
      = ((∑ q, genOf C p (Fin.castAdd C.l q) * u.2 q)
          + ∑ j, genOf C p (Fin.natAdd C.r j) * u.1 j)
        + ((∑ q, genOf C p (Fin.castAdd C.l q) * w.2 q)
          + ∑ j, genOf C p (Fin.natAdd C.r j) * w.1 j)
    simp only [mul_add, Finset.sum_add_distrib]
    exact add_add_add_comm _ _ _ _
  map_smul c u := by
    funext p s
    show (∑ q, genOf C p (Fin.castAdd C.l q) * (c * u.2 q))
        + ∑ j, genOf C p (Fin.natAdd C.r j) * (c * u.1 j)
      = c * ((∑ q, genOf C p (Fin.castAdd C.l q) * u.2 q)
          + ∑ j, genOf C p (Fin.natAdd C.r j) * u.1 j)
    simp only [mul_add, Finset.mul_sum, mul_left_comm c]

/-- The laws, at any number 2^a of positions of the group. -/
theorem ldOf_laws (C : Fmt.M1.Code) (a : ℕ) (ha : C.a ≤ 32) (hk : C.r + C.l ≤ 2 ^ C.a) :
    (ldOf C a).Laws where
  encLin := ldOf_encLin C a
  tLin := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  inj m r h := by
    have hinj : Function.Injective (genOf C).mulVec :=
      (hasDist_genOf C ha hk).injective (Nat.succ_pos _)
    have h0 : (genOf C).mulVec (Fin.append r m) = (genOf C).mulVec 0 := by
      funext p
      rw [← ldOf_enc C a m r p (), h, Matrix.mulVec_zero]
      rfl
    exact append_eq_zero (hinj h0)
  loc f g x h := by
    funext s
    show f (posIn C x) () = g (posIn C x) ()
    rw [h (posIn C x) (Finset.mem_singleton_self _)]

/-- The distance, at the code's own positions. -/
theorem ldOf_dist (C : Fmt.M1.Code) (ha : C.a ≤ 32) (hk : C.r + C.l ≤ 2 ^ C.a) :
    (ldOf C C.a).Dist (2 ^ C.a - (C.r + C.l) + 1) := by
  intro m r hmr
  have hv : Fin.append r m ≠ 0 := fun h => hmr (append_eq_zero h)
  refine (hasDist_genOf C ha hk (Fin.append r m) hv).trans (cnt_mono fun x hx h0 => hx ?_)
  have h1 : (ldOf C C.a).enc m r (posIn C x) () = 0 := congrFun h0 ()
  rwa [ldOf_enc, posIn_self] at h1

/-! ## The repeated code -/

/-- A symbol of a repeated code word is the symbol of the code's own word at the position modulo the
code's length. -/
theorem ldRep_enc (C : Fmt.M1.Code) (a : ℕ) (m : Fin C.l → GE) (r : Fin C.r → GE)
    (p : Fin (2 ^ a)) (s : Unit) :
    (ldRep C a).enc m r p s = (ldOf C C.a).enc m r (posIn C p) () := rfl

/-- At a group of the code's own length the repeated code is the code. -/
theorem ldRep_eq (C : Fmt.M1.Code) (a : ℕ) (h : C.a = a) : ldRep C a = ldOf C a := by
  subst h
  simp only [ldRep, ldOf, posIn_self]

/-- A position of the code, as a position of a group that is at least as long. -/
def upIn (C : Fmt.M1.Code) {a : ℕ} (h : C.a ≤ a) (y : Fin (2 ^ C.a)) : Fin (2 ^ a) :=
  ⟨y.val, lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by decide) h)⟩

/-- Modulo the code's length it is the position from which it was made. -/
theorem posIn_upIn (C : Fmt.M1.Code) {a : ℕ} (h : C.a ≤ a) (y : Fin (2 ^ C.a)) :
    posIn C (upIn C h y) = y :=
  Fin.ext (Nat.mod_eq_of_lt y.isLt)

/-- Exactly 2^(a - C.a) positions of the group are equal to a given position of the code modulo the
code's length. -/
theorem cnt_posIn (C : Fmt.M1.Code) {a : ℕ} (h : C.a ≤ a) (y : Fin (2 ^ C.a)) :
    cnt (fun x : Fin (2 ^ a) => posIn C x = y) = 2 ^ (a - C.a) := by
  rw [cnt_congr (fun x : Fin (2 ^ a) => (Fin.ext_iff : posIn C x = y ↔ _)),
    ← Nat.pow_div h (by decide)]
  exact CodeRep.cnt_mod (Nat.pow_dvd_pow 2 h) y

/-- The laws of the repeated code, at a group that is at least as long as the code (C.a ≤ a), if
C.a ≤ 32 and the code has room for C.r + C.l symbols (C.r + C.l ≤ 2^C.a). -/
theorem ldRep_laws (C : Fmt.M1.Code) (a : ℕ) (hle : C.a ≤ a) (ha : C.a ≤ 32)
    (hk : C.r + C.l ≤ 2 ^ C.a) : (ldRep C a).Laws where
  encLin :=
    { map_add := fun u w => by
        funext p s
        exact congrFun (congrFun ((ldOf_encLin C C.a).map_add u w) (posIn C p)) ()
      map_smul := fun c u => by
        funext p s
        exact congrFun (congrFun ((ldOf_encLin C C.a).map_smul c u) (posIn C p)) () }
  tLin := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  inj m r h := by
    refine (ldOf_laws C C.a ha hk).inj m r ?_
    funext y s
    have h1 : (ldRep C a).enc m r (upIn C hle y) () = 0 := congrFun (congrFun h (upIn C hle y)) ()
    rw [ldRep_enc, posIn_upIn] at h1
    exact h1
  loc f g x h := by
    funext s
    show f x () = g x ()
    rw [h x (Finset.mem_singleton_self _)]

/-- The distance of the repeated code: 2^C.a - (C.r + C.l) + 1, times the 2^(a - C.a) copies. The
first number is the one that `ldOf_dist` gives for the code at its own positions. Under the
hypotheses of `ldRep_laws`: C.a ≤ a, C.a ≤ 32, and room for C.r + C.l symbols. -/
theorem ldRep_dist (C : Fmt.M1.Code) (a : ℕ) (hle : C.a ≤ a) (ha : C.a ≤ 32)
    (hk : C.r + C.l ≤ 2 ^ C.a) :
    (ldRep C a).Dist (2 ^ (a - C.a) * (2 ^ C.a - (C.r + C.l) + 1)) := by
  intro m r hmr
  have key : ∀ x : Fin (2 ^ a), (ldOf C C.a).T ((ldOf C C.a).enc m r) (posIn C x) ≠ 0 →
      (ldRep C a).T ((ldRep C a).enc m r) x ≠ 0 := by
    intro x hx h
    refine hx (funext fun s => ?_)
    have h1 : (ldRep C a).enc m r x () = 0 := congrFun h ()
    show (ldOf C C.a).enc m r (posIn C (posIn C x)) () = 0
    rw [posIn_self]
    exact h1
  refine (Nat.mul_le_mul_left _ (ldOf_dist C ha hk m r hmr)).trans (le_trans (le_of_eq ?_)
    (cnt_mono key))
  exact (CodeRep.cnt_comp_even (posIn C) (2 ^ (a - C.a)) (cnt_posIn C hle)
    fun y => (ldOf C C.a).T ((ldOf C C.a).enc m r) y ≠ 0).symm

end OnBytes.Slice

#print axioms OnBytes.Slice.ldRep_laws
#print axioms OnBytes.Slice.ldRep_dist
#print axioms OnBytes.Slice.ldOf_enc
#print axioms OnBytes.Slice.ldOf_laws
#print axioms OnBytes.Slice.ldOf_dist
