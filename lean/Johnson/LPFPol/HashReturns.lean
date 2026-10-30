-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFPol/HashReturns.lean: the digest of the three configuration files that the planner forms
and drops (`hPar`, OnBytes/Model/Config.lean) returns at a second parameter file if it returns at a
first one, with the same scale file and layout file, and the second file has fewer than 2^32 bytes.

Why. `publicOf` (OnBytes/Model/VerifyPublic.lean) calls `hPar` on the bytes of the parameter file
and drops the value. So a law that carries a return of `publicOf` from one parameter file to another
owes only that `hPar` returns at the other file. The two files may differ in length.

Main names.
* `bind_ok`: a step that returns a can be replaced by a in what follows it.
* `isSome_levels`: k + 1 levels of the tree hash return on a string of 1 to 512 * 16^k bytes.
* `isSome_olderTK_of`: the tree hash `secondHashFunctionTree` (OnBytes/Hash/SecondHashFunction.lean) returns on every string of
  whole words, of at least 32 and fewer than 2^40 bytes.
* `textTH_returns`: `textTH` returns on every text of fewer than 2^32 bytes, and its digest has 32
  bytes. `textTH_size`: what `textTH` returns has a digest of 32 bytes.
* `layTH`, `parDigests_parts`, `parDigests_of`: `parDigests` returns exactly if its three digests
  are made and the test `klHeld` on the scale file's length passes, and its record is made of them.
* `hPar_returns`: the law of the first paragraph.

Premises. Of `hPar_returns`: h, `hPar` returns at pol, KL, layout; hl, pol' has fewer than 2^32
bytes.

Limits. Nothing is said on the value that `hPar` returns, at either file: only that there is one.
Nothing is said on the hash but the length of its values (32 bytes: `size_olderK`,
OnBytes/K/ServedFreeItem.lean). That `hPar` returns at any first file is a premise. Nothing on
soundness, on hiding or on a security level. For proofs only; no program imports this file.


-/
import OnBytes.K.ServedFreeItem
import OnBytes.Params.ConfigureLaws
import OnBytes.Model.Config

set_option autoImplicit false

namespace LPFPol

open OnBytes OnBytes.Model
open OnBytes.Params (exc_bind)
open OnBytes.K (size_olderLevel size_olderTK isSome_olderTK size_word32)

/-- A step that returns a can be replaced by a in what follows it. -/
theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {a : α} (h : x = .ok a) :
    (x >>= f) = f a := by
  subst h
  rfl

/-- `refuseIf` at false returns. -/
theorem refuseIf_no {b : Bool} {n : String} (h : b = false) : refuseIf b n = .ok () := by
  subst h
  rfl

/-- n zero bytes are n bytes. -/
theorem size_zeroBytes (n : Nat) : (Fmt.zeroBytes n).size = n := by
  simp [Fmt.zeroBytes, ByteArray.size]

/-- One level of `secondHashFunctionTreeLevels`, written out. -/
theorem olderLevels_succ (k num : Nat) (w : ByteArray) :
    secondHashFunctionTreeLevels (k + 1) num w =
      if (secondHashFunctionTreeLevel num w).size == 32 then some (secondHashFunctionTreeLevel num w)
      else secondHashFunctionTreeLevels k 11 (secondHashFunctionTreeLevel num w) := by
  rw [secondHashFunctionTreeLevels]

/-- k + 1 levels are enough for a string of 1 to 512 * 16^k bytes. -/
theorem isSome_levels (k : Nat) : ∀ (num : Nat) (w : ByteArray), 0 < w.size →
    w.size ≤ 512 * 16 ^ k → (secondHashFunctionTreeLevels (k + 1) num w).isSome = true := by
  induction k with
  | zero =>
    intro num w h0 h1
    have h1' : w.size ≤ 512 := by simpa using h1
    have e : (secondHashFunctionTreeLevel num w).size = 32 := by
      rw [size_olderLevel]
      omega
    rw [olderLevels_succ, e]
    rfl
  | succ k ih =>
    intro num w h0 h1
    rw [olderLevels_succ]
    by_cases hc : ((secondHashFunctionTreeLevel num w).size == 32) = true
    · rw [if_pos hc]
      rfl
    · rw [if_neg hc]
      have e : (16 : Nat) ^ (k + 1) = 16 ^ k * 16 := Nat.pow_succ 16 k
      rw [e] at h1
      apply ih 11
      · rw [size_olderLevel]
        omega
      · rw [size_olderLevel]
        omega

/-- The tree hash returns on every string of whole words, of at least 32 and fewer than 2^40
bytes. -/
theorem isSome_olderTK_of (w : ByteArray) (h4 : w.size % 4 = 0) (h32 : 32 ≤ w.size)
    (hb : w.size < 2 ^ 40) : (secondHashFunctionTree w).isSome = true := by
  have c : ¬ ((w.size % 4 != 0 || decide (w.size < 32)) = true) := by
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    omega
  unfold secondHashFunctionTree
  rw [if_neg c]
  exact isSome_levels 15 10 w (by omega)
    (Nat.le_of_lt (Nat.lt_of_lt_of_le hb (by decide)))

/-- What `textTH` returns has a digest of 32 bytes. -/
theorem textTH_size {t : ByteArray} {p : ByteArray × Nat} (h : textTH t = .ok p) :
    p.1.size = 32 := by
  unfold textTH at h
  obtain ⟨_, _, h⟩ := exc_bind h
  dsimp only at h
  split at h
  · rename_i d hd
    cases h
    exact size_olderTK hd
  · cases h

/-- `textTH` returns on every text of fewer than 2^32 bytes. -/
theorem textTH_returns (t : ByteArray) (h : t.size < 2 ^ 32) : ∃ p, textTH t = .ok p := by
  have hw : (word32 t.size ++ textWords t ++ Fmt.zeroBytes 28).size =
      4 + (t.size + (4 - t.size % 4) % 4) + 28 := by
    unfold textWords
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_append, size_word32,
      size_zeroBytes, size_zeroBytes]
  have hs : (secondHashFunctionTree (word32 t.size ++ textWords t ++ Fmt.zeroBytes 28)).isSome = true :=
    isSome_olderTK_of _ (by rw [hw]; omega) (by rw [hw]; omega) (by rw [hw]; omega)
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 hs
  refine ⟨(d, (word32 t.size ++ textWords t ++ Fmt.zeroBytes 28).size / 4), ?_⟩
  unfold textTH
  refine (bind_ok (refuseIf_no (decide_eq_false (by omega)))).trans ?_
  dsimp only
  rw [hd]
  rfl

/-- The digest of the layout file with its number of words, as `parDigests` forms it. -/
def layTH : Option ByteArray → Except String (ByteArray × Nat)
  | some t => textTH t
  | none => .ok (Fmt.zeroBytes 32, 0)

/-- What `parDigests` returns was made of three digests. -/
theorem parDigests_parts {pol KL : ByteArray} {layout : Option ByteArray} {D : ParDigests}
    (hD : parDigests pol KL layout = .ok D) :
    ∃ p k l, textTH pol = .ok p ∧ klHeld KL = .ok () ∧ secondHashFunctionTree KL = some k ∧
      layTH layout = .ok l ∧ D = ⟨p.1, p.2, k, klWords KL, l.1, l.2⟩ := by
  unfold parDigests at hD
  obtain ⟨p, hp, hD⟩ := exc_bind hD
  obtain ⟨u, a1, hD⟩ := exc_bind hD
  dsimp only at hD
  cases hk : secondHashFunctionTree KL with
  | none =>
    rw [hk] at hD
    try dsimp only at hD
    obtain ⟨_, e, _⟩ := exc_bind hD
    cases e
  | some k =>
    rw [hk] at hD
    try dsimp only at hD
    obtain ⟨_, e, hD⟩ := exc_bind hD
    cases e
    cases layout with
    | none =>
      try dsimp only at hD
      obtain ⟨_, e, hD⟩ := exc_bind hD
      cases e
      cases hD
      exact ⟨p, k, _, hp, a1, rfl, rfl, rfl⟩
    | some t =>
      try dsimp only at hD
      obtain ⟨l, a3, hD⟩ := exc_bind hD
      cases hD
      exact ⟨p, k, l, hp, a1, rfl, a3, rfl⟩

/-- The way back: of three digests `parDigests` makes its record. -/
theorem parDigests_of {pol KL : ByteArray} {layout : Option ByteArray} {p l : ByteArray × Nat}
    {k : ByteArray} (hp : textTH pol = .ok p) (a1 : klHeld KL = .ok ())
    (hk : secondHashFunctionTree KL = some k) (a3 : layTH layout = .ok l) :
    parDigests pol KL layout = .ok ⟨p.1, p.2, k, klWords KL, l.1, l.2⟩ := by
  unfold parDigests
  refine (bind_ok hp).trans ?_
  refine (bind_ok a1).trans ?_
  dsimp only
  rw [hk]
  try dsimp only
  refine (bind_ok (a := k) rfl).trans ?_
  cases layout with
  | none =>
    cases a3
    rfl
  | some t =>
    try dsimp only
    refine (bind_ok (a := l) a3).trans ?_
    rfl

/-- **`hPar` returns at a second parameter file.** Premises: h, it returns at pol; hl, pol' has
fewer than 2^32 bytes. The scale file and the layout file are the same. -/
theorem hPar_returns {pol pol' KL : ByteArray} {layout : Option ByteArray} {x : ByteArray}
    (h : hPar pol KL layout = .ok x) (hl : pol'.size < 2 ^ 32) :
    ∃ x', hPar pol' KL layout = .ok x' := by
  unfold hPar at h ⊢
  obtain ⟨D, hD, h⟩ := exc_bind h
  obtain ⟨p, k, l, hp, a1, hk, a3, rfl⟩ := parDigests_parts hD
  obtain ⟨p', hp'⟩ := textTH_returns pol' hl
  have e : (secondHashFunctionTree (p'.1 ++ word32 p'.2 ++ k ++ word32 (klWords KL) ++ l.1 ++ word32 l.2)).isSome =
      (secondHashFunctionTree (p.1 ++ word32 p.2 ++ k ++ word32 (klWords KL) ++ l.1 ++ word32 l.2)).isSome := by
    apply isSome_olderTK
    simp only [ByteArray.size_append, size_word32, textTH_size hp, textTH_size hp']
  have s : (secondHashFunctionTree (p.1 ++ word32 p.2 ++ k ++ word32 (klWords KL) ++ l.1 ++ word32 l.2)).isSome =
      true := by
    unfold hParOf at h
    dsimp only at h
    split at h
    · rename_i x0 hx
      rw [hx]
      rfl
    · cases h
  obtain ⟨x', hx'⟩ := Option.isSome_iff_exists.1 (e.trans s)
  refine ⟨x', ?_⟩
  refine (bind_ok (parDigests_of hp' a1 hk a3)).trans ?_
  unfold hParOf
  dsimp only
  rw [hx']
  rfl

end LPFPol

#print axioms LPFPol.hPar_returns
