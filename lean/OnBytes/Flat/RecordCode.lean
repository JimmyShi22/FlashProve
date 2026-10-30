-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/RecordCode.lean: a record of a stored table written as a list of 256-bit digests, no
two records alike, all with one number of digests.

A record in plain letters (`RecP`, OnBytes/Slice/KeyOfRec.lean) holds, for each of s answers, a
point of lg coordinates and a factor, and the answers of each of the 2 ^ v rows. Each
element of the field is written as the program writes it (`writeE`: three machine words below the
prime), and the three words are laid into the first 192 bits of a digest, lowest bit first.

Main definitions.
 `digW`, `digE`   an element of the program's type, and one of the field, as a digest.
 `codeS`          a record's seeds as a list: the points' coordinates, seed by seed; the factors.
 `codeA`          a record's answers as a list, in the order of the program's key (`keyOf`): entry
                  r * s + i is the answer of the row with the number r under seed i.
 `codeP`          a record as a list: `codeS` of its seeds, then `codeA` of its answers.
Main theorems.
 `digW_inj`, `digE_inj`, `codeS_inj`, `codeA_inj`, `codeP_inj`   no two are written alike.
 `codeS_length`, `codeA_length`, `codeP_length`   a list's length hangs on the three numbers alone.
 `codeA_key`      `codeA` is the array of the program's key, element by element.
 `codeP_eq`       by definition.

Not claimed. That any program hashes this list. The programs write a record as bytes in a statement,
not as digests.

-/
import OnBytes.Slice.KeyOfRec

set_option autoImplicit false

namespace OnBytes.Flat
open OnBytes.Slice _root_.Iop

/-- An element of the program's type as a digest: its three words in the bits 0 to 63, 64 to 127,
128 to 191, lowest bit first; the other bits are 0. -/
def digW (e : E) : Dig 256 := fun i =>
  if i.val < 64 then e.c0.toNat.testBit i.val
  else if i.val < 128 then e.c1.toNat.testBit (i.val - 64)
  else if i.val < 192 then e.c2.toNat.testBit (i.val - 128)
  else false

/-- Two words with the same 64 bits are one word. -/
theorem word_eq (a b : UInt64) (h : ∀ j, j < 64 → a.toNat.testBit j = b.toNat.testBit j) :
    a = b := by
  apply UInt64.toNat_inj.1
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 64
  · exact h j hj
  · have hp : 2 ^ 64 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hj)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le a.toNat_lt hp),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le b.toNat_lt hp)]

/-- No two elements of the program's type are written alike. -/
theorem digW_inj : Function.Injective digW := by
  intro a b h
  have h0 : a.c0 = b.c0 := word_eq _ _ fun j hj => by
    have := congrFun h ⟨j, by omega⟩
    simpa [digW, hj] using this
  have h1 : a.c1 = b.c1 := word_eq _ _ fun j hj => by
    have := congrFun h ⟨j + 64, by omega⟩
    simpa [digW, hj, show ¬ j + 64 < 64 by omega, show j + 64 < 128 by omega] using this
  have h2 : a.c2 = b.c2 := word_eq _ _ fun j hj => by
    have := congrFun h ⟨j + 128, by omega⟩
    simpa [digW, hj, show ¬ j + 128 < 64 by omega, show ¬ j + 128 < 128 by omega,
      show j + 128 < 192 by omega] using this
  cases a
  cases b
  simp_all

/-- An element of the field as a digest: as the program writes it. -/
def digE (x : GE) : Dig 256 := digW (writeE x)

/-- No two elements of the field are written alike. -/
theorem digE_inj : Function.Injective digE := fun x y h => by
  have := congrArg readE (digW_inj h)
  rwa [readE_writeE, readE_writeE] at this

section
variable {B : Type} (val : B → GE) {v lg s : ℕ}

/-- **A record's seeds as a list of digests**: the points' coordinates, seed by seed; the factors.
val: how a factor is read in the field. -/
def codeS (σ : Fin s → (Fin lg → GE) × B) : List (Dig 256) :=
  List.ofFn (fun q : Fin (s * lg) =>
      digE ((σ (finProdFinEquiv.symm q).1).1 (finProdFinEquiv.symm q).2)) ++
    List.ofFn (fun i : Fin s => digE (val (σ i).2))

/-- **A record's answers as a list of digests**, in the order of the program's key. -/
def codeA (a : (Fin v → Bool) × Fin s → GE) : List (Dig 256) :=
  List.ofFn fun n : Fin (2 ^ v * s) =>
    digE (a (vtx v (n.val / s), ⟨n.val % s, Nat.mod_lt _ (pos_of_place n)⟩))

/-- **A record as a list of digests.** -/
def codeP (r : RecP B v lg s) : List (Dig 256) := codeS val r.1 ++ codeA r.2

/-- By definition. -/
theorem codeP_eq (r : RecP B v lg s) : codeP val r = codeS val r.1 ++ codeA r.2 := rfl

/-- The seeds' list has a digest for each coordinate and factor. -/
theorem codeS_length (σ : Fin s → (Fin lg → GE) × B) : (codeS val σ).length = s * lg + s := by
  unfold codeS
  simp

/-- The answers' list has a digest for each row and answer. -/
theorem codeA_length (a : (Fin v → Bool) × Fin s → GE) : (codeA a).length = 2 ^ v * s := by
  unfold codeA
  simp

/-- A record's list. -/
theorem codeP_length (r : RecP B v lg s) :
    (codeP val r).length = s * lg + s + 2 ^ v * s := by
  rw [codeP_eq, List.length_append, codeS_length, codeA_length]

/-- The answers' list is the array of the program's key, element by element. -/
theorem codeA_key (r : RecP B v lg s) :
    codeA r.2 = (keyOf val r).record.toList.map digW := by
  unfold codeA keyOf
  simp [List.map_ofFn, Function.comp_def, digE]

/-- No two lists of seeds are written alike, if no two factors are read alike. -/
theorem codeS_inj (hv : Function.Injective val) :
    Function.Injective (codeS val (lg := lg) (s := s)) := by
  intro σ σ' h
  unfold codeS at h
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
  have e1 : ∀ i t, (σ i).1 t = (σ' i).1 t := fun i t => by
    have := congrFun (List.ofFn_injective h1) (finProdFinEquiv (i, t))
    simpa using digE_inj this
  have e2 : ∀ i, (σ i).2 = (σ' i).2 := fun i =>
    hv (digE_inj (congrFun (List.ofFn_injective h2) i))
  exact funext fun i => Prod.ext (funext (e1 i)) (e2 i)

/-- **No two tables of answers are written alike.** -/
theorem codeA_inj : Function.Injective (codeA (v := v) (s := s)) := by
  intro a a' h
  have e3 : (keyOf (fun x : GE => x) ((fun _ => (fun _ : Fin 0 => 0, 0), a) :
        RecP GE v 0 s)).record =
      (keyOf (fun x : GE => x) ((fun _ => (fun _ : Fin 0 => 0, 0), a') : RecP GE v 0 s)).record :=
    Array.toList_inj.1 (List.map_injective_iff.2 digW_inj (by
      rw [← codeA_key, ← codeA_key]
      exact h))
  funext p
  have h1 := keyOf_record (fun x : GE => x)
    ((fun _ => (fun _ : Fin 0 => 0, 0), a) : RecP GE v 0 s) p.1 p.2
  have h2 := keyOf_record (fun x : GE => x)
    ((fun _ => (fun _ : Fin 0 => 0, 0), a') : RecP GE v 0 s) p.1 p.2
  rw [e3] at h1
  exact h1.symm.trans h2

/-- **No two records are written alike**, if no two factors are read alike. -/
theorem codeP_inj (hv : Function.Injective val) :
    Function.Injective (codeP val (v := v) (lg := lg) (s := s)) := by
  intro r r' h
  rw [codeP_eq, codeP_eq] at h
  obtain ⟨h1, h2⟩ := List.append_inj h (by rw [codeS_length, codeS_length])
  exact Prod.ext (codeS_inj val hv h1) (codeA_inj h2)

end

end OnBytes.Flat

#print axioms OnBytes.Flat.digE_inj
#print axioms OnBytes.Flat.codeP_length
#print axioms OnBytes.Flat.codeP_inj
#print axioms OnBytes.Flat.codeA_inj
#print axioms OnBytes.Flat.codeA_length
#print axioms OnBytes.Flat.codeA_key
