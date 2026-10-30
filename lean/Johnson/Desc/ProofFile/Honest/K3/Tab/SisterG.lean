-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Tab/SisterG.lean:
a second text of the products in a key of the layers' calls, in which the factors of the long sums
are read off rows that are handed in; and the theorems that, at rows whose values are the library's
own factors, it is the library's text. Definitions with code, and theorems without a
hypothesis but the one that is named.

Terms. Honest/K3/GLOSSARY.md. In this file: the library's text is `gamG` with what it calls
(OnBytes/Tie/Pv/Lookup/Ends/G.lean). A row (`Row`) is an array with a function behind it: its value
at a number is the array's entry where there is one, the function's value beyond the array's end
(`Memo.read`, Honest/K3/Memo.lean). It has two fields, so that a program holds it as an object: an
application that yields a row is done once, in front of a sum. (A structure of one field is erased
by Lean's compiler, and the application was then done anew at every term: that was tried.)

Why. The library's text spells each matrix product out term by term and makes both factors of a
term anew (`ten`, `wt`, `gated`) from the cells, for each key. Here a sum's two factors are read
off two rows, which are fetched once in front of the sum.

This is a second text beside a definition of the library. It is kept as thin as could be: only seven
arms of `gamG` are written anew, each of which holds a sum over a model's dimension (G and U, V, O,
D, LR, QK), with the five accumulators that they call; the order of the arms (but QK, which is drawn
forward, in front of N1 and N2), the shifts, the rotary table's factors and the public stub are the
library's words; the other arms call the library.
It is typed for the honest prover's own sake, and for that alone.
`mul0` changes what a program evaluates, not the value (`mul0_eq`); it asks `[DecidableEq R]` of the
ring.

What is defined.
  `Row`, `Row.get`, `Inner`: a row; its value; the five families of rows that the sums read.
  `Inner.Is`: the rows' values are the library's own factors. Meant as a hypothesis: the theorems'.
  `innerOf`: the library's own factors as rows with empty arrays.
  `mul0`: a product whose second factor is not made where the first is 0.
  `accDenseBy`, `accRoutedBy`, `accDBy`, `accQKBy`, `rotQKBy`, `attORow`, `gamGBy`: the second text.
  `kvOfBy`: the text of `kvOf` with `col q j` in the place of `colG P.y q j`: the library's `colG`
    walks the segments' lists of positions anew for each key.

What is shown.
  `Row.get_nil`: at the empty array a row's value is the function's.
  `mul0_eq`: `mul0` is the product. `innerOf_is`: that hypothesis holds of `innerOf`.
  `accDenseBy_of`, `accRoutedBy_of`, `accDBy_of`, `accQKBy_of`, `rotQKBy_of`, `attORow_of`: under
    `Inner.Is` each is the library's.
  `kvOfBy_of`: at `colG P.y` it is `kvOf`: by `rfl`.
  `gamGBy_of`: the last theorem, conditional on `Inner.Is P g cell I`: `gamGBy P g cell I` is
    `gamG P g cell`.

Imported. OnBytes/Tie/Pv/Lookup/Ends/G.lean and what stands beneath it; Honest/K3/Memo.lean.

Limits. Nothing says how long anything takes. At rows of which `Inner.Is` fails nothing is said.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import OnBytes.Tie.Pv.Lookup.Ends.G
import Johnson.Desc.ProofFile.Honest.K3.Memo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.TabG
open OnBytes.Model OnBytes.Ends.G

/-- An array with a function behind it. -/
structure Row (R : Type) where
  /-- the values at the numbers below its size -/
  arr : Array R
  /-- the values beyond -/
  f : ℕ → R

/-- A row's value at a number. -/
def Row.get {R : Type} (r : Row R) (k : ℕ) : R := Memo.read r.arr r.f k

/-- At the empty array the value is the function's. -/
theorem Row.get_nil {R : Type} (f : ℕ → R) (k : ℕ) : (⟨#[], f⟩ : Row R).get k = f k :=
  Memo.read_empty f k

/-- **The rows that the long sums read.** -/
structure Inner (R : Type) where
  /-- of a tensor's name, an instance and a token: the tensor's entries -/
  tn : String → ℕ → ℕ → Row R
  /-- of a layer of the group and a token: the gated products by feature -/
  su : ℕ → ℕ → Row R
  /-- of a layer of the group, a head and a coordinate: the weights of kind 0 by channel -/
  w0 : ℕ → ℕ → ℕ → Row R
  /-- of a kind, a layer of the group and a second index: the weights by their first index -/
  w2 : ℕ → ℕ → ℕ → Row R
  /-- of a kind, a layer of the group, a second and a third index: the weights by their first -/
  w3 : ℕ → ℕ → ℕ → ℕ → Row R

variable {R : Type} [CommRing R]

/-- **The theorems' hypothesis: the rows' values are the library's own factors.** -/
structure Inner.Is (P : Layer.Pub) (g : ℕ) (cell : NameG → R) (I : Inner R) : Prop where
  tn : ∀ n inst i x, (I.tn n inst i).get x = ten P cell n inst x i
  su : ∀ lam i k, (I.su lam i).get k = gated P cell lam k i
  w0 : ∀ lam hd cd k, (I.w0 lam hd cd).get k = wt P cell 0 (lOf P g lam) [hd, cd, k]
  w2 : ∀ X lam x k, (I.w2 X lam x).get k = wt P cell X (lOf P g lam) [k, x]
  w3 : ∀ X lam e x k, (I.w3 X lam e x).get k = wt P cell X (lOf P g lam) [k, e, x]

/-- The library's own factors, as rows with empty arrays. -/
def innerOf (P : Layer.Pub) (g : ℕ) (cell : NameG → R) : Inner R :=
  { tn := fun n inst i => ⟨#[], fun x => ten P cell n inst x i⟩
    su := fun lam i => ⟨#[], fun k => gated P cell lam k i⟩
    w0 := fun lam hd cd => ⟨#[], fun k => wt P cell 0 (lOf P g lam) [hd, cd, k]⟩
    w2 := fun X lam x => ⟨#[], fun k => wt P cell X (lOf P g lam) [k, x]⟩
    w3 := fun X lam e x => ⟨#[], fun k => wt P cell X (lOf P g lam) [k, e, x]⟩ }

/-- That hypothesis holds of them. -/
theorem innerOf_is (P : Layer.Pub) (g : ℕ) (cell : NameG → R) :
    (innerOf P g cell).Is P g cell :=
  ⟨fun _ _ _ _ => Row.get_nil _ _, fun _ _ _ => Row.get_nil _ _, fun _ _ _ _ => Row.get_nil _ _,
   fun _ _ _ _ => Row.get_nil _ _, fun _ _ _ _ _ => Row.get_nil _ _⟩

/-- A product whose second factor is not made where the first is 0. -/
def mul0 [DecidableEq R] (a : R) (f : Unit → R) : R := if a = 0 then 0 else a * f ()

theorem mul0_eq [DecidableEq R] (a : R) (f : Unit → R) : mul0 a f = a * f () := by
  unfold mul0
  split_ifs with h
  · rw [h, zero_mul]
  · rfl

variable (P : Layer.Pub) (g : ℕ) (cell : NameG → R) (I : Inner R)

/-- `accDense`, off rows. -/
def accDenseBy (up : Bool) (lam x i : ℕ) : R :=
  let X := if moe P lam then (if up then 6 else 5) else (if up then 4 else 3)
  let a := I.tn "m" lam i
  let b := I.w2 X lam x
  sumN P.y.h.d fun k2 => a.get k2 * b.get k2

/-- `accRouted`, off rows. -/
def accRoutedBy [DecidableEq R] (up : Bool) (lam x i : ℕ) : R :=
  let s := I.tn "sel" (lam / 2) i
  let a := I.tn "xr" (lam / 2) i
  sumN P.y.h.NE fun e =>
    mul0 (s.get e) fun _ =>
      let b := I.w3 (if up then 8 else 7) lam e (x - P.y.h.fe)
      sumN P.y.h.d fun k2 => a.get k2 * b.get k2

/-- `attO` at a layer and a token, as a row. -/
def attORow (lam i : ℕ) : Row R :=
  if P.y.h.p4 then I.tn "o" lam i
  else ⟨#[], fun k2 => ((Layer.stubO P.y (lOf P g lam) i k2 : ℤ) : R)⟩

/-- `accD`, off rows. -/
def accDBy [DecidableEq R] (lam x i : ℕ) : R :=
  let G := I.su lam i
  (let b := I.w2 9 lam x
   sumN (if moe P lam then P.y.h.fe else P.y.h.f) fun k => G.get k * b.get k) +
    (if moe P lam then
      let s := I.tn "sel" (lam / 2) i
      sumN P.y.h.NE fun e =>
        mul0 (s.get e) fun _ =>
          let b := I.w3 10 lam e x
          sumN P.y.h.fe fun k => G.get (P.y.h.fe + k) * b.get k
    else 0)

/-- `accQK`, off rows. -/
def accQKBy (lam hd cd i : ℕ) : R :=
  let a := I.tn "a" lam i
  let b := I.w0 lam hd cd
  sumN P.y.h.d fun k2 => a.get k2 * b.get k2

/-- `rotQK`, over `accQKBy`. -/
def rotQKBy (lam x i : ℕ) : R :=
  let dh := P.y.h.dh
  let hd := x / dh
  let cd := x % dh
  let C : R := ((Layer.ropeC P.y.h P.sc P.rope (lOf P g lam) i (cd / 2) false : ℤ) : R)
  let S : R := ((Layer.ropeC P.y.h P.sc P.rope (lOf P g lam) i (cd / 2) true : ℤ) : R)
  if cd % 2 == 0 then C * accQKBy P I lam hd cd i - S * accQKBy P I lam hd (cd + 1) i
  else S * accQKBy P I lam hd (cd - 1) i + C * accQKBy P I lam hd cd i

/-- **`gamG`, its long sums off rows.** -/
def gamGBy [DecidableEq R] (sn : String) (lam x i : ℕ) : R :=
  if sn == "G" || sn == "U" then
    let up := sn == "U"
    2 ^ (16 - kGU P g up lam x) *
      (if routed P lam x then accRoutedBy P I up lam x i else accDenseBy P I up lam x i)
  else if sn == "V" then
    2 ^ (16 - kL P g lam Layer.Lkv) *
      (let a := I.tn "a" lam i
       let b := I.w2 1 lam x
       sumN P.y.h.d fun k2 => a.get k2 * b.get k2)
  else if sn == "O" then
    2 ^ (16 - kL P g lam Layer.Lko) *
      (let a := attORow P g I lam i
       let b := I.w2 2 lam x
       sumN P.y.dq fun k2 => a.get k2 * b.get k2)
  else if sn == "D" then 2 ^ (16 - kL P g lam Layer.Lkd) * accDBy P I lam x i
  else if sn == "LR" then
    2 ^ (16 - kR P g lam) *
      (let a := I.tn "m" lam i
       let b := I.w2 11 lam x
       sumN P.y.h.d fun k2 => a.get k2 * b.get k2)
  else if sn == "QK" then 2 ^ (16 - kQK P g lam x) * rotQKBy P g I lam x i
  else gamG P g cell sn lam x i

/-- **`kvOf`, with the entry and the segment of a column read off a function that is handed in.**
The library's text but for `col q j` in the place of `colG P.y q j`. -/
def kvOfBy (col : ℕ → ℕ → Option (Seg × ℕ)) (f : String → ℕ → ℕ → ℕ → R) (q X : ℕ) : R :=
  let lJ := (P.y.calls.getD q default).lJ
  let i := X % P.y.T
  let j := X / P.y.T % 2 ^ lJ
  let lam := X / P.y.T / 2 ^ lJ
  match col q j with
  | some (s, x) =>
    if s.moe && lam % 2 == 0 then (OnBytes.Ends.tauN P.y.fo q (OnBytes.Ends.t0N P.y.fo q) : R)
    else f s.name lam x i
  | none => (OnBytes.Ends.tauN P.y.fo q (OnBytes.Ends.t0N P.y.fo q) : R)

/-- At the library's `colG` it is `kvOf`. -/
theorem kvOfBy_of (f : String → ℕ → ℕ → ℕ → R) (q X : ℕ) :
    kvOfBy P (colG P.y) f q X = kvOf P f q X := rfl

/-! ## At rows whose values are the library's own factors -/

variable {P g cell I}

theorem accDenseBy_of (h : I.Is P g cell) (up : Bool) (lam x i : ℕ) :
    accDenseBy P I up lam x i = accDense P g cell up lam x i := by
  simp only [accDenseBy, accDense, h.tn, h.w2]

theorem accRoutedBy_of [DecidableEq R] (h : I.Is P g cell) (up : Bool) (lam x i : ℕ) :
    accRoutedBy P I up lam x i = accRouted P g cell up lam x i := by
  simp only [accRoutedBy, accRouted, mul0_eq, h.tn, h.w3]

theorem attORow_of (h : I.Is P g cell) (lam k2 i : ℕ) :
    (attORow P g I lam i).get k2 = attO P g cell lam k2 i := by
  unfold attORow attO
  split_ifs
  · exact h.tn _ _ _ _
  · exact Row.get_nil _ _

theorem accDBy_of [DecidableEq R] (h : I.Is P g cell) (lam x i : ℕ) :
    accDBy P I lam x i = accD P g cell lam x i := by
  simp only [accDBy, accD, mul0_eq, h.tn, h.su, h.w2, h.w3]

theorem accQKBy_of (h : I.Is P g cell) (lam hd cd i : ℕ) :
    accQKBy P I lam hd cd i = accQK P g cell lam hd cd i := by
  simp only [accQKBy, accQK, h.tn, h.w0]

theorem rotQKBy_of (h : I.Is P g cell) (lam x i : ℕ) :
    rotQKBy P g I lam x i = rotQK P g cell lam x i := by
  simp only [rotQKBy, rotQK, accQKBy_of h]

/-- **At rows whose values are the library's own factors the second text is the library's.**
Conditional on `Inner.Is`. -/
theorem gamGBy_of [DecidableEq R] (h : I.Is P g cell) (sn : String) (lam x i : ℕ) :
    gamGBy P g cell I sn lam x i = gamG P g cell sn lam x i := by
  unfold gamGBy
  simp only [accRoutedBy_of h, accDenseBy_of h, accDBy_of h, rotQKBy_of h, attORow_of h, h.tn, h.w2]
  by_cases h1 : (sn == "G" || sn == "U") = true
  · simp only [if_pos h1, gamG]
  by_cases h2 : (sn == "V") = true
  · simp only [if_neg h1, if_pos h2, gamG]
  by_cases h3 : (sn == "O") = true
  · simp only [if_neg h1, if_neg h2, if_pos h3, gamG]
  by_cases h4 : (sn == "D") = true
  · simp only [if_neg h1, if_neg h2, if_neg h3, if_pos h4, gamG]
  by_cases h5 : (sn == "LR") = true
  · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5, gamG]
  by_cases h6 : (sn == "QK") = true
  · have e : sn = "QK" := by simpa using h6
    have n1 : ¬ (sn == "N1") = true := by subst e; decide
    have n2 : ¬ (sn == "N2") = true := by subst e; decide
    simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6, if_neg n1,
      if_neg n2, gamG]
  simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6]

end ProofFile.Honest.K3.TabG

#print axioms ProofFile.Honest.K3.TabG.mul0_eq
#print axioms ProofFile.Honest.K3.TabG.innerOf_is
#print axioms ProofFile.Honest.K3.TabG.kvOfBy_of
#print axioms ProofFile.Honest.K3.TabG.accDenseBy_of
#print axioms ProofFile.Honest.K3.TabG.accRoutedBy_of
#print axioms ProofFile.Honest.K3.TabG.attORow_of
#print axioms ProofFile.Honest.K3.TabG.accDBy_of
#print axioms ProofFile.Honest.K3.TabG.accQKBy_of
#print axioms ProofFile.Honest.K3.TabG.rotQKBy_of
#print axioms ProofFile.Honest.K3.TabG.gamGBy_of
