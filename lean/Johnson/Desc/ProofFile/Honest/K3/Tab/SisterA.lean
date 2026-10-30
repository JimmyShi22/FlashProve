-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Tab/SisterA.lean: the key formulas of an attention sub-proof's
lookup (OnBytes/Tie/Pv/Lookup/Ends/A.lean) with the factors of their two long sums taken as
arguments; and that at the library's own factors they are the library's formulas. Conditional on
`InnerA.Is`. Definitions with code, and theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: the two long sums are `A.score`, over the dh features of
a head, and `A.acc`, over the places of a token's row; a row is a value of `TabG.Row`
(Honest/K3/Tab/SisterG.lean): an array with a function behind it.

Why. `A.score` reads 2 dh values of `A.ten` for each key of the segments fm and fd, and `A.acc` a
value of `A.wt` and one of `A.ten` for each place of a token's row, for each key of the segment wl;
each such value is made of cells anew. Here they are read off rows, which a caller can make once.

A second text beside a definition of the library, as thin as it can be. Only the two sums' bodies
are abstracted; of `segKey` the three arms that read them are copied (fm, fd, wl), and the other
four segments are handed to `A.segKey` itself; `ssAt`, `kvSel` and `kvA` are copied to the letter,
with the new names laid in; in the arms of fm and fd the one `A.wt` is read off its row.

What is defined.
  `InnerA R`: the rows: q and k: of a layer and a token, `ten` at `S.atQ` and at `S.atK` by feature;
    v: of a layer and a feature, `ten` at `S.atV` by token; w: of the sort of place, a layer and a
    head of a group, `wt` by place.
  `InnerA.Is S cell I`: the rows' values are the library's own factors. Meant as a hypothesis.
  `innerOfA S cell`: the library's own factors as rows with empty arrays.
  `scoreBy`, `accBy`, `ssAtBy`, `segKeyBy`, `kvSelBy`, `kvABy`: the sister texts. In `scoreBy` and
    `accBy` the rows are picked in front of the sums.

What is shown.
  `innerOfA_is`: `InnerA.Is` has a member at every S and cell.
  `scoreBy_of`, `accBy_of`, `ssAtBy_of`, `segKeyBy_of`, `kvSelBy_of`, `kvABy_of`: conditional on
    `InnerA.Is S cell I`: each sister text is the library's formula.

Imported. OnBytes/Tie/Pv/Lookup/Ends/A.lean; Honest/K3/Tab/SisterG.lean, for `Row`, and through it
OnBytes/Tie/Pv/Lookup/Ends/G.lean and Honest/K3/Memo.lean. No file of the frame.

Users. Honest/K3/Tab/TabA.lean.

Limits. Nothing says how long anything takes. At rows of which `InnerA.Is` fails nothing is said.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import OnBytes.Tie.Pv.Lookup.Ends.A
import Johnson.Desc.ProofFile.Honest.K3.Tab.SisterG

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.TabA
open OnBytes.Model OnBytes.Ends OnBytes.Ends.A
open ProofFile.Honest.K3.TabG (Row)

/-- **The rows that the two long sums read.** -/
structure InnerA (R : Type) where
  /-- of a layer and a token: q's entries by feature -/
  q : ℕ → ℕ → Row R
  /-- of a layer and a token: k's entries by feature -/
  k : ℕ → ℕ → Row R
  /-- of a layer and a feature: v's entries by token -/
  v : ℕ → ℕ → Row R
  /-- of the sort of place (on the diagonal tiles or below), a layer and a head of a group: the
  softmax weights by place -/
  w : Bool → ℕ → ℕ → Row R

variable {R : Type} [CommRing R]

/-- **The theorems' hypothesis: the rows' values are the library's own factors.** -/
structure InnerA.Is (S : Sh) (cell : NameA → R) (I : InnerA R) : Prop where
  q : ∀ lam i f, (I.q lam i).get f = ten S cell S.atQ lam f i
  k : ∀ lam i f, (I.k lam i).get f = ten S cell S.atK lam f i
  v : ∀ lam f i, (I.v lam f).get i = ten S cell S.atV lam f i
  w : ∀ isD lam a π, (I.w isD lam a).get π = wt S cell lam a isD π

/-- The library's own factors, as rows with empty arrays. -/
def innerOfA (S : Sh) (cell : NameA → R) : InnerA R :=
  { q := fun lam i => ⟨#[], fun f => ten S cell S.atQ lam f i⟩
    k := fun lam i => ⟨#[], fun f => ten S cell S.atK lam f i⟩
    v := fun lam f => ⟨#[], fun i => ten S cell S.atV lam f i⟩
    w := fun isD lam a => ⟨#[], fun π => wt S cell lam a isD π⟩ }

/-- That hypothesis has a member. -/
theorem innerOfA_is (S : Sh) (cell : NameA → R) : (innerOfA S cell).Is S cell :=
  ⟨fun _ _ _ => Row.get_nil _ _, fun _ _ _ => Row.get_nil _ _, fun _ _ _ => Row.get_nil _ _,
    fun _ _ _ _ => Row.get_nil _ _⟩

section Sisters
variable (S : Sh) (cell : NameA → R) (I : InnerA R)

/-- `A.score`, its factors off two rows. -/
def scoreBy (lam hd g ti tj : ℕ) : R :=
  let a := I.q lam ti
  let b := I.k lam tj
  sumN S.dh fun n => a.get (hd * S.dh + n) * b.get (g * S.dh + n)

/-- `A.acc`, its factors off three rows. -/
def accBy (lam a g i n : ℕ) : R :=
  let wm := I.w false lam a
  let wd := I.w true lam a
  let vv := I.v lam (g * S.dh + n)
  (sumN S.hP fun P => sumN (S.nT - 1) fun sg =>
    if (S.cover P sg).1 = i / S.B then
      sumN S.B fun j => wm.get (codeM S g P sg (i % S.B) j) * vv.get ((S.cover P sg).2 * S.B + j)
    else 0) +
  sumN S.B fun j => wd.get (codeD S g (i / S.B) (i % S.B) j) * vv.get (i / S.B * S.B + j)

/-- `A.ssAt` over `scoreBy`. -/
def ssAtBy (isD : Bool) (lam a κ : ℕ) : R :=
  let j := κ % S.B
  let i := κ / S.B % S.B
  if isD then
    let I' := κ / (S.B * S.B) % S.nT
    let g := κ / (S.B * S.B * S.nT)
    scoreBy S I lam (g * S.HA + a) g (I' * S.B + i) (I' * S.B + j)
  else
    let sg := κ / (S.B * S.B) % S.nT
    let P := κ / (S.B * S.B * S.nT) % S.hP
    let g := κ / (S.B * S.B * S.nT * S.hP)
    if sg = S.nT - 1 then 0
    else scoreBy S I lam (g * S.HA + a) g ((S.cover P sg).1 * S.B + i) ((S.cover P sg).2 * S.B + j)

/-- `A.segKey` over `ssAtBy` and `accBy`: the arms of fm, fd and wl; at the other four segments it
is `A.segKey` itself. -/
def segKeyBy (sh : ℕ) (s : OnBytes.Attention.Seg) (lam a κ : ℕ) : R :=
  let isD := s == OnBytes.Attention.Seg.rd || s == OnBytes.Attention.Seg.fd
  match s with
  | .fm | .fd =>
    gapAt S cell sh isD lam a κ - ssAtBy S I isD lam a κ - (asC S cell 0 lam a isD κ + 128) -
      256 * (asC S cell 1 lam a isD κ + 128) + ((2 ^ 32 : ℕ) : R) * asC S cell 2 lam a isD κ +
      ((2 ^ 33 : ℕ) : R) * (I.w isD lam a).get κ
  | .wl =>
    let n := κ % S.dh
    let i := κ / S.dh % S.T
    let g := κ / (S.dh * S.T) % S.G
    let hd := g * S.HA + a
    let dn := den S cell lam hd i
    let re := 2 * accBy S I lam a g i n + dn - 2 * (dn * ten S cell S.atO lam (hd * S.dh + n) i)
    if κ / (S.dh * S.T * S.G) = 0 then re - 65536 * (rh S cell lam (hd * S.dh + n) i + 128)
    else 2 * dn - 1 - re - 65536 * (rhp S cell lam (hd * S.dh + n) i + 128)
  | s => segKey S cell sh s lam a κ

/-- `A.kvSel` over `segKeyBy`. -/
def kvSelBy (h : Forest.Shape) (sel : OnBytes.Attention.Seg → Bool) (pad : Bool) (q X : ℕ) : R :=
  match S.calls[q]? with
  | none => 0
  | some c =>
    match c.pcs.toList.find? fun p => decide (p.off ≤ X ∧ X < p.off + 2 ^ p.b) with
    | some p => if sel p.seg then segKeyBy S cell I c.sh p.seg p.lam p.a (X - p.off) else 0
    | none => if pad then (tauN h q (t0N h q) : R) else 0

/-- `A.kvA` over `kvSelBy`. -/
def kvABy (h : Forest.Shape) (q X : ℕ) : R := kvSelBy S cell I h (fun _ => true) true q X

variable {S cell I}

/-- Conditional on `InnerA.Is`: `scoreBy` is `A.score`. -/
theorem scoreBy_of (hI : I.Is S cell) (lam hd g ti tj : ℕ) :
    scoreBy S I lam hd g ti tj = score S cell lam hd g ti tj := by
  simp only [scoreBy, score, hI.q, hI.k]

/-- Conditional on `InnerA.Is`: `accBy` is `A.acc`. -/
theorem accBy_of (hI : I.Is S cell) (lam a g i n : ℕ) :
    accBy S I lam a g i n = acc S cell lam a g i n := by
  simp only [accBy, acc, hI.w, hI.v]

/-- Conditional on `InnerA.Is`: `ssAtBy` is `A.ssAt`. -/
theorem ssAtBy_of (hI : I.Is S cell) (isD : Bool) (lam a κ : ℕ) :
    ssAtBy S I isD lam a κ = ssAt S cell isD lam a κ := by
  simp only [ssAtBy, ssAt, scoreBy_of hI]

/-- Conditional on `InnerA.Is`: `segKeyBy` is `A.segKey`. -/
theorem segKeyBy_of (hI : I.Is S cell) (sh : ℕ) (s : OnBytes.Attention.Seg) (lam a κ : ℕ) :
    segKeyBy S cell I sh s lam a κ = segKey S cell sh s lam a κ := by
  cases s <;> simp only [segKeyBy, segKey, ssAtBy_of hI, accBy_of hI, hI.w]

/-- Conditional on `InnerA.Is`: `kvSelBy` is `A.kvSel`. -/
theorem kvSelBy_of (hI : I.Is S cell) (h : Forest.Shape) (sel : OnBytes.Attention.Seg → Bool)
    (pad : Bool) (q X : ℕ) : kvSelBy S cell I h sel pad q X = kvSel S h cell sel pad q X := by
  simp only [kvSelBy, kvSel, segKeyBy_of hI]
  rfl

/-- **Conditional on `InnerA.Is`: `kvABy` is `A.kvA`.** -/
theorem kvABy_of (hI : I.Is S cell) (h : Forest.Shape) (q X : ℕ) :
    kvABy S cell I h q X = kvA S h cell q X :=
  kvSelBy_of hI h _ _ q X

end Sisters

end ProofFile.Honest.K3.TabA

#print axioms ProofFile.Honest.K3.TabA.innerOfA_is
#print axioms ProofFile.Honest.K3.TabA.scoreBy_of
#print axioms ProofFile.Honest.K3.TabA.accBy_of
#print axioms ProofFile.Honest.K3.TabA.ssAtBy_of
#print axioms ProofFile.Honest.K3.TabA.segKeyBy_of
#print axioms ProofFile.Honest.K3.TabA.kvSelBy_of
#print axioms ProofFile.Honest.K3.TabA.kvABy_of
