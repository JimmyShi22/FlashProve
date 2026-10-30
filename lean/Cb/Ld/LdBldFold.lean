-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBldFold.lean: the parameters of one fold of the proximity test, the sumcheck that folds a
table of words (`SumPar`, Cb/Ld/LdSum.lean), are made here from numbers and two codes, with the
hiding polynomial's coefficients laid into the mask's message in one fixed order.

Definitions and statements; the proofs are in Cb/Ld/LdBldFoldProofs.lean. Generic: any finite field,
any long positions, any two codes read under a transformation. Nothing assumed beyond the hypotheses
of the statements and whatever the arguments hold as proofs. The file follows the paper that this
protocol builds on (lean/CREDITS.md).
The law of a packing (`PackLaw h g n pk Qw`, Cb/Ld/LdSumPack.lean) is an identity: for all
coefficients W and all points γ, the polynomial `hU` (Cb/Ld/LdHide.lean) with the coefficients W has
at γ the value ∑ j, Qw γ j · T j, where T is the table `pk W`, its rows on the cube of h variables
interpolated multilinearly at the first h coordinates of γ (`foldV`, Cb/Ld/LdRel.lean).

Why: the packing into 2^h rows (`pkC`, `QwC`, Cb/Ld/LdSumPack.lean) has columns with names
(`PCol h g m`) and is laid into a code's message through an injection that the caller supplies. The
instances supply it for toy codes, one message symbol a row. A stage of a whole test at given
numbers needs it for any mask code whose message coordinates are numbered, from one inequality
between numbers. No proof is an argument of a definition: the terms can be written for all numbers,
and are of use where `NoOK` holds.

Main names (before ⇒, `NoOK` is short for `NoOK (colCt h g m) idx`):
  `colCt h g m`: the number of columns: h m + (g (m + 1) + 1). `Spec.bld_colCt`: it is
    (h + g)(m + 1) + 1 - h, written without a subtraction.
  `colNo h g m`: the order of the columns, an explicit numbering (no choice). `Spec.bld_colNo`, in
    numbers: the column (i, q) of the first h variables (exponent q + 2) has the number q + m i; the
    coefficient (t, p) of the last g variables (exponent p + 1) the number h m + p + (m + 1) t; the
    constant comes last.
  `pkN`, `QwN h g m idx`: the table and the public weights for message coordinates J with a
    numbering idx : J → ℕ: the coordinate with the number c below `colCt` holds the column c; all
    other coordinates hold 0 and have the weight 0 (so, where there are idle coordinates, the fresh
    mask's message is not uniform on all its coordinates, whatever the coefficients' law).
  `fold h g m C Z AaW TW srcW idx`: the fold: 2^(h + g) main rows under C, 2^h mask rows under Z,
    round polynomials of degree at most m + 1, challenges from all of E, the fresh mask read under
    (AaW, TW, srcW), the packing `pkN`, `QwN`. Its own forms are 0 on one state: a tower puts its
    form in by `SumPar.reform`.
  `Spec.bld_at`: `NoOK` ⇒ `pkN`, `QwN` are the padded packing (`pkAt`, `QwAt`) along an injection
    that sends the column c to the coordinate with the number `colNo` c.
  `Spec.bld_law`: `NoOK` ⇒ the law of a packing (`PackLaw`). Also for a first stage on a group: a
    shape (`GShape`, Cb/Ld/LdGroupFold.lean; `StdArr`, Cb/Ld/LdGroupStd.lean) takes `pkN`, `QwN` as
    its fields pk, Qw.
  `Spec.bld_deg`: the degrees of the weights, for every numbering: at most m in each of the first h
    variables, at most m + 1 in the others.
  `Spec.bld_inj`: `NoOK` ⇒ the table determines the coefficients: none is lost.
  `Spec.bld_fold`: 1 ≤ m, `NoOK` ⇒ for every form sl that a tower puts in: challenges injective, 2 ≤
    degree, `SumPar.PackOK`, `SumPar.QwDeg`: the four clauses of a stage's fold that do not speak of
    codes.
  `Spec.bld_fin`: a numbering of Fin M by the value is `NoOK` at every N ≤ M: the predicate is not
    empty.

Limits: this file says nothing on the two codes (laws, distance, lists, agreement, what an encoding
hides): they are parameters here. It says nothing on errors. No protocol.
Declared differences to the paper that this protocol builds on: those of Cb/Ld/LdSumPack.lean, no
further one. By reading: the number of columns, the zeros in all further coordinates of every row
and of the public weights are the technical report's; the report leaves the order of the columns
open (a public parameter): colNo is one order.

Terms: lean/GLOSSARY.md.
"The technical report": this protocol's technical report (lean/CREDITS.md).
-/
import Cb.Ld.LdSumPack
import Cb.Ld.LdSumClaimY
import Cb.Ld.LdTowerSum
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false

namespace Cb.Bld
open Prob

/-- the number of columns of the packing into 2^h rows -/
def colCt (h g m : ℕ) : ℕ := h * m + (g * (m + 1) + 1)

/-- The order of the columns. -/
def colNo (h g m : ℕ) : PCol h g m ≃ Fin (colCt h g m) :=
  (Equiv.sumCongr finProdFinEquiv
      ((Equiv.sumCongr finProdFinEquiv (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv)).trans
    finSumFinEquiv

/-- what is asked of a numbering of coordinates: injective, and every number below N is taken -/
def NoOK {J : Type} (N : ℕ) (idx : J → ℕ) : Prop :=
  Function.Injective idx ∧ ∀ c, c < N → ∃ j, idx j = c

section Defs
variable {E : Type} [Field E] {J : Type}

/-- The table: the coordinate with the number c holds the column c; the others 0. -/
def pkN (h g m : ℕ) (idx : J → ℕ) (W : HIdx (sVars E (m + 1) (h + g)) → E) :
    (Fin h → Bool) × J → E := fun a =>
  if hc : idx a.2 < colCt h g m then pkC h g m W (a.1, (colNo h g m).symm ⟨idx a.2, hc⟩) else 0

/-- The public weights. -/
def QwN (h g m : ℕ) (idx : J → ℕ) (z : Fin (h + g) → E) : J → E := fun j =>
  if hc : idx j < colCt h g m then QwC h g m z ((colNo h g m).symm ⟨idx j, hc⟩) else 0

end Defs

/-- The fold of a stage. -/
def fold {E P : Type} [Field E] [Fintype E] (h g m : ℕ) (C Z : LdCode E P) (AaW : Type)
    (TW : Z.Word → P → AaW → E) (srcW : P → Finset Z.NP) (idx : Z.J → ℕ) : SumPar E P where
  h := h
  g := g
  n := m + 1
  Ch := E
  val := id
  C := C
  Z := Z
  AaW := AaW
  TW := TW
  srcW := srcW
  St := Unit
  StS := Unit
  sl := fun _ _ => 0
  slS := fun _ _ => 0
  pk := pkN h g m idx
  Qw := QwN h g m idx

namespace Spec

def bld_colCt : Prop := ∀ h g m : ℕ, colCt h g m + h = (h + g) * (m + 1) + 1

/-- The order, in numbers. -/
def bld_colNo : Prop :=
  ∀ h g m : ℕ,
    (∀ (i : Fin h) (q : Fin m), (colNo h g m (.inl (i, q))).val = q.val + m * i.val) ∧
    (∀ (t : Fin g) (p : Fin (m + 1)),
      (colNo h g m (.inr (.inl (t, p)))).val = h * m + (p.val + (m + 1) * t.val)) ∧
    (colNo h g m (.inr (.inr ()))).val = h * m + g * (m + 1)

/-- the numbering of Fin M by the value -/
def bld_fin : Prop := ∀ N M : ℕ, N ≤ M → NoOK N (fun j : Fin M => j.val)

section
variable (E : Type) [Field E]

/-- States: under `NoOK (colCt h g m) idx`, `pkN`, `QwN` are the padded packing. -/
def bld_at : Prop :=
  ∀ (h g m : ℕ) (J : Type) [Fintype J] [DecidableEq J] (idx : J → ℕ), NoOK (colCt h g m) idx →
    ∃ plc : PCol h g m → J, Function.Injective plc ∧ (∀ c, idx (plc c) = (colNo h g m c).val) ∧
      pkN (E := E) h g m idx = pkAt plc (pkC h g m) ∧ QwN (E := E) h g m idx = QwAt plc (QwC h g m)

/-- The law of a packing. -/
def bld_law : Prop :=
  ∀ (h g m : ℕ) (J : Type) [Fintype J] (idx : J → ℕ),
    NoOK (colCt h g m) idx → PackLaw (E := E) h g (m + 1) (pkN h g m idx) (QwN h g m idx)

/-- The degrees of the weights. -/
def bld_deg : Prop :=
  ∀ (h g m : ℕ) (J : Type) (idx : J → ℕ) (j : J), Alg.DegLE
    (fun v : Fin (h + g) => if v.val < h then m else m + 1) (fun z => QwN (E := E) h g m idx z j)

/-- States: under `NoOK (colCt h g m) idx`, no coefficient is lost. -/
def bld_inj : Prop :=
  ∀ (h g m : ℕ) (J : Type) (idx : J → ℕ),
    NoOK (colCt h g m) idx → Function.Injective (pkN (E := E) h g m idx)

/-- The four clauses of a stage's fold that do not speak of codes. -/
def bld_fold [Fintype E] : Prop :=
  ∀ (P : Type) (h g m : ℕ) (C Z : LdCode E P) (AaW : Type) (TW : Z.Word → P → AaW → E)
      (srcW : P → Finset Z.NP) (idx : Z.J → ℕ),
    1 ≤ m → NoOK (colCt h g m) idx →
    ∀ (St : Type) (sl : Slf E St (fold h g m C Z AaW TW srcW idx).Cin.J),
      Function.Injective ((fold h g m C Z AaW TW srcW idx).reform sl).val ∧
      2 ≤ ((fold h g m C Z AaW TW srcW idx).reform sl).n ∧
      ((fold h g m C Z AaW TW srcW idx).reform sl).PackOK ∧
      ((fold h g m C Z AaW TW srcW idx).reform sl).QwDeg

end
end Spec
end Cb.Bld
