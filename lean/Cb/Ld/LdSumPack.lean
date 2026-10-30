-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSumPack.lean: how the coefficients of the hiding polynomial lie in the fresh mask's table,
with 2^h rows, so that public weights applied to the folded table give the polynomial's value.

Definitions and statements (each a `Prop` in `Cb.Spec`); the proofs are in
Cb/Ld/LdSumPackProofs.lean.

Why: the fold of Cb/Ld/LdSum.lean has the packing as a parameter (`SumPar.pk`, `SumPar.Qw`) with one
law (`SumPar.PackOK`): the hiding polynomial at a point γ is the value of public weights at γ on the
table folded at the first h coordinates of γ. Here are the packings that meet the law.

The polynomial (`hU`, Cb/Ld/LdHide.lean; k = h + g plain variables, round polynomials of degree at
most n):
      U(X) = ∑_l ∑_(p = 1 .. n) w(l, p) X_l^p X_(l+1) .. X_k + c.
  It has k n + 1 coefficients. `hIx`, `hCst`: the names of the coefficients by
  (variable, exponent - 1), and of the constant.
  `Spec.ld_pack_formula`: the display above, for n ≥ 1.
The law, free of a code (`PackLaw h g n pk Qw`, for tables with columns J): `SumPar.PackOK` is
`PackLaw` at the block's own data (`Spec.ld_pack_ok_iff`).
The packing into 2^h rows (`pkC`, `QwC`; n = m + 1). A monomial of one of the first h variables is
split in two factors,
      X_i^p X_(i+1) .. X_k = ( X_i X_(i+1) .. X_h ) · ( X_i^(p-1) X_(h+1) .. X_k ).
  The first factor is multilinear in the first h variables: it is tabulated on the cube, one row for
  each corner β, times its coefficient; folding the table at γ evaluates it. The second factor is
  the public weight of the column. Monomials with the same weight share a column.
  Columns (`PCol h g m`): (i, p) for i ≤ h and 2 ≤ p ≤ n: the entry at the row β is w(i, p) β_i ..
  β_h, the weight γ_i^(p-1) γ_(h+1) .. γ_k; and one column for each coefficient of the last g
  variables and for the constant: the entry is that coefficient in every row, the weight its own
  monomial.
  The h terms with p = 1 have the weight γ_(h+1) .. γ_k, which is already there: it is the weight of
  w(h+1, 1), or of the constant if g = 0 (the leading column, `pLead`). Their tabulated factors are
  added to that column. So h columns are saved: `Spec.ld_pack_card`: the number of columns is k n +
  1 - h. `Spec.ld_pack_law`: the law holds.
  For h = 0 the table has one row, which holds the coefficients, each in a column of its own, with
  its own monomial as weight.
Padding (`pkAt`, `QwAt`). The columns are laid into the message coordinates J of a code through an
injection plc; the other coordinates hold 0 and have the weight 0. `Spec.ld_pack_place`: the law is
kept.
Further statements:
  `Spec.ld_pack_deg`: every weight is a polynomial of degree at most n - 1 in each of the first h
    variables and at most n in each of the others (so that weight times folded table has degree at
    most n in every variable).
  `Spec.ld_pack0`: the plain packing for h = 0 and every n (one row, the coefficients under their
    own names, the weights `hSl` of Cb/Ld/LdHide.lean) meets the law.

Limits:
Declared differences to the text that we follow. One generator of the module (the field itself).
Columns have names, not an order. The text asks that the message of the mask code have at least k n
+ 1 - h coordinates: here that is the existence of the injection plc.
This file says nothing on running times. It says nothing on a protocol.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSum
import Alg.Poly

set_option autoImplicit false

namespace Cb
open Prob

section Defs
variable {E : Type} [Field E]

/-- the name of the coefficient of X_l^(p+1) .., and of the constant -/
def hIx (E : Type) [Field E] (n : ℕ) : (k : ℕ) → Fin k → Fin n → HIdx (sVars E n k)
  | 0, l, _ => l.elim0
  | k + 1, l, p =>
    Fin.cases (motive := fun _ => HIdx (sVars E n (k + 1))) (.inl p)
      (fun l' => .inr (hIx E n k l' p)) l
def hCst (E : Type) [Field E] (n : ℕ) : (k : ℕ) → HIdx (sVars E n k)
  | 0 => ()
  | k + 1 => .inr (hCst E n k)

/-- The law of a packing, for tables with rows on the cube of the first h variables and columns J.
-/
def PackLaw (h g n : ℕ) {J : Type} [Fintype J]
    (pk : (HIdx (sVars E n (h + g)) → E) → (Fin h → Bool) × J → E)
    (Qw : (Fin (h + g) → E) → J → E) : Prop :=
  ∀ (W : HIdx (sVars E n (h + g)) → E) (γ : HPt (sVars E n (h + g))), hU (sVars E n (h + g)) W γ =
    ∑ j, Qw (sPt n (h + g) γ) j * foldV (fun i => sPt n (h + g) γ (Fin.castAdd g i)) (pk W) j

/-- The columns: (i, p - 2) for the first h variables; the coefficients of the last g variables; the
constant. -/
abbrev PCol (h g m : ℕ) : Type := (Fin h × Fin m) ⊕ ((Fin g × Fin (m + 1)) ⊕ Unit)

/-- the leading column: the first coefficient of the variable h + 1, or the constant if there is no
such variable -/
def pLead (g m : ℕ) : (Fin g × Fin (m + 1)) ⊕ Unit → Bool
  | .inl tp => decide (tp.1.val = 0 ∧ tp.2.val = 0)
  | .inr _ => decide (g = 0)

/-- the monomial X_i .. X_h at a corner of the cube -/
def pMon {h : ℕ} (i : Fin h) (β : Fin h → Bool) : E :=
  ∏ j : Fin h, if i ≤ j then (if β j then 1 else 0) else 1

/-- The table. -/
def pkC (h g m : ℕ) (W : HIdx (sVars E (m + 1) (h + g)) → E) :
    (Fin h → Bool) × PCol h g m → E := fun a =>
  match a.2 with
  | .inl iq => W (hIx E (m + 1) (h + g) (Fin.castAdd g iq.1) iq.2.succ) * pMon iq.1 a.1
  | .inr s =>
      (match s with
        | .inl tp => W (hIx E (m + 1) (h + g) (Fin.natAdd h tp.1) tp.2)
        | .inr _ => W (hCst E (m + 1) (h + g)))
      + if pLead g m s then ∑ i : Fin h, W (hIx E (m + 1) (h + g) (Fin.castAdd g i) 0) * pMon i a.1
      else 0

/-- The public weights. -/
def QwC (h g m : ℕ) (z : Fin (h + g) → E) : PCol h g m → E
  | .inl iq => z (Fin.castAdd g iq.1) ^ (iq.2.val + 1) * ∏ t : Fin g, z (Fin.natAdd h t)
  | .inr (.inl tp) =>
    z (Fin.natAdd h tp.1) ^ (tp.2.val + 1) * ∏ t : Fin g, if tp.1 < t then z (Fin.natAdd h t) else 1
  | .inr (.inr _) => 1

/-- a vector with coordinates Cl, laid into the coordinates J; 0 elsewhere -/
def placeV {Cl J : Type} [Fintype Cl] [DecidableEq J] (plc : Cl → J) (v : Cl → E) : J → E :=
  fun j => ∑ c, if plc c = j then v c else 0

/-- Padding: a packing with columns Cl, laid into the coordinates J. -/
def pkAt {Ix Rw Cl J : Type} [Fintype Cl] [DecidableEq J]
    (plc : Cl → J) (pk : (Ix → E) → Rw × Cl → E) : (Ix → E) → Rw × J → E :=
  fun W a => placeV plc (fun c => pk W (a.1, c)) a.2
def QwAt {Pt Cl J : Type} [Fintype Cl] [DecidableEq J] (plc : Cl → J) (Qw : Pt → Cl → E) :
    Pt → J → E :=
  fun z => placeV plc (Qw z)

/-- a point from a function of the variable: the inverse of sPt -/
def sUn (n : ℕ) : (k : ℕ) → (Fin k → E) → HPt (sVars E n k)
  | 0, _ => ()
  | k + 1, z => (z 0, sUn n k (Fin.tail z))

/-- The plain packing for h = 0: one row, the coefficients under their own names. -/
def pk0 (g n : ℕ) (W : HIdx (sVars E n (0 + g)) → E) :
    (Fin 0 → Bool) × HIdx (sVars E n (0 + g)) → E := fun a => W a.2
def Qw0 (g n : ℕ) (z : Fin (0 + g) → E) : HIdx (sVars E n (0 + g)) → E :=
  hSl (sVars E n (0 + g)) (sUn n (0 + g) z)

end Defs

namespace Spec
section
variable (E : Type) [Field E]

/-- The hiding polynomial, written out, for 1 ≤ n. -/
def ld_pack_formula : Prop :=
  ∀ (n k : ℕ), 1 ≤ n →
    ∀ (W : HIdx (sVars E n k) → E) (γ : HPt (sVars E n k)), hU (sVars E n k) W γ =
      ∑ l : Fin k, ∑ p : Fin n, W (hIx E n k l p) *
          (sPt n k γ l ^ (p.val + 1) * ∏ j : Fin k, if l < j then sPt n k γ j else 1) +
        W (hCst E n k)

/-- Every coefficient has exactly one name. -/
def ld_pack_names : Prop :=
  ∀ (n k : ℕ), Function.Bijective (fun a : (Fin k × Fin n) ⊕ Unit =>
    (Sum.elim (fun lp => hIx E n k lp.1 lp.2) (fun _ => hCst E n k) a : HIdx (sVars E n k)))

/-- The law of the block is the law of this file. -/
def ld_pack_ok_iff : Prop := ∀ (P : Type) (Y : SumPar E P), Y.PackOK ↔ PackLaw Y.h Y.g Y.n Y.pk Y.Qw

/-- The packing into 2^h rows meets the law. -/
def ld_pack_law : Prop := ∀ h g m : ℕ, PackLaw (E := E) h g (m + 1) (pkC h g m) (QwC h g m)

/-- `pkC` saves h columns. -/
def ld_pack_card : Prop := ∀ h g m : ℕ, Fintype.card (PCol h g m) + h = (h + g) * (m + 1) + 1

/-- Padding through an injection keeps the law. -/
def ld_pack_place : Prop :=
  ∀ (h g n : ℕ) (Cl J : Type) [Fintype Cl] [Fintype J] [DecidableEq J] (plc : Cl → J)
      (pk : (HIdx (sVars E n (h + g)) → E) → (Fin h → Bool) × Cl → E)
      (Qw : (Fin (h + g) → E) → Cl → E),
    Function.Injective plc → PackLaw h g n pk Qw → PackLaw h g n (pkAt plc pk) (QwAt plc Qw)

/-- The table is linear in the coefficients. -/
def ld_pack_lin : Prop :=
  ∀ (h g m : ℕ) (W W' : HIdx (sVars E (m + 1) (h + g)) → E) (c : E),
    pkC h g m (W + c • W') = pkC h g m W + c • pkC h g m W'

/-- The table determines the coefficients. -/
def ld_pack_inj : Prop := ∀ h g m : ℕ, Function.Injective (pkC (E := E) h g m)

/-- The degrees of the weights. -/
def ld_pack_deg : Prop :=
  ∀ (h g m : ℕ) (c : PCol h g m), Alg.DegLE
    (fun v : Fin (h + g) => if v.val < h then m else m + 1) (fun z => QwC (E := E) h g m z c)

/-- Padding keeps bounds on the degrees of the weights. -/
def ld_pack_deg_place : Prop :=
  ∀ (ι Cl J : Type) [DecidableEq ι] [Fintype Cl] [DecidableEq J] (plc : Cl → J)
      (Qw : (ι → E) → Cl → E) (d : ι → ℕ),
    (∀ c, Alg.DegLE d fun z => Qw z c) → ∀ j, Alg.DegLE d fun z => QwAt plc Qw z j

/-- The plain packing for h = 0. -/
def ld_pack0 : Prop := ∀ g n : ℕ, PackLaw (E := E) 0 g n (pk0 g n) (Qw0 g n)

end
end Spec
end Cb
