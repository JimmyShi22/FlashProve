-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/Tail/ClaimsT.lean: the claims of the smallness test at reads that are given by tables: the
reads that stand for a segment of a table, and no others.

Cb/Pv/Tail/Tables.lean numbers the reads of a matrix so that some numbers stand for no segment of a
table: such a read has weights 0 and value 0. The list of claims (Cb/Pv/Tail/Claims.lean) leaves
them out here.

Main names:
  `keepT`: the read stands for a segment of a table. `keepT_false`: if not, its weights and values
    are 0.
  `relOut_iffT`: the relation after the round says: the digits are in their tables, every tie holds,
    and every read that stands for a segment of a table holds.
  `qOf`: the number of a kept read among all kept reads: matrix by matrix, within a matrix table by
    table in the order of the list, within a table segment by segment.
  `PExp`, `PExp.exps`: exponents of the form: a tie: plan + eqFirst μ + i' * step + u; a read:
    plan + eqFirst NM + q * step + u.

Limits: `qOf` and `PExp.exps` are definitions. Nothing here says that these exponents differ from
each other, or compares them with a program's.

Terms: lean/GLOSSARY.md.
-/
import Cb.Pv.Tail.Claims
import Cb.Pv.Tail.Tables

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tail
open TWhole

variable {K : Type} [Field K] {t : TSize} (Θ : TLetters K t)

/-- The read stands for a segment of a table. -/
def keepT (t : TSize) (μ : Fin t.size.NM) (r : Fin (t.size.nr μ)) : Bool := (t.dec μ r).isSome

theorem keepT_false {x : Θ.X} {msg : Θ.M} (μ : Fin t.size.NM) (r : Fin (t.size.nr μ))
    (h : keepT t μ r = false) :
    (∀ i, Θ.letters.w x μ r i = 0) ∧ ∀ c, Θ.letters.tab msg μ r c = 0 := by
  have hd : t.dec μ r = none := Option.isSome_eq_false_iff.1 h |> Option.isNone_iff_eq_none.1
  exact ⟨fun i => by
      show wOf t (Θ.phi x) μ r i = 0
      unfold wOf
      rw [hd],
    fun c => by
      show tabOf t (Θ.u3 msg) μ r c = 0
      unfold tabOf
      rw [hd]⟩

/-- The relation after the round, with the reads of the tables alone. -/
theorem relOut_iffT (e : Exps t.size) (x : Θ.X) (β : Dr t.size) (msg : Θ.M) (Z : Dig K t.size) :
    relOut Θ.letters x β msg Z ↔
      (∀ μ u i, Cb.Rng.InTab t.size.lo (Z.zl μ u i) ∧ Cb.Rng.InTab t.size.hi (Z.zh μ u i)) ∧
        (cl Θ.letters e (keepT t) (x, β)).Holds (vals Θ.letters msg Z) :=
  relOut_iff Θ.letters e (keepT t) x β msg Z fun μ r h => keepT_false Θ μ r h

/-- the kept reads of matrix μ with a number below r -/
def qIn (t : TSize) (μ r : ℕ) : ℕ := ((List.range r).filter fun r' => (t.dec μ r').isSome).length

/-- The number of a kept read among all kept reads. -/
def qOf (t : TSize) (μ r : ℕ) : ℕ :=
  (∑ ν ∈ Finset.range μ, qIn t ν (t.tabs.length * (t.m ν + 1))) + qIn t μ r

/-- The numbers from which exponents are made. -/
structure PExp where
  plan : ℕ
  step : ℕ
  eqFirst : ℕ → ℕ

/-- The exponents. -/
def PExp.exps (p : PExp) (t : TSize) : Exps t.size :=
  ⟨fun μ u i' => p.plan + p.eqFirst μ + i' * p.step + u,
    fun μ u r => p.plan + p.eqFirst t.NM + qOf t μ r * p.step + u⟩

end Cb.Pv.Tail

#print axioms Cb.Pv.Tail.keepT_false
#print axioms Cb.Pv.Tail.relOut_iffT
