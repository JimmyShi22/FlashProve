-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/JoinNorms.lean: CONDITIONAL.

What is here. Two fields of the structure `FrontWorth` (Johnson/Road/K4/WorthGroups.lean), `rows`
and `norms`, from the shared hypotheses of Ground.lean: the tie of `rows_zero` (RowsZero.lean) and
`norms_zero'` (NormsZero.lean) to that structure. Statements and proofs.

  `rows_field`    the field rows.
  `norms_field`   the field norms.

Not shown here. That any world meets the hypotheses: no example is known. The squares' own claim is
a premise (hrow), and of group 2's three forms the third alone comes by a law (NormsZero.lean). The
other eight fields of FrontWorth.
No property is claimed.
-/
import Johnson.Road.K4.W.Ground
import Johnson.Road.K4.W.RowsZero
import Johnson.Road.K4.W.NormsZero
import Johnson.Road.K4.WorthGroups

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.W
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Pub Own)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell)
open OnBytes.Desc.First.K4 (rowsForms normsForms)

variable {K : Type} [Field K] {ρ : Reading K} {W : World K} {P : Pub} {o : Own} {c : Cells K}
  {t : Cell → K} [scl : Scl] {D : Dim} {low u lowV uV lowE uE : ℕ → K}

/-- **The field rows of FrontWorth.** -/
theorem rows_field (F : Fits ρ W o.v D c t low u)
    (T3 : TrueAt3 ρ W o.v D.lT c lowV uV (pt ρ o.H.PV) (pt ρ o.H.tV.r) lowE uE)
    (N : NormWords o.v D) (Z : K4Sizes P o.v o.H o.hd o.hd2 D) (O : Opened ρ W P o D t)
    (I : IdnHold D t) :
    ∀ x, rowsForms o.v o.H = some x → ∀ f ∈ x, f.value ρ W = 0 :=
  rows_zero F T3 N Z.NI I.jn O.sums O.prods O.ends8

/-- **The field norms of FrontWorth.** -/
theorem norms_field (F : Fits ρ W o.v D c t low u)
    (T3 : TrueAt3 ρ W o.v D.lT c (lowVOf ρ P o.v o.H) (uVOf ρ P o.v o.H) (pt ρ o.H.PV)
      (pt ρ o.H.tV.r) lowE uE)
    (Z : K4Sizes P o.v o.H o.hd o.hd2 D) (O : Opened ρ W P o D t)
    (hrow : o.H.wpl.row.value ρ W = 0) :
    ∀ x, normsForms P o.v o.H = some x → ∀ f ∈ x, f.value ρ W = 0 :=
  norms_zero' F Z.y T3 Z.NI Z.Pd Z.lsPd Z.NIle Z.blocks hrow O.sqR O.sqL

/-- The two statements have the two fields' types. -/
example (F : Fits ρ W o.v D c t low u)
    (T3 : TrueAt3 ρ W o.v D.lT c (lowVOf ρ P o.v o.H) (uVOf ρ P o.v o.H) (pt ρ o.H.PV)
      (pt ρ o.H.tV.r) lowE uE)
    (N : NormWords o.v D) (Z : K4Sizes P o.v o.H o.hd o.hd2 D) (O : Opened ρ W P o D t)
    (I : IdnHold D t) (hrow : o.H.wpl.row.value ρ W = 0) {g : ℕ} {sh : Array E}
    {pp : Aff × List Aff} (X : FrontWorth ρ W P g o sh pp) : FrontWorth ρ W P g o sh pp :=
  { X with rows := rows_field F T3 N Z O I, norms := norms_field F T3 Z O hrow }

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.rows_field
#print axioms OnBytes.Road.K4.W.norms_field
