-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/ValueSlots.lean: the value of Johnson/Road/K4/Value.lean WITH ITS SEVENTEEN FIRST
SLOTS AS FORMULAS IN ONE NUMBER, the first free slot n0 in front of the own rounds, and the
library's sizes; and with the three orders the programs' (OnBytes/Tie/Pv/Lay/OrderE.lean).
Definitions.

  `Slots4`: the seventeen numbers. `slotsAt D n0 nT nI`: the formulas. A masked sumcheck over k
    variables of three coefficients and a further variable with dy + 1 takes 1 + 2 k + dy slots for
    its own coefficients, then its end values'; a token sumcheck one slot more in front, for its
    claimed sum. nT: the number of end values of the second token sumcheck; nI: of the batched one.
  `Plan4L E M X`: the letters that then stay. `Plan4L.plan : Plan4 E M X`. `Plan4L.full : FullPar E
    M X`.

Limits. THE FORMULAS ARE ARITHMETIC BY HAND FROM THE TEXTS' ORDER OF TAKING SLOTS (sums · squares
· products · their token sumcheck · the second token sumcheck · the batched sumcheck · two product
layers · the merge): THAT A HEARING OF K4's TEXT HOLDS JUST THESE NUMBERS IS NOT SHOWN HERE
(Johnson/Road/K4/SlotsTie.lean is meant to). For a sub-proof that is not the first (the first takes
one slot more in front of the merge). The range order wants at least 9 variables.
-/
import Johnson.Road.K4.Value
import OnBytes.Tie.Pv.Lay.OrderE

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop Prob Cb IOR Finset TWhole Johnson.L5.Layers Cb.Pv.Att Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl Tables)
open Inst.Model.Layout (units off)
open Inst.Model.FFSeg (Dim Cell LW layerR lDd lF lFe)

noncomputable section

/-- The seventeen first slots. -/
structure Slots4 where
  sW : ℕ
  fS : ℕ
  vS : ℕ
  sP : ℕ
  cP0 : ℕ
  fP : ℕ
  vP : ℕ
  cT0 : ℕ
  fT : ℕ
  vT : ℕ
  fI : ℕ
  vI : ℕ
  f5 : ℕ
  v5 : ℕ
  f6 : ℕ
  v6 : ℕ
  f7 : ℕ

/-- The formulas. -/
def slotsAt (D : Dim) (n0 nT nI : ℕ) : Slots4 :=
  let sW := n0
  let fS := sW + 9 * D.nNu
  let vS := fS + (1 + 2 * (D.lL + 1 + (lDd D + D.lT)) + 2)
  let sP := vS + 2
  let cP0 := sP + D.nNu * 7
  let fP := cP0 + 1
  let vP := fP + (1 + 2 * D.lT + 2)
  let cT0 := vP + 4 * D.nNu
  let fT := cT0 + 1
  let vT := fT + (1 + 2 * D.lT + 1)
  let fI := vT + nT
  let vI := fI + (1 + 2 * kS D + 2)
  let f5 := vI + nI
  let v5 := f5 + (1 + 2 * (D.lL + lF D + D.lT) + 2)
  let f6 := v5 + 2
  let v6 := f6 + (1 + 2 * (D.lL - 1 + (lFe D + D.lT)) + 2)
  let f7 := v6 + 2
  ⟨sW, fS, vS, sP, cP0, fP, vP, cT0, fT, vT, fI, vI, f5, v5, f6, v6, f7⟩

/-- The letters that then stay. -/
structure Plan4L (E : Type) [Field E] [Fintype E] [scl : Scl] (M X : Type) where
  D : Dim
  tb : Tables
  L0 : ℕ
  Jc : Type
  [finJc : Fintype Jc]
  [decJc : DecidableEq Jc]
  nameOf : Cell → Option Jc
  ns : ℕ
  kW : ℕ
  hW : ℕ
  nx : ℕ
  cellAt : M → Jc → E
  maskAt : M → ℕ → E
  matAt : M → ℕ → ℕ → E
  idxAt : M → ℕ → E
  two : (2 : E) ≠ 0
  zOf : X → ℕ → E
  kTg : X → E
  kIncS : X → ℕ → E
  /-- the first free slot in front of the own rounds; the numbers of end values -/
  n0 : ℕ
  nT : ℕ
  nI : ℕ
  /-- which entry of the index-mask message masks the merge's shown value -/
  v7 : ℕ
  numT : ShA D → ℕ
  numI : IA D ⊕ IB D → ℕ
  nW : ℕ
  num : Fin nW ≃ Piece D
  /-- the range order wants nine variables -/
  h5 : 9 ≤ D.lL + lF D + D.lT
  h6 : 9 ≤ D.lL - 1 + (lFe D + D.lT)
  hfe : D.fe ≤ D.f
  h0 : L0 % 2 = 0
  hf : D.f = 2 * D.fe
  hh : D.P.nq + D.P.nkv ≤ 64
  hLay : L0 + D.nl ≤ D.P.layers
  hH : off kW (units D.P) (units D.P).length ≤ hW

attribute [instance] Plan4L.finJc Plan4L.decJc

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type}

namespace Plan4L
variable (Q : Plan4L E M X)

/-- Its slots. -/
def slots : Slots4 := slotsAt Q.D Q.n0 Q.nT Q.nI

/-- The letters of Value.lean. -/
def plan : Plan4 E M X where
  D := Q.D
  tb := Q.tb
  L0 := Q.L0
  Jc := Q.Jc
  nameOf := Q.nameOf
  ns := Q.ns
  kW := Q.kW
  hW := Q.hW
  nx := Q.nx
  cellAt := Q.cellAt
  maskAt := Q.maskAt
  matAt := Q.matAt
  idxAt := Q.idxAt
  two := Q.two
  zOf := Q.zOf
  kTg := Q.kTg
  kIncS := Q.kIncS
  eS := OnBytes.Tie.Pv.Lay.eDefault _
  e5 := OnBytes.Tie.Pv.Lay.eRange _ Q.h5
  e6 := OnBytes.Tie.Pv.Lay.eRange _ Q.h6
  sW := Q.slots.sW
  fS := Q.slots.fS
  vS := Q.slots.vS
  sP := Q.slots.sP
  cP0 := Q.slots.cP0
  fP := Q.slots.fP
  vP := Q.slots.vP
  cT0 := Q.slots.cT0
  fT := Q.slots.fT
  vT := Q.slots.vT
  fI := Q.slots.fI
  vI := Q.slots.vI
  f5 := Q.slots.f5
  v5 := Q.slots.v5
  f6 := Q.slots.f6
  v6 := Q.slots.v6
  f7 := Q.slots.f7
  v7 := Q.v7
  numT := Q.numT
  numI := Q.numI
  nW := Q.nW
  num := Q.num
  hfe := Q.hfe
  h0 := Q.h0
  hf := Q.hf
  hh := Q.hh
  hLay := Q.hLay
  hH := Q.hH

/-- The value. -/
def full : FullPar E M X := Q.plan.full

end Plan4L
end
end OnBytes.Road.K4
