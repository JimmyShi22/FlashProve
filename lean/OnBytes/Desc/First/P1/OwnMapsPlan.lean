-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/P1/OwnMapsPlan.lean: the seven ties of OwnMaps.lean FROM THE CONDITION
that the chain's numbers are those of a record of sizes (OnBytes/Tie/Pv/Lay/OwnPlan.lean: `StgIs`,
`TailIs`). Definitions.

  `StgM.ofIs`: a stage whose variables all have degree 2 and are k in number, and k written rounds
    for them: the tie. The stage's formats are the library's by definition; `fmt_rep`
    (Cb/Pv/Lay/Shapes.lean) writes them as a list of equal members.
  `TailLens R x`: the seven sumchecks' written variables' rounds are as many as the record x says.
  `TailNums T`: a numbering of each sumcheck's end values.
  `TailM.ofIs`: the seven ties.

Limits. `TailIs` is a condition on the chain's letters: no value is built here. The numberings are
letters: which written end value is which typed one is compared with no text.
-/
import OnBytes.Desc.First.P1.OwnMaps
import OnBytes.Tie.Pv.Lay.OwnPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P1
open Iop Prob IOR Cb TWhole Cb.Pv.Lay Cb.Pv.Att Johnson.L5.Layers Johnson.L5.Door
open OnBytes.Flat OnBytes.Maker OnBytes.Slice

variable {M : Type}

/-- The tie of a stage whose numbers are n, k, dy, vals to k written rounds for its variables. -/
def StgM.ofIs {X : Type} {S : Stg GE M X} {n k dy vals : ℕ}
    (h : OnBytes.Tie.Pv.Lay.StgIs S n k dy vals) (r : ScR) (hk : r.vs.length = k)
    (num : S.L.T.par.A → ℕ) : StgM S r where
  DY := S.L.M.DY
  num := num
  hf := by
    show ldPartFmt GE S.L.S.k S.L.M.n ++ [pDummy GE S.L.M.DY] = _
    rw [show S.L.M.n = fun _ => 2 from funext h.hd, fmt_rep, hk, h.hk]

/-- The seven sumchecks' written variables' rounds are as many as the record says. -/
structure TailLens (R : TailR) (x : OnBytes.Params.LayerRounds) : Prop where
  l1 : R.r1.vs.length = x.lNI + x.lPd + x.lt
  l2 : R.r2.vs.length = x.lt
  l3 : R.r3.vs.length = x.lt
  l4 : R.r4.vs.length = x.lamS
  l5 : R.r5.vs.length = x.ll + x.lPf + x.lt
  l6 : R.r6.vs.length = x.ll - 1 + x.lfe + x.lt
  l7 : R.r7.vs.length = x.lkW

/-- A numbering of each sumcheck's end values. -/
structure TailNums {X : Type} (T : LayTail GE M X) where
  n1 : T.s1.L.T.par.A → ℕ
  n2 : T.s2.L.T.par.A → ℕ
  n3 : T.s3.L.T.par.A → ℕ
  n4 : T.s4.L.T.par.A → ℕ
  n5 : T.s5.L.T.par.A → ℕ
  n6 : T.s6.L.T.par.A → ℕ
  n7 : T.s7.L.T.par.A → ℕ

/-- **The seven ties, from the condition on the chain's numbers.** -/
def TailM.ofIs {X : Type} {T : LayTail GE M X} {x : OnBytes.Params.LayerRounds}
    (h : OnBytes.Tie.Pv.Lay.TailIs T x) {R : TailR} (hl : TailLens R x) (N : TailNums T) :
    TailM T R where
  w1 := StgM.ofIs h.s1 R.r1 hl.l1 N.n1
  w2 := StgM.ofIs h.s2 R.r2 hl.l2 N.n2
  w3 := StgM.ofIs h.s3 R.r3 hl.l3 N.n3
  w4 := StgM.ofIs h.s4 R.r4 hl.l4 N.n4
  w5 := StgM.ofIs h.s5 R.r5 hl.l5 N.n5
  w6 := StgM.ofIs h.s6 R.r6 hl.l6 N.n6
  w7 := StgM.ofIs h.s7 R.r7 hl.l7 N.n7

end OnBytes.Desc.First.P1
