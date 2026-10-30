-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/FF/NoWrap.lean: no wrap-around in a feed-forward segment: the term, what the three
  statements say, and two facts at the reference sizes (`szR_ref`, `emb_abs`).

  No wrap-around: the field relation modulo p gives the integer program's steps
  (Inst/Model/Program.lean) over the integers. The field relation (`TraceSpec.RF`,
  Blocks/Segment.lean, at `trace`, Inst/Model/FF/Trace.lean) says of an integer trace: every cell is
  small, every looked-up value is an entry of its table, every identity holds.

  The statements `noWrap1K`, `noWrap2K`, `noWrap3K` (Cm/TargetInstFFK.lean), at the reference sizes
  (`Dim.ref`): let p be a prime with `Big p` (Inst/Model/Bound/Base.lean), let the scales of every
  layer be valid (`LawfulW`), assume the setting (`SettingK`: tables with the ranges of (Tab)
  (`Tables.OK`, Inst/Model/Tables.lean), a well-formed matrix W, a segment of four layers that
  starts at an even layer, tokens in the vocabulary), and let a trace t satisfy the field relation
  over `ZMod p` with W. Then, for every layer ℓ of the segment:
   1  `Part1`: what the relation gives without a fact from another segment: both normalisations,
      with their intermediate values and range conditions; the projections; on all hidden units the
      steps (U2) to (U4) as functions of gw, and the range conditions of (U2) and (U5); on the units
      that are not routed, (U1) and (U5); and the bound (FL14) on the two states of the stream that
      are normalised;
   2  if (FA12) holds (`OBound`: |o[j]| ≤ 2,047), a fact of the attention segment: `Part2`, that is
      (PL7): x_(2ℓ+1) is the value that the output projection computes from x_(2ℓ) and o;
   3  if (FL19) holds (`LastBound`: |x_8[j]| < 2^39), a fact of the next feed-forward segment or of
      the head: `Part3`, the feed-forward block: the router and the input of the routed expert in a
      layer with experts; no range condition of (PL8) to (PL13) fails; x_(2ℓ+2) is the integer
      model's; and in the first segment (PL1): the stream at the index 0 is the embedding of the
      prompt.
  `part1`, `part2`, `part3` (Cm/TargetInstFFAll.lean): `Part1`, `Part2`, `Part3` from `RFraw`
  (Inst/Model/FF/Cast.lean), at a number p with `Big p`, for all sizes D that meet the size
  conditions: `AdmN` (normalisations), `AdmP` (projections), `AdmS` (stream), `SzR` (units, router),
  with `OBound` for `part2` and `LastBound` for `part3`, for l < D.nl. The steps are proved in
  Inst/Model/FF/NoWrapNorm.lean, Inst/Model/FF/NoWrapProj.lean, Inst/Model/FF/NoWrapStream.lean
  (residual additions, (PL12)), Cm/TargetInstFFUnit.lean and Cm/TargetInstFFRouter.lean (also the
  embedding), from the lemmas of Inst/Model/Common/.
  Labels such as (PL7) and (FA12) link one docstring to another; (PL..), (U..) stand at the steps of
  the integer program (Inst/Model/Program.lean); x_s, o, gw: Inst/Model/FF/Trace.lean.

  Scales: the instance argument `[scl : Scl]` (Inst/Model/Scl.lean, Inst/Model/FF/Index.lean). A
  theorem marked "omit scl in" reads no scale.
-/
import Inst.Model.FF.NoWrapRouter
import Inst.Model.FF.NoWrapStream
import Inst.Model.FF.NoWrapProj
import Inst.Model.FF.NoWrapRef

set_option autoImplicit false

/- The default instance `Scl.ref` (the reference scales) is switched off in this file: whatever
reads scales takes `[scl : Scl]`. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Inst.Model.FFSeg

variable [scl : Scl]

open Finset

namespace NWA
open NWR (SzR WFabs)

theorem szR_ref [Lawful] : SzR Dim.ref :=
  { kg := fun l => (Lawful.all l).rg.2, kg' := fun l => (Lawful.all l).rg'.2,
    ku := fun l => (Lawful.all l).ru.2, ku' := fun l => (Lawful.all l).ru'.2, d := by decide,
    kr := fun l => (Lawful.all l).ranges.kr, nx := rfl, f2 := by decide }

omit scl in
/-- for a well-formed W (`Layout.WFW`, reference parameters), every entry of the embedding read from
W is at most 2,155,905,152 in absolute value, the bound of four signed bytes -/
theorem emb_abs {W : Mat} (hW : Layout.WFW ppref Layout.kRef W Layout.hRef) (a b : ℕ) :
    |(Layout.weightsOf ppref Layout.kRef W).Emb a b| ≤ 2155905152 := by
  have h2 : if a < ppref.V ∧ b < ppref.d then
      -2155905152 ≤ (Layout.weightsOf ppref Layout.kRef W).Emb a b ∧
      (Layout.weightsOf ppref Layout.kRef W).Emb a b ≤ 2139062143
    else
      (Layout.weightsOf ppref Layout.kRef W).Emb a b = 0 := (Layout.Bridge.indexOf W hW).2.2.1 a b
  rw [abs_le]
  split_ifs at h2
  · constructor <;> omega
  · rw [h2]
    norm_num

end NWA

end Inst.Model.FFSeg
