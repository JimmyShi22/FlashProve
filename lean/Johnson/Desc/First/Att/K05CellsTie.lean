-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05CellsTie.lean: at the parameters beside the closed caller of the lookup on
an attention link's calls, the cells' tie (`K5Law.CellsTie`,
Johnson/Desc/First/Att/Claims/AgreeAll.lean) holds by definition at the matrices that are read off
the tuple of messages.

Definitions, statements and proofs.
Main names:
  `matsOfMsg x tl D rad m`: entry (matrix a, row r, column c) is the caller's own reading `msgAtt`
    of the tuple of messages m at the cell `enCell` x.ns tl a r c; it is 0 where there is no such
    cell. `Mats` K is ℕ → ℕ → ℕ → K (Johnson/Road/FormsKeysMat.lean), and `mAt` M (a, r, c) is M a r
    c at every address (Johnson/Road/Rows/AttRead.lean).
  `cell_att`: at every cell c, the message of the closed parameters at the place that `endLay` gives
    c is `cellsK` S (matsOfMsg x tl D rad m) c. The two sides are one term.
  `cellsTie_att`: `CellsTie` (oldOf S gL i) (matsOfMsg x tl D rad m) at the places of `endLay` with
    `cellAtt` and at the message of `closedOf` attBase attLin. It has no premise.
What it is worth. At this M the tie is a definition unfolded: by itself it says nothing.
`GatheredAllJ` (Johnson/Desc/First/Att/K05GatheredJ.lean) says "there are matrices M"; where M is
taken as matsOfMsg x tl D rad m, all that `GatheredAllJ` asks is still asked: it lies in `AttAt` at
that M (every table of the list is true of the cells that the caller reads off the messages) and in
"the forms are worth 0" at the one world.
Limits: nothing on `AttAt` is shown in this file or in what it imports. The record tl of `attBase`,
by which matsOfMsg finds a cell, and the tl that `GatheredAllJ` says there is are two letters: only
where the two are one are the cells of matsOfMsg those of the list of matrices that `AttAt` speaks
of. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05RowAtt
import Johnson.Desc.First.Att.K05GatheredJ

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open K5Law (oldOf CellsTie)
open VerifiableInference.Desc.First.Look (Sent attCaller attSg JAtt msgAtt enCell sigListCalls seatCalls)

section CellsTie
variable (x : VerifiableInference.Desc.First.Look.Place) (S : Attention.Shape) (tl : HTailF2) (D : Sent)
  (rad : OracleShape → Nat)

/-- **The matrices, read off the tuple of messages**: the caller's own reading at each cell. -/
noncomputable def matsOfMsg (m : (attSg x D rad).Msg) : OnBytes.Road.Mats Cb.Gl.E := fun a r c =>
  msgAtt D.codes (sigListCalls D rad x.link) (seatCalls D x.link) tl x.ns m (enCell x.ns tl a r c)

variable (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → Cb.Gl.E) (ns : ℕ) (N : Nums)

/-- At every cell the two readings are one term. -/
theorem cell_att (j0 : NameJ (attBase x S tl D rad).D S.ls S.cf.lmS) (m : (attSg x D rad).Msg) (c : AttSeg.Raw) :
    (closedOf (attBase x S tl D rad) (attLin x S tl D rad Ex Wp α ns N) ns N).msg m
        ((endLay (attBase x S tl D rad) (attLin x S tl D rad Ex Wp α ns N) ns N (cellAtt x S tl) S.ls S.cf.lmS j0).cellJ c) =
      OnBytes.Road.Rows.cellsK S (matsOfMsg x tl D rad m) c := rfl

/-- **The cells' tie holds at the matrices read off the message**: no premise. -/
theorem cellsTie_att (j0 : NameJ (attBase x S tl D rad).D S.ls S.cf.lmS) (m : (attSg x D rad).Msg)
    (gL : Forest.Heard) (i : Runs.In) :
    CellsTie (oldOf S gL i) (matsOfMsg x tl D rad m)
      (endLay (attBase x S tl D rad) (attLin x S tl D rad Ex Wp α ns N) ns N (cellAtt x S tl) S.ls S.cf.lmS j0).cellJ
      ((closedOf (attBase x S tl D rad) (attLin x S tl D rad Ex Wp α ns N) ns N).msg m) where
  row := fun _ _ r _ k _ => cell_att x S tl D rad Ex Wp α ns N j0 m (r.atPos k)
  long := fun _ _ r _ c _ i' _ => cell_att x S tl D rad Ex Wp α ns N j0 m ((r.addN c).atPos i')
  col := fun _ _ r _ k _ => cell_att x S tl D rad Ex Wp α ns N j0 m (r.addX k)

end CellsTie

end VerifiableInference.Desc.First.Att.P
