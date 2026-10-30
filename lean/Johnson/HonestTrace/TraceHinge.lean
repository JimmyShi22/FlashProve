-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/TraceHinge.lean

Two definitions in which statements on theTrace X i x (Johnson/HonestTrace/FullPlanes.lean) can be
carried to a trace that is given as a function of an index and an input.

Main definitions:
* "TraceHinge X trace instOf": wherever trace i ξ is there, instOf reads an instance x off ξ, the
  index i serves x (ServesAt X i x), and the trace is theTrace X i x. trace and instOf are
  parameters.
* "MidPAtReaders X cell entry x": Cb.Lkp.MidP at the 25 lookups of the calls (12 groups of layers,
  their 12 attention sub-proofs, the head), for all θ and al, with keys and bits read at fromG,
  fromA and fromH (Johnson/HonestTrace/FromCells.lean) of a reader of cells and a reader of the
  weights. It is the conclusion of midP_in_scope (Johnson/Goal/HonestTrace/FullPlanesInScope.lean)
  with fromG X cell entry g, fromA X cell g and fromH X cell entry in the stead of cellMW, cellZ and
  readH at the lists of theTrace.

Limits. Definitions alone: this file has no theorem. Nothing under Johnson/Goal/ is imported or
called here. TraceHinge goes one way: it does not say that a trace is there at any input, and the
function that never answers meets it. The lookups of the smallness tests' digits are not among the
25. All is at the full size: Instance ppref, 12 groups.

Not claimed: anything on a prover, on what a verifier accepts, or on a property of the protocol.

-/
import Johnson.HonestTrace.FromCells
import Johnson.HonestTrace.FullPlanes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model
open OnBytes.Road

/-- **Where the trace is there, it is theTrace at a served instance that is read off the input.**
trace: a trace as a function of an index and an input of any type Xi; instOf: a reader of an
instance off the input. One way alone: nothing says that a trace is there. Where
Johnson/Desc/ProofFile/Honest/AtPureFull.lean and AtPureFullLaw.lean of that folder lie: fullTrace
instOf Z meets it at X := Z.p.X (fullTrace_some) and is there at every served instance that instOf
reads (fullTrace_served). These two files are not imported and not called here. -/
def TraceHinge {Xi : Type} (X : Model.Verify.Public) (trace : Cm.Idx → Xi → Option Tr)
    (instOf : Xi → Option (Instance ppref)) : Prop :=
  ∀ i ξ ω, trace i ξ = some ω → ∃ x, instOf ξ = some x ∧ ServesAt X i x ∧ ω = theTrace X i x

/-- **MidP at all 25 lookups of the calls, at two readers and an instance**: for all θ and al of
Cb.Gl.E: at each group g below 12 of layers, at the attention sub-proof of each group g below 12 and
at the head, Cb.Lkp.MidP of the sub-proof's joint key vector, joint table, public padding and
planes' bits, with keys and bits read at fromG X cell entry g, fromA X cell g and fromH X cell
entry. The head's clause alone reads the instance x, through pubHAt X x. -/
def MidPAtReaders (X : Model.Verify.Public) (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F)
    (entry : ℕ → ℕ → Cb.Gl.F) (x : Instance ppref) : Prop :=
  ∀ θ al : Cb.Gl.E,
    (∀ g < 12, Cb.Lkp.MidP X.y.fo.v X.y.fo.d 5 32
      (Ends.G.keyG X.layers g (fromG X cell entry g) θ) (Ends.G.tabG X.layers θ)
      (FoNums.pads X.y.fo) (fun u j => Ends.G.bitsG X.y (fromG X cell entry g) (u * 32 + j)) al) ∧
    (∀ g < 12, Cb.Lkp.MidP (fsAt X g).v (fsAt X g).d 5 32
      (Ends.A.keyA (Hd.shapeA X g) (fsAt X g) (fromA X cell g) θ) (Ends.A.tabA (fsAt X g) θ)
      (FoNums.pads (fsAt X g))
      (fun u j => Ends.A.bitsA (Hd.shapeA X g) (fsAt X g) (fromA X cell g) (u * 32 + j)) al) ∧
    Cb.Lkp.MidP X.HLy.fs.v X.HLy.fs.d 5 32
      (Ends.H.keyH (pubHAt X x) (fromH X cell entry) θ) (Ends.H.tabH (pubHAt X x) θ)
      (FoNums.pads X.HLy.fs)
      (fun u j => Ends.H.bitsH X.hS X.HLy.fs (fromH X cell entry) (u * 32 + j)) al

end OnBytes.HonestTrace
