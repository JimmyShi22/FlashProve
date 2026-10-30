-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/LibAtSeat.lean: THE RECORD OF LETTERS Same (Johnson/Desc/Kinds/Law/LibJoin.lean) AS A THEOREM AT THE SEAT's OWN LETTERS (Johnson/Stored/HeadSeatAt.lean: sizesOf h · parOf h work's policy · requestOf s), AGAINST THE LIBRARY's REQUEST Req.of (polOf h) x AT polOf | npOf (Johnson/Road/HeadLinkLPort.lean, HeadLines.lean); AND THE ROAD FROM WHAT K6's LAW CLOSES AT A RECORD
(Law/RowFront.lean: FrontIdn) TO THE LIBRARY's TWO CLAUSES IN THE VERY TERMS OF HeadR0 (Johnson/Road/Lane5SplitH.lean): STATED AND PROVED.
  same_at        FullH h (Johnson/Road/HeadPlace.lean: nine equations on the head's public numbers) · the record's two positions are the instance's (s.rowR = x.r, s.rowE = x.e) ⇒ Same (Req.of (polOf h) x) at the seat's letters (C | theta | cap: rfl against polOf).
  np_at          the normalisation's three numbers (Law/NormProof.lean: npOf) at sizesOf h ARE Hd.npOf h (rfl).
  front_to_lib   FrontIdn (parOf h work) (seatAt h iU3) s c ⇒ the 17 identities at Hd.npOf h and sB2 = 0 ∧ sB3 = 0 at Req.of (polOf h) x, over the base field, at (cellsN c).cast.
WHAT IT DOES NOT SAY. **s.rowR = x.r AND s.rowE = x.e ARE PREMISES**: that the request file's two words in the record are the instance's r and e is the frame's tie of the record to the instance: typed by nobody here. That cellsN c is what the committed integers of segment 24 spell: the reading of the witness's duty. FullH: the full size alone. Wide and More (the vocabulary without
padding · sh = 8 · the tables' cut · the checked tokens) are NOT paid here: these clauses do not read them. No chance in it.

-/
import Mathlib
import Johnson.Road.HeadLinkLPort
import Johnson.Desc.Kinds.Law.LibIdn

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open OnBytes (E)
open Inst.Model (ppref Instance)
open Inst.Model.Head (Req nT sB2 sB3)
open OnBytes.Road.Hd (FullH)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.HeadJoin (Same cellsN)
open Norm (lt ls d lPd S2 T)

/-- **Same at the seat's own letters.** -/
theorem same_at (h : OnBytes.Model.Head.Shape) (work : Nat) (s : S) (x : Instance ppref)
    (hF : FullH h) (hr : s.rowR = x.r) (he : s.rowE = x.e) :
    @Same (sizesOf h) (parOf h work).policy (requestOf s) (Req.of (OnBytes.Road.Hd.polOf h) x) :=
  @Same.mk (sizesOf h) (parOf h work).policy (requestOf s) _
    (by show 2 ^ h.lt = 1024; rw [hF.lt]) hr.symm he.symm rfl rfl rfl

/-- The normalisation's three numbers at the seat's sizes are Hd.npOf h. -/
theorem np_at (h : OnBytes.Model.Head.Shape) : @npOf (sizesOf h) = OnBytes.Road.Hd.npOf h := rfl

/-- **FROM WHAT K6's LAW CLOSES AT A RECORD TO THE LIBRARY's TWO CLAUSES, IN HeadR0's TERMS.** -/
theorem front_to_lib (h : OnBytes.Model.Head.Shape) (iU3 work : Nat) (s : S) (x : Instance ppref)
    (hF : FullH h) (hr : s.rowR = x.r) (he : s.rowE = x.e) (c : NCells)
    (hfront : FrontIdn (parOf h work) (seatAt h iU3) s c) :
    (∀ i < nT, ∀ k < 17,
      Inst.Model.Head.N.idn (OnBytes.Road.Hd.npOf h) ((cellsN c).cast Cb.Gl.F) i k = 0) ∧
      (sB2 ((cellsN c).cast Cb.Gl.F) (Req.of (OnBytes.Road.Hd.polOf h) x) = 0 ∧
        sB3 ((cellsN c).cast Cb.Gl.F) (Req.of (OnBytes.Road.Hd.polOf h) x) = 0) :=
  @lib_of_plain (sizesOf h) (parOf h work).policy (requestOf s) c _
    (same_at h work s x hF hr he) hF.d
    (idnPlain_of_front (parOf h work) (seatAt h iU3) s c hfront)

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.same_at
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.front_to_lib
