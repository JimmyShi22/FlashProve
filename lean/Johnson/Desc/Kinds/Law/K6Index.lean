-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6Index.lean: **THE LAST LETTER OF Law/K6Own24.lean's READING THAT NO PREMISE
READ, wh (from the stored table's cells to the output matrix's weights), FILLED BY THE LIBRARY's OWN
READER**: the stored table's cells are a matrix of field elements (the table of joints' own filling
of the witness's component "cells"); whOf M := the output matrix H that the library's layout reads
(Inst/Model/Layout.lean: weightsOf ppref kRef) in THE INDEX
THAT THE MATRIX HOLDS (Johnson/Flat/LedgerClaim.lean: indexOf; Holds M i: every entry of M is the
cast of the index's digit; a matrix holds at most one index: holds_unique); the zero matrix where M
holds none. SO THE PREMISE "c.Wh IS THE OUTPUT MATRIX IN Wz" OF Law/K06Means.lean's ASSEMBLY BECOMES
"THE STORED TABLE's CELLS HOLD THE INDEX i", with Wz := i.mat: the very premise under which the
table's filling of "constr" speaks (constrQ: "at every index that the decoded matrix
holds"): STATED AND PROVED.
  (IN Law/WhOf.lean, imported:) whOf · whOf_holds : rows ≤ hRef → cols ≤ 2 ^ kRef → Holds M i → whOf
      M = (weightsOf ppref kRef
      i.mat).H.
  compIx comp24 at whOf. k6OwnIx Law/K6Own24.lean's call at it: NO ∀-LETTER OF THE READING IS LEFT
      THAT NO PREMISE READS.
  k06_whole_ix the assembly at one record: … ∧ Holds w.cells i ⇒ Policy.HeadCl (Hd.npOf
      Wp.hS) (polOf Wp.hS) i.mat x (Hd.cellsH Wp.hS Wp.HLy (borderOf Wp.y) (ownQ … w 24)).
THE LETTERS. Under "there is": none of this file's own (indexOf chooses among the indices that M
holds: at most one, by holds_unique, under the two bounds on rows and cols). ∀-letters
that no premise reads: G (the frame's description of the files). rows | cols: read by the two bounds
in k06_whole_ix; in k6OwnIx by nothing: the law does not spend them.
WHAT IT DOES NOT SAY. WHERE THE CELLS HOLD NO INDEX whOf IS 0, IN SILENCE: K6's law holds there too
and says little. That the decoder's matrix holds an index is the key file's side (the table's
"decodes" and the claims' "in range"). All that Law/K6Own24.lean does not say: s | seat | N | arr |
ms | msR | nM | pl tied to no plan; four public conditions that have run at no plan; the piece's
premises; NO MEMBER. No
chance in it beyond p.Own's own.
OVERTAKEN AS A TOP: k6OwnIx AND k6OwnIxBy ARE OVERTAKEN BY Law/K6Cut.lean's k6OwnCut | k6OwnCutBy:
here the sizes s, the mask row's length nM and the pinned list ms are still free letters beside Wp,
and SeatsNamed is asked at every segment: three finds of a reader stand open in them; nobody calls
them as tops; what lives of this file are its definitions and the assemblies at one record.
GENERAL IN THE BLOCK: k6OwnIxBy: the call for any block b6, of any type of claims, that meets
Law/K6Steps.lean's record K6Steps Wp b6 on after: p.Own (on) (after) ...; k6OwnIx, with its
statement as it was, is its instance at blockOf, K6On and K6After.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.WhOf
import Johnson.Desc.Kinds.Law.K6Own24

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open Inst.Model.Layout (kRef hRef)
open VerifiableInference.OnPublicFiles.Flat (GE Holds indexOf indexOf_eq)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.Sound (Piece Frame Sending Mem MsgT Fenced SmpStays ErrBears kitK
    kitFs
  SeatsNamed namedOnce)

variable {rows cols : Nat} (cs : OnBytes.Codes) {Tok : Type} (arr : Nat → Nat → Nat)
  (ms msR : List Mem) (N : Numbers) (s : Nat → Cb.Pv.Tail.Size)
  (seat : ∀ k, Fin (s k).NM → Nat → Nat → Nat × Nat × Nat) (Wp : OnBytes.Model.Verify.Public)
  (nM : Nat) (pl : Nat → Nat × Bool × Nat × Nat)

/-- **The components that K6's rule reads, off the table's witness, with no letter for the
weights.** -/
def compIx : Wit (Fin rows → Fin cols → GE) Tok MsgT → Pinned :=
  comp24 cs arr msR N s seat Wp whOf nM pl

namespace Came

/-- **THE CALL, WITH NO LETTER OF THE READING THAT NO PREMISE READS.** -/
theorem k6OwnIxBy {Xi : Type} (G : FileDescription Xi)
    (smp : S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (decT : (Nat → Option (Nat × List UInt64)) → S → Option (Fin rows → Fin cols → GE))
    (fld : Fmt.Fld) (Fr : Frame)
    {Cl : Type} (p : Piece (_root_.Run.ckP fld) Fr S Cl (Wit (Fin rows → Fin cols → GE) Tok MsgT))
    (b6 : Block S Cl) {on after : S → Prop}
    (hst : K6Steps Wp b6 on after) (hpb : p.b = Sound.below b6)
    (hback : p.back = []) (hext : ∀ a τ w, p.ext a τ w = w) (hN : SeatsNamed arr N s seat)
    (hI : SeatsIn cs arr ms msR N s seat 24)
    (hn : ∀ j, j < nM → namedOnce arr N 24 (pl j).1 = true)
    (hin : ∀ j, j < nM →
      InCopy cs arr ms msR N 24 (pl j).1 (pl j).2.1 (pl j).2.2.1 (pl j).2.2.2)
    (hF : Fenced p.base ms) (hS : SmpStays cs smp p ms) (hD : DecTStays decT p)
    (hlog : ∀ d, d ∈ toRDs p.ds → d.entry.logN ≤ 64)
    (hErr : ErrBears (_root_.Run.ckP fld)
      (fun j => kitK (toRDs p.ds) j *
        (priceAt (parOf Wp.hS (workOf Wp)) j * kitFs fld (toRDs p.ds) j)) (toRDs p.ds) 0 p.err) :
    p.Own (fun a => on a.1) (fun b => after b.1)
      (meansW cs G arr smp decT ms (compIx cs arr msR N s seat Wp nM pl) (base24 cs arr msR N s
          seat)
        Wp Fr) InK6 OutK6 :=
  k6Own24By cs arr ms msR N s seat Wp whOf nM pl G smp decT fld Fr p b6 hst hpb hback hext hN hI hn
      hin hF hS
    hD hlog hErr

/-- The same at the block at the unit type, under K6On, with K6After behind.
    -/
theorem k6OwnIx {Xi : Type} (G : FileDescription Xi)
    (smp : S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (decT : (Nat → Option (Nat × List UInt64)) → S → Option (Fin rows → Fin cols → GE))
    (fld : Fmt.Fld) (Fr : Frame)
    (p : Piece (_root_.Run.ckP fld) Fr S Unit (Wit (Fin rows → Fin cols → GE) Tok MsgT))
    (b6 : Block S Unit) (hb6 : blockOf Wp 24 = some b6) (hpb : p.b = Sound.below b6)
    (hback : p.back = []) (hext : ∀ a τ w, p.ext a τ w = w) (hN : SeatsNamed arr N s seat)
    (hI : SeatsIn cs arr ms msR N s seat 24)
    (hn : ∀ j, j < nM → namedOnce arr N 24 (pl j).1 = true)
    (hin : ∀ j, j < nM →
      InCopy cs arr ms msR N 24 (pl j).1 (pl j).2.1 (pl j).2.2.1 (pl j).2.2.2)
    (hF : Fenced p.base ms) (hS : SmpStays cs smp p ms) (hD : DecTStays decT p)
    (hlog : ∀ d, d ∈ toRDs p.ds → d.entry.logN ≤ 64)
    (hErr : ErrBears (_root_.Run.ckP fld)
      (fun j => kitK (toRDs p.ds) j *
        (priceAt (parOf Wp.hS (workOf Wp)) j * kitFs fld (toRDs p.ds) j)) (toRDs p.ds) 0 p.err) :
    p.Own (fun a => K6On Wp a.1) (fun b => K6After Wp b.1)
      (meansW cs G arr smp decT ms (compIx cs arr msR N s seat Wp nM pl) (base24 cs arr msR N s
          seat)
        Wp Fr) InK6 OutK6 :=
  k6OwnIxBy cs arr ms msR N s seat Wp nM pl G smp decT fld Fr p b6
    ((k6Steps_blockOf Wp 24 b6 hb6).weaken fun _ h => h.1) hpb hback hext hN hI hn hin hF hS hD hlog
        hErr

/-- **THE ASSEMBLY AT ONE RECORD, AT THE INDEX THAT THE STORED TABLE's CELLS HOLD.** -/
theorem k06_whole_ix (hr0 : rows ≤ hRef) (hc0 : cols ≤ 2 ^ kRef) (s0 : S) (y : Nat)
    (x : Inst.Model.Instance Inst.Model.ppref) (i : Cm.Idx) (tab : Nat → Nat)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (hon : K6On Wp s0)
    (hin : K6In Wp s0 (compIx cs arr msR N s seat Wp nM pl w))
    (hy : Reply.token (seatAt Wp.hS (readsOf Wp)).toSeat s0 = some y)
    (hlook : LookCallsAt Wp tab s0 y (compIx cs arr msR N s seat Wp nM pl w).1)
    (hrider : RiderAt Wp s0 y (compIx cs arr msR N s seat Wp nM pl w).1)
    (hsmall : ∀ m f t, ((compIx cs arr msR N s seat Wp nM pl w).1.cell m f t).natAbs < 2 ^ 18)
    (hsmallS : ∀ f t, ((compIx cs arr msR N s seat Wp nM pl w).1.stream f t).natAbs < 2 ^ 18)
    (hF : OnBytes.Road.Hd.FullH Wp.hS) (h8 : Wp.hS.digSh = 8) (hr : s0.rowR = x.r)
    (he : s0.rowE = x.e) (htok : ∀ t, t < 1024 → s0.tokv.getD t 0 = x.tok t) (hyx : y = x.y.val)
    (htab : ∀ u, u < 2 ^ 16 → (tab u : Int) = Inst.Model.EX u) (hH : Holds w.cells i) :
    _root_.Policy.HeadCl (OnBytes.Road.Hd.npOf Wp.hS) (OnBytes.Road.Hd.polOf Wp.hS) i.mat x
      (OnBytes.Road.Hd.cellsH Wp.hS Wp.HLy (OnBytes.Model.Verify.borderOf Wp.y)
        (P5J.ownQ cs arr msR N s seat w 24)) := by
  unfold compIx at hin hlook hrider hsmall hsmallS
  exact k06_whole_24 cs arr msR N s seat Wp whOf nM pl s0 y x i.mat tab w hon hin hy hlook hrider
      hsmall
    hsmallS hF h8 hr he htok hyx htab (whOf_holds hr0 hc0 hH)

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.k6OwnIxBy
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.k6OwnIx
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.k06_whole_ix
#check @VerifiableInference.Desc.Kinds.Head.Law.Came.k6OwnIx
#check @VerifiableInference.Desc.Kinds.Head.Law.Came.k06_whole_ix
