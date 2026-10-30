-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ListedWholeCutTop.lean: at the description of a whole file the verifier along lists on
the cut string (OnBytes/Maker/ListedWholeCut.lean, verifyWholeC) is the compiled verifier of one
slot (OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean, verifyOneProtocol) at the file's own wire record
(OnBytes/Maker/Wire.lean, wqWhole) and the cut string, as a tree of queries, FOR EVERY ARGUMENT
STRING AND EVERY TWO LISTS.

No soundness: a test. This module states nothing on soundness.

It joins verifyWholeL_eq (OnBytes/Maker/ListedWholeTop.lean), whose two premises speak of the string
and the lists, with listedOK_cutS and cutTo_ext_listed
(OnBytes/TypedOracleCompiler/Compile/Batch/ListedCutLaws.lean), which pay them at the cut string.

Main theorems.
  verifyWholeC_eq: the equation, under one premise on the file's rounds' wire records: PlacesOK.
  verifyWholeC_eq_ckP: at verifier's messages as hash blocks, under two premises on the rounds' data
    and K: no round needs more than K blocks; no round has more than 64 bits of work: those of
    wqWhole_okg_ckP (OnBytes/Maker/WireLaws.lean), from which PlacesOK is taken.

Limits. WHAT IS EQUAL TO verifyOneProtocol IS THE RUN ON THE CUT STRING, NOT ON π. The cut strikes openings:
so a string with an opening at a place that is not read, which verifyOneProtocol refuses by its strict
format, can pass after a cut by lists that leave that place out. A statement on all strings covers
the cut string too; a statement that the verifier refuses just what another program's strict format
refuses does not follow. The premises name neither
the string nor the lists; they are shown at no data here (PlacesOK at all data: placesOK_wiresOf,
OnBytes/Maker/ListedWholePlaces.lean). PlacesOK speaks of trees and leaves alone:
that it needs the two premises on blocks and work is not said: they are what the theorem at hand
asks. No oracle functions come in: the two sides are one tree of queries. Nothing on time or memory.
Nothing on soundness. The program does not import this file.


-/
import OnBytes.Maker.ListedWholeCut
import OnBytes.Maker.ListedWholeTop
import OnBytes.Maker.WireLaws
import OnBytes.TypedOracleCompiler.Compile.Batch.ListedCutLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (D : WholeD)
  {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3) {I X : Type} {L : BatchProtocolWithLeafBody I X} {Xi : Type}
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- **The verifier of a whole file along the lists on the cut string is the compiled verifier at the
file's wire record and the cut string**: for every argument string and every two lists. -/
theorem verifyWholeC_eq (sMT sFS : ℕ) (t : _root_.Compile.Tag)
    (embS : (p : OPos (chainsOf C D tF tJ t3).sh) → OSym (chainsOf C D tF tJ t3).sh p → Body L)
    (embP : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann →
      PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t))
    (xin : Xi → Option X) (embE : SgX → Body L) (depthReq : ℕ) (cms : List (Dig 256)) (x : Xi)
    (hW : PlacesOK (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann
      (wiresOf C K chal D tF tJ t3).sh)
    (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch) (own : Leaves)
    (listed : List (oneExternalString (2 ^ D.a) SgX).Pos) :
    verifyWholeC C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x π own
        listed =
      verifyOneProtocol sMT sFS t (wholeDesc C D tF tJ t3 silent run).batch
        (wqWhole C K chal D tF tJ t3 silent run) embS embP xin embE depthReq cms x
        (π.cutTo (wiresOf C K chal D tF tJ t3).sh (wlOne D.a) own listed) :=
  verifyWholeL_eq C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x
    (π.cutTo (wiresOf C K chal D tF tJ t3).sh (wlOne D.a) own listed) own listed
    (listedOK_cutS _ _ _ π.opens own hW)
    (cutTo_ext_listed π (wiresOf C K chal D tF tJ t3).sh (wlOne D.a) own listed)

end

/-- **The same at verifier's messages as hash blocks**, if no round needs more than K blocks or has
more than 64 bits of work. -/
theorem verifyWholeC_eq_ckP (f : Fmt.Fld) (K : ℕ) (D : WholeD) {TF TJ T3 : Type} (tF : TF)
    (tJ : TJ) (t3 : T3) {I X : Type} {L : BatchProtocolWithLeafBody I X} {Xi : Type}
    (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)
    (hK : ∀ d ∈ D.ds₁ ++ (D.ds₂ ++ D.ds₃), (bsRound f d.entry d.kind).b ≤ K)
    (hw : ∀ d ∈ D.ds₁ ++ (D.ds₂ ++ D.ds₃), d.entry.work ≤ 64)
    (sMT sFS : ℕ) (t : _root_.Compile.Tag)
    (embS : (p : OPos (chainsOf (ckP f) D tF tJ t3).sh) →
      OSym (chainsOf (ckP f) D tF tJ t3).sh p → Body L)
    (embP : PlainPart (chainsOf (ckP f) D tF tJ t3).sh (chainsOf (ckP f) D tF tJ t3).ann →
      PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t))
    (xin : Xi → Option X) (embE : SgX → Body L) (depthReq : ℕ) (cms : List (Dig 256)) (x : Xi)
    (π : OneProtocolProof 256 (wholeDesc (ckP f) D tF tJ t3 silent run).batch) (own : Leaves)
    (listed : List (oneExternalString (2 ^ D.a) SgX).Pos) :
    verifyWholeC (ckP f) K (chalP f K) D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq
        cms x π own listed =
      verifyOneProtocol sMT sFS t (wholeDesc (ckP f) D tF tJ t3 silent run).batch
        (wqWhole (ckP f) K (chalP f K) D tF tJ t3 silent run) embS embP xin embE depthReq cms x
        (π.cutTo (wiresOf (ckP f) K (chalP f K) D tF tJ t3).sh (wlOne D.a) own listed) :=
  verifyWholeC_eq (ckP f) K (chalP f K) D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq
    cms x (placesOK_of_okg _ _ _ (wqWhole_okg_ckP f K D tF tJ t3 silent run hK hw).sh) π own listed

end OnBytes.Maker

#print axioms OnBytes.Maker.verifyWholeC_eq
#print axioms OnBytes.Maker.verifyWholeC_eq_ckP
