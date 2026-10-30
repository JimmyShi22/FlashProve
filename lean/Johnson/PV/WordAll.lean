-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/WordAll.lean: the extractor's reading of a log of strings is the same through two members
  of the family of codings `mAll` (Johnson/PV/CutAll.lean), if their pages have one configuration's
  digest and one spelling of leaves, and one total code stands behind the escape.

The six digests of parameter bytes, the tests of fitness, both files' data and the entry's spelling
  may differ. Every step is a call: `agree_of_back` (OnBytes/K/Arm/AgreeTrees.lean),
  `sameTrees_of_agree` (Johnson/Top/SameTreesOf.lean), `extEnc_codings`
  (Johnson/TypedOracleCompiler/RecCompile/WordCodings.lean).
Limits: nothing on soundness.

-/
import Johnson.PV.CutAll
import Johnson.Top.SameTreesOf
import Johnson.TypedOracleCompiler.RecCompile.FrontRoot

set_option autoImplicit false

namespace OnBytes.K.Arm
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.PageOf
open OnBytes.Maker.Page
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

/-- At a leaf it writes what the page's spelling of leaves writes; at a vertex, the library's code
at the
page's digest. -/
theorem cutAll_leaf {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ} (C : BothCut L K) (q : LeafIn L) :
    cutAll C (.inl q) = C.P.leafX q := cutProof_leaf C.proof q

theorem cutAll_node {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ} (C : BothCut L K) (q : Bits × Bits) :
    cutAll C (.inr (.inl q)) = (pNode C.P.cfg).put q := cutProof_node C.proof q

variable {I X : Type} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
  (W : QueryLayout 256 (typedOracleCarrier L Bd aT aL))
  {C C' : BothCut (typedOracleCarrier L Bd aT aL) W.K} (H : BothLaws C) (H' : BothLaws C') {lL lL' : ℕ}
  (G : LinkLaws C lL) (G' : LinkLaws C' lL')
  (back : StrCode (AllPts 256 W.K (typedOracleCarrier L Bd aT aL)))

/-- **Two members of the family agree on the leaf and node oracles.** -/
theorem sameTrees_mAll (hX : C.P.leafX = C'.P.leafX) (hc : C.P.cfg = C'.P.cfg) :
    SameTrees W (mAll H G back) (mAll H' G' back) :=
  sameTrees_of_agree W _ _
    (agree_of_back (pageOf (cutAll C) (cutAll_one H G) (cutAll_hd H G) back)
      (pageOf (cutAll C') (cutAll_one H' G') (cutAll_hd H' G') back)
      (fun q => by
        show cutAll C (.inl q) = cutAll C' (.inl q)
        rw [cutAll_leaf, cutAll_leaf, hX])
      (fun q => by
        show cutAll C (.inr (.inl q)) = cutAll C' (.inr (.inl q))
        rw [cutAll_node, cutAll_node, hc]) rfl)

/-- **«word»: the index extractor reads one index off every log of strings through both.** -/
theorem word_mAll (hX : C.P.leafX = C'.P.leafX) (hc : C.P.cfg = C'.P.cfg) :
    (extractorOverOneHashFunction (mAll H G back) (indexExtractorAtRootAndOutOfDomainSample W)).Ei = (extractorOverOneHashFunction (mAll H' G' back) (indexExtractorAtRootAndOutOfDomainSample W)).Ei :=
        by
  funext k tr
  show L.decodeIndex (extEnc W (singleTr (mAll H G back) tr) k.cm) k.rcd =
    L.decodeIndex (extEnc W (singleTr (mAll H' G' back) tr) k.cm) k.rcd
  rw [extEnc_codings (by norm_num) (sameTrees_mAll W H H' G G' back hX hc) tr k.cm]

end OnBytes.K.Arm

#print axioms OnBytes.K.Arm.sameTrees_mAll
#print axioms OnBytes.K.Arm.word_mAll
