-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Print/FitsOfRuns.lean: FROM THE COMPILED PROVER's THREE EQUATIONS (the key file's,
the copy's file's, the proof file's run, each at its written letters) TO Fits
(Johnson/Prover/Print/FormBack.lean): all that the form's way back asks of the nine typed parts.

Main names.
  RunsOwe      ONE RECORD OF ALL NAMED PREMISES: on the three byte coins (CoinsPrint twice; the
    entry's lengths at a binding shape of depth 0) · on the wire records (FewJ, Few0 and the laws:
    premises of the prover's own theorem) · numbers (caps, depths, widths below 2^64) · on what the
    prover does not make (WholeOwes twice, EntryOwes) · the key file's front bears the key's
    OOD answers and the copy's number 0; the proof file's front bears the copy's number.
  fits_of_runs THE END.

By: whole_prints (OnBytes/Prover/Print/Owed.lean), twice · entry_prints
(Johnson/Prover/Print/OwedEntry.lean) · publicL_full (Johnson/Prover/Print/EntryAtFull.lean).

How it is met with the prover of a whole request: its three runs are the compiled prover at the
verifiers' letters; that these are the written letters is proveTA_fullD, proveLA_fullD,
proveBA_fullD (Johnson/Prover/At/WiresAt.lean), by unfolding.

HANDED THROUGH UNTOUCHED, from RunsOwe into Fits or into Printable and Canon: c32 · ansT · copyT ·
copyB · both "again" · the fronts' answers, their number and the copy's number · the words of plain
parts and of opened columns · at the outer trees: the stored columns' words and lengths. PREMISES
THAT ARE SPENT: that the strategy has sent the coins' run2 and run3 (so the string's second and
third run values are the coins' by premise). PROVED of the prover's value: own leaves' salts' starts
and lengths · the number of roots · the binding tree's fields · nonces · paths' lengths · own
columns' widths · that the string's first run value is the coins' run1.

Not shown here: that RunsOwe is met. Of its clauses ansT, copyT and both "again" follow where the
interactive verifiers accept (OnBytes/Prover/Print/Answers.lean). Nothing on acceptance, soundness
or completeness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Print.FormBack
import Johnson.Prover.Print.OwedEntry
import OnBytes.Prover.Print.Owed
import OnBytes.Flat.TableNumbers
import Run.CodingPage160

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Print

open VerifierAndGoals FlashProve Rom
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open _root_.Run
open _root_.Compile (Tag)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch
open TypedOracleCompiler.Joined (pls₁ pls₂ pls₃ FewJ Few0)
open Compile.Joined (Chains)
open LPFD.Full (XF sBG sTG)
open PV.EntryFive (dsF xsF)
open Johnson.RunOne.StrictW (wqW)
open OnBytes.Prover OnBytes.Prover.Print

variable {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk) {I X' : Type} (L : BatchProtocolWithLeafBody I X') (K : ℕ)

/-- The key file's wire at S, and the proof file's, and the copy's file's. -/
abbrev wT := wqWhole (ckP .two) K (chalP .two K) (S.DK.at frS.P.T.a) (front₀ S.G.rec₀)
  (join₀ S.G.rec₀) ByteArray.empty silK S.runK
abbrev wB := wqWhole (ckP .two) K (chalP .two K) (S.DP.at frS.P.T.a) (front₀ S.G.z₀.2)
  (join₀ S.G.z₀.2) ByteArray.empty silP S.runP
abbrev wL := wqW (ckP .two) dsF frS.P.T.a xsF S.dec K (chalP .two K)

/-- the numbers of the joining round and of the seam -/
abbrev GT := chainsOf (ckP .two) (S.DK.at frS.P.T.a) (front₀ S.G.rec₀) (join₀ S.G.rec₀)
  ByteArray.empty
abbrev GB := chainsOf (ckP .two) (S.DP.at frS.P.T.a) (front₀ S.G.z₀.2) (join₀ S.G.z₀.2)
  ByteArray.empty

variable {L} {K}

/-- **All named premises, in one record.** c: the configuration's digest, as bytes; salt: the bytes
of a leaf's own salt; sL: a binding shape of depth 0 for the copy's file's coins. -/
structure RunsOwe (c : ByteArray) (salt : ℕ) (sL : OnBytes.Params.LinBindingShape)
    (bcT bcL bcB : ByteCoins L) (capT capL capB : ℕ → ℕ) (xB : XF)
    (yT : (oneExternalString (2 ^ (S.DK.at frS.P.T.a).a) PQ.SgX).Str) (yL : (twoExternalStrings (2 ^ frS.P.T.a) PQ.SgX).Str)
    (yB : (oneExternalString (2 ^ (S.DP.at frS.P.T.a).a) PQ.SgX).Str) (xtT xtL xtB : ℕ → TreeK 256 L)
    (q : Typed S) (τT : Tr (QT S).loc.shape) (τL : Tr (QL S).loc.shape)
    (τB : Tr (QB S).loc.shape) : Prop where
  c32 : c.size = 32
  -- the coins
  coT : CoinsPrint bcT salt (sTG S.G)
  coB : CoinsPrint bcB salt (sBG S.G)
  coL : bcL.Fit salt sL
  depthL : sL.logLeaves = 0
  -- the wire records: premises of the prover's own theorem
  fewJT : FewJ (QT S).loc.shape (QT S).ann (wT S K).sh
  few0T : Few0 (QT S).loc.shape (QT S).ann (wT S K).sh
  okT : (wT S K).OKG
  fewJB : FewJ (QB S).loc.shape (QB S).ann (wB S K).sh
  few0B : Few0 (QB S).loc.shape (QB S).ann (wB S K).sh
  okB : (wB S K).OKG
  okL : (wL S K).OKG
  -- numbers
  capT : ∀ i, capT i < 2 ^ 64
  capL : ∀ i, capL i < 2 ^ 64
  capB : ∀ i, capB i < 2 ^ 64
  depT : maxDepthW (S.DK.at frS.P.T.a) < 2 ^ 64
  depB : maxDepthW (S.DP.at frS.P.T.a) < 2 ^ 64
  depL : (wL S K).maxDepth < 2 ^ 64
  widT : ∀ d ∈ (S.DK.at frS.P.T.a).ds₁ ++ ((S.DK.at frS.P.T.a).ds₂ ++ (S.DK.at frS.P.T.a).ds₃),
    ∀ u ∈ d.trees, u.W < 2 ^ 64
  widB : ∀ d ∈ (S.DP.at frS.P.T.a).ds₁ ++ ((S.DP.at frS.P.T.a).ds₂ ++ (S.DP.at frS.P.T.a).ds₃),
    ∀ u ∈ d.trees, u.W < 2 ^ 64
  -- what the prover does not make
  oweT : WholeOwes (ckP .two) (S.DK.at frS.P.T.a) (front₀ S.G.rec₀) (join₀ S.G.rec₀)
    ByteArray.empty silK S.runK q.rcd yT xtT bcT c q.piT τT
  oweB : WholeOwes (ckP .two) (S.DP.at frS.P.T.a) (front₀ S.G.z₀.2) (join₀ S.G.z₀.2)
    ByteArray.empty silP S.runP (xB, q.rcd') yB xtB bcB c q.piB τB
  oweL : EntryOwes (ckP .two) dsF frS.P.T.a xsF S.dec (q.rcd, q.rcd') yL xtL c τL
  -- the fronts
  ansT : (pls₁ (wholeDesc (ckP .two) (S.DK.at frS.P.T.a) (front₀ S.G.rec₀) (join₀ S.G.rec₀)
    ByteArray.empty silK S.runK) q.piT).1.answers = (trAns q.rcd.2).map OnBytes.E.ofTriple
  copyT : (pls₁ (wholeDesc (ckP .two) (S.DK.at frS.P.T.a) (front₀ S.G.rec₀) (join₀ S.G.rec₀)
    ByteArray.empty silK S.runK) q.piT).1.copy = 0
  copyB : (pls₁ (wholeDesc (ckP .two) (S.DP.at frS.P.T.a) (front₀ S.G.z₀.2) (join₀ S.G.z₀.2)
    ByteArray.empty silP S.runP) q.piB).1.copy = q.copy

variable (L) (K)

/-- **FROM THE THREE RUNS TO Fits.** -/
theorem fits_of_runs (c : ByteArray) (salt : ℕ) (sL : OnBytes.Params.LinBindingShape)
    (bcT bcL bcB : ByteCoins L) (capT capL capB : ℕ → ℕ) (xB : XF)
    (yT : (oneExternalString (2 ^ (S.DK.at frS.P.T.a).a) PQ.SgX).Str) (yL : (twoExternalStrings (2 ^ frS.P.T.a) PQ.SgX).Str)
    (yB : (oneExternalString (2 ^ (S.DP.at frS.P.T.a).a) PQ.SgX).Str) (xtT xtL xtB : ℕ → TreeK 256 L)
    (q : Typed S) (τT : Tr (QT S).loc.shape) (τL : Tr (QL S).loc.shape) (τB : Tr (QB S).loc.shape)
    (g : Fam (typedOracleFamily 256 (K + 1) L)) (tT tL tB : Tag)
    (embT : (p : OPos (QT S).loc.shape) → OSym (QT S).loc.shape p → Body L)
    (embPT : PlainPart (QT S).loc.shape (QT S).ann → PlainPart (shapeOf L tT) (annOf L tT))
    (xinT : RecFull → Option X') (cmsT : List (Dig 256)) (σT : Strat (QT S).loc.shape Unit)
    (embL : (p : OPos (QL S).loc.shape) → OSym (QL S).loc.shape p → Body L)
    (embPL : PlainPart (QL S).loc.shape (QL S).ann → PlainPart (shapeOf L tL) (annOf L tL))
    (xinL : RecFull × RecFull → Option X') (cmsL : List (Dig 256))
    (σL : Strat (QL S).loc.shape Unit)
    (embB : (p : OPos (QB S).loc.shape) → OSym (QB S).loc.shape p → Body L)
    (embPB : PlainPart (QB S).loc.shape (QB S).ann → PlainPart (shapeOf L tB) (annOf L tB))
    (xinB : XF × RecFull → Option X') (cmsB : List (Dig 256)) (σB : Strat (QB S).loc.shape Unit)
    (runT : (proveX tT (QT S) (wT S K) embT embPT xinT cmsT q.rcd yT xtT σT
      (coinsOf (GT S).nJ (GT S).n3 (sTG S.G).logLeaves bcT) capT).det g = .ok (q.piT, τT))
    (runL : (proveX tL (QL S) (wL S K) embL embPL xinL cmsL (q.rcd, q.rcd') yL xtL σL
      (coinsOf (dsF.length + 1) (dsF.length + 1) sL.logLeaves bcL) capL).det g = .ok (q.piL, τL))
    (runB : (proveX tB (QB S) (wB S K) embB embPB xinB cmsB (xB, q.rcd') yB xtB σB
      (coinsOf (GB S).nJ (GB S).n3 (sBG S.G).logLeaves bcB) capB).det g = .ok (q.piB, τB))
    (h : RunsOwe S (K := K) c salt sL bcT bcL bcB capT capL capB xB yT yL yB xtT xtL xtB q τT τL
      τB) : Fits S c q := by
  have hlen : ∀ r : RecFull, (trAns r.2).length < 2 ^ 64 := fun r => by
    rw [(wf_seedsOf r).2.2, frS_v]
    decide
  obtain ⟨pT, cT, rT⟩ := whole_prints (ckP .two) (S.DK.at frS.P.T.a) (front₀ S.G.rec₀)
    (join₀ S.G.rec₀) ByteArray.empty silK S.runK L K (chalP .two K) tT embT embPT xinT cmsT q.rcd yT
    xtT σT bcT capT g c salt (sTG S.G) q.piT τT runT h.coT h.fewJT h.few0T h.okT h.capT h.depT
    h.widT h.oweT
  obtain ⟨pB, cB, rB⟩ := whole_prints (ckP .two) (S.DP.at frS.P.T.a) (front₀ S.G.z₀.2)
    (join₀ S.G.z₀.2) ByteArray.empty silP S.runP L K (chalP .two K) tB embB embPB xinB cmsB
    (xB, q.rcd') yB xtB σB bcB capB g c salt (sBG S.G) q.piB τB runB h.coB h.fewJB h.few0B h.okB
    h.capB h.depB h.widB h.oweB
  obtain ⟨pL, zL⟩ := entry_prints (ckP .two) dsF frS.P.T.a xsF S.dec L K (chalP .two K) tL embL
    embPL xinL cmsL (q.rcd, q.rcd') yL xtL σL bcL capL g c salt sL q.piL τL (digToBytes q.cm)
    (trAns q.rcd.2) (digToBytes q.cm') (trAns q.rcd'.2) runL h.coL h.depthL h.coT.salt64 h.c32
    publicL_full h.okL h.capL h.depL (size_digToBytes _) (hlen _) (size_digToBytes _) (hlen _)
    h.oweL
  exact ⟨h.c32, pT, cT, pB, cB, pL, zL, rT, rB, h.ansT, h.copyT, h.copyB⟩

end Johnson.Prover.Print

#print axioms Johnson.Prover.Print.RunsOwe
#print axioms Johnson.Prover.Print.fits_of_runs
