-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Face/CommitValueF.lean: the value of the compiled committer's commitment, where committer and
prover go to the one hash function by the third exit (committerAndProverOverOneHash, Johnson/CompletenessAndZeroKnowledge/OneHashByFirstBlockTestFront.lean).

 1. The scheme committerAndProverOverOneHash, where what is published is the commitment alone, is run at a number n in
    the place of its coins.
 2. At every hash function its commitment is that of the committer of the first table alone
    (LayoutsByPublicReading.commitAtCoins, Johnson/Top/ToldCommitPlain.lean), at the encoding randomness and the
    salts that the first two digits of n name in the honest side's two enumerations: the same right
    side as at the first exit (evaluate_commit_frontArgK, CommitValue.lean of this folder).
 3. The premise on the third exit is on ONE TABLE's program alone (tabO: its tree, its seed's two
    queries): at every value of the public reading it reads each answer only as far as the third
    exit asks it. It is not FactorsAt (OneHashByFirstBlockTestFront.lean), which speaks of the provers' runs too:
    so the equation reads no prover and no search for a nonce.
 4. At tests made of a letter pass the premise follows from PassFits and FirstIs
    (evaluate_commit_frontArgKF_pass).
 5. At the description's own family of layouts and the test made of the wires' own work bits, at
    every set of public files, NO PREMISE IS LEFT (evaluate_commit_frontArgKF_atFiles).
An equation between values. Nothing on the committer's queries, on binding or on hiding.
-/
import Johnson.CompletenessAndZeroKnowledge.OneHashByFirstBlockTestFront
import Johnson.Face.CommitValue
import Johnson.Face.CommitValueOneHashByFirstBlockTest
import Johnson.Goal.Conditions.HonestAtDescriptionDataAtFiles
import Johnson.Goal.Conditions.WideOnto
import Johnson.FrontRoad.AtBuiltNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Johnson.Face
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.PublicAt OnBytes.FrontRoad VerifiableInference
open VerifiableInference.OnPublicFiles ZKCP.PublicRead
open _root_.Iop (HolographicProtocol RoundSplits Dig)

variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R) (h : T.D → HonestSide 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)
  (more : (d : T.D) → More (typedOracleFamily 256 R.queryLayout.K (typedOracleCarrier R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)) 256)
  {J P' : Type} (idx : J → R.Index) (x₀ : R.Instance)

theorem readToldF_C (i : R.Index) :
    (readToldF T h more).C i = T.Pub.bind fun d =>
      ((((commitW R.queryLayout (T.Sd d) (T.cA d) (h d) i).overOneF (T.m d) (more d)).bind fun k =>
        Rom.OComp.pure ((T.part d, k.1), k.2)).bind fun k => Rom.OComp.pure (k.1, (d, k.2))) := rfl

/-- The key of the scheme behind the public reading, at a number. -/
theorem det_readToldF (noCoin : T.Pub.NoCoin) (i : R.Index) (n : ℕ) (g : Fam (rom 256)) :
    ((((readToldF T h more).C i).withCoins n).det g).1 =
      (T.part (T.Pub.det g),
        ((((commitW R.queryLayout (T.Sd (T.Pub.det g)) (T.cA (T.Pub.det g)) (h (T.Pub.det g)) i).overOneF
          (T.m (T.Pub.det g)) (more (T.Pub.det g))).withCoins n).det g).1) := by
  rw [readToldF_C, OComp.withCoins_bind_of_noCoin _ _ _ noCoin, OComp.det_bind,
    OComp.withCoins_bind_pure, OComp.det_bind, OComp.withCoins_bind_pure, OComp.det_bind]
  rfl

/-- **THE VALUE OF THE COMPILED COMMITTER's COMMITMENT, BY THE THIRD EXIT.** -/
theorem evaluate_commit_frontArgKF (noCoin : T.Pub.NoCoin)
    (factors : ∀ d i r s, (tabO R.queryLayout (T.Sd d) (h d).b₀ i r (cutS (2 ^ R.queryLayout.depth) s)).FactorsBy
      (AgreeF (T.m d) (more d)))
    (ϖ : FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits → RequestProof 256 R.protocol → P')
    (Vf : ZKCP.Digest 256 → List Token × List Token → P' → ZKCP.OComp 256 Bool) (w : J) (n : ℕ)
    (f : Hash) :
    (deterministicOf ((((committerAndProverOverOneHash T h more idx x₀ (fun id _ => id) ϖ Vf).C w).withCoins n).mapO
        Prod.fst)).evaluate f =
      (T.commitAtCoins (h (T.Pub.det (_root_.Run.famOne f))).b₀ (idx w)
        (firstRandomness (h (T.Pub.det (_root_.Run.famOne f))) n)
        (firstSalts (h (T.Pub.det (_root_.Run.famOne f))) (2 ^ R.queryLayout.depth) n)).evaluate f := by
  have eC : (committerAndProverOverOneHash T h more idx x₀ (fun id _ => id) ϖ Vf).C w =
      (ofRom ((readToldF T h more).C (idx w))).bind fun keys =>
        (ZKCP.keyDigest (fun ck : KeyT R => T.encT (ck.1, lowKey ck.2)) keys.1).mapO fun dg =>
          (dg, (keys.1.2, keys.2)) := rfl
  rw [OnBytes.Maker.ParsedRead.evaluate_deterministicOf_det, eC,
    ZKCP.OComp.withCoins_bind_of_drawsNoCoin _
      (fun keys => ZKCP.OComp.DrawsNoCoin.mapO _ _ (drawsNoCoin_keyDigest _ _)),
    withCoins_ofRom]
  rw [det_mapO, ZKCP.OComp.det_bind, _root_.Run.det_ofRom, det_keyDigest_mapO,
    evaluate_commitAtCoins]
  unfold LayoutsByPublicReading.keyAtCoins
  rw [OComp.det_bind, OComp.det_bind, det_overOne]
  show ZKCP.digestUnder f T.encT
      (((((readToldF T h more).C (idx w)).withCoins n).det (_root_.Run.famOne f)).1.1,
        lowKey ((((readToldF T h more).C (idx w)).withCoins n).det (_root_.Run.famOne f)).1.2) = _
  rw [det_readToldF T h more noCoin]
  show ZKCP.digestUnder f T.encT (_, lowKey _) = _
  rw [lowKey_commitW_thirdExit _ _ _ _ _ _ _ _ _ (factors _ _)]
  rfl

/-- The same at tests made of a letter pass, under which the seed's two queries are asked whole. -/
theorem evaluate_commit_frontArgKF_pass (noCoin : T.Pub.NoCoin) {hK : 0 < R.queryLayout.K}
    (pass : T.D → Pass 256 (typedOracleCarrier R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits))
    (fits : ∀ d, PassFits R.queryLayout (T.Sd d) hK (pass d)) (first : ∀ d, FirstIs hK (T.m d))
    (ϖ : FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits → RequestProof 256 R.protocol → P')
    (Vf : ZKCP.Digest 256 → List Token × List Token → P' → ZKCP.OComp 256 Bool) (w : J) (n : ℕ)
    (f : Hash) :
    (deterministicOf ((((committerAndProverOverOneHash T h (fun d => moreP (pass d)) idx x₀ (fun id _ => id) ϖ
        Vf).C w).withCoins n).mapO Prod.fst)).evaluate f =
      (T.commitAtCoins (h (T.Pub.det (_root_.Run.famOne f))).b₀ (idx w)
        (firstRandomness (h (T.Pub.det (_root_.Run.famOne f))) n)
        (firstSalts (h (T.Pub.det (_root_.Run.famOne f))) (2 ^ R.queryLayout.depth) n)).evaluate f :=
  evaluate_commit_frontArgKF T h (fun d => moreP (pass d)) idx x₀ noCoin
    (fun d i r _ => factors_tabO R.queryLayout (T.Sd d) (T.m d) (fits d) (first d) (h d).b₀ i r _) ϖ Vf w n f

section AtFiles
open VerifierAndGoals FlashProve FlashProve

/-- **At the description's own family and the wires' own test: no premise.** -/
theorem evaluate_commit_frontArgKF_atFiles (files : PublicFiles)
    (h : (layoutsOfBuiltDescription flashProveData allZeroDigest [] files).D →
      HonestSide 256 (R₀ files).protocol (R₀ files).LeafBody (R₀ files).offlineRoundSplits (R₀ files).linkRoundSplits)
    {J P' : Type} (idx : J → (R₀ files).Index) (x₀ : (R₀ files).Instance)
    (ϖ : FullKey 256 (R₀ files).protocol (R₀ files).offlineRoundSplits (R₀ files).linkRoundSplits → RequestProof 256 (R₀ files).protocol → P')
    (Vf : ZKCP.Digest 256 → List Token × List Token → P' → ZKCP.OComp 256 Bool) (w : J) (n : ℕ)
    (f : Hash) :
    (deterministicOf ((((committerAndProverOverOneHash (layoutsOfBuiltDescription flashProveData allZeroDigest [] files) h
        (fun _ => moreP (firstBlockTestAtDescriptionData (dataAtFiles flashProveData files) allZeroDigest [])) idx x₀ (fun id _ => id) ϖ
        Vf).C w).withCoins n).mapO Prod.fst)).evaluate f =
      ((layoutsOfBuiltDescription flashProveData allZeroDigest [] files).commitAtCoins
        (h ((layoutsOfBuiltDescription flashProveData allZeroDigest [] files).Pub.det (_root_.Run.famOne f))).b₀ (idx w)
        (firstRandomness (h ((layoutsOfBuiltDescription flashProveData allZeroDigest [] files).Pub.det (_root_.Run.famOne f))) n)
        (firstSalts (h ((layoutsOfBuiltDescription flashProveData allZeroDigest [] files).Pub.det (_root_.Run.famOne f)))
          (2 ^ (R₀ files).queryLayout.depth) n)).evaluate f :=
  evaluate_commit_frontArgKF_pass (layoutsOfBuiltDescription flashProveData allZeroDigest [] files) h idx x₀
    (familyLaws_the files).noCoin (fun _ => firstBlockTestAtDescriptionData (dataAtFiles flashProveData files) allZeroDigest [])
    (fun d => passFits_layoutsByPublicReading (dataAtFiles flashProveData files) allZeroDigest [] d)
    (fun d => firstIs_layoutsByPublicReading (dataAtFiles flashProveData files) allZeroDigest [] d) ϖ Vf w n f

end AtFiles

end Johnson.Face

#print axioms Johnson.Face.det_readToldF
#print axioms Johnson.Face.evaluate_commit_frontArgKF
#print axioms Johnson.Face.evaluate_commit_frontArgKF_pass
#print axioms Johnson.Face.evaluate_commit_frontArgKF_atFiles
