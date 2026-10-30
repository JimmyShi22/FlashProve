-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/OneHashByFirstBlockTestFront.lean: THE STOREYS ABOVE THE THIRD EXIT. wholeAtF, toldAtF, readToldF, readOneF,
committerAndProverOverOneHash, frontIdF, slotArgF, slotSystemF are wholeAt, toldAt, readTold, readOne, frontArgK, frontId,
slotArg, slotSystem with the committer and the prover at each reading by overOneF, so that a failed try
of a search asks one hash block. The verifier is the same term.

Each storey has the law of its twin at every hash function and at every number for the committer's
coins, under FactorsAt: that is all that completeness and zero knowledge read, so each conclusion at
slotSystem carries to slotSystemF, with the same simulator and error (zeroKnowledgeOn_slotSystemF,
completeOn_slotSystemF, and at the scheme strongPrivacy_frontArgKF, completeness_frontArgKF).
Nothing here is a goal. Of the honest side's query log nothing is said.
-/
import Johnson.CompletenessAndZeroKnowledge.OneHashByFirstBlockTest
import Johnson.CompletenessAndZeroKnowledge.SameRun
import Johnson.CompletenessAndZeroKnowledge.SameSystem
import Johnson.FrontRoad.Slot

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace Rom

variable {S : OSpec} {lam : ℕ} {α : Type}

/-- The third exit can be taken before or after the number is given. -/
theorem withCoins_overOneF (m : OracleCoding S lam) (more : More S lam) : ∀ (c : OComp S α) (coins : ℕ),
    (c.overOneF m more).withCoins coins = (c.withCoins coins).overOneF m more
  | .pure _, _ => rfl
  | .sample _ k, _ => withCoins_overOneF m more (k _) _
  | .query o q k, coins => by
      show ((askFirst lam (m.blocks o) (more o q) (m.code o q)).bind fun bs =>
          (k ((m.rng o).symm bs)).overOneF m more).withCoins coins
        = (askFirst lam (m.blocks o) (more o q) (m.code o q)).bind fun bs =>
          ((k ((m.rng o).symm bs)).withCoins coins).overOneF m more
      rw [OComp.withCoins_bind_of_noCoin _ _ _ (noCoin_askFirst _ _ _)]
      exact congrArg _ (funext fun bs => withCoins_overOneF m more (k _) coins)

/-- A program that factors still factors at a number. -/
theorem OComp.FactorsBy.withCoins {ag : ∀ o, S.Dom o → S.Rng o → S.Rng o → Prop} :
    ∀ (c : OComp S α) (coins : ℕ), c.FactorsBy ag → (c.withCoins coins).FactorsBy ag
  | .pure _, _, _ => trivial
  | .sample _ k, _, h => OComp.FactorsBy.withCoins (k _) _ (h _)
  | .query _ _ k, coins, h =>
    ⟨fun r r' hr => congrArg (fun c => OComp.withCoins c coins) (h.1 r r' hr),
      fun r => OComp.FactorsBy.withCoins (k r) coins (h.2 r)⟩

/-- At a number too the third exit has the first exit's law at every hash function. -/
theorem runEager_withCoins_overOneF (m : OracleCoding S lam) (more : More S lam) (g : Fam (rom lam))
    (c : OComp S α) (h : c.FactorsBy (AgreeF m more)) (coins : ℕ) :
    ((c.overOneF m more).withCoins coins).runEager g =
      ((c.overOne m).withCoins coins).runEager g := by
  rw [withCoins_overOneF, withCoins_overOne]
  exact runEager_overOneF_eq m more g _ (OComp.FactorsBy.withCoins c coins h)

theorem run_ofRom {β : Type} (f : ZKCP.Oracle lam) (c : OComp (rom lam) β) :
    (ofRom c).run f = c.runEager (famOf f) := by
  rw [← runEager_toRom, toRom_ofRom]

end Rom

namespace OnBytes.FrontRoad
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.PublicAt VerifiableInference
open VerifiableInference.OnPublicFiles ZKCP.PublicRead VerifierAndGoals
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

section Read
variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R) (h : T.D → HonestSide 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)
  (more : (d : T.D) → More (typedOracleFamily 256 R.queryLayout.K (typedOracleCarrier R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)) 256)

/-- The scheme at d over one hash function, committer and prover by the third exit. -/
def wholeAtF (d : T.D) : ZKCP.Gen.Arg (rom 256) R.Index R.Instance Unit (FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits)
    (Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits) (RequestProof 256 R.protocol) :=
  overOneArgFF (T.m d) (more d) (typedAt T h d)

/-- The same with the told part of d in front of its key. -/
def toldAtF (d : T.D) : ZKCP.Gen.Arg (rom 256) R.Index R.Instance Unit (KeyT R) (Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)
    (RequestProof 256 R.protocol) :=
  mapKeyArg (wholeAtF T h more d) (fun k => (T.part d, k)) fun ck x π =>
    if ck.1 = T.part d then (wholeAtF T h more d).V ck.2 x π else .pure false

/-- The public reading, then toldAtF at the value that it returns. -/
def readToldF : ZKCP.Gen.Arg (rom 256) R.Index R.Instance Unit (KeyT R) (T.D × Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)
    (RequestProof 256 R.protocol) :=
  glueArg T.Pub (toldAtF T h more)

/-- readToldF as a ZKCP.Arg: one hash function, one request a call. -/
def readOneF : ZKCP.Arg 256 R.Index R.Instance Unit (KeyT R) (T.D × Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)
    (RequestProof 256 R.protocol) :=
  ZKCP.SpecialAny.oneOf (readToldF T h more)

/-- What the third exit asks at every reading. -/
structure FactorsAt : Prop where
  C : ∀ d i, ((typedAt T h d).C i).FactorsBy (AgreeF (T.m d) (more d))
  P : ∀ d k b, ((typedAt T h d).P k b).FactorsBy (AgreeF (T.m d) (more d))

variable {T h more}

theorem sameHonest_wholeAt (F : FactorsAt T h more) (d : T.D) :
    SameHonestLaw (wholeAt T h d) (wholeAtF T h more d) :=
  sameHonestLaw_overOneFF (T.m d) (more d) (F.C d) (F.P d)

theorem sameHonest_toldAt (F : FactorsAt T h more) (d : T.D) :
    SameHonestLaw (toldAt T h d) (toldAtF T h more d) where
  C := fun g i => by
    show (((wholeAtF T h more d).C i).bind fun k => .pure ((T.part d, k.1), k.2)).runEager g =
      (((wholeAt T h d).C i).bind fun k => .pure ((T.part d, k.1), k.2)).runEager g
    rw [OComp.runEager_bind, OComp.runEager_bind, (sameHonest_wholeAt F d).C g i]
  P := (sameHonest_wholeAt F d).P
  V := rfl

theorem sameHonest_readTold (F : FactorsAt T h more) :
    SameHonestLaw (readTold T h) (readToldF T h more) where
  C := fun g i => by
    show (T.Pub.bind fun d => ((toldAtF T h more d).C i).bind fun k =>
        .pure (k.1, (d, k.2))).runEager g =
      (T.Pub.bind fun d => ((toldAt T h d).C i).bind fun k => .pure (k.1, (d, k.2))).runEager g
    rw [OComp.runEager_bind, OComp.runEager_bind]
    refine congrArg _ (funext fun d => ?_)
    rw [OComp.runEager_bind, OComp.runEager_bind, (sameHonest_toldAt F d).C g i]
  P := fun g k b => (sameHonest_toldAt F k.1).P g k.2 b
  V := rfl

/-- The committer at a number. -/
theorem sameCoins_readTold (noCoin : T.Pub.NoCoin) (F : FactorsAt T h more) (i : R.Index) (coins : ℕ)
    (g : Fam (rom 256)) :
    (((readToldF T h more).C i).withCoins coins).runEager g =
      (((readTold T h).C i).withCoins coins).runEager g := by
  show ((T.Pub.bind fun d => ((((typedAt T h d).C i).overOneF (T.m d) (more d)).bind fun k =>
        .pure ((T.part d, k.1), k.2)).bind fun k => .pure (k.1, (d, k.2))).withCoins coins).runEager g =
    ((T.Pub.bind fun d => ((((typedAt T h d).C i).overOne (T.m d)).bind fun k =>
        .pure ((T.part d, k.1), k.2)).bind fun k => .pure (k.1, (d, k.2))).withCoins coins).runEager g
  rw [OComp.withCoins_bind_of_noCoin _ _ _ noCoin, OComp.withCoins_bind_of_noCoin _ _ _ noCoin,
    OComp.runEager_bind, OComp.runEager_bind]
  refine congrArg _ (funext fun d => ?_)
  rw [OComp.withCoins_bind_pure, OComp.withCoins_bind_pure, OComp.withCoins_bind_pure,
    OComp.withCoins_bind_pure, OComp.runEager_bind, OComp.runEager_bind, OComp.runEager_bind,
    OComp.runEager_bind, runEager_withCoins_overOneF _ _ g _ (F.C d i) coins]

section Scheme
variable (T h more)
variable {J K' P' : Type} (idx : J → R.Index) (x₀ : R.Instance)
  (κ : ZKCP.Digest 256 → FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits → K')
  (ϖ : FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits → RequestProof 256 R.protocol → P')
  (Vf : K' → List Token × List Token → P' → ZKCP.OComp 256 Bool)

/-- **frontArgK with committer and prover by the third exit.** -/
def committerAndProverOverOneHash : ZKCP.Arg 256 J (List Token × List Token) Unit K'
    (FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits × (T.D × Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)) P' where
  C := fun w => ((readOneF T h more).C (idx w)).bind fun keys =>
    (ZKCP.keyDigest (fun ck : KeyT R => T.encT (ck.1, lowKey ck.2)) keys.1).mapO fun dg =>
      (κ dg keys.1.2, (keys.1.2, keys.2))
  P := fun isk x' _ => ((readOneF T h more).P isk.2 (instOf R x₀ x') ()).mapO (ϖ isk.1)
  V := Vf

variable {T h more}

theorem run_readOne_C (F : FactorsAt T h more) (f : ZKCP.Oracle 256) (i : R.Index) :
    ((readOneF T h more).C i).run f = ((readOne T h).C i).run f := by
  show (ofRom ((readToldF T h more).C i)).run f = (ofRom ((readTold T h).C i)).run f
  rw [run_ofRom, run_ofRom, (sameHonest_readTold F).C]

theorem run_readOne_P (F : FactorsAt T h more) (f : ZKCP.Oracle 256)
    (k : T.D × Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits) (x : R.Instance) (u : Unit) :
    ((readOneF T h more).P k x u).run f = ((readOne T h).P k x u).run f := by
  show (ofRom (((readToldF T h more).P k [(x, u)]).bind fun πs => .pure (ZKCP.Special.head1 πs))).run f =
    (ofRom (((readTold T h).P k [(x, u)]).bind fun πs => .pure (ZKCP.Special.head1 πs))).run f
  rw [run_ofRom, run_ofRom, OComp.runEager_bind, OComp.runEager_bind, (sameHonest_readTold F).P]

/-- **committerAndProverOverOneHash has frontArgK's law at every hash function.** -/
theorem sameRun_frontK (F : FactorsAt T h more) :
    ZKCP.SameRun (frontArgK T h idx x₀ κ ϖ Vf) (committerAndProverOverOneHash T h more idx x₀ κ ϖ Vf) where
  C := fun f w => ZKCP.run_bind_congr f (run_readOne_C F f (idx w)) fun _ => rfl
  P := fun f isk x' u => by
    show (((readOneF T h more).P isk.2 (instOf R x₀ x') ()).mapO (ϖ isk.1)).run f =
      (((readOne T h).P isk.2 (instOf R x₀ x') ()).mapO (ϖ isk.1)).run f
    rw [ZKCP.OComp.run_mapO, ZKCP.OComp.run_mapO, run_readOne_P F]
  V := rfl

/-- The committer at a number. -/
theorem run_withCoins_frontK (noCoin : T.Pub.NoCoin) (F : FactorsAt T h more) (f : ZKCP.Oracle 256)
    (w : J) (coins : ℕ) :
    (((committerAndProverOverOneHash T h more idx x₀ κ ϖ Vf).C w).withCoins coins).run f =
      (((frontArgK T h idx x₀ κ ϖ Vf).C w).withCoins coins).run f := by
  have hg : ∀ keys : KeyT R × (T.D × Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits), ((ZKCP.keyDigest
                                                (fun ck : KeyT R => T.encT (ck.1, lowKey ck.2)) keys.1).mapO fun dg =>
                                                  (κ dg keys.1.2, (keys.1.2, keys.2))).DrawsNoCoin := fun keys =>
    ZKCP.OComp.DrawsNoCoin.mapO _ _ (drawsNoCoin_keyDigest _ keys.1)
  show (((ofRom ((readToldF T h more).C (idx w))).bind _).withCoins coins).run f =
    (((ofRom ((readTold T h).C (idx w))).bind _).withCoins coins).run f
  rw [ZKCP.OComp.withCoins_bind_of_drawsNoCoin _ hg, ZKCP.OComp.withCoins_bind_of_drawsNoCoin _ hg]
  refine ZKCP.run_bind_congr f ?_ fun _ => rfl
  rw [withCoins_ofRom, withCoins_ofRom, run_ofRom, run_ofRom]
  exact sameCoins_readTold noCoin F (idx w) coins _

/-- **Index privacy, in its strong form, carries to committerAndProverOverOneHash**, with the same simulator and bound. -/
theorem strongPrivacy_frontArgKF {PP : Type}
    {Rel : ZKCP.IndexedRelation J (List Token × List Token) Unit PP}
    {Sim : ZKCP.Simulator 256 PP K' (List Token × List Token) P'} {ζ : ℕ → ℕ → ℝ≥0∞}
    (F : FactorsAt T h more)
    (hp : ZKCP.HasStrongIndexPrivacyWith Rel (frontArgK T h idx x₀ κ ϖ Vf) Sim ζ) :
    ZKCP.HasStrongIndexPrivacyWith Rel (committerAndProverOverOneHash T h more idx x₀ κ ϖ Vf) Sim ζ :=
  ZKCP.strongPrivacy_congr (sameRun_frontK idx x₀ κ ϖ Vf F) hp

/-- **Completeness carries to committerAndProverOverOneHash.** -/
theorem completeness_frontArgKF {PP : Type}
    {Rel : ZKCP.IndexedRelation J (List Token × List Token) Unit PP} {α : ℝ≥0∞}
    (F : FactorsAt T h more) (hc : ZKCP.HasCompletenessError Rel (frontArgK T h idx x₀ κ ϖ Vf) α) :
    ZKCP.HasCompletenessError Rel (committerAndProverOverOneHash T h more idx x₀ κ ϖ Vf) α :=
  ZKCP.completeness_congr (sameRun_frontK idx x₀ κ ϖ Vf F) hc

end Scheme

end Read

section Slot
variable (D : Description) (Z : VerifierAndGoals.PublicFiles) (c₀ : Digest) (m₀ : D.More)
  (T : LayoutsByPublicReading (D.input Z c₀ m₀))
  (h : T.D → HonestSide 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits
    (D.input Z c₀ m₀).linkRoundSplits)
  (more : (d : T.D) → More (typedOracleFamily 256 (D.input Z c₀ m₀).queryLayout.K
    (typedOracleCarrier (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits
      (D.input Z c₀ m₀).linkRoundSplits)) 256)
  (s : IntegerTransformer.Settings) (idx : ModelWeights s → (D.input Z c₀ m₀).Index)
  (x₀ : (D.input Z c₀ m₀).Instance) (Form : Type) (parse : Parser D Z Form)
  (encF : TypedProof (D.F Z) (D.P Z) → Form) (bound : ℕ)

/-- frontId with committer and prover by the third exit. Its verifier is frontId's. -/
def frontIdF : ZKCP.Arg 256 (ModelWeights s) (List Token × List Token) Unit Commitment
    (FullKey 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).offlineRoundSplits (D.input Z c₀ m₀).linkRoundSplits ×
      (T.D × Isk 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits
        (D.input Z c₀ m₀).linkRoundSplits)) Form :=
  committerAndProverOverOneHash T h more idx x₀ (fun id _ => id) (fun k π => encF ([], (lowKey k, lowPrf k π)))
    fun c x' form => (verify D Z parse c x'.1 x'.2 form).toRandomized.toUpload

/-- frontIdF with the committer's random choices sampled first. -/
def slotArgF : ZKCP.Arg 256 (ModelWeights s) (List Token × List Token) Unit (ZKCP.Digest 256)
    (ModelWeights s × Fin (bound + 1)) Form :=
  (frontIdF D Z c₀ m₀ T h more s idx x₀ Form parse encF).coinsFirst bound

/-- frontIdF's committer at a given number: the commitment ID. -/
def slotCommitF (w : ModelWeights s) (coins : Fin (bound + 1)) : ZKCP.OComp 256 (ZKCP.Digest 256) :=
  (((frontIdF D Z c₀ m₀ T h more s idx x₀ Form parse encF).C w).withCoins coins.val).mapO Prod.fst

/-- **slotSystem with committer and prover by the third exit.** -/
def slotSystemF : ArgumentSystem :=
  withHonest (slotSystem D Z c₀ m₀ T h s idx x₀ Form parse encF bound)
    (fun w coins => deterministicOf (slotCommitF D Z c₀ m₀ T h more s idx x₀ Form parse encF
      bound w coins))
    (fun w coins p o => RandomizedAlgorithm.ofUpload
      ((slotArgF D Z c₀ m₀ T h more s idx x₀ Form parse encF bound).P (w, coins) (p, o) ()))

/-- Its verifier field is the verifier of Ladder.lean. -/
theorem slotF_verify :
    (slotSystemF D Z c₀ m₀ T h more s idx x₀ Form parse encF bound).verify = verify D Z parse :=
  slot_verify D Z c₀ m₀ T h s idx x₀ Form parse encF bound

variable {D Z c₀ m₀ T h more s idx x₀ Form parse encF bound}

theorem evaluate_deterministicOf_congr {α : Type} {c c' : ZKCP.OComp 256 α} (hc : c.DrawsNoCoin)
    (hc' : c'.DrawsNoCoin) (hash : Hash) (h : c.run hash = c'.run hash) :
    (deterministicOf c).evaluate hash = (deterministicOf c').evaluate hash := by
  have e : ∀ {d : ZKCP.OComp 256 α}, d.DrawsNoCoin →
      d.run hash = PMF.pure ((deterministicOf d).evaluate hash) := fun {d} hd => by
    have := RandomizedAlgorithm.run_toUpload hash (deterministicOf d).toRandomized
    rw [toUpload_deterministicOf d hd, DeterministicAlgorithm.run_toRandomized] at this
    exact this
  have h2 := (e hc).symm.trans (h.trans (e hc'))
  classical
  by_contra hne
  have h3 := congrArg (fun p => p ((deterministicOf c).evaluate hash)) h2
  simp only [PMF.pure_apply, if_true, if_neg hne] at h3
  exact one_ne_zero h3

theorem slot_commit_same (noCoin : T.Pub.NoCoin) (F : FactorsAt T h more) (hash : Hash)
    (w : ModelWeights s) (coins : Fin (bound + 1)) :
    (deterministicOf (slotCommitF D Z c₀ m₀ T h more s idx x₀ Form parse encF bound w
      coins)).evaluate hash =
      (deterministicOf (slotCommit D Z c₀ m₀ T h s idx x₀ Form parse encF bound w coins)).evaluate
        hash := by
  refine evaluate_deterministicOf_congr ?_ ?_ hash ?_
  · exact ZKCP.OComp.DrawsNoCoin.mapO _ _ (ZKCP.OComp.drawsNoCoin_withCoins _ _)
  · exact ZKCP.OComp.DrawsNoCoin.mapO _ _ (ZKCP.OComp.drawsNoCoin_withCoins _ _)
  · show ((((frontIdF D Z c₀ m₀ T h more s idx x₀ Form parse encF).C w).withCoins
        coins.val).mapO Prod.fst).run hash =
      ((((frontId D Z c₀ m₀ T h s idx x₀ Form parse encF).C w).withCoins coins.val).mapO
        Prod.fst).run hash
    rw [ZKCP.OComp.run_mapO, ZKCP.OComp.run_mapO]
    exact congrArg _ (run_withCoins_frontK _ _ _ _ _ noCoin F hash w coins.val)

theorem slot_prove_same (noCoin : T.Pub.NoCoin) (F : FactorsAt T h more) (hash : Hash)
    (w : ModelWeights s) (coins : Fin (bound + 1)) (p o : List Token) :
    (RandomizedAlgorithm.ofUpload
      ((slotArgF D Z c₀ m₀ T h more s idx x₀ Form parse encF bound).P (w, coins) (p, o) ())).run hash =
      ((slotSystem D Z c₀ m₀ T h s idx x₀ Form parse encF bound).prove w coins p o).run hash := by
  show (RandomizedAlgorithm.ofUpload _).run hash = (RandomizedAlgorithm.ofUpload
    ((slotArg D Z c₀ m₀ T h s idx x₀ Form parse encF bound).P (w, coins) (p, o) ())).run hash
  rw [RandomizedAlgorithm.run_ofUpload, RandomizedAlgorithm.run_ofUpload]
  exact ZKCP.run_bind_congr hash (run_withCoins_frontK _ _ _ _ _ noCoin F hash w coins.val) fun key =>
    (sameRun_frontK _ _ _ _ _ F).P hash key.2 (p, o) ()

/-- **Zero knowledge on a domain carries from slotSystem to slotSystemF**, with the same error. -/
theorem zeroKnowledgeOn_slotSystemF (noCoin : T.Pub.NoCoin) (F : FactorsAt T h more)
    {domain : ModelWeights s → List Token → List Token → Prop} {ζ : ℕ → ℕ → ℝ≥0∞}
    (hz : ZeroKnowledgeOn (slotSystem D Z c₀ m₀ T h s idx x₀ Form parse encF bound) domain ζ) :
    ZeroKnowledgeOn (slotSystemF D Z c₀ m₀ T h more s idx x₀ Form parse encF bound) domain ζ := by
  exact zeroKnowledgeOn_congr (fun hash w coins => slot_commit_same noCoin F hash w coins)
    (fun hash w coins p o => slot_prove_same noCoin F hash w coins p o) hz

/-- **Completeness on a domain carries from slotSystem to slotSystemF**, with the same error. -/
theorem completeOn_slotSystemF (noCoin : T.Pub.NoCoin) (F : FactorsAt T h more)
    {domain : ModelWeights s → List Token → List Token → Prop} {α : ℝ≥0∞}
    (hc : CompleteOn (slotSystem D Z c₀ m₀ T h s idx x₀ Form parse encF bound) domain α) :
    CompleteOn (slotSystemF D Z c₀ m₀ T h more s idx x₀ Form parse encF bound) domain α := by
  exact completeOn_congr (fun hash w coins => slot_commit_same noCoin F hash w coins)
    (fun hash w coins p o => slot_prove_same noCoin F hash w coins p o) hc

end Slot

end OnBytes.FrontRoad

#print axioms Rom.withCoins_overOneF
#print axioms OnBytes.FrontRoad.sameHonest_readTold
#print axioms OnBytes.FrontRoad.sameRun_frontK
#print axioms OnBytes.FrontRoad.strongPrivacy_frontArgKF
#print axioms OnBytes.FrontRoad.completeness_frontArgKF
#print axioms OnBytes.FrontRoad.slotF_verify
#print axioms OnBytes.FrontRoad.zeroKnowledgeOn_slotSystemF
#print axioms OnBytes.FrontRoad.completeOn_slotSystemF
