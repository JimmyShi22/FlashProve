-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/TestInPlace.lean: a bound on the probability that the honest key and proof fail a
test carries over from the typed scheme at every value of the public reading to the scheme behind
the commitment ID.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has.
test_front: let t be any test on a whole key and a typed proof. Suppose that at every value d of the
type of the public reading's values, over the typed oracles, one run of the committer and one run of
the prover at d give a key and a proof that fail t with probability at most α. Then one run of the
committer and one run of the prover of openArg give a key and a proof that fail t with probability
at most α. It holds for every family T with the four properties of its public reading and for every
honest side h. Both bounds are for the pairs of a relation, R₁ at d and Rel at openArg, and Rel of
w and x' must give R₁ of idx w and the instance instOf R x₀ x'.

How it is done. The test is put in the verifier's place. A scheme's completeness error is the
probability that its verifier rejects the honest proof. So for the scheme with the same committer
and prover whose "verifier" asks no oracle and returns t of the key and the proof, "completeness
error at most α" says that the honest key and proof fail t with probability at most α. The theorems
that carry completeness upward are general in the verifier, and they are applied to these schemes:
completeness_overOne (Rom/ExitBind.lean), completeness_mapKey (Johnson/FrontRoad/Complete.lean),
complete_pub (ZKCP/PublicRead/Complete.lean), completeness_of_gen (ZKCP/SpecialAny.lean) and
pr_frontK_le (Johnson/FrontRoad/CompleteK.lean). None of these schemes is a scheme of the protocol:
their verifiers check nothing about an instance.

  testAt, testTold, testRead, testOne   the typed scheme at d, the same over one hash function with
      the told part in front of its key, the same behind the public reading, and the same with one
      request per call, each with t in the verifier's place. Committer and prover are those of
      typedAt, toldAt, readTold and readOne, by definition (testOne_C, testOne_P).
  openArg   frontArgK (Johnson/FrontRoad/FrontK.lean) with the pair (commitment ID, whole key) as
      its key, the typed proof as its proof, and t in the verifier's place.
  frontK_C_of_open, frontK_P_of_open   the committer and the prover of frontArgK, at any form κ of
      the key and any form ϖ of a proof, are those of openArg followed by κ and ϖ. So openArg shows
      what every such scheme, frontId among them, makes before it is put into its final form.
  ofRom_bindO, run_const   the step to the form of ZKCP/Defs.lean keeps sequential composition; an
      algorithm that ends in a fixed value returns it.

How it fits. Johnson/FrontRoad/LaidBeside.lean applies it to the test "all proof strings are
present". Not one of the release's goal statements.

Limits. The premise at every d is a premise here. A statement about one run of the committer and one
request, both fixed before the hash function is sampled. It says nothing about what a verifier of
the protocol accepts, and nothing on soundness or hiding.
-/
import Johnson.FrontRoad.CompleteK

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.PublicAt VerifiableInference
open VerifiableInference.OnPublicFiles ZKCP.PublicRead
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- The step to the form of ZKCP/Defs.lean keeps sequential composition. -/
theorem ofRom_bindO {lam : ℕ} {α β : Type} : ∀ (c : Rom.OComp (rom lam) α)
    (g : α → Rom.OComp (rom lam) β), ofRom (c.bind g) = (ofRom c).bind fun a => ofRom (g a)
  | .pure _, _ => rfl
  | .query _ q k, g => congrArg (ZKCP.OComp.query q) (funext fun r => ofRom_bindO (k r) g)
  | .sample n k, g => congrArg (ZKCP.OComp.sample n) (funext fun r => ofRom_bindO (k r) g)

/-- An algorithm that ends in a fixed value returns it, under every hash function. -/
theorem run_const {lam : ℕ} {α β : Type} (f : ZKCP.Oracle lam) (b : β)
    (c : Rom.OComp (rom lam) α) : (ofRom (c.bind fun _ => .pure b)).run f = PMF.pure b := by
  rw [ofRom_bindO, ZKCP.run_bind]
  exact PMF.bind_const _ _

variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R) (h : T.D → HonestSide 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)
  (t : FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits → RequestProof 256 R.protocol → Bool)

/-- The typed scheme at d with the test in the verifier's place. -/
def testAt (d : T.D) : ZKCP.Gen.Arg (typedOracleFamily 256 R.queryLayout.K (typedOracleCarrier R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)) R.Index R.Instance Unit
    (FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits) (Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits) (RequestProof 256 R.protocol) :=
  ⟨(typedAt T h d).C, (typedAt T h d).P, fun k _ π => .pure (t k π)⟩

/-- The same over one hash function, with the told part in front of its key. -/
def testTold (d : T.D) : ZKCP.Gen.Arg (rom 256) R.Index R.Instance Unit (KeyT R)
    (Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits) (RequestProof 256 R.protocol) :=
  mapKeyArg (schemeOverOneHashFunction (T.m d) (testAt T h t d)) (fun k => (T.part d, k)) fun ck _ π =>
    .pure (t ck.2 π)

/-- The same behind the public reading. -/
def testRead : ZKCP.Gen.Arg (rom 256) R.Index R.Instance Unit (KeyT R) (T.D × Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)
    (RequestProof 256 R.protocol) :=
  glueArg T.Pub (testTold T h t)

/-- The same, one request per call. -/
def testOne : ZKCP.Arg 256 R.Index R.Instance Unit (KeyT R) (T.D × Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)
    (RequestProof 256 R.protocol) :=
  ZKCP.SpecialAny.oneOf (testRead T h t)

/-- Its committer is readOne's, by definition. -/
theorem testOne_C : (testOne T h t).C = (readOne T h).C := rfl

/-- Its prover is readOne's, by definition. -/
theorem testOne_P : (testOne T h t).P = (readOne T h).P := rfl

variable {PP : Type}

/-- From every d to the scheme behind the public reading, one request per call. -/
theorem complete_testOne (R₁ : ZKCP.IndexedRelation R.Index R.Instance Unit PP) (α : ℝ≥0∞)
    (noCoin : T.Pub.NoCoin) (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (hA : ∀ d, ZKCP.Gen.HasCompletenessError (ZKCP.Special.toPair R₁) (testAt T h t d) 1 α) :
    ZKCP.HasCompletenessError R₁ (testOne T h t) α :=
  ZKCP.SpecialAny.completeness_of_gen R₁ (ZKCP.SpecialAny.agrees_oneOf _) α
    (complete_pub 256 _ _ _ _ _ _ _ _ (ZKCP.Special.toPair R₁) (testTold T h t) 1 α T.Pt T.Pub
      noCoin asks once
      (fun d i => asks_mapKey_C _ _ _ _ i (wholeAt_C h spare d i))
      (fun d isk b => wholeAt_P h spare d isk b) (fun _ _ _ _ => trivial)
      fun d => completeness_mapKey (ZKCP.Special.toPair R₁) (schemeOverOneHashFunction (T.m d) (testAt T h t d)) 1
        α _ _ (fun _ _ _ => rfl)
        (completeness_overOne (T.m d) (ZKCP.Special.toPair R₁) (testAt T h t d) 1 α (hA d)))

variable {J : Type} (idx : J → R.Index) (x₀ : R.Instance)

/-- frontArgK with the pair (commitment ID, whole key) as its key, the typed proof as its proof, and
the test in the verifier's place. -/
def openArg : ZKCP.Arg 256 J (List Token × List Token) Unit (KeyF R)
    (FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits × (T.D × Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)) (RequestProof 256 R.protocol) :=
  frontArgK T h idx x₀ (fun dg k => (dg, k)) (fun _ π => π) fun dk _ π => .pure (t dk.2 π)

/-- **The honest key and proof of openArg fail the test with probability at most α**, if those of
the typed scheme do at every d, under the four properties of the public reading, and if Rel of w and
x' gives R₁ of idx w and the instance instOf R x₀ x'. -/
theorem test_front {PP' : Type} (R₁ : ZKCP.IndexedRelation R.Index R.Instance Unit PP)
    (Rel : ZKCP.IndexedRelation J (List Token × List Token) Unit PP') (α : ℝ≥0∞)
    (noCoin : T.Pub.NoCoin) (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (hA : ∀ d, ZKCP.Gen.HasCompletenessError (ZKCP.Special.toPair R₁) (testAt T h t d) 1 α)
    (hrel : ∀ w x', Rel.rel w x' () → R₁.rel (idx w) (instOf R x₀ x') ()) :
    ZKCP.HasCompletenessError Rel (openArg T h t idx x₀) α := by
  intro w x' u hr
  cases u
  exact le_trans
    (pr_frontK_le (testOne T h t) (fun ck : KeyT R => T.encT (ck.1, lowKey ck.2)) (fun ck => ck.2)
      (fun dg k => (dg, k)) (fun _ π => π) (fun dk _ π => .pure (t dk.2 π)) (idx w)
      (instOf R x₀ x') x' () fun f keys _ π _ =>
        le_of_eq (congrArg (fun μ => ZKCP.prob μ {b | b = false})
          (run_const f (t keys.1.2 π) T.Pub).symm))
    (complete_testOne T h t R₁ α noCoin asks once spare hA (idx w) (instOf R x₀ x') ()
      (hrel w x' hr))

variable {K' P' : Type} (κ : ZKCP.Digest 256 → FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits → K')
  (ϖ : FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits → RequestProof 256 R.protocol → P')
  (Vf : K' → List Token × List Token → P' → ZKCP.OComp 256 Bool)

/-- The committer of frontArgK, at any form of the key, is openArg's followed by that form. -/
theorem frontK_C_of_open (w : J) :
    (frontArgK T h idx x₀ κ ϖ Vf).C w =
      ((openArg T h t idx x₀).C w).mapO fun o => (κ o.1.1 o.1.2, o.2) := by
  show _ = (((readOne T h).C (idx w)).bind fun keys =>
    (ZKCP.keyDigest (fun ck : KeyT R => T.encT (ck.1, lowKey ck.2)) keys.1).mapO fun dg =>
      ((dg, keys.1.2), (keys.1.2, keys.2))).mapO fun o => (κ o.1.1 o.1.2, o.2)
  rw [ZKCP.OComp.bind_mapO]
  refine congrArg _ (funext fun keys => ?_)
  exact (ZKCP.OComp.mapO_bind (fun dg => ((dg, keys.1.2), (keys.1.2, keys.2)))
    (ZKCP.keyDigest (fun ck : KeyT R => T.encT (ck.1, lowKey ck.2)) keys.1)
    fun o => .pure (κ o.1.1 o.1.2, o.2)).symm

/-- The prover of frontArgK, at any form of a proof, is openArg's followed by that form. -/
theorem frontK_P_of_open
    (isk : FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits × (T.D × Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits))
    (x' : List Token × List Token) :
    (frontArgK T h idx x₀ κ ϖ Vf).P isk x' () =
      ((openArg T h t idx x₀).P isk x' ()).mapO (ϖ isk.1) :=
  (ZKCP.OComp.mapO_bind (fun π => π) ((readOne T h).P isk.2 (instOf R x₀ x') ())
    fun π => .pure (ϖ isk.1 π)).symm

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.ofRom_bindO
#print axioms OnBytes.FrontRoad.run_const
#print axioms OnBytes.FrontRoad.testOne_C
#print axioms OnBytes.FrontRoad.testOne_P
#print axioms OnBytes.FrontRoad.complete_testOne
#print axioms OnBytes.FrontRoad.test_front
#print axioms OnBytes.FrontRoad.frontK_C_of_open
#print axioms OnBytes.FrontRoad.frontK_P_of_open
