-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/SameVerifier.lean: THE SAME COMPILED VERIFIER. The library's compiled verifier (`innerCompiledVerifier`,
Johnson/Top/InnerCompiledVerifier.lean) is made from an input that holds an object (`Iop.HolographicProtocol`). If the object's
index type is re-indexed and its three honest provers are replaced by any others, the compiled
verifier is the same function.

Why. E2E/ObjectAtFiles.lean's object `objAt Z P` differs from the object in the types of
`VerifierAndGoals.verify` in the index type and the provers. The library's types of keys and proofs have the
object as a parameter, so a theorem about "the compiled verifier at `objAt Z P`" speaks by type of
another term. Here that term is shown to be the verifier's own, up to the library's own passage of
keys and proofs through their verifier's side (`KeyRoot.v`, `KeyRoot.ofV`, … : field by field the
same values; Johnson/TypedOracleCompiler/RecCompile/SideTies.lean).

How. The library shows that `innerCompiledVerifier r` is `verifyV r.toInputV` (`innerCompiledVerifier_eq`,
Johnson/Top/InnerCompiledVerifierSide.lean; no hypothesis), and `toInputV` reads the object through its
verifier's side `HolographicProtocol.v` alone. The two inputs have ONE `toInputV`, by unfolding.

Definitions.
  `swapL L f g hT hL hB`: L re-indexed along f and g (E2E/CutIndex.lean) with its three honest
    provers replaced by hT, hL, hB.
  `swapIn r f g hT hL hB next ISK commit prove`: the input r with its object so replaced. What the
    verifier reads is r's own (the wire of the OOD sample, the code of a key and the fixed pair are
    passed through their verifier's side). The model and the honest side's algorithms are free
    letters: the verifier does not read them.
What is shown.
  `v_swapL`: the verifier's side of `swapL …` is L's. `swapL_reIndex`: at L's own provers it is
    `reIndex`.
  `toInputV_swapIn`: the two inputs have one verifier's side: BY UNFOLDING.
  `innerCompiledVerifier_swapIn`: **the compiled verifier at the replaced object is the compiled verifier at
    r**, at every commitment, prompt, output and proof.
  `swapL_obj`: at three protocols F over any configuration and any set p of indices: `cut (F.withProvers P)
    p` is `swapL (F.withProvers P₀) …` for every P₀ and P: by unfolding.
  `inputCut`, `inputCut_L`, `innerCompiledVerifier_cut`: there: the compiled verifier at an input whose object
    is `cut (F.withProvers P) p`, for ANY provers P, is the compiled verifier at the library's input
    `innerInputOfThreeProtocols F P₀ T`. (Stated for any configuration: written out at the full size's own, Lean's
    comparison of the two sides ran out of its limits.)
  `input_eq_describe`: at three public files Z the library's input at any letters T of the full size
    is `innerInputOfThreeProtocols (filesAt Z) …` at the library's own provers: by definition. So the line above,
    at F := `filesAt Z`, speaks of `objAt Z P` and of that input.

Limits.
- An equation of two algorithms with an oracle. Nothing on soundness, completeness or what a view
  shows. No property of the compiled argument is carried across by it alone: a theorem about the
  argument system at the replaced input also reads its committer, prover and model, which are free
  letters here.
- It does not reach the protocols with 0 proof-of-work bits: there the three protocols differ.
- No statement here names `VerifierAndGoals.verify`. That it calls `innerCompiledVerifier` at the input of its argument D,
  behind the scope's test, a parser and two readings, is `verify_calls` (E2E/DescriptionTie.lean).

BESIDE EVERY TELLING of the result on the index's committed tables, to which this file belongs
(E2E/WholeViewAtFiles.lean, E2E/TablesAtOwnObject.lean):
- placeholder provers: no message of the protocol is covered; it is not zero knowledge;
- before compilation: no hashing; each OOD seed is chosen before its table's coins are drawn, from
  nothing but what has been shown and coins of the environment's own: of a seed that hangs on
  anything hidden, another table's pads too, nothing is said;
- fresh uniform pads and encoding randomness for each table (as run: derived from the committer's
  secret seed); one OOD sample a table; one set of public files. One table's randomness is used
  under one set of public files alone. The same rows and pads under other public files would get
  another seed, and of two OOD samples on one table's pads this file says nothing.
- the budget is table by table, is kept by nobody, and has no slack: at one column more the
  interface's clause on the encoder fails (a theorem: some OOD seed, two matrices in range, at every
  set of that size; it states no size of the difference, only that the two laws differ; typed for
  the form with all OOD seeds alone); that the result itself fails there is typed by no environment;
- that the IOP's own tests on the public files pass is shown in the side library: at the library's
  two named sets of public files (AtFullSide/E2E/AtWrittenFiles.lean), and at the first set's files
  under every policy within four bounds (`theLive_zAt`, AtFullSide/Top/LiveAtPolicies.lean); no
  theorem ties any of these to a file on a disk.


-/
import E2E.ObjectAtFiles
import Johnson.Top.InnerCompiledVerifierSide
import Johnson.TypedOracleCompiler.RecCompile.SideTies
import Johnson.Flat.Dec.TwoSizesAt
import Johnson.Goal.Description.Letters

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles
open Prob Hiop AtPublicFiles.Cut
open VerifiableInference VerifiableInference.OnPublicFiles
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Flat (Files)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData)

/-! ## 1. For any object and any input -/

section General
variable {I I' X : Type}

/-- L re-indexed along f and g, with its three honest provers replaced. -/
def swapL (L : HolographicProtocol I X) (f : I' → I) (g : I → Option I')
    (hT : Honest L.offline (I' × L.EncodingRandomness × L.OutOfDomainSeed))
    (hL : Honest L.link (I' × (L.EncodingRandomness × L.OutOfDomainSeed) × (L.EncodingRandomness × L.OutOfDomainSeed)))
    (hB : BatchHonestProver L.onlineBatch (I' × L.EncodingRandomness × L.OutOfDomainSeed)) : HolographicProtocol I' X :=
  { reIndex L f g with honestOfflineProver := hT, honestLinkProver := hL, honestOnlineBatchProver := hB }

/-- Its verifier's side is L's. -/
theorem v_swapL (L : HolographicProtocol I X) (f : I' → I) (g : I → Option I')
    (hT : Honest L.offline (I' × L.EncodingRandomness × L.OutOfDomainSeed))
    (hL : Honest L.link (I' × (L.EncodingRandomness × L.OutOfDomainSeed) × (L.EncodingRandomness × L.OutOfDomainSeed)))
    (hB : BatchHonestProver L.onlineBatch (I' × L.EncodingRandomness × L.OutOfDomainSeed)) : (swapL L f g hT hL hB).v = L.v := rfl

/-- At L's own provers, read through f, it is the re-indexed object. -/
theorem swapL_reIndex (L : HolographicProtocol I X) (f : I' → I) (g : I → Option I') :
    swapL L f g (reW L.honestOfflineProver (onFst f)) (reW L.honestLinkProver (onFst f)) (reWB L.honestOnlineBatchProver (onFst f)) = reIndex L f g :=
  rfl

end General

section Input
variable (r : InnerCompilerInput) {I' : Type} (f : I' → r.Index) (g : r.Index → Option I')
  (hT : Honest r.protocol.offline (I' × r.protocol.EncodingRandomness × r.protocol.OutOfDomainSeed))
  (hL : Honest r.protocol.link (I' × (r.protocol.EncodingRandomness × r.protocol.OutOfDomainSeed) × (r.protocol.EncodingRandomness × r.protocol.OutOfDomainSeed)))
  (hB : BatchHonestProver r.protocol.onlineBatch (I' × r.protocol.EncodingRandomness × r.protocol.OutOfDomainSeed))
  (next : I' → List Token → Option Token) (ISK : Type)
  (commit : I' → Rom.OComp (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits))
    (KeyRoot 256 (swapL r.protocol f g hT hL hB) × ISK))
  (prove : ISK → (b : List (r.Instance × Unit)) →
    Rom.OComp (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits))
      (ZKCP.Gen.Slots (OfflineLinkOnlineProof 256 (swapL r.protocol f g hT hL hB) r.offlineRoundSplits r.linkRoundSplits) b))

/-- The input r with its object replaced. What the verifier reads is r's own. -/
def swapIn : InnerCompilerInput where
  Index := I'
  Instance := r.Instance
  protocol := swapL r.protocol f g hT hL hB
  LeafBody := r.LeafBody
  offlineRoundSplits := r.offlineRoundSplits
  linkRoundSplits := r.linkRoundSplits
  queryLayout := r.queryLayout
  seedQueries := OutOfDomainSampleQueryLayout.ofV r.seedQueries.v
  answerCode := r.answerCode
  fixedSample := r.fixedSample
  compilerParameters := r.compilerParameters
  oracleCoding := r.oracleCoding
  keyCode := fun k => r.keyCode (KeyRoot.ofV k.v)
  buildInstance := r.buildInstance
  nextToken := next
  ProverKey := ISK
  commit := commit
  prove := prove
  coinBound := r.coinBound
  fallbackProof := (KeyRoot.ofV r.fallbackProof.1.v, OfflineLinkOnlineProof.ofV r.fallbackProof.2.v)

/-- **The two inputs have one verifier's side**: by unfolding. -/
theorem toInputV_swapIn :
    (swapIn r f g hT hL hB next ISK commit prove).toInputV = r.toInputV := rfl

/-- **The compiled verifier at the replaced object is the compiled verifier at r.** The key and the
proof are passed through their verifier's side: field by field the same values. -/
theorem innerCompiledVerifier_swapIn (commitment : Commitment) (prompt output : List Token)
    (proof : (innerSystem (swapIn r f g hT hL hB next ISK commit prove)).Proof) :
    innerCompiledVerifier (swapIn r f g hT hL hB next ISK commit prove) commitment prompt output proof =
      innerCompiledVerifier r commitment prompt output
        (proof.1, KeyRoot.ofV proof.2.1.v, OfflineLinkOnlineProof.ofV proof.2.2.v) := by
  rw [innerCompiledVerifier_eq, innerCompiledVerifier_eq]
  rfl

end Input

/-! ## 2. At three protocols over any configuration, and at Z -/

section Files
variable {C : ConfigurationWithOutOfDomainSample} (F : Files C) (P₀ : F.Provers) (p : C.I → Prop) (P : F.Provers)

/-- **The cut object with any provers P is the library's object with any provers P₀, re-indexed,
with the provers replaced**: by unfolding. -/
theorem swapL_obj :
    swapL (F.withProvers P₀) (Subtype.val : {i // p i} → C.I) (back p) (reW P.hT (onFst Subtype.val))
        (reW P.hL (onFst Subtype.val)) (reWB P.hB (onFst Subtype.val)) =
      cut (F.withProvers P) p := rfl

variable (T : InnerCompilerInputFieldsOverThreeProtocols F P₀) (next : {i // p i} → List Token → Option Token) (ISK : Type)
  (commit : {i // p i} → Rom.OComp (typedOracleFamily 256 T.W.K (typedOracleCarrier (F.withProvers P₀) T.Bd F.annT F.annL))
    (KeyRoot 256 (cut (F.withProvers P) p) × ISK))
  (prove : ISK → (b : List (C.X × Unit)) →
    Rom.OComp (typedOracleFamily 256 T.W.K (typedOracleCarrier (F.withProvers P₀) T.Bd F.annT F.annL))
      (ZKCP.Gen.Slots (OfflineLinkOnlineProof 256 (cut (F.withProvers P) p) F.annT F.annL) b))

/-- The library's input at three protocols F, provers P₀ and letters T (`innerInputOfThreeProtocols`,
Johnson/Flat/InnerInputOfThreeProtocols.lean), with its object replaced by `cut (F.withProvers P) p`. -/
def inputCut : InnerCompilerInput :=
  swapIn (innerInputOfThreeProtocols F P₀ T) (Subtype.val : {i // p i} → C.I) (back p)
    (reW P.hT (onFst Subtype.val)) (reW P.hL (onFst Subtype.val)) (reWB P.hB (onFst Subtype.val))
    next ISK commit prove

/-- Its object is `cut (F.withProvers P) p`. -/
theorem inputCut_L : (inputCut F P₀ p P T next ISK commit prove).protocol = cut (F.withProvers P) p := rfl

/-- **The compiled verifier at the cut object with any provers P is the compiled verifier at the
library's input with the provers P₀.** -/
theorem innerCompiledVerifier_cut (commitment : Commitment) (prompt output : List Token)
    (proof : (innerSystem (inputCut F P₀ p P T next ISK commit prove)).Proof) :
    innerCompiledVerifier (inputCut F P₀ p P T next ISK commit prove) commitment prompt output proof =
      innerCompiledVerifier (innerInputOfThreeProtocols F P₀ T) commitment prompt output
        (proof.1, KeyRoot.ofV proof.2.1.v, OfflineLinkOnlineProof.ofV proof.2.2.v) :=
  innerCompiledVerifier_swapIn (innerInputOfThreeProtocols F P₀ T) _ _ _ _ _ next ISK commit prove commitment prompt output
    proof

end Files

/-- The library's input at any letters T of the full size is `innerInputOfThreeProtocols` at `T.letters`: by
definition. So `innerCompiledVerifier_cut` at F := `filesAt Z`, P₀ := the library's own provers, p := `inRange`
and `T.letters` speaks of `objAt Z P` (which is `cut ((filesAt Z).withProvers P) inRange` by definition) and
of that input. -/
theorem input_eq_describe (Z : PublicFiles)
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize (dataAtFiles flashProveData Z).A (dataAtFiles flashProveData Z).E (dataAtFiles flashProveData Z).DK
      (dataAtFiles flashProveData Z).DP (dataAtFiles flashProveData Z).runK (dataAtFiles flashProveData Z).runP PV.EntryFive.dsF
      PV.EntryFive.xsF (dataAtFiles flashProveData Z).dec (dataAtFiles flashProveData Z).G.rec₀ (dataAtFiles flashProveData Z).G.z₀.2
      (LPFD.Full.sBG (dataAtFiles flashProveData Z).G).logLeaves (dataAtFiles flashProveData Z).G.early
      (LPFD.Full.saltG (dataAtFiles flashProveData Z).G)
      (LPFD.Full.KF (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).DP) (dataAtFiles flashProveData Z).P) :
    innerCompilerInputAtFullSize T = innerInputOfThreeProtocols (filesAt Z) (dataAtFiles flashProveData Z).P T.letters := rfl

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.inputCut_L
#print axioms AtPublicFiles.AtFiles.innerCompiledVerifier_cut
#print axioms AtPublicFiles.AtFiles.input_eq_describe
#print axioms AtPublicFiles.AtFiles.v_swapL
#print axioms AtPublicFiles.AtFiles.swapL_reIndex
#print axioms AtPublicFiles.AtFiles.toInputV_swapIn
#print axioms AtPublicFiles.AtFiles.innerCompiledVerifier_swapIn
#print axioms AtPublicFiles.AtFiles.swapL_obj
