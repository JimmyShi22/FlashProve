-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/InnerCompiledVerifierYes.lean: where the verifier `innerCompiledVerifier r` (Johnson/Top/InnerCompiledVerifier.lean),
evaluated at a hash function, says yes: the instance is built, the key's code hashes to the
commitment, and the compiled verifier for an object with records says yes at the typed oracle
functions that are read out of that hash function.

Why. `VCA_yes` (Johnson/TypedOracleCompiler/RecCompile/YesGivesAccept.lean) speaks of the compiled verifier's value
at typed oracle functions. A run evaluates a verifier at one hash function. Between the two lie
layers that are equations proved in this library: `innerCompiledVerifier_written`
(Johnson/Top/InnerCompiledVerifierSide.lean), `det_ofRom`
(Run/RunIsVProofs.lean), `det_overOne` (Run/DetOverOne.lean).
  `evaluate_deterministicOf_det`: the deterministic algorithm of a tree evaluates to the tree's
  value.
  `innerCompiledVerifier_yes`: the first sentence above.
  `innerCompiledVerifier_yes_parts`: with `VCA_yes`: the key's test, the link and the session have each said yes
  at the transcript made of the proof and of what the chain has drawn; THE THREE PROOF STRINGS, THE
  ENTRY's ROOT AND ITS RECORD ARE THIS PROOF's OWN: three equations say where in the proof each
  stands.
  The like for the goals' own term `VerifierAndGoals.verify` stands in Johnson/Goal/VerifyYes.lean
  [not in this library] (a file of
  Johnson/Top/ may not reach the library VerifierAndGoals: scripts/IMPORTS.txt).
Limits. One direction. No probability: no soundness follows. The proof is a typed one: nothing on a
file's bytes.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.InnerCompiledVerifierSide
import Johnson.TypedOracleCompiler.RecCompile.YesGivesAccept
import Run.RunIsVProofs
import Run.DetOverOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference

/-- The deterministic algorithm of a tree evaluates to the tree's value. -/
theorem evaluate_deterministicOf_det {α : Type} (hash : Hash) :
    ∀ c : ZKCP.OComp 256 α, (deterministicOf c).evaluate hash = c.det hash
  | .pure _ => rfl
  | .query q k => evaluate_deterministicOf_det hash (k (hash q))
  | .sample _ k => evaluate_deterministicOf_det hash (k 0)

end VerifiableInference

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable (r : InnerCompilerInput)

/-- **A yes of `innerCompiledVerifier` at a hash function.** -/
theorem innerCompiledVerifier_yes (hash : Hash) (commitment : Commitment) (prompt output : List Token)
    (proof : (innerSystem r).Proof)
    (h : (innerCompiledVerifier r commitment prompt output proof).evaluate hash = true) :
    ∃ x code, r.buildInstance (prompt, output) proof.1 = some x ∧ r.keyCode proof.2.1 = some code ∧
      hash code = commitment ∧
      (verifyAtKeyRoot r.queryLayout r.seedQueries r.answerCode r.fixedSample r.compilerParameters proof.2.1 x proof.2.2).det
        (readBlocks r.oracleCoding (Run.famOne hash)) = true := by
  rw [innerCompiledVerifier_written, evaluate_deterministicOf_det] at h
  unfold ZKCP.verifyBuilt at h
  cases hb : r.buildInstance (prompt, output) proof.1 with
  | none =>
    simp only [hb] at h
    exact absurd h (by show ¬ (false = true); decide)
  | some x =>
    simp only [hb] at h
    unfold ZKCP.verifyDigestKey at h
    cases he : r.keyCode proof.2.1 with
    | none =>
      simp only [he] at h
      exact absurd h (by show ¬ (false = true); decide)
    | some code =>
      simp only [he] at h
      have h2 : (if hash code = commitment then
          Rom.ofRom ((verifyAtKeyRoot r.queryLayout r.seedQueries r.answerCode r.fixedSample r.compilerParameters proof.2.1 x proof.2.2).overOne r.oracleCoding)
          else ZKCP.OComp.pure false).det hash = true := h
      split at h2
      · rename_i hc
        rw [Run.det_ofRom, Rom.det_overOne] at h2
        exact ⟨x, code, rfl, rfl, hc, h2⟩
      · exact absurd h2 (by show ¬ (false = true); decide)

/-- **And its three slots.** -/
theorem innerCompiledVerifier_yes_parts (hash : Hash) (commitment : Commitment) (prompt output : List Token)
    (proof : (innerSystem r).Proof)
    (h : (innerCompiledVerifier r commitment prompt output proof).evaluate hash = true) :
    ∃ x πT cmj recj πL πB, r.buildInstance (prompt, output) proof.1 = some x ∧
      (proof.2.1.full proof.2.2).piT = some πT ∧
      (proof.2.1.full proof.2.2).links[proof.2.2.low.leaf]? = some (cmj, recj, some πL) ∧
      proof.2.2.low.piB = some πB ∧
      YesAt (readBlocks r.oracleCoding (Run.famOne hash)) Tag.test (batTC r.protocol r.offlineRoundSplits) (wTC r.queryLayout) id
        (fun _ => none) (cmsTA r.answerCode (proof.2.1.full proof.2.2).cm (proof.2.1.full proof.2.2).rcd.2)
        (proof.2.1.full proof.2.2).rcd πT ∧
      YesAt (readBlocks r.oracleCoding (Run.famOne hash)) Tag.link (batLC r.protocol r.linkRoundSplits) (wLC r.queryLayout) id
        (fun _ => none)
        (cmsLA r.answerCode (proof.2.1.full proof.2.2).cm cmj (proof.2.1.full proof.2.2).rcd.2 recj.2)
        ((proof.2.1.full proof.2.2).rcd, recj) πL ∧
      YesAt (readBlocks r.oracleCoding (Run.famOne hash)) Tag.onl r.protocol.onlineBatch (wBC r.queryLayout) id (xinBA r.fixedSample)
        (cmsBA r.answerCode cmj recj.2) (x, recj) πB := by
  obtain ⟨x, -, hx, -, -, hv⟩ := innerCompiledVerifier_yes r hash commitment prompt output proof h
  obtain ⟨πT, cmj, recj, πL, πB, e1, e2, e3, a, b, c⟩ :=
    VCA_yes r.queryLayout r.seedQueries r.answerCode r.fixedSample _ r.compilerParameters (proof.2.1.full proof.2.2) x proof.2.2.low hv
  exact ⟨x, πT, cmj, recj, πL, πB, hx, e1, e2, e3, a, b, c⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.innerCompiledVerifier_yes
#print axioms VerifiableInference.OnPublicFiles.innerCompiledVerifier_yes_parts
