-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/InnerCompiledVerifierYesBack.lean: FROM THE PARTS' YES TO THE VERIFIER's: the converse of
`innerCompiledVerifier_yes` (Johnson/Top/InnerCompiledVerifierYes.lean), and the yes of the compiled verifier at the key
(root, OOD sample) from its six parts.

Why. A statement that an honest proof is accepted ends at `innerCompiledVerifier r`, evaluated at a hash
function. What a prover's theorem gives is the yes of each compiled verifier of a slot, at the typed
oracle functions that are read out of that hash function. Between the two stand equations that the
library has:
`OnBytes.K.VCA_det` (Johnson/Top/TieInnerCompiledVerifier.lean: the run of verifyAtFullKey at a key with one entry is the
"and" of its six runs), `seedIs_det` (Johnson/TypedOracleCompiler/RecCompile/SeedDet.lean), `innerCompiledVerifier_written`
(Johnson/Top/InnerCompiledVerifierSide.lean), `det_ofRom`, `det_overOne`. Here they are read from right to
left.
  `vra_yes_of_six`: the stored copy's number passes; both OOD seeds are the ones that the seed
    queries at their roots give; the key's test, the link and the session say yes: so verifyAtKeyRoot says yes.
  `innerCompiledVerifier_yes_of`: the instance is built, the key's code hashes to the commitment, verifyAtKeyRoot says yes:
    so innerCompiledVerifier says yes. `innerCompiledVerifier_yes_iff`: with `innerCompiledVerifier_yes`, both ways.
Kin. `vca_yes_of_parts`, `vra_det_key` (Johnson/Top/Fire/KeyArmIsPart.lean [not in this library])
say the first with the
key file's arm as one part. Limits. No probability: no completeness follows. The proof is a typed
one: nothing on a file's bytes. Nothing here says that any prover's strings meet the premises.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Top.InnerCompiledVerifierYes
import Johnson.Top.TieInnerCompiledVerifier
import Johnson.TypedOracleCompiler.RecCompile.SeedDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable (r : InnerCompilerInput)

/-- **Six yeses, so the yes of the compiled verifier at the key (root, OOD sample).** -/
theorem vra_yes_of_six (g : Fam (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits))) (cm : Dig 256)
    (c : r.protocol.Rec) (πT : OneProtocolProof 256 (batTC r.protocol r.offlineRoundSplits)) (cmj : Dig 256) (cj : r.protocol.Rec)
    (πL : OneProtocolProof 256 (batLC r.protocol r.linkRoundSplits)) (x : r.Instance) (n : ℕ) (πB : OneProtocolProof 256 r.protocol.onlineBatch)
    (hn : r.seedQueries.num n πB.plains = true) (h0 : c.1 = seedOfRoot r.queryLayout r.seedQueries g cm)
    (hj : cj.1 = seedOfRoot r.queryLayout r.seedQueries g cmj) (hT : (verifyOfflineProof r.queryLayout r.answerCode r.compilerParameters cm c πT).det g = true)
    (hL : (verifyLinkProof r.queryLayout r.answerCode r.compilerParameters cm cmj c cj πL).det g = true)
    (hB : (verifyOnlineProof r.queryLayout r.answerCode r.fixedSample r.compilerParameters cmj x cj πB).det g = true) :
    (verifyAtKeyRoot r.queryLayout r.seedQueries r.answerCode r.fixedSample r.compilerParameters ⟨cm, c⟩ x ⟨n, some πT, (cmj, cj, some πL), some πB⟩).det g =
      true := by
  show (verifyAtFullKey r.queryLayout r.seedQueries r.answerCode r.fixedSample r.compilerParameters ⟨cm, c, some πT, [(cmj, cj, some πL)]⟩ x
    ⟨0, n, some πB⟩).det g = true
  rw [OnBytes.K.VCA_det, hn, (seedIs_det r.queryLayout r.seedQueries g cm c.1).2 h0, (seedIs_det r.queryLayout r.seedQueries g cmj cj.1).2
      hj, hT, hL,
    hB]
  rfl

/-- **The converse of `innerCompiledVerifier_yes`.** -/
theorem innerCompiledVerifier_yes_of (hash : Hash) (commitment : Commitment) (prompt output : List Token)
    (proof : (innerSystem r).Proof) {x : r.Instance} {code : ZKCP.Str}
    (hb : r.buildInstance (prompt, output) proof.1 = some x) (he : r.keyCode proof.2.1 = some code)
    (hc : hash code = commitment)
    (hv : (verifyAtKeyRoot r.queryLayout r.seedQueries r.answerCode r.fixedSample r.compilerParameters proof.2.1 x proof.2.2).det
      (readBlocks r.oracleCoding (Run.famOne hash)) = true) :
    (innerCompiledVerifier r commitment prompt output proof).evaluate hash = true := by
  rw [innerCompiledVerifier_written, evaluate_deterministicOf_det]
  unfold ZKCP.verifyBuilt
  simp only [hb]
  unfold ZKCP.verifyDigestKey
  simp only [he]
  show (if hash code = commitment then
      Rom.ofRom ((verifyAtKeyRoot r.queryLayout r.seedQueries r.answerCode r.fixedSample r.compilerParameters proof.2.1 x proof.2.2).overOne r.oracleCoding)
      else ZKCP.OComp.pure false).det hash = true
  rw [if_pos hc, Run.det_ofRom, Rom.det_overOne]
  exact hv

/-- Both ways. -/
theorem innerCompiledVerifier_yes_iff (hash : Hash) (commitment : Commitment) (prompt output : List Token)
    (proof : (innerSystem r).Proof) :
    (innerCompiledVerifier r commitment prompt output proof).evaluate hash = true ↔
      ∃ x code, r.buildInstance (prompt, output) proof.1 = some x ∧ r.keyCode proof.2.1 = some code ∧
        hash code = commitment ∧
        (verifyAtKeyRoot r.queryLayout r.seedQueries r.answerCode r.fixedSample r.compilerParameters proof.2.1 x proof.2.2).det
          (readBlocks r.oracleCoding (Run.famOne hash)) = true :=
  ⟨innerCompiledVerifier_yes r hash commitment prompt output proof,
    fun ⟨_, _, hb, he, hc, hv⟩ => innerCompiledVerifier_yes_of r hash commitment prompt output
        proof hb he hc hv⟩

end VerifiableInference.OnPublicFiles
