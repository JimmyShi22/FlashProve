-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Axioms.lean

Prints the axioms under every theorem of Bridge, Checks, Agreement, AgreementZeroKnowledge and
Steps, under the definition of each statement of Statements.lean, and under the two theorems of
IntegerModel/ that tie a true request, and the library's own program, to the model function
(`IntegerModel.isModelOutput_of_isTrueRequest`, `modelNextToken_eq_nextToken`).
These six files of VerifiableInference/ print nothing themselves. Every other file of
VerifiableInference/ that proves theorems prints the axioms of all its own theorems at its end.
The axioms printed for a theorem are those of everything that its proof uses: so the lines for the
theorems of VerifiableInference/ cover what they use of IntegerModel/ and of the rest of the
library.
A `#print axioms` line only prints: the file compiles whatever the lists hold. scripts/check.py,
when it is run, audits in its step `build` the axioms of every declaration of the library, printed
or not.
-/
import VerifiableInference.AgreementZeroKnowledge
import VerifiableInference.Steps
import IntegerModel.ModelOutput
import IntegerModel.Arrays.SameModel

#print axioms VerifiableInference.DeterministicAlgorithm.run_toRandomized
#print axioms VerifiableInference.ArgumentSystem.run_verify
#print axioms VerifiableInference.sound_of_soundAndBinding
#print axioms VerifiableInference.soundOpened_of_soundAndBinding
#print axioms VerifiableInference.rejectAll_soundAndBinding
#print axioms VerifiableInference.rejectAll_sound
#print axioms VerifiableInference.acceptAll_complete
#print axioms VerifiableInference.Prob_eq_Pr
#print axioms VerifiableInference.complete_iff
#print axioms VerifiableInference.indexBinding_of_sound
#print axioms VerifiableInference.sound_of_indexBinding
#print axioms VerifiableInference.sound_iff
#print axioms VerifiableInference.zeroKnowledge_iff
#print axioms VerifiableInference.indexPrivacy_of_zeroKnowledge
#print axioms VerifiableInference.CompleteSoundZeroKnowledge.toIsZKCPArg
#print axioms VerifiableInference.complete_iff_completeOn
#print axioms VerifiableInference.Sound
#print axioms VerifiableInference.SoundAndBinding
#print axioms VerifiableInference.SoundOpened
#print axioms VerifiableInference.Complete
#print axioms VerifiableInference.ZeroKnowledge
#print axioms VerifiableInference.CompleteSoundZeroKnowledge
#print axioms VerifiableInference.MaliciousVerifier.toUpload_ofUpload
#print axioms VerifiableInference.MaliciousVerifier.queryBound_toUpload
#print axioms VerifiableInference.View.ofUpload_toUpload
#print axioms VerifiableInference.View.toUpload_ofUpload
#print axioms VerifiableInference.Simulator.toUpload_ofUpload
#print axioms VerifiableInference.chooserToUpload_ofUpload
#print axioms VerifiableInference.OComp_bind_assoc
#print axioms VerifiableInference.realSteps_toUpload
#print axioms VerifiableInference.simulatedSteps_eq
#print axioms VerifiableInference.realExperiment_toUpload
#print axioms VerifiableInference.prob_bind_pure_map
#print axioms VerifiableInference.Prob_realExperiment
#print axioms VerifiableInference.simulatedExperiment_eq
#print axioms VerifiableInference.statisticalDistance_views
#print axioms VerifiableInference.bitString_eq
#print axioms VerifiableInference.digest_eq
#print axioms VerifiableInference.hash_eq
#print axioms VerifiableInference.queryLog_eq
#print axioms VerifiableInference.uniformHash_eq
#print axioms VerifiableInference.eventProbability_eq
#print axioms VerifiableInference.statisticalDistance_eq
#print axioms VerifiableInference.RandomizedAlgorithm.ofUpload_toUpload
#print axioms VerifiableInference.RandomizedAlgorithm.toUpload_ofUpload
#print axioms VerifiableInference.RandomizedAlgorithm.run_toUpload
#print axioms VerifiableInference.RandomizedAlgorithm.queryBound_toUpload
#print axioms VerifiableInference.RandomizedAlgorithm.toUpload_bind
#print axioms VerifiableInference.RandomizedAlgorithm.toUpload_withQueryLog
#print axioms VerifiableInference.RandomizedAlgorithm.run_ofUpload
#print axioms VerifiableInference.RandomizedAlgorithm.run_ofUpload_withQueryLog
#print axioms VerifiableInference.RandomizedAlgorithm.run_toUpload_withTrace
#print axioms VerifiableInference.RandomizedAlgorithm.queryBound_ofUpload
#print axioms VerifiableInference.run_done
#print axioms VerifiableInference.run_bind
#print axioms VerifiableInference.measurable_eventProbability_run
#print axioms VerifiableInference.queryBound_map
#print axioms VerifiableInference.run_withQueryLog_map
#print axioms VerifiableInference.run_withQueryLog_fst
#print axioms VerifiableInference.run_withQueryLog_bind_fst
#print axioms VerifiableInference.Prob_congr_run
#print axioms VerifiableInference.Prob_eq_zero
#print axioms VerifiableInference.ind_le
#print axioms VerifiableInference.ind_le_add
#print axioms IntegerModel.isModelOutput_of_isTrueRequest
#print axioms VerifiableInference.modelNextToken_eq_nextToken
