--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeySilent.lean: THE TEST ON THE THREE ROUNDS WITHOUT A CHALLENGE ACCEPTS WHAT
E2E/KeyHonest.lean's
`keySeam` LAYS, AT EVERY OOD SAMPLE WHOSE WRITTEN KEY HAS THE HONEST SAMPLE's LIST OF ANSWERS. One
statement with its proof, by unfolding. One test of the verifier's on values that are public behind
the key: NOTHING IS SHOWN OF ANY PROVER's PART IN A ROUND WITH A CHALLENGE: no completeness.

Why. E2E/KeyHonest.lean's `keySeam_silentK` speaks at the honest OOD sample itself. A caller that
holds an instance by a relation to the private input (E2E/KeyLink.lean's premise on this test) has
an OOD sample a of which it knows only what that relation says of the written key. The test reads of
the instance its key's list of answers alone.

  **`keySeam_silentK_of_answers`**: for every a whose written key's list of answers is the honest
    sample's: the library's test at a accepts the three values; the joining round's value may be
    taken at any value of the third chain's coin, which it does not read.
  `keySeam_silentK_of_key`: the same where the two written keys are equal.

Limits. That a relation gives the premise is its caller's to show.


-/
import E2E.KeyHonest

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.AtFiles
open OnBytes.Flat (RecFull)
open OnBytes.Slice (frS frZ DecR)
open VerifiableInference.Desc.Key (keyInstanceOfOutOfDomainSample)

section
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) {R₂ R₃ : Type} (val₂ : R₂ → ByteArray)
  (val₃ : R₃ → ByteArray)

theorem keySeam_silentK_of_answers (r2 : R₂) (r3 r3' : R₃) (i : (DecR.configurationOfStoredTable A R).I)
    (r : (DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) (e : (DecR.configurationOfStoredTable A R).Seed) (a : RecFull)
    (h : (keyInstanceOfOutOfDomainSample a).key.record.toList = (keyInstanceOfOutOfDomainSample (sampleOf A R i r e)).key.record.toList) :
    OnBytes.Flat.silK a ((keySeam A R val₂ val₃ r2 r3).front i r e (keyInstanceOfOutOfDomainSample a))
      ((keySeam A R val₂ val₃ r2 r3').join i r e)
      ((keySeam A R val₂ val₃ r2 r3).seam i r e (keyInstanceOfOutOfDomainSample a)) = true := by
  rw [silK_fun]
  simp [silKey, OnBytes.Maker.silentOf, keySeam, h]

theorem keySeam_silentK_of_key (r2 : R₂) (r3 r3' : R₃) (i : (DecR.configurationOfStoredTable A R).I)
    (r : (DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) (e : (DecR.configurationOfStoredTable A R).Seed) (a : RecFull)
    (h : (keyInstanceOfOutOfDomainSample a).key = (keyInstanceOfOutOfDomainSample (sampleOf A R i r e)).key) :
    OnBytes.Flat.silK a ((keySeam A R val₂ val₃ r2 r3).front i r e (keyInstanceOfOutOfDomainSample a))
      ((keySeam A R val₂ val₃ r2 r3').join i r e)
      ((keySeam A R val₂ val₃ r2 r3).seam i r e (keyInstanceOfOutOfDomainSample a)) = true :=
  keySeam_silentK_of_answers A R val₂ val₃ r2 r3 r3' i r e a (by rw [h])

end

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.keySeam_silentK_of_answers
#print axioms AtPublicFiles.AtFiles.keySeam_silentK_of_key
