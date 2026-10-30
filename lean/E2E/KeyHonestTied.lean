--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyHonestTied.lean: THE LETTERS OF E2E/KeyHonest.lean ARE THOSE OF E2E/TiedAtFiles.lean. Two
files name the honest OOD sample, the committed table, the written key and what the three rounds
without a challenge send: the first for the key file, at any configuration of the full size; the
second for the proof file, at the configuration with the format's encoder. Here: at that
configuration they are the same. Equations between definitions. NOTHING IS SHOWN OF ANY PROVER.

What is shown, at the configuration with the format's encoder (`Cf A Pad holdW`):
  `sampleOf_recAt`: the honest OOD sample. `tableOf_encAt`: the committed table. `keySeam_keyAt`:
    the key that `keySeam` writes. `keySeam_seamAt`: what the seam sends. All four by unfolding.
  `keySeam_frontAt`: what the front round sends is `frontAt` AT THE COPY's NUMBER 0.
    `keySeam_joinAt`: what the joining round sends. These two open the library's list of the answers
    of an OOD sample by name (it is marked irreducible).
  `sampleOf_recAt_atFiles`, `tableOf_encAt_atFiles`: the first two at three public files Z, at the
    letters at which E2E/KeyHonest.lean's section on Z lays them: by unfolding.

Limits. Definitions alone. The condition `Tied` of E2E/TiedAtFiles.lean is not stated for the key
file here.


-/
import E2E.KeyHonest
import E2E.TiedAtFiles

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles
open Iop Hiop
open OnBytes.Flat (relationsAndEncodingOfClaims RecFull codingHonest)
open OnBytes.Slice (frS frZ DecR)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc.Key (keyInstanceOfOutOfDomainSample)
open AtPublicFiles.Committed (Cf Coin recAt encAt keyAt frontAt joinAt seamAt AZ PadZ holdZ)
open VerifierAndGoals (PublicFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData)

section Enc
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X) (Pad : Type) [Fintype Pad]
  [Nonempty Pad] (holdW : A.Mat → Pad → ℕ → List UInt64)

/-- The honest OOD sample. -/
theorem sampleOf_recAt (i : (Cf A Pad holdW).I) (r : Coin A Pad holdW)
    (e : (Cf A Pad holdW).Seed) :
    sampleOf A (relationsAndEncodingOfClaims A (codingHonest frS frZ 402653181 A Pad holdW)) i r e =
      recAt A Pad holdW i r e := rfl

/-- The committed table. -/
theorem tableOf_encAt (DK : WholeD) (i : (Cf A Pad holdW).I) (r : Coin A Pad holdW)
    (e : (Cf A Pad holdW).Seed) :
    tableOf A (relationsAndEncodingOfClaims A (codingHonest frS frZ 402653181 A Pad holdW)) DK (i, r, e) =
      encAt A Pad holdW i r := rfl

variable {R₂ R₃ : Type} (val₂ : R₂ → ByteArray) (val₃ : R₃ → ByteArray) (r2 : R₂) (r3 : R₃)
  (i : (Cf A Pad holdW).I) (r : Coin A Pad holdW) (e : (Cf A Pad holdW).Seed)

/-- The written key. -/
theorem keySeam_keyAt :
    (keySeam A (relationsAndEncodingOfClaims A (codingHonest frS frZ 402653181 A Pad holdW)) val₂ val₃ r2 r3).keyOf i r
      e = keyAt (recAt A Pad holdW i r e) := rfl

/-- **The front round: at the copy's number 0.** -/
theorem keySeam_frontAt (x : KeyInst) :
    (keySeam A (relationsAndEncodingOfClaims A (codingHonest frS frZ 402653181 A Pad holdW)) val₂ val₃ r2 r3).front i r
      e x = frontAt (Xi := KeyInst) A Pad holdW 0 r2 r3 i r e x := by
  unfold frontAt OnBytes.Flat.ansL
  rfl

/-- The joining round. -/
theorem keySeam_joinAt :
    (keySeam A (relationsAndEncodingOfClaims A (codingHonest frS frZ 402653181 A Pad holdW)) val₂ val₃ r2 r3).join i r
      e = joinAt A Pad holdW val₂ r2 i r e := by
  unfold joinAt OnBytes.Flat.ansL
  rfl

/-- The seam. -/
theorem keySeam_seamAt (x : KeyInst) :
    (keySeam A (relationsAndEncodingOfClaims A (codingHonest frS frZ 402653181 A Pad holdW)) val₂ val₃ r2 r3).seam i r
      e x = seamAt (Xi := KeyInst) A Pad holdW val₃ r2 r3 i r e x := rfl

end Enc

/- As in E2E/TiedAtFiles.lean: the search for this instance runs out of time. -/
local instance (priority := high) : Nonempty PadZ := AtPublicFiles.Committed.pads_nonempty frS 402653181

/-- The honest OOD sample at Z's letters. -/
theorem sampleOf_recAt_atFiles (Z : PublicFiles) (i : (Cz Z).I) (r : (Cz Z).Pad × (Cz Z).Rnd)
    (e : (Cz Z).Seed) :
    sampleOf (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) i r e =
      recAt (AZ Z) PadZ (holdZ Z) i r e := rfl

/-- The committed table at Z's letters. -/
theorem tableOf_encAt_atFiles (Z : PublicFiles) (i : (Cz Z).I) (r : (Cz Z).Pad × (Cz Z).Rnd)
    (e : (Cz Z).Seed) :
    tableOf (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK (i, r, e) =
      encAt (AZ Z) PadZ (holdZ Z) i r := rfl

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.sampleOf_recAt
#print axioms AtPublicFiles.AtFiles.tableOf_encAt
#print axioms AtPublicFiles.AtFiles.keySeam_keyAt
#print axioms AtPublicFiles.AtFiles.keySeam_frontAt
#print axioms AtPublicFiles.AtFiles.keySeam_joinAt
#print axioms AtPublicFiles.AtFiles.keySeam_seamAt
#print axioms AtPublicFiles.AtFiles.sampleOf_recAt_atFiles
#print axioms AtPublicFiles.AtFiles.tableOf_encAt_atFiles
