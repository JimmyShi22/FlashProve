-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/SealLastPull.lean: one lemma, from a KeyData.lean (a file of this project that is not in this repository; not the library's OnBytes/Slice/KeyData.lean) to the letter, so that the plain road's files need not import the other road's rule (the proof is `rfl`: it reads no text of `sealLast`).
-/
import Johnson.Desc.Sound.TilesData

set_option autoImplicit false

namespace LPFD
open VerifiableInference.Desc (FileDescription)

/-- The test on the first chain's last block does not read the instances. -/
theorem sealLast_pull {Xi Xi' : Type} (f : Xi' → Xi) (F : FileDescription Xi) : (F.pull f).sealLast = F.sealLast := rfl

end LPFD

#print axioms LPFD.sealLast_pull
