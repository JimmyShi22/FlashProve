-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/AskAllLaws.lean: the one term of Johnson/RunOne/AskAll.lean (verifyAllAskSmall) is
the "and" of its parts, and the form that runs has its value. Proofs. What a yes of the term holds:
Johnson/RunOne/AskAllYes.lean.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

Main names.
  verifyAllAskSmall_parts: the one term is the "and" of its parts. No premise.
  verifyAllAskRun_eq: verifyAllAskRun H U G = verifyAllAskSmall H U G. No premise. By the two ends'
    own laws: verifyKeyAskRun_eq (Johnson/RunOne/AskKeyLaws.lean); verifyProofAskSmall_parts and
    verifyProofAskSmallPartsT_eq (Johnson/RunOne/AskProof.lean).
  tests_upTo: the tests up to the first no all say yes just where verifyAllAskRun says yes.

Limits. Nothing is said of what the three checks or the joins mean: see their own files. That the
run with its print (tellAll, in IO) returns upToNo's list is by the two texts. Nothing on soundness.
The program does not import this file.


-/
import Johnson.RunOne.AskAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Ask.All
open OnBytes OnBytes.Maker

/-- **The one term is its parts' "and".** No premise. -/
theorem verifyAllAskSmall_parts (H : ByteArray → ByteArray) (U : User) (G : Given) :
    verifyAllAskSmall H U G = (verifyAllAskSmallParts H U G).all fun x => x.2 := by
  unfold verifyAllAskSmall verifyAllAskSmallParts
  rw [List.all_map]
  rfl

/-- The proof file's check in the form that runs is the check. -/
theorem proofEnd_eq (H : ByteArray → ByteArray) (F : Proof.Files) :
    (fun k => (Proof.verifyProofAskSmallPartsT H F k).all fun x => x.2) =
      Proof.verifyProofAskSmall H F := by
  funext k
  rw [Proof.verifyProofAskSmallPartsT_eq, ← Proof.verifyProofAskSmall_parts]

/-- The key file's check in the form that runs is the check. -/
theorem keyEnd_eq (Kn : Nat) (H : ByteArray → ByteArray) (U : Key.User) :
    Key.verifyKeyAskRun Kn H U = Key.verifyKeyAskSmall Kn H U := by
  funext k
  exact Key.verifyKeyAskRun_eq Kn H U k

/-- **What runs has the one term's value.** No premise. -/
theorem verifyAllAskRun_eq (H : ByteArray → ByteArray) (U : User) (G : Given) :
    verifyAllAskRun H U G = verifyAllAskSmall H U G := by
  unfold verifyAllAskRun testsRun verifyAllAskSmall
  rw [proofEnd_eq, keyEnd_eq]

/-- The tests up to the first no all say yes just where the form that runs says yes. -/
theorem tests_upTo (H : ByteArray → ByteArray) (U : User) (G : Given) :
    ((upToNo (testsRun H U G)).all fun x => x.2) = verifyAllAskRun H U G :=
  upToNo_all _

end Johnson.RunOne.Ask.All

#print axioms Johnson.RunOne.Ask.All.verifyAllAskSmall_parts
#print axioms Johnson.RunOne.Ask.All.verifyAllAskRun_eq
#print axioms Johnson.RunOne.Ask.All.tests_upTo
