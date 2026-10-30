-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/AtLaidLetters.lean: the linear claim (kind K14): THE STRUCTURE FiveAtBorder
(Johnson/Desc/ProofFile/Honest/Thread/FiveAtBorder.lean) AT THE MEMBERS 1 TO 8 OF THE SHARED CHAIN's
THREAD, AT A RETURN OF THE BASE MAKER (baseMaker, E2E/BaseMaker.lean), AT EVERY INPUT w, where the
letters that sharedParts leaves open (LaterLetters, Honest/Thread/TheLaterThreads.lean) have their
table and their fixed laid as tableShared and fixedShared.

  KeyIsTheCommitters  **the one premise on the run's input w, under a name**: where w's index is in
                      range, the key of w is one that the committer makes of w's index and coins at
                      some seed
  keyIsTheCommitters_made   it holds where the key of w is read off the library's explicit input
                            xiAt,
                      at every index, all coins, every seed and every pair of byte strings
  k14_five_shared_laid   **the five**

WHAT STAYS A PREMISE, beside the maker's return and the head at the return. htab, hfix: two
equations on the letters, which hold by unfolding at a value whose table is tableShared at the base
prover's two readers (at any two test jobs) and whose fixed is fixedShared at the written
description's declared rounds of the shared chain. late: every rider begins at border 10 or later:
the chain has one list of riders, so nothing rides at the borders 0 to 9. hw: KeyIsTheCommitters at
w.

NOT IN FRONT OF A LAW OVER COINS (the rule: Johnson/Bind/ForProver/FiveFieldsAt.lean's head). The
ground: w is a letter for a value, and hw ties its key to its coins: at a fixed key it holds at some
coins and fails at others (the first kind of premise). What lifts that bar: keyIsTheCommitters_made,
at the made term A.H.key (xiAt …); the seed stays a letter beside the coins. The thread's invariant,
from which each of the five starts, is a premise on the letters that are left (L's rest and riders,
the two test jobs, `Said`), which may read the coins: no lemma here shows it at every value of the
coins: there the bar is flat. "The index is in range" is of the second kind: it reads the hidden
index and no coin.

A LIMIT. THE BASE MAKER's PROVER IS NOT THE HONEST PROVER OF THE PROTOCOL: that one is made at the
filling onlineFilling, which is baseFilling read through, at another type of coins
(onlineFilling_eq, E2E/BaseMaker.lean). Nothing here carries the five over.

What is not claimed. That any premise holds at a run. That the thread's invariant holds at any
state. Nothing on completeness, soundness or hiding.
Terms. letter, border: lean/GLOSSARY.md. A thread is the invariant along a chain with its parameters
(Honest/Thread/Thr.lean). A member is a sub-protocol of a chain's flat list, numbered from 0.
-/
import AtFullSide.K14.AtBaseMaker
import AtFullSide.K14.FiveTabled

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K14
open OnBytes (TableKey)
open ProofFile.Honest ProofFile.Honest.K14
open ProofFile.Honest.Term (baseMaker matrixInput)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open ProofFile.Honest.FirstThread (HeadAtReturn LaterLetters sharedThread sharedParts)
open ProofFile.Honest.K12 (TestJob)
open ProofFile.Honest.K12.AtFile (tableShared fixedShared)
open Bind.ForProver (validAt shapeOf)
open Desc.K14 (St)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins ProofFile.Honest.Cells Unit Unit}

/-- **The premise on the run's input w**: where w's index is in range, the key of w is one that the
committer makes of w's index and coins, at some seed. -/
def KeyIsTheCommitters (A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins ProofFile.Honest.Cells Unit Unit)
    (w : Common FullSizeMatrix IndexCommitterCoins TableKey) : Prop :=
  A.H.inRange w.w₀ = true → validAt (shapeOf A.Z) A.Z ⟨matrixInput.weights A.Z w.w₀, w.rc, w.key⟩

/-- It holds where the key of w is read off the library's explicit input xiAt. -/
theorem keyIsTheCommitters_made (made : baseMaker files = .ok A) (w₀ : FullSizeMatrix) (rc : IndexCommitterCoins)
    (sd : Bind.ForProver.Seed (shapeOf A.Z) × ℕ) (bytes : ByteArray × ByteArray) :
    KeyIsTheCommitters A ⟨w₀, rc, A.H.key (Bind.ForProver.xiAt (shapeOf A.Z) A.Z
      ⟨matrixInput.weights A.Z w₀, rc, sd⟩ bytes)⟩ :=
  fun _ => validAt_made made (matrixInput.weights A.Z) w₀ rc sd bytes

/-- **FiveAtBorder at a member b, 1 ≤ b ≤ 8, of the shared chain's thread at sharedParts, at a
return of the base maker, at every input w.** htab: table is tableShared at the base prover's
readers. hfix: fixed is fixedShared at the written description's declared rounds. late: every rider
begins at border 10 or later. hw: the key of w is the committer's.
NOT IN FRONT OF A LAW OVER COINS: w is a letter and hw ties its key to its coins (the file's head).
-/
theorem k14_five_shared_laid (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (L : LaterLetters A) {JU JO : TestJob (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit}
    (htab : L.table = tableShared (qAt A.Z h.places) (matrixInput.weights A.Z)
      (randNow (qAt A.Z h.places)) JU JO ())
    (hfix : L.fixed = fixedShared P2Law.ProofPlan.declProofFull.2.1)
    (late : ∀ c ∈ L.riders, 10 ≤ c.lo) (w : Common FullSizeMatrix IndexCommitterCoins TableKey)
    (hw : KeyIsTheCommitters A w)
    (Said : Nat → Coins A.B → Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit → Prop)
    (fall : Nat → St → List Fmt.Drawn → Option String) (b : Nat) (hb1 : 1 ≤ b) (hb8 : b ≤ 8) :
    FiveAtBorder (sharedThread h ⟨matrixInput.weights A.Z, randNow (qAt A.Z h.places)⟩
      (sharedParts h L) w) Said fall b :=
  five_at_sharedThread matrixInput _ _ _ made h (sharedParts h L) w htab
    (by show L.fixed (.own 0) = 1; rw [hfix]; exact fixedShared_low.1)
    (fun i hi => by show L.fixed (.own (1 + i)) = 4; rw [hfix]; exact fixedShared_low.2 i hi)
    hw (cs := L.riders) (fun _ _ _ => Iff.rfl) late Said fall b hb1 hb8

end AtFullSide.K14

#print axioms AtFullSide.K14.keyIsTheCommitters_made
#print axioms AtFullSide.K14.k14_five_shared_laid
