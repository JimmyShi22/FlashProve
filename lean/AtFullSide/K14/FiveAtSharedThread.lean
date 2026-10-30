-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/FiveAtSharedThread.lean: the linear claim's shared rounds (kind K14): THE FIVE
STATEMENTS ON ONE SUB-PROTOCOL, AS THE STRUCTURE FiveAtBorder
(Johnson/Desc/ProofFile/Honest/Thread/FiveAtBorder.lean), AT THE MEMBERS 1 TO 8 OF THE TERM
sharedThread (Honest/Thread/TheFirstThread.lean): the shared chain's thread at a return of the maker
onlineProverFromPublicFiles; here at its return at the filling onlineProverPartsInUse, at any type of index, with the term's
two readers of the prover's input (IndexReaders) laid as the filling's: I.weights A.Z, and the
committer's pads and tails at the plan's item (randNow).

  five_at_sharedThread   **FiveAtBorder there**, at a run's input w that is a letter:
                         five_at_base_valid
                      (AtFullSide/K14/FiveValid.lean) at that term's letters
  five_at_sharedThread_made   **FiveAtBorder there AT THE COMMITTER's MADE INPUT**: the key of w is
                              what the
                      prover reads of the explicit input xiAt at the index, the coins and a seed: hv
                      is shown (validAt_made), at every index, all coins and every seed

WHAT IS ASKED OF sharedThread's OPEN PARTS (SharedThreadParts), as equations.
  htab                table is tableShared (Honest/K12/AtFile/TableShared.lean) at these readers, at
                      any two test jobs
  h0, h1              fixed is 1 at the chain's own tree 0, and 4 at its own trees 1 and 2
                      (fixedShared_low, AtFullSide/K14/FiveTabled.lean, has that of fixedShared at
                      the written rounds)
  hr, late            rides is a list of clauses that all begin at border 10 or later: so nothing
                      rides at the borders 0 to 9, nor in front of the member 9
lens, meaning, shape, rest and keeps stay free.

WHAT ELSE IS A PREMISE.
  hA, h               onlineProverFromPublicFiles returns A at the filling; the head at that return (HeadAtReturn: the
                      library's hypothesis at the full size, at A's public part)
  hv                  where the index of the run's input w is in range, the key of w is the key that
                      the committer makes of w's index and coins, at some seed (validAt,
                      Johnson/Bind/ForProver/FiveAt.lean)
`Said` and `fall` are free.

NOT IN FRONT OF A LAW OVER COINS (the rule: Johnson/Bind/ForProver/FiveFieldsAt.lean's head), of
five_at_sharedThread: w is a letter for a value and hv ties its key to its coins (the ground at
length: AtFullSide/K14/FiveValid.lean's head). This tie is of the first kind (it picks among the
coins). five_at_sharedThread_made BEARS THE LABEL TOO, with another ground: the tie of the key is
lifted there (the key is the term that the committer makes, and hv is shown at every value of the
coins by validAt_made), but the seed is a letter beside the coins, and the thread's invariant,
from which each of the five starts, is a premise on the letters table (its two test jobs), lens,
meaning, rest, shape, keeps and `Said`, which may read the coins. "The index is in range" is of the
second kind: it reads the hidden index and no coin, and a law over coins would have to name it.

What is not claimed. That any premise holds. That a run's explicit input is such an xiAt. That the
thread's invariant holds at any state: each of the five starts from it. Nothing on the members 0, 9,
10, 11. Nothing on completeness, soundness or hiding.
Terms. letter, border: lean/GLOSSARY.md. A thread is the invariant along a chain with its parameters
(Honest/Thread/Thr.lean). A member is a sub-protocol of a chain's blocksInOrder list, numbered from 0.
-/
import AtFullSide.K14.FiveValid
import Johnson.Desc.ProofFile.Honest.Thread.FiveAtBorder
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K14
open OnBytes (TableKey)
open ProofFile (SecondHashFunctionArgument)
open ProofFile.Honest ProofFile.Honest.K14
open ProofFile.Honest.FirstThread (HeadAtReturn SharedThreadParts sharedThread)
open ProofFile.Honest.K12 (TestJob)
open ProofFile.Honest.K12.AtFile (tableShared)
open Bind.ForProver (validAt shapeOf)
open Desc.K14 (St)

/-- **FiveAtBorder at a member b, 1 ≤ b ≤ 8, of sharedThread**, at the maker's return at the
filling. htab: table is tableShared at the filling's readers. h0, h1: fixed is 1 at own 0, and 4 at
own 1 and 2. hv: where w's index is in range, the key of w is the committer's. hr, late: rides is a
list of clauses that all begin at border 10 or later. NOT IN FRONT OF A LAW OVER COINS: w is a
letter and hv ties its key to its coins (the file's head). -/
theorem five_at_sharedThread {files : VerifierAndGoals.PublicFiles} {W₀ Wt : Type} (I : WiderIn W₀) (o' : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL (onlineProverPartsInUse I o' S O) = .ok A)
    (h : HeadAtReturn files A) (parts : SharedThreadParts A Wt) (w : Common W₀ IndexCommitterCoins TableKey)
    {JU JO : TestJob (Common W₀ IndexCommitterCoins TableKey) Unit}
    (htab : parts.table =
      tableShared (qAt A.Z h.places) (I.weights A.Z) (randNow (qAt A.Z h.places)) JU JO ())
    (h0 : parts.fixed (.own 0) = 1) (h1 : ∀ i, i < 2 → parts.fixed (.own (1 + i)) = 4)
    (hv : A.H.inRange w.w₀ = true →
      validAt (shapeOf A.Z) A.Z ⟨I.weights A.Z w.w₀, w.rc, w.key⟩)
    {cs : List (RiderCl (Common W₀ IndexCommitterCoins TableKey) St)}
    (hr : ∀ b v s, parts.rides b v s ↔ ridersOf cs b v s) (late : ∀ c ∈ cs, 10 ≤ c.lo)
    (Said : Nat → Coins A.B → Mid (Common W₀ IndexCommitterCoins TableKey) Unit → Prop)
    (fall : Nat → St → List Fmt.Drawn → Option String) (b : Nat) (hb1 : 1 ≤ b) (hb8 : b ≤ 8) :
    FiveAtBorder (sharedThread h ⟨I.weights A.Z, randNow (qAt A.Z h.places)⟩ parts w) Said fall
      b := by
  obtain ⟨lens, meaning, shape, rest, table, fixed, rides, keeps⟩ := parts
  dsimp only at htab h0 h1 hr
  subst htab
  obtain ⟨p, bh, ex, rp, ac⟩ := five_at_base_valid (ℓ := lens) (N := h.sharedNumbers)
    (nothingLeft := fun d => (Desc.K14.ended d).isSome) (fixed := fixed) (n₁ := h.description.t₁)
    (n₂ := h.description.t₂) h.head I o' S O hA (JU := JU) (JO := JO) (Mg₀ := meaning)
    (shape₀ := shape) (rest := rest) (Kp₀ := keeps) (Vd := fun v => A.H.inRange v.w₀ = true)
    (Rd := rides) (w := w) rfl rfl h0 h1 hv Said fall hr late b hb1 hb8
  exact ⟨p, bh, ex, rp, ac⟩

/-- **FiveAtBorder at a member b, 1 ≤ b ≤ 8, of sharedThread, at the committer's made input**: at
every index w₀, all coins rc, every seed sd and all bytes of the request. htab: table is tableShared
at the filling's readers. h0, h1: fixed is 1 at own 0, and 4 at own 1 and 2. hr, late: rides is a
list of clauses that all begin at border 10 or later. NOT IN FRONT OF A LAW OVER COINS: the seed is
a letter, and the invariant is a premise on letters that may read the coins (the file's head). -/
theorem five_at_sharedThread_made {files : VerifierAndGoals.PublicFiles} {W₀ Wt : Type} (I : WiderIn W₀)
    (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL (onlineProverPartsInUse I o' S O) = .ok A)
    (h : HeadAtReturn files A) (parts : SharedThreadParts A Wt) (w₀ : W₀) (rc : IndexCommitterCoins)
    (sd : Bind.ForProver.Seed (shapeOf A.Z) × ℕ) (bytes : ByteArray × ByteArray)
    {JU JO : TestJob (Common W₀ IndexCommitterCoins TableKey) Unit}
    (htab : parts.table =
      tableShared (qAt A.Z h.places) (I.weights A.Z) (randNow (qAt A.Z h.places)) JU JO ())
    (h0 : parts.fixed (.own 0) = 1) (h1 : ∀ i, i < 2 → parts.fixed (.own (1 + i)) = 4)
    {cs : List (RiderCl (Common W₀ IndexCommitterCoins TableKey) St)}
    (hr : ∀ b v s, parts.rides b v s ↔ ridersOf cs b v s) (late : ∀ c ∈ cs, 10 ≤ c.lo)
    (Said : Nat → Coins A.B → Mid (Common W₀ IndexCommitterCoins TableKey) Unit → Prop)
    (fall : Nat → St → List Fmt.Drawn → Option String) (b : Nat) (hb1 : 1 ≤ b) (hb8 : b ≤ 8) :
    FiveAtBorder (sharedThread h ⟨I.weights A.Z, randNow (qAt A.Z h.places)⟩ parts
      ⟨w₀, rc, A.H.key (Bind.ForProver.xiAt (shapeOf A.Z) A.Z ⟨I.weights A.Z w₀, rc, sd⟩ bytes)⟩)
      Said fall b :=
  five_at_sharedThread I o' S O hA h parts _ htab h0 h1
    (fun _ => validAt_made hA (I.weights A.Z) w₀ rc sd bytes) hr late Said fall b hb1 hb8

end AtFullSide.K14

#print axioms AtFullSide.K14.five_at_sharedThread
#print axioms AtFullSide.K14.five_at_sharedThread_made
