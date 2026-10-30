-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
WHAT IS LACKING STANDS IN NAMED PREMISES, NOT PROVED.
E2E/KeySharedThread.lean: the shared chain's thread at a key file, as the proof file's shared chain
has it: the thread `Letters.thread` (Johnson/Desc/ProofFile/Honest/Thread/Shared.lean) with the
letters that the linear claim's own maker `letters2` lays
(Johnson/Desc/ProofFile/Honest/K14/Thread2.lean), at the key file's description.

Why. The laws of the linear claim's eight shared rounds are stated at `Letters.thread`. This file
says what that thread is at a key file, so that those laws can be called there.

Main names.
  `parKey`, `sentKey`: the linear claim's parameters at the key, and what goes out with the
    sending of o_u, as a term.
  `othersKey`: what `letters2` does not lay: the key's planner's values as `keyAsProof` writes them,
    the two proximity tests, the closing block, the key prover's halves and stored table, and the
    letters that stay.
  `lettersKey`, `threadKey`: the letters, and the thread at the description's own types.
  `sits_two`: the thread stands where the rule for a file asks the shared chain's thread to stand.
  `start_key`: its first state is the description's own start of that chain.
  `asked_key`: the nine equations that the linear claim asks of its letters.
  `plan_key`: in the goals' scope, the claim's public premises hold at these parameters.

What stays a letter. How a witness is read (`ℓ`), the table's numbers, the meaning of the fields
that the linear claim does not lay, the trees' tables, the witness outside the claim's messages,
what a sub-protocol keeps outside the claim's eight, and, of which inputs are meant, `Vd` alone.
`valid` is laid as `v = w ∧ Vd v`: it fixes the input at one letter `w`, with its index, the
committer's coins and the key, where Honest/Thread/Thr.lean's head means `valid` to bear no clause
on these. So whatever stands behind this thread at a border, or behind its `valid`, ties `w` to the
coins: E2E/KeySharedQuiet.lean's head. No statement of this file does.

Not claimed. That this thread holds at any run. That the letters can be met together. Anything of
the key file's first or last chain, or of the joint between the chains. The value `keyAsProof c` is
made up: it is no planner's answer. Nothing on soundness, completeness or hiding.

-/
import E2E.KeyProver
import E2E.KeyThreadBase
import E2E.KeyShapeSharedTies
import Johnson.Desc.Key.Desc
import Johnson.Desc.Key.SharedChainIsChainOf
import Johnson.Desc.ProofFile.Honest.K14.LettersVar
import Johnson.Desc.ProofFile.Honest.K14.Holds2

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace AtPublicFiles.KeySharedThread
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey OracleNotice)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source LaterPlaces Claim sharedPar beforeSharedPoint sharedTests
  keyAsProof)
open _root_.Desc.K14 (P14 St)
open AtPublicFiles.KeyFile (KeyParts keyProver randK14)
open AtPublicFiles.KeyThread (fixedOwn decl₂)

/-- The linear claim's parameters at the key. -/
abbrev parKey (Xs : Source) (Pl : LaterPlaces) : P14 :=
  sharedPar Xs.chains (beforeSharedPoint Pl)

/-- What goes out with the sending of o_u, as a term; the first mask of the test on G_u is among
it. The empty array where the shape cannot say it: not so in the goals' scope (`plan_key`). -/
def sentKey (Xs : Source) (Pl : LaterPlaces) : Array OracleNotice :=
  (_root_.Desc.K14.withU (parKey Xs Pl).S).getD #[]

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tb : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)

/-- The reader of the committer's coins that the key prover's two sendings read. -/
def randKey (c : Rc) : TableRand := randK14 (K.rand c)

/-- **What the linear claim's maker does not lay, at the key.** -/
def othersKey : Others Bk W₀ Rc X₀ P₁ Wt where
  lens := ℓ
  c := keyAsProof Xs.chains
  tests := sharedTests Pl
  last := VerifiableInference.Desc.K12.Seat.last
  N := Nm
  Mg₀ := Mg₀
  shape := fun _ _ => true
  nothingLeft := fun _ => true
  hs := (keyProver K).shared
  table := tb
  fixed := fixedOwn (decl₂ (VerifiableInference.Desc.Key.descriptionFromSource Xs Nr Pl))
  stored := fun v => (keyProver K).storedWords v.w₀ v.rc
  n₁ := 6
  n₂ := 11
  valid := fun v => v = w ∧ Vd v
  keeps := Kp
  rides := fun _ _ _ => True
  holds := holds2 (parKey Xs Pl) K.weights (randKey K)
  rest := rest

/-- **The shared chain's letters at the key.** -/
def lettersKey : SharedThread.Letters Bk St Claim W₀ Rc TableKey X₀ P₁ Wt :=
  letters2 (parKey Xs Pl) (sentKey Xs Pl) (othersKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w) Claim

/-- **The shared chain's thread at the key**, at the types of the description. -/
def threadKey :
    Thread Bk (VerifiableInference.Desc.Key.descriptionFromSource Xs Nr Pl).S₂
      (VerifiableInference.Desc.Key.descriptionFromSource Xs Nr Pl).Cl Empty (Common W₀ Rc TableKey) X₀ TableKey :=
  (lettersKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).thread

/-- **The thread stands where the rule for a file asks the shared chain's thread to stand**: the
field `two` of `Sits`, at the key's description and the key's prover. -/
theorem sits_two :
    (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).φ = .shared ∧
      (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).chain = 1 ∧
      (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).ft = 0 ∧
      (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).bs =
        (VerifiableInference.Desc.Key.descriptionFromSource Xs Nr Pl).shared.blocksInOrder ∧
      (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).hs = (keyProver K).shared :=
  ⟨rfl, rfl, rfl,
    (VerifiableInference.Desc.Key.sharedChain_flat_eq_chainOf_flat Xs.chains Pl Claim).symm, rfl⟩

/-- **The chain's first state is the description's own start of it**, at every instance. -/
theorem start_key (x : VerifiableInference.Desc.Key.Xi) :
    (VerifiableInference.Desc.Key.descriptionFromSource Xs Nr Pl).start₂ x =
      (lettersKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).first x.key := rfl

/-- **What the linear claim asks of its letters**, at the key: its nine equations. -/
theorem asked_key :
    Asked ℓ (lettersKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w) (parKey Xs Pl) (sentKey Xs Pl)
      (keyAsProof Xs.chains) (sharedTests Pl) VerifiableInference.Desc.K12.Seat.last
      (holds2 (parKey Xs Pl) K.weights (randKey K)) :=
  asked_letters2 (parKey Xs Pl) (sentKey Xs Pl)
    (othersKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w) Claim

end

/-- **The claim's public premises hold at the key's parameters**, in the goals' scope. -/
theorem plan_key {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {Nr : H2U.PlaceNums} {Pl : LaterPlaces}
    (hs : AtPublicFiles.AtFiles.KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true) :
    ∃ layO, Plan2 (parKey Xs Pl) (sentKey Xs Pl) layO := by
  unfold sentKey parKey
  rw [AtPublicFiles.AtFiles.Full.par_sourced hs scope]
  exact AtPublicFiles.AtFiles.Full.plan2_full

end AtPublicFiles.KeySharedThread

#print axioms AtPublicFiles.KeySharedThread.sits_two
#print axioms AtPublicFiles.KeySharedThread.start_key
#print axioms AtPublicFiles.KeySharedThread.asked_key
#print axioms AtPublicFiles.KeySharedThread.plan_key
