-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/SharedChainIsChainOf.lean: a key file's shared chain, written as the general
shared chain `chainOf`.

Why. `chainOf` (Johnson/Desc/K14/Blocks.lean) makes a proof file's shared chain out of a planner's
record, and what is known of the letters of a shared chain is stated at `chainOf`. The key file's
`sharedChain` (Johnson/Desc/Key/Chains23.lean) lays the same blocks behind its front. Only the two
front blocks differ: `frontBlock` asks the tests `OkD.AtC.front2`, which are written over the
proof's half of the record, and `sharedFront` asks `sharedFrontOk`, which is written over the
key's half. So this file does not equate the two chains at the record c itself. It equates them
at the record `keyAsProof c`, for every c.

Main names.
  `keyAsProof`: the record c with the key's setting, codes, one-time sizes and shared chain's
  parameters laid into the proof's half.
  `front2_keyAsProof`, `frontBlock_keyAsProof`: there, the two fronts are one.
  `sharedChain_eq_chainOf`: the key's shared chain is `chainOf` there.
  `sharedChain_flat_eq_chainOf_flat`: the same of the two flat lists, at every `Cl : Type`.
  `front2_reads_proof_half`: a control: one change to the proof's half makes `front2` false and
  leaves `sharedFrontOk` as it was.

No theorem here has a premise.

What is not claimed. `keyAsProof c` is a made-up record: it is not made by a planner, and nothing
here says that a planner could give it. Nothing here says that either front's tests hold at any
record. The library does have a record at which the key's do: `Johnson.KB4.front_W`
(Johnson/HB/LLHARD/KB4/CFile.lean) proves `sharedFrontOk chainsW = true`, where `chainsW`
(Johnson/HB/LLHARD/KB4/SourceW.lean) is a closed term at the library's written values. This file
does not import those files or use that fact.

Of the structure `Asked` (Johnson/Desc/ProofFile/Honest/K14/LettersVar.lean) this file speaks only
to the right side of the one equation on the field `bs`, and of the other eight fields nothing is
said. It names no letters L: nothing here says that any key file's letters have the left side of
`sharedChain_flat_eq_chainOf_flat` as their `L.bs`. That step is the caller's.

`K14Asks` (Johnson/Desc/ProofFile/Honest/K14/Asks.lean) holds an `Asked` as its field `letters`.
Nothing is said of its other fields. Its `halves` and `sends` carry the record c too, which it
calls the planner's chains, and nothing here speaks to them at `keyAsProof c`. This file imports
neither `Asked` nor `K14Asks`, so the compiler checks none of what is said of them here: that
rests on reading those two files. Nothing of a key file's last chain.
Nothing on soundness, on an honest prover or on hiding.
-/
import Johnson.Desc.Key.Chains23

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key
open OnBytes OnBytes.Params VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Block roundlessBlock)

/-- **The key's numbers in the proof's place.** The record c, with the sized proof's setting, codes
and batch replaced by the sized key's setting, codes and one-time sizes, and the proof's shared
chain's parameters replaced by the key's. A made-up record: it is not made by a planner. -/
def keyAsProof (c : Model.Verify.Chains) : Model.Verify.Chains :=
  let z := c.made.sized.key
  { c with
    made := { c.made with sized := { c.made.sized with
      proof := { c.made.sized.proof with set := z.set, codes := z.codes, batch := z.once } } }
    proof := { c.proof with shared := c.key.shared } }

/-- A helper for `front2_keyAsProof`. Six tests joined by `&&` from the left say the same as a
list of the six, named, all of which hold. No premise. -/
theorem six_and_eq_all (a b d e f g : Bool) (n₁ n₂ n₃ n₄ n₅ n₆ : String) :
    (a && b && d && e && f && g) =
      [(n₁, a), (n₂, b), (n₃, d), (n₄, e), (n₅, f), (n₆, g)].all (·.2) := by
  cases a <;> cases b <;> cases d <;> cases e <;> cases f <;> cases g <;> rfl

/-- **The proof's front tests at `keyAsProof c` are the key's front tests at c.** Once unfolded,
they are the same terms clause by clause, in the same order. No premise. -/
theorem front2_keyAsProof (c : Model.Verify.Chains) :
    OkD.AtC.front2 (keyAsProof c) = sharedFrontOk c :=
  six_and_eq_all _ _ _ _ _ _ _ _ _ _ _ _

/-- **The proof's front block at `keyAsProof c` is the key's front block at c.** No premise. -/
theorem frontBlock_keyAsProof (c : Model.Verify.Chains) :
    _root_.Desc.K14.frontBlock (keyAsProof c) = sharedFront c := by
  have h := congrArg
    (fun b : Bool =>
      ({ roundlessBlock "the shared chain's front" 2 none 0 .ok with planOk := b } :
        Block _root_.Desc.K14.St Unit))
    (front2_keyAsProof c)
  exact h

/-- **The key file's shared chain is `chainOf` at `keyAsProof c`,** with the key's own parameters,
proximity tests and closing block. The parameters stand as `sharedPar`: no theorem here says
that they are `p14Of (keyAsProof c)` (Johnson/Desc/K14/Blocks.lean), the form that facts on a
proof file's shared chain use, as in Johnson/ToldDescR/SharedPlaces.lean. No premise. -/
theorem sharedChain_eq_chainOf (c : Model.Verify.Chains) (N : LaterPlaces) :
    sharedChain c N =
      _root_.Desc.K14.chainOf (keyAsProof c) (sharedPar c (beforeSharedPoint N)) (sharedTests N)
        VerifiableInference.Desc.K12.Seat.last := by
  have h := congrArg
    (fun b : Block _root_.Desc.K14.St Unit =>
      let inFront := _root_.Desc.K14.blocksOr (sharedPar c (beforeSharedPoint N)) ++ sharedTests N
      ({ first := b, front := [], links := [], back := inFront
         last := VerifiableInference.Desc.K12.Seat.last inFront } :
        Chain _root_.Desc.K14.St Unit))
    (frontBlock_keyAsProof c).symm
  exact h

/-- **The same of the flat lists**, at every `Cl : Type`. It is one rewrite by the theorem above:
it adds a form and no new fact. Its right side is the right side of the equation on the field
`bs` of the structure `Asked` (Johnson/Desc/ProofFile/Honest/K14/LettersVar.lean), at
c := `keyAsProof c`, Q := `sharedPar c (beforeSharedPoint N)`, tests := `sharedTests N` and
last := `K12.Seat.last`. No letters L are named here: the step from `L.bs` to the left side is
the caller's. No premise. -/
theorem sharedChain_flat_eq_chainOf_flat (c : Model.Verify.Chains) (N : LaterPlaces) (Cl : Type) :
    ((sharedChain c N).retype (Cl' := Cl)).blocksInOrder =
      ((_root_.Desc.K14.chainOf (keyAsProof c) (sharedPar c (beforeSharedPoint N)) (sharedTests N)
        VerifiableInference.Desc.K12.Seat.last).retype (Cl' := Cl)).blocksInOrder := by
  rw [sharedChain_eq_chainOf]

/-- The record c with the number of answers to a sample, in the plan of the proof's shared chain,
set to 2. A made-up record too, for the control below. -/
def proofSamplesTwo (c : Model.Verify.Chains) : Model.Verify.Chains :=
  { c with proof := { c.proof with shared := { c.proof.shared with
      given := { c.proof.shared.given with
        plan := { c.proof.shared.given.plan with samples := 2 } } } } }

/-- **A control: a change to the proof's half that the key's front tests do not see.** It makes
`front2` false and leaves `sharedFrontOk` as it was, at every c. This is one direction only: the
statement's first half alone does not show that `front2` reads the field, since a test that is
false at every record would meet it too. Wherever `sharedFrontOk c` is true, the record
`proofSamplesTwo c` is one at which these two tests differ. That rests on the condition, and the
record is made up, so nothing here follows of a planner's own record. No premise. This file
shows no record at which `sharedFrontOk` is true. The library has one: `Johnson.KB4.front_W`
(Johnson/HB/LLHARD/KB4/CFile.lean) proves
`sharedFrontOk chainsW = true`. This file does not import it. -/
theorem front2_reads_proof_half (c : Model.Verify.Chains) :
    OkD.AtC.front2 (proofSamplesTwo c) = false ∧
      sharedFrontOk (proofSamplesTwo c) = sharedFrontOk c :=
  ⟨rfl, rfl⟩

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.six_and_eq_all
#print axioms VerifiableInference.Desc.Key.front2_keyAsProof
#print axioms VerifiableInference.Desc.Key.frontBlock_keyAsProof
#print axioms VerifiableInference.Desc.Key.sharedChain_eq_chainOf
#print axioms VerifiableInference.Desc.Key.sharedChain_flat_eq_chainOf_flat
#print axioms VerifiableInference.Desc.Key.front2_reads_proof_half
