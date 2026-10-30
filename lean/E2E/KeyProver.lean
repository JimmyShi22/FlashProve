--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyProver.lean: the honest prover of the key file's three chains, in the frame for the honest
side (`ProofFile.Honest.Prover`, Johnson/Desc/ProofFile/Honest/Frame.lean), AS A LIST OF HALVES AT THEIR
PLACES. Definitions, and equations that hold by unfolding. NOTHING IS SHOWN OF THIS PROVER: not that
a verifier accepts it, and nothing on what its messages show.

What the file is for: it is a test of TYPES. Each kind's half is the proof file's. Here
each is called at the key file's instance (`VerifiableInference.Desc.Key.Xi`: the key of a table;
there is no request and no trace), at the key's type `OnBytes.TableKey`, with its public data as
letters.

  `KeyInst`, `In1`, `In2`: the instance; what a half of the first or the second chain is handed;
    what a half of the shared chain is handed.
  `randK14`: the committer's coins for one table, field by field; the shared chain's two sendings
    read the frame's own type, so it returns what it is given.
  `KeyParts W₀ Rc X₀ X Wk`: all letters: the readers of the index and of the committer's coins; each
    place's public data; and FOUR HALVES THAT ARE LETTERS: the four proximity tests.
  `sharedChainProverSidesInOrder`: the shared chain's own halves and its two sendings, in the order of the places.
  **`keyProver K`**: the prover. First chain, seven halves: the index-mask message · the
    multiplicities · two lookups, at the owners that the key file's book names (below) · the proximity
    test on the ranges' group · the batching · W.
    Shared chain: the kind's own rounds and the two sendings, in the order of the places, then two
    proximity tests. Second chain: one proximity test.
  `keyProver_first`, `keyProver_shared`, `keyProver_second`, `keyProver_trace`, `keyProver_key`:
    what its fields are, by unfolding.
  `KeyParts.AtPlaces`, `first_places`: where the letters bear the key file's places, the first
    chain's halves stand at these seven places, in this order.

Limits.
  * A place without a round has no half.
  * The four proximity tests' halves are letters: no such half is written.
  * What each sending's rows hold (`SendJob.data`), the lookups' summands (`LookJobs`), the readers
    and the pile's filler are letters.
  * THE LOOKUPS ARE SEATED AT THE OWNERS OF THE KEY FILE's BOOK: `K3.proverSideOfLookupInChain` at `K3.keyOwners`
    of each lookup's own face (Johnson/Desc/ProofFile/Honest/K3/RowOwned.lean). `K3.proverSideOfLookupInChainAtOneOwner` names
    every stretch after one fixed owner, the segment's mask row. The entries of `keyBook`
    (E2E/KeyBook.lean) name two others, so the frame's `lend` refuses that row at its first test, and
    `ready` with it. This file compares no name: that the row at `K3.keyOwners` states the names of
    the book's entries is read off the definitions and stated in no theorem, and it holds only where
    `look0`, `look1` bear the book's faces, which `KeyParts.AtPlaces` does not ask. Nothing here
    holds the halves against a book.
  * Nothing holds the halves against the key file's description: neither the places, nor the numbers
    of rounds, nor what is sent.

-/
import Johnson.Desc.ProofFile.Honest.K1.Part
import Johnson.Desc.ProofFile.Honest.K14.Sendings
import Johnson.Desc.ProofFile.Honest.K13.Part
import Johnson.Desc.ProofFile.Honest.K3.RowOwned
import Johnson.Desc.Key.Xi

set_option autoImplicit false

namespace AtPublicFiles.KeyFile
open ProofFile.Honest
open VerifiableInference.Desc (Place)

/-- The key file's instance: the key of a table. -/
abbrev KeyInst : Type := VerifiableInference.Desc.Key.Xi

/-- What a half of the first or the second chain is handed: there is no trace. -/
abbrev In1 (W₀ Rc : Type) : Type := Local W₀ Rc KeyInst Unit

/-- What a half of the shared chain is handed. -/
abbrev In2 (W₀ Rc : Type) : Type := Common W₀ Rc OnBytes.TableKey

/-- The committer's coins for one table, field by field. The shared chain's two sendings read the
frame's own `TableRand` (Honest/ForKinds.lean), so this returns what it is given. -/
def randK14 (c : TableRand) : TableRand := ⟨c.pad, c.tail⟩

/-- **All letters of the key file's prover.** Wk: what a lookup's summands are written at. -/
structure KeyParts (W₀ Rc X₀ X Wk : Type) where
  /-- the stored table's columns -/
  stored : W₀ → Rc → Nat → Nat → Option (List Cb.Gl.F)
  inRange : W₀ → Bool
  dummy : W₀
  own₀ : X
  ownShared₀ : X₀
  meet : X → State (In2 W₀ Rc) X₀ → X
  /-- the index's reader -/
  weights : W₀ → Weights
  /-- the reader of the committer's coins -/
  rand : Rc → TableRand
  /-- the three sendings of the first chain -/
  idx : K1.SendJob (In1 W₀ Rc) X
  msg : K1.SendJob (In1 W₀ Rc) X
  w : K1.SendJob (In1 W₀ Rc) X
  /-- the two lookups: one reader of points; each lookup has a job of its own, because the two have
  different faces and a job sees no face -/
  reads : K3.Reads
  jobs0 : K3.LookJobs Wk
  jobs1 : K3.LookJobs Wk
  wit : In1 W₀ Rc → Wk
  look0 : K3.At
  look1 : K3.At
  /-- the proximity test on the ranges' group: A LETTER -/
  rng : Placed (In1 W₀ Rc) (In1 W₀ Rc) X
  /-- the batching -/
  pile : K13.PileOf KeyInst
  batt : VerifiableInference.Desc.K13.Where
  /-- the shared chain's own rounds and its two sendings -/
  lin : K14.Data
  send : K14.SendPub
  /-- the two proximity tests of the shared chain: LETTERS -/
  onU : Placed Empty (In2 W₀ Rc) X₀
  onOmega : Placed Empty (In2 W₀ Rc) X₀
  /-- the proximity test of the second chain: A LETTER -/
  own : Placed (In1 W₀ Rc) (In1 W₀ Rc) X

variable {W₀ Rc X₀ X Wk : Type}

/-- The shared chain's halves in the order of the places: the kind's own (pieces 1, 4, 7 and, where
the shape splits, 8) with the two sendings (pieces 2, 5) between them. -/
def sharedChainProverSidesInOrder (own send : List (Placed Empty (In2 W₀ Rc) X₀)) : List (Placed Empty (In2 W₀ Rc) X₀) :=
  match own, send with
  | p1 :: p4 :: rest, [s2, s5] => p1 :: s2 :: p4 :: s5 :: rest
  | a, b => a ++ b

/-- **The key file's honest prover, as halves at their places.** -/
def keyProver (K : KeyParts W₀ Rc X₀ X Wk) : Prover W₀ Rc KeyInst OnBytes.TableKey Unit X₀ X where
  stored := K.stored
  trace := fun _ _ => some ()
  key := fun x => x.key
  inRange := K.inRange
  dummy := K.dummy
  own₀ := K.own₀
  ownShared₀ := K.ownShared₀
  first :=
    [K1.proverSideOfSending K.idx, K1.proverSideOfSending K.msg,
      K3.proverSideOfLookupInChain (K3.keyOwners K.look0.face) K.reads K.jobs0 K.wit K.look0,
      K3.proverSideOfLookupInChain (K3.keyOwners K.look1.face) K.reads K.jobs1 K.wit K.look1, K.rng,
      K13.proverSideOfClaimCombination K.weights K.pile K.batt, K1.proverSideOfSending K.w]
  shared :=
    sharedChainProverSidesInOrder (K14.proverSidesOfSharedRounds K.lin K.weights) (K14.proverSidesOfSharedSendings K.send K.weights fun c => randK14 (K.rand c))
      ++ [K.onU, K.onOmega]
  second := [K.own]
  meet := K.meet

/-- The first chain's seven halves. -/
theorem keyProver_first (K : KeyParts W₀ Rc X₀ X Wk) :
    (keyProver K).first =
      [K1.proverSideOfSending K.idx, K1.proverSideOfSending K.msg,
        K3.proverSideOfLookupInChain (K3.keyOwners K.look0.face) K.reads K.jobs0 K.wit K.look0,
        K3.proverSideOfLookupInChain (K3.keyOwners K.look1.face) K.reads K.jobs1 K.wit K.look1, K.rng,
        K13.proverSideOfClaimCombination K.weights K.pile K.batt, K1.proverSideOfSending K.w] := rfl

/-- The places of the shared chain's halves, where the shape splits. -/
theorem keyProver_shared (K : KeyParts W₀ Rc X₀ X Wk) (h : K.lin.S.sharedSplitNeeded = true) :
    (keyProver K).shared.map (·.place) =
      [K14.place 1, K14.sendPlace 2, K14.place 4, K14.sendPlace 5, K14.place 7, K14.place 8,
        K.onU.place, K.onOmega.place] := by
  simp [keyProver, sharedChainProverSidesInOrder, K14.proverSidesOfSharedRounds, K14.proverSidesOfSharedSendings, h]

/-- The second chain's one half. -/
theorem keyProver_second (K : KeyParts W₀ Rc X₀ X Wk) : (keyProver K).second = [K.own] := rfl

/-- There is a trace at every index and instance: the value of the type with one member. -/
theorem keyProver_trace (K : KeyParts W₀ Rc X₀ X Wk) (w₀ : W₀) (x : KeyInst) :
    (keyProver K).trace w₀ x = some () := rfl

/-- The shared chain is handed the instance's one field. -/
theorem keyProver_key (K : KeyParts W₀ Rc X₀ X Wk) (x : KeyInst) : (keyProver K).key x = x.key :=
  rfl

/-- The letters bear the key file's places in the first chain. -/
structure KeyParts.AtPlaces (K : KeyParts W₀ Rc X₀ X Wk) : Prop where
  idx : K.idx.P.place = ⟨1, none, 1, .K1⟩
  msg : K.msg.P.place = ⟨1, none, 2, .K1⟩
  look0 : K.look0.place = ⟨1, some 0, 2, .K3⟩
  look1 : K.look1.place = ⟨1, some 1, 2, .K3⟩
  rng : K.rng.place = ⟨1, none, 5, .K12⟩
  batt : K13.k13Place K.batt = ⟨1, none, 13, .K13⟩
  w : K.w.P.place = ⟨1, none, 14, .K1⟩

/-- Then the first chain's halves stand at these seven places, in this order. -/
theorem first_places (K : KeyParts W₀ Rc X₀ X Wk) (h : K.AtPlaces) :
    (keyProver K).first.map (·.place) =
      [⟨1, none, 1, .K1⟩, ⟨1, none, 2, .K1⟩, ⟨1, some 0, 2, .K3⟩, ⟨1, some 1, 2, .K3⟩,
        ⟨1, none, 5, .K12⟩, ⟨1, none, 13, .K13⟩, ⟨1, none, 14, .K1⟩] := by
  show [K.idx.P.place, K.msg.P.place, K.look0.place, K.look1.place, K.rng.place,
    K13.k13Place K.batt, K.w.P.place] = _
  rw [h.idx, h.msg, h.look0, h.look1, h.rng, h.batt, h.w]

end AtPublicFiles.KeyFile

#print axioms AtPublicFiles.KeyFile.keyProver_first
#print axioms AtPublicFiles.KeyFile.keyProver_shared
#print axioms AtPublicFiles.KeyFile.keyProver_second
#print axioms AtPublicFiles.KeyFile.keyProver_trace
#print axioms AtPublicFiles.KeyFile.keyProver_key
#print axioms AtPublicFiles.KeyFile.first_places
