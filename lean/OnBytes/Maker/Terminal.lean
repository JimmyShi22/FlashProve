-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Terminal.lean: from a block of the verifier program to an interactive oracle reduction
as data, for the blocks that end a protocol. Definitions alone.

An interactive oracle reduction (`IOR`, Ior/Ior.lean) is terminal here if its output is the trivial
statement: `Unit` as the explicit part, no oracle (`extNone`) as the implicit part. Such a reduction
is an interactive oracle proof (`IOR.toInteractiveOracleProof`).

A block (`Blk`, OnBytes/Iop/Ground.lean) is written once and read twice. Its dry run gives the
rounds of a chain's description; from these the library makes the rounds' data `ds`
(Run/PlanQTypes.lean, `RD`) and, for a chain that opens two stored tables, their depth `a` and the
openings `xs` (Run/PlanQX.lean, `XO`). Its run on a view is a decision (`Blk.decides`).

What the file contains.
  `iorX`: the reduction of a description with two stored tables. Its shape, its marks, and the
    positions that it reads are those of Run/PlanQX.lean's skeleton `skeletonOverBothExternalStrings`, word for word: they
    hang on the verifier's messages alone. Its verifier is that skeleton's, with a decision that may
    read the instance.
  `iorS`: the same for a description without stored tables (Run/PlanQS.lean, `PSof`).
  `iorBlkX`, `iorBlkS`: the two at the decision that a block makes. The block may hang on the
    instance; the rounds' data may not: an `IOR` has one shape for all instances. That the dry run
    of `b x` gives the same rounds for every x is not asked here: it is owed by whoever lays `ds`,
    `a` and `xs`.

The proofs of work stand inside the shape, whatever the kit `C` of verifier's messages is: a round's
plain part holds its nonce and its verifier's message its test bits, by the entry's number of bits
(Run/PlanQS.lean, `roundS`), and the verifier tests them. So no work is to be laid on these
reductions afterwards.

What is not claimed. No law is stated here. The field `tie` is the empty set and the field `blinded`
is the skeleton's; nothing is said here of what these two fields are read for.


-/
import Run.PlanQX
import Ior.Ior
import OnBytes.Iop.Ground

set_option autoImplicit false

namespace OnBytes.Maker

open Iop _root_.Run _root_.Run.PQ

/-- The terminal reduction of a description with two stored tables; the decision reads the
instance. -/
@[reducible] def iorX {Xi : Type} (C : CK) (ds : List RD) (a : ℕ) (xs : List XO)
    (dec : Xi → View → Bool) : IOR Xi (twoExternalStrings (2 ^ a) SgX) Unit extNone where
  shape := Twin.up (SOf C ds)
  blinded := fun _ => true
  extReads := fun ρ => ((xWanted a ds xs (drawnSL C ds ρ.2)).filterMap (xPos (2 ^ a))).toFinset
  reads := fun ρ =>
    (((wanted ds (drawnSL C ds ρ.2)).filterMap fun nx =>
      (posAtS C ds nx.1 nx.2).map fun p => (Sum.inr p : OPos (Twin.up (SOf C ds))))).toFinset
  out := fun x y τ => if (skeletonOverBothExternalStrings C ds a xs (dec x)).accept () y τ then some () else none
  imp := fun _ _ => ()
  srcE := fun _ _ => ∅
  srcO := fun _ _ => ∅
  tie := fun _ _ => ∅

/-- The terminal reduction of a description without stored tables. -/
@[reducible] def iorS {Xi : Type} (C : CK) (ds : List RD) (dec : Xi → View → Bool) :
    IOR Xi E0 Unit extNone where
  shape := Twin.up (SOf C ds)
  blinded := fun _ => true
  extReads := fun _ => ∅
  reads := fun ρ =>
    (((wanted ds (drawnSL C ds ρ.2)).filterMap fun nx =>
      (posAtS C ds nx.1 nx.2).map fun p => (Sum.inr p : OPos (Twin.up (SOf C ds))))).toFinset
  out := fun x y τ => if (PSof C ds (dec x)).accept () y τ then some () else none
  imp := fun _ _ => ()
  srcE := fun _ _ => ∅
  srcO := fun _ _ => ∅
  tie := fun _ _ => ∅

/-- `iorX` at the decision of a block that may hang on the instance, from the start s. -/
@[reducible] def iorBlkX {Xi : Type} (C : CK) (ds : List RD) (a : ℕ) (xs : List XO)
    (b : Xi → Blk Unit) (s : Start) : IOR Xi (twoExternalStrings (2 ^ a) SgX) Unit extNone :=
  iorX C ds a xs fun x => (b x).decides s

/-- `iorS` at the decision of a block that may hang on the instance, from the start s. -/
@[reducible] def iorBlkS {Xi : Type} (C : CK) (ds : List RD) (b : Xi → Blk Unit) (s : Start) :
    IOR Xi E0 Unit extNone :=
  iorS C ds fun x => (b x).decides s

end OnBytes.Maker
