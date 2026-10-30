-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/WoOwed.lean: the statement alone, as a Prop by def.

The sentence "wo" (`woAt`, Johnson/Top/H0/Fill/FillP1.lean) reads
the witness through a reader rw that takes the verifier's state: the pending row that the frame's
reader gives at a state, if it gives one, holds of `rw a w`. So "from the state behind to the state
in front" speaks of two readings of one witness, and the statement bears a premise for that.

  `WoBackAtCommit`: "wo" goes back over an accept of a later moment's sub-protocol `commitAtS`
    (Johnson/Desc/K1/AtS.lean; K1's files call a sub-protocol a block), WHERE THE TWO READINGS AGREE
    on the matrix and on the mask entries of the index masks' message (`AgreeAt`,
    Johnson/Desc/K13/Law/Agree.lean), at the number that the state in front holds for that message.

Can the new premise be met? At a reader that does not read the state it holds by rfl. At the reader
that is meant (`rwBook`, Johnson/Desc/K13/Law/ReaderByBook.lean) it is a law on a sending, left to
other files; not shown here.
Limits. Nothing on the reads' place's joined sub-protocol. K01_law is not proved by this. Nothing on
soundness.
-/
import Johnson.Top.H0.Fill.FillP1
import Johnson.Desc.K1.Law.GoodSend5
import Johnson.Desc.K13.Law.Agree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S)

/-- **ROW G.wo, at a segment's later moment.** -/
def WoBackAtCommit : Prop :=
  ∀ (Cl Pp W : Type) (nR kC : ℕ) (P : Par) (link moment : Nat) (arrays : Option (List Nat))
    (d : First.FillP1.PubData) (rw : Pp × S → W → First.FillP1.PileWit nR kC) (m : Nat)
    (x x' : Pp × S) (y y' : Strs) (w : W) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))),
    (commitAtS P link moment arrays : Block S Cl).decide x.2 rs gs = .ok x'.2 →
      K13.Law.AgreeAt x.2.out.indexMasks (rw x' w) (rw x w) →
      First.FillP1.woAt d rw m x' y' w → First.FillP1.woAt d rw m x y w

end VerifiableInference.Desc.K1
