-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Walk.lean: a reading of a chain's rounds in their order.

A decision (OnBytes/Base.lean) sees a chain as a list of rounds. Each round holds the items of the
prover's message, without the roots, and what the verifier drew. A protocol is made of blocks, and
each block uses up some rounds in their order. `Walk α` is a reading of that kind: it takes the
rounds that are left and returns a value with the remaining rounds, or fails.

The blocks of this directory are not written as walks. They are written in the richer type `Blk`
(OnBytes/Iop/Ground.lean). The run of a block on a view, `Blk.walk`, is a `Walk`, and
`Blk.decides` is `Walk.decides` of it.

Main definitions: `Walk`, `Walk.decides`, `elemsOf`.
-/
import OnBytes.Base

namespace OnBytes

/-- A reading of the rounds that are left: a value and the remaining rounds, or failure. -/
abbrev Walk : Type → Type := StateT (List Fmt.RoundView) Option

namespace Walk

/-- True if the walk succeeds on the view's rounds and uses all of them. -/
def decides (w : Walk Unit) (v : Fmt.View) : Bool :=
  match w v.rounds with
  | some (_, []) => true
  | _ => false

end Walk

/-- The elements of the extension field among a round's items, in their order. An answer to an
out-of-domain sample counts as an element. -/
def elemsOf (r : Fmt.RoundView) : List E :=
  r.vals.filterMap fun g =>
    match g with
    | .e x => some (E.ofTriple x)
    | .answer x => some (E.ofTriple x)
    | _ => none

end OnBytes
