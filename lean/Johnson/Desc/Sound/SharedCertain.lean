-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SharedCertain.lean: A BLOCK OF THE SHARED CHAIN WHOSE STEP BACK HOLDS AT EVERY TRANSCRIPT PAYS
FOR EVERY N, AT ANY ERRORS, WHATEVER ITS RELATIONS READ; and the front block at the table's own terms. Two
statements written as `def … : Prop`. NOTHING IS PROVED IN THIS FILE.

  `PaysOfCertain`: if, from every statement with `on` and AT EVERY TRANSCRIPT, the block's yes gives the promise
    behind and leads every witness behind back to one in front, the block pays for N slots
    (`Piece.PaysN`), for every N, at its own errors whatever they are, at any acting part. No challenge is
    bad for any slot: so nothing is counted. It serves the blocks without a round and those whose rounds
    draw nothing that matters ((rec_gamma), joins, SPLIT, a chain's end), AND IT LETS THE RELATIONS READ A SLOT's
    OWN. (Other files name the like for a block without a round or with errors 0.)
  `FrontPays`: the shared chain's front block, at `onQ₂` and `relQ₂` between borders 0 and 1: if it turns nothing
    (its yes puts out the statement as it was), sends no tree (the next block's first tree is its own),
    its extractor is the identity, and the book-keeping at border 0 gives that at border 1.

Limits. Rules. `PaysOfCertain` is met for nothing by a block that refuses all. That the real front block
turns nothing (a stretch without a round leaves the oracles as they were) is a premise.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.BordersSharedQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.Shared

/-- **A step back that holds at every transcript is paid for every N.** -/
def PaysOfCertain : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (N : ℕ)
    (on on' : S × F.E.Str → Prop) (R R' : S × F.E.Str → W → Prop) (act : BKey F S),
    (∀ a τ b, on a → p.ior.red.out a τ = some b → on' b ∧ ∀ w, R' b w → R a (p.ext a τ w)) →
    p.PaysN N on on' R R' act

/-- **The front block pays, at the table's own terms.** -/
def FrontPays : Prop :=
  ∀ (P₁ S₂ Cl Wt : Type) (C : CK) (Fr : Frame) (N : NumbersS) (Mg : MeaningS S₂ P₁ Wt)
    (Pm : PromMeaning S₂) (Oc : P₁ → Strs → Prop) (split : Bool) (n : ℕ)
    (f pt : Piece C Fr (P₁ × S₂) Cl Wt) (r : List (Piece C Fr (P₁ × S₂) Cl Wt)),
    (∀ a τ b, f.ior.red.out a τ = some b → b = a) → pt.base = f.base →
    (∀ a τ w, f.ext a τ w = w) → (∀ s, Pm.shape 0 s = true → Pm.shape 1 s = true) →
    f.PaysN n (onQ₂ N Pm Oc split f (pt :: r) 0) (onQ₂ N Pm Oc split f (pt :: r) 1)
      (relQ₂ N Mg split f (pt :: r) 0) (relQ₂ N Mg split f (pt :: r) 1)
      (actQ N f (pt :: r) 0)

#check @PaysOfCertain
#check @FrontPays

end VerifiableInference.Desc.Sound
