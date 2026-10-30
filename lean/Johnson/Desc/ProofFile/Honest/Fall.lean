-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Fall.lean: whether, and where, a run meets a fall, as executable
definitions. A fall (`Fall`, Honest/Side.lean) is a test for an event at which a sub-protocol may
reject an honest run; it fires where its test returns `some`. This file is the counterpart of
`silentAt` (Honest/Rule.lean) for falls, at a whole file. Definitions only; no theorem.

  1  `frontsOf`, `chainFall`   the verifier's state before each sub-protocol of a chain, along a
     view, by the library's own `Block.step`, one sub-protocol after another; the first fall of a
     chain that fires
  2  `viewsFall`, `fallAt`   the same at a file's three views; at an honest run
  3  `Sides.fallsSeated`, `fallWords`   every fall is at the place of a sub-protocol of its chain;
     words for a printout

How it differs from the silent set. `silentAt` has no coin among its arguments. `fallAt` has the
run's coins among its arguments: it plays the run and reads what was sent. It plays by `runC`
(Honest/Walk.lean), which calls no later part of the chain, and no part of the second chain, after a
sub-protocol that rejects. So, where the sub-protocol at the fall's place rejects, a later part that
would be at fault cannot make `fallAt` return `none`. (Where a fall fires and that sub-protocol's
step accepts all the same, the run goes on, and a later fault still can.) (By `run`, which plays on,
it could: nobody has to prove that a move after a rejection is without fault.) A fall is asked at
the state before the sub-protocol at its place, the one that rejects; `frontsOf` lists that
sub-protocol and none after it, so the substitutes are not read. A fall's share is asked at each
fixed input and each fixed coin.

Limits.
  * `frontsOf` is a second definition of the course of `foldBlocks` (Johnson/Desc/Block.lean): it
    takes rounds and columns off the front as that function does, and calls the same `Block.step`.
    It is not proved here that the two agree.
  * `frontsOf` ends at the first sub-protocol that rejects: a fall after that sub-protocol is not
    seen.
  * The second chain's falls are seen only where the first two chains' folds have returned and the
    second chain's start has not rejected.
  * Nothing compares a fall's test with the verifier's own test, or its share with the test.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Walk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place OpenedColumn chainAt withEmptySealRound)

variable {S Cl Xi W₀ Rc Ky Tr X₀ X : Type}

/-! ## 1 Along one chain -/

/-- **The verifier's state before each sub-protocol**, along a chain's rounds and columns: the
place, the state before it, the sub-protocol's own challenges. Up to and including the first
sub-protocol that rejects; not a sub-protocol for which the rounds are too few. -/
def frontsOf (firstTree : Nat) : List (Block S Cl) → S → List Fmt.RoundView → List OpenedColumn →
    List (Place × S × List Fmt.Drawn)
  | [], _, _, _ => []
  | b :: l, s, rs, cols =>
    let mine := rs.take b.rounds.length
    if mine.length != b.rounds.length then [] else
    (b.place, s, mine.map (·.drawn)) ::
      match b.step firstTree s mine cols with
      | .error _ => []
      | .ok (s', k) => frontsOf firstTree l s' (rs.drop b.rounds.length) (cols.drop k)

/-- The first fall of a chain that fires, along a view: its place and its words. -/
def chainFall (fs : List (Fall S)) (firstTree : Nat) (bs : List (Block S Cl)) (s : S)
    (v : Fmt.View) : Option (Place × String) :=
  (frontsOf firstTree bs s v.rounds v.opened).findSome? fun x =>
    (fallOf fs x.1 x.2.1 x.2.2).map fun e => (x.1, e)

/-! ## 2 At a file -/

/-- **The first fall that three views meet**: the first chain's, at its view with the sealing round
put back; then the shared chain's; then the second chain's, from its start at the two earlier
chains' ends. The starts and the order are those of `FileDescription.runEnd`. -/
def viewsFall (F : FileDescription Xi) (f₁ : List (Fall F.S₁)) (f₂ : List (Fall F.S₂))
    (f₃ : List (Fall F.S₃)) (x : Xi) (U : Views) : Option (Place × String) :=
  let s₁ := F.start₁ (F.pub x)
  let s₂ := F.start₂ (F.pub x)
  ((chainFall f₁ 0 F.first.blocksInOrder s₁ (withEmptySealRound U.1)).or
    (chainFall f₂ 0 F.shared.blocksInOrder s₂ U.2.1)).or
    ((chainAt "" 0 F.first.blocksInOrder s₁ (withEmptySealRound U.1)).toOption.bind fun e₁ =>
      (chainAt "" 0 F.shared.blocksInOrder s₂ U.2.1).toOption.bind fun e₂ =>
        (F.start₃ (F.pub x) e₁ e₂).toOption.bind fun s₃ =>
          chainFall f₃ F.lastChainFirstTreeNumber F.second.blocksInOrder s₃ U.2.2)

/-- **Where an honest run meets a fall**: at an input, the run's coins and a list of challenges.
`none` if the run returns an error (a stop, a fault), and if it meets none. -/
def fallAt {F : FileDescription Xi} {Bk : ProverCoinCounts} (G : Sides F Bk W₀ Rc Ky Tr X₀ X)
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc) (x : Xi) (k : Coins Bk) (ρ : Draws) :
    Option (Place × String) :=
  (runC F Bk (G.prover H) w₀ rc x k ρ).toOption.bind fun r =>
    viewsFall F G.falls₁ G.falls₂ G.falls₃ x r.run.views

/-! ## 3 Two small things -/

/-- Every fall is at the place of a sub-protocol of its chain, with a list of parts or without (a
sub-protocol without a round has none): otherwise nothing ever asks it. -/
def Sides.fallsSeated {F : FileDescription Xi} {Bk : ProverCoinCounts} (G : Sides F Bk W₀ Rc Ky Tr X₀ X) : Bool :=
  G.falls₁.all (fun f => F.first.blocksInOrder.any fun b => b.place == f.place) &&
    G.falls₂.all (fun f => F.shared.blocksInOrder.any fun b => b.place == f.place) &&
    G.falls₃.all fun f => F.second.blocksInOrder.any fun b => b.place == f.place

/-- For a printout, beside `Rows.print` (Honest/Rows.lean). -/
def fallWords (o : Option (Place × String)) : String :=
  match o with
  | none => "it meets no fall"
  | some x => s!"IT MEETS A FALL at {x.1.chain}.{(x.1.link.map toString).getD "-"}.{x.1.piece}: " ++
      x.2

end ProofFile.Honest
