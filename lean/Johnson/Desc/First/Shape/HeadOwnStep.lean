-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/HeadOwnStep.lean: THE SUB-PROTOCOL "THE OUTPUT HEAD's OWN ROUNDS" (the kind
K6; Kinds.Head.blockAt, Johnson/Stored/HeadSeatAt.lean) AS ONE STEP ON THE SHAPE OF THE STATE THAT
THE FIRST CHAIN CARRIES (Chain.lean). General; nothing is evaluated.
  **`k6G h`**: the step: it reads the ledger's shape, the shape of what the lookup returned (of it
    the number of coordinates of the lookup's point) and the head's own fields; the hearing's step
    on the ledger's shape returns (headS (ztOf h.lt ‹that number›), HearHead.lean); it lays the
    ledger's shape behind, the lookup's record as what the head's rounds hand on (look), the shape
    of what was heard (HeadSh.x := headHeardOfSh …, HeardOfShape.lean) and of the squares' level's
    state (HeadSh.squaresP).
  **`k6_carries`**: at the bare block: where it says yes and the step returns, the step returns the
    shape behind.
By k6_shapes (HeadOwnRounds.lean).
Limits. THE WEAK FORM: under the step's own return (HearFrame.lean). The bare block: the guards of a
seat are not in it. "Returns" is not here. No state is shown at which the step returns. Nothing on
soundness, completeness or hiding.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Shape.HeadOwnRounds
import Johnson.Desc.First.Shape.Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.Kinds.Head (blockAt sizesOf)

/-- **The sub-protocol "the output head's own rounds" on the chain's shape.** It reads the ledger's
shape, the shape of what the lookup returned (of it the number of coordinates of the lookup's point)
and the head's own fields; the hearing's step on the ledger's shape (headS, HearHead.lean) returns;
it lays the ledger's shape behind, the lookup's record as what the head's rounds hand on, the shape
of what was heard and the shape of the squares' level's state. -/
def k6G (h : Model.Head.Shape) (a : ChainSh) : Option ChainSh :=
  match a.led, a.lookHeard, a.head with
  | some L, some g, some hd =>
    (@headS (sizesOf h) (ztOf h.lt g.zx) L).map fun y =>
      ((a.setLed y.2).layLook (some g)).setHead
        { hd with
          x := some (@headHeardOfSh (sizesOf h) g.zx y.1)
          squaresP := some (pscOfSh y.1.norm.squares.psc false) }
  | _, _, _ => none

/-- **(B1)** at the bare block: where it says yes and the step returns, the step returns the shape
behind. -/
theorem k6_carries (h : Model.Head.Shape) (iU3 work l : Nat) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {u : ChainSh}
    (hd : (blockAt h iU3 work l).decide s rs gs = .ok s') (hg : k6G h (chainSh s) = some u) :
    u = chainSh s' := by
  obtain ⟨o, g, F1, X, Q, hs, hop, hlk, rfl, rfl, hy⟩ := k6_shapes h iU3 work l hd
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  obtain rfl : here = .head o := hs
  obtain ⟨fr, kept, ids, L, F, x, t, tl, claim, wo, Fm, slot, opened, squaresP, lookHeard⟩ := o
  obtain rfl : opened = true := hop
  obtain rfl : lookHeard = some X.g1 := hlk
  unfold k6G at hg
  obtain ⟨y, h1, rfl⟩ := Option.map_eq_some_iff.1 hg
  obtain ⟨e1, e2, e3⟩ := hy y h1
  show ((ChainSh.setLed _ y.2).layLook (some (heardAll X.g1))).setHead
    { headSh _ with
      x := some (@headHeardOfSh (sizesOf h) X.g1.zx.size y.1)
      squaresP := some (pscOfSh y.1.norm.squares.psc false) } = _
  rw [← e1, ← e2, ← e3]
  rfl

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.k6_carries
#print axioms VerifiableInference.Desc.First.Shape.k6G
