-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/TestEnd.lean: THE LINK's LAST TWO BLOCKS, FORWARD: the block of the proximity
test says yes where the test does, and the chain's end says yes where nothing is left untested.
Statements and proofs, at the description's own text (Johnson/Desc/Link/LinkDesc.lean: enter · leave
· testBlock · linkProtocolChain; Johnson/Desc/ChainEnd.lean). No prover and no value stands in this file.

  testBlock_yes   enter's record · the test's yes at it ⟹ the block's yes, and the record that leave
                  lays back
  left_spent      marking a message as spent leaves "nothing is left untested" as it is
  end_yes         nothing is left untested ⟹ the chain's end says yes and turns nothing

Not shown here. That the test says yes. Nothing on soundness, on an honest prover or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Link.LinkDesc
import Johnson.Desc.ChainEndExact
import Johnson.Desc.K15.HsemSays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.K12
open _root_.Desc.K15 (P15 St enter leave testBlock linkProtocolChain p12Of)

theorem testBlock_yes (P : P15) (d : St) (t₀ t' : T12) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (he : enter d = .ok t₀)
    (h : (proximityTestKind guardedProximityTestParts (p12Of P) : Block T12 Unit).decide t₀ rs gs = .ok t') :
    (testBlock P).decide d rs gs =
      .ok { d with st := t'.st, book := t'.book, roots := t'.roots } := by
  show (enter d).bind (fun t => ((proximityTestKind guardedProximityTestParts _ : Block T12 Unit).decide t rs gs).bind (leave d)) =
    _
  rw [he]
  show ((proximityTestKind guardedProximityTestParts (p12Of P) : Block T12 Unit).decide t₀ rs gs).bind (leave d) = _
  rw [h]
  rfl

theorem left_spent (T : Statement) (star : ℕ) (h : ChainEnd.NothingLeft T) :
    ChainEnd.NothingLeft
      { T with oracles := T.oracles.modify star fun x => { x with spentAsMask := true } } := by
  refine ⟨h.1, fun i hi hs => ?_⟩
  have hi' : i < T.oracles.size := by simpa using hi
  have e : (T.oracles.modify star fun x => { x with spentAsMask := true })[i]'hi =
      if star = i then { T.oracles[i] with spentAsMask := true } else T.oracles[i] := by
    rw [Array.getElem_modify]
  have hs' : (T.oracles[i]).sampled = true := by
    have := hs
    rw [show ({ T with oracles := T.oracles.modify star fun x =>
      { x with spentAsMask := true } } : Statement).oracles[i] = _ from e] at this
    split at this <;> exact this
  obtain ⟨g, hg, G, hG, hr⟩ := h.2 i hi' hs'
  refine ⟨g, ?_, G, hG, hr⟩
  rw [show ({ T with oracles := T.oracles.modify star fun x =>
    { x with spentAsMask := true } } : Statement).oracles[i] = _ from e]
  split <;> exact hg

theorem end_yes (P : P15) (d : St) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (h : ChainEnd.NothingLeft d.st) : (linkProtocolChain P).last.decide d rs gs = .ok d := by
  show (ChainEnd.refuse (ChainEnd.untestedL d.st)).map (fun _ => d) = _
  rw [(ChainEnd.untested_iff d.st).2 h]
  rfl

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.testBlock_yes
#print axioms Johnson.Prover.Link.left_spent
#print axioms Johnson.Prover.Link.end_yes
