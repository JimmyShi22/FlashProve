-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/MadeAtOpeningSent.lean: TWO PUBLIC TESTS OF ANOTHER LAYER THAT COME
AT THE FIRST SEGMENT's OPENING ARE MADE BY THE SUB-PROTOCOL: "frame.sentIs" and "ledger.treesAre"
at segment 0 (`sentIsB`, `treesAreB`: Johnson/Desc/First/FillSent.lean). Statements with their
proofs. What the joined sub-protocol does: kind K1's first sending writes the request's frame
(`K1.firstAtS_frame`: the whole frame behind, as one written term); the frame's step "link 0:
opened" lays the open link's context from that copy and the fresh ledger
(`openLayZero_ok`). `openingZero_sentIs`: `sentIsB d 0` accepts behind, WHERE three things hold of
  the state IN FRONT and of the layer's data: as what segment 0's kept targets were first sent is
    the data's; the frame's list of kept copies is the data's; the numbers of the first messages
    that the sending lays are the data's list "own". EACH IS A NAMED PREMISE.
  `openingZero_treesAre`: `treesAreB d 0` accepts behind, WHERE the fresh ledger's arrays have the
  data's
    look: a test on the list of rounds' values alone.
What is not claimed. These premises. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.MadeAtOpeningLook
import Johnson.Desc.K1.Law.FrameAtFirst
import Johnson.Desc.First.FillSent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice
open Desc.Plain
open Johnson.Desc.First.Walk (LayPar startFork)
open Johnson.Desc.First.Walk.Law (openLayZero_ok)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.FillSent (SentData sentIsB treesAreB treeLook)

section
variable {Cl : Type} {q : Params.First} {gp : GPar} {nm : String} {X : LayPar}
  {fvs : List Bool} {kCol : ℕ}

/-- **"frame.sentIs" at segment 0.** -/
theorem openingZero_sentIs {s t : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.openingZero q gp nm X fvs kCol : Block S Cl).decide s [r₁, r₂] gs = .ok t)
    (d : SentData) (hb : (s.check.frame.groups.getD 0 {}).born = d.born 0)
    (hk : s.check.frame.keptBefore = d.kept 0)
    (ho : (K1.idsOf (K1.firstPar q gp) s.st.oracles.size).extract 0
      (s.check.frame.atMoment 0).length = d.own 0) : sentIsB d 0 t = true := by
  obtain ⟨s₁, g₁, h1, h2⟩ := K1.openingZero_mid h
  obtain ⟨_, _, hl0, _, _, hl, _⟩ := openLayZero_ok h2
  obtain ⟨g, mask, e, _, _⟩ := K1.firstAtS_frame q gp s s₁ r₁ r₂ g₁ h1
  have ho' := K1.firstAtS_own q gp s s₁ r₁ r₂ g₁ h1
  have hk' := K1.firstAtS_keptBefore q gp s s₁ r₁ r₂ g₁ h1
  have hn : s₁.check.frame.next = .laterOrClose := by rw [e]
  have hg : s₁.check.frame.groups = s.check.frame.groups := by rw [e]
  unfold sentIsB
  rw [hl]
  simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨hn, hl0⟩, by rw [hg]; exact hb⟩, by rw [ho']; exact ho⟩, by rw [hk']; exact hk⟩

/-- **"ledger.treesAre" at segment 0.** -/
theorem openingZero_treesAre {s t : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.openingZero q gp nm X fvs kCol : Block S Cl).decide s [r₁, r₂] gs = .ok t)
    (d : SentData) (ht : (startFork X.X X.ns).trees.toList.map treeLook = d.trees 0) :
    treesAreB d 0 t = true := by
  obtain ⟨_, hf, _⟩ := openingZero_fresh h
  unfold treesAreB
  rw [hf]
  simpa only [Option.any_some, decide_eq_true_eq] using ht

end

end VerifiableInference.Desc.K13.Law
