-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/HeadSpotsAt.lean: K9Sorts' CLOSED CONJUNCT "∃ nH, HeadSpots
Zp nH" (HeadSpots: Johnson/LPFK9R/SlotsSeat.lean:103) FROM THREE SENTENCES ON THE PUBLIC PART: the
named test spotsFitB Z · "25 links" (the two premises of stands24) · "the built link 24
is of the head's kind". One statement and its proof. General in Z.

  headSpots_of_fit: spotsFitB Z = true · Z.s₀.check.frame.shape.link.length = 25 · (∀ X,
                   Z.p.built.links[24]? = some X → X.kind = 2) ⊢ HeadSpots Z Z.p.X.H.ns

How (a map, by reading). A place in the head's dress has link 24:
under the test each place's dress goes by its link, and the head's dress asks the last link
(dress_head, Top/H0/K2Caller/Stands24.lean). The right side: the head's letters' plan is G.W.H
by construction (P1K2.pureLetters), and G.W = Z.p.X (ProofFile.Law.blankBy_W). The left side:
at a link other than 0 where the frame has no letters nsW answers nH; the frame has none at a built
link of kind 2 (Walk.Seat.frameAt).

Limits. ALL THREE PREMISES ARE PREMISES. spotsFitB is a test that the verifier does not run. The
third: IM.ground_named has "kind = 2" at the blank ground's built[24], in scope:
that Z.p.built.links is that list is not shown here. headSpotsB |
headSpots_of_B is the test with its law: another road to the same end. Neither name is declared in
this library. No soundness statement.

-/
import Johnson.LPFK9R.SlotsSeat
import Johnson.Top.H0.K2Caller.Stands24
import Johnson.Desc.ProofFile.Law.MakerPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.K2Caller (spotsFitB dressOf dress_head)
open Johnson.Desc.First.Walk.Seat (frameAt)

/-- The frame has no letters at a built link of the head's kind. -/
theorem frameAt_none_of_kind2 (built : Array Stages.LinkH) (W : Verify.Public) (l : ℕ)
    (hK : ∀ X, built[l]? = some X → X.kind = 2) : frameAt built W l = none := by
  unfold frameAt
  cases hX : built[l]? with
  | none => rfl
  | some X =>
    have h2 := hK X hX
    simp [h2]

/-- **HeadSpots, from three sentences on the public part.** -/
theorem headSpots_of_fit {Z : ProofFile.Pub} (hT : spotsFitB Z = true)
    (hL : Z.s₀.check.frame.shape.link.length = 25)
    (hK : ∀ X, Z.p.built.links[24]? = some X → X.kind = 2) : HeadSpots Z Z.p.X.H.ns := by
  intro G hG x hx hst l P hl hP
  have hx' : x ∈ ProofFile.k2SpotsAt Z := by
    unfold ProofFile.k2SpotsAt
    rw [hG]
    exact hx
  unfold spotsFitB at hT
  rw [Bool.and_eq_true] at hT
  have hD := of_decide_eq_true (List.all_eq_true.1 hT.2 x hx')
  rw [hst, hL, hl] at hD
  obtain ⟨l', e, hl'⟩ := dress_head hD.symm
  obtain rfl : l = l' := Option.some.inj e
  obtain rfl : l = 24 := by omega
  have hp : P.hp = G.W.H := by
    unfold P1K2.pureLetters at hP
    obtain ⟨X, -, rfl⟩ := Option.map_eq_some_iff.1 hP
    rfl
  rw [hp, ProofFile.Law.blankBy_W hG]
  show nsOfBuilt Z.p.built.links Z.p.X Z.p.X.H.ns 24 = _
  unfold nsOfBuilt nsW
  rw [if_neg (by omega), frameAt_none_of_kind2 _ _ _ hK]

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.frameAt_none_of_kind2
#print axioms VerifiableInference.Desc.LinkJoin.headSpots_of_fit
