-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/GoodInEq.lean
(kind K9's soundness lemma): THEOREM: THE PIECE OF THE EQUATION's BLOCK IS GOOD,
in the form in which the rule of composition takes a block (Johnson/Desc/Sound/GoodIn.lean:
Piece.GoodIn), at any errors: the block draws nothing, and no transcript is bad.
  equation_goodIn   for a piece that holds K9.oneEquation X p (under the words' test "below"):
      IN FRONT:  the one equation's value, on the data that the witness's tables hold, is 0
                 (oneK .. (dataAt ..) = 0: the sentence at which the law of the segment ends), and
                 every open row of the segment's group holds on these tables;
      BEHIND:    every open row of the segment's group holds on these tables (the row that the block
                 has laid is one of them).
tabOf: which tables a witness holds at a statement: a letter. The hypotheses, by name: hext (the
extractor hands the witness on) · hhands (the conditions) · hcarry (the tables are the same in front
and behind) · lens · facts (RowPremises: public).

-/
import Johnson.Desc.LinkLaw3
import Johnson.Desc.First.Batch.Law.Hout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.Sound
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Doomed)
open VerifiableInference.Desc.K9 (Lens equation)

variable {T W K Cl : Type} {C : CK} {F : Frame} [CommRing K]

/-- **The piece of the equation's block is good**, at any errors. -/
theorem equation_goodIn (X : Lens T) (ρ : Reading K) (pw : K9.Where) (N : Nat)
    (p : Piece C F T Cl W) (hb : p.b = below (K9.oneEquation X pw))
    (hext : ∀ a τ w, p.ext a τ w = w) (on on' : T × F.E.Str → Prop)
    (tabOf : T × F.E.Str → W → Nat → OnBytes.Part → Nat → K)
    (hhands : ∀ a τ b, on a → p.ior.red.out a τ = some b → on' b)
    (hcarry : ∀ a τ b w, on a → p.ior.red.out a τ = some b → tabOf b w = tabOf a w)
    (lens : ∀ s a, (X.get? s).isSome = true →
      ∃ a', X.get? (X.set s a) = some a' ∧ a'.L = a.L ∧ a'.d.st = a.d.st)
    (facts : ∀ s, on s → ∀ a q G, X.get? s.1 = some a → equation a.L a.F = .ok (q, G) →
      RowPremises a.L.check a.d.st N q) :
    p.GoodIn on on'
      (fun a w => oneK X ρ a.1 a.1 (dataAt X a.1 (tabOf a w)) = 0 ∧
        GroupHoldsAt X ρ N a.1 (tabOf a w))
      (fun b w => GroupHoldsAt X ρ N b.1 (tabOf b w)) := by
  intro a ha
  refine Doomed.of_forall _ _ fun τ b hout => ⟨hhands a τ b ha hout, ?_⟩
  intro w hw
  rw [hext]
  obtain ⟨_, _, hfold⟩ := Piece.out_below hb hout
  obtain ⟨k, hstep⟩ := fold_one hfold
  rw [hcarry a τ b w ha hout] at hw
  exact oneEquation_joint X ρ pw F.ft a.1 _ _ b.1 k N (tabOf a w) lens (facts a ha) hstep hw

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.equation_goodIn
