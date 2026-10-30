-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/BesideLifts.lean: A ROW's DEBT AT THE LAST TABLE LIFTS TO THE LAYER besideL PL X.
The two statements are taken over, as definitions, to the letter (from another file,
but for the import's name); the two proofs beneath them
are not taken over.

  ownLifts     a piece that hands on what was handed (b.1.1 = a.1.1 at every yes): its own law
               between the promises at two borders lifts to the layer: the promise in front is
               taken apart (onQ₃_beside), the elder law is run, and X's yes is put back behind, at
               the same e.
  framesLift   "what rides" lifts WITHOUT A PREMISE ON THE PIECE: Frames asks its conclusion under
               the two promises; the layer's promises are the stronger: so the elder law is called
               at less.
IS IT EMPTY? Each is an implication from a law at PL to the like at besideL PL X, at all letters.
Where no statement lies in the layer's promise the conclusion is idle, as the premise may be.
Nothing on soundness.
-/
import Johnson.Desc.Last.BesideL

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.Last
open OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last

/-- **(G1a), THE STATEMENT.** A piece that hands on what was handed: its own law between the promises
at two borders lifts to the layer. -/
def OwnLifts : Prop :=
  ∀ (P S₁ S₂ S₃' Cl Wt : Type) (C : CK) (Fr : Frame) (N : NumbersS) (Mg : MeaningS S₂ (P × S₁) Wt)
    (ML : MeaningL S₃' Wt) (Pm : PromMeaning S₂) (PL : PromMeaningL S₂ S₃' (P × S₁))
    (Oc : P × S₁ → Strs → Prop) (X : S₂ → Bool) (k : ℕ)
    (x : Piece C Fr ((P × S₁ × S₂) × S₃') Cl Wt) (In Out : ItemL → Prop),
    (∀ a τ b, x.ior.red.out a τ = some b → b.1.1 = a.1.1) →
    x.Own (onQ₃ N Mg Pm PL Oc k) (onQ₃ N Mg Pm PL Oc (k + 1)) (meansQ₃ N Mg ML) In Out →
    x.Own (onQ₃ N Mg Pm (besideL PL X) Oc k) (onQ₃ N Mg Pm (besideL PL X) Oc (k + 1))
      (meansQ₃ N Mg ML) In Out

/-- **(G1b), THE STATEMENT.** So does "what rides". -/
def FramesLift : Prop :=
  ∀ (P S₁ S₂ S₃' Cl Wt : Type) (C : CK) (Fr : Frame) (N : NumbersS) (Mg : MeaningS S₂ (P × S₁) Wt)
    (ML : MeaningL S₃' Wt) (Pm : PromMeaning S₂) (PL : PromMeaningL S₂ S₃' (P × S₁))
    (Oc : P × S₁ → Strs → Prop) (X : S₂ → Bool) (k : ℕ)
    (x : Piece C Fr ((P × S₁ × S₂) × S₃') Cl Wt) (Open In : ItemL → Prop),
    x.Frames (onQ₃ N Mg Pm PL Oc k) (onQ₃ N Mg Pm PL Oc (k + 1)) (meansQ₃ N Mg ML) Open In →
    x.Frames (onQ₃ N Mg Pm (besideL PL X) Oc k) (onQ₃ N Mg Pm (besideL PL X) Oc (k + 1))
      (meansQ₃ N Mg ML) Open In

/-- **(G1a).** -/
theorem ownLifts : OwnLifts := by
  intro P S₁ S₂ S₃' Cl Wt C Fr N Mg ML Pm PL Oc X k x In Out hstay h a ha
  obtain ⟨h1, hX⟩ := (onQ₃_beside N Mg Pm PL Oc X k a).1 ha
  refine _root_.Iop.Doomed.mono _ _ ?_ (h a h1)
  intro τ hτ b hb
  obtain ⟨hon, hw⟩ := hτ b hb
  refine ⟨(onQ₃_beside N Mg Pm PL Oc X (k + 1) b).2 ⟨hon, ?_⟩, hw⟩
  rw [hstay a τ b hb]
  exact hX

/-- **(G1b).** -/
theorem framesLift : FramesLift := by
  intro P S₁ S₂ S₃' Cl Wt C Fr N Mg ML Pm PL Oc X k x Open In h a τ b w i ha hb hb' hO hI hm
  exact h a τ b w i ((onQ₃_beside N Mg Pm PL Oc X k a).1 ha).1 hb
    ((onQ₃_beside N Mg Pm PL Oc X (k + 1) b).1 hb').1 hO hI hm

end VerifiableInference.OnPublicFiles.Last

#print axioms VerifiableInference.OnPublicFiles.Last.ownLifts
#print axioms VerifiableInference.OnPublicFiles.Last.framesLift
