-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/BatchMonoK9.lean: THE ONE PREMISE THAT Chain.guarded_chainAt (SeatGuardChain.lean) ASKS OF A KIND's TEXT, AT K9's REAL BATCHING (Johnson/Desc/First/Batch/Kind.lean): it is
monotone in the function of claims that it is handed: it calls that function once, behind the draw and two tests, and goes on from its yes.

  K9.adds_mono, **K9.batch_mono**: where f' says yes f says the same yes ⇒ batch X p f' has batch X p f's rounds, and where it says yes batch X p f says the same yes: at every lens X and place p.

  K9.batch_face: and its face (name, place, own test on the plan, rounds, oracles, "before", the runs' names) does not hang on that function: by rfl.

Every "there is", walked: no statement has one.
Limits. Of K9's kind as Johnson/Desc/First/Batch/Kind.lean has it, general in the lens; the driver lays «{ … (batch c) with place := a9 }» over it: a change of place turns neither rounds nor decision. Nothing on soundness.

-/
import Johnson.Desc.First.Batch.Kind
import Johnson.Desc.Sound.SeatGuardChain
import Johnson.Desc.Sound.SeatGuardFaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9

variable {T Cl : Type}

theorem adds_mono (X : Lens T) (p : Where) (piece : Nat) (what : String)
    (f' f : T → Except String (List Claim × T)) (h : ∀ s y, f' s = .ok y → f s = .ok y) :
    (adds (Cl := Cl) X p piece what f').UnderR (adds X p piece what f) :=
  ⟨rfl, fun t _ _ s' D => by
    refine bindMono D fun _ D => ?_
    refine bindMono D fun _ D => ?_
    exact bindMonoL D fun x hx => h _ _ hx⟩

/-- **K9's batching is monotone in its function of claims.** -/
theorem batch_mono (X : Lens T) (p : Where) (f' f : T → Except String (List Claim × T))
    (h : ∀ s y, f' s = .ok y → f s = .ok y) : (batch X p f').UnderR (batch X p f) :=
  ⟨rfl, fun t rs gs s' D => by
    refine bindMono D fun t₁ D => ?_
    exact (adds_mono X p p.piece "the segment's" f' f h).2 t₁ [] [] s' D⟩

/-- **K9's batching shows the tests on the plan one face, whatever function it is handed** (Link.BatchFace's clause, SeatGuardFaces.lean). -/
theorem batch_face (X : Lens T) (p : Where) (f' f : T → Except String (List Claim × T)) :
    (batch X p f').face = (batch X p f).face := rfl

end VerifiableInference.Desc.K9

#print axioms VerifiableInference.Desc.K9.adds_mono
#print axioms VerifiableInference.Desc.K9.batch_mono
#print axioms VerifiableInference.Desc.K9.batch_face
