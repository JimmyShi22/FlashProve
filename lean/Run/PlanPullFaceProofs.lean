-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanPullFaceProofs.lean: the proofs of Run/PlanPullFace.lean. The main one is `planPull_face`:
the interface `LtS`, with challenges as hash blocks, is as a term `BatchProtocol.drawsGrind` of the interface
`L0`, which has challenges as sampled values and no work. Its limits: the head of
Run/PlanPullFace.lean (4., and that no run function stands at `LtS`). `LtS`: the interface whose
Test is the protocol of `PSof` (Run/PlanQS.lean); Link and Batch have no rounds.

Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

The strategies that send fixed substitutes (`dfltS`, Run/PlanQPage.lean; `dfltSS`, `dfltLS`,
Run/PlanQS.lean) commute with the library's two steps (pulling back along samplers, adding the tests
of work), by one induction on the shape each. The records then agree field by field. For the Test's
protocol the proof of `planPull_face` uses Run/PlanPullProtoProofs.lean's `planPull_proto`.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PlanPullFace
import Run.PlanPullProtoProofs

set_option autoImplicit false

namespace Run
open Iop Rom Compile Compile.Batch Run.PQ

theorem lts_lof : Spec.lts_lof := fun _ _ _ => rfl

theorem dflt_pull {β : Type} (b : β) :
    ∀ (s : Shape) (σ : Samplers s), Strat.pull σ (dfltS b s) = dfltS b (Shape.pull s σ)
  | [], _ => rfl
  | r :: s, (σ, σs) =>
      congrArg (fun k => (((r.dOrc, r.dPlain), fun _ => k) : Strat (Shape.pull (r :: s) (σ, σs)) β))
        (dflt_pull b s σs)

theorem dflt_grind {β : Type} (b : β) :
    ∀ (s : Shape) (g : GBits s),
      Strat.grind g (dfltS b s) (NStrat.const g (GNon.nil ℕ s)) = dfltS b (Shape.grind ℕ s g)
  | [], _ => rfl
  | r :: s, (w, g) =>
      congrArg (fun k =>
          ((((r.grind ℕ w).dOrc, (r.grind ℕ w).dPlain),
            fun _ => k) : Strat (Shape.grind ℕ (r :: s) (w, g)) β))
        (dflt_grind b s g)

theorem dummy_step : Spec.dummy_step := by
  intro X Wt E Q ext σ g
  have e : Strat.grind g (Strat.pull σ (dfltS () Q.shape))
        (NStrat.const g (GNon.nil ℕ (Shape.pull Q.shape σ))) =
      dfltS () (Shape.grind ℕ (Shape.pull Q.shape σ) g) := by
    rw [dflt_pull]
    exact dflt_grind () _ g
  exact congrArg
    (fun (a : Strat ((Q.pull σ).grind ℕ g).shape Unit) =>
      ({ Coin := Unit, ext := ext, strat := fun _ _ _ => a, Bad := ∅,
         Hid := fun _ _ => ∅ } : Honest ((Q.pull σ).grind ℕ g) Wt)) e

theorem dfltSS_pull :
    ∀ (s : Shape) (A : RoundSplits s) (σ : Samplers s),
      SStrat.pull σ (dfltSS s A) = dfltSS (Shape.pull s σ) (RoundSplits.pull σ A)
  | [], _, _ => rfl
  | r :: s, (a, A), (σ, σs) =>
      congrArg (fun k =>
          (((a.split (r.dOrc, r.dPlain)).1, fun _ => k) :
            SStrat (Shape.pull (r :: s) (σ, σs)) (RoundSplits.pull (s := r :: s) (σ, σs) (a, A))))
        (dfltSS_pull s A σs)

theorem dfltLS_pull :
    ∀ (s : Shape) (A : RoundSplits s) (σ : Samplers s),
      LStrat.pull σ (dfltLS s A) = dfltLS (Shape.pull s σ) (RoundSplits.pull σ A)
  | [], _, _ => rfl
  | r :: s, (a, A), (σ, σs) =>
      congrArg (fun k =>
          (((a.split (r.dOrc, r.dPlain)).2, fun _ => k) :
            LStrat (Shape.pull (r :: s) (σ, σs)) (RoundSplits.pull (s := r :: s) (σ, σs) (a, A))))
        (dfltLS_pull s A σs)

theorem headS (r : Round) (a : RAnn r) (w : ℕ) :
    GPlain.mk (a.kind.b0 w) (a.split (r.dOrc, r.dPlain)).1 (default : ℕ) =
      ((a.grind ℕ w).split ((r.grind ℕ w).dOrc, (r.grind ℕ w).dPlain)).1 := by
  obtain ⟨k, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  cases w with
  | zero => rfl
  | succ n => cases k <;> rfl

theorem headL (r : Round) (a : RAnn r) (w : ℕ) :
    GPlain.mk (a.kind.bJ w) (a.split (r.dOrc, r.dPlain)).2 (default : ℕ) =
      ((a.grind ℕ w).split ((r.grind ℕ w).dOrc, (r.grind ℕ w).dPlain)).2 := by
  obtain ⟨k, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  cases w with
  | zero => rfl
  | succ n => cases k <;> rfl

theorem dfltSS_grind :
    ∀ (s : Shape) (A : RoundSplits s) (g : GBits s),
      SStrat.grind g (dfltSS s A) (GNon.nil ℕ s) = dfltSS (Shape.grind ℕ s g) (RoundSplits.grind ℕ A g)
  | [], _, _ => rfl
  | r :: s, (a, A), (w, g) => by
      show ((GPlain.mk (a.kind.b0 w) (a.split (r.dOrc, r.dPlain)).1 (default : ℕ),
          fun _ => SStrat.grind g (dfltSS s A) (GNon.nil ℕ s)) :
          SStrat (Shape.grind ℕ (r :: s) (w, g)) (RoundSplits.grind ℕ (s := r :: s) (a, A) (w, g))) =
        (((a.grind ℕ w).split ((r.grind ℕ w).dOrc, (r.grind ℕ w).dPlain)).1,
          fun _ => dfltSS (Shape.grind ℕ s g) (RoundSplits.grind ℕ A g))
      rw [headS, dfltSS_grind s A g]

theorem dfltLS_grind :
    ∀ (s : Shape) (A : RoundSplits s) (g : GBits s),
      LStrat.grind g (dfltLS s A) (GNon.nil ℕ s) = dfltLS (Shape.grind ℕ s g) (RoundSplits.grind ℕ A g)
  | [], _, _ => rfl
  | r :: s, (a, A), (w, g) => by
      show ((GPlain.mk (a.kind.bJ w) (a.split (r.dOrc, r.dPlain)).2 (default : ℕ),
          fun _ => LStrat.grind g (dfltLS s A) (GNon.nil ℕ s)) :
          LStrat (Shape.grind ℕ (r :: s) (w, g)) (RoundSplits.grind ℕ (s := r :: s) (a, A) (w, g))) =
        (((a.grind ℕ w).split ((r.grind ℕ w).dOrc, (r.grind ℕ w).dPlain)).2,
          fun _ => dfltLS (Shape.grind ℕ s g) (RoundSplits.grind ℕ A g))
      rw [headL, dfltLS_grind s A g]

theorem dummyB_step : Spec.dummyB_step := by
  intro X Wt E Q ext σ g
  have e0 : SStrat.grind g (SStrat.pull σ (dfltSS Q.loc.shape Q.ann))
        (GNon.nil ℕ (Shape.pull Q.loc.shape σ)) =
      dfltSS (Shape.grind ℕ (Shape.pull Q.loc.shape σ) g) (RoundSplits.grind ℕ (RoundSplits.pull σ Q.ann) g) := by
    rw [dfltSS_pull]
    exact dfltSS_grind _ _ g
  have e1 : LStrat.grind g (LStrat.pull σ (dfltLS Q.loc.shape Q.ann))
        (GNon.nil ℕ (Shape.pull Q.loc.shape σ)) =
      dfltLS (Shape.grind ℕ (Shape.pull Q.loc.shape σ) g) (RoundSplits.grind ℕ (RoundSplits.pull σ Q.ann) g) := by
    rw [dfltLS_pull]
    exact dfltLS_grind _ _ g
  exact (congrArg₂
    (fun (a : SStrat ((Q.pull σ).grind ℕ g).loc.shape ((Q.pull σ).grind ℕ g).ann)
      (b : LStrat ((Q.pull σ).grind ℕ g).loc.shape ((Q.pull σ).grind ℕ g).ann) =>
        ({ Coin0 := Unit, Coin := Unit, ext := ext, strat0 := fun _ _ => a,
           strat := fun _ _ _ _ => b, Bad := ∅, Hid := fun _ _ => ∅,
           stop0 := fun _ => false } : BatchHonestProver ((Q.pull σ).grind ℕ g) Wt))
    e0 e1)

theorem lo3_step : Spec.lo3_step := by
  intro T Lk B dr gT gL gB
  have eT := dummy_step Unit (Unit × Unit) (oneExternalString 0 Unit) T (fun _ _ => ())
    (Samplers.ofDraws _ dr.T) (gT.pull (Samplers.ofDraws _ dr.T))
  have eL := dummy_step Unit (Unit × Unit × Unit) (twoExternalStrings 0 Unit) Lk
    (fun _ => (fun _ => (), fun _ => ()))
    (Samplers.ofDraws _ dr.Lk) (gL.pull (Samplers.ofDraws _ dr.Lk))
  have eB := dummyB_step Unit (Unit × Unit) (oneExternalString 0 Unit) B (fun _ _ => ())
    (Samplers.ofDraws _ dr.B) (gB.pull (Samplers.ofDraws _ dr.B))
  show ({ wordLength := 0, Symbol := Unit, EncodingRandomness := Unit, encodeIndex := fun _ _ _ => (), decodeIndex := fun _ => some (),
          offline := (T.pull (Samplers.ofDraws _ dr.T)).grind ℕ (gT.pull (Samplers.ofDraws _ dr.T)),
          link := (Lk.pull (Samplers.ofDraws _ dr.Lk)).grind ℕ (gL.pull (Samplers.ofDraws _ dr.Lk)),
          maxBatchSize := 1,
          onlineBatch := (B.pull (Samplers.ofDraws _ dr.B)).grind ℕ (gB.pull (Samplers.ofDraws _ dr.B)),
          honestOfflineProver := ((dummyH T fun _ _ => ()).pull (Samplers.ofDraws _ dr.T)).grind
              (gT.pull (Samplers.ofDraws _ dr.T)) (GNon.nil ℕ _),
          honestLinkProver := ((dummyH Lk fun _ => (fun _ => (), fun _ => ())).pull
                              (Samplers.ofDraws _ dr.Lk)).grind
              (gL.pull (Samplers.ofDraws _ dr.Lk)) (GNon.nil ℕ _),
          honestOnlineBatchProver := ((dummyB B fun _ _ => ()).pull (Samplers.ofDraws _ dr.B)).grind
              (gB.pull (Samplers.ofDraws _ dr.B)) (GNon.nil ℕ _),
          early := id, late := none } : BatchProtocol Unit Unit) = _
  rw [eT, eL, eB]

theorem planPull_face : Spec.planPull_face := fun f ds dec =>
  (congrArg Lof (planPull_proto f ds dec)).trans
    (lo3_step (Qv (ck f) ds dec) pL (BatchInteractiveOracleProof.ofProto pB)
      ⟨drOf f ds, (), ()⟩ (g0Of f ds) () ()).symm

theorem face_data : Spec.face_data := by
  intro f ds dec D w hd hg
  rw [planPull_face f ds dec, ← hd, ← hg]
  rfl

end Run
