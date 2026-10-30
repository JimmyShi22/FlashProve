-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/OpensTwoStage.lean: from "outside the rare event the extractor gives the
opened index", said of logs, to index binding of a scheme with openings in place of proofs
(ZKCP/WithOpenings.lean, Rom/WithOpenings.lean).

Main names. `Rom.withOpenings_V_rom`, `Rom.binding_withOpenings_rom`: index binding of a scheme over
one hash function with openings in place of proofs passes to the syntax of ZKCP/Defs.lean, with the
same bound: the last steps of `binding_withOpenings_oneOf` (Rom/WithOpenings.lean) without a coding.
`binding_of_badW`: under hgood, index binding of `G.withOpenings` with `E.withOpenings` at 2 (tC +
(tP + tS) + 1)² / 2^lam, where tS bounds the committer's queries.

How. The game's verifier runs the committer again and compares keys. In the analysis the opener and
that run are ONE second-stage algorithm on strings, so tP + tS counts both, and the verdict asks
nothing. At each function g the game's bad event lies in `BadW` at the coding of the public
algorithm's value at g; the probability is `word_pr_pub` (Johnson/TypedOracleCompiler/RecCompile/WordPub.lean).

Limits.
- hgood IS A HYPOTHESIS, and all that is special to a scheme lies in it. It has no
  probability: at every g, key, index i, number n and three logs with g's answers (trC the
  committer's, trP the opener's, trV the run again's): a run of `G.commitAt i n` in trV to the key,
  no `EM` on the three logs under the coding at `Pub.det g`, and "the word off trC is the word off
  all three" give `E.Ei key trC = some i`.
- hgood speaks of every index. IT CANNOT HOLD AT AN INDEX TYPE THAT HOLDS AN INDEX THAT `E.Ei` NEVER
  GIVES (by an argument on paper from the definition of the hash event: a second honest run repeats
  the first's entries; not proved in Lean). It is to be met at a type of indices cut to those that
  the extractor can give.
- `root` is a letter: which digest of a key is the root under which the word is read is for the user
  to say.
- The premises on the public algorithm are those of `word_pr_pub`.
- No scheme is written here. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.WordPub
import Rom.WithOpenings
import OnBytes.K.Arm.TreeLog
import OnBytes.Slice.WrapBetween

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace Rom
open ZKCP
variable {lam : ℕ} {I X W IVK ISK Pf : Type}

/-- Openings in place of proofs, before or after the step to the syntax of ZKCP/Defs.lean: the same
verifier. -/
theorem withOpenings_V_rom (G : Gen.Arg (rom lam) I X W IVK ISK Pf) :
    (SpecialAny.oneOf G.withOpenings).V = (SpecialAny.oneOf G).withOpenings.V := by
  classical
  funext key x π
  show ofRom ((((G.C x.1).withCoins x.2).bind fun keys => OComp.pure keys.1).bind
      fun key' => OComp.pure (decide (key' = key)))
    = (((ofRom (G.C x.1)).withCoins x.2).mapO Prod.fst).mapO fun key' => decide (key' = key)
  rw [SpecialAny.ofRom_bind, SpecialAny.ofRom_bind, withCoins_ofRom]
  rfl

/-- Index binding of a scheme over one hash function with openings in place of proofs passes to the
syntax of ZKCP/Defs.lean, with the same bound. -/
theorem binding_withOpenings_rom (G : Gen.Arg (rom lam) I X W IVK ISK Pf)
    (E : Gen.Extractor (rom lam) I X W IVK Pf) (β : ℕ → ℕ → ℝ≥0∞)
    (h : Gen.HasIndexBindingWith (Special.toPair (openingRelation I)) G.withOpenings E.withOpenings
        β) :
    HasIndexBindingWith (openingRelation I) (SpecialAny.oneOf G).withOpenings
      (Special.extOf E).withOpenings β := by
  have h2 : HasIndexBindingWith (openingRelation I) (SpecialAny.oneOf G.withOpenings)
      (Special.extOf E.withOpenings) β :=
    SpecialAny.bindingWith_of_gen (openingRelation I) (SpecialAny.agrees_oneOf _) _ β
      (by rwa [Special.extTo_extOf])
  exact (SameV.hasIndexBindingWith_iff (withOpenings_V_rom G) (openingRelation I) _ β).1 h2

end Rom

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob ZKCP
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)}

/-- **From "outside the rare event the extractor gives the opened index" to index binding of the
scheme with openings in place of proofs.** The second stage of the analysis is the opener followed
by the committer's run again, as one algorithm on strings; the verdict asks nothing. hgood speaks of
logs: trC the committer's, trP the opener's, trV the run again's, all with g's answers. -/
theorem binding_of_badW {D I' X₀ W₀ IVK ISK Pf₀ : Type} (hlam : 0 < lam)
    (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (Pt : List Bool → Prop)
    (hPt : ∀ d s, Pt s → IsOther (m d) s) (Pub : OComp (rom lam) D) (hnc : Pub.NoCoin)
    (hasks : Pub.AsksIn fun _ s => Pt s) (hnr : NoRepeat Pub)
    (G : Gen.Arg (rom lam) I' X₀ W₀ IVK ISK Pf₀) (E : Gen.Extractor (rom lam) I' X₀ W₀ IVK Pf₀)
    (root : IVK → Dig lam) (tS : ℕ) (hS : ∀ i, (G.C i).QueryBound tS)
    (hgood : ∀ (g : Fam (rom lam)) (key : IVK) (i : I') (n : ℕ) (trC trP trV : Trace (rom lam)),
      (∀ e ∈ trC ++ (trP ++ trV), e.2.2 = g e.1 e.2.1) → RunsIn trV (G.commitAt i n) key →
      ¬ EM (singleTr (m (Pub.det g)) (trC ++ (trP ++ trV))) →
      extEnc W (singleTr (m (Pub.det g)) trC) (root key) =
        extEnc W (singleTr (m (Pub.det g)) (trC ++ (trP ++ trV))) (root key) →
      E.Ei key trC = some i) :
    Gen.HasIndexBindingWith (Special.toPair (openingRelation I')) G.withOpenings E.withOpenings
      fun tC tP => 2 * ((tC + (tP + tS) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  classical
  intro tC tP St Ct P1 hC hP
  have hNC : ∀ i n, (G.commitAt i n).NoCoin := fun i n =>
    OComp.NoCoin.bind (OComp.noCoin_withCoins _ _) fun _ => trivial
  have hSq : ∀ i n, (G.commitAt i n).QueryBound (tS + 0) := fun i n =>
    (OComp.QueryBound.withCoins _ _ _ (hS i)).bind fun _ => trivial
  have hC' : (Ct.bind fun o => OComp.pure (root o.1, o)).QueryBound (tC + 0) :=
    hC.bind fun _ => trivial
  have hP' : ∀ o : IVK × St, ((P1 o.2).bind fun xp =>
      (G.commitAt xp.1.1 xp.1.2).bind fun key' => OComp.pure (xp, key')).QueryBound
        (tP + (tS + 0 + 0)) := fun o =>
    (hP o.2).bind fun xp => (hSq _ _).bind fun _ => trivial
  have hw := word_pr_pub (W := W) hlam m Pt hPt Pub hnc hasks hnr
    (Ct.bind fun o => OComp.pure (root o.1, o))
    (fun o : IVK × St => (P1 o.2).bind fun xp =>
      (G.commitAt xp.1.1 xp.1.2).bind fun key' => OComp.pure (xp, key')) tC (tP + tS)
    (by simpa using hC') (fun o => by simpa using hP' o)
  refine le_trans ?_ hw
  refine MeasureTheory.lintegral_mono fun g => ?_
  unfold Rom.PrCoins
  have eL : Gen.bindingExp G.withOpenings E.withOpenings Ct P1 =
      Ct.withTrace.bind fun a => (P1 a.1.2).withTrace.bind fun b =>
        ((G.commitAt b.1.1.1 b.1.1.2).bind fun key' => OComp.pure (decide (key' = a.1.1))).bind
          fun c => OComp.pure ⟨c, E.Ei a.1.1 a.2, b.1.1, ()⟩ := rfl
  rw [eL]
  simp only [expP, verdP, run2, Rom.withTrace_bind, Rom.OComp.bind_assoc, Rom.OComp.withTrace,
    Rom.OComp.bind, Rom.OComp.runEager_bind, Rom.OComp.runEager, PMF.pure_bind, hnc.runEager g,
    (hNC _ _).runEager g, OnBytes.Slice.runEager_withTrace_det g _ (hNC _ _)]
  refine pr_bind_le_bind _ _ _ _ _ fun a ha => pr_bind_le_bind _ _ _ _ _ fun b hb => ?_
  refine pr_pure_le_pure ?_
  rintro ⟨hacc, hbad⟩
  refine ⟨rfl, ?_⟩
  by_contra hnb
  have hkey : (G.commitAt b.1.1.1 b.1.1.2).det g = a.1.1 := of_decide_eq_true hacc
  have hnb' : ¬ (EM (singleTr (m (Pub.det g))
        (a.2 ++ (b.2 ++ ((G.commitAt b.1.1.1 b.1.1.2).withTrace.det g).2))) ∨
      extEnc W (singleTr (m (Pub.det g)) a.2) (root a.1.1) ≠
        extEnc W (singleTr (m (Pub.det g))
          (a.2 ++ (b.2 ++ ((G.commitAt b.1.1.1 b.1.1.2).withTrace.det g).2))) (root a.1.1)) := by
    simpa [BadW] using hnb
  obtain ⟨h1, h2⟩ := not_or.1 hnb'
  have hrun : RunsIn ((G.commitAt b.1.1.1 b.1.1.2).withTrace.det g).2
      (G.commitAt b.1.1.1 b.1.1.2) a.1.1 := by
    have h0 := OnBytes.K.Arm.runsIn_ownLog g (hNC b.1.1.1 b.1.1.2)
    rwa [hkey] at h0
  have hansC := OnBytes.Slice.support_withTrace_ans g Ct a ha
  have hansP := OnBytes.Slice.support_withTrace_ans g (P1 a.1.2) b hb
  have hansV := OnBytes.Slice.support_withTrace_ans g (G.commitAt b.1.1.1 b.1.1.2)
    ((G.commitAt b.1.1.1 b.1.1.2).withTrace.det g) (by
      rw [OnBytes.Slice.runEager_withTrace_det g _ (hNC _ _), PMF.support_pure]
      rfl)
  have hans : ∀ e ∈ a.2 ++ (b.2 ++ ((G.commitAt b.1.1.1 b.1.1.2).withTrace.det g).2),
      e.2.2 = g e.1 e.2.1 := fun e he =>
    (List.mem_append.1 he).elim (hansC e) fun he' =>
      (List.mem_append.1 he').elim (hansP e) (hansV e)
  have hE := hgood g a.1.1 b.1.1.1 b.1.1.2 a.2 b.2 _ hans hrun h1 (not_not.1 h2)
  rcases hbad with h | h
  · refine h ?_
    show b.1.1 ∈ (Special.toPair (openingRelation I')).L (E.Ei a.1.1 a.2)
    rw [hE]
    exact ⟨(), rfl⟩
  · refine h ?_
    show (Special.toPair (openingRelation I')).no' (E.Ei a.1.1 a.2) b.1.1 ()
    rw [hE]
    exact rfl

end TypedOracleCompiler.Compile.Batch.Cms

#print axioms Rom.withOpenings_V_rom
#print axioms Rom.binding_withOpenings_rom
#print axioms TypedOracleCompiler.Compile.Batch.Cms.binding_of_badW
