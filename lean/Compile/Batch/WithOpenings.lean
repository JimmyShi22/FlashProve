-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/WithOpenings.lean: over the compiler's typed oracles, whoever opens a key opens it to
the index that the extractor reads from the key and its maker's queries.

`binding_withOpenings`: for every W : `QueryLayout lam L` that meets `W.OKG`, let G be a scheme over the
typed oracles whose keys hold a root, and let every outcome of its committer have the property
`TraceOpens` (Compile/Batch/TraceOpens.lean) under that root. Then `G.withOpenings`
(Rom/WithOpenings.lean: openings in place of proofs) has index binding with the index part of
`extractorBK W` and the bound 2 (tC + tP + tR + 1)² / 2^λ. tC and tP bound the queries of the
adversary's committer and opener, tR those of G's committer, which is run again.
`traceOpens_argBKE`: the compiled scheme `argBKE` is such a G, for all such W, if the decoder
returns i on an encoding of i (`L.Wired`).
How. Fix the oracle functions. Put in one trace: the adversary's committer; one query that announces
the root in its key (made in this analysis alone); the opener; G's committer, run again. Outside the
hash event `EM` on that trace (`hashEvents`, Compile/Batch/Hash.lean, bounds `EM` and `EF` together;
`EF` is not used): the run of G's committer holds an opening of every leaf of an encoding of the
index, so the string that the whole trace determines under the root decodes to that index
(`TraceOpens.dec`); and what a trace determines under a root does not change after the root has
occurred in it (`extEnc_stable`), so the first part determines the same string.
The comparison of the two experiments (`prCoins_bindingExp_le`) is that of
`TraceBinding.binding` (Compile/TraceBinding.lean), with the condition on the verifier asked under
the given oracle functions only, and not on every trace.
Limits: one opening in a run; the bound counts the committer that is run again, so it is never below
2 tR² / 2^λ; the oracles are random functions; no number here is a security level.
-/
import Compile.Batch.TraceOpens
import Compile.Batch.GlueTools
import Compile.Batch.StarKE
import Compile.TraceBinding
import Rom.WithOpenings

set_option autoImplicit false

noncomputable section

namespace Rom

variable {S : OSpec} {α : Type}

/-- The trace of `c.withCoins coins` is the trace of c at that number. -/
theorem OComp.withTrace_withCoins : ∀ (c : OComp S α) (coins : ℕ),
    (c.withCoins coins).withTrace = c.withTrace.withCoins coins
  | .pure _, _ => rfl
  | .query o q k, coins => by
      show OComp.query o q (fun r => ((k r).withCoins coins).withTrace.bind
          fun out => .pure (out.1, ⟨o, q, r⟩ :: out.2))
        = OComp.query o q fun r =>
          ((k r).withTrace.bind fun out => .pure (out.1, ⟨o, q, r⟩ :: out.2)).withCoins coins
      exact congrArg _ (funext fun r => by
        rw [OComp.withCoins_bind_pure, OComp.withTrace_withCoins (k r) coins])
  | .sample _ k, _ => OComp.withTrace_withCoins (k _) _

end Rom

namespace Compile
open Rom Prob ZKCP.Gen
open scoped ENNReal

variable {S : OSpec} {I X W PP IVK ISK Pf : Type}

/-- What an algorithm returns at a given number, it can return. -/
theorem outs_withCoins {α : Type} {f : Fam S} : ∀ (c : OComp S α) (coins : ℕ) {b : α},
    b ∈ Outs f (c.withCoins coins) → b ∈ Outs f c
  | .pure _, _, _, h => h
  | .query o q k, coins, _, h => outs_withCoins (k (f o q)) coins h
  | .sample _ k, _, _, h => mem_outs_sample.2 ⟨_, outs_withCoins (k _) _ h⟩

/-- Under given oracle functions f: if an acceptance by V outside an event `Ev` on the trace (the
committer's, the query `an v`, the prover's, V's) is right for the extracted index, then the bad
event of index binding has at most the probability of `Ev` on the trace of the four as one
algorithm. -/
theorem prCoins_bindingExp_le (R : RelPair I X W PP) (A : Arg S I X W IVK ISK Pf)
    (E : Extractor S I X W IVK Pf) (an : IVK → Σ o : S.ι, S.Dom o) (Ev : Trace S → Prop)
    (f : Fam S)
    (core : ∀ v x π (trC trP : Trace S), ∀ c ∈ Outs f (A.V v x π).withTrace, c.1 = true →
      ¬ Ev (trC ++ ⟨(an v).1, (an v).2, f (an v).1 (an v).2⟩ :: (trP ++ c.2)) →
      x ∈ R.L (E.Ei v trC) ∧ R.no' (E.Ei v trC) x (E.Ew v trC x π trP))
    {St : Type} (Ct : OComp S (IVK × St)) (Pt : St → OComp S (X × Pf)) :
    Rom.PrCoins f (bindingExp A E Ct Pt) (bindingBad R)
      ≤ Rom.PrCoins f (TraceBinding.committerProverAndVerifierRun A an Ct Pt).withTrace {o | Ev o.2} := by
  unfold Rom.PrCoins
  simp only [bindingExp, bind_eq, pure_eq, TraceBinding.committerProverAndVerifierRun, withTrace_bind, OComp.bind_assoc,
    OComp.ask, OComp.withTrace, OComp.bind, OComp.runEager_bind, OComp.runEager]
  refine pr_bind_le_bind _ _ _ _ _ fun a _ => pr_bind_le_bind _ _ _ _ _ fun b _ => ?_
  have e1 : (A.V a.1.1 b.1.1 b.1.2).runEager f
      = ((A.V a.1.1 b.1.1 b.1.2).withTrace.runEager f).map Prod.fst :=
    (runEager_withTrace_fst f _).symm
  rw [e1, PMF.bind_map]
  refine pr_bind_le_bind _ _ _ _ _ fun c hc => pr_pure_le_pure ?_
  rintro ⟨hacc, hbad⟩
  by_contra hnb
  have hnb' : ¬ Ev (a.2 ++ ⟨(an a.1.1).1, (an a.1.1).2, f (an a.1.1).1 (an a.1.1).2⟩ ::
      (b.2 ++ c.2)) := by
    simpa using hnb
  obtain ⟨h1, h2⟩ := core a.1.1 b.1.1 b.1.2 a.2 b.2 c hc hacc hnb'
  rcases hbad with hb | hb
  · exact hb h1
  · exact hb h2

/-- What the verifier of `G.withOpenings` returns with its trace: a run of G's committer with that
trace, and whether the verifier's key that it returns is the given one. -/
theorem outs_withOpenings_V (G : Arg S I X W IVK ISK Pf) (f : Fam S) (key : IVK) (x : I × ℕ)
    (π : Unit) : ∀ c ∈ Outs f (G.withOpenings.V key x π).withTrace,
      ∃ o ∈ Outs f (G.C x.1).withTrace, c.2 = o.2 ∧ (c.1 = true → o.1.1 = key) := by
  classical
  intro c hc
  have hc' : c ∈ Outs f ((((G.C x.1).withCoins x.2).bind fun keys => OComp.pure keys.1).bind
      fun key' => OComp.pure (decide (key' = key))).withTrace := hc
  rw [withTrace_bind, withTrace_bind] at hc'
  obtain ⟨a, ha, h1⟩ := mem_outs_bind.1 hc'
  obtain ⟨o, ho, h2⟩ := mem_outs_bind.1 ha
  obtain ⟨b, hb, h3⟩ := mem_outs_bind.1 h2
  obtain ⟨d, hd, h4⟩ := mem_outs_bind.1 h1
  have eb : b = (o.1.1, []) := mem_outs_pure.1 hb
  have ea : a = (b.1, o.2 ++ b.2) := mem_outs_pure.1 h3
  have ed : d = (decide (a.1 = key), []) := mem_outs_pure.1 hd
  have ec : c = (d.1, a.2 ++ d.2) := mem_outs_pure.1 h4
  rw [OComp.withTrace_withCoins] at ho
  refine ⟨o, outs_withCoins _ _ ho, ?_, ?_⟩
  · rw [ec, ed, ea, eb]
    simp
  · intro ht
    rw [ec, ed, ea, eb] at ht
    exact of_decide_eq_true ht

/-- The verifier of `G.withOpenings` makes no more queries than G's committer. -/
theorem queryBound_withOpenings_V (G : Arg S I X W IVK ISK Pf) (tR : ℕ)
    (hq : ∀ i, (G.C i).QueryBound tR) (key : IVK) (x : I × ℕ) (π : Unit) :
    (G.withOpenings.V key x π).QueryBound tR := by
  classical
  have h1 : (((G.C x.1).withCoins x.2).bind fun keys => OComp.pure keys.1).QueryBound (tR + 0) :=
    (OComp.QueryBound.withCoins (G.C x.1) tR x.2 (hq x.1)).bind fun _ => trivial
  have h2 : ((((G.C x.1).withCoins x.2).bind fun keys => OComp.pure keys.1).bind
      fun key' => OComp.pure (decide (key' = key))).QueryBound (tR + 0 + 0) :=
    h1.bind fun _ => trivial
  exact h2

end Compile

namespace Compile.Batch
open Iop Rom Prob ZKCP
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- Index binding of `G.withOpenings` over the typed oracles, for compiler parameters W that meet
`W.OKG`, for every scheme G whose committer's outcomes all have the property `TraceOpens` under the
root in the key. tR bounds the queries of G's committer at every index. -/
theorem binding_withOpenings (W : QueryLayout lam L) (hW : W.OKG) {Xg Wg ISKg Pfg : Type}
    (G : Gen.Arg (spec lam W.K L) I Xg Wg (IVKK lam L) ISKg Pfg) (tR : ℕ)
    (hq : ∀ i, (G.C i).QueryBound tR)
    (hG : ∀ (f : Fam (spec lam W.K L)) (i : I), ∀ o ∈ Outs f (G.C i).withTrace,
      TraceOpens W i o.1.1.1.cm o.2) :
    Gen.HasIndexBindingWith (Special.toPair (openingRelation I)) G.withOpenings
      (extractorBK W).withOpenings
      fun tC tP => 2 * ((tC + tP + tR + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  intro tC tP St Ct Pt hC hP
  have hV := queryBound_withOpenings_V G tR hq
  have hJ : (TraceBinding.committerProverAndVerifierRun G.withOpenings
      (fun v : IVKK lam L => (⟨OracleName.ann, v.1.cm⟩ : Σ o : (spec lam W.K L).ι, (spec lam W.K L).Dom o))
      Ct Pt).QueryBound (tC + tP + tR + 1) := by
    have h' : (TraceBinding.committerProverAndVerifierRun G.withOpenings
        (fun v : IVKK lam L =>
          (⟨OracleName.ann, v.1.cm⟩ : Σ o : (spec lam W.K L).ι, (spec lam W.K L).Dom o))
        Ct Pt).QueryBound (tC + (1 + (tP + (tR + 0)))) := by
      unfold TraceBinding.committerProverAndVerifierRun
      exact hC.bind fun a =>
        (detBound_ask (S := spec lam W.K L) OracleName.ann a.1.1.cm).queryBound.bind fun _ =>
          (hP a.2).bind fun xp => (hV a.1 xp.1 xp.2).bind fun _ => trivial
    exact h'.mono (by omega)
  refine le_trans (MeasureTheory.lintegral_mono fun f =>
    prCoins_bindingExp_le (Special.toPair (openingRelation I)) G.withOpenings (extractorBK
        W).withOpenings
      (fun v : IVKK lam L => (⟨OracleName.ann, v.1.cm⟩ : Σ o : (spec lam W.K L).ι, (spec lam W.K L).Dom o))
      (fun tr => EM tr ∨ EF tr) f ?_ Ct Pt) ?_
  · intro v x π trC trP c hc hacc hnb
    obtain ⟨o, ho, h2, h1⟩ := outs_withOpenings_V G f v x π c hc
    have hk : o.1.1 = v := h1 hacc
    have hEM : ¬ EM (trC ++ annE W v.1.cm (f OracleName.ann v.1.cm) :: (trP ++ c.2)) :=
      fun h => hnb (Or.inl h)
    have hH : TraceOpens W x.1 v.1.cm (trC ++ annE W v.1.cm (f OracleName.ann v.1.cm) :: (trP ++ c.2)) := by
      have h0 := hG f x.1 o ho
      rw [hk, ← h2] at h0
      exact TraceOpens.mono (fun e he => List.mem_append_right _
        (List.mem_cons_of_mem _ (List.mem_append_right _ he))) h0
    have hdec := TraceOpens.dec hW hEM hH
    have hst : extEnc W (trC ++ [annE W v.1.cm (f OracleName.ann v.1.cm)]) v.1.cm
        = extEnc W (trC ++ annE W v.1.cm (f OracleName.ann v.1.cm) :: (trP ++ c.2)) v.1.cm :=
      extEnc_stable hEM ⟨trP ++ c.2, by simp⟩
        (occursIn_of_announced (List.mem_append_right _ (List.mem_singleton.2 rfl)))
    rw [extEnc_ann] at hst
    have hEi : (extractorBK W).withOpenings.Ei v trC = some x.1 := by
      show L.decodeIndex (extEnc W trC v.1.cm) = some x.1
      rw [hst, hdec]
    rw [hEi]
    exact ⟨⟨(), rfl⟩, rfl⟩
  · exact le_trans (le_of_eq (Pr_eq_law _ _)) (hashEvents _ _ hJ)

/-- The compiled scheme `argBKE`, for every W : `QueryLayout lam L` that meets `W.OKG`, if the decoder
returns i on an encoding of i (`L.Wired`): every outcome of its committer has the property
`TraceOpens` under the root in its key. The committer is `C` followed by a function of its result.
-/
theorem traceOpens_argBKE (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (hwd : L.Wired) (hW :
          W.OKG)
    (f : Fam (spec lam W.K L)) (i : I) :
    ∀ o ∈ Outs f ((argBKE W WP p).C i).withTrace, TraceOpens W i o.1.1.1.cm o.2 := by
  intro o ho
  have ho' : o ∈ Outs f ((C W WP p i).bind fun o =>
      OComp.pure ((o.1, linksOf (keyOf o.2.1)), o.2)).withTrace := ho
  rw [withTrace_bind] at ho'
  obtain ⟨a, ha, h1⟩ := mem_outs_bind.1 ho'
  obtain ⟨b, hb, h2⟩ := mem_outs_bind.1 h1
  have eb : b = (((a.1.1, linksOf (keyOf a.1.2.1)), a.1.2), []) := mem_outs_pure.1 hb
  have eo : o = (b.1, a.2 ++ b.2) := mem_outs_pure.1 h2
  rw [eo, eb]
  show TraceOpens W i a.1.1.cm (a.2 ++ [])
  rw [List.append_nil]
  exact traceOpens_C W WP p hwd hW i f a ha

end Compile.Batch
