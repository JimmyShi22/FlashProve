-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/OneWorldAsk.lean: the step to one oracle where the analysis of a compiled verifier
holds only of traces in which certain queries stand before others.

Why. `JudgeAt` (OnBytes/TypedOracleCompiler/Slice/OneWorldJ.lean) asks of a compiled verifier's analysis: outside a
set of traces whose probability it bounds, an accepted run means that the strings under its roots
are in the language. Its third clause has no place for a condition on the ORDER of a trace. For a
stored table with a record the analysis needs one: the queries by which the table's seed is drawn
stand before a first query that holds the table's root. That order cannot go into that set: a maker
can leave it out with probability 1. It is had by making an algorithm ask these queries itself. This
file does that INSIDE THE PROOF of the step to one oracle, among the typed oracles, behind the
passage from bit strings to typed points: there the algorithm of the proof (maker, announcement of
roots, checker, the compiled verifier's run) is made to ask first, whole. So the experiment and the
event do not turn, nothing is asked of a maker, and the price is a factor on the count, in typed
queries.

Main definitions: `JudgeAtAsk W J e pre`: `JudgeAt` with its third clause asked only of traces that
ask first (`AsksFirst`, OnBytes/Slice/WrapBetween.lean) and hold one family's answers, so that no
query stands in them with two answers; `pre`: what is to be asked before a typed query.
Main theorems.
 `JudgeAt.ask` `JudgeAt` gives `JudgeAtAsk`, whatever is asked first.
 `short_coreJ` the core of `short_typedJ`, under one family of oracle functions: that proof's text.
 `short_typedJ_ask`, `one_worldJ_ask` `short_typedJ` and `one_worldJ` from `JudgeAtAsk`, with the
     count multiplied by 1 + n.

What is not claimed. No `pre` is given HERE, and `JudgeAtAsk` is shown here of nothing but what has
`JudgeAt`. One `pre`, with its three laws: `preSeed` (OnBytes/TypedOracleCompiler/Slice/SeedFirstAsk.lean,
JudgeOff.lean); there `JudgeAtAsk` is drawn from hypotheses that nobody has met. At a `pre` that
asks nothing `JudgeAtAsk` is weaker than `JudgeAt`: its third clause is asked only of traces that
hold one family's answers. `AsksFirst pre F tr` says that tr is SOME lengthened trace: "before EVERY
entry of tr stands what `pre` asks for it" follows only if `pre` asks nothing for its own queries
(`asksFirst_before`, WrapBetween.lean). `hb` (the reading reads the same off a trace and off the
lengthened trace) is a hypothesis; for a `pre` that asks neither the leaves' nor the vertices'
oracle: `Reading.blind_of_asksOnly` (OnBytes/TypedOracleCompiler/Slice/ReadingBlind.lean). The second clause of
`JudgeAtAsk`, closed under appending, is not used. THE FACTOR 1 + n STANDS ON THE WHOLE COUNT, and
so on the error e of ALL the analysis' lanes, though what is asked first belongs to one. The fourth
clause of `JudgeAtAsk` is `JudgeAt`'s: asked of all traces. All limits in the head of OneWorldJ.lean
hold here too; the bound says nothing once it reaches 1.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.OneWorldJ
import OnBytes.Slice.WrapBetween

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop MeasureTheory
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal
open OnBytes.Slice (noCoin_of_detBound fst_of_mem_support twoExp twoExpOne_glue
    fst_down_of_mem_support
  Pr_twoExp_det measurable_twoExp_det)
open OnBytes.Slice (between lenB lenB_append between_law between_bound AsksFirst mem_lenB lenB_ans
  support_withTrace_ans)

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {β δ Out : Type}

/-- `JudgeAt`, with its third clause asked only of traces that ask first and hold one family's
answers. `pre`: what is to be asked, among the typed oracles, before a typed query. The set of
traces has the bound of `JudgeAt` for EVERY algorithm. That it holds every trace with an accepted
run on an output whose strings are outside the language is asked only of the traces tr for which
there is a family F of oracle functions such that (1) tr is a lengthened trace under F
(`AsksFirst`: some trace with, before each of ITS entries, the log under F of what `pre` asks for
that entry), and (2) every entry of tr holds F's own answer: so no query stands in tr with two
answers. -/
def JudgeAtAsk (W : QueryLayout lam L) (J : Judge W Out) (εs : ℝ≥0∞)
    (pre : (o : (typedOracleFamily lam W.K L).ι) → (typedOracleFamily lam W.K L).Dom o → TypedOracleComputation lam W.K L Unit) : Prop :=
  ∃ Bad : Tc W → Prop,
    (∀ (β : Type) (A : TypedOracleComputation lam W.K L β) (t : ℕ), A.QueryBound t →
      pr A.withTrace.law {o | Bad o.2} ≤
        (t : ℝ≥0∞) * εs + 2 * ((t + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam) ∧
    (∀ tr tr', Bad tr → Bad (tr ++ tr')) ∧
    (∀ F tr o, ¬ Bad tr → AsksFirst pre F tr → (∀ e ∈ tr, e.2.2 = F e.1 e.2.1) → J.ok o →
      RunsIn tr (J.run o) true → J.Lang o ((J.roots o).map (J.R.at W tr))) ∧
    (∀ tr tr' cm, ¬ Bad (tr ++ tr') → Announced W tr cm →
      J.R.at W tr cm = J.R.at W (tr ++ tr') cm)

/-- `JudgeAt` gives `JudgeAtAsk`, whatever is asked first. -/
theorem JudgeAt.ask {W : QueryLayout lam L} {J : Judge W Out} {εs : ℝ≥0∞} (h : JudgeAt W J εs)
    (pre : (o : (typedOracleFamily lam W.K L).ι) → (typedOracleFamily lam W.K L).Dom o → TypedOracleComputation lam W.K L Unit) :
    JudgeAtAsk W J εs pre := by
  obtain ⟨Bad, h1, h2, h3, h4⟩ := h
  exact ⟨Bad, h1, h2, fun _ tr o hb _ _ => h3 tr o hb, h4⟩

/-- The core of `short_typedJ`, under one family F of oracle functions, for any set of traces
with the two properties that its proof uses. The text of that proof. -/
theorem short_coreJ (W : QueryLayout lam L) (J : Judge W Out) (F : Fam (typedOracleFamily lam W.K L))
    (Bad : Tc W → Prop)
    (hL : ∀ tr o, ¬ Bad tr → J.ok o → RunsIn tr (J.run o) true →
      J.Lang o ((J.roots o).map (J.R.at W tr)))
    (hst : ∀ tr tr' cm, ¬ Bad (tr ++ tr') → Announced W tr cm →
      J.R.at W tr cm = J.R.at W (tr ++ tr') cm)
    (B1 : TypedOracleComputation lam W.K L β) (rts : β → List (Dig lam)) (B2 : β → TypedOracleComputation lam W.K L δ)
    (sel : β → δ → Option Out)
    (hP : ∀ x ∈ (B1.withTrace.runEager F).support,
      ∀ y ∈ ((B2 x.1).withTrace.runEager F).support, ∀ o, sel x.1 y.1 = some o →
        (J.run o).det F = true ∧ J.ok o ∧ ∀ c ∈ J.roots o, c ∈ rts x.1) :
    PrCoins F (twoExp B1 B2) (winJ W J sel) ≤
      PrCoins F (joinedJ W J B1 rts B2 sel).withTrace {o | Bad o.2} := by
  unfold PrCoins
  simp only [twoExp, joinedJ, Compile.withTrace_bind, OComp.bind_assoc, OComp.withTrace,
    OComp.bind, OComp.runEager_bind, OComp.runEager, announceL_run, PMF.pure_bind]
  refine pr_bind_le_bind _ _ _ _ _ fun x hx => ?_
  rw [← runEager_withTrace_fst F (B2 x.1), PMF.bind_map]
  refine pr_bind_le_bind _ _ _ _ _ fun y hy => ?_
  show pr (PMF.pure (x, y.1)) (winJ W J sel) ≤ _
  rw [← PMF.bind_const ((runJ J (sel x.1 y.1)).withTrace.runEager F) (PMF.pure (x, y.1))]
  refine pr_bind_le_bind _ _ _ _ _ fun c hc => pr_pure_le_pure ?_
  rintro ⟨o, ho, hbad⟩
  have ho' : sel x.1 y.1 = some o := ho
  obtain ⟨hdet, hok, hroots⟩ := hP x hx y hy o ho'
  show Bad (x.2 ++ (annL W (rts x.1) ++ (y.2 ++ (c.2 ++ []))))
  by_contra hnb
  rw [ho'] at hc
  have hc' : c ∈ ((J.run o).withTrace.runEager F).support := hc
  have hc1 : c.1 = true :=
    (fst_of_mem_support F _ (noCoin_of_detBound _ _ (J.bound o)) c hc').trans hdet
  have hrun : RunsIn c.2 (J.run o) true := by
    have h3 := runsIn_of_mem_support (J.bound o) F c hc'
    rwa [hc1] at h3
  have hfull := hL _ o hnb hok (hrun.mono (fun e he =>
    List.mem_append_right x.2 (List.mem_append_right _ (List.mem_append_right y.2
      (List.mem_append_left [] he)))))
  have eassoc : x.2 ++ (annL W (rts x.1) ++ (y.2 ++ (c.2 ++ []))) =
      (x.2 ++ annL W (rts x.1)) ++ (y.2 ++ (c.2 ++ [])) := (List.append_assoc _ _ _).symm
  rw [eassoc] at hnb hfull
  have hmap : (J.roots o).map (J.R.at W ((x.2 ++ annL W (rts x.1)) ++ (y.2 ++ (c.2 ++ [])))) =
      (J.roots o).map (J.R.at W x.2) := by
    refine List.map_congr_left fun cm hcm => ?_
    have hann : TypedOracleCompiler.Compile.Batch.Announced W (x.2 ++ annL W (rts x.1)) cm :=
      List.mem_append_right _ (List.mem_map.2 ⟨cm, hroots cm hcm, rfl⟩)
    rw [← hst _ _ cm hnb hann, at_append_annL]
  rw [hmap] at hfull
  exact hbad hfull

/-- The bound in two phases, under the typed random oracles, from `JudgeAtAsk`. As
`short_typedJ`, with the count multiplied by 1 + n, where `pre` asks at most n queries. In the proof
the algorithm "first phase, announcement, second phase, the judge's run" is made to ask first,
WHOLE: the judge's own queries too. Asked beside: `pre` tosses no coin; `hb`: the judge's reading
reads the same off a trace and off the trace lengthened by what `pre` asks. The experiment and the
event are `short_typedJ`'s: no maker is asked to ask anything. -/
theorem short_typedJ_ask (W : QueryLayout lam L) (J : Judge W Out) (εs : ℝ≥0∞)
    (pre : (o : (typedOracleFamily lam W.K L).ι) → (typedOracleFamily lam W.K L).Dom o → TypedOracleComputation lam W.K L Unit) (n : ℕ)
    (hn : ∀ o q, (pre o q).NoCoin) (hq : ∀ o q, (pre o q).QueryBound n)
    (hb : ∀ F tr cm, J.R.at W (lenB pre F tr) cm = J.R.at W tr cm)
    (h : JudgeAtAsk W J εs pre)
    (B1 : TypedOracleComputation lam W.K L β) (rts : β → List (Dig lam)) (B2 : β → TypedOracleComputation lam W.K L δ)
    (sel : β → δ → Option Out) (t a tR : ℕ) (h1 : B1.QueryBound t)
    (ha : ∀ b, (rts b).length ≤ a) (h2 : ∀ b, (B2 b).QueryBound tR)
    (hP : ∀ (F : Fam (typedOracleFamily lam W.K L)), ∀ x ∈ (B1.withTrace.runEager F).support,
      ∀ y ∈ ((B2 x.1).withTrace.runEager F).support, ∀ o, sel x.1 y.1 = some o →
        (J.run o).det F = true ∧ J.ok o ∧ ∀ c ∈ J.roots o, c ∈ rts x.1) :
    Rom.Pr (twoExp B1 B2) (fun _ => winJ W J sel) ≤
      (((t + a + tR + J.tV) * (1 + n) : ℕ) : ℝ≥0∞) * εs +
        2 * (((t + a + tR + J.tV) * (1 + n) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  obtain ⟨Bad, hrare, -, hL, hst⟩ := h
  refine le_trans ?_ (hrare _ (between pre (joinedJ W J B1 rts B2 sel)) _
    (between_bound pre n hq _ _ (joinedJ_queryBound W J rts sel h1 ha h2)))
  rw [← Pr_eq_law]
  refine MeasureTheory.lintegral_mono fun F => ?_
  have e : PrCoins F (between pre (joinedJ W J B1 rts B2 sel)).withTrace {o | Bad o.2} =
      PrCoins F (joinedJ W J B1 rts B2 sel).withTrace {o | Bad (lenB pre F o.2)} := by
    unfold PrCoins
    rw [between_law pre hn F, pr_map]
    rfl
  show PrCoins F (twoExp B1 B2) (winJ W J sel) ≤ _
  rw [e]
  refine le_trans (short_coreJ W J F
    (fun tr => Bad (lenB pre F tr) ∨ ¬ ∀ e ∈ tr, e.2.2 = F e.1 e.2.1)
    (fun tr o hnb hok hrun => ?_) (fun tr tr' cm hnb hann => ?_) B1 rts B2 sel (hP F))
    (Prob.pr_mono_support _ fun z hz h =>
      h.resolve_right (not_not.2 (support_withTrace_ans F _ z hz)))
  · have h3 := hL F _ o (not_or.1 hnb).1 ⟨tr, rfl⟩
      (lenB_ans pre hn F tr (not_not.1 (not_or.1 hnb).2)) hok
      (hrun.mono fun e he => mem_lenB pre F tr e he)
    have em : (J.roots o).map (J.R.at W (lenB pre F tr)) = (J.roots o).map (J.R.at W tr) :=
      List.map_congr_left fun cm _ => hb F tr cm
    rwa [em] at h3
  · have hnb' : ¬ Bad (lenB pre F tr ++ lenB pre F tr') := by
      rw [← lenB_append]
      exact (not_or.1 hnb).1
    have h4 := hst _ _ cm hnb' (mem_lenB pre F tr _ hann)
    rw [← lenB_append, hb, hb] at h4
    exact h4

/-- The step to one oracle, from `JudgeAtAsk`. `one_worldJ` with the count multiplied by 1 + n.
The experiment and the event are that theorem's: a maker with at most t queries to the one oracle on
bit strings, which is asked to ask NOTHING first; a checker without coins. What is asked first is
asked in the proof alone, among the typed oracles, behind the passage from bit strings to typed
points: n counts typed queries. -/
theorem one_worldJ_ask {γ : Type} (W : QueryLayout lam L) (J : Judge W Out) (εs : ℝ≥0∞)
    (pre : (o : (typedOracleFamily lam W.K L).ι) → (typedOracleFamily lam W.K L).Dom o → TypedOracleComputation lam W.K L Unit) (n : ℕ)
    (hpn : ∀ o q, (pre o q).NoCoin) (hpq : ∀ o q, (pre o q).QueryBound n)
    (hb : ∀ F tr cm, J.R.at W (lenB pre F tr) cm = J.R.at W tr cm)
    (h : JudgeAtAsk W J εs pre) (m : OracleCoding (typedOracleFamily lam W.K L) lam)
        (hl : m.blocks TypedOracleCompiler.Compile.Batch.OracleName.leaf = 1)
    (hn : m.blocks TypedOracleCompiler.Compile.Batch.OracleName.node = 1) (chk : γ → OComp (rom lam) (Option Out))
    (rts : γ → List (Dig lam)) (tR a : ℕ) (hnc : ∀ x, (chk x).NoCoin)
    (hq : ∀ x, (chk x).QueryBound tR) (ha : ∀ x, (rts x).length ≤ a)
    (hfit : ∀ (g : Fam (rom lam)) (x : γ) (o : Out), (chk x).det g = some o →
      (J.run o).det (readBlocks m g) = true ∧ J.ok o)
    (hrt : ∀ (g : Fam (rom lam)) (x : γ) (o : Out), (chk x).det g = some o →
      ∀ r ∈ J.roots o, r ∈ rts x)
    (A : OComp (rom lam) γ) (t : ℕ) (hA : A.QueryBound t) :
    Rom.Pr (twoExp A chk) (fun _ => winJOne W m J fun _ y => y) ≤
      (((t + a + tR + J.tV) * (1 + n) : ℕ) : ℝ≥0∞) * εs +
        2 * (((t + a + tR + J.tV) * (1 + n) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  have e1 : winJOne W m J (fun (_ : γ) (y : Option Out) => y) =
      (fun z : (γ × Trace (rom lam)) × Option Out =>
        ((z.1.1, singleTr m z.1.2), z.2)) ⁻¹' winJ W J fun _ y => y := rfl
  have hF : ∀ F : Fam (typedOracleFamily lam W.K L),
      PrCoins (glue m F) (twoExp A chk) (winJOne W m J fun _ y => y) =
        PrCoins F (twoExp (down m A) fun b => down m (chk b)) (winJ W J fun _ y => y) :=
    fun F => by
      unfold PrCoins
      rw [e1, ← pr_map, twoExpOne_glue, pr_map, ← winJ_single W m hl hn J]
  have hP : Rom.Pr (twoExp A chk) (fun _ => winJOne W m J fun _ y => y) =
      Rom.Pr (twoExp (down m A) fun b => down m (chk b)) (fun _ => winJ W J fun _ y => y) := by
    unfold Rom.Pr
    rw [lintegral_glue m (fun g => PrCoins g (twoExp A chk) (winJOne W m J fun _ y => y))]
    · simp only [hF]
    · simp only [hF]
      exact measurable_PrCoins _ _
  rw [hP]
  refine short_typedJ_ask W J εs pre n hpn hpq hb h (down m A) rts (fun b => down m (chk b))
    (fun _ y => y) t a tR
    (queryBound_down m A t hA) ha (fun b => queryBound_down m (chk b) tR (hq b))
    fun F x _ y hy o ho => ?_
  have hy1 : y.1 = (chk x.1).det (glue m F) := fst_down_of_mem_support m F _ (hnc x.1) y hy
  have hd : (chk x.1).det (glue m F) = some o := hy1.symm.trans ho
  have h3 := hfit (glue m F) x.1 o hd
  rw [readBlocks_glue] at h3
  exact ⟨h3.1, h3.2, hrt (glue m F) x.1 o hd⟩

end TypedOracleCompiler.Slice
