-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/OneWorldJ.lean: the step from a compiled verifier's analysis under typed random
oracles to a checker that asks one random oracle on bit strings, stated once for any such verifier.

OnBytes/Slice/OneWorld.lean makes that step for the library's compiled Link verifier and the
library's own reading of the strings under two roots. The proof uses five things of that verifier:
what a checker returns; the verifier's run and a bound on its queries; the list of roots; the
reading; and the analysis' conclusion. This file takes the first four, with a language and a side
condition on the checker's output, as data (`Judge`), and the conclusion as a hypothesis
(`JudgeAt`), and makes the step for all. In the code e is εs.

Main definitions.
 `Judge W Out`   a compiled verifier as the step uses it: its run on what a checker returns (`Out`),
                 a bound on its queries, the external roots in order, a reading of the string under
                 a root (`Reading`, OnBytes/Slice/Reading.lean), a language of the strings under
                 these roots, and what a checker owes of its output beside the run's yes (`ok`).
 `JudgeAt W J e` the analysis' conclusion: a set of bad traces that is rare (at most
                 t * e + 2 (t + 1)^2 / 2^lam for t queries), closed under appending, outside which
                 an accepted output that is `ok` has its strings in the language, and outside which
                 what is read under an announced root does not change when the trace grows.
 `winJ`, `winJOne`   the events.
Main theorems.
 `short_typedJ`  under the typed random oracles, for an algorithm in two phases.
 `one_worldJ`    over one random oracle on bit strings: a maker with at most t queries; a checker
                 without coins with at most tR. With probability at most
                 (t + a + tR + tV) * e + 2 (t + a + tR + tV + 1)^2 / 2^lam the checker returns
                 something while the strings that are read off the one-block entries of THE MAKER's
                 OWN TRACE under its roots are outside the language. a bounds the number of roots
                 that are read off the maker's output; tV is the judge's bound.

How. As in OnBytes/Slice/OneWorld.lean. In the proof, and in no statement on one oracle, a typed
algorithm is put together from the maker, an announcement of the roots (queries to the marker oracle
`ann`, which stands for no hash call and off which nothing is read), the checker and the judge's
run.

What is not claimed. That any judge meets `JudgeAt`: judge and e are variables, and all content lies
there. That any checker meets `hfit`; that an implementation m exists for a given interface, or
spells a typed query as a program's hash call. A checker that always refuses meets `hfit`, and the
event is then empty; so does one that says yes under few oracles only. Nothing here says that a
checker says yes on anything. What a reading is worth is said at `Reading`. The roots are the
maker's choice. Nothing reads bytes. Nothing on the program (the Lean port built from OnBytes/), on
the C++ verifier or on BLAKE2b. The bound says nothing once it reaches 1.

-/
import OnBytes.Slice.StableLeaf
import OnBytes.Slice.Reading

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Prob Compile Compile.Batch MeasureTheory
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} {β δ Out : Type}

/-! ## A compiled verifier as the step uses it -/

/-- What the analysis of one compiled verifier speaks of, in the form that the step to one oracle
uses. -/
structure Judge (W : QueryLayout lam L) (Out : Type) where
  /-- the compiled verifier on what a checker returns -/
  run : Out → TypedOracleComputation lam W.K L Bool
  /-- a bound on its queries -/
  tV : ℕ
  /-- it tosses no coin and asks at most tV queries -/
  bound : ∀ o, DetBound (run o) tV
  /-- the external roots, in order -/
  roots : Out → List (Dig lam)
  /-- the reading of the string under a root -/
  R : Reading L
  /-- the language, of the strings under these roots -/
  Lang : Out → List (Fin L.wordLength → L.Symbol) → Prop
  /-- what a checker owes of its output beside the run's yes -/
  ok : Out → Prop

/-- **The analysis' conclusion on a compiled verifier.** Some set of traces is rare, is closed under
appending queries, holds every trace with an accepted run on an output that is `ok` and whose
strings are outside the language, and holds every trace along which what is read under an announced
root changes. The set stands under "there is": the form is for use in one world, where the bound on
the set and the run stand under the same random oracles. For a run under one fixed family of oracle
functions it would be true for free. The second clause, closed under appending, is not used in this
file. -/
def JudgeAt (W : QueryLayout lam L) (J : Judge W Out) (εs : ℝ≥0∞) : Prop :=
  ∃ Bad : Tc W → Prop,
    (∀ (β : Type) (A : TypedOracleComputation lam W.K L β) (t : ℕ), A.QueryBound t →
      pr A.withTrace.law {o | Bad o.2} ≤
        (t : ℝ≥0∞) * εs + 2 * ((t + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam) ∧
    (∀ tr tr', Bad tr → Bad (tr ++ tr')) ∧
    (∀ tr o, ¬ Bad tr → J.ok o → RunsIn tr (J.run o) true →
      J.Lang o ((J.roots o).map (J.R.at W tr))) ∧
    (∀ tr tr' cm, ¬ Bad (tr ++ tr') → Announced W tr cm →
      J.R.at W tr cm = J.R.at W (tr ++ tr') cm)

/-- The judge's run on what a checker returns; "no" where it returns nothing. -/
def runJ {W : QueryLayout lam L} (J : Judge W Out) : Option Out → TypedOracleComputation lam W.K L Bool
  | none => OComp.pure false
  | some o => J.run o

/-- It tosses no coin and asks at most tV queries. -/
theorem detBound_runJ {W : QueryLayout lam L} (J : Judge W Out) : ∀ y, DetBound (runJ J y) J.tV
  | none => trivial
  | some o => J.bound o

/-! ## Announcing a list of roots -/

/-- The entries that an announcement of a list of roots leaves in a trace. -/
def annL (W : QueryLayout lam L) (l : List (Dig lam)) : Tc W := l.map fun c => annK lam W.K L c

/-- Announces a list of roots: one query to the marker oracle for each. -/
def announceL (W : QueryLayout lam L) : List (Dig lam) → TypedOracleComputation lam W.K L Unit
  | [] => OComp.pure ()
  | c :: l => OComp.query (S := spec lam W.K L) Batch.OracleName.ann c fun _ => announceL W l

/-- The run of `announceL` under fixed oracles, with its trace. -/
theorem announceL_run (W : QueryLayout lam L) (F : Fam (spec lam W.K L)) :
    ∀ l : List (Dig lam), (announceL W l).withTrace.runEager F = PMF.pure ((), annL W l)
  | [] => rfl
  | c :: l => by
    show ((announceL W l).withTrace.bind fun out => OComp.pure
      (out.1, (⟨Batch.OracleName.ann, c, F Batch.OracleName.ann c⟩ : QA (spec lam W.K L)) :: out.2)).runEager F = _
    rw [OComp.runEager_bind, announceL_run W F l, PMF.pure_bind]
    rfl

/-- `announceL` asks once for each root. -/
theorem announceL_queryBound (W : QueryLayout lam L) :
    ∀ l : List (Dig lam), (announceL W l).QueryBound l.length
  | [] => trivial
  | _ :: l => fun _ => announceL_queryBound W l

/-- An announcement behind a trace changes nothing that a reading reads off it. -/
theorem at_append_annL (W : QueryLayout lam L) (R : Reading L) (tr : Tc W) (l : List (Dig lam))
    (cm : Dig lam) : R.at W (tr ++ annL W l) cm = R.at W tr cm := by
  have e : (tr ++ annL W l).filter notAnnK = tr.filter notAnnK := by
    rw [List.filter_append]
    have : (annL W l).filter notAnnK = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx
      obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
      simp [notAnnK, annK]
    rw [this, List.append_nil]
  refine R.at_congr fun j => ?_
  rw [← extLeaf_notAnn (tr ++ annL W l), e, extLeaf_notAnn]

/-! ## Two phases, under the typed oracles -/

/-- **The event**: `sel` reads an output for the judge off the two phases' outputs, and the strings
that are read off the FIRST phase's trace under its roots are outside the language. -/
def winJ (W : QueryLayout lam L) (J : Judge W Out) (sel : β → δ → Option Out) :
    Set ((β × Tc W) × δ) :=
  {z | ∃ o, sel z.1.1 z.2 = some o ∧ ¬ J.Lang o ((J.roots o).map (J.R.at W z.1.2))}

/-- The algorithm of the proof: the first phase, the announcement of the roots, the second phase,
the judge's run. It stands in no statement. -/
def joinedJ (W : QueryLayout lam L) (J : Judge W Out) (B1 : TypedOracleComputation lam W.K L β)
    (rts : β → List (Dig lam)) (B2 : β → TypedOracleComputation lam W.K L δ) (sel : β → δ → Option Out) :
    TypedOracleComputation lam W.K L Unit :=
  B1.bind fun b => (announceL W (rts b)).bind fun _ => (B2 b).bind fun d =>
    (runJ J (sel b d)).bind fun _ => OComp.pure ()

/-- The algorithm of the proof asks at most t + a + tR + tV queries. -/
theorem joinedJ_queryBound (W : QueryLayout lam L) (J : Judge W Out) {B1 : TypedOracleComputation lam W.K L β}
    (rts : β → List (Dig lam)) {B2 : β → TypedOracleComputation lam W.K L δ} (sel : β → δ → Option Out)
    {t a tR : ℕ} (h1 : B1.QueryBound t) (ha : ∀ b, (rts b).length ≤ a)
    (h2 : ∀ b, (B2 b).QueryBound tR) :
    (joinedJ W J B1 rts B2 sel).QueryBound (t + a + tR + J.tV) := by
  have h : (joinedJ W J B1 rts B2 sel).QueryBound (t + (a + (tR + (J.tV + 0)))) :=
    h1.bind fun b => ((announceL_queryBound W (rts b)).mono (ha b)).bind fun _ =>
      (h2 b).bind fun d => (detBound_runJ J (sel b d)).queryBound.bind fun _ => trivial
  exact h.mono (by omega)

/-- **The bound in two phases, under the typed random oracles.** Asked beside `JudgeAt W J e`: the
first phase asks at most t queries and the second at most tR; and `hP`: under every family F, on all
outputs that the two phases can have under F, the judge's run accepts under F what `sel` reads off
them, that output is `ok`, and its roots are among those that `rts` reads off the first phase's
output. Then with probability at most (t + a + tR + tV) * e + 2 (t + a + tR + tV + 1)^2 / 2^lam the
strings that are read off the first phase's trace under these roots are outside the language. a
bounds the number of roots that `rts` gives, and stands for as many queries to the marker oracle in
the proof. The bound says nothing once it reaches 1. -/
theorem short_typedJ (W : QueryLayout lam L) (J : Judge W Out) (εs : ℝ≥0∞) (h : JudgeAt W J εs)
    (B1 : TypedOracleComputation lam W.K L β) (rts : β → List (Dig lam)) (B2 : β → TypedOracleComputation lam W.K L δ)
    (sel : β → δ → Option Out) (t a tR : ℕ) (h1 : B1.QueryBound t)
    (ha : ∀ b, (rts b).length ≤ a) (h2 : ∀ b, (B2 b).QueryBound tR)
    (hP : ∀ (F : Fam (spec lam W.K L)), ∀ x ∈ (B1.withTrace.runEager F).support,
      ∀ y ∈ ((B2 x.1).withTrace.runEager F).support, ∀ o, sel x.1 y.1 = some o →
        (J.run o).det F = true ∧ J.ok o ∧ ∀ c ∈ J.roots o, c ∈ rts x.1) :
    Rom.Pr (twoExp B1 B2) (fun _ => winJ W J sel) ≤
      ((t + a + tR + J.tV : ℕ) : ℝ≥0∞) * εs +
        2 * ((t + a + tR + J.tV + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  obtain ⟨Bad, hrare, -, hL, hst⟩ := h
  refine le_trans ?_ (hrare _ (joinedJ W J B1 rts B2 sel) _
    (joinedJ_queryBound W J rts sel h1 ha h2))
  rw [← Pr_eq_law]
  refine MeasureTheory.lintegral_mono fun F => ?_
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
  obtain ⟨hdet, hok, hroots⟩ := hP F x hx y hy o ho'
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
    have hann : Batch.Announced W (x.2 ++ annL W (rts x.1)) cm :=
      List.mem_append_right _ (List.mem_map.2 ⟨cm, hroots cm hcm, rfl⟩)
    rw [← hst _ _ cm hnb hann, at_append_annL]
  rw [hmap] at hfull
  exact hbad hfull

/-! ## Over one oracle -/

/-- **The event over one oracle**: `sel` reads an output for the judge off the two phases' outputs,
and the strings that are read off the one-block entries of the FIRST phase's trace under its roots
are outside the language. -/
def winJOne (W : QueryLayout lam L) (m : OracleCoding (spec lam W.K L) lam) (J : Judge W Out)
    (sel : β → δ → Option Out) : Set ((β × Trace (rom lam)) × δ) :=
  {z | ∃ o, sel z.1.1 z.2 = some o ∧
    ¬ J.Lang o ((J.roots o).map (J.R.at W (singleTr m z.1.2)))}

/-- Whether the event holds is read off the one-block entries of the typed trace alone. Asked of m:
a leaf's and a vertex's answer is one block. -/
theorem winJ_single (W : QueryLayout lam L) (m : OracleCoding (spec lam W.K L) lam)
    (hl : m.blocks Batch.OracleName.leaf = 1) (hn : m.blocks Batch.OracleName.node = 1) (J : Judge W Out)
    (sel : β → δ → Option Out) :
    winJ W J sel =
      (fun z : (β × Tc W) × δ => ((z.1.1, single m z.1.2), z.2)) ⁻¹' winJ W J sel := by
  ext z
  have e : J.R.at W (single m z.1.2) = J.R.at W z.1.2 :=
    funext fun cm => J.R.at_single m hl hn z.1.2 cm
  simp only [winJ, Set.mem_setOf_eq, Set.mem_preimage, e]

/-- **The step to one oracle, for any compiled verifier.** The oracle is a function from all bit
strings to strings of lam bits, each value drawn uniformly and independently. A maker with at most t
queries, which may toss coins, puts out a value. A checker without coins, with at most tR queries to
the same oracle, refuses it or returns an output for the judge. With probability at most (t + a + tR
+ tV) * e + 2 (t + a + tR + tV + 1)^2 / 2^lam the checker returns something while the strings that
the judge's reading reads off the one-block entries of THE MAKER's OWN TRACE under the output's
roots are outside the judge's language. t and tR count strings put to the oracle, a repeated one
again; tV is the judge's bound on its typed queries; a bounds the number of roots that `rts` reads
off the maker's output. a and tV come from the proof: in the experiment no compiled verifier runs.
Asked: `JudgeAt W J e`; in m a leaf's and a vertex's answer is one block; `hfit`: under every oracle
g, the judge's run accepts what the checker returns, under the family that is read out of g through
m, and that output is `ok`; `hrt`: the output's roots are among those that `rts` gives. `hfit` is an
assumption on the checker; judge, checker and m are variables: that any checker meets it, or says
yes on anything, is not shown. The roots are the maker's choice. All content lies in `JudgeAt` at a
named language, a reading that is worth something, and a small e; the bound says nothing once it
reaches 1. Nothing on bytes, on the program, on BLAKE2b or on the C++ verifier. -/
theorem one_worldJ {γ : Type} (W : QueryLayout lam L) (J : Judge W Out) (εs : ℝ≥0∞)
    (h : JudgeAt W J εs) (m : OracleCoding (spec lam W.K L) lam) (hl : m.blocks Batch.OracleName.leaf = 1)
    (hn : m.blocks Batch.OracleName.node = 1) (chk : γ → OComp (rom lam) (Option Out))
    (rts : γ → List (Dig lam)) (tR a : ℕ) (hnc : ∀ x, (chk x).NoCoin)
    (hq : ∀ x, (chk x).QueryBound tR) (ha : ∀ x, (rts x).length ≤ a)
    (hfit : ∀ (g : Fam (rom lam)) (x : γ) (o : Out), (chk x).det g = some o →
      (J.run o).det (readBlocks m g) = true ∧ J.ok o)
    (hrt : ∀ (g : Fam (rom lam)) (x : γ) (o : Out), (chk x).det g = some o →
      ∀ r ∈ J.roots o, r ∈ rts x)
    (A : OComp (rom lam) γ) (t : ℕ) (hA : A.QueryBound t) :
    Rom.Pr (twoExp A chk) (fun _ => winJOne W m J fun _ y => y) ≤
      ((t + a + tR + J.tV : ℕ) : ℝ≥0∞) * εs +
        2 * ((t + a + tR + J.tV + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  have e1 : winJOne W m J (fun (_ : γ) (y : Option Out) => y) =
      (fun z : (γ × Trace (rom lam)) × Option Out =>
        ((z.1.1, singleTr m z.1.2), z.2)) ⁻¹' winJ W J fun _ y => y := rfl
  have hF : ∀ F : Fam (spec lam W.K L),
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
  refine short_typedJ W J εs h (down m A) rts (fun b => down m (chk b)) (fun _ y => y) t a tR
    (queryBound_down m A t hA) ha (fun b => queryBound_down m (chk b) tR (hq b))
    fun F x _ y hy o ho => ?_
  have hy1 : y.1 = (chk x.1).det (glue m F) := fst_down_of_mem_support m F _ (hnc x.1) y hy
  have hd : (chk x.1).det (glue m F) = some o := hy1.symm.trans ho
  have h3 := hfit (glue m F) x.1 o hd
  rw [readBlocks_glue] at h3
  exact ⟨h3.1, h3.2, hrt (glue m F) x.1 o hd⟩

end OnBytes.Slice
