-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/KnowBinding.lean: from traces to the experiment of index binding, with the named witness
extractor (`extractorBW`, CompileK/KnowExt.lean).

This file is about index binding, the soundness notion of a commit-and-prove argument, with a
witness extractor: the step from a statement on lists of queries to the security experiment.
CompileK/KnowSoundSpec.lean (`BcsAtK`) speaks of an event Bad on traces, and of the witness read off
a trace that contains the verifier's queries. In the experiment of the binding definition
(ZKCP/Gen.lean) the witness extractor is handed the committer's trace and the prover's, and not the
verifier's. This file closes that gap.
  Part 1. What the extractor reads depends on a trace only through its entries at the two Merkle
  oracles of trees over oracles (`readB_of_filter`).
  Part 2. The slot's chain asks no Merkle oracle (`noMk_chainB`), and every root that it deals out
  to a round occurs in a trace that holds the chain's queries (`roots_occur_chainB`).
  Part 3. `GoodRun`, what is known of the trace of an accepting verifier of the analysis: it begins
  with entries that are no queries to these two Merkle oracles and at which all the roots of the
  slot's string (`π.piB`) that belong to a round occur. `coreBK`: outside Bad, after such a run, the
  index read off the committer's trace and the witness read off the committer's and the prover's
  trace are in `Rno`.
  Part 4. `bindingOfRun`: index binding from any verifier of the analysis that decides as V does,
  flips no coin and has good runs. The bound counts its queries.
  Part 5. A first proof: the verifier of the analysis announces the roots of the slot's string that
  belong to a round (queries to the oracle with empty answers) and then runs V (`bindingBatchKA`,
  with 2 · rounds more queries on the prover's account).
  Part 6. The proof with the exact bound: the verifier of the analysis runs V's three checks in
  another order, the slot's first, so that the slot's own chain is the announcement.
  `bindingBatchKAt` (from `BcsAtK`) and `bindingBatchK : Spec.bindingBatchK`, with exactly the bound
  `epsB` of the theorem on languages (`bindingBatchAt`, Compile/Batch/GlueBinding.lean).
Each under the hypotheses of its statement. The scheme here is the base scheme `argB` in the syntax
with witnesses. The step up to the scheme with the links in the key is in
CompileK/KnowBindingUp.lean.

Limits: the verifiers of Parts 5 and 6 are objects of the analysis; the scheme's verifier is V,
unchanged, and the theorems are about V. The honest prover plays no part: index binding reads a
scheme through V alone. Nothing is said of the running time of the extractor.
No statement here ranges over all traces that contain V's queries: for a real witness such a
statement is false (a trace may hold, between the prover's entries and V's, an honest prover's whole
run).
At a bound of 1 or more the theorems are empty, as every bound on a probability is.

Terms: lean/GLOSSARY.md.
-/
import CompileK.KnowSound
import Compile.Batch.GlueBinding
import Rom.AsksIn

set_option autoImplicit false

noncomputable section

namespace Compile.Batch
open Iop Rom Prob
open scoped ENNReal

variable {I X Wn : Type} {lam : ℕ} {L : BatchProtocol I X}

/-! ## Part 1. What the extractor reads of a trace -/

section Read
variable {K : ℕ}

/-- The names of the two Merkle oracles of trees over oracles. -/
def mkON : OracleName → Bool
  | .leaf => true
  | .node => true
  | _ => false

/-- An entry at one of these two oracles. -/
def isMk (e : QA (spec lam K L)) : Bool := mkON e.1

theorem extLeaf_filter (tr : Trace (spec lam K L)) (d : ℕ) (c : Dig lam) (j : ℕ) :
    extLeaf (tr.filter isMk) d c j = extLeaf tr d c j := by
  unfold extLeaf
  refine Local.preimage_filter (pairM lam K L) _ ?_ ?_ tr _ c
  · rintro ⟨o, q, r⟩ ho
    cases o <;> first | rfl | (simp [isMk, mkON] at ho)
  · rintro ⟨o, q, r⟩ ho
    cases o <;> first | rfl | (simp [isMk, mkON] at ho)

/-- What `readStar` reads (CompileK/KnowExt.lean: the oracles of τ∗) depends on the trace only
through what it determines under digests. -/
theorem readStar_ext {tr tr' : Trace (spec lam K L)}
    (h : ∀ d c j, extLeaf tr d c j = extLeaf tr' d c j) :
    ∀ (s : Shape) (A : RoundSplits s) (ws : RoundsQueryLayout lam K s A)
        (prjS : (p : OPos s) → Body L → Option (OSym s p)) (rts : RootsOfChain lam s) (pls : Plains s),
      readStar tr s A ws prjS rts pls = readStar tr' s A ws prjS rts pls
  | [], _, _, _, _, _ => funext fun p => nomatch p
  | _ :: s, (_, A), (w, ws), prjS, (rt, rts), (pl, pls) => by
      funext p
      rcases p with p | p
      · show Round.rd _ (msgStar tr w (fun p => prjS (.inl p)) rt pl).1 p =
          Round.rd _ (msgStar tr' w (fun p => prjS (.inl p)) rt pl).1 p
        rw [msgStar_congr w (fun p => prjS (.inl p)) pl fun c _ d j => h d c j]
      · exact congrFun (readStar_ext h s A ws (fun p => prjS (.inr p)) rts pls) p

end Read

/-- Two traces with the same Merkle entries, in the same order, give the extractor the same oracles.
-/
theorem readB_of_filter (W : QueryLayout lam L) {tr tr' : Tc W}
    (h : tr.filter isMk = tr'.filter isMk) (π : OneProtocolProof lam L.onlineBatch) : readB W tr π = readB W tr' π :=
  readStar_ext (fun d c j => by rw [← extLeaf_filter tr, h, extLeaf_filter]) _ _ _ _ _ _

/-! ## Part 2. The chain of a slot: no Merkle query; its roots occur -/

section Chain
variable {K : ℕ}

/-- The algorithm asks neither of the two Merkle oracles of trees over oracles. -/
abbrev NoMk {α : Type} (c : TypedOracleComputation lam K L α) : Prop :=
  OComp.AsksIn (S := spec lam K L) (fun o _ => mkON o = false) c

theorem noMk_pure {α : Type} (a : α) : NoMk (OComp.pure a : TypedOracleComputation lam K L α) := trivial

theorem noMk_askV (o : OracleName) (ho : mkON o = false) (q : domOf lam L o) :
    NoMk (askTypedOracle (L := L) (K := K) o q) :=
  ⟨ho, fun _ => trivial⟩

theorem noMk_chainB (t : Tag) (cms : List (Dig lam)) (x : Option X)
    (salt : Bits) (rtreq : Dig lam) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t))
        (i : ℕ) (ph : Phase lam) (rts : List (Dig lam)) (pls : Plains s),
      NoMk (recomputeChain (L := L) t cms x salt rtreq s A W embP i ph rts pls)
  | [], _, _, _, _, _, _, _ => noMk_pure _
  | _ :: s, (a, A), (w, W), embP, i, ph, rts, (pl, pls) => by
      simp only [recomputeChain]
      split
      · split
        · simp only [bind_eq]
          exact OComp.AsksIn.bind
            (fun ans =>
              OComp.AsksIn.bind (fun r => noMk_pure _)
                (noMk_chainB t cms x salt rtreq s A W _ _ _ _ pls))
            (noMk_askV _ rfl _)
        · exact noMk_pure _
      · split
        · simp only [bind_eq]
          exact OComp.AsksIn.bind
            (fun ans =>
              OComp.AsksIn.bind (fun r => noMk_pure _)
                (noMk_chainB t cms x salt rtreq s A W _ _ _ _ pls))
            (noMk_askV _ rfl _)
        · exact noMk_pure _
      · split
        · split
          · simp only [bind_eq]
            exact OComp.AsksIn.bind
              (fun c =>
                OComp.AsksIn.bind
                  (fun ans =>
                    OComp.AsksIn.bind (fun r => noMk_pure _)
                      (noMk_chainB t cms x salt rtreq s A W _ _ _ _ pls))
                  (noMk_askV _ rfl _))
              (noMk_askV _ rfl _)
          · exact noMk_pure _
        · exact noMk_pure _
      · exact noMk_pure _

/-- Every entry of the algorithm's own trace is a query that it may ask. -/
theorem entries_of_asksIn {S : OSpec} {α : Type} {P : (o : S.ι) → S.Dom o → Prop} (f : Fam S) :
    ∀ {c : OComp S α}, c.AsksIn P → ∀ o ∈ (c.withTrace.runEager f).support, ∀ e ∈ o.2, P e.1 e.2.1
  | .pure a, _, o, ho, e, he => by
      simp only [OComp.withTrace, OComp.runEager, PMF.support_pure, Set.mem_singleton_iff] at ho
      subst ho
      cases he
  | .query o q k, h, out, hout, e, he => by
      simp only [OComp.withTrace, OComp.runEager, OComp.runEager_bind, PMF.mem_support_bind_iff,
        PMF.support_pure, Set.mem_singleton_iff] at hout
      obtain ⟨z, hz, rfl⟩ := hout
      rcases List.mem_cons.1 he with rfl | he'
      · exact h.1
      · exact entries_of_asksIn f (h.2 _) z hz e he'
  | .sample n k, h, out, hout, e, he => by
      simp only [OComp.withTrace, OComp.runEager, PMF.mem_support_bind_iff] at hout
      obtain ⟨r, -, hr⟩ := hout
      exact entries_of_asksIn f (h r) out hr e he

/-- The trace of an algorithm that asks no Merkle oracle has no Merkle entry. -/
theorem filter_nil_of_noMk {α : Type} {c : TypedOracleComputation lam K L α} (h : NoMk c) (f : Fam (spec lam K L))
    {o : α × Trace (spec lam K L)} (ho : o ∈ (c.withTrace.runEager f).support) :
    o.2.filter isMk = [] :=
  List.filter_eq_nil_iff.2 fun e he => by
    have := entries_of_asksIn f h o ho e he
    simp only [isMk, this, Bool.false_eq_true, not_false_eq_true]

/-- The roots of one round of the chain occur in a trace that holds the round's queries. -/
theorem VStep.roots_occur {t : Tag} {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s}
    {tr : Trace (spec lam K L)} {cms : List (Dig lam)} {x : Option X} {salt : Bits}
    {rtreq : Dig lam} {embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)} {i : ℕ}
    {pl : r.Plain} {ph ph₁ : Phase lam} {cur : Item lam L t} {ans : FsAns lam K}
    {rt : RtC lam × RtC lam} (h : VStep tr cms x salt rtreq embP i pl ph cur ans ph₁ rt)
    (hq : fbE t cur.q ans ∈ tr) (c : Dig lam) (hc : c ∈ rt.1.join.toList ++ rt.2.join.toList) :
    (evM lam K L).OccursIn tr c := by
  cases h with
  | f1 root ans hk => exact ⟨_, hq, evM_occurs_rt _ ans (by simpa using hc)⟩
  | f2 ρ root ans hk => exact ⟨_, hq, evM_occurs_rt _ ans (by simpa using hc)⟩
  | join ρ rtj rt0 cv ans hk hg =>
    rcases List.mem_append.1 hc with h0 | hj
    · exact ⟨_, hq, evM_occurs_rt _ ans (by simpa using h0)⟩
    · exact ⟨_, hg, evM_occurs_g _ cv (by simpa using hj)⟩
  | f5 ρ0 cv root ans hk => exact ⟨_, hq, evM_occurs_rt _ ans (by simpa using hc)⟩
  | f3 ρ0 cv root ans hk => exact ⟨_, hq, evM_occurs_rt _ ans (by simpa using hc)⟩
  | f2' ρ cv root ans hk => exact ⟨_, hq, evM_occurs_rt _ ans (by simpa using hc)⟩

/-- Every root that the chain deals out to a round occurs in a trace that holds the chain's queries.
-/
theorem roots_occur_chainB {tr : Trace (spec lam K L)} {t : Tag} {cms : List (Dig lam)}
    {x : Option X} {salt : Bits} {rtreq : Dig lam} :
    ∀ (s : Shape) (A : RoundSplits s) (ws : RoundsQueryLayout lam K s A)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph ph' : Phase lam)
        (rts : List (Dig lam)) (pls : Plains s) (ρ : Rho s) (RTs : RootsOfChain lam s),
      RunsIn tr (recomputeChain (K := K) t cms x salt rtreq s A ws embP i ph rts pls) (some (ρ, RTs, ph')) →
      ∀ c ∈ RootsOfChain.list s RTs, (evM lam K L).OccursIn tr c
  | [], _, _, _, _, _, _, _, _, _, _, _, c, hc => by cases hc
  | _ :: s, (_, A), (_, ws), embP, i, ph, ph', rts, (pl, pls), (_, ρ), (rt, RTs), h, c, hc => by
      obtain ⟨cur, ans, ph₁, rts', hv, hq, -, hr⟩ := runsIn_chainB_cons h
      rcases List.mem_append.1 hc with h1 | h1
      · exact hv.roots_occur hq c h1
      · exact roots_occur_chainB s A ws _ (i + 1) ph₁ ph' rts' pls ρ RTs hr c h1

end Chain

/-! ## Part 3. Good runs, and the deterministic core -/

section Core
variable (W : QueryLayout lam L) (p : Params)

/-- What is known of the trace trV of an accepting verifier of the analysis: it begins with entries
(trH) that are no queries to the two Merkle oracles of trees over oracles (`isMk`) and at which all
roots of the slot's string that belong to a round occur; and V's three checks run to "accept" within
it, those of Test and Link on some strings (πT, πL), the slot's on `π.piB`. -/
def GoodRun (v : IVK lam L) (x : X) (π : Prf lam L) (trV : Tc W) : Prop :=
  ∃ (πT : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.offline))
      (πL : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link)) (πB : OneProtocolProof lam L.onlineBatch) (trH rest : Tc W),
    π.piB = some πB ∧ trV = trH ++ rest ∧
    trH.filter isMk = [] ∧
    (∀ c ∈ RootsOfChain.list L.onlineBatch.loc.shape (rtsB W πB), (evM lam W.K L).OccursIn trH c) ∧
    RunsIn trV (vTS W p.sMT p.sFS v.cm πT) true ∧
    RunsIn trV (vLS W p.sMT p.sFS v.cm π.cm πL) true ∧
    RunsIn trV (vBS W p.sMT p.sFS π.cm x πB) true

variable {W p}

/-- An accepting run of V is an accepting run of its three checks. -/
theorem runs_of_V {v : IVK lam L} {x : X} {π : Prf lam L}
    {tr : Tc W} (h : RunsIn tr (V W p v x π) true) :
    ∃ πT πL πB,
      π.piB = some πB ∧
      RunsIn tr (vTS W p.sMT p.sFS v.cm πT) true ∧
      RunsIn tr (vLS W p.sMT p.sFS v.cm π.cm πL) true ∧
      RunsIn tr (vBS W p.sMT p.sFS π.cm x πB) true := by
  unfold V at h
  split at h
  · rename_i πT πL πB _ _ e3
    split_ifs at h
    · simp only [bind_eq, pure_eq, runsIn_bind_iff, runsIn_pure_iff] at h
      obtain ⟨a, ha, b, hb, c, hc, habc⟩ := h
      simp only [Bool.and_eq_true] at habc
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := habc
      exact ⟨πT, πL, πB, e3, ha, hb, hc⟩
    · exact absurd (runsIn_pure_iff.1 h) (by simp)
  · exact absurd (runsIn_pure_iff.1 h) (by simp)

/-- Under the hypotheses below: outside Bad, after a good run, the index that the committer's trace
determines, the instance, and the witness that the extractor reads off the committer's trace
followed by the prover's, are in `Rno`. -/
theorem coreBK (hW : W.OKG) {Rno : I → X → Wn → Prop} {wit : X → Orcs L.onlineBatch.loc.shape → Wn}
    (w0 : Wn) {Bad : Tc W → Prop}
    (hT : ∀ tr cm π, ¬ Bad tr → RunsIn tr (vT W cm π) true → L.decodeIndex (extEnc W tr cm) ≠ none)
    (hL : ∀ tr cm cm' π, ¬ Bad tr → RunsIn tr (vL W cm cm' π) true →
      L.decodeIndex (extEnc W tr cm) = none ∨ L.decodeIndex (extEnc W tr cm') = L.decodeIndex (extEnc W tr cm))
    (hO : ∀ tr cm x π, ¬ Bad tr → RunsIn tr (vB W cm x π) true →
      L.decodeIndex (extEnc W tr cm) = none ∨
      ∃ i, L.decodeIndex (extEnc W tr cm) = some i ∧ Rno i x (wit x (readB W tr π)))
    (hE : ∀ tr tr' cm,
      ¬ Bad (tr ++ tr') → Announced W tr cm → extEnc W tr cm = extEnc W (tr ++ tr') cm)
    (hR : ∀ tr tr' π, ¬ Bad (tr ++ tr') →
      (∀ c ∈ RootsOfChain.list L.onlineBatch.loc.shape (rtsB W π), (evM lam W.K L).OccursIn tr c) →
      readB W tr π = readB W (tr ++ tr') π)
    (v : IVK lam L) (x : X) (π : Prf lam L) (trC trP trV : Tc W) (u : Unit)
    (hg : GoodRun W p v x π trV) (hnb : ¬ Bad ((trC ++ [annE W v.cm u]) ++ (trP ++ trV))) :
    ∃ i,
      L.decodeIndex (extEnc W trC v.cm) = some i ∧ Rno i x ((extractorBW W wit w0).Ew v trC x π trP) := by
  obtain ⟨πT, πL, πB, trH, rest, e3, rfl, hmk, hocc, ha, hb, hc⟩ := hg
  set tr : Tc W := (trC ++ [annE W v.cm u]) ++ (trP ++ (trH ++ rest)) with htr
  have hsub : trH ++ rest ⊆ tr := fun e he => List.mem_append_right _ (List.mem_append_right _ he)
  have hann : Announced W (trC ++ [annE W v.cm u]) v.cm := by
    cases u
    exact List.mem_append_right _ (List.mem_singleton.2 rfl)
  have hext : extEnc W trC v.cm = extEnc W tr v.cm := by
    rw [← extEnc_ann trC v.cm u v.cm]
    exact hE _ _ v.cm hnb hann
  obtain ⟨_, _, ha'⟩ := runsIn_verifyB_of_strict hW.T (ha.mono hsub)
  obtain ⟨_, _, hb'⟩ := runsIn_verifyB_of_strict hW.Lk (hb.mono hsub)
  obtain ⟨P1, P2, hc'⟩ := runsIn_verifyB_of_strict hW.B (hc.mono hsub)
  -- the equation: the extractor's two traces give what the whole trace gives
  have hpre : ((trC ++ [annE W v.cm u]) ++ (trP ++ trH)) ++ rest = tr := by
    simp only [htr, List.append_assoc]
  have hread : readB W tr (πB.withPaths P1 P2) = readB W (trC ++ trP) πB :=
    calc readB W tr (πB.withPaths P1 P2) = readB W tr πB := rfl
      _ = readB W ((trC ++ [annE W v.cm u]) ++ (trP ++ trH)) πB := by
          rw [← hpre]
          exact (hR _ rest πB (by rw [hpre]; exact hnb) fun c hc =>
            (hocc c hc).mono fun e he => List.mem_append_right _ (List.mem_append_right _ he)).symm
      _ = readB W (trC ++ trP) πB := readB_of_filter W (by
          have hann0 : [annE W v.cm u].filter isMk = [] := rfl
          simp only [List.filter_append, hmk, hann0, List.append_nil]) πB
  have hw : (extractorBW W wit w0).Ew v trC x π trP = wit x (readB W (trC ++ trP) πB) := by
    simp only [extractorBW, e3]
  rw [hext, hw, ← hread]
  exact pathLemmaB (Rno := fun i x => Rno i x (wit x (readB W tr (πB.withPaths P1 P2))))
    (hT tr v.cm _ hnb ha') (hL tr v.cm π.cm _ hnb hb') (hO tr π.cm x _ hnb hc')

end Core

/-! ## Part 4. Index binding from a verifier of the analysis -/

/-- The cheating committer, the announcement of the root in ivk, the cheating prover and a verifier
of the analysis, as one algorithm. -/
def joinedV (W : QueryLayout lam L) (V' : IVK lam L → X → Prf lam L → TypedOracleComputation lam W.K L Bool) {St : Type}
    (Ct : TypedOracleComputation lam W.K L (IVK lam L × St)) (Pt : St → TypedOracleComputation lam W.K L (X × Prf lam L)) :
    TypedOracleComputation lam W.K L Unit :=
  Ct.bind fun a => (OComp.ask (S := spec lam W.K L) OracleName.ann a.1.cm).bind fun _ =>
    (Pt a.2).bind fun xp => (V' a.1 xp.1 xp.2).bind fun _ => OComp.pure ()

theorem joinedV_queryBound (W : QueryLayout lam L) {V' : IVK lam L → X → Prf lam L → TypedOracleComputation lam W.K L Bool}
    {t' : ℕ} (hdet : ∀ v x π, DetBound (V' v x π) t') {St : Type}
    {Ct : TypedOracleComputation lam W.K L (IVK lam L × St)} {Pt : St → TypedOracleComputation lam W.K L (X × Prf lam L)} {tC tP : ℕ}
    (hC : Ct.QueryBound tC) (hP : ∀ st, (Pt st).QueryBound tP) :
    (joinedV W V' Ct Pt).QueryBound (tC + tP + t' + 1) := by
  have h : (joinedV W V' Ct Pt).QueryBound (tC + (1 + (tP + (t' + 0)))) := by
    unfold joinedV
    exact hC.bind fun a =>
        (detBound_ask (S := spec lam W.K L) OracleName.ann a.1.cm).queryBound.bind fun _ =>
      (hP a.2).bind fun xp => (hdet a.1 xp.1 xp.2).queryBound.bind fun _ => trivial
  exact h.mono (by omega)

/-- Index binding with the named witness extractor, from `hsub`, `hB`, `hW` and a verifier V' of the
analysis that, for every fixed oracle, decides as V does, that flips no coin and asks at most t'
queries, and whose accepting runs are good. The theorem is about the scheme's own V; the bound
counts the queries of V'. -/
theorem bindingOfRun (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (Ryes Rno : I → X → Wn → Prop)
    (wit : X → Orcs L.onlineBatch.loc.shape → Wn) (w0 : Wn) (N : LH.Nums)
    (hsub : ∀ i x w, Ryes i x w → Rno i x w) (hB : BcsAtK W Rno wit N.εs) (hW : W.OKG)
    (V' : IVK lam L → X → Prf lam L → TypedOracleComputation lam W.K L Bool) (t' : ℕ)
    (hsame : ∀ f v x π, (V' v x π).runEager f = (V W p v x π).runEager f)
    (hdet : ∀ v x π, DetBound (V' v x π) t')
    (hgood : ∀ f v x π,
      ∀ o ∈ ((V' v x π).withTrace.runEager f).support, o.1 = true → GoodRun W p v x π o.2) :
    ZKCP.Gen.HasIndexBindingWith (ZKCP.Gen.relPairW Ryes Rno hsub)
      (ZKCP.Gen.withW Wn (argB W WP p)) (extractorBW W wit w0) (fun tC tP =>
        ((tC + tP + t' + 1 : ℕ) : ℝ≥0∞) * N.εs +
            2 * ((tC + tP + t' + 2 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam) := by
  intro tC tP St Ct Pt hC hP
  obtain ⟨Bad, hrare, -, hT, hL, hO, hE, hR⟩ := hB
  have hpt : ∀ f : Fam (spec lam W.K L),
      PrCoins f (ZKCP.Gen.bindingExp (ZKCP.Gen.withW Wn (argB W WP p)) (extractorBW W wit w0) Ct Pt)
          (ZKCP.Gen.bindingBad (ZKCP.Gen.relPairW Ryes Rno hsub)) ≤
        PrCoins f (joinedV W V' Ct Pt).withTrace {o | Bad o.2} := by
    intro f
    unfold PrCoins
    simp only [ZKCP.Gen.bindingExp, bind_eq, pure_eq, joinedV, withTrace_bind, OComp.bind_assoc,
      OComp.ask, OComp.withTrace, OComp.bind, OComp.runEager_bind, OComp.runEager]
    refine pr_bind_le_bind _ _ _ _ _ fun a _ => pr_bind_le_bind _ _ _ _ _ fun b _ => ?_
    have e1 : ((ZKCP.Gen.withW Wn (argB W WP p)).V a.1.1 b.1.1 b.1.2).runEager f =
        ((V' a.1.1 b.1.1 b.1.2).withTrace.runEager f).map Prod.fst :=
      ((runEager_withTrace_fst f _).trans (hsame f _ _ _)).symm
    rw [e1, PMF.bind_map]
    refine pr_bind_le_bind _ _ _ _ _ fun c hc => pr_pure_le_pure ?_
    rintro ⟨hacc, hbad⟩
    by_contra hnb
    have hnb' : ¬ Bad ((a.2 ++ [annE W a.1.1.cm (f OracleName.ann a.1.1.cm)]) ++ (b.2 ++ c.2)) := by
      simpa [annE] using hnb
    obtain ⟨i, hi, hr⟩ :=
      coreBK hW w0 hT hL hO hE hR a.1.1 b.1.1 b.1.2 a.2 b.2 c.2 _ (hgood f _ _ _ c hc hacc) hnb'
    have hi' : (extractorBW W wit w0).Ei a.1.1 a.2 = some i := hi
    simp only [hi'] at hbad
    rcases hbad with hb | hb
    · exact hb ⟨_, hr⟩
    · exact hb hr
  calc
    Rom.Pr (ZKCP.Gen.bindingExp (ZKCP.Gen.withW Wn (argB W WP p)) (extractorBW W wit w0) Ct Pt)
          (fun _ => ZKCP.Gen.bindingBad (ZKCP.Gen.relPairW Ryes Rno hsub)) ≤
        Rom.Pr (joinedV W V' Ct Pt).withTrace (fun _ => {o | Bad o.2}) :=
      MeasureTheory.lintegral_mono hpt
    _ = pr (joinedV W V' Ct Pt).withTrace.law {o | Bad o.2} := Pr_eq_law _ _
    _ ≤ ((tC + tP + t' + 1 : ℕ) : ℝ≥0∞) * N.εs +
          2 * ((tC + tP + t' + 1 + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam :=
        hrare Unit (joinedV W V' Ct Pt) _ (joinedV_queryBound W hdet hC hP)

/-! ## Part 5. A first proof: the roots are announced -/

section Announce
variable {K : ℕ}

/-- Announce every digest of a list: queries to the oracle whose answers are empty. -/
def annAll : List (Dig lam) → TypedOracleComputation lam K L Unit
  | [] => .pure ()
  | c :: l => .query (S := spec lam K L) OracleName.ann c fun _ => annAll l

theorem detBound_annAll : ∀ l : List (Dig lam), DetBound (annAll (K := K) (L := L) l) l.length
  | [] => trivial
  | _ :: l => fun _ => detBound_annAll l

theorem noMk_annAll : ∀ l : List (Dig lam), NoMk (annAll (K := K) (L := L) l)
  | [] => trivial
  | _ :: l => ⟨rfl, fun _ => noMk_annAll l⟩

theorem runEager_annAll (f : Fam (spec lam K L)) :
    ∀ l : List (Dig lam), (annAll (K := K) (L := L) l).runEager f = PMF.pure ()
  | [] => rfl
  | _ :: l => runEager_annAll f l

theorem occurs_of_annAll {tr : Trace (spec lam K L)} :
    ∀ l : List (Dig lam),
      RunsIn tr (annAll (K := K) (L := L) l) () → ∀ c ∈ l, (evM lam K L).OccursIn tr c
  | [], _, c, hc => by cases hc
  | d :: l, h, c, hc => by
      obtain ⟨r, hm, hr⟩ := runsIn_query_iff.1 h
      rcases List.mem_cons.1 hc with rfl | hc'
      · exact ⟨_, hm, List.mem_singleton.2 rfl⟩
      · exact occurs_of_annAll l hr c hc'

theorem RootsOfChain.list_length_le : ∀ (s : Shape) (r : RootsOfChain lam s), (RootsOfChain.list s r).length ≤ 2 * s.length
  | [], _ => Nat.zero_le _
  | _ :: s, (rt, rts) => by
      have ih := RootsOfChain.list_length_le s rts
      have h1 : rt.1.join.toList.length ≤ 1 := by cases rt.1.join <;> simp
      have h2 : rt.2.join.toList.length ≤ 1 := by cases rt.2.join <;> simp
      simp only [RootsOfChain.list, List.length_append, List.length_cons]
      omega

end Announce

/-- A pair in the support of the traced run of a sequence comes from a pair of each part. -/
theorem mem_support_withTrace_bind {S : OSpec} {α β : Type} (f : Fam S) (c : OComp S α)
    (g : α → OComp S β) {o : β × Trace S} (ho : o ∈ ((c.bind g).withTrace.runEager f).support) :
    ∃ a ∈ (c.withTrace.runEager f).support,
      ∃ b ∈ ((g a.1).withTrace.runEager f).support, o = (b.1, a.2 ++ b.2) := by
  simp only [withTrace_bind, OComp.runEager_bind, OComp.runEager, PMF.mem_support_bind_iff,
    PMF.support_pure, Set.mem_singleton_iff] at ho
  obtain ⟨a, ha, b, hb, rfl⟩ := ho
  exact ⟨a, ha, b, hb, rfl⟩

section WayA
variable (W : QueryLayout lam L) (p : Params)

/-- The roots of the slot's string that belong to a round. -/
def rootsOf (π : Prf lam L) : List (Dig lam) :=
  match π.piB with
  | some πB => RootsOfChain.list L.onlineBatch.loc.shape (rtsB W πB)
  | none => []

/-- The verifier of the analysis of the first proof: announce these roots, then run V. -/
def VA (v : IVK lam L) (x : X) (π : Prf lam L) : TypedOracleComputation lam W.K L Bool :=
  (annAll (rootsOf W π)).bind fun _ => V W p v x π

theorem VA_same (f : Fam (spec lam W.K L)) (v : IVK lam L) (x : X) (π : Prf lam L) :
    (VA W p v x π).runEager f = (V W p v x π).runEager f := by
  unfold VA
  rw [OComp.runEager_bind, runEager_annAll, PMF.pure_bind]

theorem detBound_VA (v : IVK lam L) (x : X) (π : Prf lam L) :
    DetBound (VA W p v x π) (2 * L.onlineBatch.loc.shape.length + tVB W) := by
  refine ((detBound_annAll (rootsOf W π)).mono ?_).bind fun _ => detBound_V W p v x π
  unfold rootsOf
  split
  · exact RootsOfChain.list_length_le _ _
  · exact Nat.zero_le _

theorem VA_good (f : Fam (spec lam W.K L)) (v : IVK lam L) (x : X) (π : Prf lam L) :
    ∀ o ∈ ((VA W p v x π).withTrace.runEager f).support, o.1 = true → GoodRun W p v x π o.2 := by
  intro o ho hacc
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_support_withTrace_bind f _ _ ho
  have hrun : RunsIn b.2 (V W p v x π) true := by
    have := runsIn_of_mem_support (detBound_V W p v x π) f b hb
    have hb1 : b.1 = true := hacc
    rwa [hb1] at this
  obtain ⟨πT, πL, πB, e3, h1, h2, h3⟩ := runs_of_V hrun
  have hsub : b.2 ⊆ a.2 ++ b.2 := fun e he => List.mem_append_right _ he
  refine ⟨πT, πL, πB, a.2, b.2, e3, rfl, filter_nil_of_noMk (noMk_annAll _) f ha, ?_, h1.mono hsub,
    h2.mono hsub, h3.mono hsub⟩
  have hr := runsIn_of_mem_support (detBound_annAll (rootsOf W π)) f a ha
  have hl : rootsOf W π = RootsOfChain.list L.onlineBatch.loc.shape (rtsB W πB) := by simp only [rootsOf, e3]
  rw [hl] at hr
  exact occurs_of_annAll _ hr

end WayA

/-- Index binding with the named witness extractor, first proof, from `hsub`, `hB` and `hW`: the
bound of the theorem on languages with 2 · (rounds of Batch) more queries on the prover's account.
-/
theorem bindingBatchKA (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (Ryes Rno : I → X → Wn → Prop)
    (wit : X → Orcs L.onlineBatch.loc.shape → Wn) (w0 : Wn) (N : LH.Nums)
    (hsub : ∀ i x w, Ryes i x w → Rno i x w) (hB : BcsAtK W Rno wit N.εs) (hW : W.OKG) :
    ZKCP.Gen.HasIndexBindingWith (ZKCP.Gen.relPairW Ryes Rno hsub) (ZKCP.Gen.withW Wn (argB W WP p))
      (extractorBW W wit w0) (fun tC tP => epsB W N tC (tP + 2 * L.onlineBatch.loc.shape.length)) := by
  intro tC tP St Ct Pt hC hP
  refine (bindingOfRun W WP p Ryes Rno wit w0 N hsub hB hW (VA W p) _ (VA_same W p)
      (detBound_VA W p) (VA_good W p) tC tP St Ct Pt hC hP).trans (le_of_eq ?_)
  unfold epsB
  dsimp only
  rw [show tC + tP + (2 * L.onlineBatch.loc.shape.length + tVB W) + 1 =
        tC + (tP + 2 * L.onlineBatch.loc.shape.length) + tVB W + 1 by omega,
    show tC + tP + (2 * L.onlineBatch.loc.shape.length + tVB W) + 2 =
      tC + (tP + 2 * L.onlineBatch.loc.shape.length) + tVB W + 2 by omega]

/-! ## Part 6. The exact bound: the slot's check first -/

section WayC
variable (W : QueryLayout lam L) (p : Params)

/-- What the strict verifier of a slot of Batch does after its chain. -/
def tailBS (cm : Dig lam) (x : X) (π : OneProtocolProof lam L.onlineBatch)
    (r : Option (Rho L.onlineBatch.loc.shape × RootsOfChain lam L.onlineBatch.loc.shape × Phase lam)) : TypedOracleComputation lam W.K L Bool :=
  match r with
  | none => pure false
  | some (ρ, rts, ph) =>
      if proofHasStrictFormat p.sMT p.sFS L.onlineBatch W.B W.depthReq x π ρ rts ph then
        checkPrunedOpenings L.onlineBatch W.B (fun p a => some (.inr ⟨Tag.onl, ⟨p, a⟩⟩)) (fun s => some (.inl s))
          W.depthReq [cm] x π ρ rts ph
      else pure false

/-- The chain of the slot's string. -/
abbrev chainBS (cm : Dig lam) (x : X) (π : OneProtocolProof lam L.onlineBatch) :
    TypedOracleComputation lam W.K L (Option (Rho L.onlineBatch.loc.shape × RootsOfChain lam L.onlineBatch.loc.shape × Phase lam)) :=
  recomputeChainOfProof Tag.onl L.onlineBatch W.B id some [cm] x π

theorem vBS_eq (cm : Dig lam) (x : X) (π : OneProtocolProof lam L.onlineBatch) :
    vBS W p.sMT p.sFS cm x π = (chainBS W cm x π).bind (tailBS W p cm x π) := by
  unfold vBS verifyOneProtocol
  refine congrArg _ (funext fun r => ?_)
  rcases r with _ | ⟨ρ, rts, ph⟩ <;> rfl

theorem detBound_tailBS (cm : Dig lam) (x : X) (π : OneProtocolProof lam L.onlineBatch)
    (r : Option (Rho L.onlineBatch.loc.shape × RootsOfChain lam L.onlineBatch.loc.shape × Phase lam)) :
    DetBound (tailBS W p cm x π r) (W.B.nOpen * (W.B.maxDepth + 1) + (W.depthReq + 1)) := by
  rcases r with _ | ⟨ρ, rts, ph⟩
  · exact detBound_pure _ _
  · unfold tailBS
    dsimp only
    split_ifs
    · exact detBound_afterBO _ _ _ _ _ _ _ _ _ _ _
    · exact detBound_pure _ _

/-- After the chain: the rest of the slot's check, then the checks of the test and of the link
(`vTS`, `vLS`). -/
def restC (v : IVK lam L) (x : X) (π : Prf lam L) (πT : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.offline))
    (πL : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link)) (πB : OneProtocolProof lam L.onlineBatch)
    (r : Option (Rho L.onlineBatch.loc.shape × RootsOfChain lam L.onlineBatch.loc.shape × Phase lam)) : TypedOracleComputation lam W.K L Bool :=
  (tailBS W p π.cm x πB r).bind fun c =>
    (vTS W p.sMT p.sFS v.cm πT).bind fun a =>
      (vLS W p.sMT p.sFS v.cm π.cm πL).bind fun b => .pure (a && b && c)

/-- The verifier of the analysis of the second proof: V with the check of the slot's string before
the checks of the test and of the link (`vTS`, `vLS`). So its first queries are those of the slot's
chain. -/
def VC (v : IVK lam L) (x : X) (π : Prf lam L) : TypedOracleComputation lam W.K L Bool :=
  match v.piT, π.piL, π.piB with
  | some πT, some πL, some πB =>
    if π.leaf ≤ p.M then (chainBS W π.cm x πB).bind (restC W p v x π πT πL πB) else .pure false
  | _, _, _ => .pure false

theorem chain_restC (v : IVK lam L) (x : X) (π : Prf lam L)
    (πT : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.offline))
    (πL : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link)) (πB : OneProtocolProof lam L.onlineBatch) :
    (chainBS W π.cm x πB).bind (restC W p v x π πT πL πB) =
      (vBS W p.sMT p.sFS π.cm x πB).bind fun c =>
        (vTS W p.sMT p.sFS v.cm πT).bind fun a =>
            (vLS W p.sMT p.sFS v.cm π.cm πL).bind fun b => .pure (a && b && c) := by
  rw [vBS_eq, OComp.bind_assoc]
  rfl

/-- Three independent draws, the last one first. -/
theorem pmf_rot {α β γ δ : Type} (T : PMF α) (Lk : PMF β) (B : PMF γ) (G : α → β → γ → PMF δ) :
    (T.bind fun a => Lk.bind fun b => B.bind fun c => G a b c) =
      B.bind fun c => T.bind fun a => Lk.bind fun b => G a b c := by
  have h1 : ∀ a,
      (Lk.bind fun b => B.bind fun c => G a b c) = B.bind fun c => Lk.bind fun b => G a b c :=
    fun a => PMF.bind_comm Lk B (G a)
  simp only [h1]
  exact PMF.bind_comm T B fun a c => Lk.bind fun b => G a b c

/-- For every fixed oracle the verifier of the analysis decides as V does. -/
theorem VC_same (f : Fam (spec lam W.K L)) (v : IVK lam L) (x : X) (π : Prf lam L) :
    (VC W p v x π).runEager f = (V W p v x π).runEager f := by
  unfold VC V
  rcases v.piT with _ | πT
  · rfl
  rcases π.piL with _ | πL
  · rfl
  rcases π.piB with _ | πB
  · rfl
  dsimp only
  split_ifs
  · rw [chain_restC]
    simp only [bind_eq, pure_eq, OComp.runEager_bind]
    exact (pmf_rot _ _ _ _).symm
  · rfl

theorem detBound_VC (v : IVK lam L) (x : X) (π : Prf lam L) : DetBound (VC W p v x π) (tVB W) := by
  unfold VC tVB
  split
  · split_ifs
    · rw [chain_restC]
      refine ((detBound_vBS W _ _ _ _ _).bind
        (t := tVQB W.T W.depthReq + (tVQB W.Lk W.depthReq + 0)) fun c =>
          (detBound_vTS W _ _ _ _).bind (t := tVQB W.Lk W.depthReq + 0) fun a =>
            (detBound_vLS W _ _ _ _ _).bind (t := 0) fun b => detBound_pure _ _).mono ?_
      omega
    · exact detBound_pure _ _
  · exact detBound_pure _ _

theorem detBound_restC (v : IVK lam L) (x : X) (π : Prf lam L)
    (πT : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.offline)) (πL : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link))
    (πB : OneProtocolProof lam L.onlineBatch) (r : Option (Rho L.onlineBatch.loc.shape × RootsOfChain lam L.onlineBatch.loc.shape × Phase lam)) :
    DetBound (restC W p v x π πT πL πB r)
      ((W.B.nOpen * (W.B.maxDepth + 1) + (W.depthReq + 1)) +
        (tVQB W.T W.depthReq + (tVQB W.Lk W.depthReq + 0))) :=
  (detBound_tailBS W p _ _ _ _).bind fun _ =>
    (detBound_vTS W _ _ _ _).bind fun _ =>
      (detBound_vLS W _ _ _ _ _).bind (t := 0) fun _ => detBound_pure _ _

/-- The accepting runs of the verifier of the analysis are good: its trace begins with the exact
trace of the slot's chain, which holds no Merkle query and at which all roots of the slot's string
that belong to a round occur. -/
theorem VC_good (f : Fam (spec lam W.K L)) (v : IVK lam L) (x : X) (π : Prf lam L) :
    ∀ o ∈ ((VC W p v x π).withTrace.runEager f).support, o.1 = true → GoodRun W p v x π o.2 := by
  intro o ho hacc
  have hfalse : ∀ o : Bool × Tc W, o ∈
        ((OComp.pure false : TypedOracleComputation lam W.K L Bool).withTrace.runEager f).support →
      o.1 = true → False := by
    intro o ho hacc
    simp only [OComp.withTrace, OComp.runEager, PMF.support_pure, Set.mem_singleton_iff] at ho
    subst ho
    cases hacc
  unfold VC at ho
  split at ho
  · rename_i πT πL πB _ _ e3
    split_ifs at ho
    · obtain ⟨a, ha, b, hb, rfl⟩ := mem_support_withTrace_bind f _ _ ho
      have hch : RunsIn a.2 (chainBS W π.cm x πB) a.1 :=
        runsIn_of_mem_support (detBound_chainB Tag.onl [π.cm] (some x) πB.salt πB.rtreq
            L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh id 0 .first πB.roots πB.plains)
          f a ha
      have hrest : RunsIn b.2 (restC W p v x π πT πL πB a.1) true := by
        have := runsIn_of_mem_support (detBound_restC W p v x π πT πL πB a.1) f b hb
        have hb1 : b.1 = true := hacc
        rwa [hb1] at this
      unfold restC at hrest
      simp only [runsIn_bind_iff, runsIn_pure_iff] at hrest
      obtain ⟨c, hc, a', ha', b', hb', habc⟩ := hrest
      simp only [Bool.and_eq_true] at habc
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := habc
      have hsubA : a.2 ⊆ a.2 ++ b.2 := fun e he => List.mem_append_left _ he
      have hsubB : b.2 ⊆ a.2 ++ b.2 := fun e he => List.mem_append_right _ he
      refine ⟨πT, πL, πB, a.2, b.2, e3, rfl,
        filter_nil_of_noMk (noMk_chainB _ _ _ _ _ _ _ _ _ _ _ _ _) f ha, ?_,
        ha'.mono hsubB, hb'.mono hsubB, ?_⟩
      · rcases hr : a.1 with _ | ⟨ρ, rts, ph⟩
        · rw [hr] at hc
          exact absurd (runsIn_pure_iff.1 hc) (by simp)
        · rw [hr] at hch
          rw [rtsB_of_chainQB hch]
          exact roots_occur_chainB _ _ _ _ _ _ _ _ _ _ _ hch
      · rw [vBS_eq]
        exact (runsIn_bind_iff _ _ _).2 ⟨a.1, hch.mono hsubA, hc.mono hsubB⟩
    · exact (hfalse o ho hacc).elim
  · exact (hfalse o ho hacc).elim

end WayC

/-- Index binding with the named witness extractor, with exactly the bound of the theorem on
languages, from `hsub`, the event Bad of one wire (`hB`) and `hW`. -/
theorem bindingBatchKAt (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
    (Ryes Rno : I → X → Wn → Prop) (wit : X → Orcs L.onlineBatch.loc.shape → Wn) (w0 : Wn) (N : LH.Nums)
    (hsub : ∀ i x w, Ryes i x w → Rno i x w) (hB : BcsAtK W Rno wit N.εs) (hW : W.OKG) :
    ZKCP.Gen.HasIndexBindingWith (ZKCP.Gen.relPairW Ryes Rno hsub) (ZKCP.Gen.withW Wn (argB W WP p))
      (extractorBW W wit w0) (epsB W N) :=
  bindingOfRun W WP p Ryes Rno wit w0 N hsub hB hW (VC W p) (tVB W) (VC_same W p)
    (detBound_VC W p) (VC_good W p)

/-- The statement: `Ryes` ⊆ `Rno`, round-by-round knowledge soundness of the interface, locality, a
coherent annotation and a wire with `W.OKG` give index binding of the compiled argument with the
named extractors and the bound `epsB`. -/
def Spec.bindingBatchK : Prop :=
  ∀ (I X Wn : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
      (Ryes Rno : I → X → Wn → Prop) (wit : X → Orcs L.onlineBatch.loc.shape → Wn) (w0 : Wn) (N : LH.Nums)
      (hsub : ∀ i x w, Ryes i x w → Rno i x w),
    L.SoundK Rno wit N.εs → L.offline.IsLocal → L.link.IsLocal → L.onlineBatch.loc.IsLocal →
    L.onlineBatch.ann.Coherent → W.OKG →
    ZKCP.Gen.HasIndexBindingWith (ZKCP.Gen.relPairW Ryes Rno hsub) (ZKCP.Gen.withW Wn (argB W WP p))
      (extractorBW W wit w0) (epsB W N)

theorem bindingBatchK : Spec.bindingBatchK :=
  fun I X Wn lam L W WP p Ryes Rno wit w0 N hsub hs hlT hlL hlB hcoh hW =>
    bindingBatchKAt W WP p Ryes Rno wit w0 N hsub
      (bcsSoundBatchK I X Wn lam L W Rno wit N.εs hs hlT hlL hlB hcoh hW) hW

end Compile.Batch
