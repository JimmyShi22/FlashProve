-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/CutPriv.lean: the splitting step (an answer split between two oracles: `OCut`, `cutSpec`,
Rom/SpecCut.lean): index privacy carries over from a family of oracles to the split family, with the
same bound and the simulator `simCut C Sim`, under `NeedOKCut`: committer, prover and verifier each
meet the condition `ReadsCut` (Rom/SpecCut.lean) under their rule (`privacy_cut`). A rule
(`NeedCut`, Rom/SpecCut.lean) says, after the first part of an answer, whether the second part is
queried. Structure as in Rom/ExitPriv.lean, whose logs, challengers and loop (`Log`, `GWorld`,
`lLoop`, `simWorld`, `eagerWorld`, `lLoop_shift`) are generic and are used as they are.

An adversarial verifier V over the split family becomes `downVCut C V` over the family S: a query
for a part becomes one query for the whole answer. (Here the trivial second oracle of an oracle that
is not split is queried like any other: `simCut` passes every query to Sim, and no extractor reads
this trace.) The view over S does not say which part V asked for; the view over the split family is
recovered from it by replaying V on it (`replayCut`).

By `simWorld_simCut` and `eagerWorld_cutFam` (under `NeedOKCut`, at a family `cutFam C F`) the two
challengers of the scheme after the step are of the form `partWorld C Wd`.

Notation:
  `nC`, `nP`, `nV`: `NeedCut C` (Rom/SpecCut.lean): a rule for each algorithm (doc comment of
    `cutArg`)
  `B`: `ℕ`: the bound on the length of a batch (doc comment of `Gen.Arg`, ZKCP/Gen.lean)
  `ζ`: `ℕ → ℕ → ℝ≥0∞`: in `Gen.PrivacyFor R A Sim ζ i Z` (ZKCP/Gen.lean) it stands as `ζ tV N`, with
    `∀ ivk, (Vt ivk).QueryBound tV`; N counts batches
  `Z`: `Gen.ViewEnv (cutSpec S C) IVK X W Pf` (ZKCP/Gen.lean): the environment; `Vt`:
    `IVK → Gen.AdvVerifier (cutSpec S C) X Pf`; in `loop_replayCut`: `Z`:
    `Log (cutSpec S C) X Pf → Option (Gen.Batch X W)`
  `Log S X Pf` (Rom/ExitPriv.lean): what a view holds beside ivk: the fields `sessions`, `trace`,
    `coins`; `Log.oneS x`, `Log.oneT e`, `Log.oneC c`: `⟨[x], [], []⟩`, `⟨[], [e], []⟩`,
    `⟨[], [], [c]⟩`
  `Wd`: `GWorld S X W Pf` (Rom/ExitPriv.lean): the challenger of an adversarial verifier: it answers
    oracle queries and serves batches (the fields `σ`, `answer`, `serve`)
  `n` in `lLoop Wd Z V n l s` and `replayCut C V n l`: `ℕ`: the number of batches still allowed (doc
    comment of `Gen.realLoop`, ZKCP/Gen.lean)

Limits: what the head of Rom/SpecCut.lean lists as not said is not said here either.
-/
import Rom.CutBind
import Rom.ExitPriv

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Rom
open ZKCP

variable {S : OSpec} (C : ∀ o, OCut (S.Rng o)) {I X W PP IVK ISK Pf : Type}

/-- the oracle of S behind an oracle of the split family -/
def baseOf : (cutSpec S C).ι → S.ι
  | .inl o => o
  | .inr o => o
/-- the query, as one to `baseOf` -/
def pointOf : (x : (cutSpec S C).ι) → (cutSpec S C).Dom x → S.Dom (baseOf C x)
  | .inl _, q => q
  | .inr _, q => q
/-- the part of an answer that the oracle x of the split family returns -/
def partOf : (x : (cutSpec S C).ι) → S.Rng (baseOf C x) → (cutSpec S C).Rng x
  | .inl o, r => (C o).front r
  | .inr o, r => (C o).rest r

theorem cutFam_eq (F : Fam S) :
    ∀ (x : (cutSpec S C).ι) (q : (cutSpec S C).Dom x),
      cutFam C F x q = partOf C x (F (baseOf C x) (pointOf C x q))
  | .inl _, _ => rfl
  | .inr _, _ => rfl

/-- A challenger over the family, seen through the parts: a query for a part is answered with that
part of the challenger's answer. -/
def partWorld (Wd : GWorld S X W Pf) : GWorld (cutSpec S C) X W Pf where
  σ := Wd.σ
  answer s x q :=
    (Wd.answer s (baseOf C x) (pointOf C x q)).map fun out => (partOf C x out.1, out.2)
  serve := Wd.serve

/-- The adversarial verifier over the family: a query for a part becomes one query for the whole
answer. -/
def downVCut : Gen.AdvVerifier (cutSpec S C) X Pf → Gen.AdvVerifier S X Pf
  | .halt => .halt
  | .sample n k => .sample n fun r => downVCut (k r)
  | .query x q k => .query (baseOf C x) (pointOf C x q) fun r => downVCut (k (partOf C x r))
  | .request k => .request fun l => downVCut (k l)

theorem queryBound_downVCut (V : Gen.AdvVerifier (cutSpec S C) X Pf) :
    ∀ t, V.QueryBound t → (downVCut C V).QueryBound t := by
  induction V with
  | halt => intro t _; trivial
  | sample n k ih => exact fun t h r => ih r t (h r)
  | query x q k ih =>
    intro t h
    cases t with
    | zero => exact h
    | succ t => exact fun r => ih _ t (h _)
  | request k ih => exact fun t h l => ih l t (h l)

open Classical in
/-- Replay V on a log over the family: the log over the split family that V has seen. It stops where
the log ends or does not fit V's next move. -/
def replayCut : Gen.AdvVerifier (cutSpec S C) X Pf → ℕ → Log S X Pf → Log (cutSpec S C) X Pf
  | .halt, _, _ => Log.nil
  | .sample mm k, n, l =>
      match l.coins with
      | [] => Log.nil
      | c :: cs =>
        if hc : c < mm + 1 then (Log.oneC c).app (replayCut (k ⟨c, hc⟩) n { l with coins := cs })
        else Log.nil
  | .query x q k, n, l =>
      match l.trace with
      | [] => Log.nil
      | e :: tr =>
        if he : (⟨e.1, e.2.1⟩ : Σ o, S.Dom o) = ⟨baseOf C x, pointOf C x q⟩ then
          (Log.oneT
              ⟨x, q, partOf C x ((show e.1 = baseOf C x from congrArg Sigma.fst he) ▸ e.2.2)⟩).app
            (replayCut (k (partOf C x ((show e.1 = baseOf C x from congrArg Sigma.fst he) ▸ e.2.2)))
              n { l with trace := tr })
        else Log.nil
  | .request _, 0, _ => Log.nil
  | .request k, n + 1, l =>
      match l.sessions with
      | [] => Log.nil
      | y :: ys => (Log.oneS y).app (replayCut (k y) n { l with sessions := ys })

theorem replayCut_sample (mm : ℕ) (k : Fin (mm + 1) → Gen.AdvVerifier (cutSpec S C) X Pf) (n : ℕ)
    (r : Fin (mm + 1)) (l : Log S X Pf) :
    replayCut C (.sample mm k) n ((Log.oneC r.val).app l) =
      (Log.oneC r.val).app (replayCut C (k r) n l) := by
  simp only [replayCut, Log.app, Log.oneC, List.cons_append, List.nil_append,
    r.isLt, dif_pos, Fin.eta]

theorem replayCut_query (x : (cutSpec S C).ι) (q : (cutSpec S C).Dom x)
    (k : (cutSpec S C).Rng x → Gen.AdvVerifier (cutSpec S C) X Pf) (n : ℕ)
    (r : S.Rng (baseOf C x)) (l : Log S X Pf) :
    replayCut C (.query x q k) n ((Log.oneT ⟨baseOf C x, pointOf C x q, r⟩).app l) =
      (Log.oneT ⟨x, q, partOf C x r⟩).app (replayCut C (k (partOf C x r)) n l) := by
  simp only [replayCut, Log.app, Log.oneT, List.cons_append, List.nil_append, dif_pos]

theorem replayCut_request (k : List (X × Pf) → Gen.AdvVerifier (cutSpec S C) X Pf) (n : ℕ)
    (y : List (X × Pf)) (l : Log S X Pf) :
    replayCut C (.request k) (n + 1) ((Log.oneS y).app l) =
      (Log.oneS y).app (replayCut C (k y) n l) := by
  simp only [replayCut, Log.app, Log.oneS, List.cons_append, List.nil_append]

/-- The replay lemma, for every challenger: the loop over the split family is the image, under the
replay, of the loop over the family. -/
theorem loop_replayCut (Wd : GWorld S X W Pf) (V : Gen.AdvVerifier (cutSpec S C) X Pf) :
    ∀ (Z : Log (cutSpec S C) X Pf → Option (Gen.Batch X W)) (n : ℕ) (s : Wd.σ),
      lLoop (partWorld C Wd) Z V n Log.nil s =
        (lLoop Wd (fun l => Z (replayCut C V n l)) (downVCut C V) n Log.nil s).map
          (replayCut C V n) := by
  induction V with
  | halt => intro Z n s; simp only [lLoop, downVCut, PMF.pure_map, replayCut]
  | sample mm k ih =>
    intro Z n s
    simp only [lLoop, downVCut, PMF.map_bind]
    refine congrArg _ (funext fun r => ?_)
    have e1 : ({ (Log.nil : Log (cutSpec S C) X Pf) with
                 coins := (Log.nil : Log (cutSpec S C) X Pf).coins ++ [r.val] }) =
        (Log.oneC r.val).app Log.nil := rfl
    have e2 : ({ (Log.nil : Log S X Pf) with coins := (Log.nil : Log S X Pf).coins ++ [r.val] }) =
        (Log.oneC r.val).app Log.nil := rfl
    rw [e1, e2, lLoop_shift, lLoop_shift, ih, PMF.map_comp, PMF.map_comp]
    simp only [replayCut_sample, Function.comp_def]
  | query x q k ih =>
    intro Z n st
    simp only [lLoop, downVCut, PMF.map_bind]
    show ((Wd.answer st (baseOf C x) (pointOf C x q)).map _).bind _ = _
    rw [PMF.bind_map]
    refine congrArg _ (funext fun out => ?_)
    have e1 : ({ (Log.nil : Log (cutSpec S C) X Pf) with
                 trace := (Log.nil : Log (cutSpec S C) X Pf).trace ++
                     [⟨x, q, partOf C x out.1⟩] }) =
        (Log.oneT ⟨x, q, partOf C x out.1⟩).app Log.nil := rfl
    have e2 : ({ (Log.nil : Log S X Pf) with
                 trace := (Log.nil : Log S X Pf).trace ++ [⟨baseOf C x, pointOf C x q, out.1⟩] }) =
        (Log.oneT ⟨baseOf C x, pointOf C x q, out.1⟩).app Log.nil := rfl
    simp only [Function.comp_def]
    rw [e1, e2, lLoop_shift, lLoop_shift, ih, PMF.map_comp, PMF.map_comp]
    simp only [replayCut_query, Function.comp_def]
  | request k ih =>
    intro Z n s
    cases n with
    | zero => simp only [lLoop, downVCut, PMF.pure_map, replayCut]
    | succ n =>
      have hnil : replayCut C (.request k) (n + 1) (Log.nil : Log S X Pf) = Log.nil := rfl
      cases hz : Z Log.nil with
      | none => simp only [lLoop, downVCut, hnil, hz, PMF.pure_map]
      | some b =>
        simp only [lLoop, downVCut, hnil, hz, PMF.map_bind]
        refine congrArg _ (funext fun out => ?_)
        have e1 : ({ (Log.nil : Log (cutSpec S C) X Pf) with
                     sessions := (Log.nil : Log (cutSpec S C) X Pf).sessions ++ [out.1] }) =
            (Log.oneS out.1).app Log.nil := rfl
        have e2 : ({ (Log.nil : Log S X Pf) with
                     sessions := (Log.nil : Log S X Pf).sessions ++ [out.1] }) =
            (Log.oneS out.1).app Log.nil := rfl
        rw [e1, e2, lLoop_shift, lLoop_shift, ih, PMF.map_comp, PMF.map_comp]
        simp only [replayCut_request, Function.comp_def]

/-! ### The two experiments -/

theorem simWorld_simCut (Sim : Gen.Simulator S PP IVK X Pf) :
    (simWorld (simCut C Sim) : GWorld (cutSpec S C) X W Pf) = partWorld C (simWorld Sim) := by
  have h : (simCut C Sim).answer =
      fun s x q =>
        (Sim.answer s (baseOf C x) (pointOf C x q)).map fun out => (partOf C x out.1, out.2) := by
    funext s x
    cases x <;> rfl
  show GWorld.mk Sim.St (simCut C Sim).answer _ = GWorld.mk Sim.St _ _
  rw [h]
  rfl

theorem eagerWorld_cutFam {A : Gen.Arg S I X W IVK ISK Pf} {nC nP nV : NeedCut C}
    (h : NeedOKCut C A nC nP nV) (isk : ISK) (F : Fam S) :
    eagerWorld (cutArg C nC nP nV A) isk (cutFam C F) = partWorld C (eagerWorld A isk F) := by
  have h1 : (fun (_ : Unit) (x : (cutSpec S C).ι) (q : (cutSpec S C).Dom x) =>
        PMF.pure (cutFam C F x q, ())) =
      fun _ x q =>
        (PMF.pure (F (baseOf C x) (pointOf C x q), ())).map fun out =>
            (partOf C x out.1, out.2) := by
    funext _ x q
    rw [PMF.pure_map, cutFam_eq]
  have h2 : (fun (_ : Unit) (b : Gen.Batch X W) =>
        (((A.P isk b.pairs).cut C nP).runEager (cutFam C F)).map fun πs =>
          (b.released πs.val, ())) =
      fun _ b => ((A.P isk b.pairs).runEager F).map fun πs => (b.released πs.val, ()) := by
    funext _ b
    rw [runCut S C _ nP _ (h.prv isk b.pairs) F]
  show GWorld.mk Unit
      (fun (_ : Unit) (x : (cutSpec S C).ι) (q : (cutSpec S C).Dom x) =>
        PMF.pure (cutFam C F x q, ()))
      (fun (_ : Unit) (b : Gen.Batch X W) =>
        (((A.P isk b.pairs).cut C nP).runEager (cutFam C F)).map fun πs =>
          (b.released πs.val, ())) = _
  rw [h1, h2]
  rfl

/-- The view over the split family, recovered from the view over the family. -/
def replayViewCut (Vt : IVK → Gen.AdvVerifier (cutSpec S C) X Pf)
    (N : ℕ) (v : Gen.View S IVK X Pf) :
    Gen.View (cutSpec S C) IVK X Pf :=
  (replayCut C (Vt v.ivk) N (Log.ofView v)).view v.ivk

theorem realExp_cutFam {A : Gen.Arg S I X W IVK ISK Pf} {nC nP nV : NeedCut C}
    (h : NeedOKCut C A nC nP nV) (Vt : IVK → Gen.AdvVerifier (cutSpec S C) X Pf)
    (Z : Gen.ViewEnv (cutSpec S C) IVK X W Pf) (i : I) (N : ℕ) (F : Fam S) :
    (Gen.realExp (cutArg C nC nP nV A) Vt Z i N).runEager (cutFam C F) =
      ((Gen.realExp A (fun ivk => downVCut C (Vt ivk))
          (fun v => Z (replayViewCut C Vt N v)) i N).runEager F).map
        (replayViewCut C Vt N) := by
  have e1 : Gen.realExp (cutArg C nC nP nV A) Vt Z i N = ((A.C i).cut C nC).bind fun key =>
      Gen.realLoop (cutArg C nC nP nV A)
          Z key.2 (Vt key.1) N ((Log.nil : Log (cutSpec S C) X Pf).view key.1) := rfl
  have e2 : Gen.realExp A (fun ivk => downVCut C (Vt ivk)) (fun v => Z (replayViewCut C Vt N v)) i N = (A.C i).bind fun key =>
      Gen.realLoop A (fun v => Z (replayViewCut C Vt N v)) key.2 (downVCut C (Vt key.1))
          N ((Log.nil : Log S X Pf).view key.1) := rfl
  rw [e1, e2]
  simp only [OComp.runEager_bind, runCut S C _ nC _ (h.com i) F, PMF.map_bind]
  refine congrArg _ (funext fun key => ?_)
  rw [realLoop_eq, realLoop_eq, lLoop_congr (eagerWorld_cutFam C h key.2 F), loop_replayCut,
    PMF.map_comp, PMF.map_comp]
  rfl

theorem idealExp_simCut (R : Gen.RelPair I X W PP) (Sim : Gen.Simulator S PP IVK X Pf)
    (Vt : IVK → Gen.AdvVerifier (cutSpec S C) X Pf)
    (Z : Gen.ViewEnv (cutSpec S C) IVK X W Pf) (i : I) (N : ℕ) :
    Gen.idealExp R (simCut C Sim) Vt Z i N =
      (Gen.idealExp R Sim (fun ivk => downVCut C (Vt ivk))
          (fun v => Z (replayViewCut C Vt N v)) i N).map
        (replayViewCut C Vt N) := by
  have e1 : Gen.idealExp R (simCut C Sim) Vt Z i N = (Sim.init (R.pp i) N).bind fun out =>
      Gen.idealLoop (simCut C Sim)
          Z (Vt out.1) N ((Log.nil : Log (cutSpec S C) X Pf).view out.1) out.2 := rfl
  have e2 : Gen.idealExp R Sim (fun ivk => downVCut C (Vt ivk)) (fun v => Z (replayViewCut C Vt N v)) i N = (Sim.init (R.pp i) N).bind fun out =>
      Gen.idealLoop Sim (fun v => Z (replayViewCut C Vt N v)) (downVCut C (Vt out.1)) N
          ((Log.nil : Log S X Pf).view out.1) out.2 := rfl
  rw [e1, e2, PMF.map_bind]
  refine congrArg _ (funext fun out => ?_)
  rw [idealLoop_eq, idealLoop_eq, lLoop_congr (simWorld_simCut (W := W) C Sim), loop_replayCut,
    PMF.map_comp, PMF.map_comp]
  rfl

/-! ### Consistency -/

/-- Every entry of a replayed trace is a part of an entry of the log at the same query. -/
theorem mem_replayCut_trace (V : Gen.AdvVerifier (cutSpec S C) X Pf) :
    ∀ (n : ℕ) (l : Log S X Pf) (x : (cutSpec S C).ι)
        (q : (cutSpec S C).Dom x) (b : (cutSpec S C).Rng x),
      (⟨x, q, b⟩ : QA (cutSpec S C)) ∈ (replayCut C V n l).trace →
      ∃ r : S.Rng (baseOf C x),
        (⟨baseOf C x, pointOf C x q, r⟩ : QA S) ∈ l.trace ∧ b = partOf C x r := by
  induction V with
  | halt => intro n l x q b h; simp [replayCut, Log.nil] at h
  | sample mm k ih =>
    intro n l x q b h
    simp only [replayCut] at h
    cases hc : l.coins with
    | nil => simp [hc, Log.nil] at h
    | cons c cs =>
      simp only [hc] at h
      by_cases hlt : c < mm + 1
      · simp only [hlt, dif_pos, Log.app, Log.oneC, List.nil_append] at h
        exact ih _ n { l with coins := cs } x q b h
      · simp [hlt, Log.nil] at h
  | query x' q' k ih =>
    intro n l x q b h
    simp only [replayCut] at h
    cases ht : l.trace with
    | nil => simp [ht, Log.nil] at h
    | cons e tr =>
      simp only [ht] at h
      by_cases he : (⟨e.1, e.2.1⟩ : Σ o, S.Dom o) = ⟨baseOf C x', pointOf C x' q'⟩
      · simp only [he, dif_pos, Log.app, Log.oneT, List.cons_append,
          List.nil_append, List.mem_cons] at h
        rcases h with h | h
        · obtain ⟨o, q0, r⟩ := e
          simp only at he
          obtain ⟨rfl, hq⟩ := Sigma.mk.inj_iff.1 he
          have hq' := eq_of_heq hq
          subst hq'
          obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.1 h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq hh)
          exact ⟨r, List.mem_cons_self, rfl⟩
        · obtain ⟨r, hr, hb⟩ := ih _ n _ x q b h
          exact ⟨r, List.mem_cons_of_mem _ hr, hb⟩
      · simp [he, Log.nil] at h
  | request k ih =>
    intro n l x q b h
    cases n with
    | zero => simp [replayCut, Log.nil] at h
    | succ n =>
      simp only [replayCut] at h
      cases hs : l.sessions with
      | nil => simp [hs, Log.nil] at h
      | cons y ys =>
        simp only [hs, Log.app, Log.oneS, List.nil_append] at h
        exact ih _ n { l with sessions := ys } x q b h

theorem consistent_replayCut (V : Gen.AdvVerifier (cutSpec S C) X Pf) (n : ℕ)
    (l : Log S X Pf) (h : Gen.TraceConsistent l.trace) :
    Gen.TraceConsistent (replayCut C V n l).trace := by
  intro x q b b' h1 h2
  obtain ⟨r, hr, rfl⟩ := mem_replayCut_trace C V n l x q b h1
  obtain ⟨r', hr', rfl⟩ := mem_replayCut_trace C V n l x q b' h2
  rw [h _ _ r r' hr hr']

/-! ### Under the hypotheses below, index privacy carries over -/

theorem privacy_cut (R : Gen.RelPair I X W PP) {A : Gen.Arg S I X W IVK ISK Pf}
    {nC nP nV : NeedCut C} (hN : NeedOKCut C A nC nP nV) (B : ℕ) (Sim : Gen.Simulator S PP IVK X Pf)
    (ζ : ℕ → ℕ → ℝ≥0∞) (h : Gen.HasIndexPrivacyWith R A B Sim ζ) :
    Gen.HasIndexPrivacyWith R (cutArg C nC nP nV A) B (simCut C Sim) ζ := by
  intro i Z hZ tV Vt N hb
  obtain ⟨h1, h2⟩ := h i (fun v => Z (replayViewCut C Vt N v)) (fun v b hv => hZ _ b hv) tV
    (fun ivk => downVCut C (Vt ivk)) N fun ivk => queryBound_downVCut C (Vt ivk) tV (hb ivk)
  have hreal : ∀ T, Pr (Gen.realExp (cutArg C nC nP nV A) Vt Z i N) (fun _ => T) =
      Pr (Gen.realExp A (fun ivk => downVCut C (Vt ivk)) (fun v => Z (replayViewCut C Vt N v)) i N)
        (fun _ => replayViewCut C Vt N ⁻¹' T) := by
    intro T
    unfold Pr
    rw [lintegral_cutFam C (fun g => PrCoins g (Gen.realExp (cutArg C nC nP nV A) Vt Z i N) T)]
    · simp only [PrCoins, realExp_cutFam C hN, Prob.pr_map]
    · simp only [PrCoins, realExp_cutFam C hN, Prob.pr_map]
      exact measurable_PrCoins _ _
  have hideal : ∀ T, Prob.pr (Gen.idealExp R (simCut C Sim) Vt Z i N) T =
      Prob.pr (Gen.idealExp R Sim (fun ivk => downVCut C (Vt ivk))
          (fun v => Z (replayViewCut C Vt N v)) i N)
        (replayViewCut C Vt N ⁻¹' T) := by
    intro T
    rw [idealExp_simCut, Prob.pr_map]
  constructor
  · simp only [hreal, hideal]
    exact (Prob.sd_comap_le _ _ (replayViewCut C Vt N)).trans h1
  · rw [hideal]
    refine le_antisymm (le_trans (Prob.pr_mono _ ?_) (le_of_eq h2)) (zero_le _)
    intro v hv hc
    exact hv (consistent_replayCut C (Vt v.ivk) N (Log.ofView v) hc)

end Rom
