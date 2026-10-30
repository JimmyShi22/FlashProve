-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/ExitPriv.lean: the step to one hash function (by domain separation: Rom/Family.lean), part 3:
index privacy (ZKCP/Gen.lean) carries over from the family of oracles to the hash function
(`privacy_overOne`). With parts 1 and 2 this proves `Spec.family` of Rom/Family.lean (`family`).

An adversarial verifier V over the hash function becomes `downV m V` over the family: a query at a
string becomes one query at its point (oracle, query, index of the hash block). The view over the
family does not say which hash block of an answer V asked for, so the view over the hash function is
recovered from it by replaying V on it (`replay`). The environment (`ViewEnv`: the function of the
view that names the next batch) over the family is the environment over the hash function after the
replay.

Notation: `B : ℕ` (the docstring of `Gen.Arg`, ZKCP/Gen.lean): the bound B on the length of a batch;
`ζ : ℕ → ℕ → ℝ≥0∞`: the last argument of `Gen.HasIndexPrivacyWith` (there), taken at `tV N` in
`Gen.PrivacyFor`; N counts batches; `Gen.TraceConsistent tr : Prop` (there): a query that is asked
twice gets one answer, for each oracle of the family; `Batch.ownX`, `Batch.released` (there): see
their docstrings; `lLoop`, `replay` (this file): see their docstrings; their `n : ℕ`: in
`Gen.realLoop` (ZKCP/Gen.lean), the number of batches still allowed.
-/
import Rom.ExitBind
noncomputable section -- Lean tags what it cannot compile

open MeasureTheory
open scoped ENNReal

namespace Rom

open ZKCP

variable {S : OSpec} {lam : ℕ} {I X W PP IVK ISK Pf : Type}

/-! ### Logs, challengers, the loop -/

/-- What a view holds beside ivk. -/
structure Log (S : OSpec) (X Pf : Type) where
  sessions : List (List (X × Pf))
  trace : Trace S
  coins : List ℕ

namespace Log
def nil : Log S X Pf := ⟨[], [], []⟩
def app (a b : Log S X Pf) : Log S X Pf :=
  ⟨a.sessions ++ b.sessions, a.trace ++ b.trace, a.coins ++ b.coins⟩
def view (ivk : IVK) (l : Log S X Pf) : Gen.View S IVK X Pf := ⟨ivk, l.sessions, l.trace, l.coins⟩
def ofView (v : Gen.View S IVK X Pf) : Log S X Pf := ⟨v.sessions, v.trace, v.coins⟩
def oneS (x : List (X × Pf)) : Log S X Pf := ⟨[x], [], []⟩
def oneT (e : QA S) : Log S X Pf := ⟨[], [e], []⟩
def oneC (c : ℕ) : Log S X Pf := ⟨[], [], [c]⟩
end Log

/-- The challenger of an adversarial verifier: it answers oracle queries and serves batches. -/
structure GWorld (S : OSpec) (X W Pf : Type) where
  σ : Type
  answer : σ → (o : S.ι) → S.Dom o → PMF (S.Rng o × σ)
  serve : σ → Gen.Batch X W → PMF (List (X × Pf) × σ)

/-- The loop of the two privacy experiments, against a challenger. -/
def lLoop (Wd : GWorld S X W Pf) (Z : Log S X Pf → Option (Gen.Batch X W)) :
    Gen.AdvVerifier S X Pf → ℕ → Log S X Pf → Wd.σ → PMF (Log S X Pf)
  | .halt, _, l, _ => PMF.pure l
  | .query o q k, n, l, s =>
      (Wd.answer s o q).bind fun out =>
        lLoop Wd Z (k out.1) n { l with trace := l.trace ++ [⟨o, q, out.1⟩] } out.2
  | .sample mm k, n, l, s =>
      (PMF.uniformOfFintype (Fin (mm + 1))).bind fun r =>
        lLoop Wd Z (k r) n { l with coins := l.coins ++ [r.val] } s
  | .request _, 0, l, _ => PMF.pure l
  | .request k, n + 1, l, s =>
      match Z l with
      | none => PMF.pure l
      | some b =>
        (Wd.serve s b).bind fun out =>
          lLoop Wd Z (k out.1) n { l with sessions := l.sessions ++ [out.1] } out.2

/-- The ideal experiment's challenger: the simulator. -/
def simWorld (Sim : Gen.Simulator S PP IVK X Pf) : GWorld S X W Pf where
  σ := Sim.St
  answer := Sim.answer
  serve s b := (Sim.prove s b.ownX).map fun out => (b.ownX.zip out.1.val, out.2)

/-- The real experiment's challenger, the family F fixed. -/
def eagerWorld (A : Gen.Arg S I X W IVK ISK Pf) (isk : ISK) (F : Fam S) :
    GWorld S X W Pf where
  σ := Unit
  answer _ o q := PMF.pure (F o q, ())
  serve _ b := ((A.P isk b.pairs).runEager F).map fun πs => (b.released πs.val, ())

theorem idealLoop_eq (Sim : Gen.Simulator S PP IVK X Pf) (Z : Gen.ViewEnv S IVK X W Pf) (ivk : IVK)
    (V : Gen.AdvVerifier S X Pf) :
    ∀ (n : ℕ) (l : Log S X Pf) (s : Sim.St),
      Gen.idealLoop Sim Z V n (l.view ivk) s
        = (lLoop (simWorld Sim) (fun l => Z (l.view ivk)) V n l s).map (Log.view ivk) := by
  induction V with
  | halt => intro n l s; simp only [Gen.idealLoop, lLoop, PMF.pure_map]
  | query o q k ih =>
    intro n l s
    simp only [Gen.idealLoop, lLoop, PMF.map_bind]
    exact congrArg _ (funext fun out => ih _ n { l with trace := l.trace ++ [⟨o, q, out.1⟩] } out.2)
  | sample mm k ih =>
    intro n l s
    simp only [Gen.idealLoop, lLoop, PMF.map_bind]
    exact congrArg _ (funext fun r => ih _ n { l with coins := l.coins ++ [r.val] } s)
  | request k ih =>
    intro n l s
    cases n with
    | zero => simp only [Gen.idealLoop, lLoop, PMF.pure_map]
    | succ n =>
      cases hz : Z (l.view ivk) with
      | none => simp only [Gen.idealLoop, lLoop, hz, PMF.pure_map]
      | some b =>
        simp only [Gen.idealLoop, lLoop, hz, PMF.map_bind]
        show _ = ((Sim.prove s b.ownX).map _).bind _
        rw [PMF.bind_map]
        exact congrArg _ (funext fun out =>
          ih _ n { l with sessions := l.sessions ++ [b.ownX.zip out.1.val] } out.2)

theorem realLoop_eq (A : Gen.Arg S I X W IVK ISK Pf) (Z : Gen.ViewEnv S IVK X W Pf) (isk : ISK)
    (ivk : IVK) (F : Fam S) (V : Gen.AdvVerifier S X Pf) :
    ∀ (n : ℕ) (l : Log S X Pf), (Gen.realLoop A Z isk V n (l.view ivk)).runEager F =
      (lLoop (eagerWorld A isk F) (fun l => Z (l.view ivk)) V n l ()).map (Log.view ivk) := by
  induction V with
  | halt => intro n l; simp only [Gen.realLoop, lLoop, PMF.pure_map]; rfl
  | query o q k ih =>
    intro n l
    simp only [Gen.realLoop, lLoop, OComp.runEager, PMF.map_bind]
    show _ = (PMF.pure (F o q, ())).bind _
    rw [PMF.pure_bind]
    exact ih _ n { l with trace := l.trace ++ [⟨o, q, F o q⟩] }
  | sample mm k ih =>
    intro n l
    simp only [Gen.realLoop, lLoop, OComp.runEager, PMF.map_bind]
    exact congrArg _ (funext fun r => ih _ n { l with coins := l.coins ++ [r.val] })
  | request k ih =>
    intro n l
    cases n with
    | zero => simp only [Gen.realLoop, lLoop, PMF.pure_map]; rfl
    | succ n =>
      cases hz : Z (l.view ivk) with
      | none => simp only [Gen.realLoop, lLoop, hz, PMF.pure_map]; rfl
      | some b =>
        simp only [Gen.realLoop, lLoop, hz, PMF.map_bind, OComp.runEager_bind]
        show _ = (((A.P isk b.pairs).runEager F).map _).bind _
        rw [PMF.bind_map]
        exact congrArg _
          (funext fun πs => ih _ n { l with sessions := l.sessions ++ [b.released πs.val] })

/-! ### Shifting the start of the loop -/

theorem lLoop_shift (Wd : GWorld S X W Pf) (a : Log S X Pf) (V : Gen.AdvVerifier S X Pf) :
    ∀ (Z : Log S X Pf → Option (Gen.Batch X W)) (n : ℕ) (l : Log S X Pf) (s : Wd.σ),
      lLoop Wd Z V n (a.app l) s = (lLoop Wd (fun l' => Z (a.app l')) V n l s).map a.app := by
  induction V with
  | halt => intro Z n l s; simp only [lLoop, PMF.pure_map]
  | query o q k ih =>
    intro Z n l s
    simp only [lLoop, PMF.map_bind]
    refine congrArg _ (funext fun out => ?_)
    rw [← ih]
    simp [Log.app]
  | sample mm k ih =>
    intro Z n l s
    simp only [lLoop, PMF.map_bind]
    refine congrArg _ (funext fun r => ?_)
    rw [← ih]
    simp [Log.app]
  | request k ih =>
    intro Z n l s
    cases n with
    | zero => simp only [lLoop, PMF.pure_map]
    | succ n =>
      cases hz : Z (a.app l) with
      | none => simp only [lLoop, hz, PMF.pure_map]
      | some b =>
        simp only [lLoop, hz, PMF.map_bind]
        refine congrArg _ (funext fun out => ?_)
        rw [← ih]
        simp [Log.app]

/-! ### From the hash function to the family -/

/-- A challenger over the family, seen through the hash function: a query at a string is answered
with the hash block of the challenger's answer. -/
def oneWorld (m : OracleCoding S lam) (Wd : GWorld S X W Pf) : GWorld (rom lam) X W Pf where
  σ := Wd.σ
  answer s _ str :=
    (Wd.answer s (m.dec str).1 (m.dec str).2.1).map fun out => (m.blk out.1 (m.dec str).2.2, out.2)
  serve := Wd.serve

/-- The adversarial verifier over the family: a query at a string becomes one query at its point. -/
def downV (m : OracleCoding S lam) : Gen.AdvVerifier (rom lam) X Pf → Gen.AdvVerifier S X Pf
  | .halt => .halt
  | .sample n k => .sample n fun r => downV m (k r)
  | .query _ s k => .query (m.dec s).1 (m.dec s).2.1 fun r => downV m (k (m.blk r (m.dec s).2.2))
  | .request k => .request fun l => downV m (k l)

theorem queryBound_downV (m : OracleCoding S lam) (V : Gen.AdvVerifier (rom lam) X Pf) :
    ∀ t, V.QueryBound t → (downV m V).QueryBound t := by
  induction V with
  | halt => intro t _; trivial
  | sample n k ih => exact fun t h r => ih r t (h r)
  | query u s k ih =>
    intro t h
    cases t with
    | zero => exact h
    | succ t => exact fun r => ih _ t (h _)
  | request k ih => exact fun t h l => ih l t (h l)

open Classical in
/-- Replay V on a log over the family: the log over the hash function that V has seen. It stops
where the log ends or does not fit V's next move. -/
def replay (m : OracleCoding S lam) :
    Gen.AdvVerifier (rom lam) X Pf → ℕ → Log S X Pf → Log (rom lam) X Pf
  | .halt, _, _ => Log.nil
  | .sample mm k, n, l =>
      match l.coins with
      | [] => Log.nil
      | c :: cs =>
        if hc : c < mm + 1 then (Log.oneC c).app (replay m (k ⟨c, hc⟩) n { l with coins := cs })
        else Log.nil
  | .query _ s k, n, l =>
      match l.trace with
      | [] => Log.nil
      | e :: tr =>
        if he : (⟨e.1, e.2.1⟩ : Σ o, S.Dom o) = ⟨(m.dec s).1, (m.dec s).2.1⟩ then
          (Log.oneT ⟨(), s, m.blk (congrArg Sigma.fst he ▸ e.2.2) (m.dec s).2.2⟩).app
            (replay m (k (m.blk (congrArg Sigma.fst he ▸ e.2.2) (m.dec s).2.2))
              n { l with trace := tr })
        else Log.nil
  | .request _, 0, _ => Log.nil
  | .request k, n + 1, l =>
      match l.sessions with
      | [] => Log.nil
      | x :: xs => (Log.oneS x).app (replay m (k x) n { l with sessions := xs })

theorem replay_sample (m : OracleCoding S lam) (mm : ℕ) (k : Fin (mm + 1) → Gen.AdvVerifier (rom lam) X Pf)
    (n : ℕ) (r : Fin (mm + 1)) (l : Log S X Pf) :
    replay m (.sample mm k) n ((Log.oneC r.val).app l) =
      (Log.oneC r.val).app (replay m (k r) n l) := by
  simp only [replay, Log.app, Log.oneC, List.cons_append, List.nil_append, r.isLt, dif_pos, Fin.eta]

theorem replay_query (m : OracleCoding S lam) (s : List Bool)
    (k : (rom lam).Rng () → Gen.AdvVerifier (rom lam) X Pf) (n : ℕ)
    (r : S.Rng (m.dec s).1) (l : Log S X Pf) :
    replay m (.query () s k) n ((Log.oneT ⟨(m.dec s).1, (m.dec s).2.1, r⟩).app l) =
      (Log.oneT ⟨(), s, m.blk r (m.dec s).2.2⟩).app (replay m (k (m.blk r (m.dec s).2.2)) n l) := by
  simp only [replay, Log.app, Log.oneT, List.cons_append, List.nil_append, dif_pos]

theorem replay_request (m : OracleCoding S lam) (k : List (X × Pf) → Gen.AdvVerifier (rom lam) X Pf) (n : ℕ)
    (x : List (X × Pf)) (l : Log S X Pf) :
    replay m (.request k) (n + 1) ((Log.oneS x).app l) = (Log.oneS x).app (replay m (k x) n l) := by
  simp only [replay, Log.app, Log.oneS, List.cons_append, List.nil_append]

/-- The replay lemma, for every challenger: the loop over the hash function is the image, under the
replay, of the loop over the family. -/
theorem loop_replay (m : OracleCoding S lam) (Wd : GWorld S X W Pf) (V : Gen.AdvVerifier (rom lam) X Pf) :
    ∀ (Z : Log (rom lam) X Pf → Option (Gen.Batch X W)) (n : ℕ) (s : Wd.σ),
      lLoop (oneWorld m Wd) Z V n Log.nil s
        = (lLoop Wd (fun l => Z (replay m V n l)) (downV m V) n Log.nil s).map (replay m V n) := by
  induction V with
  | halt => intro Z n s; simp only [lLoop, downV, PMF.pure_map, replay]
  | sample mm k ih =>
    intro Z n s
    simp only [lLoop, downV, PMF.map_bind]
    refine congrArg _ (funext fun r => ?_)
    have e1 : ({ (Log.nil : Log (rom lam) X Pf) with
                 coins := (Log.nil : Log (rom lam) X Pf).coins ++ [r.val] }) =
        (Log.oneC r.val).app Log.nil := rfl
    have e2 : ({ (Log.nil : Log S X Pf) with coins := (Log.nil : Log S X Pf).coins ++ [r.val] })
        = (Log.oneC r.val).app Log.nil := rfl
    rw [e1, e2, lLoop_shift, lLoop_shift, ih, PMF.map_comp, PMF.map_comp]
    simp only [replay_sample, Function.comp_def]
  | query u s k ih =>
    intro Z n st
    cases u
    simp only [lLoop, downV, PMF.map_bind]
    show ((Wd.answer st (m.dec s).1 (m.dec s).2.1).map _).bind _ = _
    rw [PMF.bind_map]
    refine congrArg _ (funext fun out => ?_)
    have e1 : ({ (Log.nil : Log (rom lam) X Pf) with
        trace := (Log.nil : Log (rom lam) X Pf).trace ++ [⟨(), s, m.blk out.1 (m.dec s).2.2⟩] })
        = (Log.oneT ⟨(), s, m.blk out.1 (m.dec s).2.2⟩).app Log.nil := rfl
    have e2 : ({ (Log.nil : Log S X Pf) with
        trace := (Log.nil : Log S X Pf).trace ++ [⟨(m.dec s).1, (m.dec s).2.1, out.1⟩] })
        = (Log.oneT ⟨(m.dec s).1, (m.dec s).2.1, out.1⟩).app Log.nil := rfl
    simp only [Function.comp_def]
    rw [e1, e2, lLoop_shift, lLoop_shift, ih, PMF.map_comp, PMF.map_comp]
    simp only [replay_query, Function.comp_def]
  | request k ih =>
    intro Z n s
    cases n with
    | zero => simp only [lLoop, downV, PMF.pure_map, replay]
    | succ n =>
      have hnil : replay m (.request k) (n + 1) (Log.nil : Log S X Pf) = Log.nil := rfl
      cases hz : Z Log.nil with
      | none => simp only [lLoop, downV, hnil, hz, PMF.pure_map]
      | some b =>
        simp only [lLoop, downV, hnil, hz, PMF.map_bind]
        refine congrArg _ (funext fun out => ?_)
        have e1 : ({ (Log.nil : Log (rom lam) X Pf) with
                     sessions := (Log.nil : Log (rom lam) X Pf).sessions ++ [out.1] }) =
            (Log.oneS out.1).app Log.nil := rfl
        have e2 : ({ (Log.nil : Log S X Pf) with
                     sessions := (Log.nil : Log S X Pf).sessions ++ [out.1] }) =
            (Log.oneS out.1).app Log.nil := rfl
        rw [e1, e2, lLoop_shift, lLoop_shift, ih, PMF.map_comp, PMF.map_comp]
        simp only [replay_request, Function.comp_def]

/-! ### The two experiments -/

/-- The simulator over the hash function: a query at a string is answered with the hash block of the
simulator's answer at its point. -/
def simOne (m : OracleCoding S lam) (Sim : Gen.Simulator S PP IVK X Pf) :
    Gen.Simulator (rom lam) PP IVK X Pf where
  St := Sim.St
  init := Sim.init
  answer s _ str :=
    (Sim.answer s (m.dec str).1 (m.dec str).2.1).map fun out => (m.blk out.1 (m.dec str).2.2, out.2)
  prove := Sim.prove

theorem simWorld_simOne (m : OracleCoding S lam) (Sim : Gen.Simulator S PP IVK X Pf) :
    (simWorld (simOne m Sim) : GWorld (rom lam) X W Pf) = oneWorld m (simWorld Sim) := rfl

theorem eagerWorld_glue (m : OracleCoding S lam) (A : Gen.Arg S I X W IVK ISK Pf) (isk : ISK) (F : Fam S) :
    eagerWorld (schemeOverOneHashFunction m A) isk (glue m F) = oneWorld m (eagerWorld A isk F) := by
  simp only [eagerWorld, oneWorld, schemeOverOneHashFunction, runEager_overOne, readBlocks_glue, PMF.pure_map]
  rfl

theorem lLoop_congr {Wd₁ Wd₂ : GWorld S X W Pf} (h : Wd₁ = Wd₂)
    (Z : Log S X Pf → Option (Gen.Batch X W)) (V : Gen.AdvVerifier S X Pf) (n : ℕ)
    (l : Log S X Pf) (s : Wd₁.σ) :
    lLoop Wd₁ Z V n l s = lLoop Wd₂ Z V n l (cast (congrArg GWorld.σ h) s) := by
  subst h; rfl

/-- The view over the hash function, recovered from the view over the family. -/
def replayView (m : OracleCoding S lam) (Vt : IVK → Gen.AdvVerifier (rom lam) X Pf) (N : ℕ)
    (v : Gen.View S IVK X Pf) : Gen.View (rom lam) IVK X Pf :=
  (replay m (Vt v.ivk) N (Log.ofView v)).view v.ivk

theorem realExp_glue (m : OracleCoding S lam) (A : Gen.Arg S I X W IVK ISK Pf)
    (Vt : IVK → Gen.AdvVerifier (rom lam) X Pf) (Z : Gen.ViewEnv (rom lam) IVK X W Pf)
    (i : I) (N : ℕ) (F : Fam S) :
    (Gen.realExp (schemeOverOneHashFunction m A) Vt Z i N).runEager (glue m F) =
      ((Gen.realExp A (fun ivk => downV m (Vt ivk))
          (fun v => Z (replayView m Vt N v)) i N).runEager F).map
        (replayView m Vt N) := by
  have e1 : Gen.realExp (schemeOverOneHashFunction m A) Vt Z i N = ((A.C i).overOne m).bind fun key =>
      Gen.realLoop (schemeOverOneHashFunction m A)
          Z key.2 (Vt key.1) N ((Log.nil : Log (rom lam) X Pf).view key.1) := rfl
  have e2 : Gen.realExp A (fun ivk => downV m (Vt ivk)) (fun v => Z (replayView m Vt N v)) i N = (A.C i).bind fun key =>
      Gen.realLoop A (fun v => Z (replayView m Vt N v)) key.2 (downV m (Vt key.1)) N
        ((Log.nil : Log S X Pf).view key.1) := rfl
  rw [e1, e2]
  simp only [OComp.runEager_bind, runEager_overOne, readBlocks_glue, PMF.map_bind]
  refine congrArg _ (funext fun key => ?_)
  rw [realLoop_eq, realLoop_eq, lLoop_congr (eagerWorld_glue m A key.2 F), loop_replay,
    PMF.map_comp, PMF.map_comp]
  rfl

theorem idealExp_simOne (m : OracleCoding S lam) (R : Gen.RelPair I X W PP)
    (Sim : Gen.Simulator S PP IVK X Pf) (Vt : IVK → Gen.AdvVerifier (rom lam) X Pf)
    (Z : Gen.ViewEnv (rom lam) IVK X W Pf) (i : I) (N : ℕ) :
    Gen.idealExp R (simOne m Sim) Vt Z i N =
      (Gen.idealExp R Sim (fun ivk => downV m (Vt ivk)) (fun v => Z (replayView m Vt N v)) i N).map
        (replayView m Vt N) := by
  have e1 : Gen.idealExp R (simOne m Sim) Vt Z i N = (Sim.init (R.pp i) N).bind fun out =>
      Gen.idealLoop (simOne m Sim)
          Z (Vt out.1) N ((Log.nil : Log (rom lam) X Pf).view out.1) out.2 := rfl
  have e2 : Gen.idealExp R Sim (fun ivk => downV m (Vt ivk)) (fun v => Z (replayView m Vt N v)) i N
      = (Sim.init (R.pp i) N).bind fun out =>
        Gen.idealLoop Sim (fun v => Z (replayView m Vt N v)) (downV m (Vt out.1)) N
          ((Log.nil : Log S X Pf).view out.1) out.2 := rfl
  rw [e1, e2, PMF.map_bind]
  refine congrArg _ (funext fun out => ?_)
  rw [idealLoop_eq, idealLoop_eq]
  have hl :=
    loop_replay m (simWorld (W := W) Sim) (Vt out.1) (fun l => Z (Log.view out.1 l)) N out.2
  change PMF.map _ (lLoop (oneWorld m (simWorld Sim)) _ _ _ _ _) = _
  rw [hl, PMF.map_comp, PMF.map_comp]
  rfl

/-! ### Consistency -/

/-- For every entry (s, b) of a replayed trace, the log's trace has an entry at the oracle and query
that s encodes, and b is the hash block of its answer that s encodes. -/
theorem mem_replay_trace (m : OracleCoding S lam) (V : Gen.AdvVerifier (rom lam) X Pf) :
    ∀ (n : ℕ) (l : Log S X Pf) (s : List Bool) (b : Fin lam → Bool), (⟨(), s, b⟩ : QA (rom lam)) ∈
        (replay m V n l).trace →
      ∃ r : S.Rng (m.dec s).1,
        (⟨(m.dec s).1, (m.dec s).2.1, r⟩ : QA S) ∈ l.trace ∧ b = m.blk r (m.dec s).2.2 := by
  induction V with
  | halt => intro n l s b h; simp [replay, Log.nil] at h
  | sample mm k ih =>
    intro n l s b h
    simp only [replay] at h
    cases hc : l.coins with
    | nil => simp [hc, Log.nil] at h
    | cons c cs =>
      simp only [hc] at h
      by_cases hlt : c < mm + 1
      · simp only [hlt, dif_pos, Log.app, Log.oneC, List.nil_append] at h
        exact ih _ n { l with coins := cs } s b h
      · simp [hlt, Log.nil] at h
  | query u s' k ih =>
    intro n l s b h
    simp only [replay] at h
    cases ht : l.trace with
    | nil => simp [ht, Log.nil] at h
    | cons e tr =>
      simp only [ht] at h
      by_cases he : (⟨e.1, e.2.1⟩ : Σ o, S.Dom o) = ⟨(m.dec s').1, (m.dec s').2.1⟩
      · simp only [he, dif_pos, Log.app, Log.oneT, List.cons_append,
          List.nil_append, List.mem_cons] at h
        rcases h with h | h
        · obtain ⟨o, q, r⟩ := e
          simp only at he
          obtain ⟨rfl, hq⟩ := Sigma.mk.inj_iff.1 he
          have hq' := eq_of_heq hq
          subst hq'
          simp only [Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨r, List.mem_cons_self, rfl⟩
        · obtain ⟨r, hr, hb⟩ := ih _ n _ s b h
          exact ⟨r, List.mem_cons_of_mem _ hr, hb⟩
      · simp [he, Log.nil] at h
  | request k ih =>
    intro n l s b h
    cases n with
    | zero => simp [replay, Log.nil] at h
    | succ n =>
      simp only [replay] at h
      cases hs : l.sessions with
      | nil => simp [hs, Log.nil] at h
      | cons x xs =>
        simp only [hs, Log.app, Log.oneS, List.nil_append] at h
        exact ih _ n { l with sessions := xs } s b h

theorem consistent_replay (m : OracleCoding S lam) (V : Gen.AdvVerifier (rom lam) X Pf) (n : ℕ)
    (l : Log S X Pf) (h : Gen.TraceConsistent l.trace) :
    Gen.TraceConsistent (replay m V n l).trace := by
  rintro ⟨⟩ s b b' h1 h2
  obtain ⟨r, hr, rfl⟩ := mem_replay_trace m V n l s b h1
  obtain ⟨r', hr', rfl⟩ := mem_replay_trace m V n l s b' h2
  rw [h _ _ r r' hr hr']

/-! ### Index privacy carries over; the whole step -/

theorem privacy_overOne (m : OracleCoding S lam) (R : Gen.RelPair I X W PP) (A : Gen.Arg S I X W IVK ISK Pf)
    (B : ℕ) (Sim : Gen.Simulator S PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞)
    (h : Gen.HasIndexPrivacyWith R A B Sim ζ) :
    Gen.HasIndexPrivacyWith R (schemeOverOneHashFunction m A) B (simOne m Sim) ζ := by
  intro i Z hZ tV Vt N hb
  obtain ⟨h1, h2⟩ := h i (fun v => Z (replayView m Vt N v)) (fun v b hv => hZ _ b hv) tV
    (fun ivk => downV m (Vt ivk)) N fun ivk => queryBound_downV m (Vt ivk) tV (hb ivk)
  have hreal : ∀ T, Pr (Gen.realExp (schemeOverOneHashFunction m A) Vt Z i N) (fun _ => T)
      = Pr (Gen.realExp A (fun ivk => downV m (Vt ivk)) (fun v => Z (replayView m Vt N v)) i N)
          (fun _ => replayView m Vt N ⁻¹' T) := by
    intro T
    unfold Pr
    rw [lintegral_glue m (fun g => PrCoins g (Gen.realExp (schemeOverOneHashFunction m A) Vt Z i N) T)]
    · simp only [PrCoins, realExp_glue, Prob.pr_map]
    · simp only [PrCoins, realExp_glue, Prob.pr_map]
      exact measurable_PrCoins _ _
  have hideal : ∀ T, Prob.pr (Gen.idealExp R (simOne m Sim) Vt Z i N) T =
      Prob.pr
        (Gen.idealExp R Sim (fun ivk => downV m (Vt ivk)) (fun v => Z (replayView m Vt N v)) i N)
        (replayView m Vt N ⁻¹' T) := by
    intro T
    rw [idealExp_simOne, Prob.pr_map]
  constructor
  · simp only [hreal, hideal]
    exact (Prob.sd_comap_le _ _ (replayView m Vt N)).trans h1
  · rw [hideal]
    refine le_antisymm (le_trans (Prob.pr_mono _ ?_) (le_of_eq h2)) (zero_le _)
    intro v hv hc
    exact hv (consistent_replay m (Vt v.ivk) N (Log.ofView v) hc)

/-- The step to one hash function: the statement `Spec.family` of Rom/Family.lean. -/
theorem family : Spec.family := by
  intro S lam m I X W PP IVK ISK Pf R A B E α ε ζ hE hc hb hp
  obtain ⟨Sim, hS⟩ := hp
  exact ⟨completeness_overOne m R A B α hc, ⟨extractorOverOneHashFunction m E, binding_overOne m R A E hE ε hb⟩,
    ⟨simOne m Sim, privacy_overOne m R A B Sim ζ hS⟩⟩

end Rom
