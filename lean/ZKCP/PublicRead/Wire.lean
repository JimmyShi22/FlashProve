-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/PublicRead/Wire.lean: AN ADVERSARIAL VERIFIER WITH A LIST OF ANSWERS WIRED IN, and the view of
the verifier itself, recovered from the view of the wired one. Definitions, and theorems with their
proofs.

General definitions and lemmas, over one hash function. This file states no goal of the release. It
serves ZKCP/PublicRead/Privacy.lean.

A list l of (string, answer) is fixed.
  listWorld l Wd   a challenger with the list in front: a query at a string of the list is answered
                   from the list, AND THE CHALLENGER's STATE IS LEFT UNTOUCHED; every other query,
                   and every batch, goes to the challenger Wd.
  wireV l V        the verifier V with the list wired in: at a string of the list it asks nothing
                   and goes on with the listed answer.
  replayL l V n    V replayed on a log of wireV l V: the log that V itself has seen, with the
                   entries at listed strings laid back in. It stops where the log ends or does not
                   fit V's next move.
  loop_list        THE LAW: V against listWorld l Wd is wireV l V against Wd, with the log replayed;
                   the environment of the second run is the environment of the first behind the
                   replay. It holds for every challenger: so for the real experiment under a fixed
                   hash function and for the ideal one.
  replayL_sample, replayL_none, replayL_some, replayL_request   the replay commutes with the ways in
                   which a log grows.
  queryBound_wireV   the wired verifier asks no more.
  consistent_replayL   a consistent log is replayed to a consistent log.

It follows the pattern of Rom/ExitPriv.lean (downV, replay, loop_replay, mem_replay_trace,
consistent_replay), whose types of logs and challengers (Log, GWorld, lLoop, lLoop_shift) it uses.
Terms: lean/GLOSSARY.md.

-/
import ZKCP.PublicRead.Spec

set_option autoImplicit false

noncomputable section

namespace ZKCP.PublicRead
open Rom Prob

variable {lam : ℕ} {X W Pf : Type}

/-- **A challenger with the list in front.** -/
def listWorld (l : Path lam) (Wd : GWorld (rom lam) X W Pf) : GWorld (rom lam) X W Pf where
  σ := Wd.σ
  answer := fun st u s =>
    match l.lookup s with
    | some r => PMF.pure (r, st)
    | none => Wd.answer st u s
  serve := Wd.serve

/-- **The verifier with the list wired in.** -/
def wireV (l : Path lam) : Gen.AdvVerifier (rom lam) X Pf → Gen.AdvVerifier (rom lam) X Pf
  | .halt => .halt
  | .sample n k => .sample n fun r => wireV l (k r)
  | .request k => .request fun x => wireV l (k x)
  | .query u s k =>
      match l.lookup s with
      | some r => wireV l (k r)
      | none => .query u s fun r => wireV l (k r)

/-- The wired verifier asks no more. -/
theorem queryBound_wireV (l : Path lam) : ∀ (V : Gen.AdvVerifier (rom lam) X Pf) (t : ℕ),
    V.QueryBound t → (wireV l V).QueryBound t := by
  intro V
  induction V with
  | halt => exact fun _ _ => trivial
  | sample n k ih => exact fun t h r => ih r t (h r)
  | request k ih => exact fun t h x => ih x t (h x)
  | query u s k ih =>
    intro t h
    cases t with
    | zero => exact h.elim
    | succ t =>
      have up : ∀ (V' : Gen.AdvVerifier (rom lam) X Pf) (t' : ℕ), V'.QueryBound t' →
          V'.QueryBound (t' + 1) := by
        intro V'
        induction V' with
        | halt => exact fun _ _ => trivial
        | sample n k ih' => exact fun t' h' r => ih' r t' (h' r)
        | request k ih' => exact fun t' h' x => ih' x t' (h' x)
        | query u s k ih' =>
          intro t' h'
          cases t' with
          | zero => exact h'.elim
          | succ t' => exact fun r => ih' r t' (h' r)
      cases hl : l.lookup s with
      | some r =>
        simp only [wireV, hl]
        exact up _ t (ih r t (h r))
      | none =>
        simp only [wireV, hl]
        exact fun r => ih r t (h r)

/-- **The verifier replayed on a log of the wired verifier.** -/
def replayL (l : Path lam) :
    Gen.AdvVerifier (rom lam) X Pf → ℕ → Log (rom lam) X Pf → Log (rom lam) X Pf
  | .halt, _, _ => Log.nil
  | .sample mm k, n, lg =>
      match lg.coins with
      | [] => Log.nil
      | c :: cs =>
        if hc : c < mm + 1 then (Log.oneC c).app (replayL l (k ⟨c, hc⟩) n { lg with coins := cs })
        else Log.nil
  | .query _ s k, n, lg =>
      match l.lookup s with
      | some r => (Log.oneT ⟨(), s, r⟩).app (replayL l (k r) n lg)
      | none =>
        match lg.trace with
        | [] => Log.nil
        | e :: tr =>
          if (show List Bool from e.2.1) = s then
            (Log.oneT ⟨(), s, e.2.2⟩).app (replayL l (k e.2.2) n { lg with trace := tr })
          else Log.nil
  | .request _, 0, _ => Log.nil
  | .request k, n + 1, lg =>
      match lg.sessions with
      | [] => Log.nil
      | x :: xs => (Log.oneS x).app (replayL l (k x) n { lg with sessions := xs })

/-! ## The replay commutes with the ways in which a log grows -/

theorem replayL_sample (l : Path lam) (mm : ℕ)
    (k : Fin (mm + 1) → Gen.AdvVerifier (rom lam) X Pf) (n : ℕ) (r : Fin (mm + 1))
    (lg : Log (rom lam) X Pf) :
    replayL l (.sample mm k) n ((Log.oneC r.val).app lg) =
      (Log.oneC r.val).app (replayL l (k r) n lg) := by
  simp only [replayL, Log.app, Log.oneC, List.cons_append, List.nil_append, r.isLt, dif_pos,
    Fin.eta]

theorem replayL_none (l : Path lam) (s : (rom lam).Dom ())
    (k : (rom lam).Rng () → Gen.AdvVerifier (rom lam) X Pf) (n : ℕ) (r : (rom lam).Rng ())
    (lg : Log (rom lam) X Pf) (hl : l.lookup s = none) :
    replayL l (.query () s k) n ((Log.oneT ⟨(), s, r⟩).app lg) =
      (Log.oneT ⟨(), s, r⟩).app (replayL l (k r) n lg) := by
  simp only [replayL, hl, Log.app, Log.oneT, List.cons_append, List.nil_append, if_true]

theorem replayL_some (l : Path lam) (s : (rom lam).Dom ())
    (k : (rom lam).Rng () → Gen.AdvVerifier (rom lam) X Pf) (n : ℕ) (r : (rom lam).Rng ())
    (lg : Log (rom lam) X Pf) (hl : l.lookup s = some r) :
    replayL l (.query () s k) n lg = (Log.oneT ⟨(), s, r⟩).app (replayL l (k r) n lg) := by
  simp only [replayL, hl]

theorem replayL_request (l : Path lam) (k : List (X × Pf) → Gen.AdvVerifier (rom lam) X Pf) (n : ℕ)
    (x : List (X × Pf)) (lg : Log (rom lam) X Pf) :
    replayL l (.request k) (n + 1) ((Log.oneS x).app lg) =
      (Log.oneS x).app (replayL l (k x) n lg) := by
  simp only [replayL, Log.app, Log.oneS, List.cons_append, List.nil_append]

/-! ## The law -/

/-- **The verifier against the challenger with the list in front is the wired verifier against the
challenger, with the log replayed.** -/
theorem loop_list (l : Path lam) (Wd : GWorld (rom lam) X W Pf)
    (V : Gen.AdvVerifier (rom lam) X Pf) :
    ∀ (Z : Log (rom lam) X Pf → Option (Gen.Batch X W)) (n : ℕ) (st : Wd.σ),
      lLoop (listWorld l Wd) Z V n Log.nil st =
        (lLoop Wd (fun lg => Z (replayL l V n lg)) (wireV l V) n Log.nil st).map
          (replayL l V n) := by
  induction V with
  | halt => intro Z n st; simp only [lLoop, wireV, PMF.pure_map, replayL]
  | sample mm k ih =>
    intro Z n st
    simp only [lLoop, wireV, PMF.map_bind]
    refine congrArg _ (funext fun r => ?_)
    have e1 : ({ (Log.nil : Log (rom lam) X Pf) with
        coins := (Log.nil : Log (rom lam) X Pf).coins ++ [r.val] }) =
        (Log.oneC r.val).app Log.nil := rfl
    rw [e1, lLoop_shift, lLoop_shift, ih, PMF.map_comp, PMF.map_comp]
    simp only [replayL_sample, Function.comp_def]
  | query u s k ih =>
    intro Z n st
    cases u
    cases hl : l.lookup s with
    | some r =>
      have e0 : lLoop (listWorld l Wd) Z (.query () s k) n Log.nil st =
          lLoop (listWorld l Wd) Z (k r) n ((Log.oneT ⟨(), s, r⟩).app Log.nil) st := by
        simp only [lLoop]
        show (match l.lookup s with
          | some r => PMF.pure (r, st)
          | none => Wd.answer st () s).bind _ = _
        rw [hl]
        exact PMF.pure_bind _ _
      have e2 : wireV l (.query () s k) = wireV l (k r) := by simp only [wireV, hl]
      have e3 : replayL l (Gen.AdvVerifier.query () s k) n =
          fun lg => (Log.oneT ⟨(), s, r⟩).app (replayL l (k r) n lg) :=
        funext fun lg => replayL_some l s k n r lg hl
      rw [e0, e2, e3, lLoop_shift, ih, PMF.map_comp]
      rfl
    | none =>
      have e2 : wireV l (.query () s k) = .query () s fun r => wireV l (k r) := by
        simp only [wireV, hl]
      rw [e2]
      simp only [lLoop, PMF.map_bind]
      show (match l.lookup s with
        | some r => PMF.pure (r, st)
        | none => Wd.answer st () s).bind _ = _
      rw [hl]
      refine congrArg _ (funext fun out => ?_)
      have e1 : ({ (Log.nil : Log (rom lam) X Pf) with
          trace := (Log.nil : Log (rom lam) X Pf).trace ++ [⟨(), s, out.1⟩] }) =
          (Log.oneT ⟨(), s, out.1⟩).app Log.nil := rfl
      rw [e1, lLoop_shift, lLoop_shift, ih, PMF.map_comp, PMF.map_comp]
      simp only [replayL_none l s k n _ _ hl, Function.comp_def]
  | request k ih =>
    intro Z n st
    cases n with
    | zero => simp only [lLoop, wireV, PMF.pure_map, replayL]
    | succ n =>
      have hnil : replayL l (.request k) (n + 1) (Log.nil : Log (rom lam) X Pf) = Log.nil := rfl
      cases hz : Z Log.nil with
      | none => simp only [lLoop, wireV, hnil, hz, PMF.pure_map]
      | some b =>
        simp only [lLoop, wireV, hnil, hz, PMF.map_bind]
        refine congrArg _ (funext fun out => ?_)
        have e1 : ({ (Log.nil : Log (rom lam) X Pf) with
            sessions := (Log.nil : Log (rom lam) X Pf).sessions ++ [out.1] }) =
            (Log.oneS out.1).app Log.nil := rfl
        rw [e1, lLoop_shift, lLoop_shift, ih, PMF.map_comp, PMF.map_comp]
        simp only [replayL_request, Function.comp_def]

/-! ## Consistency -/

/-- An entry of a replayed trace is the list's, or it stands in the log, at a string that is not
listed. -/
theorem mem_replayL_trace (l : Path lam) (V : Gen.AdvVerifier (rom lam) X Pf) :
    ∀ (n : ℕ) (lg : Log (rom lam) X Pf) (s : (rom lam).Dom ()) (b : (rom lam).Rng ()),
      (⟨(), s, b⟩ : QA (rom lam)) ∈ (replayL l V n lg).trace →
      l.lookup s = some b ∨ (l.lookup s = none ∧ (⟨(), s, b⟩ : QA (rom lam)) ∈ lg.trace) := by
  induction V with
  | halt => intro n lg s b h; simp [replayL, Log.nil] at h
  | sample mm k ih =>
    intro n lg s b h
    simp only [replayL] at h
    cases hc : lg.coins with
    | nil => simp [hc, Log.nil] at h
    | cons c cs =>
      simp only [hc] at h
      by_cases hlt : c < mm + 1
      · simp only [hlt, dif_pos, Log.app, Log.oneC, List.nil_append] at h
        exact ih _ n { lg with coins := cs } s b h
      · simp [hlt, Log.nil] at h
  | query u s' k ih =>
    intro n lg s b h
    cases u
    cases hl : l.lookup s' with
    | some r =>
      simp only [replayL, hl, Log.app, Log.oneT, List.cons_append, List.nil_append,
        List.mem_cons] at h
      rcases h with h | h
      · simp only [Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Or.inl hl
      · exact ih _ n lg s b h
    | none =>
      simp only [replayL, hl] at h
      cases ht : lg.trace with
      | nil => simp [ht, Log.nil] at h
      | cons e tr =>
        simp only [ht] at h
        by_cases he : (show List Bool from e.2.1) = s'
        · simp only [he, if_true, Log.app, Log.oneT, List.cons_append, List.nil_append,
            List.mem_cons] at h
          rcases h with h | h
          · simp only [Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨⟨⟩, q, r⟩ := e
            obtain rfl : q = s := he
            exact Or.inr ⟨hl, List.mem_cons_self ..⟩
          · rcases ih _ n { lg with trace := tr } s b h with h' | ⟨h1, h2⟩
            · exact Or.inl h'
            · exact Or.inr ⟨h1, List.mem_cons_of_mem _ h2⟩
        · simp [he, Log.nil] at h
  | request k ih =>
    intro n lg s b h
    cases n with
    | zero => simp [replayL, Log.nil] at h
    | succ n =>
      simp only [replayL] at h
      cases hs : lg.sessions with
      | nil => simp [hs, Log.nil] at h
      | cons x xs =>
        simp only [hs, Log.app, Log.oneS, List.nil_append] at h
        exact ih _ n { lg with sessions := xs } s b h

/-- **A consistent log is replayed to a consistent log.** -/
theorem consistent_replayL (l : Path lam) (V : Gen.AdvVerifier (rom lam) X Pf) (n : ℕ)
    (lg : Log (rom lam) X Pf) (h : Gen.TraceConsistent lg.trace) :
    Gen.TraceConsistent (replayL l V n lg).trace := by
  rintro ⟨⟩ s b b' h1 h2
  rcases mem_replayL_trace l V n lg s b h1 with e1 | ⟨e1, m1⟩
  · rcases mem_replayL_trace l V n lg s b' h2 with e2 | ⟨e2, _⟩
    · exact Option.some.inj (e1.symm.trans e2)
    · rw [e1] at e2
      cases e2
  · rcases mem_replayL_trace l V n lg s b' h2 with e2 | ⟨_, m2⟩
    · rw [e1] at e2
      cases e2
    · exact h () s b b' m1 m2

end ZKCP.PublicRead

#print axioms ZKCP.PublicRead.queryBound_wireV
#print axioms ZKCP.PublicRead.loop_list
#print axioms ZKCP.PublicRead.consistent_replayL
