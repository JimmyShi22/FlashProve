-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/StateFirstPrivReplay.lean: the step that expands a long answer of a random oracle from a state
(Rom/StateFirst.lean), index privacy, part 1: the reduction (`downVSt`), the replay (`replaySt`),
and the replay lemma for every challenger (`loop_replaySt`).

Chain oracles, states, dr: `Link`, `stSpec` (Rom/StateFirst.lean); mixed programs, `real`, `ideal`,
`Book`: Rom/StateFirstMix.lean.

An adversarial verifier V over the second family (`stSpec`) becomes one over the first (S), which
keeps a table (`Book`, Rom/StateFirstMix.lean) and does with the answers that it receives what the
simulator `simSt` does with Sim's. A query costs the reduction at most one query
(`queryBound_downVSt`). `stWorld C Wd` is a challenger Wd over the first family (`GWorld`,
Rom/ExitPriv.lean: it answers queries and serves batches), seen through the second family; for the
challenger made of the simulator Sim it is the one made of `simSt C Sim` (`simWorld_simSt`,
Rom/StateFirstPriv.lean).

Limits: nothing on the real experiment over the second family (Rom/StateFirstPrivMix.lean), nothing
on consistency of traces (Rom/StateFirstPrivCons.lean), no bound but the count of queries
(`queryBound_downVSt`).

A difference from `ideal C false` of Rom/StateFirstMix.lean: that interpretation queries the first
family again at a repeated query for a state; the reduction here does not, because `simSt` does not
ask Sim again. With the family fixed, on the mixed experiment from the empty table the two have the
same distribution, after the replay (`ideal_mixExp`, Rom/StateFirstPrivIdeal.lean).
-/
import Rom.StateFirstFind
import Rom.ExitPriv
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Rom
open ZKCP

variable {S : OSpec} {lam : ℕ} (C : ∀ o, Link lam (S.Rng o)) {I X W PP IVK ISK Pf : Type}

/-! ## Helper lemmas and definitions -/

/-- the image of the uniform distribution under a bijection is uniform -/
theorem uniform_map_equiv {α β : Type} [Fintype α] [Nonempty α] [Fintype β]
    [Nonempty β] (e : α ≃ β) :
    (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β := by
  ext b
  rw [PMF.map_apply, tsum_eq_single (e.symm b)]
  · simp [PMF.uniformOfFintype_apply, Fintype.card_congr e]
  · intro a ha
    have : b ≠ e a := fun h => ha (by simp [h])
    simp [this]

theorem advQueryBound_mono (V : Gen.AdvVerifier S X Pf) :
    ∀ t t', t ≤ t' → V.QueryBound t → V.QueryBound t' := by
  induction V with
  | halt => intro _ _ _ _; trivial
  | sample n k ih => exact fun t t' h hb r => ih r t t' h (hb r)
  | request k ih => exact fun t t' h hb l => ih l t t' h (hb l)
  | query o q k ih =>
    intro t t' h hb
    cases t with
    | zero => exact hb.elim
    | succ t =>
      cases t' with
      | zero => omega
      | succ t' => exact fun r => ih r t t' (by omega) (hb r)

/-- the stored answer of a query to a chain oracle; none at an unchanged oracle -/
def Book.kept (b : Book S lam) (o : S.ι) (q : S.Dom o) : Option (S.Rng o) :=
  if (C o).isPlain then none else findMade b.made o q

/-- the table in a state of the simulator -/
def SimSt.book {T : Type} (st : SimSt S lam T) : Book S lam := ⟨st.made, st.loose⟩
/-- the simulator's state made of a table and a state of Sim -/
def Book.withS {T : Type} (b : Book S lam) (s : T) : SimSt S lam T := ⟨s, b.made, b.loose⟩

/-- an entry of a trace over the second family, at an oracle of the first -/
abbrev eI (o : S.ι) (q : S.Dom o) (a : (C o).Ans) : QA (stSpec S lam C) := ⟨.inl o, q, a⟩
/-- an entry at dr -/
abbrev eD (p : (Dg lam × Dg lam) × ℕ) (r : Dg lam) : QA (stSpec S lam C) := ⟨.inr (), p, r⟩

/-! ## A challenger seen through the second family -/

def stWorld (Wd : GWorld S X W Pf) : GWorld (stSpec S lam C) X W Pf where
  σ := SimSt S lam Wd.σ
  answer := fun st x => match x with
    | .inl o => fun q =>
        match st.book.kept C o q with
        | some r => PMF.pure ((C o).toAns r, st)
        | none =>
          (Wd.answer st.s o q).map fun out =>
            ((C o).toAns out.1, (st.book.note C o q out.1).withS out.2)
    | .inr _ => fun p => ansDr C st p
  serve := fun st b => (Wd.serve st.s b).map fun out => (out.1, { st with s := out.2 })

section Steps
variable (Wd : GWorld S X W Pf) (b : Book S lam) (s : Wd.σ)

theorem stWorld_inl_some {o : S.ι} {q : S.Dom o} {r : S.Rng o} (h : b.kept C o q = some r) :
    (stWorld C Wd).answer (b.withS s) (.inl o) q =
      (PMF.pure ((C o).toAns r, b.withS s) :
        PMF ((stSpec S lam C).Rng (.inl o) × (stWorld C Wd).σ)) := by
  show (match b.kept C o q with
    | some r => PMF.pure ((C o).toAns r, b.withS s)
    | none => (Wd.answer s o q).map fun out : S.Rng o × Wd.σ => ((C o).toAns out.1, (b.note C o q out.1).withS out.2)) = _
  rw [h]
  rfl

theorem stWorld_inl_none {o : S.ι} {q : S.Dom o} (h : b.kept C o q = none) :
    (stWorld C Wd).answer (b.withS s) (.inl o) q =
      ((Wd.answer s o q).map fun out =>
        ((C o).toAns out.1, (b.note C o q out.1).withS out.2) :
            PMF ((stSpec S lam C).Rng (.inl o) × (stWorld C Wd).σ)) := by
  show (match b.kept C o q with
    | some r => PMF.pure ((C o).toAns r, b.withS s)
    | none => (Wd.answer s o q).map fun out : S.Rng o × Wd.σ => ((C o).toAns out.1, (b.note C o q out.1).withS out.2)) = _
  rw [h]
  rfl

theorem stWorld_dr_some {u : Unit} {p : (Dg lam × Dg lam) × ℕ}
    {r : Dg lam} (h : drVal C b p = some r) :
    (stWorld C Wd).answer (b.withS s) (.inr u) p =
      (PMF.pure (r, b.withS s) : PMF ((stSpec S lam C).Rng (.inr u) × (stWorld C Wd).σ)) := by
  show ansDr C (b.withS s) p = _
  unfold drVal at h
  simp only [ansDr, Book.withS]
  cases h1 : b.loose.lookup p with
  | some r' => rw [h1] at h; cases h; rfl
  | none => rw [h1] at h; simp only [h]; rfl

theorem stWorld_dr_none {u : Unit} {p : (Dg lam × Dg lam) × ℕ} (h : drVal C b p = none) :
    (stWorld C Wd).answer (b.withS s) (.inr u) p =
      ((PMF.uniformOfFintype (Fin (nDg lam + 1))).map fun x =>
        (digE lam x, ({ b with loose := (p, digE lam x) :: b.loose } : Book S lam).withS s) :
            PMF ((stSpec S lam C).Rng (.inr u) × (stWorld C Wd).σ)) := by
  show ansDr C (b.withS s) p = _
  unfold drVal at h
  simp only [ansDr, Book.withS]
  cases h1 : b.loose.lookup p with
  | some r' => rw [h1] at h; cases h
  | none =>
    rw [h1] at h
    simp only [h]
    rw [← uniform_map_equiv (digE lam), PMF.map_comp]
    rfl

end Steps

/-! ## The reduction -/

/-- The reduction: the adversarial verifier over the first family, from the table b. A query for a
state: if the table has the answer of this query, the state in it, without a query; else one query
to the first family, whose answer is entered (at an unchanged oracle the answer itself comes back
and nothing is entered). An expansion query: what the table gives (`drVal`: its own earlier answer,
else the hash block of the oldest entered answer with this state that has such a hash block); else a
uniform hash block, which is stored. Coins and requests stay. -/
def downVSt :
    Gen.AdvVerifier (stSpec S lam C) X Pf → Book S lam → Gen.AdvVerifier S X Pf
  | .halt, _ => .halt
  | .sample n k, b => .sample n fun r => downVSt (k r) b
  | .request k, b => .request fun l => downVSt (k l) b
  | .query (.inl o) q k, b =>
      match b.kept C o q with
      | some r => downVSt (k ((C o).toAns r)) b
      | none => .query o q fun r => downVSt (k ((C o).toAns r)) (b.note C o q r)
  | .query (.inr _) p k, b =>
      match drVal C b p with
      | some r => downVSt (k r) b
      | none =>
        .sample (nDg lam) fun x =>
          downVSt (k (digE lam x)) { b with loose := (p, digE lam x) :: b.loose }

theorem queryBound_downVSt (V : Gen.AdvVerifier (stSpec S lam C) X Pf) :
    ∀ (b : Book S lam) (t : ℕ), V.QueryBound t → (downVSt C V b).QueryBound t := by
  induction V with
  | halt => intro _ _ _; trivial
  | sample n k ih => exact fun b t h r => ih r b t (h r)
  | request k ih => exact fun b t h l => ih l b t (h l)
  | query x q k ih =>
    intro b t h
    cases t with
    | zero => exact h.elim
    | succ t =>
      match x, q, k, ih, h with
      | .inl o, q, k, ih, h =>
        simp only [downVSt]
        cases b.kept C o q with
        | some r => exact advQueryBound_mono _ t (t + 1) (Nat.le_succ t) (ih _ b t (h _))
        | none => exact fun r => ih _ _ t (h _)
      | .inr u, p, k, ih, h =>
        simp only [downVSt]
        cases drVal C b p with
        | some r => exact advQueryBound_mono _ t (t + 1) (Nat.le_succ t) (ih _ b t (h _))
        | none => exact fun x => advQueryBound_mono _ t (t + 1) (Nat.le_succ t) (ih _ _ t (h _))

/-! ## The replay -/

/-- The replay: V is run again on a log l of the reduction; the result is the log over the second
family that V itself has seen. The reduction's own coins leave the list of coins and appear as
answers of dr. It stops where the log ends or does not fit V's next move. -/
def replaySt :
    Gen.AdvVerifier (stSpec S lam C) X Pf → ℕ → Book S lam → Log S X Pf → Log (stSpec S lam C) X Pf
  | .halt, _, _, _ => Log.nil
  | .sample mm k, n, b, l =>
      match l.coins with
      | [] => Log.nil
      | c :: cs =>
        if hc : c < mm + 1 then (Log.oneC c).app (replaySt (k ⟨c, hc⟩) n b { l with coins := cs })
        else Log.nil
  | .query (.inl o) q k, n, b, l =>
      match b.kept C o q with
      | some r => (Log.oneT (eI C o q ((C o).toAns r))).app (replaySt (k ((C o).toAns r)) n b l)
      | none =>
        match l.trace with
        | [] => Log.nil
        | e :: tr =>
          match findMade [e] o q with
          | some r =>
            (Log.oneT (eI C o q ((C o).toAns r))).app
              (replaySt (k ((C o).toAns r)) n (b.note C o q r) { l with trace := tr })
          | none => Log.nil
  | .query (.inr _) p k, n, b, l =>
      match drVal C b p with
      | some r => (Log.oneT (eD C p r)).app (replaySt (k r) n b l)
      | none =>
        match l.coins with
        | [] => Log.nil
        | c :: cs =>
          if hc : c < nDg lam + 1 then
            (Log.oneT (eD C p (digE lam ⟨c, hc⟩))).app
              (replaySt (k (digE lam ⟨c, hc⟩)) n
                { b with loose := (p, digE lam ⟨c, hc⟩) :: b.loose } { l with coins := cs })
          else Log.nil
  | .request _, 0, _, _ => Log.nil
  | .request k, n + 1, b, l =>
      match l.sessions with
      | [] => Log.nil
      | x :: xs => (Log.oneS x).app (replaySt (k x) n b { l with sessions := xs })

section ReplaySteps
variable (n : ℕ) (b : Book S lam) (l : Log S X Pf)

theorem replaySt_sample (mm : ℕ)
    (k : Fin (mm + 1) → Gen.AdvVerifier (stSpec S lam C) X Pf) (r : Fin (mm + 1)) :
    replaySt C (.sample mm k) n b ((Log.oneC r.val).app l) =
      (Log.oneC r.val).app (replaySt C (k r) n b l) := by
  simp only [replaySt, Log.app, Log.oneC, List.cons_append, List.nil_append,
    r.isLt, dif_pos, Fin.eta]

theorem replaySt_request (k : List (X × Pf) → Gen.AdvVerifier (stSpec S lam C) X Pf)
    (x : List (X × Pf)) :
    replaySt C (.request k) (n + 1) b ((Log.oneS x).app l) =
      (Log.oneS x).app (replaySt C (k x) n b l) := by
  simp only [replaySt, Log.app, Log.oneS, List.cons_append, List.nil_append]

theorem replaySt_inl_some {o : S.ι} {q : S.Dom o} {r : S.Rng o}
    (k : (C o).Ans → Gen.AdvVerifier (stSpec S lam C) X Pf) (h : b.kept C o q = some r) :
    replaySt C (.query (S := stSpec S lam C) (.inl o) q k) n b =
      fun l =>
        (Log.oneT (eI C o q ((C o).toAns r))).app (replaySt C (k ((C o).toAns r)) n b l) := by
  funext l
  simp only [replaySt, h]

theorem replaySt_inl_none {o : S.ι} {q : S.Dom o}
    (k : (C o).Ans → Gen.AdvVerifier (stSpec S lam C) X Pf)
    (h : b.kept C o q = none) (r : S.Rng o) :
    replaySt C (.query (S := stSpec S lam C) (.inl o) q k) n b ((Log.oneT ⟨o, q, r⟩).app l) =
      (Log.oneT (eI C o q ((C o).toAns r))).app
        (replaySt C (k ((C o).toAns r)) n (b.note C o q r) l) := by
  simp only [replaySt, h, Log.app, Log.oneT, List.cons_append, List.nil_append, findMade_self]

theorem replaySt_dr_some {u : Unit} {p : (Dg lam × Dg lam) × ℕ} {r : Dg lam}
    (k : Dg lam → Gen.AdvVerifier (stSpec S lam C) X Pf) (h : drVal C b p = some r) :
    replaySt C (.query (S := stSpec S lam C) (.inr u) p k) n b =
      fun l => (Log.oneT (eD C p r)).app (replaySt C (k r) n b l) := by
  funext l
  simp only [replaySt, h]

theorem replaySt_dr_none {u : Unit} {p : (Dg lam × Dg lam) × ℕ}
    (k : Dg lam → Gen.AdvVerifier (stSpec S lam C) X Pf)
    (h : drVal C b p = none) (x : Fin (nDg lam + 1)) :
    replaySt C (.query (S := stSpec S lam C) (.inr u) p k) n b ((Log.oneC x.val).app l) =
      (Log.oneT (eD C p (digE lam x))).app
        (replaySt C (k (digE lam x)) n { b with loose := (p, digE lam x) :: b.loose } l) := by
  simp only [replaySt, h, Log.app, Log.oneC, List.cons_append, List.nil_append,
    x.isLt, dif_pos, Fin.eta]

end ReplaySteps

/-! ## The replay lemma -/

theorem nil_trace (e : QA S) :
    ({ (Log.nil : Log S X Pf) with trace := (Log.nil : Log S X Pf).trace ++ [e] }) =
      (Log.oneT e).app Log.nil := rfl
theorem nil_coins (c : ℕ) :
    ({ (Log.nil : Log S X Pf) with coins := (Log.nil : Log S X Pf).coins ++ [c] }) =
      (Log.oneC c).app Log.nil := rfl
theorem nil_sessions (x : List (X × Pf)) :
    ({ (Log.nil : Log S X Pf) with sessions := (Log.nil : Log S X Pf).sessions ++ [x] }) =
      (Log.oneS x).app Log.nil := rfl

/-- The replay lemma, for every challenger Wd: the loop of V against `stWorld C Wd` is the image,
under the replay, of the loop of the reduction against Wd, with the environment applied to the
replayed log. An equality of distributions. -/
theorem loop_replaySt (Wd : GWorld S X W Pf) (V : Gen.AdvVerifier (stSpec S lam C) X Pf) :
    ∀ (Z : Log (stSpec S lam C) X Pf → Option (Gen.Batch X W)) (n : ℕ) (b : Book S lam) (s : Wd.σ),
      lLoop (stWorld C Wd) Z V n Log.nil (b.withS s) =
        (lLoop Wd (fun l => Z (replaySt C V n b l)) (downVSt C V b) n Log.nil s).map
          (replaySt C V n b) := by
  induction V with
  | halt => intro Z n b s; simp only [lLoop, downVSt, PMF.pure_map, replaySt]
  | sample mm k ih =>
    intro Z n b s
    simp only [lLoop, downVSt, PMF.map_bind]
    refine congrArg _ (funext fun r => ?_)
    rw [nil_coins, nil_coins, lLoop_shift, lLoop_shift, ih, PMF.map_comp, PMF.map_comp]
    simp only [replaySt_sample, Function.comp_def]
  | request k ih =>
    intro Z n b s
    cases n with
    | zero => simp only [lLoop, downVSt, PMF.pure_map, replaySt]
    | succ n =>
      have hnil : replaySt C (.request k) (n + 1) b (Log.nil : Log S X Pf) = Log.nil := rfl
      cases hz : Z Log.nil with
      | none => simp only [lLoop, downVSt, hnil, hz, PMF.pure_map]
      | some bt =>
        simp only [lLoop, downVSt, hnil, hz, PMF.map_bind]
        show ((Wd.serve s bt).map _).bind _ = _
        rw [PMF.bind_map]
        refine congrArg _ (funext fun out => ?_)
        simp only [Function.comp_def]
        rw [nil_sessions, nil_sessions, lLoop_shift, lLoop_shift]
        refine (congrArg (PMF.map _)
          (ih out.1 (fun l' => Z ((Log.oneS out.1).app l')) n b out.2)).trans ?_
        rw [PMF.map_comp, PMF.map_comp]
        simp only [replaySt_request, Function.comp_def]
  | query x q k ih =>
    intro Z n b s
    match x, q, k, ih with
    | .inl o, q, k, ih =>
      cases hk : b.kept C o q with
      | some r =>
        rw [replaySt_inl_some C n b k hk]
        simp only [lLoop, downVSt, hk]
        rw [stWorld_inl_some C Wd b s hk, PMF.pure_bind, nil_trace, lLoop_shift, ih, PMF.map_comp]
        rfl
      | none =>
        simp only [lLoop, downVSt, hk, PMF.map_bind]
        rw [stWorld_inl_none C Wd b s hk, PMF.bind_map]
        refine congrArg _ (funext fun out => ?_)
        simp only [Function.comp_def]
        rw [nil_trace, nil_trace, lLoop_shift, lLoop_shift, ih, PMF.map_comp, PMF.map_comp]
        simp only [replaySt_inl_none C n b _ k hk, Function.comp_def]
    | .inr u, p, k, ih =>
      cases h1 : drVal C b p with
      | some r =>
        rw [replaySt_dr_some C n b k h1]
        simp only [lLoop, downVSt, h1]
        rw [stWorld_dr_some C Wd b s h1, PMF.pure_bind, nil_trace, lLoop_shift, ih, PMF.map_comp]
        rfl
      | none =>
        simp only [lLoop, downVSt, h1, PMF.map_bind]
        rw [stWorld_dr_none C Wd b s h1, PMF.bind_map]
        refine congrArg _ (funext fun x => ?_)
        simp only [Function.comp_def]
        rw [nil_trace, nil_coins, lLoop_shift, lLoop_shift, ih, PMF.map_comp, PMF.map_comp]
        simp only [replaySt_dr_none C n b _ k h1, Function.comp_def]

end Rom
