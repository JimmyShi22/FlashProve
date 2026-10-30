-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoKeyFormRun.lean.
What a run of Head.keyForm returns.

States:
  keyForm_ok: if a run of Head.keyForm for call q returns the form v, then v is the sum of: the
    padding key times the weight of the columns that no segment lists; the slot of the stream's
    sumcheck, if q is R.x.qN, the number that the run holds for the call with the segment NF; and
    the forms that Head.LINE returns, from the same state and context, for the call's segments in
    their order. The columns that no segment lists are read off the marks that Head.markColumns
    leaves.
Not claimed: that any run of Head.keyForm returns. Nor is it claimed that call R.x.qN has the
segment NF. Nothing is said of the counts (laid) that keyForm returns, nor of the state and the
context that it leaves.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoStillH

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

/-- The weight of the columns that no segment lists. -/
def padWOf (e : Array E) (weighed : Array ℕ) (J : ℕ) : E :=
  (List.range' 0 J 1).foldl
    (fun p j => if weighed.getD j 0 == 0 then addE p (e.getD j zeroE) else p) zeroE

theorem getAsL_ok {α : Type} (name : String) (x : Option α) (F : Fork) (c : Ctx)
    (r : (α × Fork) × Ctx) (h : (liftM (Head.getAs name x) : SubM α) F c = .ok r) :
    ∃ a, x = some a ∧ r = ((a, F), c) := by
  obtain ⟨a, c1, h1, rfl⟩ := (lift_ok (Head.getAs name x) F c r).1 h
  cases x with
  | none =>
    have e : (Except.error { name := name } : Except Failure (α × Ctx)) = .ok (a, c1) := h1
    cases e
  | some b =>
    have e : (b, c) = (a, c1) := Except.ok.inj h1
    cases e
    exact ⟨_, rfl, rfl⟩

theorem thenPure_ok {α : Type} (a : α) (F : Fork) (c : Ctx) (out : (α × Fork) × Ctx)
    (h : ((pure PUnit.unit : SubM PUnit) >>= fun _ => pure a) F c = .ok out) :
    out = ((a, F), c) := by
  rw [bind_ok] at h
  obtain ⟨_, G, d, k1, k2⟩ := h
  have e := (pure_ok _ _ _ _).1 k1
  have t1 : G = F := congrArg (fun x : (PUnit × Fork) × Ctx => x.1.2) e
  have t2 : d = c := congrArg (fun x : (PUnit × Fork) × Ctx => x.2) e
  rw [t1, t2] at k2
  exact (pure_ok _ _ _ _).1 k2

theorem mustThen_ok {α : Type} (name : String) (b : Bool) (a : α) (F : Fork) (c : Ctx)
    (out : (α × Fork) × Ctx)
    (h : ((liftM (mustAs name b) : SubM Unit) >>= fun _ =>
      (pure PUnit.unit : SubM PUnit) >>= fun _ => pure a) F c = .ok out) :
    out = ((a, F), c) := by
  rw [bind_ok] at h
  obtain ⟨_, G, d, k1, k2⟩ := h
  obtain ⟨_, e⟩ := (mustAs_ok _ _ F c _).1 k1
  have t1 : G = F := congrArg (fun x : (Unit × Fork) × Ctx => x.1.2) e
  have t2 : d = c := congrArg (fun x : (Unit × Fork) × Ctx => x.2) e
  rw [t1, t2] at k2
  exact thenPure_ok a F c out k2

theorem lines_ok (R : Head.Run) (F : Fork) (c : Ctx)
    (body : Seg → MProd Aff (Array ℕ) → SubM (ForInStep (MProd Aff (Array ℕ))))
    (hb : ∀ g s out, body g s F c = .ok out → ∃ a w,
      Head.LINE R g.name F c = .ok ((a, F), c) ∧ Head.markColumns R s.snd g = some w ∧
        out = ((ForInStep.yield ⟨s.fst + a, w⟩, F), c)) :
    ∀ (l : List Seg) (s : MProd Aff (Array ℕ)) (out),
      (forIn l s body) F c = .ok out → out.1.2 = F ∧ out.2 = c ∧
        ∃ ls : List Aff, List.Forall₂ (fun g a => Head.LINE R g.name F c = .ok ((a, F), c)) l ls ∧
          out.1.1.fst = ls.foldl (· + ·) s.fst ∧
          l.foldlM (Head.markColumns R) s.snd = some out.1.1.snd
  | [], s, out, h => by
    rw [List.forIn_nil] at h
    rw [(pure_ok s F c out).1 h]
    exact ⟨rfl, rfl, [], .nil, rfl, rfl⟩
  | g :: l, s, out, h => by
    rw [List.forIn_cons, bind_ok] at h
    obtain ⟨st, G, c1, h1, h2⟩ := h
    obtain ⟨a, w, k1, k2, e⟩ := hb g s _ h1
    have e1 : st = ForInStep.yield ⟨s.fst + a, w⟩ :=
      congrArg (fun x : (ForInStep (MProd Aff (Array ℕ)) × Fork) × Ctx => x.1.1) e
    have e2 : G = F :=
      congrArg (fun x : (ForInStep (MProd Aff (Array ℕ)) × Fork) × Ctx => x.1.2) e
    have e3 : c1 = c :=
      congrArg (fun x : (ForInStep (MProd Aff (Array ℕ)) × Fork) × Ctx => x.2) e
    rw [e1, e2, e3] at h2
    obtain ⟨a1, a2, ls, b1, b2, b3⟩ := lines_ok R F c body hb l ⟨s.fst + a, w⟩ out h2
    refine ⟨a1, a2, a :: ls, .cons k1 b1, b2, ?_⟩
    rw [List.foldlM_cons, k2]
    exact b3

theorem pads_ok (F : Fork) (c : Ctx) (e : Array E) (weighed : Array ℕ)
    (body : ℕ → MProd (Array ℕ) E → SubM (ForInStep (MProd (Array ℕ) E)))
    (hb : ∀ j s out, body j s F c = .ok out → ∃ laid1,
      out = ((ForInStep.yield ⟨laid1,
        if weighed.getD j 0 == 0 then addE s.snd (e.getD j zeroE) else s.snd⟩, F), c)) :
    ∀ (l : List ℕ) (s : MProd (Array ℕ) E) (out),
      (forIn l s body) F c = .ok out → out.1.2 = F ∧ out.2 = c ∧
        out.1.1.snd = l.foldl
          (fun p j => if weighed.getD j 0 == 0 then addE p (e.getD j zeroE) else p) s.snd
  | [], s, out, h => by
    rw [List.forIn_nil] at h
    rw [(pure_ok s F c out).1 h]
    exact ⟨rfl, rfl, rfl⟩
  | j :: l, s, out, h => by
    rw [List.forIn_cons, bind_ok] at h
    obtain ⟨st, G, c1, h1, h2⟩ := h
    obtain ⟨laid1, e0⟩ := hb j s _ h1
    have e1 : st = _ :=
      congrArg (fun x : (ForInStep (MProd (Array ℕ) E) × Fork) × Ctx => x.1.1) e0
    have e2 : G = F :=
      congrArg (fun x : (ForInStep (MProd (Array ℕ) E) × Fork) × Ctx => x.1.2) e0
    have e3 : c1 = c :=
      congrArg (fun x : (ForInStep (MProd (Array ℕ) E) × Fork) × Ctx => x.2) e0
    rw [e1, e2, e3] at h2
    exact pads_ok F c e weighed body hb l _ out h2

/-- **What a run of Head.keyForm returns.** -/
theorem keyForm_ok (R : Head.Run) (q : ℕ) (laid laid' : Array ℕ) (F G : Fork) (c c' : Ctx)
    (v : Aff) (h : Head.keyForm R q laid F c = .ok (((v, laid'), G), c')) :
    ∃ (ls : List Aff) (weighed : Array ℕ),
      List.Forall₂ (fun g a => Head.LINE R g.name F c = .ok ((a, F), c))
        (R.L.calls.getD q default).segs ls ∧
      (R.L.calls.getD q default).segs.foldlM (Head.markColumns R)
        (Array.replicate (R.L.calls.getD q default).J 0) = some weighed ∧
      v = (if q == R.x.qN then
          Aff.ofConst (scaleE ((R.L.cl.getD q default).tauAt (R.L.cl.getD q default).t0)
            (padWOf (eqTab (Head.zjOf R.L R.x.g1 q)) weighed (R.L.calls.getD q default).J)) +
            Head.S_ R.x.tN.sCl
        else
          Aff.ofConst (scaleE ((R.L.cl.getD q default).tauAt (R.L.cl.getD q default).t0)
            (padWOf (eqTab (Head.zjOf R.L R.x.g1 q)) weighed (R.L.calls.getD q default).J))) +
        ls.foldl (· + ·) {} := by
  unfold Head.keyForm at h
  dsimp only at h
  rw [bind_ok] at h
  obtain ⟨⟨lines, weighed⟩, F1, c1, h1, h⟩ := h
  obtain ⟨a1, a2, ls, b1, b2, b3⟩ := lines_ok R F c _ (fun g s out ho => by
    rw [bind_ok] at ho
    obtain ⟨a, G1, d1, k1, k2⟩ := ho
    obtain ⟨s1, s2⟩ := still_LINE R g.name F c _ k1
    have s1' : G1 = F := s1
    have s2' : d1 = c := s2
    rw [s1', s2'] at k1 k2
    rw [bind_ok] at k2
    obtain ⟨w, G2, d2, k3, k4⟩ := k2
    obtain ⟨w', m1, m2⟩ := getAsL_ok _ _ F c _ k3
    have n1 : w = w' := congrArg (fun x : (Array ℕ × Fork) × Ctx => x.1.1) m2
    have n2 : G2 = F := congrArg (fun x : (Array ℕ × Fork) × Ctx => x.1.2) m2
    have n3 : d2 = c := congrArg (fun x : (Array ℕ × Fork) × Ctx => x.2) m2
    rw [n2, n3] at k4
    exact ⟨a, w, k1, n1 ▸ m1, thenPure_ok _ F c out k4⟩) _ _ _ h1
  have a1' : F1 = F := a1
  have a2' : c1 = c := a2
  have b2' : lines = ls.foldl (· + ·) {} := b2
  have b3' : (R.L.calls.getD q default).segs.foldlM (Head.markColumns R)
      (Array.replicate (R.L.calls.getD q default).J 0) = some weighed := b3
  rw [a1', a2', bind_ok] at h
  obtain ⟨⟨laid2, padW⟩, F2, c2, h2, h⟩ := h
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h2
  obtain ⟨p1, p2, p3⟩ := pads_ok F c (eqTab (Head.zjOf R.L R.x.g1 q)) weighed _
    (fun j s out ho => by
      dsimp only at ho
      by_cases w0 : (weighed.getD j 0 == 0) = true
      · rw [if_pos w0] at ho ⊢
        rw [bind_ok] at ho
        obtain ⟨_, G3, d3, k1, k2⟩ := ho
        have e := (pure_ok _ _ _ _).1 k1
        have t1 : G3 = F := congrArg (fun x : (PUnit × Fork) × Ctx => x.1.2) e
        have t2 : d3 = c := congrArg (fun x : (PUnit × Fork) × Ctx => x.2) e
        rw [t1, t2] at k2
        by_cases w1 : (weighed.getD j 0 != 1) = true
        · rw [if_pos w1] at k2
          exact ⟨_, mustThen_ok _ _ _ F c out k2⟩
        · rw [if_neg w1] at k2
          exact ⟨_, thenPure_ok _ F c out k2⟩
      · rw [if_neg w0] at ho ⊢
        rw [bind_ok] at ho
        obtain ⟨_, G3, d3, k1, k2⟩ := ho
        have e := (pure_ok _ _ _ _).1 k1
        have t1 : G3 = F := congrArg (fun x : (PUnit × Fork) × Ctx => x.1.2) e
        have t2 : d3 = c := congrArg (fun x : (PUnit × Fork) × Ctx => x.2) e
        rw [t1, t2] at k2
        by_cases w1 : (weighed.getD j 0 != 1) = true
        · rw [if_pos w1] at k2
          exact ⟨_, mustThen_ok _ _ _ F c out k2⟩
        · rw [if_neg w1] at k2
          exact ⟨_, thenPure_ok _ F c out k2⟩) _ _ _ h2
  have p3' : padW = padWOf (eqTab (Head.zjOf R.L R.x.g1 q)) weighed
      (R.L.calls.getD q default).J := by
    have : padW = _ := p3
    rw [this]
    unfold padWOf
    simp [Std.Legacy.Range.size]
  have e9 := (pure_ok _ _ _ _).1 h
  have v1 : v = _ := congrArg (fun x : ((Aff × Array ℕ) × Fork) × Ctx => x.1.1.1) e9
  refine ⟨ls, weighed, b1, b3', ?_⟩
  rw [v1, ← p3', ← b2']

end Fo
