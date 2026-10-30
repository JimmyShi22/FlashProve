-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/Gather.lean
(kind K9's soundness lemma): THEOREM: THE PREMISE ON A FUNCTION OF CLAIMS (AddOk,
Law/Moves.lean) AT THE GATHERING OF A STEP OF ADDING (Batch/Objects.lean: gather ws cut runs), FROM
A PREMISE ON EACH RUN OF ITS LIST.
  RunOk       the premise on one run. The gathering hands a run the number "front" of claims
              gathered so far IN THIS CALL; the law numbers the claims through: so a run's claims
              are numbered from THE LEDGER's COUNT PLUS front on. At every fixed part q and every
              state that goes on from q (Fx, Law/Moves.lean) and is good in the other kinds' eyes,
              whatever its ledger's sums: the run leaves the ledger's core and the arrays' frame
              (treesFrame: all that the arrays hold but the weights' values) alone, keeps "good" and
              "goes on from q", is "more", makes len q claims, and, WHERE ITS CLAIMS CAN BE ADDED AT
              ALL (behind any list of "front" claims, to any ledger with the same core and frame),
              the sum of its claims with their weights, read at any full later state, is the
              polynomial tm at q.
  TermedRun, termsRuns, lenRuns   a run with its terms; the terms and the number of a list of runs.
  gstep, gather_eq, gstep_ok      one step of the gathering's fold (its text, named).
  gather_addOk   **AddOk at gather ws cut (the runs), with the terms and the number of the list.**
The windows' test (K9.window) is passed by: nothing is made of it.
Not claimed: RunOk of any real run.

-/
import Johnson.Desc.First.Batch.Objects
import Johnson.Desc.First.Batch.Law.Moves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Lens Where gather RunOf Window windowsOk)

variable {T P K : Type}

/-- A run with its terms. -/
structure TermedRun (T P K : Type) where
  run : RunOf T
  tm : ℕ → P → Bound K → List (ℕ × K)
  len : P → ℕ

/-- The terms of a list of runs, if n claims stand before. -/
def termsRuns (p : P) (y : Bound K) : List (TermedRun T P K) → ℕ → List (ℕ × K)
  | [], _ => []
  | r :: l, n => r.tm n p y ++ termsRuns p y l (n + r.len p)

/-- Their number of claims. -/
def lenRuns (p : P) : List (TermedRun T P K) → ℕ
  | [] => 0
  | r :: l => r.len p + lenRuns p l

/-- One step of the gathering's fold. -/
def gstep (ws : T → List Window) (cut : List (Nat × String)) (x : List Claim × T) (r : RunOf T) :
    Except String (List Claim × T) :=
  let who := (cut.find? fun o => o.2 == r.1).getD (0, r.1)
  match (r.2 x.1.length x.2).bind fun y => (windowsOk (ws x.2) who y.1).map fun _ => y with
  | .ok y => .ok (x.1 ++ y.1, y.2)
  | .error e => .error (r.1 ++ ": " ++ e)

theorem gather_eq (ws : T → List Window) (cut : List (Nat × String)) (runs : List (RunOf T))
    (t : T) : gather ws cut runs t = runs.foldlM (gstep ws cut) ([], t) := rfl

theorem gstep_ok {ws : T → List Window} {cut : List (Nat × String)} {x x' : List Claim × T}
    {r : RunOf T} (h : gstep ws cut x r = .ok x') :
    ∃ c e, r.2 x.1.length x.2 = .ok (c, e) ∧ x' = (x.1 ++ c, e) := by
  unfold gstep at h
  simp only [] at h
  split at h
  · rename_i y hy
    cases hr : r.2 x.1.length x.2 with
    | error e =>
      rw [hr] at hy
      exact nomatch hy
    | ok z =>
      rw [hr] at hy
      have hy' : (windowsOk (ws x.2) ((cut.find? fun o => o.2 == r.1).getD (0, r.1)) z.1).map
        (fun _ => z) = .ok y := hy
      cases hw : windowsOk (ws x.2) ((cut.find? fun o => o.2 == r.1).getD (0, r.1)) z.1 with
      | error e =>
        rw [hw] at hy'
        exact nomatch hy'
      | ok u =>
        rw [hw] at hy'
        have e : z = y := Except.ok.inj hy'
        subst e
        exact ⟨z.1, z.2, rfl, (Except.ok.inj h).symm⟩
  · exact nomatch h

variable [Field K] (ρ : Reading K) (X : Lens T) (O : Others T P K) (Fx : P → T → Prop)

/-- The premise on one run. -/
def RunOk (r : Nat → T → Except String (List Claim × T)) (tm : ℕ → P → Bound K → List (ℕ × K))
    (len : P → ℕ) : Prop :=
  ∀ q front e a c e₁, Fx q e → O.good e → X.get? e = some a → a.F.LS.size = a.F.ns →
    r front e = .ok (c, e₁) →
    ∃ a₁, X.get? e₁ = some a₁ ∧ core a₁.F = core a.F ∧
      treesFrame a₁.F.trees = treesFrame a.F.trees ∧ O.good e₁ ∧ O.more e e₁ ∧
      Fx q e₁ ∧ c.length = len q ∧
      ∀ pre A₀ G, pre.length = front → core A₀ = core a₁.F →
        treesFrame A₀.trees = treesFrame a₁.F.trees → addAll A₀ (pre ++ c) = some G →
      ∀ t y, laterK X O e₁ t → O.full t →
        wsumK X ρ t y (ρ.val a.F.theta) (a.F.nClaim + front) c =
          termsAt K (tm (a.F.nClaim + front) q y) (ρ.val a.F.theta)

theorem gather_fold (p : Where) (H : FitsM X O Fx p) (ws : T → List Window)
    (cut : List (Nat × String)) (q : P) :
    ∀ (rl : List (TermedRun T P K)), (∀ r ∈ rl, RunOk ρ X O Fx r.run.2 r.tm r.len) →
      ∀ (x out : List Claim × T) (a : K9.Part), Fx q x.2 → O.good x.2 → X.get? x.2 = some a →
      a.F.LS.size = a.F.ns → (rl.map (·.run)).foldlM (gstep ws cut) x = .ok out →
      ∃ c a₁, out.1 = x.1 ++ c ∧ X.get? out.2 = some a₁ ∧ core a₁.F = core a.F ∧
        treesFrame a₁.F.trees = treesFrame a.F.trees ∧ O.good out.2 ∧
        O.more x.2 out.2 ∧ Fx q out.2 ∧ c.length = lenRuns q rl ∧
        ∀ pre A₀ G, pre.length = x.1.length → core A₀ = core a₁.F →
          treesFrame A₀.trees = treesFrame a₁.F.trees → addAll A₀ (pre ++ c) = some G →
        ∀ t y, laterK X O out.2 t → O.full t →
          wsumK X ρ t y (ρ.val a.F.theta) (a.F.nClaim + x.1.length) c =
            termsAt K (termsRuns q y rl (a.F.nClaim + x.1.length)) (ρ.val a.F.theta)
  | [], _, x, out, a, hf, hg, ha, _, h => by
    have e : x = out := Except.ok.inj h
    subst e
    exact ⟨[], a, by simp, ha, rfl, rfl, hg, H.moreRefl _, hf, rfl, fun _ _ _ _ _ _ _ t y _ _ => by
      simp [wsumK, termsRuns, termsAt]⟩
  | r :: l, hr, x, out, a, hf, hg, ha, hs, h => by
    rw [List.map_cons, List.foldlM_cons] at h
    obtain ⟨x', hx', h'⟩ := ok_bind h
    obtain ⟨c, e, hc, rfl⟩ := gstep_ok hx'
    obtain ⟨a₁, ha₁, k, w1, g1, m1, f1, l1, s1⟩ :=
      hr r List.mem_cons_self q x.1.length x.2 a c e hf hg ha hs hc
    obtain ⟨_, k2, k3, k4, k5, k6⟩ := core_parts k
    obtain ⟨c', a₂, o1, ha₂, k', w2, g2, m2, f2, l2, s2⟩ :=
      gather_fold p H ws cut q l (fun z hz => hr z (List.mem_cons_of_mem _ hz)) (x.1 ++ c, e) out
        a₁ f1 g1 ha₁ (by rw [k5, k6]; exact hs) h'
    obtain ⟨_, j2, _, j4, _, _⟩ := core_parts k'
    refine ⟨c ++ c', a₂, by rw [o1, List.append_assoc], ha₂, k'.trans k, w2.trans w1, g2,
      H.moreTrans _ _ _ m1 m2, f2, ?_, fun pre A₀ G hn hc hw hA t y ht hf => ?_⟩
    · rw [List.length_append, l1, l2]
      rfl
    · have hl : laterK X O e t := by
        refine ⟨?_, H.moreTrans _ _ _ m2 ht.2.1, ?_⟩
        · rw [← ht.1]
          simp only [planOf, ha₁, ha₂, Option.map_some, j4]
        · rw [← ht.2.2]
          simp only [thetaOf, ha₁, ha₂, Option.map_some, j2]
      have hA' : addAll A₀ ((pre ++ c) ++ c') = some G := by rw [List.append_assoc]; exact hA
      obtain ⟨G₁, hG₁, _⟩ := addAll_front A₀ G (pre ++ c) c' hA'
      have q2 := s2 (pre ++ c) A₀ G (by simp [hn]) hc hw hA' t y ht hf
      simp only [List.length_append] at q2
      rw [k2, k3, ← Nat.add_assoc, l1] at q2
      rw [wsumK_append, s1 pre A₀ G₁ hn (hc.trans k') (hw.trans w2) hG₁ t y hl hf, l1, q2,
        termsRuns, termsAt_append]

/-- **The gathering meets the premise on a function of claims.** -/
theorem gather_addOk (p : Where) (H : FitsM X O Fx p) (ws : T → List Window)
    (cut : List (Nat × String)) (rl : List (TermedRun T P K))
    (hr : ∀ r ∈ rl, RunOk ρ X O Fx r.run.2 r.tm r.len) :
    AddOk ρ X O Fx (gather ws cut (rl.map (·.run))) (fun n q y => termsRuns q y rl n)
      (fun q => lenRuns q rl) := by
  intro q e a c e₁ hf hg ha hs h
  rw [gather_eq] at h
  obtain ⟨c', a₁, o1, ha₁, k, _, g1, m1, f1, l1, s1⟩ :=
    gather_fold ρ X O Fx p H ws cut q rl hr ([], e) (c, e₁) a hf hg ha hs h
  have ec : c = c' := by simpa using o1
  subst ec
  exact ⟨a₁, ha₁, k, g1, m1, f1, l1, fun A₀ G hc hw hA t y ht hf => by
    simpa using s1 [] A₀ G rfl hc hw hA t y ht hf⟩

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.gstep_ok
#print axioms VerifiableInference.Desc.K9L.gather_fold
#print axioms VerifiableInference.Desc.K9L.gather_addOk
