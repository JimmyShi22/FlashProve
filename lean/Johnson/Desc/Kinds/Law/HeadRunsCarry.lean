-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadRunsCarry.lean: FOR THE PREMISE "HeadRuns hd Z" [not in this library] (every run of the head's two lists of adding carries): THE OUTPUT HEAD's TWO LISTS OF
NAMED RUNS (Johnson/Stored/HeadAddsAtS.lean: frontRuns | backRuns) BROUGHT DOWN TO THE BLOCKS THAT STATE THEM, AND K6's OWN FOUR RUNS PAID. GENERAL IN THE RELATION: P : S → S → Prop
is a letter (CF hd := CarriesFo S.fork? hd goes in its place; its text is not imported here).
  runs_from        every run of runsOf bs row is, under its name, a run that one of the blocks bs states.
  k6_same          K6's "norm" | "policy" | "logits" at the real seat: THE RECORD BEHIND IS THE RECORD IN FRONT.
  k6_join          K6's "join" (the lookup's joinRun at K6's key vectors): the record behind is the record in front WITH THE LEDGER ALONE TURNED: s.putFork (F.paid g.owedJoin), F the ledger in
                   front, g what the lookup heard: one owed claim is marked as added; nothing else.
  headRuns_carry   if P s s at every record · P s (s.putFork (F.paid g.owedJoin)) where s.fork? = some F, s.lookHeard? = some g · every run of the lookup's block as the head calls it (lookClaims
                   W l: "objects" · "guests" · "planes") has P · K11's run "the merge" has P: THEN every run of frontRuns W l and of backRuns W l has P.
WHAT IT IS NOT. Nothing on soundness: a frame's law. THE LOOKUP's RUNS AND K11's RUN ARE PREMISES: other files' texts (the lookup's: K3.block, withCaller, planesRun · K11's: headMergeClaim). That P holds of
"the ledger with one owed claim marked" is the caller's: it hangs on CarriesFo's letter.

-/
import Mathlib
import Johnson.Stored.HeadAddsAtS
import Johnson.Desc.Kinds.Law.Heard
import Johnson.Desc.Kinds.Law.JoinValue

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes.Model (Fork)
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.First (S)

theorem mapM_mem' {α β : Type} (f : α → Option β) : ∀ (l : List α) (l' : List β),
    l.mapM f = some l' → ∀ y, y ∈ l' → ∃ x, x ∈ l ∧ f x = some y
  | [], l', h, y, hy => by
    simp at h
    subst h
    simp at hy
  | a :: l, l', h, y, hy => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [ha, hl] at h
      | some bs =>
        simp [ha, hl] at h
        subst h
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact ⟨a, List.mem_cons_self, ha⟩
        · obtain ⟨x, hx, e⟩ := mapM_mem' f l bs hl y hy'
          exact ⟨x, List.mem_cons_of_mem _ hx, e⟩

/-- Every run of the list is, under its name, a run that one of the blocks states. -/
theorem runs_from (bs : List (Block S Claim)) (row : List (Nat × String)) (runs : List RunAtS)
    (h : runsOf bs row = some runs) (r : RunAtS) (hr : r ∈ runs) :
    ∃ (i : Nat) (b : Block S Claim), bs[i]? = some b ∧ b.claims.lookup r.1 = some r.2 := by
  obtain ⟨o, _, ho⟩ := mapM_mem' _ row runs h r hr
  obtain ⟨b, hb, hl⟩ := Option.bind_eq_some_iff.mp ho
  obtain ⟨run, hrun, rfl⟩ := Option.map_eq_some_iff.mp hl
  exact ⟨o.1, b, hb, hrun⟩

theorem lookup_mem {α : Type} : ∀ (l : List (String × α)) (n : String) (x : α),
    l.lookup n = some x → (n, x) ∈ l
  | [], _, _, h => by simp at h
  | (k, v) :: l, n, x, h => by
    rw [List.lookup_cons] at h
    split at h
    · rename_i hk
      obtain rfl := Option.some.inj h
      have : n = k := by simpa using hk
      subst this
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem l n x h)

/-- **K6's three runs of its own forms leave the record as it is**, at the real seat. -/
theorem k6_same (h : OnBytes.Model.Head.Shape) (iU3 l piece : Nat) (p : Par)
    (c : String × (Nat → S → Except String (List Claim × S)))
    (hc : c ∈ (kind asClaim (seatAt h iU3) l piece p).claims) (n : Nat) (s : S)
    (y : List Claim × S) (hy : c.2 n s = .ok y) : y.2 = s :=
  k6_runs_leave asClaim (seatAt h iU3) l piece p id (fun _ _ => rfl) c hc n s y hy

/-- **K6's "join" turns the ledger alone**: one owed claim is marked as added. -/
theorem k6_join (keys : S → Option (Array OnBytes.Model.Aff)) (n : Nat) (s : S)
    (y : List Claim × S) (hy : K3.joinRun (K3.seatCalls asClaim) keys n s = .ok y) :
    ∃ (F : Fork) (g : OnBytes.Model.Forest.Heard), s.fork? = some F ∧ s.lookHeard? = some g ∧
      y.2 = s.putFork (F.paid g.owedJoin) := by
  unfold K3.joinRun at hy
  simp only [bind, Except.bind] at hy
  cases hF : (K3.seatCalls asClaim).fork s with
  | none => simp [hF, named] at hy
  | some F =>
    cases hg : (K3.seatCalls asClaim).heard s with
    | none => simp [hF, hg, named] at hy
    | some g =>
      simp only [hF, hg, named] at hy
      split at hy
      · cases hy
      · split at hy
        · cases hy
        · rename_i KF hKF
          split at hy
          · cases hy
          · rename_i x hx
            have hx' : First.Look.joinF g KF F [] = some x := by
              cases hj : First.Look.joinF g KF F [] with
              | none => simp [hj] at hx
              | some x' =>
                simp [hj] at hx
                rw [hx]
            obtain ⟨_, hG, _, _⟩ := (Came.joinF_spec g KF F x.2.1 [] x.2.2 x.1).mp hx'
            have e := Except.ok.inj hy
            refine ⟨F, g, hF, hg, ?_⟩
            rw [← e, ← hG]
            rfl

section Carry

variable (P : S → S → Prop) (W : OnBytes.Model.Verify.Public) (l : Nat)

/-- A block's runs all have P. -/
def RunsHave (b : Block S Claim) : Prop :=
  ∀ c ∈ b.claims, ∀ n s y, c.2 n s = .ok y → P s y.2

theorem quiet_have (name : String) (i : Nat) :
    RunsHave P (roundlessBlock name 1 (some l) i .ok : Block S Claim) :=
  fun _ hc => nomatch hc

/-- K6's block with true claims: its four runs. -/
theorem k6_have (hrefl : ∀ s, P s s)
    (hjoin : ∀ s F g, s.fork? = some F → s.lookHeard? = some g →
      P s (s.putFork (F.paid g.owedJoin)))
    (b6 : Block S Claim) (hb : blockClaims W l = some b6) : RunsHave P b6 := by
  obtain ⟨iU3, _, rfl⟩ := Option.map_eq_some_iff.mp hb
  intro c hc n s y hy
  have hc' : c ∈ (kind asClaim (seatAt W.hS iU3) l 4 _).claims.take 1 ++
      [("join", K3.joinRun (K3.seatCalls asClaim) (callerKeys _ (seatAt W.hS iU3)))] ++
      (kind asClaim (seatAt W.hS iU3) l 4 _).claims.drop 1 := hc
  rcases List.mem_append.mp hc' with h | h
  · rcases List.mem_append.mp h with h | h
    · rw [k6_same W.hS iU3 l 4 _ c (List.mem_of_mem_take h) n s y hy]
      exact hrefl s
    · obtain rfl := List.mem_singleton.mp h
      obtain ⟨F, g, hF, hg, e⟩ := k6_join _ n s y hy
      rw [e]
      exact hjoin s F g hF hg
  · rw [k6_same W.hS iU3 l 4 _ c (List.mem_of_mem_drop h) n s y hy]
    exact hrefl s

/-- Every block of the segment, as far as the two steps call its runs. -/
theorem seg_have (hrefl : ∀ s, P s s)
    (hjoin : ∀ s F g, s.fork? = some F → s.lookHeard? = some g →
      P s (s.putFork (F.paid g.owedJoin)))
    (hlook : ∀ x, lookClaims W l = some x → RunsHave P x)
    (hmerge : ∀ n s y, Johnson.Desc.First.ForkMerge.headMergeClaim n s = .ok y → P s y.2)
    (bs : List (Block S Claim)) (hbs : segBlocks W l = some bs) : ∀ b ∈ bs, RunsHave P b := by
  obtain ⟨b6, hb6, rfl⟩ := Option.map_eq_some_iff.mp hbs
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact quiet_have P l _ _
  · exact quiet_have P l _ _
  · cases hx : lookClaims W l with
    | none => exact quiet_have P l _ _
    | some x => exact hlook x hx
  · exact k6_have P W l hrefl hjoin _ hb6
  · exact quiet_have P l _ _
  · exact quiet_have P l _ _
  · exact quiet_have P l _ _
  · exact quiet_have P l _ _
  · intro c hc n s y hy
    obtain rfl := List.mem_singleton.mp (show c ∈ [("the merge",
      Johnson.Desc.First.ForkMerge.headMergeClaim)] from hc)
    exact hmerge n s y hy

/-- **THE HEAD's TWO LISTS CARRY**, as RunsCarry (not in this repository), the relation a letter. -/
theorem headRuns_carry (hrefl : ∀ s, P s s)
    (hjoin : ∀ s F g, s.fork? = some F → s.lookHeard? = some g →
      P s (s.putFork (F.paid g.owedJoin)))
    (hlook : ∀ x, lookClaims W l = some x → RunsHave P x)
    (hmerge : ∀ n s y, Johnson.Desc.First.ForkMerge.headMergeClaim n s = .ok y → P s y.2)
    (runs : List RunAtS) (h : frontRuns W l = some runs ∨ backRuns W l = some runs) :
    ∀ r ∈ runs, ∀ n s cl s', r.2 n s = .ok (cl, s') → P s s' := by
  intro r hr n s cl s' hrun
  have key : ∃ bs row, segBlocks W l = some bs ∧ runsOf bs row = some runs := by
    rcases h with h | h
    · obtain ⟨bs, hbs, hro⟩ := Option.bind_eq_some_iff.mp h
      exact ⟨bs, _, hbs, hro⟩
    · obtain ⟨bs, hbs, hro⟩ := Option.bind_eq_some_iff.mp h
      exact ⟨bs, _, hbs, hro⟩
  obtain ⟨bs, row, hbs, hro⟩ := key
  obtain ⟨i, b, hb, hl⟩ := runs_from bs row runs hro r hr
  exact seg_have P W l hrefl hjoin hlook hmerge bs hbs b (List.mem_of_getElem? hb) (r.1, r.2)
    (lookup_mem _ _ _ hl) n s (cl, s') hrun

end Carry

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6_same
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6_join
#print axioms VerifiableInference.Desc.Kinds.Head.Law.headRuns_carry
