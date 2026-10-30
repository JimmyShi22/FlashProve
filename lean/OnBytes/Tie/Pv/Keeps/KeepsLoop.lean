-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Keeps/KeepsLoop.lean: loops, for the tactics of OnBytes/Tie/Pv/Keeps/KeepsPeel.lean:
after a peel a loop is one call, r_i : Runs (forIn …) …. Here are the laws that take it apart,
general in the layer (a block, a routine of a sub-proof, of a link), with "no dry run" carried
forward and "no mark" carried backward.

 1. RunFold step l b s b' s': the runs of a loop's body over the list l, each from the value and the
    state that the one before has left; step a b s b1 s1 is what is said of one of them. It is
    Slice.RunFold (OnBytes/Slice/BlkSendRun.lean, for a block) with the whole state as one letter.
 2. runs_forIn (a list), runs_forIn_array, runs_forIn_range: if each run of the body goes on (yield)
    and has the property step, a success of the loop is a RunFold. The hypothesis on the body is
    asked only on a view, and with "no mark at the very end ⟹ none behind this run of the body".
 3. runs_forIn_inv: an invariant, also for a body that may break off.
 4. RunFold.split: the runs cut at member number j: those before it, from the loop's own start; the
    run at it; those behind it, to the loop's own end.
 5. Laws on LinkM's own tests (LinkM.must, mustAs, testAs) and on LinkM.call, SubM.change.
 6. An example: rootInH (OnBytes/Model/Trees.lean), whole, with its loop.
For a routine that calls itself there is no law: take the routine's own induction, and peel in the
step (so runLinksFrom_chain, OnBytes/Tie/Pv/Keeps/KeepsChain.lean).

Limits: one direction: from a success.
-/
import OnBytes.Tie.Pv.Keeps.KeepsPeel
import OnBytes.Tie.Pv.Keeps.KeepsModel

namespace OnBytes.L5

open OnBytes OnBytes.Model

/-- The runs of a loop's body over a list, each from what the one before has left. -/
def RunFold {S α β : Type} (step : α → β → S → β → S → Prop) : List α → β → S → β → S → Prop
  | [], b, s, b', s' => b' = b ∧ s' = s
  | a :: l, b, s, b', s' => ∃ b1 s1, step a b s b1 s1 ∧ RunFold step l b1 s1 b' s'

/-- What a step of a loop hands on. -/
def handsOn {β : Type} : ForInStep β → β
  | .done b => b
  | .yield b => b

section Loops

variable {m : Type → Type} [Monad m] [HasKeeps m] [HasRuns m] [RunsKeep m] {α β : Type}

/-- A loop over a list whose body always goes on. sEnd: the state at the very end of the run in
which the loop stands. -/
theorem runs_forIn (f : α → β → m (ForInStep β)) [∀ a b, KeepsM (f a b)]
    (step : α → β → HasRuns.St m → β → HasRuns.St m → Prop) (sEnd : HasRuns.St m)
    (hf : ∀ a b s r s1, View s → (Clean sEnd → Clean s1) → Runs (f a b) s r s1 →
      ∃ b1, r = .yield b1 ∧ step a b s b1 s1) :
    ∀ (l : List α) (b : β) (s : HasRuns.St m) (b' : β) (s' : HasRuns.St m), View s →
      (Clean sEnd → Clean s') → Runs (forIn l b f) s b' s' → RunFold step l b s b' s'
  | [], b, s, b', s', _, _, h => by
    rw [List.forIn_nil] at h
    exact HasRuns.runs_pure h
  | a :: l, b, s, b', s', d, B, h => by
    rw [List.forIn_cons] at h
    obtain ⟨r, s1, h1, d1, h2⟩ := OnBytes.L5.step h d
    cases r with
    | done b1 =>
      obtain ⟨-, e⟩ := HasRuns.runs_pure h2
      obtain ⟨b2, e2, -⟩ := hf a b s _ s1 d (fun k => e ▸ B k) h1
      cases e2
    | yield b1 =>
      have B1 : Clean sEnd → Clean s1 := fun k => runs_clean (x := forIn l b1 f) h2 (B k)
      obtain ⟨b2, e2, hs⟩ := hf a b s _ s1 d B1 h1
      cases e2
      exact ⟨b1, s1, hs, runs_forIn f step sEnd hf l b1 s1 b' s' d1 B h2⟩

/-- The same for a loop over an array. -/
theorem runs_forIn_array (f : α → β → m (ForInStep β)) [∀ a b, KeepsM (f a b)]
    (step : α → β → HasRuns.St m → β → HasRuns.St m → Prop) (sEnd : HasRuns.St m)
    (hf : ∀ a b s r s1, View s → (Clean sEnd → Clean s1) → Runs (f a b) s r s1 →
      ∃ b1, r = .yield b1 ∧ step a b s b1 s1)
    (l : Array α) (b : β) (s : HasRuns.St m) (b' : β) (s' : HasRuns.St m) (d : View s)
    (B : Clean sEnd → Clean s') (h : Runs (forIn l b f) s b' s') :
    RunFold step l.toList b s b' s' := by
  rw [← Array.forIn_toList] at h
  exact runs_forIn f step sEnd hf l.toList b s b' s' d B h

/-- The same for a loop over a range [start : stop : step]. -/
theorem runs_forIn_range (f : Nat → β → m (ForInStep β)) [∀ a b, KeepsM (f a b)]
    (step : Nat → β → HasRuns.St m → β → HasRuns.St m → Prop) (sEnd : HasRuns.St m)
    (hf : ∀ a b s r s1, View s → (Clean sEnd → Clean s1) → Runs (f a b) s r s1 →
      ∃ b1, r = .yield b1 ∧ step a b s b1 s1)
    (r : Std.Legacy.Range) (b : β) (s : HasRuns.St m) (b' : β) (s' : HasRuns.St m) (d : View s)
    (B : Clean sEnd → Clean s') (h : Runs (forIn r b f) s b' s') :
    RunFold step (List.range' r.start r.size r.step) b s b' s' := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  exact runs_forIn f step sEnd hf _ b s b' s' d B h

/-- An invariant of a loop, also where the body may break off. -/
theorem runs_forIn_inv (f : α → β → m (ForInStep β)) [∀ a b, KeepsM (f a b)]
    (I : β → HasRuns.St m → Prop) (sEnd : HasRuns.St m) :
    ∀ (l : List α) (b : β) (s : HasRuns.St m) (b' : β) (s' : HasRuns.St m),
      (∀ a ∈ l, ∀ b s r s1, I b s → View s → (Clean sEnd → Clean s1) → Runs (f a b) s r s1 →
        I (handsOn r) s1) →
      I b s → View s → (Clean sEnd → Clean s') → Runs (forIn l b f) s b' s' → I b' s'
  | [], b, s, b', s', _, h0, _, _, h => by
    rw [List.forIn_nil] at h
    obtain ⟨e1, e2⟩ := HasRuns.runs_pure h
    rw [e1, e2]
    exact h0
  | a :: l, b, s, b', s', hf, h0, d, B, h => by
    rw [List.forIn_cons] at h
    obtain ⟨r, s1, h1, d1, h2⟩ := OnBytes.L5.step h d
    cases r with
    | done b1 =>
      obtain ⟨e1, e2⟩ := HasRuns.runs_pure h2
      rw [e1, e2]
      exact hf a List.mem_cons_self b s _ s1 h0 d (fun k => e2 ▸ B k) h1
    | yield b1 =>
      have B1 : Clean sEnd → Clean s1 := fun k => runs_clean (x := forIn l b1 f) h2 (B k)
      exact runs_forIn_inv f I sEnd l b1 s1 b' s'
        (fun a' ha' => hf a' (List.mem_cons_of_mem _ ha'))
        (hf a List.mem_cons_self b s _ s1 h0 d B1 h1) d1 B h2

end Loops

/-- The runs cut at member number j: before it, at it, behind it. -/
theorem RunFold.split {S α β : Type} {step : α → β → S → β → S → Prop} :
    ∀ {l : List α} {b : β} {s : S} {b' : β} {s' : S}, RunFold step l b s b' s' →
      ∀ (j : Nat) (a : α), l[j]? = some a → ∃ b0 s0 b1 s1,
        RunFold step (l.take j) b s b0 s0 ∧ step a b0 s0 b1 s1 ∧
        RunFold step (l.drop (j + 1)) b1 s1 b' s'
  | [], _, _, _, _, _, _, _, hj => by cases hj
  | x :: l, b, s, b', s', h, j, a, hj => by
    obtain ⟨b1, s1, h1, h2⟩ := h
    cases j with
    | zero =>
      have e : x = a := Option.some.inj hj
      exact ⟨b, s, b1, s1, ⟨rfl, rfl⟩, e ▸ h1, h2⟩
    | succ j =>
      obtain ⟨b0, s0, b2, s2, A, B, C⟩ := RunFold.split h2 j a hj
      exact ⟨b0, s0, b2, s2, ⟨b1, s1, h1, A⟩, B, C⟩

/-! ## LinkM's own calls -/

/-- A public condition without a name. -/
theorem runs_must {b : Bool} {n : String} {c : Ctx} {u : Unit} {c' : Ctx}
    (h : Runs (Blk.must b n) c u c') : b = true ∧ c' = c := by
  cases b with
  | true => cases h; exact ⟨rfl, rfl⟩
  | false => cases h

/-- LinkM.must: the condition was true, and all is as it was. -/
theorem linkMust_L {b : Bool} {s : HasRuns.St LinkM} {u : Unit} {s' : HasRuns.St LinkM}
    (h : Runs (LinkM.must b) s u s') : b = true ∧ s' = s := by
  obtain ⟨h1, e1⟩ := runs_sub h
  obtain ⟨h2, e2⟩ := runs_lift (σ := Fork) (x := Blk.must b) h1
  obtain ⟨hb, e3⟩ := runs_must h2
  exact ⟨hb, st_ext e1 e2 e3⟩

/-- LinkM.mustAs: the condition was true, and all is as it was. -/
theorem linkMustAs_L {n : String} {b : Bool} {s : HasRuns.St LinkM} {u : Unit}
    {s' : HasRuns.St LinkM} (h : Runs (LinkM.mustAs n b) s u s') : b = true ∧ s' = s := by
  obtain ⟨h1, e1⟩ := runs_sub h
  obtain ⟨h2, e2⟩ := runs_up h1
  obtain ⟨hb, e3⟩ := runs_mustAs h2
  exact ⟨hb, st_ext e1 e2 e3⟩

/-- LinkM.testAs on a view: the condition was true, and all is as it was. -/
theorem linkTestAs_L {n : String} {b : Bool} {s : HasRuns.St LinkM} {u : Unit}
    {s' : HasRuns.St LinkM} (h : Runs (LinkM.testAs n b) s u s') (d : View s) :
    b = true ∧ s' = s := by
  obtain ⟨h1, e1⟩ := runs_sub h
  obtain ⟨h2, e2⟩ := runs_up h1
  obtain ⟨hb, e3⟩ := runs_testAs h2 d
  exact ⟨hb, st_ext e1 e2 e3⟩

/-- A change of the sub-proof's state: the function has returned the new state, and the context is
as it was. -/
theorem runs_change {f : Fork → Option Fork} {t : HasRuns.St SubM} {u : Unit} {t' : HasRuns.St SubM}
    (h : Runs (SubM.change f) t u t') : f t.1 = some t'.1 ∧ t'.2 = t.2 := by
  have h' : SubM.change f t.1 t.2 = .ok ((u, t'.1), t'.2) := h
  unfold SubM.change at h'
  cases e : f t.1 with
  | none => rw [e] at h'; cases h'
  | some G =>
    rw [e] at h'
    have k : (Except.ok (((), G), t.2) : Except Failure ((Unit × Fork) × Ctx)) =
      .ok ((u, t'.1), t'.2) := h'
    cases t'
    cases k
    exact ⟨rfl, rfl⟩

/-- A call of the chain in a link: the link's number is the chain's, the call has succeeded on the
context, the link's state has the call's result as its check and is else as it was, and the
sub-proof's state is as it was. -/
theorem call_L {f : ChainCheck → Blk ChainCheck} {s : HasRuns.St LinkM} {u : Unit}
    {s' : HasRuns.St LinkM} (h : Runs (LinkM.call f) s u s') :
    (s.1.link == s.1.check.link) = true ∧ ∃ chk, f s.1.check s.2.2 = .ok (chk, s'.2.2) ∧
      s'.1 = { s.1 with check := chk } ∧ s'.2.1 = s.2.1 := by
  have h' : Runs (m := SubM) (do
      SubM.must (s.1.link == s.1.check.link)
      let check ← (liftM (f s.1.check) : SubM ChainCheck)
      pure ((), { s.1 with check := check })) s.2 (u, s'.1) s'.2 := h
  obtain ⟨_, t1, h1, h2⟩ := HasRuns.runs_bind h'
  obtain ⟨chk, t2, h3, h4⟩ := HasRuns.runs_bind h2
  obtain ⟨e1, e2⟩ := HasRuns.runs_pure h4
  obtain ⟨k1, k2⟩ := runs_lift (σ := Fork) (x := Blk.must _) h1
  obtain ⟨hb, k3⟩ := runs_must k1
  obtain ⟨k4, k5⟩ := runs_up h3
  have et : t1 = s.2 := Prod.ext k2 k3
  rw [et] at k4 k5
  rw [e2]
  exact ⟨hb, chk, k4, congrArg Prod.snd e1, k5⟩

/-- A change of this layer's own state. -/
theorem runs_modify {m : Type → Type} [Monad m] [HasRuns m] {σ : Type} {f : σ → σ}
    {s : HasRuns.St (StateT σ m)} {u : PUnit} {s' : HasRuns.St (StateT σ m)}
    (h : Runs (modify f : StateT σ m PUnit) s u s') : s' = (f s.1, s.2) := by
  obtain ⟨e1, e2⟩ := HasRuns.runs_pure (m := m) (a := (PUnit.unit, f s.1)) h
  exact Prod.ext (congrArg Prod.snd e1) e2

/-! ## An example: rootInH, whole, with its loop -/

/-- One turn of rootInH's loop: array t is marked as committed, and nothing else changes. -/
def rootTurn (t : Nat) (_ : PUnit) (s : HasRuns.St LinkM) (_ : PUnit) (s1 : HasRuns.St LinkM) :
    Prop :=
  s1 = (s.1, s.2.1.rootTaken t 0, s.2.2)

/-- If rootInH succeeds on a view: the link was neither handed over nor done; the chain's call for
the link's next moment has succeeded on the caller's context; the link's state has that call's
result and one moment more; and the loop has marked the arrays of the list, one after the other,
from the caller's state F, on the context that the chain's call has left. -/
theorem rootInH_ran (trees : List Nat) {L L' : LinkCtx} {F F' : Fork} {c c' : Ctx}
    (hd : c.ch.dry = false) (h : rootInH trees L F c = .ok ((((), L'), F'), c')) :
    (!L.handed && !L.done) = true ∧ (L.link == L.check.link) = true ∧
    ∃ chk c1, L.check.later c = .ok (chk, c1) ∧
      RunFold rootTurn trees PUnit.unit
        ({ L with check := chk, moments := L.moments + 1 }, F, c1) PUnit.unit (L', F', c') := by
  have hr : Runs (rootInH trees) (L, F, c) () (L', F', c') := h
  clear h
  have d : View (m := LinkM) (L, F, c) := hd
  unfold rootInH at hr
  peel3 hr d
  obtain ⟨t1, e⟩ := runs_get r1
  cases e
  dsimp only at t1
  subst t1
  obtain ⟨t2, e⟩ := linkMustAs_L r2
  cases e
  obtain ⟨t3, chk, k1, k2, k3⟩ := call_L r3
  dsimp only at t3 k1 k2 k3
  subst k2 k3
  have e4 := runs_modify r4
  cases e4
  obtain ⟨-, e⟩ := linkMustAs_L hr
  cases e
  refine ⟨t2, t3, chk, _, k1, ?_⟩
  refine runs_forIn _ rootTurn (L', F', c') ?_ trees _ _ _ _ d4 b5 r5
  intro t b s r s1 dt Bt hb
  peel3_from hb dt Bt 11
  obtain ⟨-, e⟩ := fork_L r11
  cases e
  obtain ⟨-, e⟩ := linkMustAs_L r12
  cases e
  obtain ⟨q1, q2⟩ := runs_sub r13
  obtain ⟨q3, q4⟩ := runs_change q1
  obtain ⟨e1, e2⟩ := runs_pure' hb
  dsimp only at q2 q3 q4
  have q5 := Option.some.inj q3
  subst q2 q4 q5 e1 e2
  exact ⟨PUnit.unit, rfl, rfl⟩

#print axioms runs_forIn
#print axioms runs_forIn_array
#print axioms runs_forIn_range
#print axioms runs_forIn_inv
#print axioms RunFold.split
#print axioms runs_must
#print axioms linkMust_L
#print axioms linkMustAs_L
#print axioms linkTestAs_L
#print axioms runs_change
#print axioms call_L
#print axioms runs_modify
#print axioms rootInH_ran

end OnBytes.L5
