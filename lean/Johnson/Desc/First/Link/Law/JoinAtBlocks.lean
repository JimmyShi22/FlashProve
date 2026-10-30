-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/JoinAtBlocks.lean: THE JOINING's PREMISES ON THE BLOCKS, PAID AT A
LINK's OWN TWO BLOCKS: the batching handed the link's own gatherer is a draw with ONE move; the
frame's block behind it is ONE quiet move; and each of the two moves owes what its runs owe, one
duty a run. Theorems: general in the state.

Why. `LinkJoin.JoinAsks` (Johnson/Desc/First/Link/Law/LinkJoin.lean) takes `hb₁` (the batching's
block is a draw with the moves ms₁), `hb₂` (the block behind it is the moves ms₂), `hms` and `hkd`
(each move's duties). A segment's batching is handed `claimsInBy L.each L.hear L.order`
(Johnson/Desc/Block.lean), not the batching kind's own gatherer; the block behind it decides by
`L.runBehind`: the link's tests, then `afterIn L.hear L.orderAfter`.

What is said.
  `batch_drawMoves`: the batching kind's block at a function f of claims is a draw with the one move
    «add f». `behind_isMoves`: the frame's block is the one quiet move `L.runBehind`.
  `runsIn bs order`: the runs that an order names, off the blocks' own lists. `claimsInBy_gather`:
    **a yes of the link's gatherer is a yes of the batching kind's gatherer at these runs, without a
    window, with the same return** (the test behind a run can only refuse). `claimsInBy_addOk`: **so
    the link's gatherer meets `AddOk` from one `RunOk` a run.** `claimsInBy_door`: the door's duty,
    from one a run.
  `afterIn_quietOk`, `runBehind_quietOk`: **`QuietOk` of the runs behind the batching, from one
    `QuietOk` a run**; the link's tests cannot turn the state, by type. `runBehind_door`: the door's
    duty.

Limits. Tools. That a record's batching IS the batching kind's block, and each run's own duty, stay
owed. Nothing on soundness.

-/
import Johnson.Desc.BlockLaws
import Johnson.Desc.LinkLaw2
import Johnson.Desc.First.Batch.Law.AtBlock
import Johnson.Desc.First.Batch.Law.Steps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.JoinAtBlocks
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Lens Where RunOf gather)
open VerifiableInference.Desc.K9L

variable {T P K : Type}

/-! ## The two blocks -/

/-- The batching kind's block at a function of claims is a draw with one move. -/
theorem batch_drawMoves (X : Lens T) (p : Where) (f : T → Except String (List Claim × T)) :
    DrawMoves X p [.add f] (K9.batch X p f) := by
  intro ft s rs cols s' k h
  obtain ⟨r, x, a, o, cls, s₂, b, G, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    batch_step X p f ft s rs cols s' k h
  exact ⟨r, x, a, o, cls ++ [], h1, h2, h3, h4, s', cls, [], ⟨s₂, b, G, h5, h6, h7, h8⟩,
    ⟨rfl, rfl⟩, rfl⟩

/-- The frame's block behind the batching is one quiet move. -/
theorem behind_isMoves (X : Lens T) (L : Link T Claim) :
    IsMoves X [.quiet L.runBehind] L.behindB :=
  isMoves_quiet X L.behindB rfl L.runBehind fun _ _ _ => rfl

/-! ## The link's gatherer -/

/-- The runs that an order names, off the blocks' own lists. -/
def runsIn (bs : List (Block T Claim)) (order : List (ℕ × String)) : List (RunOf T) :=
  order.filterMap fun o => ((bs[o.1]?).bind fun b => b.claims.lookup o.2).map fun r => (o.2, r)

/-- One step. -/
theorem step_gstep (each : ℕ × String → List Claim → T → Except String Unit)
    (bs : List (Block T Claim)) (x z : List Claim × T) (o : ℕ × String)
    (h : claimsInStep each bs x o = .ok z) :
    ∃ run, ((bs[o.1]?).bind fun b => b.claims.lookup o.2) = some run ∧
      gstep (fun _ => []) [] x (o.2, run) = .ok z := by
  have h0 := claimsInStep_ok each bs x z o h
  unfold claimsInStep at h0
  cases hl : ((bs[o.1]?).bind fun b => b.claims.lookup o.2) with
  | none => simp [hl, named, Except.bind] at h0
  | some run =>
    refine ⟨run, rfl, ?_⟩
    simp only [hl, named, Except.bind] at h0
    cases hr : run x.1.length x.2 with
    | error e => simp [hr] at h0
    | ok y =>
      simp only [hr] at h0
      unfold gstep
      simp only [hr]
      exact h0

/-- The fold. -/
theorem fold_gstep (each : ℕ × String → List Claim → T → Except String Unit)
    (bs : List (Block T Claim)) : ∀ (order : List (ℕ × String)) (x z : List Claim × T),
      order.foldl (fun (acc : Except String (List Claim × T)) o =>
        acc.bind fun x => claimsInStep each bs x o) (.ok x) = .ok z →
      (runsIn bs order).foldlM (gstep (fun _ => []) []) x = .ok z
  | [], x, z, h => h
  | o :: l, x, z, h => by
    have h' : l.foldl (fun (acc : Except String (List Claim × T)) o =>
        acc.bind fun x => claimsInStep each bs x o) (claimsInStep each bs x o) = .ok z := h
    cases hs : claimsInStep each bs x o with
    | error e =>
      rw [hs, claimsInFold_error] at h'
      exact nomatch h'
    | ok x' =>
      rw [hs] at h'
      obtain ⟨run, hl, hg⟩ := step_gstep each bs x x' o hs
      have e : runsIn bs (o :: l) = (o.2, run) :: runsIn bs l :=
        List.filterMap_cons_some (by simp only [hl, Option.map_some])
      rw [e, List.foldlM_cons, hg]
      exact fold_gstep each bs l x' z h'

/-- **A yes of the link's gatherer is a yes of the batching kind's, with the same return.** -/
theorem claimsInBy_gather (each : ℕ × String → List Claim → T → Except String Unit)
    (bs : List (Block T Claim)) (order : List (ℕ × String)) (s : T) (z : List Claim × T)
    (h : claimsInBy each bs order s = .ok z) :
    gather (fun _ => []) [] (runsIn bs order) s = .ok z := by
  rw [gather_eq]
  exact fold_gstep each bs order ([], s) z h

variable [Field K] (ρ : Reading K) (X : Lens T) (O : Others T P K) (Fx : P → T → Prop)

/-- The premise on a function of claims starts from a yes. -/
theorem addOk_of_yes {g g' : T → Except String (List Claim × T)}
    {tm : ℕ → P → Bound K → List (ℕ × K)} {len : P → ℕ} (h : ∀ e x, g e = .ok x → g' e = .ok x)
    (H : AddOk ρ X O Fx g' tm len) : AddOk ρ X O Fx g tm len :=
  fun q e a c e₁ hf hg ha hs hr => H q e a c e₁ hf hg ha hs (h e _ hr)

/-- **THE LINK's GATHERER MEETS AddOk, FROM ONE RunOk A RUN.** -/
theorem claimsInBy_addOk (p : Where) (H : FitsM X O Fx p)
    (each : ℕ × String → List Claim → T → Except String Unit) (bs : List (Block T Claim))
    (order : List (ℕ × String)) (rl : List (TermedRun T P K))
    (hrl : rl.map (·.run) = runsIn bs order)
    (hr : ∀ r ∈ rl, RunOk ρ X O Fx r.run.2 r.tm r.len) :
    AddOk ρ X O Fx (claimsInBy each bs order) (fun n q y => termsRuns q y rl n)
      (fun q => lenRuns q rl) :=
  addOk_of_yes ρ X O Fx
    (fun e x h => by rw [hrl]; exact claimsInBy_gather each bs order e x h)
    (gather_addOk ρ X O Fx p H (fun _ => []) [] rl hr)

/-! ## The runs behind the batching -/

/-- One step of the fold of the runs behind the batching. -/
def stepA (bs : List (Block T Claim)) (acc : Except String T) (o : ℕ × String) : Except String T :=
  acc.bind fun x =>
    (named (o.2 ++ ": no such run") ((bs[o.1]?).bind fun b => b.after.lookup o.2)).bind fun run =>
      match run x with
      | .ok y => .ok y
      | .error e => .error (o.2 ++ ": " ++ e)

theorem afterIn_eq (bs : List (Block T Claim)) (order : List (ℕ × String)) (s : T) :
    afterIn bs order s = order.foldl (stepA bs) (.ok s) := rfl

/-- A fold of the runs behind the batching that stands at a refusal stays there. -/
theorem afterFold_error (bs : List (Block T Claim)) (order : List (ℕ × String)) (e : String) :
    order.foldl (stepA bs) (Except.error e) = Except.error e := by
  induction order with
  | nil => rfl
  | cons o l ih => exact ih

/-- What a yes of the runs behind the batching is: a chain of yeses of the named runs. -/
inductive Ran (bs : List (Block T Claim)) : List (ℕ × String) → T → T → Prop
  | nil (e : T) : Ran bs [] e e
  | cons (o : ℕ × String) (l : List (ℕ × String)) (run : T → Except String T) (e e' e₁ : T) :
      ((bs[o.1]?).bind fun b => b.after.lookup o.2) = some run → run e = .ok e' →
      Ran bs l e' e₁ → Ran bs (o :: l) e e₁

theorem afterIn_ran (bs : List (Block T Claim)) : ∀ (order : List (ℕ × String)) (e e₁ : T),
    afterIn bs order e = .ok e₁ → Ran bs order e e₁
  | [], e, e₁, h => by
    obtain rfl : e = e₁ := Except.ok.inj h
    exact .nil e
  | o :: l, e, e₁, h => by
    rw [afterIn_eq, List.foldl_cons] at h
    cases hl : ((bs[o.1]?).bind fun b => b.after.lookup o.2) with
    | none =>
      have e0 : stepA bs (.ok e) o = .error (o.2 ++ ": no such run") := by
        unfold stepA
        rw [hl]
        rfl
      rw [e0, afterFold_error] at h
      exact nomatch h
    | some run =>
      cases hr : run e with
      | error x =>
        have e0 : stepA bs (.ok e) o = .error (o.2 ++ ": " ++ x) := by
          unfold stepA
          rw [hl]
          show (match run e with
            | .ok y => Except.ok y
            | .error e => .error (o.2 ++ ": " ++ e)) = _
          rw [hr]
        rw [e0, afterFold_error] at h
        exact nomatch h
      | ok e' =>
        have e0 : stepA bs (.ok e) o = .ok e' := by
          unfold stepA
          rw [hl]
          show (match run e with
            | .ok y => Except.ok y
            | .error e => .error (o.2 ++ ": " ++ e)) = _
          rw [hr]
        rw [e0] at h
        exact .cons o l run e e' e₁ hl hr (afterIn_ran bs l e' e₁ h)

omit [Field K] in
/-- **QuietOk OF THE RUNS BEHIND THE BATCHING, FROM ONE A RUN.** -/
theorem afterIn_quietOk (p : Where) (H : FitsM X O Fx p) (bs : List (Block T Claim))
    (order : List (ℕ × String))
    (hq : ∀ o ∈ order, ∀ run, ((bs[o.1]?).bind fun b => b.after.lookup o.2) = some run →
      QuietOk X O Fx run) :
    QuietOk X O Fx (afterIn bs order) := by
  intro q e a e₁ hf hg ha hs h
  have hR := afterIn_ran bs order e e₁ h
  clear h
  induction hR generalizing a with
  | nil e => exact ⟨a, ha, rfl, hg, H.moreRefl e, hf⟩
  | cons o l run e e' e₁ hl hr _ ih =>
    obtain ⟨a', ha', c1, g1, m1, f1⟩ :=
      hq o (List.mem_cons_self ..) run hl q e a e' hf hg ha hs hr
    obtain ⟨_, _, _, _, p5, p6⟩ := core_parts c1
    obtain ⟨a₁, ha₁, c2, g2, m2, f2⟩ :=
      ih (fun o' ho' => hq o' (List.mem_cons_of_mem _ ho')) a' f1 g1 ha' (by rw [p5, p6]; exact hs)
    exact ⟨a₁, ha₁, c2.trans c1, g2, H.moreTrans _ _ _ m1 m2, f2⟩

omit [Field K] in
/-- The same of the frame's function: the link's tests cannot turn the state, by type. -/
theorem runBehind_quietOk (p : Where) (H : FitsM X O Fx p) (L : Link T Claim)
    (hq : ∀ o ∈ L.orderAfter, ∀ run,
      ((L.hear[o.1]?).bind fun b => b.after.lookup o.2) = some run → QuietOk X O Fx run) :
    QuietOk X O Fx L.runBehind :=
  fun q e a e₁ hf hg ha hs h =>
    afterIn_quietOk X O Fx p H L.hear L.orderAfter hq q e a e₁ hf hg ha hs
      (Link.afterIn_of_runBehind h)

/-! ## The door's duty -/

omit [Field K] in
theorem keepsDoor_refl (e : T) : KeepsDoor X e e := fun a ha => ⟨a, ha, rfl, rfl⟩

omit [Field K] in
/-- The door's duty of the link's gatherer, from one a run. -/
theorem claimsInBy_door (each : ℕ × String → List Claim → T → Except String Unit)
    (bs : List (Block T Claim)) (order : List (ℕ × String))
    (hr : ∀ r ∈ runsIn bs order, ∀ n e c e₁, r.2 n e = .ok (c, e₁) → KeepsDoor X e e₁) :
    MoveDoor X (.add (claimsInBy each bs order)) := by
  intro e c e₁ h
  exact gather_door X (fun _ => []) [] (runsIn bs order) hr ([], e) (c, e₁)
    (fold_gstep each bs order ([], e) (c, e₁) h)

omit [Field K] in
/-- The door's duty of the runs behind the batching, from one a run. -/
theorem afterIn_door (bs : List (Block T Claim)) (order : List (ℕ × String))
    (hq : ∀ o ∈ order, ∀ run, ((bs[o.1]?).bind fun b => b.after.lookup o.2) = some run →
      ∀ e e₁, run e = .ok e₁ → KeepsDoor X e e₁) (e e₁ : T) (h : afterIn bs order e = .ok e₁) :
    KeepsDoor X e e₁ := by
  have hR := afterIn_ran bs order e e₁ h
  clear h
  induction hR with
  | nil e => exact keepsDoor_refl X e
  | cons o l run e e' e₁ hl hr _ ih =>
    exact keepsDoor_trans X (hq o (List.mem_cons_self ..) run hl e e' hr)
      (ih fun o' ho' => hq o' (List.mem_cons_of_mem _ ho'))

omit [Field K] in
/-- The same of the frame's function. -/
theorem runBehind_door (L : Link T Claim)
    (hq : ∀ o ∈ L.orderAfter, ∀ run,
      ((L.hear[o.1]?).bind fun b => b.after.lookup o.2) = some run →
      ∀ e e₁, run e = .ok e₁ → KeepsDoor X e e₁) :
    MoveDoor X (.quiet L.runBehind) :=
  fun e e₁ h => afterIn_door X L.hear L.orderAfter hq e e₁ (Link.afterIn_of_runBehind h)

end VerifiableInference.Desc.JoinAtBlocks

#print axioms VerifiableInference.Desc.JoinAtBlocks.batch_drawMoves
#print axioms VerifiableInference.Desc.JoinAtBlocks.behind_isMoves
#print axioms VerifiableInference.Desc.JoinAtBlocks.claimsInBy_gather
#print axioms VerifiableInference.Desc.JoinAtBlocks.claimsInBy_addOk
#print axioms VerifiableInference.Desc.JoinAtBlocks.claimsInBy_door
#print axioms VerifiableInference.Desc.JoinAtBlocks.afterIn_quietOk
#print axioms VerifiableInference.Desc.JoinAtBlocks.runBehind_quietOk
#print axioms VerifiableInference.Desc.JoinAtBlocks.runBehind_door
