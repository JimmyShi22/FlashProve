-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/RowsNoArms.lean: THE ROWS OF THE SENDINGS DO NOT HANG ON THE LINKS'
ARMS: WHERE `rowsFrom` (RowsFrom.lean beside this file) RETURNS AT TWO TABLES OF ARMS, IT RETURNS
ONE VALUE. Theorems. A law file; no running text imports it.

Why. The second reading of the three public files (Johnson/G/LinkSig.lean: sendRowsOf) reads of the
planner's value what the planner has made, two numbers that follow from it, and the links' arms
(RowsFrom.lean, RowsOfMade.lean). What was made is held against a written value by a test of the
verifier; the arms are held by none. Here: the arms bear on WHETHER the second reading returns (the
plan written anew must be the planner's), never on WHAT it returns.
  `trace cs`        what a list of calls says of samples (Call.sendSamples,
                    Johnson/G/PackList.lean).
  `Quiet x`         a noting routine that notes no call with a sample; `quiet_pure`, `quiet_bind`,
                    `quiet_lift`, `quiet_note`, `quiet_noteV`, `quiet_ite`, `quiet_forIn`; the
                    tactic `quiet`.
  `nArm_quiet`      an arm's routine is quiet (nHead, nLayer, nAttention; through nLookup,
                    nForest, nSmall, nLayerOwn, nAttentionOwn of Johnson/G/Calls.lean).
  `Sim R x x'`      two noting routines: wherever both return, from lists of calls with one trace,
                    the lists behind have one trace and the values stand in R; `sim_pure`,
                    `sim_bind`, `sim_quiet`, `sim_note`, `sim_noteV`, `sim_must`, `sim_ite`; the
                    tactic `simstep`.
  `nFrameA_sim`     the frame at two tables of arms.
  `noted_trace`, `calls_same`   the seven lists of calls at two tables of arms say the same of
                    samples.
  `pack_no_arms`, `rows_no_arms`   rowsFrom c o n A = .ok r · rowsFrom c o n A' = .ok r' ⊢ r =
                    r': the whole rows: file, chain, entry, label, codes, every sampled shape with
                    its radius, the riders.

Limits. BOTH RETURNS ARE PREMISES: at a table of arms at which the plan written anew is not the
planner's, rowsFrom refuses, and nothing is said. That the one value is a written one is not said.
Nothing on what a radius means. Nothing on soundness or on hiding.

-/
import Johnson.Desc.First.Link.Law.RowsFromCongr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom
open VerifiableInference.Number (sendsFrom)

/-- What a list of calls says of samples. -/
def trace (cs : Array Call) : List (List SampleSize) := cs.toList.flatMap Call.sendSamples

/-- Two noting routines: wherever both return, from lists of calls with one trace, the lists behind
have one trace, and the values stand in R. -/
def Sim {α : Type} (R : α → α → Prop) (x x' : N α) : Prop :=
  ∀ cs cs2 p p2 a cs' p' a2 cs2' p2', (x.run cs).run p = .ok ((a, cs'), p') →
    (x'.run cs2).run p2 = .ok ((a2, cs2'), p2') → trace cs = trace cs2 →
    trace cs' = trace cs2' ∧ R a a2

/-- A noting routine that notes no call with a sample. -/
def Quiet {α : Type} (x : N α) : Prop :=
  ∀ cs p a cs' p', (x.run cs).run p = .ok ((a, cs'), p') → trace cs' = trace cs

abbrev Any {α : Type} : α → α → Prop := fun _ _ => True

section
variable {α β : Type}

theorem run_bind_ok {x : N α} {f : α → N β} {cs : Array Call} {p : PlanState} {b : β}
    {cs' : Array Call} {p' : PlanState} (h : ((x >>= f).run cs).run p = .ok ((b, cs'), p')) :
    ∃ a cs1 p1, (x.run cs).run p = .ok ((a, cs1), p1) ∧
      ((f a).run cs1).run p1 = .ok ((b, cs'), p') := by
  rw [StateT.run_bind, StateT.run_bind] at h
  obtain ⟨⟨⟨a, cs1⟩, p1⟩, hr, h2⟩ := exc_bind h
  exact ⟨a, cs1, p1, hr, h2⟩

theorem quiet_pure (a : α) : Quiet (pure a : N α) := by
  intro cs p b cs' p' h
  cases h
  rfl

theorem quiet_bind {x : N α} {f : α → N β} (hx : Quiet x) (hf : ∀ a, Quiet (f a)) :
    Quiet (x >>= f) := by
  intro cs p b cs' p' h
  obtain ⟨a, cs1, p1, h1, h2⟩ := run_bind_ok h
  rw [hf a cs1 p1 b cs' p' h2, hx cs p a cs1 p1 h1]

theorem quiet_lift (y : Planning α) : Quiet (liftM y : N α) := by
  intro cs p b cs' p' h
  have h' : (y.run p >>= fun r => (pure ((r.1, cs), r.2) : Except String _)) =
      .ok ((b, cs'), p') := h
  obtain ⟨r, _, h2⟩ := exc_bind h'
  cases h2
  rfl

theorem note_run {c : Call} {cs : Array Call} {p : PlanState} {a : Unit} {cs' : Array Call}
    {p' : PlanState} (h : ((note c).run cs).run p = .ok ((a, cs'), p')) : cs' = cs.push c := by
  have h' : (c.plan.run p >>= fun r => (pure ((r.1, cs.push c), r.2) : Except String _)) =
      .ok ((a, cs'), p') := h
  obtain ⟨r, _, h2⟩ := exc_bind h'
  cases h2
  rfl

theorem noteV_run {c : Call} {y : Planning α} {cs : Array Call} {p : PlanState} {a : α}
    {cs' : Array Call} {p' : PlanState} (h : ((noteV c y).run cs).run p = .ok ((a, cs'), p')) :
    cs' = cs.push c := by
  have h' : (y.run p >>= fun r => (pure ((r.1, cs.push c), r.2) : Except String _)) =
      .ok ((a, cs'), p') := h
  obtain ⟨r, _, h2⟩ := exc_bind h'
  cases h2
  rfl

theorem trace_push (cs : Array Call) (c : Call) :
    trace (cs.push c) = trace cs ++ c.sendSamples := by
  unfold trace
  rw [Array.toList_push, List.flatMap_append]
  simp

theorem quiet_note {c : Call} (h : c.sendSamples = []) : Quiet (note c) := by
  intro cs p a cs' p' hr
  rw [note_run hr, trace_push, h, List.append_nil]

theorem quiet_noteV {c : Call} (y : Planning α) (h : c.sendSamples = []) : Quiet (noteV c y) := by
  intro cs p a cs' p' hr
  rw [noteV_run hr, trace_push, h, List.append_nil]

theorem quiet_ite {c : Prop} [Decidable c] {x y : N α} (hx : Quiet x) (hy : Quiet y) :
    Quiet (if c then x else y) := by
  split
  · exact hx
  · exact hy

theorem quiet_forIn {γ : Type} {f : γ → PUnit → N (ForInStep PUnit)} (h : ∀ a r, Quiet (f a r)) :
    ∀ (l : List γ) (b : PUnit), Quiet (forIn l b f)
  | [], b => by
    rw [List.forIn_nil]
    exact quiet_pure b
  | a :: l, b => by
    rw [List.forIn_cons]
    refine quiet_bind (h a b) fun s => ?_
    cases s with
    | done b' => exact quiet_pure b'
    | yield b' => exact quiet_forIn h l b'

end

/-- Steps through a routine that notes no call with a sample. -/
macro "quiet" : tactic => `(tactic| repeat' first
  | with_reducible apply quiet_bind
  | with_reducible apply quiet_ite
  | with_reducible apply quiet_forIn
  | ((with_reducible refine quiet_note ?_) <;> rfl)
  | ((with_reducible refine quiet_noteV _ ?_) <;> rfl)
  | with_reducible exact quiet_pure _
  | with_reducible exact quiet_lift _
  | with_reducible assumption
  | with_reducible intro _)

theorem nLookup_quiet (x : LookupSize) : Quiet (nLookup x) := by
  unfold nLookup
  try dsimp only
  quiet

theorem nForest_quiet (x : ForestSize) : Quiet (nForest x) := nLookup_quiet _

theorem nSmall_quiet (x : SmallSize) (which : Nat) : Quiet (nSmall x which) := by
  have := nForest_quiet x.digits
  unfold nSmall
  try dsimp only
  quiet

theorem nLayerOwn_quiet (x : LayerRounds) : Quiet (nLayerOwn x) := by
  unfold nLayerOwn
  try dsimp only
  quiet

theorem nLayer_quiet (look : ForestSize) (x : LayerRounds) (small : SmallSize)
    (claims moment : Nat) : Quiet (nLayer look x small claims moment) := by
  have := nForest_quiet look
  have := nLayerOwn_quiet x
  have := nSmall_quiet small (moment - 1)
  unfold nLayer
  try dsimp only
  quiet

theorem nAttentionOwn_quiet (x : AttentionRounds) : Quiet (nAttentionOwn x) := by
  unfold nAttentionOwn
  try dsimp only
  quiet

theorem nAttention_quiet (look : ForestSize) (x : AttentionRounds) (small : SmallSize)
    (moment : Nat) : Quiet (nAttention look x small moment) := by
  have := nForest_quiet look
  have := nAttentionOwn_quiet x
  have := nSmall_quiet small (moment - 1)
  unfold nAttention
  try dsimp only
  quiet

theorem nHead_quiet (look : ForestSize) (x : HeadRounds) (small : SmallSize) (moment : Nat) :
    Quiet (nHead look x small moment) := by
  have := nForest_quiet look
  have := nSmall_quiet small (moment - 1)
  unfold nHead
  try dsimp only
  quiet

/-- **An arm's routine notes no call with a sample.** -/
theorem nArm_quiet (a : Arm) (moment : Nat) : Quiet (nArm a moment) := by
  cases a with
  | head l x s => exact nHead_quiet l x s moment
  | layer l x s c => exact nLayer_quiet l x s c moment
  | attention l x s => exact nAttention_quiet l x s moment
  | none => exact quiet_lift _

/-! ## Two routines side by side -/

section
variable {α β : Type}

theorem sim_pure {R : α → α → Prop} {a a' : α} (h : R a a') :
    Sim R (pure a : N α) (pure a') := by
  intro cs cs2 p p2 b cs' p' b2 cs2' p2' h1 h2 ht
  cases h1
  cases h2
  exact ⟨ht, h⟩

theorem sim_bind {R : α → α → Prop} {Q : β → β → Prop} {x x' : N α} {f f' : α → N β}
    (hx : Sim R x x') (hf : ∀ a a', R a a' → Sim Q (f a) (f' a')) :
    Sim Q (x >>= f) (x' >>= f') := by
  intro cs cs2 p p2 b cs' p' b2 cs2' p2' h1 h2 ht
  obtain ⟨a, c1, q1, e1, e2⟩ := run_bind_ok h1
  obtain ⟨a', c1', q1', e1', e2'⟩ := run_bind_ok h2
  obtain ⟨t1, r⟩ := hx _ _ _ _ _ _ _ _ _ _ e1 e1' ht
  exact hf a a' r _ _ _ _ _ _ _ _ _ _ e2 e2' t1

theorem sim_quiet {x x' : N α} (h : Quiet x) (h' : Quiet x') : Sim Any x x' := by
  intro cs cs2 p p2 b cs' p' b2 cs2' p2' h1 h2 ht
  exact ⟨by rw [h _ _ _ _ _ h1, h' _ _ _ _ _ h2, ht], trivial⟩

theorem sim_note {c c' : Call} (h : c.sendSamples = c'.sendSamples) :
    Sim Any (note c) (note c') := by
  intro cs cs2 p p2 b cs' p' b2 cs2' p2' h1 h2 ht
  rw [note_run h1, note_run h2, trace_push, trace_push, ht, h]
  exact ⟨rfl, trivial⟩

theorem sim_noteV {c c' : Call} (y y' : Planning α) (h : c.sendSamples = c'.sendSamples) :
    Sim Any (noteV c y) (noteV c' y') := by
  intro cs cs2 p p2 b cs' p' b2 cs2' p2' h1 h2 ht
  rw [noteV_run h1, noteV_run h2, trace_push, trace_push, ht, h]
  exact ⟨rfl, trivial⟩

theorem sim_must (o : Option α) (w : String) :
    Sim Eq (liftM (must o w) : N α) (liftM (must o w)) := by
  intro cs cs2 p p2 b cs' p' b2 cs2' p2' h1 h2 ht
  cases o with
  | none => cases h1
  | some v =>
    cases h1
    cases h2
    exact ⟨ht, rfl⟩

theorem sim_ite {c : Prop} [Decidable c] {R : α → α → Prop} {x x' y y' : N α}
    (hx : Sim R x x') (hy : Sim R y y') :
    Sim R (if c then x else y) (if c then x' else y') := by
  split
  · exact hx
  · exact hy

end

theorem nReqSend_sim (codes : Codes) (sent : List OracleNotice) (group atStart : GroupSize)
    (riders : Nat) (ownRound : Bool) :
    Sim Any (nReqSend codes sent group atStart riders ownRound)
      (nReqSend codes sent group atStart riders ownRound) := by
  unfold nReqSend
  dsimp only
  exact sim_bind (sim_must _ _) fun _ _ _ => sim_note rfl

theorem nStages_sim (f : Nat) (m : Bool) :
    ∀ (first : Bool) (st : List StageSize), Sim Any (nStages f m first st) (nStages f m first st)
  | first, x :: y :: rest => by
    unfold nStages
    dsimp only
    exact sim_bind (sim_note rfl) fun _ _ _ => sim_bind (sim_noteV _ _ rfl) fun _ _ _ =>
      sim_bind (sim_quiet (quiet_lift _) (quiet_lift _)) fun _ _ _ =>
        nStages_sim f m false (y :: rest)
  | _, [x] => by
    unfold nStages
    dsimp only
    exact sim_bind (sim_noteV _ _ rfl) fun _ _ _ => sim_quiet (quiet_lift _) (quiet_lift _)
  | _, [] => by
    unfold nStages
    exact sim_quiet (quiet_lift _) (quiet_lift _)

theorem nIopp_sim (st : List StageSize) (rows rows' f : Nat) (m : Bool) :
    Sim Any (nIopp st rows f m) (nIopp st rows' f m) := by
  unfold nIopp
  exact sim_bind (sim_quiet (quiet_lift _) (quiet_lift _)) fun _ _ _ =>
    sim_bind (sim_note rfl) fun _ _ _ => nStages_sim f m true st

theorem nMomentsA_sim (A A' : Nat → Arm) (z : ProofSized) (l : Nat) (msgs : List ReqMessage) :
    ∀ fuel moment, Sim Any (nMomentsA A z l msgs fuel moment) (nMomentsA A' z l msgs fuel moment)
  | 0, _ => sim_pure trivial
  | fuel + 1, moment => by
    unfold nMomentsA
    dsimp only
    exact sim_bind (nReqSend_sim _ _ _ _ _ _) fun _ _ _ =>
      sim_bind (sim_quiet (nArm_quiet _ _) (nArm_quiet _ _)) fun _ _ _ =>
        sim_bind (sim_note rfl) fun _ _ _ =>
          sim_bind (nMomentsA_sim A A' z l msgs fuel (moment + 1)) fun _ _ _ => sim_pure trivial

/-- Steps through two routines of one text. -/
macro "simstep" : tactic => `(tactic| repeat' first
  | with_reducible apply sim_ite
  | with_reducible apply sim_bind
  | ((with_reducible refine sim_note ?_) <;> rfl)
  | ((with_reducible refine sim_noteV _ _ ?_) <;> rfl)
  | with_reducible exact sim_pure (R := Any) trivial
  | with_reducible exact nReqSend_sim _ _ _ _ _ _
  | with_reducible exact sim_quiet (nArm_quiet _ _) (nArm_quiet _ _)
  | with_reducible exact nIopp_sim _ _ _ _ _
  | with_reducible exact nMomentsA_sim _ _ _ _ _ _ _
  | with_reducible assumption
  | with_reducible intro _)

/-- **The frame at two tables of arms.** -/
theorem nFrameA_sim (A A' : Nat → Arm) (z : ProofSized) :
    ∀ (gs : List ReqGroup) (l : Nat) (links : List ReqLink) (open_ : List Nat)
      (before : GroupSize),
    Sim Any (nFrameA A z l gs links open_ before) (nFrameA A' z l gs links open_ before)
  | [], _, _, _, _ => by
    unfold nFrameA
    exact sim_pure trivial
  | g :: gs, l, links, open_, before => by
    have ih := fun c => nFrameA_sim A A' z gs (l + 1) (links.drop 1) (open_.drop 1) c
    unfold nFrameA
    cases links.head? with
    | none =>
      dsimp only
      simstep
    | some lk =>
      dsimp only
      simstep
      all_goals exact ih _

theorem nLinFirst_sim (codes : Codes) (x : LinSized) :
    Sim Any (nLinFirst codes x) (nLinFirst codes x) := by
  unfold nLinFirst
  refine sim_bind (sim_must _ _) fun a a' e => ?_
  subst e
  exact sim_note rfl

/-- What `noted` returns at two routines that go side by side has one trace. -/
theorem noted_trace {s : Setting} {scope : Scope} {x x' : N Unit} (hs : Sim Any x x')
    {calls calls' : List Call} {P P' : Planned} (h : noted s scope x = .ok (calls, P))
    (h' : noted s scope x' = .ok (calls', P')) :
    calls.flatMap Call.sendSamples = calls'.flatMap Call.sendSamples := by
  unfold noted at h h'
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨⟨⟨a, cs⟩, p⟩, hr, h⟩ := exc_bind h
  obtain ⟨_, _, h'⟩ := exc_bind h'
  obtain ⟨⟨⟨a', cs'⟩, p'⟩, hr', h'⟩ := exc_bind h'
  cases h
  cases h'
  exact (hs _ _ _ _ _ _ _ _ _ _ hr hr' rfl).1

theorem mapM_id_ok {ε α : Type} : ∀ (es : List (Except ε α)) (l : List α),
    es.mapM id = .ok l → es = l.map Except.ok
  | [], l, h => by
    rw [List.mapM_nil] at h
    cases h
    rfl
  | e :: es, l, h => by
    rw [List.mapM_cons] at h
    obtain ⟨a, ha, h⟩ := exc_bind h
    obtain ⟨t, ht, h⟩ := exc_bind h
    cases h
    rw [List.map_cons, ← mapM_id_ok es t ht]
    exact congrArg (· :: es) ha

theorem mapM_id7 {ε α : Type} {e0 e1 e2 e3 e4 e5 e6 : Except ε α} {l : List α}
    (h : [e0, e1, e2, e3, e4, e5, e6].mapM id = .ok l) :
    ∃ a0 a1 a2 a3 a4 a5 a6, e0 = .ok a0 ∧ e1 = .ok a1 ∧ e2 = .ok a2 ∧ e3 = .ok a3 ∧
      e4 = .ok a4 ∧ e5 = .ok a5 ∧ e6 = .ok a6 ∧ l = [a0, a1, a2, a3, a4, a5, a6] := by
  have e := mapM_id_ok _ _ h
  rcases l with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, l⟩⟩⟩⟩⟩⟩⟩⟩
    <;> simp at e
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := e
  exact ⟨a0, a1, a2, a3, a4, a5, a6, h0, h1, h2, h3, h4, h5, h6, rfl⟩

/-- Two chains' lists of calls say the same of samples. -/
def Like (a a' : Johnson.G.Chain) : Prop :=
  a.file = a'.file ∧ a.chain = a'.chain ∧
    a.calls.flatMap Call.sendSamples = a'.calls.flatMap Call.sendSamples

theorem like_refl (a : Johnson.G.Chain) : Like a a := ⟨rfl, rfl, rfl⟩

/-- **The seven lists of calls at two tables of arms say the same of samples.** -/
theorem calls_same {c : Configured} {o : List Nat} {n : Nat} {A A' : Nat → Arm} {s s' : Setting}
    {ch ch' : List Johnson.G.Chain} (h : callsFrom c o n A = .ok (s, ch))
    (h' : callsFrom c o n A' = .ok (s', ch')) : s = s' ∧ List.Forall₂ Like ch ch' := by
  unfold callsFrom at h h'
  dsimp only at h h'
  generalize c.key = K at h h'
  generalize c.proof = P at h h'
  split at h
  · dsimp only at h'
    obtain ⟨l, hl, h⟩ := exc_bind h
    obtain ⟨l', hl', h'⟩ := exc_bind h'
    cases h
    cases h'
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, h0, h1, h2, h3, h4, h5, h6, rfl⟩ := mapM_id7 hl
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, g0, g1, g2, g3, g4, g5, g6, rfl⟩ := mapM_id7 hl'
    obtain rfl : a0 = b0 := Except.ok.inj (h0.symm.trans g0)
    obtain rfl : a1 = b1 := Except.ok.inj (h1.symm.trans g1)
    obtain rfl : a2 = b2 := Except.ok.inj (h2.symm.trans g2)
    obtain rfl : a3 = b3 := Except.ok.inj (h3.symm.trans g3)
    obtain rfl : a5 = b5 := Except.ok.inj (h5.symm.trans g5)
    obtain rfl : a6 = b6 := Except.ok.inj (h6.symm.trans g6)
    obtain ⟨⟨calls, Q⟩, hn, h4⟩ := exc_bind h4
    dsimp only at h4
    split at h4
    swap
    · obtain ⟨_, e, _⟩ := exc_bind h4
      cases e
    obtain ⟨_, _, h4⟩ := exc_bind h4
    obtain ⟨_, _, h4⟩ := exc_bind h4
    split at h4
    swap
    · obtain ⟨_, e, _⟩ := exc_bind h4
      cases e
    obtain ⟨_, _, h4⟩ := exc_bind h4
    cases h4
    obtain ⟨⟨calls', Q'⟩, gn, g4⟩ := exc_bind g4
    dsimp only at g4
    split at g4
    swap
    · obtain ⟨_, e, _⟩ := exc_bind g4
      cases e
    obtain ⟨_, _, g4⟩ := exc_bind g4
    obtain ⟨_, _, g4⟩ := exc_bind g4
    split at g4
    swap
    · obtain ⟨_, e, _⟩ := exc_bind g4
      cases e
    obtain ⟨_, _, g4⟩ := exc_bind g4
    cases g4
    have key : calls.flatMap Call.sendSamples = calls'.flatMap Call.sendSamples := by
      refine noted_trace ?_ hn gn
      have := nFrameA_sim A A' c.sized.proof (reqGroups c.sized.proof.request).toList 0
        c.sized.proof.request.link o c.sized.proof.link.group
      have := nLinFirst_sim c.sized.proof.codes c.sized.proof.batch
      simstep
    exact ⟨rfl, .cons (like_refl _) (.cons (like_refl _) (.cons (like_refl _) (.cons (like_refl _)
      (.cons ⟨rfl, rfl, key⟩ (.cons (like_refl _) (.cons (like_refl _) .nil))))))⟩
  · cases h

theorem mapM_zip_like {ε α β γ : Type} {R : α → α → Prop} (F : α × β → Except ε γ)
    (hF : ∀ a a' d, R a a' → F (a, d) = F (a', d)) :
    ∀ {xs xs' : List α}, List.Forall₂ R xs xs' → ∀ ys : List β,
      (xs.zip ys).mapM F = (xs'.zip ys).mapM F
  | _, _, .nil, _ => rfl
  | _, _, .cons (a := a) (b := a') (l₁ := l) (l₂ := l') r t, ys => by
    cases ys with
    | nil => rfl
    | cons d ds =>
      rw [List.zip_cons_cons, List.zip_cons_cons, List.mapM_cons, List.mapM_cons, hF a a' d r,
        mapM_zip_like F hF t ds]

theorem pack_no_arms {c : Configured} {o : List Nat} {n : Nat} {A A' : Nat → Arm}
    {r r' : List (Codes × List (OracleShape × Nat))} (h : packFrom c o n A = .ok r)
    (h' : packFrom c o n A' = .ok r') : r = r' := by
  unfold packFrom at h h'
  obtain ⟨⟨s, ch⟩, hc, h⟩ := exc_bind h
  obtain ⟨⟨s', ch'⟩, hc', h'⟩ := exc_bind h'
  obtain ⟨rfl, F2⟩ := calls_same hc hc'
  dsimp only at h h'
  obtain ⟨sends, hs, h⟩ := exc_bind h
  obtain ⟨sends', hs', h'⟩ := exc_bind h'
  obtain rfl : sends = sends' := Except.ok.inj (hs.symm.trans hs')
  rw [mapM_zip_like _ (fun a a' d (e : Like a a') => by
    obtain ⟨e1, e2, e3⟩ := e
    dsimp only
    rw [e1, e2, e3]) F2 sends] at h
  exact Except.ok.inj (h.symm.trans h')

/-- **THE ROWS DO NOT HANG ON THE ARMS**: where the second reading's text returns at two tables
of arms, it returns one value: the whole rows, every sampled shape with its radius among them. -/
theorem rows_no_arms (c : Configured) (o : List Nat) (n : Nat) {A A' : Nat → Arm}
    {r r' : List SendRow} (h : rowsFrom c o n A = .ok r) (h' : rowsFrom c o n A' = .ok r') :
    r = r' := by
  unfold rowsFrom at h h'
  obtain ⟨sends, hs, h⟩ := exc_bind h
  obtain ⟨sends', hs', h'⟩ := exc_bind h'
  obtain rfl : sends = sends' := Except.ok.inj (hs.symm.trans hs')
  obtain ⟨pack, hp, h⟩ := exc_bind h
  obtain ⟨pack', hp', h'⟩ := exc_bind h'
  obtain rfl : pack = pack' := pack_no_arms hp hp'
  exact Except.ok.inj (h.symm.trans h')

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.calls_same
#print axioms VerifiableInference.Desc.LinkJoin.pack_no_arms
#print axioms VerifiableInference.Desc.LinkJoin.rows_no_arms
#print axioms VerifiableInference.Desc.LinkJoin.nFrameA_sim
#print axioms VerifiableInference.Desc.LinkJoin.nArm_quiet
