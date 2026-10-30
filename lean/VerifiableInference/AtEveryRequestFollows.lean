-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/AtEveryRequestFollows.lean: zero knowledge on the served requests gives zero knowledge at every request.

1.  WHAT IS CLAIMED: ZeroKnowledgeFollowsFromOn (VerifiableInference/AtEveryRequestGuards.lean), of ANY argument system, at the same error:
    where the output of a served request is the model's and the prover's answer at a refused request is one fixed proof.
2.  THE SIMULATOR: the given one at a served request; told «refused», it hands the fixed proof and keeps its state.
3.  HOW: from a chooser and a verifier that may ask refused requests, wrap makes ones that ask served requests alone: the refused replies are
    answered inside. replay lays these replies back into the view. Both experiments at every request are the experiments of the wrapped
    pair, read through replay; so the distance is not larger, and replay adds no query to the log.
4.  A refused reply uses up one of the proofs that may be asked; wrap counts them, so the wrapped verifier asks no more than proofCount.
-/
import VerifiableInference.AtEveryRequestGuards

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.AtEveryRequest

open scoped ENNReal

section Words
variable {Proof : Type} (chooser : View Proof → Option Request) (served : Request → Bool) (noProof : Proof)

/-- Walk the verifier's tree over what a view of the wrapped verifier holds, and lay the refused replies back. -/
def replay : MaliciousVerifier Proof → ℕ → View Proof → QueryLog → List ℕ → List (Request × Proof) → View Proof
  | .stop, _, view, _, _, _ => view
  | .query _ next, remaining, view, log, draws, proofs =>
      match log with
      | [] => view
      | entry :: log' =>
        replay (next entry.2) remaining { view with queryLog := view.queryLog ++ [entry] } log' draws proofs
  | .sample bound next, remaining, view, log, draws, proofs =>
      match draws with
      | [] => view
      | draw :: draws' =>
        if h : draw < bound + 1 then
          replay (next ⟨draw, h⟩) remaining { view with randomDraws := view.randomDraws ++ [draw] } log draws' proofs
        else view
  | .requestProof _, 0, view, _, _, _ => view
  | .requestProof next, remaining + 1, view, log, draws, proofs =>
      match chooser view with
      | none => view
      | some request =>
        if served request then
          match proofs with
          | [] => view
          | entry :: proofs' =>
            replay (next entry.1 entry.2) remaining { view with proofs := view.proofs ++ [entry] } log draws proofs'
        else
          replay (next request noProof) remaining { view with proofs := view.proofs ++ [(request, noProof)] } log draws
            proofs

/-- The verifier that asks served requests alone: it answers the refused ones itself. -/
def wrap : MaliciousVerifier Proof → ℕ → View Proof → MaliciousVerifier Proof
  | .stop, _, _ => .stop
  | .query input next, remaining, view =>
      .query input fun answer =>
        wrap (next answer) remaining { view with queryLog := view.queryLog ++ [(input, answer)] }
  | .sample bound next, remaining, view =>
      .sample bound fun draw =>
        wrap (next draw) remaining { view with randomDraws := view.randomDraws ++ [draw.val] }
  | .requestProof _, 0, _ => .stop
  | .requestProof next, remaining + 1, view =>
      match chooser view with
      | none => .stop
      | some request =>
        if served request then
          .requestProof fun asked proof =>
            wrap (next asked proof) remaining { view with proofs := view.proofs ++ [(asked, proof)] }
        else
          wrap (next request noProof) remaining { view with proofs := view.proofs ++ [(request, noProof)] }

theorem wrap_queryBound : ∀ (verifier : MaliciousVerifier Proof) (remaining : ℕ) (view : View Proof) (queries : ℕ),
    verifier.QueryBound queries → (wrap chooser served noProof verifier remaining view).QueryBound queries
  | .stop, _, _, _, _ => trivial
  | .query _ _, _, _, 0, h => h
  | .query _ next, remaining, view, queries + 1, h => fun answer =>
      wrap_queryBound (next answer) remaining _ queries (h answer)
  | .sample _ next, remaining, view, queries, h => fun draw =>
      wrap_queryBound (next draw) remaining _ queries (h draw)
  | .requestProof _, 0, _, _, _ => trivial
  | .requestProof next, remaining + 1, view, queries, h => by
      show (wrap chooser served noProof (.requestProof next) (remaining + 1) view).QueryBound queries
      simp only [wrap]
      cases chooser view with
      | none => exact trivial
      | some request =>
        by_cases hs : served request = true
        · simp only [hs, if_true]
          exact fun asked proof => wrap_queryBound (next asked proof) remaining _ queries (h asked proof)
        · simp only [hs]
          exact wrap_queryBound (next request noProof) remaining _ queries (h request noProof)

theorem replay_sample (bound : ℕ) (next : Fin (bound + 1) → MaliciousVerifier Proof) (remaining : ℕ) (view : View Proof)
    (log : QueryLog) (draw : Fin (bound + 1)) (draws : List ℕ) (proofs : List (Request × Proof)) :
    replay chooser served noProof (.sample bound next) remaining view log (draw.val :: draws) proofs =
      replay chooser served noProof (next draw) remaining { view with randomDraws := view.randomDraws ++ [draw.val] }
        log draws proofs := by
  simp only [replay]
  rw [dif_pos draw.isLt]

theorem replay_served (next : Request → Proof → MaliciousVerifier Proof) (remaining : ℕ) (view : View Proof)
    (log : QueryLog) (draws : List ℕ) (request : Request) (hc : chooser view = some request)
    (hs : served request = true) (entry : Request × Proof) (proofs : List (Request × Proof)) :
    replay chooser served noProof (.requestProof next) (remaining + 1) view log draws (entry :: proofs) =
      replay chooser served noProof (next entry.1 entry.2) remaining { view with proofs := view.proofs ++ [entry] }
        log draws proofs := by
  simp only [replay, hc, hs, if_true]

theorem replay_served_nil (next : Request → Proof → MaliciousVerifier Proof) (remaining : ℕ) (view : View Proof)
    (log : QueryLog) (draws : List ℕ) (request : Request) (hc : chooser view = some request)
    (hs : served request = true) :
    replay chooser served noProof (.requestProof next) (remaining + 1) view log draws [] = view := by
  simp only [replay, hc, hs, if_true]

theorem replay_refused (next : Request → Proof → MaliciousVerifier Proof) (remaining : ℕ) (view : View Proof)
    (log : QueryLog) (draws : List ℕ) (request : Request) (hc : chooser view = some request)
    (hs : served request = false) (proofs : List (Request × Proof)) :
    replay chooser served noProof (.requestProof next) (remaining + 1) view log draws proofs =
      replay chooser served noProof (next request noProof) remaining
        { view with proofs := view.proofs ++ [(request, noProof)] } log draws proofs := by
  cases proofs <;> simp only [replay, hc, hs, Bool.false_eq_true, if_false]

theorem replay_none (next : Request → Proof → MaliciousVerifier Proof) (remaining : ℕ) (view : View Proof)
    (log : QueryLog) (draws : List ℕ) (proofs : List (Request × Proof)) (hc : chooser view = none) :
    replay chooser served noProof (.requestProof next) (remaining + 1) view log draws proofs = view := by
  cases proofs <;> simp only [replay, hc]

/-- replay's log holds what the view and the list hold. -/
theorem replay_log : ∀ (verifier : MaliciousVerifier Proof) (remaining : ℕ) (view : View Proof) (log : QueryLog)
    (draws : List ℕ) (proofs : List (Request × Proof)) (entry : BitString × Digest),
    entry ∈ (replay chooser served noProof verifier remaining view log draws proofs).queryLog →
      entry ∈ view.queryLog ∨ entry ∈ log
  | .stop, _, _, _, _, _, _, h => Or.inl h
  | .query _ _, _, _, [], _, _, _, h => Or.inl h
  | .query _ next, remaining, view, first :: log, draws, proofs, entry, h => by
      rcases replay_log (next first.2) remaining _ log draws proofs entry h with h' | h'
      · rcases List.mem_append.1 h' with h'' | h''
        · exact Or.inl h''
        · exact Or.inr (List.mem_cons.2 (Or.inl (List.mem_singleton.1 h'')))
      · exact Or.inr (List.mem_cons_of_mem _ h')
  | .sample _ _, _, _, _, [], _, _, h => Or.inl h
  | .sample bound next, remaining, view, log, draw :: draws, proofs, entry, h => by
      by_cases hd : draw < bound + 1
      · have e := replay_sample chooser served noProof bound next remaining view log ⟨draw, hd⟩ draws proofs
        rw [show (⟨draw, hd⟩ : Fin (bound + 1)).val = draw from rfl] at e
        rw [e] at h
        have e' := replay_log (next ⟨draw, hd⟩) remaining _ log draws proofs entry h
        exact e'
      · have e : replay chooser served noProof (.sample bound next) remaining view log (draw :: draws) proofs = view := by
          simp only [replay]
          rw [dif_neg hd]
        rw [e] at h
        exact Or.inl h
  | .requestProof _, 0, _, _, _, _, _, h => Or.inl h
  | .requestProof next, remaining + 1, view, log, draws, proofs, entry, h => by
      cases hc : chooser view with
      | none =>
        rw [replay_none chooser served noProof next remaining view log draws proofs hc] at h
        exact Or.inl h
      | some request =>
        cases hs : served request with
        | true =>
          cases proofs with
          | nil =>
            rw [replay_served_nil chooser served noProof next remaining view log draws request hc hs] at h
            exact Or.inl h
          | cons first rest =>
            rw [replay_served chooser served noProof next remaining view log draws request hc hs first rest] at h
            have e' := replay_log (next first.1 first.2) remaining _ log draws rest entry h
            exact e'
        | false =>
          rw [replay_refused chooser served noProof next remaining view log draws request hc hs proofs] at h
          have e' := replay_log (next request noProof) remaining _ log draws proofs entry h
          exact e'

theorem wrap_none (next : Request → Proof → MaliciousVerifier Proof) (remaining : ℕ) (view : View Proof)
    (hc : chooser view = none) :
    wrap chooser served noProof (.requestProof next) (remaining + 1) view = .stop := by
  simp only [wrap, hc]

theorem wrap_served (next : Request → Proof → MaliciousVerifier Proof) (remaining : ℕ) (view : View Proof)
    (request : Request) (hc : chooser view = some request) (hs : served request = true) :
    wrap chooser served noProof (.requestProof next) (remaining + 1) view =
      .requestProof fun asked proof =>
        wrap chooser served noProof (next asked proof) remaining { view with proofs := view.proofs ++ [(asked, proof)] } := by
  simp only [wrap, hc, hs, if_true]

theorem wrap_refused (next : Request → Proof → MaliciousVerifier Proof) (remaining : ℕ) (view : View Proof)
    (request : Request) (hc : chooser view = some request) (hs : served request = false) :
    wrap chooser served noProof (.requestProof next) (remaining + 1) view =
      wrap chooser served noProof (next request noProof) remaining
        { view with proofs := view.proofs ++ [(request, noProof)] } := by
  simp only [wrap, hc, hs]
  rfl

variable (verifier : Commitment → MaliciousVerifier Proof) (proofCount : ℕ)

/-- The view at every request, out of the view of the wrapped verifier. -/
def outerView (inner : View Proof) : View Proof :=
  replay chooser served noProof (verifier inner.commitment) proofCount ⟨inner.commitment, [], [], []⟩
    inner.queryLog inner.randomDraws inner.proofs

/-- The chooser of the wrapped verifier: the given one at the view read back; served requests alone. -/
def innerChooser (inner : View Proof) : Option Request :=
  match chooser (outerView chooser served noProof verifier proofCount inner) with
  | none => none
  | some request => if served request then some request else none

/-- The wrapped verifier, at a commitment. -/
def innerVerifier (commitment : Commitment) : MaliciousVerifier Proof :=
  wrap chooser served noProof (verifier commitment) proofCount ⟨commitment, [], [], []⟩

/-- How the wrapped run stands to the run at every request. -/
structure Stands (commitment : Commitment) (tree : MaliciousVerifier Proof) (remaining : ℕ) (view inner : View Proof) :
    Prop where
  same : inner.commitment = commitment
  walk : ∀ log draws proofs,
    replay chooser served noProof (verifier commitment) proofCount ⟨commitment, [], [], []⟩
        (inner.queryLog ++ log) (inner.randomDraws ++ draws) (inner.proofs ++ proofs) =
      replay chooser served noProof tree remaining view log draws proofs

variable {chooser served noProof verifier proofCount}

theorem Stands.outer {commitment : Commitment} {tree : MaliciousVerifier Proof} {remaining : ℕ} {view inner : View Proof}
    (h : Stands chooser served noProof verifier proofCount commitment tree remaining view inner) :
    outerView chooser served noProof verifier proofCount inner =
      replay chooser served noProof tree remaining view [] [] [] := by
  have e := h.walk [] [] []
  simp only [List.append_nil] at e
  unfold outerView
  rw [h.same]
  exact e

theorem Stands.start (commitment : Commitment) :
    Stands chooser served noProof verifier proofCount commitment (verifier commitment) proofCount
      ⟨commitment, [], [], []⟩ ⟨commitment, [], [], []⟩ :=
  ⟨rfl, fun _ _ _ => rfl⟩

theorem Stands.query {commitment : Commitment} {input : BitString} {next : Digest → MaliciousVerifier Proof}
    {remaining : ℕ} {view inner : View Proof}
    (h : Stands chooser served noProof verifier proofCount commitment (.query input next) remaining view inner)
    (answer : Digest) :
    Stands chooser served noProof verifier proofCount commitment (next answer) remaining
      { view with queryLog := view.queryLog ++ [(input, answer)] }
      { inner with queryLog := inner.queryLog ++ [(input, answer)] } :=
  ⟨h.same, fun log draws proofs => by
    have e := h.walk ((input, answer) :: log) draws proofs
    simp only [List.append_assoc, List.singleton_append]
    exact e⟩

theorem Stands.sample {commitment : Commitment} {bound : ℕ} {next : Fin (bound + 1) → MaliciousVerifier Proof}
    {remaining : ℕ} {view inner : View Proof}
    (h : Stands chooser served noProof verifier proofCount commitment (.sample bound next) remaining view inner)
    (draw : Fin (bound + 1)) :
    Stands chooser served noProof verifier proofCount commitment (next draw) remaining
      { view with randomDraws := view.randomDraws ++ [draw.val] }
      { inner with randomDraws := inner.randomDraws ++ [draw.val] } :=
  ⟨h.same, fun log draws proofs => by
    have e := h.walk log (draw.val :: draws) proofs
    rw [replay_sample] at e
    simp only [List.append_assoc, List.singleton_append]
    exact e⟩

theorem Stands.atServed {commitment : Commitment} {next : Request → Proof → MaliciousVerifier Proof}
    {remaining : ℕ} {view inner : View Proof} {request : Request}
    (h : Stands chooser served noProof verifier proofCount commitment (.requestProof next) (remaining + 1) view inner)
    (hc : chooser view = some request) (hs : served request = true) (entry : Request × Proof) :
    Stands chooser served noProof verifier proofCount commitment (next entry.1 entry.2) remaining
      { view with proofs := view.proofs ++ [entry] } { inner with proofs := inner.proofs ++ [entry] } :=
  ⟨h.same, fun log draws proofs => by
    have e := h.walk log draws (entry :: proofs)
    rw [replay_served chooser served noProof next remaining view log draws request hc hs] at e
    simp only [List.append_assoc, List.singleton_append]
    exact e⟩

theorem Stands.refused {commitment : Commitment} {next : Request → Proof → MaliciousVerifier Proof}
    {remaining : ℕ} {view inner : View Proof} {request : Request}
    (h : Stands chooser served noProof verifier proofCount commitment (.requestProof next) (remaining + 1) view inner)
    (hc : chooser view = some request) (hs : served request = false) :
    Stands chooser served noProof verifier proofCount commitment (next request noProof) remaining
      { view with proofs := view.proofs ++ [(request, noProof)] } inner :=
  ⟨h.same, fun log draws proofs => (h.walk log draws proofs).trans
    (replay_refused chooser served noProof next remaining view log draws request hc hs proofs)⟩

/-- Where the run stands at a served request, the wrapped chooser picks it. -/
theorem Stands.chooses {commitment : Commitment} {next : Request → Proof → MaliciousVerifier Proof}
    {remaining : ℕ} {view inner : View Proof} {request : Request}
    (h : Stands chooser served noProof verifier proofCount commitment (.requestProof next) (remaining + 1) view inner)
    (hc : chooser view = some request) (hs : served request = true) :
    innerChooser chooser served noProof verifier proofCount inner = some request := by
  have e : outerView chooser served noProof verifier proofCount inner = view :=
    h.outer.trans (replay_served_nil chooser served noProof next remaining view [] [] request hc hs)
  unfold innerChooser
  rw [e, hc]
  simp only [hs, if_true]

end Words

/-- A law all of whose values are one value is that value. -/
theorem pmf_eq_pure {α : Type} (p : PMF α) (a : α) (h : ∀ b, p b ≠ 0 → b = a) : p = PMF.pure a := by
  have hs : p.support = {a} := by
    refine Set.eq_singleton_iff_nonempty_unique_mem.2 ⟨p.support_nonempty, fun b hb => h b ?_⟩
    exact (PMF.mem_support_iff _ _).1 hb
  have h1 : p a = 1 := (PMF.apply_eq_one_iff p a).2 hs
  ext b
  by_cases hb : b = a
  · subst hb
    simp [h1]
  · have h0 : p b = 0 := by
      by_contra hn
      exact hb (h b hn)
    simp [h0, hb]

section Real
variable (system : ArgumentSystem) (outcome : system.Weights → Request → Outcome) (noProof : system.Proof)
  (chooser : View system.Proof → Option Request) (verifier : Commitment → MaliciousVerifier system.Proof)
  (proofCount : ℕ) (weights : system.Weights)

/-- Is the request served at these weights? -/
def servedAt (request : Request) : Bool := decide (outcome weights request = .served)

/-- The distribution of a composition, written with `>>=`. -/
theorem run_monadBind {α β : Type} (hash : Hash) (first : RandomizedAlgorithm α)
    (rest : α → RandomizedAlgorithm β) :
    (first >>= rest).run hash = (first.run hash).bind fun result => (rest result).run hash :=
  run_bind hash first rest

local notation "𝔖" => servedAt system outcome weights
local notation "ℭ" => innerChooser chooser (servedAt system outcome weights) noProof verifier proofCount
local notation "𝔒" => outerView chooser (servedAt system outcome weights) noProof verifier proofCount

theorem refused_of_served_false {request : Request} (h : 𝔖 request = false) : outcome weights request = .refused := by
  cases e : outcome weights request with
  | served => exact absurd (decide_eq_true e) (by rw [show decide (outcome weights request = .served) = 𝔖 request from rfl, h]; simp)
  | refused => rfl

variable {system outcome noProof chooser verifier proofCount weights}

/-- **The real experiment at every request is the wrapped one, read back.** -/
theorem real_wrap (hN : HandsOutNoProof system (fun w r => outcome w r = .refused) (· = noProof)) (randomness : system.CommitmentRandomness)
    (hash : Hash) (commitment : Commitment) :
    ∀ (tree : MaliciousVerifier system.Proof) (remaining inner_remaining : ℕ) (view inner : View system.Proof),
      remaining ≤ inner_remaining →
      Stands chooser 𝔖 noProof verifier proofCount commitment tree remaining view inner →
      (realSteps system chooser weights randomness tree remaining view).run hash =
        ((realSteps system ℭ weights randomness (wrap chooser 𝔖 noProof tree remaining view) inner_remaining inner).run
          hash).map 𝔒
  | .stop, remaining, inner_remaining, view, inner, _, h => by
      show PMF.pure view = (PMF.pure inner).map _
      rw [PMF.pure_map, h.outer]
      rfl
  | .query input next, remaining, inner_remaining, view, inner, hr, h =>
      real_wrap hN randomness hash commitment (next (hash input)) remaining inner_remaining _ _ hr (h.query _)
  | .sample bound next, remaining, inner_remaining, view, inner, hr, h => by
      show ((PMF.uniformOfFintype (Fin (bound + 1))).bind fun draw => _) =
        ((PMF.uniformOfFintype (Fin (bound + 1))).bind fun draw => _).map _
      rw [PMF.map_bind]
      exact congrArg _ (funext fun draw =>
        real_wrap hN randomness hash commitment (next draw) remaining inner_remaining _ _ hr (h.sample draw))
  | .requestProof next, 0, inner_remaining, view, inner, _, h => by
      show PMF.pure view = ((realSteps system ℭ weights randomness .stop inner_remaining inner).run hash).map _
      show PMF.pure view = (PMF.pure inner).map _
      rw [PMF.pure_map, h.outer]
      rfl
  | .requestProof next, remaining + 1, inner_remaining, view, inner, hr, h => by
      cases hc : chooser view with
      | none =>
        rw [wrap_none _ _ _ _ _ _ hc]
        have e1 : realSteps system chooser weights randomness (.requestProof next) (remaining + 1) view = pure view := by
          simp only [realSteps, hc]
        rw [e1]
        show PMF.pure view = (PMF.pure inner).map _
        rw [PMF.pure_map, h.outer, replay_none _ _ _ _ _ _ _ _ _ hc]
      | some request =>
        cases hs : 𝔖 request with
        | true =>
          obtain ⟨m, rfl⟩ : ∃ m, inner_remaining = m + 1 := ⟨inner_remaining - 1, by omega⟩
          rw [wrap_served _ _ _ _ _ _ _ hc hs]
          have e1 : realSteps system chooser weights randomness (.requestProof next) (remaining + 1) view =
              (system.prove weights randomness request.1 request.2).bind fun proof =>
                realSteps system chooser weights randomness (next request proof) remaining
                  { view with proofs := view.proofs ++ [(request, proof)] } := by
            simp only [realSteps, hc]
          have e2 : realSteps system ℭ weights randomness (.requestProof fun asked proof =>
                wrap chooser 𝔖 noProof (next asked proof) remaining { view with proofs := view.proofs ++ [(asked, proof)] })
                (m + 1) inner =
              (system.prove weights randomness request.1 request.2).bind fun proof =>
                realSteps system ℭ weights randomness
                  (wrap chooser 𝔖 noProof (next request proof) remaining
                    { view with proofs := view.proofs ++ [(request, proof)] }) m
                  { inner with proofs := inner.proofs ++ [(request, proof)] } := by
            simp only [realSteps, h.chooses hc hs]
          rw [e1, e2, run_bind, run_bind, PMF.map_bind]
          exact congrArg _ (funext fun proof =>
            real_wrap hN randomness hash commitment (next request proof) remaining m _ _ (by omega)
              (h.atServed hc hs (request, proof)))
        | false =>
          rw [wrap_refused _ _ _ _ _ _ _ hc hs]
          have e1 : realSteps system chooser weights randomness (.requestProof next) (remaining + 1) view =
              (system.prove weights randomness request.1 request.2).bind fun proof =>
                realSteps system chooser weights randomness (next request proof) remaining
                  { view with proofs := view.proofs ++ [(request, proof)] } := by
            simp only [realSteps, hc]
          have e2 : (system.prove weights randomness request.1 request.2).run hash = PMF.pure noProof :=
            pmf_eq_pure _ _ fun form hf =>
              hN weights randomness request hash form (refused_of_served_false system outcome weights hs) hf
          rw [e1, run_bind, e2, PMF.pure_bind]
          exact real_wrap hN randomness hash commitment (next request noProof) remaining inner_remaining _ _
            (by omega) (h.refused hc hs)

/-- **The simulator at every request**: told «refused» it hands the fixed proof and keeps its state. -/
def simulatorOf (start : _root_.VerifiableInference.Simulator system.PublicParameters system.Proof) :
    Simulator system.PublicParameters Outcome system.Proof where
  State := start.State
  start := start.start
  answerQuery := start.answerQuery
  simulateProof := fun state request told =>
    match told with
    | .served => start.simulateProof state request
    | .refused => PMF.pure (noProof, state)

/-- **The simulated experiment at every request is the wrapped one, read back.** -/
theorem simulated_wrap (S₀ : _root_.VerifiableInference.Simulator system.PublicParameters system.Proof)
    (commitment : Commitment) :
    ∀ (tree : MaliciousVerifier system.Proof) (remaining inner_remaining : ℕ) (view inner : View system.Proof)
      (state : S₀.State), remaining ≤ inner_remaining →
      Stands chooser 𝔖 noProof verifier proofCount commitment tree remaining view inner →
      simulatedSteps (simulatorOf (noProof := noProof) S₀) (outcome weights) chooser tree remaining view state =
        (_root_.VerifiableInference.simulatedSteps S₀ ℭ (wrap chooser 𝔖 noProof tree remaining view) inner_remaining
          inner state).map 𝔒
  | .stop, remaining, inner_remaining, view, inner, state, _, h => by
      show PMF.pure view = (PMF.pure inner).map _
      rw [PMF.pure_map, h.outer]
      rfl
  | .query input next, remaining, inner_remaining, view, inner, state, hr, h => by
      show ((S₀.answerQuery state input).bind fun answered => _) =
        ((S₀.answerQuery state input).bind fun answered => _).map _
      rw [PMF.map_bind]
      exact congrArg _ (funext fun answered =>
        simulated_wrap S₀ commitment (next answered.1) remaining inner_remaining _ _ _ hr (h.query _))
  | .sample bound next, remaining, inner_remaining, view, inner, state, hr, h => by
      show ((PMF.uniformOfFintype (Fin (bound + 1))).bind fun draw => _) =
        ((PMF.uniformOfFintype (Fin (bound + 1))).bind fun draw => _).map _
      rw [PMF.map_bind]
      exact congrArg _ (funext fun draw =>
        simulated_wrap S₀ commitment (next draw) remaining inner_remaining _ _ _ hr (h.sample draw))
  | .requestProof next, 0, inner_remaining, view, inner, state, _, h => by
      show PMF.pure view = (_root_.VerifiableInference.simulatedSteps S₀ ℭ .stop inner_remaining inner state).map _
      show PMF.pure view = (PMF.pure inner).map _
      rw [PMF.pure_map, h.outer]
      rfl
  | .requestProof next, remaining + 1, inner_remaining, view, inner, state, hr, h => by
      cases hc : chooser view with
      | none =>
        rw [wrap_none _ _ _ _ _ _ hc]
        have e1 : simulatedSteps (simulatorOf (noProof := noProof) S₀) (outcome weights) chooser (.requestProof next)
            (remaining + 1) view state = PMF.pure view := by
          simp only [simulatedSteps, hc]
        rw [e1]
        show PMF.pure view = (PMF.pure inner).map _
        rw [PMF.pure_map, h.outer, replay_none _ _ _ _ _ _ _ _ _ hc]
      | some request =>
        cases hs : 𝔖 request with
        | true =>
          obtain ⟨m, rfl⟩ : ∃ m, inner_remaining = m + 1 := ⟨inner_remaining - 1, by omega⟩
          have ho : outcome weights request = .served := of_decide_eq_true hs
          rw [wrap_served _ _ _ _ _ _ _ hc hs]
          have e1 : simulatedSteps (simulatorOf (noProof := noProof) S₀) (outcome weights) chooser (.requestProof next)
              (remaining + 1) view state =
              (S₀.simulateProof state request).bind fun simulated =>
                simulatedSteps (simulatorOf (noProof := noProof) S₀) (outcome weights) chooser (next request simulated.1)
                  remaining { view with proofs := view.proofs ++ [(request, simulated.1)] } simulated.2 := by
            simp only [simulatedSteps, hc, ho]
            rfl
          have e2 : _root_.VerifiableInference.simulatedSteps S₀ ℭ (.requestProof fun asked proof =>
                wrap chooser 𝔖 noProof (next asked proof) remaining { view with proofs := view.proofs ++ [(asked, proof)] })
                (m + 1) inner state =
              (S₀.simulateProof state request).bind fun simulated =>
                _root_.VerifiableInference.simulatedSteps S₀ ℭ
                  (wrap chooser 𝔖 noProof (next request simulated.1) remaining
                    { view with proofs := view.proofs ++ [(request, simulated.1)] }) m
                  { inner with proofs := inner.proofs ++ [(request, simulated.1)] } simulated.2 := by
            simp only [_root_.VerifiableInference.simulatedSteps, h.chooses hc hs]
          rw [e1, e2, PMF.map_bind]
          exact congrArg _ (funext fun simulated =>
            simulated_wrap S₀ commitment (next request simulated.1) remaining m _ _ _ (by omega)
              (h.atServed hc hs (request, simulated.1)))
        | false =>
          have ho : outcome weights request = .refused := refused_of_served_false system outcome weights hs
          rw [wrap_refused _ _ _ _ _ _ _ hc hs]
          have e1 : simulatedSteps (simulatorOf (noProof := noProof) S₀) (outcome weights) chooser (.requestProof next)
              (remaining + 1) view state =
              simulatedSteps (simulatorOf (noProof := noProof) S₀) (outcome weights) chooser (next request noProof)
                remaining { view with proofs := view.proofs ++ [(request, noProof)] } state := by
            simp only [simulatedSteps, hc, ho]
            exact PMF.pure_bind _ _
          rw [e1]
          exact simulated_wrap S₀ commitment (next request noProof) remaining inner_remaining _ _ _
            (by omega) (h.refused hc hs)

end Real

/-- **ZeroKnowledgeFollowsFromOn, of every argument system.** -/
theorem zeroKnowledgeFollowsFromOn (system : ArgumentSystem) (outcome : system.Weights → Request → Outcome)
    (noProof : system.Proof) : ZeroKnowledgeFollowsFromOn system outcome noProof := by
  intro hServed hN error hOn
  obtain ⟨S₀, hS₀⟩ := hOn
  refine ⟨simulatorOf (noProof := noProof) S₀, fun weights chooser _ queries verifier proofCount hQ => ?_⟩
  have hC : ∀ view prompt output,
      innerChooser chooser (servedAt system outcome weights) noProof verifier proofCount view = some (prompt, output) →
        servedRequests outcome weights prompt output ∧ system.IsModelOutput weights prompt output := by
    intro view prompt output h
    unfold innerChooser at h
    split at h
    · cases h
    · rename_i request _
      split at h
      · rename_i hs
        obtain rfl : request = (prompt, output) := Option.some.inj h
        have ho : outcome weights (prompt, output) = .served := of_decide_eq_true hs
        exact ⟨ho, hServed weights _ ho⟩
      · cases h
  obtain ⟨hsd, hcons⟩ := hS₀ weights _ hC queries
    (innerVerifier chooser (servedAt system outcome weights) noProof verifier proofCount) proofCount
    fun commitment => wrap_queryBound _ _ _ _ _ _ _ (hQ commitment)
  have hReal : ∀ hash, (realExperiment system verifier chooser weights proofCount).run hash =
      ((realExperiment system (innerVerifier chooser (servedAt system outcome weights) noProof verifier proofCount)
        (innerChooser chooser (servedAt system outcome weights) noProof verifier proofCount) weights proofCount).run
          hash).map (outerView chooser (servedAt system outcome weights) noProof verifier proofCount) := by
    intro hash
    unfold realExperiment
    simp only [run_monadBind, PMF.map_bind]
    refine congrArg _ (funext fun randomness => congrArg _ (funext fun commitment => ?_))
    exact real_wrap hN randomness hash commitment _ _ _ _ _ le_rfl (Stands.start commitment)
  have hSim : simulatedExperiment system (simulatorOf (noProof := noProof) S₀) outcome verifier chooser weights proofCount =
      (_root_.VerifiableInference.simulatedExperiment system S₀
        (innerVerifier chooser (servedAt system outcome weights) noProof verifier proofCount)
        (innerChooser chooser (servedAt system outcome weights) noProof verifier proofCount) weights proofCount).map
          (outerView chooser (servedAt system outcome weights) noProof verifier proofCount) := by
    show ((S₀.start (system.publicParameters weights) proofCount).bind fun started => _) =
      ((S₀.start (system.publicParameters weights) proofCount).bind fun started => _).map _
    rw [PMF.map_bind]
    exact congrArg _ (funext fun started =>
      simulated_wrap S₀ started.1 _ _ _ _ _ _ le_rfl (Stands.start started.1))
  have pRealE : ∀ E, Prob (realExperiment system verifier chooser weights proofCount) E =
      Prob (realExperiment system (innerVerifier chooser (servedAt system outcome weights) noProof verifier proofCount)
        (innerChooser chooser (servedAt system outcome weights) noProof verifier proofCount) weights proofCount)
        (outerView chooser (servedAt system outcome weights) noProof verifier proofCount ⁻¹' E) := by
    intro E
    unfold Prob eventProbability
    simp only [hReal, PMF.toOuterMeasure_map_apply]
  have pSimE : ∀ E, eventProbability (simulatedExperiment system (simulatorOf (noProof := noProof) S₀) outcome verifier chooser
        weights proofCount) E =
      eventProbability (_root_.VerifiableInference.simulatedExperiment system S₀
        (innerVerifier chooser (servedAt system outcome weights) noProof verifier proofCount)
        (innerChooser chooser (servedAt system outcome weights) noProof verifier proofCount) weights proofCount)
        (outerView chooser (servedAt system outcome weights) noProof verifier proofCount ⁻¹' E) := by
    intro E
    unfold eventProbability
    rw [hSim, PMF.toOuterMeasure_map_apply]
  refine ⟨?_, ?_⟩
  · refine le_trans (iSup_le fun E => ?_) hsd
    rw [pRealE, pSimE]
    exact le_iSup (fun F => max
      (Prob (realExperiment system (innerVerifier chooser (servedAt system outcome weights) noProof verifier proofCount)
        (innerChooser chooser (servedAt system outcome weights) noProof verifier proofCount) weights proofCount) F -
        eventProbability (_root_.VerifiableInference.simulatedExperiment system S₀
          (innerVerifier chooser (servedAt system outcome weights) noProof verifier proofCount)
          (innerChooser chooser (servedAt system outcome weights) noProof verifier proofCount) weights proofCount) F)
      (eventProbability (_root_.VerifiableInference.simulatedExperiment system S₀
          (innerVerifier chooser (servedAt system outcome weights) noProof verifier proofCount)
          (innerChooser chooser (servedAt system outcome weights) noProof verifier proofCount) weights proofCount) F -
        Prob (realExperiment system (innerVerifier chooser (servedAt system outcome weights) noProof verifier proofCount)
          (innerChooser chooser (servedAt system outcome weights) noProof verifier proofCount) weights proofCount) F)) _
  · rw [pSimE]
    refine le_antisymm (le_trans (MeasureTheory.measure_mono fun inner hi => ?_) (le_of_eq hcons)) (zero_le _)
    intro hcon
    refine hi fun input answer answer' h1 h2 => ?_
    have aux : ∀ entry, entry ∈ (outerView chooser (servedAt system outcome weights) noProof verifier proofCount
        inner).queryLog → entry ∈ inner.queryLog := fun entry he => by
      rcases replay_log _ _ _ _ _ _ _ _ _ entry he with h' | h'
      · cases h'
      · exact h'
    exact hcon input answer answer' (aux _ h1) (aux _ h2)

end VerifiableInference.AtEveryRequest

#print axioms VerifiableInference.AtEveryRequest.wrap_queryBound
#print axioms VerifiableInference.AtEveryRequest.replay_log
#print axioms VerifiableInference.AtEveryRequest.real_wrap
#print axioms VerifiableInference.AtEveryRequest.simulated_wrap
#print axioms VerifiableInference.AtEveryRequest.zeroKnowledgeFollowsFromOn
