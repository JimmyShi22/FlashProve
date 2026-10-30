-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/LooksK5.lean: AN ATTENTION SEGMENT's OWN ROUNDS (kind K5) HAND ON «THE
LEDGER's ARRAYS HAVE THE PLAN's SHAPES»: K5's share of the walk of
Johnson/Desc/First/Link/Law/LooksWalk.lean. A class, instances, theorems.

How. The hearing (`Att.P.hear`, Johnson/Desc/First/Att/K5AttentionKind.lean) is a do-block over four steps in
the
state monad `Att.P.M` (the ledger, the rounds left, the lead). The ledger is written by two of them:
`take` (slots are taken; a run of hidings) and `sum` (the masked sumcheck's `hear` and `row`,
Johnson/Desc/Part/MaskedSum4.lean: slots are taken; a run of hidings each: `hear_spec`, `row_write`,
Johnson/Desc/Part/MaskedSumLedger.lean). A run of hidings leaves the arrays (`hideRun_core`).
  `StaysM x`: wherever x returns, its ledger has THE ARRAYS of the ledger that it was handed.
  `hear_arrays`: **of the whole hearing.**
  `hear5_reads`: the laying of what was heard leaves the ledger and the link's context.
  `k5_steps`: **(Att.P.attentionKind Att.P.seatSO claims p).Steps (KeepsLooks shOf)**; `k5_steps_at`: so of
    `k5AtN W l g before`'s value.
Limits. THE DECISION ALONE, AT THE SEAT seatSO: nothing on this sub-protocol's four runs of claims
(the batching's runs' share). Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.LooksWalk
import Johnson.Desc.First.Att.SeatN
import Johnson.Desc.Part.MaskedSumLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin.K5L
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (hideRun_core)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First.Att.P

variable {α β : Type}

/-- Wherever x returns, its ledger has the arrays of the ledger that it was handed. -/
class StaysM (x : M α) : Prop where
  same : ∀ {σ σ' : Fork × List Fmt.RoundView × ℕ} {a : α}, x σ = some (a, σ') → σ'.1.trees = σ.1.trees

theorem bindM_some {x : M α} {f : α → M β} {σ : Fork × List Fmt.RoundView × ℕ}
    {r : β × Fork × List Fmt.RoundView × ℕ} (h : (x >>= f) σ = some r) :
    ∃ a σ', x σ = some (a, σ') ∧ f a σ' = some r := by
  have h' : (x σ).bind (fun y => f y.1 y.2) = some r := h
  obtain ⟨y, h1, h2⟩ := Option.bind_eq_some_iff.1 h'
  exact ⟨y.1, y.2, h1, h2⟩

instance staysM_pure (a : α) : StaysM (pure a : M α) :=
  ⟨fun {σ σ' b} e => by
    have e' : some (a, σ) = some (b, σ') := e
    rw [← (Prod.mk.inj (Option.some.inj e')).2]⟩

theorem StaysM.bind {x : M α} {f : α → M β} (hx : StaysM x) (hf : ∀ a, StaysM (f a)) :
    StaysM (x >>= f) :=
  ⟨fun e => by
    obtain ⟨a, σ₁, h1, h2⟩ := bindM_some e
    exact ((hf a).same h2).trans (hx.same h1)⟩

instance staysM_bind (x : M α) (f : α → M β) [StaysM x] [∀ a, StaysM (f a)] : StaysM (x >>= f) :=
  StaysM.bind inferInstance inferInstance

instance staysM_failure : StaysM (failure : M α) := ⟨fun e => nomatch e⟩

/-- Walks a do-block: bind by bind, into each pattern. -/
local macro "staysM" : tactic =>
  `(tactic| repeat' first
    | infer_instance
    | refine StaysM.bind ?_ ?_
    | intro _
    | split)

theorem staysM_mapM_list {γ : Type} {f : γ → M β} (hf : ∀ a, StaysM (f a)) :
    ∀ l : List γ, StaysM (l.mapM f)
  | [] => by
    rw [List.mapM_nil]
    infer_instance
  | a :: l => by
    rw [List.mapM_cons]
    exact StaysM.bind (hf a) fun _ => StaysM.bind (staysM_mapM_list hf l) fun _ => inferInstance

theorem staysM_mapM_array {γ : Type} {f : γ → M β} (hf : ∀ a, StaysM (f a)) (l : Array γ) :
    StaysM (l.mapM f) := by
  rw [Array.mapM_eq_mapM_toList]
  haveI := staysM_mapM_list hf l.toList
  rw [map_eq_pure_bind]
  infer_instance

/-- n waiting scalars get the next n numbers. -/
instance staysM_take (n : ℕ) : StaysM (take n) :=
  ⟨fun {σ σ' a} e => by
    obtain ⟨F, rs, lead⟩ := σ
    unfold take at e
    cases rs with
    | nil => exact nomatch e
    | cons r rest =>
      obtain ⟨v, _, e⟩ := Option.bind_eq_some_iff.1 e
      obtain ⟨_, _, e⟩ := Option.bind_eq_some_iff.1 e
      obtain ⟨G, hG, e⟩ := Option.bind_eq_some_iff.1 e
      rw [← (Prod.mk.inj (Option.some.inj e)).2]
      exact (hideRun_core hG).trees⟩

theorem msHear_arrays {C : Aff} {k : MaskedSum.Call} {F G : Fork} {rs : List Fmt.RoundView}
    {h : MaskedSum.Heard} (hh : MaskedSum.hear C k F rs = some (h, G)) : G.trees = F.trees := by
  obtain ⟨_, _, R, _, _, _, hG⟩ := MaskedSum.hear_spec hh
  exact (hideRun_core hG).trees

theorem msRow_arrays {h : MaskedSum.Heard} {S0 : E} {kept f : Aff} {F G : Fork}
    (hr : MaskedSum.row h S0 kept F = some (f, G)) : G.trees = F.trees :=
  (hideRun_core (MaskedSum.row_write hr)).trees

/-- A masked sumcheck. -/
instance staysM_sum (C : Aff) (st : First.Att.P.Stage) : StaysM (sum C st) :=
  ⟨fun {σ σ' a} e => by
    obtain ⟨F, rs, lead⟩ := σ
    unfold sum at e
    cases st with
    | sum vs en =>
      obtain ⟨x, h1, e⟩ := Option.bind_eq_some_iff.1 e
      obtain ⟨h, G⟩ := x
      obtain ⟨y, h2, e⟩ := Option.bind_eq_some_iff.1 e
      obtain ⟨f, G'⟩ := y
      rw [← (Prod.mk.inj (Option.some.inj e)).2]
      exact (msRow_arrays h2).trans (msHear_arrays h1)
    | scalars n => exact nomatch e
    | batch n => exact nomatch e
    | point n => exact nomatch e⟩

/-- The round is closed. -/
instance staysM_close (n : ℕ) : StaysM (close n) :=
  ⟨fun {σ σ' a} e => by
    obtain ⟨F, rs, lead⟩ := σ
    unfold close at e
    cases rs with
    | nil => exact nomatch e
    | cons r rest =>
      dsimp only at e
      split at e
      · rw [← (Prod.mk.inj (Option.some.inj e)).2]
      · exact nomatch e⟩

instance staysM_batch (rows : ℕ) : StaysM (batch rows) := by
  unfold batch
  staysM

/-- **The whole hearing.** -/
instance staysM_hear (x : Params.AttentionRounds) : StaysM (hear x) := by
  unfold hear
  refine StaysM.bind (staysM_mapM_array (fun _ => inferInstance) _) fun _ => ?_
  refine StaysM.bind (staysM_mapM_array (fun _ => by staysM) _) fun _ => ?_
  staysM

theorem hear_arrays {x : Params.AttentionRounds} {F G : Fork} {rs rest : List Fmt.RoundView} {n m : ℕ}
    {h : Heard} (e : hear x (F, rs, n) = some (h, G, rest, m)) : G.trees = F.trees :=
  (staysM_hear x).same e

end VerifiableInference.Desc.LinkJoin.K5L

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att.P (attentionKind seatSO k5AtN)

/-- The laying of what was heard leaves the ledger and the link's context. -/
theorem hear5_reads {s t : S} {h : First.Att.P.Heard} (e : s.hear5? h = .ok t) :
    t.fork? = s.fork? ∧ t.link? = s.link? := by
  unfold S.hear5? at e
  obtain ⟨rfl, hf⟩ := (S.unmarked_ok _ _).1 e
  unfold S.hear5 at hf ⊢
  split
  · rename_i a ha
    split
    · constructor <;> unfold S.mark <;> split <;> rfl
    · constructor
      · simp [S.fork?, ha]
      · simp [S.link?, ha]
  · constructor <;> unfold S.mark <;> split <;> rfl

/-- **K5: an attention segment's own rounds.** -/
theorem k5_steps {Cl : Type} (shOf : ℕ → List Look)
    (claims : List (String × (ℕ → S → Except String (List Cl × S)))) (p : First.Att.P.Par) :
    (attentionKind seatSO claims p).Steps (KeepsLooks shOf) := by
  intro s rs gs s' h
  have h' : First.Att.P.decide seatSO p s rs = .ok s' := h
  unfold First.Att.P.decide at h'
  obtain ⟨_, _, h'⟩ := K9L.ok_bind h'
  obtain ⟨F, hF, h'⟩ := K9L.ok_bind h'
  obtain ⟨x, hx, h'⟩ := K9L.ok_bind h'
  obtain ⟨hd, G, rest, m⟩ := x
  obtain ⟨_, _, h'⟩ := K9L.ok_bind h'
  have hear1 : First.Att.P.hear p.own (F, rs, 0) = some (hd, G, rest, m) := by
    cases e : First.Att.P.hear p.own (F, rs, 0) with
    | none =>
      rw [e] at hx
      exact nomatch hx
    | some y =>
      rw [e] at hx
      exact congrArg some (Except.ok.inj hx)
  have lay1 : seatSO.lay s hd G = some s' := by
    cases e : seatSO.lay s hd G with
    | none =>
      rw [e] at h'
      exact nomatch h'
    | some y =>
      rw [e] at h'
      exact congrArg some (Except.ok.inj h')
  have led1 : seatSO.ledger s = some F := by
    cases e : seatSO.ledger s with
    | none =>
      rw [e] at hF
      exact nomatch hF
    | some y =>
      rw [e] at hF
      exact congrArg some (Except.ok.inj hF)
  unfold seatSO at lay1 led1
  dsimp only at lay1 led1
  cases hh : s.here with
  | att a =>
    rw [hh] at lay1 led1
    obtain rfl : a.F = F := Option.some.inj led1
    obtain ⟨_, _, lay2⟩ := Option.bind_eq_some_iff.1 lay1
    have lay3 : S.hear5? { s with rowsOwed := none, here := .att { a with F := G } } hd = .ok s' :=
        by
      cases e : S.hear5? { s with rowsOwed := none, here := .att { a with F := G } } hd with
      | error w =>
        rw [e] at lay2
        exact nomatch lay2
      | ok y =>
        rw [e] at lay2
        exact congrArg Except.ok (Option.some.inj lay2)
    obtain ⟨r1, r2⟩ := hear5_reads lay3
    refine keeps_of_cases shOf fun G' L' hG hL' => Or.inr ⟨a.F, a.L, ?_, ?_, ?_, ?_⟩
    · simp [S.fork?, hh]
    · simp [S.link?, hh]
    · rw [r2] at hL'
      exact congrArg (·.link) (Option.some.inj hL')
    · rw [r1] at hG
      rw [← Option.some.inj hG]
      exact congrArg (·.map look) (K5L.hear_arrays hear1)
  | lay a =>
    rw [hh] at led1
    exact nomatch led1
  | head a =>
    rw [hh] at led1
    exact nomatch led1
  | between =>
    rw [hh] at led1
    exact nomatch led1
  | fin a =>
    rw [hh] at led1
    exact nomatch led1
  | mem a =>
    rw [hh] at led1
    exact nomatch led1

/-- So of `k5AtN`'s value. -/
theorem k5_steps_at (shOf : ℕ → List Look) {W : Verify.Public} {l g : ℕ}
    {before : List (ℕ × ℕ)} {b : Block S Claim} (h : k5AtN W l g before = some b) :
    b.Steps (KeepsLooks shOf) := by
  unfold k5AtN at h
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  intro s rs gs s' hd
  exact k5_steps (Cl := Claim) shOf (First.Att.P.runsN p) _ s rs gs s' hd

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.K5L.hear_arrays
#print axioms VerifiableInference.Desc.LinkJoin.hear5_reads
#print axioms VerifiableInference.Desc.LinkJoin.k5_steps
#print axioms VerifiableInference.Desc.LinkJoin.k5_steps_at
