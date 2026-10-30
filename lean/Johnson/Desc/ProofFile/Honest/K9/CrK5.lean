-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/CrK5.lean: K5, AN ATTENTION SEGMENT's OWN ROUNDS: an accepting decision is `KeepsCr`.

One of nine files (Honest/K9/CrAre.lean, CrFl, CrWalk, CrK4, CrK5, CrK6, CrSeated, CrVia, CrLot) that say of the sub-protocols
which stand between a segment's opening and its batching: an accepting decision leaves what the batching's draw will test of the
ledger (`cr`) and of the segment's book-keeping (`lnk`). The walk through each sub-protocol's text is the library's own walk for
the ledger's two numbers (Johnson/Desc/First/Link/Law/FlSlots.lean and the files Slots*.lean beside it), carried over by program
to the reading `cr`, name by name, and righted by hand where the ground fact is another.

Limits. One direction: from an accepting decision. Nothing on the runs of claims unless it is said. This file proves no property
of a prover or a protocol.
-/
import Johnson.Desc.First.Link.Law.LooksK5
import Johnson.Desc.First.Link.Law.LooksWalk
import Johnson.Desc.ProofFile.Honest.K9.CrWalk
import Johnson.Desc.First.Att.SeatN
import Johnson.Desc.Part.MaskedSumLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin.K5C
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (hideRun_core)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc.LinkJoin.K5L (bindM_some)

variable {α β : Type}

/-- Wherever x returns, its ledger has the reading of the ledger that it was handed. -/
class StaysMC (x : M α) : Prop where
  same : ∀ {σ σ' : Fork × List Fmt.RoundView × ℕ} {a : α}, x σ = some (a, σ') → cr σ'.1 = cr σ.1

instance staysM_pureC (a : α) : StaysMC (pure a : M α) :=
  ⟨fun {σ σ' b} e => by
    have e' : some (a, σ) = some (b, σ') := e
    rw [← (Prod.mk.inj (Option.some.inj e')).2]⟩

theorem StaysMC.bind {x : M α} {f : α → M β} (hx : StaysMC x) (hf : ∀ a, StaysMC (f a)) :
    StaysMC (x >>= f) :=
  ⟨fun e => by
    obtain ⟨a, σ₁, h1, h2⟩ := bindM_some e
    exact ((hf a).same h2).trans (hx.same h1)⟩

instance staysM_bindC (x : M α) (f : α → M β) [StaysMC x] [∀ a, StaysMC (f a)] : StaysMC (x >>= f)
    :=
  StaysMC.bind inferInstance inferInstance

instance staysM_failureC : StaysMC (failure : M α) := ⟨fun e => nomatch e⟩

/-- Walks a do-block: bind by bind, into each pattern. -/
local macro "staysMC" : tactic =>
  `(tactic| repeat' first
    | infer_instance
    | refine StaysMC.bind ?_ ?_
    | intro _
    | split)

theorem staysM_mapM_listC {γ : Type} {f : γ → M β} (hf : ∀ a, StaysMC (f a)) :
    ∀ l : List γ, StaysMC (l.mapM f)
  | [] => by
    rw [List.mapM_nil]
    infer_instance
  | a :: l => by
    rw [List.mapM_cons]
    exact StaysMC.bind (hf a) fun _ => StaysMC.bind (staysM_mapM_listC hf l) fun _ => inferInstance

theorem staysM_mapM_arrayC {γ : Type} {f : γ → M β} (hf : ∀ a, StaysMC (f a)) (l : Array γ) :
    StaysMC (l.mapM f) := by
  rw [Array.mapM_eq_mapM_toList]
  haveI := staysM_mapM_listC hf l.toList
  rw [map_eq_pure_bind]
  infer_instance

/-- n waiting scalars get the next n numbers. -/
instance staysM_takeC (n : ℕ) : StaysMC (take n) :=
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
      exact (by have e := cr_core (hideRun_core hG); exact e)⟩

theorem msHear_cr {C : Aff} {k : MaskedSum.Call} {F G : Fork} {rs : List Fmt.RoundView}
    {h : MaskedSum.Heard} (hh : MaskedSum.hear C k F rs = some (h, G)) : cr G = cr F := by
  obtain ⟨_, _, R, _, _, _, hG⟩ := MaskedSum.hear_spec hh
  exact (by have e := cr_core (hideRun_core hG); exact e)

theorem msRow_cr {h : MaskedSum.Heard} {S0 : E} {kept f : Aff} {F G : Fork}
    (hr : MaskedSum.row h S0 kept F = some (f, G)) : cr G = cr F :=
  (by have e := cr_core (hideRun_core (MaskedSum.row_write hr)); exact e)

/-- A masked sumcheck. -/
instance staysM_sumC (C : Aff) (st : First.Att.P.Stage) : StaysMC (sum C st) :=
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
      exact (msRow_cr h2).trans (msHear_cr h1)
    | scalars n => exact nomatch e
    | batch n => exact nomatch e
    | point n => exact nomatch e⟩

/-- The round is closed. -/
instance staysM_closeC (n : ℕ) : StaysMC (close n) :=
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

instance staysM_batchC (rows : ℕ) : StaysMC (batch rows) := by
  unfold batch
  staysMC

/-- **The whole hearing.** -/
instance staysM_hearC (x : Params.AttentionRounds) : StaysMC (hear x) := by
  unfold hear
  refine StaysMC.bind (staysM_mapM_arrayC (fun _ => inferInstance) _) fun _ => ?_
  refine StaysMC.bind (staysM_mapM_arrayC (fun _ => by staysMC) _) fun _ => ?_
  staysMC

theorem hear_cr {x : Params.AttentionRounds} {F G : Fork} {rs rest : List Fmt.RoundView} {n m : ℕ}
    {h : Heard} (e : hear x (F, rs, n) = some (h, G, rest, m)) : cr G = cr F :=
  (staysM_hearC x).same e

end VerifiableInference.Desc.LinkJoin.K5C

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att.P (attentionKind seatSO k5AtN)

/-- **K5: an attention segment's own rounds.** -/
theorem k5_stepsC {Cl : Type} (claims : List (String × (ℕ → S → Except String (List Cl × S)))) (p : First.Att.P.Par) :
    (attentionKind seatSO claims p).Steps (KeepsCr) := by
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
    refine keeps_of_casesC fun G' L' hG hL' => ⟨a.F, a.L, ?_, ?_, ?_, ?_⟩
    · simp [S.fork?, hh]
    · simp [S.link?, hh]
    · rw [r2] at hL'
      exact congrArg lnk (Option.some.inj hL')
    · rw [r1] at hG
      rw [← Option.some.inj hG]
      exact id (K5C.hear_cr hear1)
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
theorem k5_steps_atC {W : Verify.Public} {l g : ℕ}
    {before : List (ℕ × ℕ)} {b : Block S Claim} (h : k5AtN W l g before = some b) :
    b.Steps (KeepsCr) := by
  unfold k5AtN at h
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  intro s rs gs s' hd
  exact k5_stepsC (Cl := Claim) (First.Att.P.runsN p) _ s rs gs s' hd

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.K5C.staysM_pureC
#print axioms VerifiableInference.Desc.LinkJoin.K5C.StaysMC.bind
#print axioms VerifiableInference.Desc.LinkJoin.K5C.staysM_bindC
#print axioms VerifiableInference.Desc.LinkJoin.K5C.staysM_failureC
#print axioms VerifiableInference.Desc.LinkJoin.K5C.staysM_mapM_listC
#print axioms VerifiableInference.Desc.LinkJoin.K5C.staysM_mapM_arrayC
#print axioms VerifiableInference.Desc.LinkJoin.K5C.staysM_takeC
#print axioms VerifiableInference.Desc.LinkJoin.K5C.msHear_cr
#print axioms VerifiableInference.Desc.LinkJoin.K5C.msRow_cr
#print axioms VerifiableInference.Desc.LinkJoin.K5C.staysM_sumC
#print axioms VerifiableInference.Desc.LinkJoin.K5C.staysM_closeC
#print axioms VerifiableInference.Desc.LinkJoin.K5C.staysM_batchC
#print axioms VerifiableInference.Desc.LinkJoin.K5C.staysM_hearC
#print axioms VerifiableInference.Desc.LinkJoin.K5C.hear_cr
#print axioms VerifiableInference.Desc.LinkJoin.k5_stepsC
#print axioms VerifiableInference.Desc.LinkJoin.k5_steps_atC
