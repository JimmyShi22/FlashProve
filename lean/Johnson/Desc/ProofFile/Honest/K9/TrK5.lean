-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/TrK5.lean: K5, AN ATTENTION SEGMENT's OWN ROUNDS: an accepting decision is `KeepsTr`.

One of nine files (Honest/K9/TrAre.lean, TrFl, TrWalk, TrK4, TrK5, TrK6, TrSeated, TrVia, TrLot) that say of the sub-protocols
which stand between a segment's opening and its batching: an accepting decision leaves the ledger's arrays, but for the mark
"the commitment is received" (`tr`), and what the batching's draw will test of the segment's book-keeping (`lnk`). They are the
nine files Honest/K9/TrAre.lean to TrLot.lean, carried over by program from the reading `tr` to the reading `tr`, name by name;
these in turn carry the library's own walk for the ledger's two numbers (Johnson/Desc/First/Link/Law/FlSlots.lean and the files
Slots*.lean beside it).

Limits. One direction: from an accepting decision. Nothing on the runs of claims unless it is said. This file proves no property
of a prover or a protocol.
-/
import Johnson.Desc.First.Link.Law.LooksK5
import Johnson.Desc.First.Link.Law.LooksWalk
import Johnson.Desc.ProofFile.Honest.K9.TrWalk
import Johnson.Desc.First.Att.SeatN
import Johnson.Desc.Part.MaskedSumLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin.K5T
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (hideRun_core)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc.LinkJoin.K5L (bindM_some)

variable {α β : Type}

/-- Wherever x returns, its ledger has the reading of the ledger that it was handed. -/
class StaysMT (x : M α) : Prop where
  same : ∀ {σ σ' : Fork × List Fmt.RoundView × ℕ} {a : α}, x σ = some (a, σ') → tr σ'.1 = tr σ.1

instance staysM_pureT (a : α) : StaysMT (pure a : M α) :=
  ⟨fun {σ σ' b} e => by
    have e' : some (a, σ) = some (b, σ') := e
    rw [← (Prod.mk.inj (Option.some.inj e')).2]⟩

theorem StaysMT.bind {x : M α} {f : α → M β} (hx : StaysMT x) (hf : ∀ a, StaysMT (f a)) :
    StaysMT (x >>= f) :=
  ⟨fun e => by
    obtain ⟨a, σ₁, h1, h2⟩ := bindM_some e
    exact ((hf a).same h2).trans (hx.same h1)⟩

instance staysM_bindT (x : M α) (f : α → M β) [StaysMT x] [∀ a, StaysMT (f a)] : StaysMT (x >>= f)
    :=
  StaysMT.bind inferInstance inferInstance

instance staysM_failureT : StaysMT (failure : M α) := ⟨fun e => nomatch e⟩

/-- Walks a do-block: bind by bind, into each pattern. -/
local macro "staysMT" : tactic =>
  `(tactic| repeat' first
    | infer_instance
    | refine StaysMT.bind ?_ ?_
    | intro _
    | split)

theorem staysM_mapM_listT {γ : Type} {f : γ → M β} (hf : ∀ a, StaysMT (f a)) :
    ∀ l : List γ, StaysMT (l.mapM f)
  | [] => by
    rw [List.mapM_nil]
    infer_instance
  | a :: l => by
    rw [List.mapM_cons]
    exact StaysMT.bind (hf a) fun _ => StaysMT.bind (staysM_mapM_listT hf l) fun _ => inferInstance

theorem staysM_mapM_arrayT {γ : Type} {f : γ → M β} (hf : ∀ a, StaysMT (f a)) (l : Array γ) :
    StaysMT (l.mapM f) := by
  rw [Array.mapM_eq_mapM_toList]
  haveI := staysM_mapM_listT hf l.toList
  rw [map_eq_pure_bind]
  infer_instance

/-- n waiting scalars get the next n numbers. -/
instance staysM_takeT (n : ℕ) : StaysMT (take n) :=
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
      exact (by have e := tr_core (hideRun_core hG); exact e)⟩

theorem msHear_tr {C : Aff} {k : MaskedSum.Call} {F G : Fork} {rs : List Fmt.RoundView}
    {h : MaskedSum.Heard} (hh : MaskedSum.hear C k F rs = some (h, G)) : tr G = tr F := by
  obtain ⟨_, _, R, _, _, _, hG⟩ := MaskedSum.hear_spec hh
  exact (by have e := tr_core (hideRun_core hG); exact e)

theorem msRow_tr {h : MaskedSum.Heard} {S0 : E} {kept f : Aff} {F G : Fork}
    (hr : MaskedSum.row h S0 kept F = some (f, G)) : tr G = tr F :=
  (by have e := tr_core (hideRun_core (MaskedSum.row_write hr)); exact e)

/-- A masked sumcheck. -/
instance staysM_sumT (C : Aff) (st : First.Att.P.Stage) : StaysMT (sum C st) :=
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
      exact (msRow_tr h2).trans (msHear_tr h1)
    | scalars n => exact nomatch e
    | batch n => exact nomatch e
    | point n => exact nomatch e⟩

/-- The round is closed. -/
instance staysM_closeT (n : ℕ) : StaysMT (close n) :=
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

instance staysM_batchT (rows : ℕ) : StaysMT (batch rows) := by
  unfold batch
  staysMT

/-- **The whole hearing.** -/
instance staysM_hearT (x : Params.AttentionRounds) : StaysMT (hear x) := by
  unfold hear
  refine StaysMT.bind (staysM_mapM_arrayT (fun _ => inferInstance) _) fun _ => ?_
  refine StaysMT.bind (staysM_mapM_arrayT (fun _ => by staysMT) _) fun _ => ?_
  staysMT

theorem hear_tr {x : Params.AttentionRounds} {F G : Fork} {rs rest : List Fmt.RoundView} {n m : ℕ}
    {h : Heard} (e : hear x (F, rs, n) = some (h, G, rest, m)) : tr G = tr F :=
  (staysM_hearT x).same e

end VerifiableInference.Desc.LinkJoin.K5T

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att.P (attentionKind seatSO k5AtN)

/-- **K5: an attention segment's own rounds.** -/
theorem k5_stepsT {Cl : Type} (claims : List (String × (ℕ → S → Except String (List Cl × S)))) (p : First.Att.P.Par) :
    (attentionKind seatSO claims p).Steps (KeepsTr) := by
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
    refine keeps_of_casesT fun G' L' hG hL' => ⟨a.F, a.L, ?_, ?_, ?_, ?_⟩
    · simp [S.fork?, hh]
    · simp [S.link?, hh]
    · rw [r2] at hL'
      exact congrArg lnk (Option.some.inj hL')
    · rw [r1] at hG
      rw [← Option.some.inj hG]
      exact id (K5T.hear_tr hear1)
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
theorem k5_steps_atT {W : Verify.Public} {l g : ℕ}
    {before : List (ℕ × ℕ)} {b : Block S Claim} (h : k5AtN W l g before = some b) :
    b.Steps (KeepsTr) := by
  unfold k5AtN at h
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  intro s rs gs s' hd
  exact k5_stepsT (Cl := Claim) (First.Att.P.runsN p) _ s rs gs s' hd

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.K5T.staysM_pureT
#print axioms VerifiableInference.Desc.LinkJoin.K5T.StaysMT.bind
#print axioms VerifiableInference.Desc.LinkJoin.K5T.staysM_bindT
#print axioms VerifiableInference.Desc.LinkJoin.K5T.staysM_failureT
#print axioms VerifiableInference.Desc.LinkJoin.K5T.staysM_mapM_listT
#print axioms VerifiableInference.Desc.LinkJoin.K5T.staysM_mapM_arrayT
#print axioms VerifiableInference.Desc.LinkJoin.K5T.staysM_takeT
#print axioms VerifiableInference.Desc.LinkJoin.K5T.msHear_tr
#print axioms VerifiableInference.Desc.LinkJoin.K5T.msRow_tr
#print axioms VerifiableInference.Desc.LinkJoin.K5T.staysM_sumT
#print axioms VerifiableInference.Desc.LinkJoin.K5T.staysM_closeT
#print axioms VerifiableInference.Desc.LinkJoin.K5T.staysM_batchT
#print axioms VerifiableInference.Desc.LinkJoin.K5T.staysM_hearT
#print axioms VerifiableInference.Desc.LinkJoin.K5T.hear_tr
#print axioms VerifiableInference.Desc.LinkJoin.k5_stepsT
#print axioms VerifiableInference.Desc.LinkJoin.k5_steps_atT
