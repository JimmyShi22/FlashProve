-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SlotsK5.lean: K5.
ONE OF FOURTEEN FILES THAT CARRY "THE OPEN LEDGER's TWO NUMBERS" (how many slots it has: ns; how
many coefficients its list LS has) ALONG THE FIRST CHAIN: `SlotsInv nsOf s`: where a ledger and a
link are open, the two numbers are the plan's nsOf at that link's number. Their top:
Johnson/LPFK9R/SlotsSeat.lean.
The walk is adapted from LooksK5.lean (beside this file): that file's theorems on the arrays' looks,
carried over by program to the two numbers, name by name (…looks… ↦ …slots…; else a letter S behind
the name), and righted by hand where the ground fact is another.
That file is imported for what it holds that does not speak of looks.
Limits. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LooksK5
import Johnson.Desc.First.Link.Law.LooksWalk
import Johnson.Desc.First.Link.Law.SlotsWalk
import Johnson.Desc.First.Att.SeatN
import Johnson.Desc.Part.MaskedSumLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin.K5S
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (hideRun_core)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc.LinkJoin.K5L (bindM_some)

variable {α β : Type}

/-- Wherever x returns, its ledger has the two numbers of the ledger that it was handed. -/
class StaysMS (x : M α) : Prop where
  same : ∀ {σ σ' : Fork × List Fmt.RoundView × ℕ} {a : α}, x σ = some (a, σ') → sl σ'.1 = sl σ.1

instance staysM_pureS (a : α) : StaysMS (pure a : M α) :=
  ⟨fun {σ σ' b} e => by
    have e' : some (a, σ) = some (b, σ') := e
    rw [← (Prod.mk.inj (Option.some.inj e')).2]⟩

theorem StaysMS.bind {x : M α} {f : α → M β} (hx : StaysMS x) (hf : ∀ a, StaysMS (f a)) :
    StaysMS (x >>= f) :=
  ⟨fun e => by
    obtain ⟨a, σ₁, h1, h2⟩ := bindM_some e
    exact ((hf a).same h2).trans (hx.same h1)⟩

instance staysM_bindS (x : M α) (f : α → M β) [StaysMS x] [∀ a, StaysMS (f a)] : StaysMS (x >>= f)
    :=
  StaysMS.bind inferInstance inferInstance

instance staysM_failureS : StaysMS (failure : M α) := ⟨fun e => nomatch e⟩

/-- Walks a do-block: bind by bind, into each pattern. -/
local macro "staysMS" : tactic =>
  `(tactic| repeat' first
    | infer_instance
    | refine StaysMS.bind ?_ ?_
    | intro _
    | split)

theorem staysM_mapM_listS {γ : Type} {f : γ → M β} (hf : ∀ a, StaysMS (f a)) :
    ∀ l : List γ, StaysMS (l.mapM f)
  | [] => by
    rw [List.mapM_nil]
    infer_instance
  | a :: l => by
    rw [List.mapM_cons]
    exact StaysMS.bind (hf a) fun _ => StaysMS.bind (staysM_mapM_listS hf l) fun _ => inferInstance

theorem staysM_mapM_arrayS {γ : Type} {f : γ → M β} (hf : ∀ a, StaysMS (f a)) (l : Array γ) :
    StaysMS (l.mapM f) := by
  rw [Array.mapM_eq_mapM_toList]
  haveI := staysM_mapM_listS hf l.toList
  rw [map_eq_pure_bind]
  infer_instance

/-- n waiting scalars get the next n numbers. -/
instance staysM_takeS (n : ℕ) : StaysMS (take n) :=
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
      exact (by have e := sl_core (hideRun_core hG); exact e)⟩

theorem msHear_slots {C : Aff} {k : MaskedSum.Call} {F G : Fork} {rs : List Fmt.RoundView}
    {h : MaskedSum.Heard} (hh : MaskedSum.hear C k F rs = some (h, G)) : sl G = sl F := by
  obtain ⟨_, _, R, _, _, _, hG⟩ := MaskedSum.hear_spec hh
  exact (by have e := sl_core (hideRun_core hG); exact e)

theorem msRow_slots {h : MaskedSum.Heard} {S0 : E} {kept f : Aff} {F G : Fork}
    (hr : MaskedSum.row h S0 kept F = some (f, G)) : sl G = sl F :=
  (by have e := sl_core (hideRun_core (MaskedSum.row_write hr)); exact e)

/-- A masked sumcheck. -/
instance staysM_sumS (C : Aff) (st : First.Att.P.Stage) : StaysMS (sum C st) :=
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
      exact (msRow_slots h2).trans (msHear_slots h1)
    | scalars n => exact nomatch e
    | batch n => exact nomatch e
    | point n => exact nomatch e⟩

/-- The round is closed. -/
instance staysM_closeS (n : ℕ) : StaysMS (close n) :=
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

instance staysM_batchS (rows : ℕ) : StaysMS (batch rows) := by
  unfold batch
  staysMS

/-- **The whole hearing.** -/
instance staysM_hearS (x : Params.AttentionRounds) : StaysMS (hear x) := by
  unfold hear
  refine StaysMS.bind (staysM_mapM_arrayS (fun _ => inferInstance) _) fun _ => ?_
  refine StaysMS.bind (staysM_mapM_arrayS (fun _ => by staysMS) _) fun _ => ?_
  staysMS

theorem hear_slots {x : Params.AttentionRounds} {F G : Fork} {rs rest : List Fmt.RoundView} {n m : ℕ}
    {h : Heard} (e : hear x (F, rs, n) = some (h, G, rest, m)) : sl G = sl F :=
  (staysM_hearS x).same e

end VerifiableInference.Desc.LinkJoin.K5S

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att.P (attentionKind seatSO k5AtN)

/-- **K5: an attention segment's own rounds.** -/
theorem k5_stepsS {Cl : Type} (nsOf : ℕ → ℕ × ℕ)
    (claims : List (String × (ℕ → S → Except String (List Cl × S)))) (p : First.Att.P.Par) :
    (attentionKind seatSO claims p).Steps (KeepsSlots nsOf) := by
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
    refine keeps_of_casesS nsOf fun G' L' hG hL' => Or.inr ⟨a.F, a.L, ?_, ?_, ?_, ?_⟩
    · simp [S.fork?, hh]
    · simp [S.link?, hh]
    · rw [r2] at hL'
      exact congrArg (·.link) (Option.some.inj hL')
    · rw [r1] at hG
      rw [← Option.some.inj hG]
      exact id (K5S.hear_slots hear1)
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
theorem k5_steps_atS (nsOf : ℕ → ℕ × ℕ) {W : Verify.Public} {l g : ℕ}
    {before : List (ℕ × ℕ)} {b : Block S Claim} (h : k5AtN W l g before = some b) :
    b.Steps (KeepsSlots nsOf) := by
  unfold k5AtN at h
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  intro s rs gs s' hd
  exact k5_stepsS (Cl := Claim) nsOf (First.Att.P.runsN p) _ s rs gs s' hd

end VerifiableInference.Desc.LinkJoin
