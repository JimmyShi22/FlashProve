-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/Names/ArrNamesK5.lean: «THE OPEN LEDGER's ARRAYS HAVE THE PLAN's NAMES»: THE
KIND K5's SHARE. MADE BY PROGRAM FROM THE LIBRARY's Johnson/Desc/First/Link/Law/LooksK5.lean, WITH
AN ARRAY's NAME (`treeName`, Johnson/Desc/K8/Honest/Names/TreeName.lean) IN THE PLACE OF ITS LOOK:
every declaration of that file that the instance `seatKeeps_arrNames` (Names/ArrNamesSeat.lean)
wants and that names the looks, or leans on one that does, under a new name; the others are called
where they lie: that file is imported. NO NEW ARGUMENT: the library's proofs, token for token, but
for the turns that are named here. None of the library's goals.
Why. The smallness test's second computation asks that the digits' array bears the name "ZZ"
(`piecesTile`, OnBytes/Model/Tail.lean). The library carries each array's look (kind, rows, columns,
number of virtual rows) from the planned ledger to every reached state; a look holds no name. Spent
in Johnson/Desc/K8/Honest/NamesAtBatch.lean.
KEPT AND RENAMED (2): k5_steps → k5_stepsN · k5_steps_at → k5_steps_atN.
CALLED WHERE THEY LIE (17): StaysM · bindM_some · staysM_pure · StaysM.bind · staysM_bind ·
staysM_failure · staysM_mapM_list · staysM_mapM_array · staysM_take · msHear_arrays · msRow_arrays ·
staysM_sum · staysM_close · staysM_batch · staysM_hear · hear_arrays · hear5_reads.
THE GENERAL TURNS: look → treeName · Look → String · …looks… → …arrNames… · …Looks… → …ArrNames… ·
shOfBuilt → anOfBuilt · shOf_at → anOf_at · Stays → StaysN · the tactic stays → staysN · every other
kept name gets an N behind; the letter shOf stays, at the type ℕ → List String; in comments "look" →
"name". Lines over 100 signs are broken.
TURNED BY HAND: nothing.
Limits. ITS SOURCE's LIMITS ARE ITS OWN: one direction, from a yes or from a return; nothing says
that any state is reached. It is no second text of its source: it speaks of another field of an
array, and no law ties the two. The comments on the declarations are the source's, turned by the
same program: they were not written for this file. It stands in the source's own namespace, so that
every name resolves as there. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.First.Link.Law.LooksK5
import Johnson.Desc.K8.Honest.Names.TreeName
import Johnson.Desc.K8.Honest.Names.ArrNamesWalk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin.K5L
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (hideRun_core)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First.Att.P

variable {α β : Type}

end VerifiableInference.Desc.LinkJoin.K5L

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att.P (attentionKind seatSO k5AtN)

/-- **K5: an attention segment's own rounds.** -/
theorem k5_stepsN {Cl : Type} (shOf : ℕ → List String)
    (claims : List (String × (ℕ → S → Except String (List Cl × S)))) (p : First.Att.P.Par) :
    (attentionKind seatSO claims p).Steps (KeepsArrNames shOf) := by
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
    refine keeps_of_casesN shOf fun G' L' hG hL' => Or.inr ⟨a.F, a.L, ?_, ?_, ?_, ?_⟩
    · simp [S.fork?, hh]
    · simp [S.link?, hh]
    · rw [r2] at hL'
      exact congrArg (·.link) (Option.some.inj hL')
    · rw [r1] at hG
      rw [← Option.some.inj hG]
      exact congrArg (·.map treeName) (K5L.hear_arrays hear1)
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
theorem k5_steps_atN (shOf : ℕ → List String) {W : Verify.Public} {l g : ℕ}
    {before : List (ℕ × ℕ)} {b : Block S Claim} (h : k5AtN W l g before = some b) :
    b.Steps (KeepsArrNames shOf) := by
  unfold k5AtN at h
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  intro s rs gs s' hd
  exact k5_stepsN (Cl := Claim) shOf (First.Att.P.runsN p) _ s rs gs s' hd

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.k5_stepsN
#print axioms VerifiableInference.Desc.LinkJoin.k5_steps_atN
