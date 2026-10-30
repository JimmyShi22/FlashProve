-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05ReadersGuarded.lean: kind K5: THE READERS OF THE SEATED LINK GIVE WHAT "THE RUN ITSELF" GIVES AT THE KIND's OWN FOUR RUNS, THOUGH THE SEATED BLOCK IS DRESSED: in the chain the lot's block stands behind a guard
(Block.guarded, Johnson/Desc/SeatGuard.lean): each of its runs of claims says yes just where the lot's run says yes AND a test "same" of the state in front against the state after holds. So what block 2 of the seated link states is
(runsN A).map guard, NOT runsN A. The kind's four runs leave the field "out" of the verifier's state: so a guard whose test reads that field alone lets them through.

IT IMPORTS Att/K05ReadersLink.lean (hRds_of_link alone).

Main names:
  guardC same c: the library's own guard around a named run (Block.guarded's text for "claims").
  readerOf_guarded: GENERAL: what the reader gives at a list of runs it gives at the guarded list, if the run that is found leaves "same".
  runsN_keep: each of the kind's four runs leaves "out": "first", "keys", "second" hand the state back; "join" marks a debt in the ledger.
  hRds_seated: **the premise hRds of k5Behind_worth_readers (Att/K05BehindWorthReaders.lean), at states := fun _ => runsN A (where its hst is rfl) and Rds x.link := the readers of the link, at every filling of their two holes.**
PREMISES OF hRds_seated: hL : statesOfLink L 2 = (runsN A).map (guardC same) [the seat's: not shown here] · hsame : states with one "out" pass "same".
THE LETTERS UNDER "FOR ALL": hsame: s, t: free on purpose (a law of the test's make) · in the conclusion: name, s: free on purpose; R pinned by the run's equation.
IS IT EMPTY HERE? Implications.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.SeatGuard
import Johnson.Desc.First.Att.SeatN
import Johnson.Desc.First.Att.Claims.RunsStep
import Johnson.Desc.First.Att.Claims.ReadsLays
import Johnson.Desc.First.Att.K05ReadersLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Claim seatSame named need)
open VerifiableInference.Desc.K9 (RunOf readerOf statesOfLink readersOfLink LinkHoles)

/-- The library's own guard around a named run of claims. -/
def guardC (same : First.S → First.S → Bool) (c : RunOf First.S) : RunOf First.S :=
  (c.1, fun n t => (c.2 n t).bind fun y => (seatSame same t y.2).map fun _ => y)

/-- A guarded run's answer where the run says yes and the test holds. -/
theorem guardC_yes (same : First.S → First.S → Bool) (c : RunOf First.S) {n : ℕ} {t : First.S} {z : List Claim × First.S}
    (h : c.2 n t = .ok z) (hs : same t z.2 = true) : (guardC same c).2 n t = .ok z := by
  show ((c.2 n t).bind fun y => (seatSame same t y.2).map fun _ => y) = .ok z
  rw [h]
  show ((seatSame same t z.2).map fun _ => z) = .ok z
  unfold seatSame
  rw [if_pos hs]
  rfl

/-- **What the reader gives at a list of runs it gives at the guarded list.** -/
theorem readerOf_guarded (same : First.S → First.S → Bool) {st₀ st : ℕ → List (RunOf First.S)} {b : ℕ}
    (h : st b = (st₀ b).map (guardC same)) {name : String} {s : First.S} {R : VerifiableInference.Desc.K9.Read}
    (hr : readerOf st₀ b name s = some R)
    (hs : ∀ c z, ((st₀ b).find? fun r => r.1 == name) = some c → c.2 0 s = .ok z → same s z.2 = true) :
    readerOf st b name s = some R := by
  unfold readerOf at hr ⊢
  obtain ⟨c, hc, hr⟩ := Option.bind_eq_some_iff.1 hr
  have hf : ((st b).find? fun r => r.1 == name) = some (guardC same c) := by
    rw [h, List.find?_map]
    show (((st₀ b).find? fun r => r.1 == name).map (guardC same)) = _
    rw [hc]
    rfl
  rw [hf]
  show (match (guardC same c).2 0 s, s.fork? with
    | .ok z, some F => _
    | _, _ => none) = some R
  cases hz : c.2 0 s with
  | error e => rw [hz] at hr; cases hr
  | ok z =>
    rw [guardC_yes same c hz (hs c z hc hz)]
    rw [hz] at hr
    exact hr

/-- "out" under putFork. -/
theorem out_putFork (s : First.S) (G : Fork) : (s.putFork G).out = s.out := by
  unfold First.S.putFork
  cases hh : s.here with
  | head a => by_cases ho : a.opened = true <;> simp [ho]
  | _ => rfl

/-- **Each of the kind's four runs leaves "out".** -/
theorem runsN_keep (A : Attention.Plan) : ∀ c ∈ runsN A, ∀ (n : ℕ) (s : First.S) (z : List Claim × First.S),
    c.2 n s = .ok z → z.2.out = s.out := by
  intro c hc n s z hz
  unfold runsN at hc
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hc
  have hz' : ((r.2 n s).map fun y => (y.1.map claimOf, y.2)) = .ok z := hz
  cases hy : r.2 n s with
  | error e => rw [hy] at hz'; cases hz'
  | ok y =>
    rw [hy] at hz'
    obtain rfl : (y.1.map claimOf, y.2) = z := Except.ok.inj hz'
    show y.2.out = s.out
    unfold runsO at hr
    obtain ⟨r₀, hr₀, hm⟩ := List.mem_flatMap.1 hr
    have hand : ∀ y', r₀.2 n s = .ok y' → y'.2 = s := fun y' e => K5Law.runsK_step _ _ r₀ hr₀ n s y'.1 y'.2 e
    split at hm
    · rcases List.mem_cons.1 hm with rfl | hm
      · rw [hand y hy]
      · obtain rfl := List.mem_singleton.1 hm
        have hj : K3.joinRun (K3.seatCalls (Cl := Aff) id) (keysOfO A) n s = .ok y := hy
        unfold K3.joinRun at hj
        obtain ⟨_, _, hj⟩ := K5Law.except_bind_ok hj
        obtain ⟨_, _, hj⟩ := K5Law.except_bind_ok hj
        obtain ⟨_, _, hj⟩ := K5Law.except_bind_ok hj
        obtain ⟨_, _, hj⟩ := K5Law.except_bind_ok hj
        obtain ⟨x, _, hj⟩ := K5Law.except_bind_ok hj
        obtain rfl : ([(K3.seatCalls (Cl := Aff) id).claim x.1], (K3.seatCalls (Cl := Aff) id).mark s x.2.1) = y :=
          Except.ok.inj hj
        exact out_putFork s x.2.1
    · obtain rfl := List.mem_singleton.1 hm
      rw [hand y hy]

/-- **hRds AT THE SEATED LINK.** -/
theorem hRds_seated (H : LinkHoles) (L : VerifiableInference.Desc.Link First.S Claim) (A : Attention.Plan)
    (same : First.S → First.S → Bool) (hL : statesOfLink L 2 = (runsN A).map (guardC same))
    (hsame : ∀ s t : First.S, t.out = s.out → same s t = true) :
    ∀ (name : String) (s : First.S) (R : VerifiableInference.Desc.K9.Read), (name == "K8.equations") = false →
      readerOf (fun _ => runsN A) 2 name s = some R → (readersOfLink H L).forms 2 name s = some R :=
  fun name s R hn hr => hRds_of_link H L 2 name s R hn
    (readerOf_guarded same (st₀ := fun _ => runsN A) hL hr fun c z hc hz =>
      hsame s z.2 (runsN_keep A c (List.mem_of_find?_eq_some hc) 0 s z hz))

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.readerOf_guarded
#print axioms VerifiableInference.Desc.First.Att.P.runsN_keep
#print axioms VerifiableInference.Desc.First.Att.P.hRds_seated
