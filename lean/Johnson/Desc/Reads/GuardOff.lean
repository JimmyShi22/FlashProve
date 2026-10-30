-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/GuardOff.lean: at the seated segment of the output head, the premise "the run
that the segment states under the name is the kind's own" of the laws on the readers can be met.

Why. `reader_fwd`, `fwd_of_run`, `fwd_of_hole`, `reader_fifth` and their likes at "join"
(Reads/ReaderFwd.lean, FwdHead.lean, JoinFwd.lean, PassFifth.lean) take a premise hst: the run that
is found under the name is the kind's bare run. In the first chain as it is made, each run of a
sub-protocol stands behind a guard, which rejects where the run has turned the reply that was heard
(`IM.guardRun`, `IM.claims_alone`, Johnson/IMR/SeatForm.lean; `ProofFile.sameReply`,
Johnson/Desc/ProofFile/Frames1.lean). So at the segment that is meant hst speaks of a guarded run,
and without a law on the guard these laws would be true and spent nowhere.

What is shown.
  `same_of_reply`: the guard's test accepts where the reply stands.
  `guard_off`: a run whose accept leaves the reply is its own guarded run.
  `guard_own`, `guard_join`: **so are the output head's three own runs and "join".** The own runs
    return the state (`run_returns`, Reads/KeptSmall.lean); "join" leaves the reply
    (`keptAll_joinRun`, Reads/KeptRuns.lean).
  `seated_runs`: the runs that the seated sub-protocol of the table states: the kind's first,
    "join", the kind's others.
  `found_laid`: what is found under a name at such a place is a run of the table's sub-protocol,
    behind the guard.
  `hst_own_laid`, `hst_join_laid`: **hst, to the letter, at the runs that a segment states at a
    place where the table's sub-protocol is laid alone behind the guard.**

Premises of the last two: the sub-protocol B is the table's (`seatedClaims`); the number of the
reads' array; bb is B laid alone (`IM.LaidAlone`); the segment holds bb at place number b.

Limits. That the made chain's segment holds such a bb at its fourth place is another file's law,
not called here. Nothing on soundness.


-/
import Johnson.Desc.Reads.PassFifth
import Johnson.IMR.SeatForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads.Pass

open OnBytes.Model (Aff)
open VerifiableInference.Desc (Block Claim Link Place K3.joinRun K3.seatCalls)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (RunOf statesOfLink)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open VerifiableInference.Reads.AtSeat (run_returns keptAll_joinRun)

/-- The guard's test accepts where the reply stands. -/
theorem same_of_reply {t u : S} (h : u.out.reply = t.out.reply) : ProofFile.sameReply t u = true := by
  unfold ProofFile.sameReply
  rw [h]
  exact beq_self_eq_true _

/-- A run whose accept leaves the reply is its own guarded run. -/
theorem guard_off {Cl : Type} (ρ : ℕ → S → Except String (List Cl × S))
    (h : ∀ n t y, ρ n t = .ok y → y.2.out.reply = t.out.reply) :
    (fun n t => (ρ n t).bind fun y =>
      (VerifiableInference.Desc.seatSame ProofFile.sameReply t y.2).map fun _ => y) = ρ := by
  funext n t
  cases hr : ρ n t with
  | error e => rfl
  | ok y =>
    show (VerifiableInference.Desc.seatSame ProofFile.sameReply t y.2).map (fun _ => y) = .ok y
    unfold VerifiableInference.Desc.seatSame
    rw [if_pos (same_of_reply (h n t y hr))]
    rfl

/-- **The output head's own runs.** -/
theorem guard_own {names : List String}
    {runs : Given → Behind → Places → List (String × List Form)}
    {keys : Given → Behind → Places → List Form} {toCl : Form → Claim} {p : Par}
    {h : OnBytes.Model.Head.Shape} {iU3 : ℕ}
    {c : String × (ℕ → S → Except String (List Claim × S))}
    (hc : c ∈ runsBy names runs keys toCl p (seatAt h iU3)) :
    IM.guardRun ProofFile.sameReply c.2 = c.2 :=
  guard_off c.2 fun n t y hr => by rw [run_returns h iU3 hc hr]

/-- **"join".** -/
theorem guard_join (claim : Aff → Claim) (keys : S → Option (Array Aff)) :
    IM.guardRun ProofFile.sameReply (K3.joinRun (K3.seatCalls claim) keys) =
      K3.joinRun (K3.seatCalls claim) keys :=
  guard_off _ fun _ _ _ hr => (keptAll_joinRun claim keys 0 hr).reply

/-- The runs that the table's sub-protocol states. -/
theorem seated_runs {W : OnBytes.Model.Verify.Public} {lk : ℕ} {before : List (ℕ × ℕ)}
    {B : Block S Claim} (hB : seatedClaims W lk before = some B) {iU3 : ℕ}
    (hi : W.H.tl.ix.U.getD 2 none = some iU3) :
    B.claims = (kind asClaim (seatAt W.hS iU3) lk 4 (parOf W.hS (Law.workOf W))).claims.take 1 ++
      [("join", K3.joinRun (K3.seatCalls asClaim)
        (callerKeys (parOf W.hS (Law.workOf W)) (seatAt W.hS iU3)))] ++
      (kind asClaim (seatAt W.hS iU3) lk 4 (parOf W.hS (Law.workOf W))).claims.drop 1 := by
  unfold seatedClaims blockClaims at hB
  rw [hi] at hB
  rw [← Option.some.inj hB]
  rfl

section
variable {W : OnBytes.Model.Verify.Public} {lk : ℕ} {before : List (ℕ × ℕ)} {B bb : Block S Claim}
  {iU3 : ℕ} {nm : String} {a : Place} {l : Link S Claim} {b : ℕ} {name : String}

/-- What is found under a name at such a place: a run of B's, behind the guard. -/
theorem found_laid (hL : IM.LaidAlone ProofFile.sameReply bb B nm a) (hh : l.hear[b]? = some bb)
    {r : RunOf S} (hf : ((statesOfLink l b).find? fun r => r.1 == name) = some r) :
    ∃ c ∈ B.claims, c.1 = name ∧ r = (c.1, IM.guardRun ProofFile.sameReply c.2) := by
  have hs : statesOfLink l b = B.claims.map fun c => (c.1, IM.guardRun ProofFile.sameReply c.2) := by
    unfold statesOfLink
    rw [hh]
    exact IM.claims_alone hL
  rw [hs] at hf
  have hm := List.mem_of_find?_eq_some hf
  have hn := List.find?_some hf
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hm
  exact ⟨c, hc, by simpa using hn, rfl⟩

/-- **hst at the three own runs.** -/
theorem hst_own_laid (hB : seatedClaims W lk before = some B)
    (hi : W.H.tl.ix.U.getD 2 none = some iU3) (hL : IM.LaidAlone ProofFile.sameReply bb B nm a)
    (hh : l.hear[b]? = some bb) (hname : name ≠ "join") :
    ∀ r, ((statesOfLink l b).find? fun r => r.1 == name) = some r →
      r ∈ runsBy ["norm", "policy", "logits"] (fun _ _ _ => claims)
        (fun g _ _ => g.calls.map fun c => keyVector key c.1 c.2) asClaim
        (parOf W.hS (Law.workOf W)) (seatAt W.hS iU3) := by
  intro r hf
  obtain ⟨c, hc, hn, rfl⟩ := found_laid hL hh hf
  rw [seated_runs hB hi] at hc
  have hk : c ∈ (kind asClaim (seatAt W.hS iU3) lk 4 (parOf W.hS (Law.workOf W))).claims := by
    rcases List.mem_append.1 hc with h1 | h1
    · rcases List.mem_append.1 h1 with h2 | h2
      · exact List.mem_of_mem_take h2
      · rw [List.mem_singleton.1 h2] at hn
        exact absurd hn.symm hname
    · exact List.mem_of_mem_drop h1
  have hk' : c ∈ runsBy ["norm", "policy", "logits"] (fun _ _ _ => claims)
      (fun g _ _ => g.calls.map fun c => keyVector key c.1 c.2) asClaim (parOf W.hS (Law.workOf W))
      (seatAt W.hS iU3) := hk
  rw [guard_own hk']
  exact hk'

/-- **hst at "join".** -/
theorem hst_join_laid (hB : seatedClaims W lk before = some B)
    (hi : W.H.tl.ix.U.getD 2 none = some iU3) (hL : IM.LaidAlone ProofFile.sameReply bb B nm a)
    (hh : l.hear[b]? = some bb) :
    ∀ r, ((statesOfLink l b).find? fun r => r.1 == "join") = some r →
      r.2 = K3.joinRun (K3.seatCalls asClaim)
        (callerKeys (parOf W.hS (Law.workOf W)) (seatAt W.hS iU3)) := by
  intro r hf
  obtain ⟨c, hc, hn, rfl⟩ := found_laid hL hh hf
  rw [seated_runs hB hi] at hc
  have own_ne : ∀ c' ∈ (kind asClaim (seatAt W.hS iU3) lk 4 (parOf W.hS (Law.workOf W))).claims,
      c'.1 ≠ "join" := by
    intro c' hc'
    have hk' : c' ∈ runsBy ["norm", "policy", "logits"] (fun _ _ _ => claims)
        (fun g _ _ => g.calls.map fun c => keyVector key c.1 c.2) asClaim
        (parOf W.hS (Law.workOf W)) (seatAt W.hS iU3) := hc'
    unfold runsBy at hk'
    obtain ⟨n0, hn0, rfl⟩ := List.mem_map.1 hk'
    intro e
    have e' : n0 = "join" := e
    subst e'
    revert hn0
    decide
  rcases List.mem_append.1 hc with h1 | h1
  · rcases List.mem_append.1 h1 with h2 | h2
    · exact absurd hn (own_ne c (List.mem_of_mem_take h2))
    · rw [List.mem_singleton.1 h2]
      exact guard_join _ _
  · exact absurd hn (own_ne c (List.mem_of_mem_drop h1))

end

end VerifiableInference.Reads.Pass

#print axioms VerifiableInference.Reads.Pass.same_of_reply
#print axioms VerifiableInference.Reads.Pass.guard_off
#print axioms VerifiableInference.Reads.Pass.guard_own
#print axioms VerifiableInference.Reads.Pass.guard_join
#print axioms VerifiableInference.Reads.Pass.seated_runs
#print axioms VerifiableInference.Reads.Pass.found_laid
#print axioms VerifiableInference.Reads.Pass.hst_own_laid
#print axioms VerifiableInference.Reads.Pass.hst_join_laid
