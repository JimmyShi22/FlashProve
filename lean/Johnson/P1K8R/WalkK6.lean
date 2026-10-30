-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/WalkK6.lean: THE OUTPUT HEAD's CALLING SUB-PROTOCOL's ADDRESS: WHAT THE SEATED LINK's
SUB-PROTOCOL NUMBER 3 AT LINK 24 STATES ("norm", "join", "policy", "logits") COMMUTES WITH THE
SMALLNESS TEST's DRAW (`RunBlind`, Johnson/Desc/First/K8/BlindReaders.lean); AND THE HEAD's READERS
OF THE PLANES' MATRIX ARE BLIND TO IT (`TlBlind`, Johnson/Desc/First/K8/BlindPub.lean). Theorems
on the head's text, and a joining.
  `planesAt_blind`, `callerReaders_blind`: the head's readers of the planes' matrix read the
    tables and the ledger: neither of the two fields that the draw writes.
  `kind_mem`: a run that the head's own sub-protocol states is looked up under its own name.
  `withJoin_blind`, `withJoin_leaves`: the sub-protocol with its four runs: every run commutes
    with the draw and leaves what goes on to the later chains: the three own runs by
    `own_runBlind` and `own_run_drawn`, "join" by `join_runBlind`
    (Johnson/Desc/Kinds/Law/K6TlBlind.lean) and `joinRun_leaves` (Johnson/P1K8R/WalkK5.lean).
  `claimsBlind_tested`, `leavesOut_tested`: the lot's tests in front of the decision
    (`tested`, Johnson/Stored/HeadSeatAt.lean) leave the runs as they are.
  `k6_states_blind`: **the join**: `IM.k6_of` (which sub-protocol stands there), these two,
    `claimsBlind_alone` and `states_blind` (Johnson/P1K8R/WalkAlone.lean).
Limits. At `OnBytes.secondHashFunction` alone. No example. Nothing on soundness or on hiding.

-/
import Johnson.P1K8R.WalkK5
import Johnson.IMR.K6Seat
import Johnson.Desc.Kinds.Law.K6TlBlind

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (TlBlind RunBlind ClaimsBlind drawn_ind)
open VerifiableInference.Desc.K9 (statesOfLink)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law (own_runBlind own_run_drawn join_runBlind)
open ProofFile (Cl)

theorem planesAt_blind (iU3 : ℕ) : TlBlind (planesAt iU3) := fun s t h => by
  refine drawn_ind (motive := fun s t => planesAt iU3 t = planesAt iU3 s) ?_ ?_ ?_ h <;>
    intros <;> simp_all [planesAt, S.fork?]

theorem callerReaders_blind (iU3 : ℕ) : TlBlind (callerReaders (planesAt iU3)) := fun s t h => by
  unfold callerReaders
  rw [planesAt_blind iU3 s t h]

section
variable (h : Model.Head.Shape) (iU3 l piece : ℕ) (p : Par)

/-- A run that the head's own sub-protocol states is looked up under its own name. -/
theorem kind_mem (c : String × (ℕ → S → Except String (List Claim × S)))
    (hc : c ∈ (kind asClaim (seatAt h iU3) l piece p).claims) :
    (kind asClaim (seatAt h iU3) l piece p).claims.lookup c.1 = some c.2 := by
  have hc' : c ∈ (kind asClaim (seatAt h iU3) l piece p).claims := hc
  unfold kind runsBy at hc' ⊢
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hc'
  rcases hc' with rfl | rfl | rfl <;> rfl

theorem withJoin_blind :
    ClaimsBlind (kindWithJoin (VerifiableInference.Desc.K3.seatCalls asClaim) (seatAt h iU3) l
      piece p) := by
  intro c hc n
  have hc' : c ∈ (kind asClaim (seatAt h iU3) l piece p).claims.take 1 ++
      [("join", VerifiableInference.Desc.K3.joinRun (VerifiableInference.Desc.K3.seatCalls asClaim)
        (callerKeys p (seatAt h iU3)))] ++
      (kind asClaim (seatAt h iU3) l piece p).claims.drop 1 := hc
  rcases List.mem_append.1 hc' with h1 | h1
  · rcases List.mem_append.1 h1 with h2 | h2
    · exact own_runBlind h iU3 l piece p (kind_mem h iU3 l piece p c (List.mem_of_mem_take h2)) n
    · obtain rfl := List.mem_singleton.1 h2
      exact join_runBlind h iU3 p n
  · exact own_runBlind h iU3 l piece p (kind_mem h iU3 l piece p c (List.mem_of_mem_drop h1)) n

theorem withJoin_leaves :
    LeavesOut (kindWithJoin (VerifiableInference.Desc.K3.seatCalls asClaim) (seatAt h iU3) l
      piece p) := by
  intro c hc n s z e
  have hc' : c ∈ (kind asClaim (seatAt h iU3) l piece p).claims.take 1 ++
      [("join", VerifiableInference.Desc.K3.joinRun (VerifiableInference.Desc.K3.seatCalls asClaim)
        (callerKeys p (seatAt h iU3)))] ++
      (kind asClaim (seatAt h iU3) l piece p).claims.drop 1 := hc
  have own : c ∈ (kind asClaim (seatAt h iU3) l piece p).claims → z.2.out = s.out := fun hm => by
    rw [(own_run_drawn h iU3 l piece p (kind_mem h iU3 l piece p c hm) n (s := s) (t := s)
      (fun _ hv => hv) e).1]
  rcases List.mem_append.1 hc' with h1 | h1
  · rcases List.mem_append.1 h1 with h2 | h2
    · exact own (List.mem_of_mem_take h2)
    · obtain rfl := List.mem_singleton.1 h2
      exact joinRun_leaves _ (fun s G => putFork_out s G) _ n s z e
  · exact own (List.mem_of_mem_drop h1)

end

/-- The lot's tests in front of the decision leave the runs as they are. -/
theorem claimsBlind_tested (ok : Bool) (start : S → Bool) (before : List (ℕ × ℕ))
    {b : Block S Claim} (hb : ClaimsBlind b) : ClaimsBlind (tested ok start before b) := hb

theorem leavesOut_tested (ok : Bool) (start : S → Bool) (before : List (ℕ × ℕ))
    {b : Block S Claim} (hb : LeavesOut b) : LeavesOut (tested ok start before b) := hb

/-- **WHAT THE SEATED LINK's SUB-PROTOCOL NUMBER 3 AT THE HEAD's LINK STATES COMMUTES WITH THE
DRAW**, in scope. -/
theorem k6_states_blind {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ Lk, c.links[24]? = some Lk ∧ ∀ ρ ∈ statesOfLink Lk 3, RunBlind (ρ.2 0) := by
  obtain ⟨Lk, b, b', ms, e1, e2, _, e3, ha, _⟩ := IM.k6_of hS hR O
  unfold seatedClaims at e3
  obtain ⟨b₀, e0, rfl⟩ := Option.map_eq_some_iff.1 e3
  unfold blockClaims at e0
  obtain ⟨iU3, _, rfl⟩ := Option.map_eq_some_iff.1 e0
  exact ⟨Lk, e1, states_blind e2 (claimsBlind_alone ha
    (claimsBlind_tested _ _ _ (withJoin_blind _ iU3 24 4 _))
    (leavesOut_tested _ _ _ (withJoin_leaves _ iU3 24 4 _)))⟩

end P1K8T

#print axioms P1K8T.callerReaders_blind
#print axioms P1K8T.withJoin_blind
#print axioms P1K8T.withJoin_leaves
#print axioms P1K8T.k6_states_blind
