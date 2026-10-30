-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/WalkK5.lean: THE ATTENTION CALLER'S ADDRESSES: WHAT THE SEATED LINK'S SUB-PROTOCOL
NUMBER 2 STATES, AT THE 12 ATTENTION LINKS, COMMUTES WITH THE SMALLNESS TEST'S DRAW. The twin of
Johnson/P1K8R/WalkK3.lean at the kind K5.

  leaves_same, leaves_map   two rules more for "a run leaves what goes on to the later chains"
  joinRun_leaves    the lookups' run "join" leaves it (the twin of WalkK3.lean's planesRun_leaves)
  runsK_leaves, runsO_leaves, k5AtN_leaves   K5's runs "first", "keys", "second" return the state as
                    it was (by firstK_eq, keysK_eq, secondK_eq); "join" by the
                    rule above; so K5's sub-protocol at a segment leaves it: LeavesOut
  k5_states_blind   THE JOIN: IM.k5_of (which sub-protocol stands there), k5AtN_blind (no premise) ·
                    k5AtN_leaves · WalkAlone.lean's claimsBlind_alone and states_blind

Limits. At OnBytes.secondHashFunction alone (IM.k5_of's). In the goals' scope. No soundness statement. Nothing
on hiding.

-/
import Johnson.P1K8R.WalkK3
import Johnson.IMR.K5Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName Claim named need)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (RunBlind ClaimsBlind k5AtN_blind firstK_eq secondK_eq
  keysK_eq)
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc.K9 (statesOfLink)
open ProofFile (Cl)

/-- A run that returns the state as it was. -/
theorem leaves_same {C : Type} (msg : String) (o : S → Option (List C)) :
    LeavesC fun s => named msg ((o s).map fun l => (l, s)) := fun s z h => by
  have h' : named msg ((o s).map fun l => (l, s)) = .ok z := h
  cases e : o s with
  | none =>
    rw [e] at h'
    exact nomatch h'
  | some l =>
    rw [e] at h'
    obtain rfl : (l, s) = z := Except.ok.inj h'
    rfl

theorem leaves_map {C C' : Type} (g : C → C') (f : S → Except String (List C × S))
    (hf : LeavesC f) : LeavesC fun s => (f s).map fun y => (y.1.map g, y.2) := fun s z h => by
  have h' : ((f s).map fun y => (y.1.map g, y.2)) = .ok z := h
  cases e : f s with
  | error x =>
    rw [e] at h'
    exact nomatch h'
  | ok y =>
    rw [e] at h'
    obtain rfl : (y.1.map g, y.2) = z := Except.ok.inj h'
    exact hf s y e

theorem joinRun_leaves {C : Type} (seat : VerifiableInference.Desc.K3.Seat S C)
    (hmk : ∀ s G, (seat.mark s G).out = s.out) (keys : S → Option (Array Aff)) (n : ℕ) :
    LeavesC (VerifiableInference.Desc.K3.joinRun seat keys n) :=
  leaves_named _ seat.fork _ fun _ => leaves_named _ seat.heard _ fun _ =>
    leaves_need _ (fun _ => _) _ <|
      leaves_named _ keys _ fun _ =>
        leaves_named _ (fun _ => _) _ fun x =>
          leaves_pure _ (fun s => seat.mark s x.2.1) fun s => hmk s _

/-- K5's three named runs return the state as it was. -/
theorem runsK_leaves (seat : SeatC S) (c : ParC) : ∀ r ∈ runsK seat c, ∀ n, LeavesC (r.2 n) := by
  intro r hr n
  unfold runsK at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · show LeavesC fun s => named "K5.first" (firstK seat c s)
    rw [show (fun s => named "K5.first" (firstK seat c s)) = _ from
      funext fun s => congrArg (named "K5.first") (firstK_eq seat c s)]
    exact leaves_same "K5.first" _
  · show LeavesC fun s => named "K5.keys" (keysK seat c s)
    rw [show (fun s => named "K5.keys" (keysK seat c s)) = _ from
      funext fun s => congrArg (named "K5.keys") (keysK_eq seat c s)]
    exact leaves_same "K5.keys" _
  · show LeavesC fun s => named "K5.second" (secondK seat c s)
    rw [show (fun s => named "K5.second" (secondK seat c s)) = _ from
      funext fun s => congrArg (named "K5.second") (secondK_eq seat c s)]
    exact leaves_same "K5.second" _

/-- K5's four named runs of forms. -/
theorem runsO_leaves (A : Attention.Plan) : ∀ r ∈ runsO A, ∀ n, LeavesC (r.2 n) := by
  intro r hr n
  unfold runsO at hr
  obtain ⟨r₀, h₀, hr⟩ := List.mem_flatMap.1 hr
  have k := runsK_leaves _ _ r₀ h₀
  split at hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact k n
    · exact joinRun_leaves _ (fun s G => putFork_out s G) _ n
  · obtain rfl := List.mem_singleton.1 hr
    exact k n

/-- **K5's sub-protocol at a segment: every run leaves what goes on to the later chains.** -/
theorem k5AtN_leaves {W : Verify.Public} {l g : ℕ} {before : List (ℕ × ℕ)} {b : Block S Claim}
    (h : k5AtN W l g before = some b) : LeavesOut b := by
  unfold k5AtN at h
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  intro c hc n
  have hc' : c ∈ runsN p := hc
  unfold runsN at hc'
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hc'
  exact leaves_map claimOf (r.2 n) (runsO_leaves p r hr n)

/-- **WHAT THE SEATED LINK's SUB-PROTOCOL NUMBER 2 STATES COMMUTES WITH THE DRAW**, in scope, at the
12 attention links. -/
theorem k5_states_blind {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (g : ℕ) (hg : g < 12) :
    ∃ Lk, c.links[2 * g + 1]? = some Lk ∧ ∀ ρ ∈ statesOfLink Lk 2, RunBlind (ρ.2 0) := by
  obtain ⟨Lk, b, b', a, e1, e2, e3, ha, -⟩ := IM.k5_of hS hR O g hg
  exact ⟨Lk, e1, states_blind e2 (claimsBlind_alone ha
    (fun c hc n => k5AtN_blind e3 c hc n) (fun c hc n => k5AtN_leaves e3 c hc n))⟩

end P1K8T

#print axioms P1K8T.k5AtN_leaves
#print axioms P1K8T.k5_states_blind
