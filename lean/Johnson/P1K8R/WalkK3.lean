-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/WalkK3.lean: THE LOOKUPS' ADDRESSES: WHAT THE SEATED LINK's LOOKUP STATES COMMUTES
WITH THE SMALLNESS TEST's DRAW (RunBlind, Johnson/Desc/First/K8/BlindReaders.lean), IN SCOPE, AT
EVERY LINK l < 25, ON THE CALLS AND ON THE DIGITS. Rules over letters, theorems on the lookups'
text, and a joining.
  LeavesC f · leaves_named | leaves_need | leaves_pure · putFork_out: THE RULES FOR «a run leaves what goes on to the later chains (S.out)»: twins of the rules runBlind_named | _need | _pure (Johnson/Desc/First/Batch/Law/BlindRunsK3.lean), whose proofs' shape the theorems below follow, arm for arm.
  via_leaves · planesRun_leaves · theOwn_leaves · theWhole_leaves · theStated_leaves: the lookups' own sub-protocol at an address (K3.theStated, Johnson/Desc/First/Look/K3Stated.lean), whole, with its runs stated: LeavesOut (WalkAlone.lean). No premise.
  k3Readers_blind: the premise hr of theStated_blind (BlindRunsK3.lean) at the lot's own readers (K3Lot.readersAt): at an attention link by readersOfO_blind (BlindRunsK5.lean, in the same folder); at a layers' link there is none; AT THE OUTPUT HEAD's LINK IT IS LEFT AS ONE PREMISE: the blindness of Kinds.Head.callerReaders (Kinds.Head.planesAt iU3) (Johnson/Desc/Kinds/HeadCaller.lean).
  k3_states_blind: **the join**: IM.k3_of (Johnson/IMR/K3Seat.lean: which sub-protocol stands at the lookups' addresses) · theStated_blind · theStated_leaves · claimsBlind_alone | states_blind.
LIMITS. At OnBytes.secondHashFunction alone (IM.k3_of's). The head's callers' readers are a premise. No soundness. Nothing on hiding.
-/
import Johnson.P1K8R.WalkAlone
import Johnson.IMR.K3Seat
import Johnson.Desc.First.Batch.Law.BlindRunsK5

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName Claim named need)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open VerifiableInference.Desc.First.K8 (TlBlind RunBlind ClaimsBlind theStated_blind readersOfO_blind)
open VerifiableInference.Desc.K9 (statesOfLink)
open ProofFile (Cl)

/-! ## The rules for "leaves what goes on to the later chains" -/

/-- A run leaves what goes on to the later chains. -/
def LeavesC {C : Type} (f : S → Except String (List C × S)) : Prop :=
  ∀ s z, f s = .ok z → z.2.out = s.out

section
variable {C : Type}

theorem leaves_named {α : Type} (msg : String) (o : S → Option α)
    (k : α → S → Except String (List C × S)) (hk : ∀ a, LeavesC (k a)) :
    LeavesC fun s => (named msg (o s)).bind fun a => k a s := fun s z h => by
  have h' : ((named msg (o s)).bind fun a => k a s) = .ok z := h
  cases e : o s with
  | none =>
    rw [e] at h'
    exact nomatch h'
  | some a =>
    rw [e] at h'
    exact hk a s z h'

theorem leaves_need (msg : String) (c : S → Bool) (k : S → Except String (List C × S))
    (hk : LeavesC k) : LeavesC fun s => (need msg (c s)).bind fun _ => k s := fun s z h => by
  have h' : ((need msg (c s)).bind fun _ => k s) = .ok z := h
  cases e : c s with
  | false =>
    rw [e] at h'
    exact nomatch h'
  | true =>
    rw [e] at h'
    exact hk s z h'

theorem leaves_pure (cl : List C) (w : S → S) (hw : ∀ s, (w s).out = s.out) :
    LeavesC fun s => (pure (cl, w s) : Except String (List C × S)) := fun s z h => by
  obtain rfl : (cl, w s) = z := Except.ok.inj h
  exact hw s

end

theorem putFork_out (s : S) (G : Fork) : (s.putFork G).out = s.out := by
  unfold S.putFork
  split
  · rfl
  · rfl
  · split <;> rfl
  · rfl

section
variable {C : Type} (seat : VerifiableInference.Desc.K3.Seat S C) (hmk : ∀ s G, (seat.mark s G).out = s.out)
include hmk

theorem via_leaves (piece : ℕ) (laid : Array ℕ) (before : List (ℕ × ℕ)) (p : VerifiableInference.Desc.First.Look.P) :
    ∀ c ∈ (VerifiableInference.Desc.K3.Law.blockVia seat piece laid before p []).claims, ∀ n, LeavesC (c.2 n) := by
  intro c hc n
  have hc' : c ∈ (VerifiableInference.Desc.K3.Law.blockVia seat piece laid before p []).claims := hc
  unfold VerifiableInference.Desc.K3.Law.blockVia at hc'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
  rcases hc' with rfl | rfl
  · exact leaves_named _ seat.fork _ fun F => leaves_named _ seat.heard _ fun g =>
      leaves_pure _ (fun s => seat.mark s (F.paid g.owedObjects)) fun s => hmk s _
  · exact leaves_pure [] (fun s => s) fun _ => rfl

theorem planesRun_leaves (lm : ℕ) (readers : VerifiableInference.Desc.K3.Readers S) (n : ℕ) :
    LeavesC (VerifiableInference.Desc.K3.planesRun seat lm readers n) :=
  leaves_named _ seat.fork _ fun _ => leaves_named _ seat.heard _ fun _ =>
    leaves_need _ (fun _ => _) _ <|
      leaves_named _ readers _ fun _ =>
        leaves_named _ (fun _ => _) _ fun x =>
          leaves_pure _ (fun s => seat.mark s x.2.1) fun s => hmk s _

end

theorem leavesOut_andThen (name : String) {p q : Block S Cl} (hp : LeavesOut p)
    (hq : LeavesOut q) : LeavesOut (p.andThen name q) := fun c hc n => by
  rcases List.mem_append.1 hc with h | h
  · exact hp c h n
  · exact hq c h n

theorem theOwn_leaves (claim : Aff → Claim) (runs : Bool) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Place) {b : Block S Claim}
    (h : VerifiableInference.Desc.K3.theOwn claim runs X codes shape a = some b) : LeavesOut b := by
  unfold VerifiableInference.Desc.K3.theOwn at h
  split at h
  · exact nomatch h
  · obtain ⟨i, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨digits, _, h⟩ := List.exists_of_findSome?_eq_some h
    split at h
    · exact nomatch h
    · obtain ⟨p, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨sent, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨laid, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨key, _, rfl⟩ := Option.map_eq_some_iff.1 h
      have W : LeavesOut (VerifiableInference.Desc.K3.Law.blockVia
          (if digits = true then VerifiableInference.Desc.K3.seatDigits claim else VerifiableInference.Desc.K3.seatCalls claim) a.piece laid sent p
          []) := by
        cases digits with
        | true => exact via_leaves _ (fun s G => putFork_out s G) a.piece laid sent p
        | false => exact via_leaves _ (fun s G => putFork_out s G) a.piece laid sent p
      cases runs with
      | true => exact W
      | false => exact fun _ hc => nomatch hc

theorem theWhole_leaves (claim : Aff → Claim) (runs : Bool) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Place) {b : Block S Claim}
    (h : VerifiableInference.Desc.K3.theWhole claim runs X codes shape a = some b) : LeavesOut b := by
  unfold VerifiableInference.Desc.K3.theWhole at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  have W := theOwn_leaves claim runs X codes shape a h0
  cases hf : (a.link.bind fun i => VerifiableInference.Desc.K3.quietAt X i (a.piece == VerifiableInference.Desc.K3.pieceAt X i true)) with
  | none => exact W
  | some f => exact leavesOut_andThen _ W fun _ hc => nomatch hc

/-- **K3's sub-protocol at an address, whole, with its runs stated: every run leaves what goes on to
the later chains.** -/
theorem theStated_leaves (claim : Aff → Claim) (readers : ℕ → Option (VerifiableInference.Desc.K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Claim}
    (h : VerifiableInference.Desc.K3.theStated claim readers X codes shape a = some b) : LeavesOut b := by
  unfold VerifiableInference.Desc.K3.theStated at h
  obtain ⟨b₀, h0, h⟩ := Option.bind_eq_some_iff.1 h
  have W := theWhole_leaves claim true X codes shape a h0
  split at h
  · cases h
    exact W
  · split at h
    · cases h
      exact W
    · split at h
      · cases h
        exact W
      · obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 h
        intro c hc n
        rcases List.mem_append.1 hc with hc | hc
        · exact W c hc n
        · obtain rfl := List.mem_singleton.1 hc
          exact planesRun_leaves _ (fun s G => putFork_out s G) _ _ n

/-! ## The join at the lookups' addresses -/

/-- The calling kinds' readers of the planes' matrix are blind, where the output head's are. -/
theorem k3Readers_blind (X : Verify.Public)
    (hH : ∀ iU3, TlBlind (VerifiableInference.Desc.Kinds.Head.callerReaders
      (VerifiableInference.Desc.Kinds.Head.planesAt iU3))) :
    ∀ i r, K3Lot.readersAt X i = some r → TlBlind r := by
  intro i r h
  unfold K3Lot.readersAt at h
  dsimp only at h
  generalize (if X.p4 = true then 2 else 1) = step at h
  by_cases h1 : VerifiableInference.Desc.K3.isHead X i = true
  · rw [if_pos h1] at h
    obtain ⟨iU3, _, rfl⟩ := Option.map_eq_some_iff.1 h
    exact hH iU3
  · rw [if_neg h1] at h
    by_cases h2 : (i % step == 0) = true
    · rw [if_pos h2] at h
      exact nomatch h
    · rw [if_neg h2] at h
      obtain ⟨A, _, rfl⟩ := Option.map_eq_some_iff.1 h
      exact readersOfO_blind A

/-- **WHAT THE SEATED LINK's LOOKUP STATES COMMUTES WITH THE DRAW**, in scope, at every link l < 25,
on the calls and on the digits: where the calling kinds' readers of the planes' matrix are blind. -/
theorem k3_states_blind {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hr : ∀ i r, K3Lot.readersAt Bs.G₀.W i = some r → TlBlind r) (l : ℕ) (hl : l < 25)
    (digits : Bool) :
    ∃ Lk, c.links[l]? = some Lk ∧ ∀ ρ ∈ statesOfLink Lk (IM.k3Ix l digits), RunBlind (ρ.2 0) := by
  obtain ⟨Lk, b, b', e1, e2, e3, ha⟩ := IM.k3_of hS hR O l hl digits
  exact ⟨Lk, e1, states_blind e2 (claimsBlind_alone ha
    (theStated_blind _ _ hr _ _ _ _ e3) (theStated_leaves _ _ _ _ _ _ e3))⟩

end P1K8T

#print axioms P1K8T.theStated_leaves
#print axioms P1K8T.k3Readers_blind
#print axioms P1K8T.k3_states_blind
