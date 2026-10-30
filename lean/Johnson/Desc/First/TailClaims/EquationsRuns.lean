-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/EquationsRuns.lean: what it says of a routine of Equations.lean (EqM)
that it has returned, and what the adding of one claim does to the record's total.

Statements and proofs. No routine of `verify-on-bytes` is named: the record (Fork) and its plain
functions (kap, push, pushRuns) alone, with their laws Fork.kap_spec, push_total,
pushRuns_total (OnBytes/Model/HideLaws.lean, TreesLaws.lean). ALSO USED, ON RECORDS AND PLAIN DATA
ALONE: Reading (gl), World, treesFrame, Fork.total, Aff.value, Run2.value, powE.
Main names:
  eq_bind_ok, eq_pure_ok, eq_liftF_ok; eq_get_ok, eq_must_ok, eq_test_ok, eq_ask_ok, emit_ok,
    eq_claims_ok: a run that returns, taken apart.
  addAll_append, addOne: the adding of a list, of one claim, taken apart.
  OnlySums P P', onlySums_claim, total_claim: one claim changes the sums alone; the total grows by
    the weight times the form's and the runs' values.
  RunFoldE, forInE_inv, forInE_inv_array, runFoldE_append | _flat | _mono | _map | _all: a loop whose
    body never breaks off is the runs of its body, in order (after OnBytes/Tie/Pv/Tail/EndLoops.lean,
    over this monad's state).
Limits: nothing on a run that refuses.

-/
import Johnson.Desc.First.TailClaims.Equations
import OnBytes.Tie.Pv.Tail.EndForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc

abbrev St : Type := Fork × Array Claim

theorem eq_bind_ok {α β : Type} (x : EqM α) (f : α → EqM β) (front : Nat) (s : St) (r : β × St) :
    (x >>= f) front s = .ok r ↔ ∃ a s1, x front s = .ok (a, s1) ∧ f a front s1 = .ok r := by
  show Except.bind (x front s) _ = .ok r ↔ _
  cases h : x front s with
  | error e => simp [Except.bind]
  | ok v =>
    obtain ⟨a, s1⟩ := v
    constructor
    · intro h'
      exact ⟨a, s1, rfl, h'⟩
    · rintro ⟨a', s', e, h'⟩
      cases e
      exact h'

theorem eq_pure_ok {α : Type} (a x : α) (front : Nat) (s s' : St) :
    (Pure.pure a : EqM α) front s = .ok (x, s') ↔ x = a ∧ s' = s := by
  show (Except.ok (a, s) : Except String (α × St)) = .ok (x, s') ↔ _
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem eq_liftF_ok {α : Type} (x : ForkM α) (front : Nat) (s s' : St) (a : α) :
    EqM.liftF x front s = .ok (a, s') ↔ ∃ F, x s.1 = .ok (a, F) ∧ s' = (F, s.2) := by
  unfold EqM.liftF
  cases h : x s.1 with
  | error e => simp
  | ok v =>
    obtain ⟨a1, F1⟩ := v
    simp only [Except.ok.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨F1, ⟨rfl, rfl⟩, rfl⟩
    · rintro ⟨F, ⟨rfl, rfl⟩, rfl⟩; exact ⟨rfl, rfl⟩

theorem addAll_nil (A : Fork) : addAll A [] = some A := rfl

theorem addAll_append (A : Fork) (l l' : List Claim) :
    addAll A (l ++ l') = (addAll A l).bind fun B => addAll B l' := by
  unfold addAll
  rw [List.foldlM_append]
  rfl


/-- P' is P but for the sums. -/
structure OnlySums (P P' : Fork) : Prop where
  ns : P'.ns = P.ns
  next : P'.next = P.next
  vp : P'.vp = P.vp
  mf : P'.mf = P.mf
  gotF : P'.gotF = P.gotF
  owed : P'.owed = P.owed
  theta : P'.theta = P.theta
  drawn : P'.thetaDrawnF = P.thetaDrawnF
  plan : P'.planClaimsF = P.planClaimsF
  door : P'.doorShutF = P.doorShutF
  trees : treesFrame P'.trees = treesFrame P.trees

/-- One claim: a weight taken, a form and runs added under a weight. -/
theorem onlySums_claim {P P1 P2 P3 : Fork} {k w : E} {a : Aff} {runs : Array Run2}
    (hs : P.LS.size = P.ns) (h1 : P.kap = some (k, P1)) (h2 : P1.push w a = some P2)
    (h3 : P2.pushRuns w runs = some P3) :
    OnlySums P P3 ∧ P3.nClaim = P.nClaim + 1 ∧ P3.LS.size = P3.ns := by
  obtain ⟨_, e1, _, _⟩ := Fork.kap_spec P P1 k h1
  have hs1 : P1.LS.size = P1.ns := by rw [e1]; exact hs
  obtain ⟨_, e2, s2, f2⟩ :=
    Fork.push_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ P1 P2 w a hs1 h2
  obtain ⟨_, e3, f3⟩ := Fork.pushRuns_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ P2 P3 w runs h3
  have t1 : P1.trees = P.trees := by rw [e1]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  all_goals first
    | (rw [f3, f2, t1])
    | (rw [e3]; exact s2)
    | (rw [e3, e2, e1])

/-- The total behind one claim under any weight. -/
theorem total_claim {K : Type} [CommRing K] (ρ : Reading K) (W : World K) {P P1 P2 P3 : Fork}
    {k w : E} {a : Aff} {runs : Array Run2} (hs : P.LS.size = P.ns) (h1 : P.kap = some (k, P1))
    (h2 : P1.push w a = some P2) (h3 : P2.pushRuns w runs = some P3) :
    P3.total ρ W = P.total ρ W +
      ρ.val w * (a.value ρ W + (runs.toList.map (Run2.value ρ W)).sum) := by
  obtain ⟨_, e1, _, _⟩ := Fork.kap_spec P P1 k h1
  have hs1 : P1.LS.size = P1.ns := by rw [e1]; exact hs
  obtain ⟨t2, _, _, _⟩ := Fork.push_total ρ W P1 P2 w a hs1 h2
  obtain ⟨t3, _, _⟩ := Fork.pushRuns_total ρ W P2 P3 w runs h3
  have t1 : P1.total ρ W = P.total ρ W := by rw [e1]; rfl
  rw [t3, t2, t1]
  ring

/-- What addAll of one claim is. -/
theorem addOne {A A' : Fork} {cl : Claim} (h : addAll A [cl] = some A') :
    ∃ k A1 w A2, A.kap = some (k, A1) ∧
      (match cl.eqFirst with
        | none => some k
        | some first =>
          if A.nClaim < A.planClaimsF then some (powE A.theta (A.planClaimsF + first)) else none)
        = some w ∧ A1.push w cl.form = some A2 ∧ A2.pushRuns w cl.runs = some A' := by
  have h' : addClaim A cl = some A' := by simpa [addAll] using h
  unfold addClaim at h'
  obtain ⟨x, hx, h'⟩ := Option.bind_eq_some_iff.1 h'
  dsimp only at h'
  obtain ⟨w, hw, h'⟩ := Option.bind_eq_some_iff.1 h'
  obtain ⟨A2, hA2, h'⟩ := Option.bind_eq_some_iff.1 h'
  exact ⟨x.1, x.2, w, A2, hx, hw, hA2, h'⟩

theorem eq_get_ok {α : Type} {n : String} {o : Option α} {front : Nat} {s s' : St} {a : α}
    (h : EqM.get n o front s = .ok (a, s')) : o = some a ∧ s' = s := by
  obtain ⟨F, hF, rfl⟩ := (eq_liftF_ok _ _ _ _ _).1 h
  cases o with
  | none => cases hF
  | some v =>
    have e := Except.ok.inj hF
    obtain rfl : v = a := congrArg Prod.fst e
    obtain rfl : s.1 = F := congrArg Prod.snd e
    exact ⟨rfl, rfl⟩

theorem eq_must_ok {n : String} {b : Bool} {front : Nat} {s s' : St} {u : Unit}
    (h : EqM.mustAs n b front s = .ok (u, s')) : b = true ∧ s' = s := by
  obtain ⟨F, hF, rfl⟩ := (eq_liftF_ok _ _ _ _ _).1 h
  cases b with
  | false => cases hF
  | true =>
    obtain rfl : s.1 = F := congrArg Prod.snd (Except.ok.inj hF)
    exact ⟨rfl, rfl⟩

theorem eq_test_ok {n : String} {b : Bool} {front : Nat} {s s' : St} {u : Unit}
    (h : EqM.testAs n b front s = .ok (u, s')) : b = true ∧ s' = s := eq_must_ok (n := n) h

theorem eq_ask_ok {α : Type} {n : String} {f : Fork → Option α} {front : Nat} {s s' : St} {a : α}
    (h : EqM.ask n f front s = .ok (a, s')) : f s.1 = some a ∧ s' = s := by
  obtain ⟨F, hF, rfl⟩ := (eq_liftF_ok _ _ _ _ _).1 h
  unfold ForkM.ask at hF
  cases e : f s.1 with
  | none => rw [e] at hF; cases hF
  | some v =>
    rw [e] at hF
    have e' := Except.ok.inj hF
    obtain rfl : v = a := congrArg Prod.fst e'
    obtain rfl : s.1 = F := congrArg Prod.snd e'
    exact ⟨rfl, rfl⟩

theorem emit_ok {c : Claim} {front : Nat} {s s' : St} {u : Unit}
    (h : EqM.emit c front s = .ok (u, s')) : s' = (s.1, s.2.push c) :=
  (congrArg Prod.snd (Except.ok.inj h)).symm

theorem push_one (a : Array Claim) (c : Claim) : a.push c = a ++ [c].toArray := by simp

theorem eq_claims_ok {front : Nat} {s s' : St} {a : Nat}
    (h : EqM.claims front s = .ok (a, s')) : a = front + s.2.size ∧ s' = s := by
  have e := Except.ok.inj h
  exact ⟨(congrArg Prod.fst e).symm, (congrArg Prod.snd e).symm⟩

/-! ## Loops -/

/-- The runs of a loop's body on the entries of a list, one after the other. -/
def RunFoldE {α β : Type} (step : α → β → St → β → St → Prop) :
    List α → β → St → β → St → Prop
  | [], b, s, b', s' => b' = b ∧ s' = s
  | a :: l, b, s, b', s' => ∃ b1 s1, step a b s b1 s1 ∧ RunFoldE step l b1 s1 b' s'

theorem forInE_inv {α β : Type} (front : Nat) (f : α → β → EqM (ForInStep β))
    (step : α → β → St → β → St → Prop)
    (hf : ∀ a b s r s1, f a b front s = .ok (r, s1) → ∃ b1, r = .yield b1 ∧ step a b s b1 s1) :
    ∀ (l : List α) (b : β) (s : St) (b' : β) (s' : St),
      (forIn l b f) front s = .ok (b', s') → RunFoldE step l b s b' s'
  | [], b, s, b', s', h => by
    rw [List.forIn_nil] at h
    exact (eq_pure_ok _ _ _ _ _).1 h
  | a :: l, b, s, b', s', h => by
    rw [List.forIn_cons] at h
    obtain ⟨r, s1, h1, h2⟩ := (eq_bind_ok _ _ _ _ _).1 h
    obtain ⟨b1, rfl, hs⟩ := hf a b s r s1 h1
    exact ⟨b1, s1, hs, forInE_inv front f step hf l b1 s1 b' s' h2⟩

theorem forInE_inv_array {α β : Type} (front : Nat) (f : α → β → EqM (ForInStep β))
    (step : α → β → St → β → St → Prop)
    (hf : ∀ a b s r s1, f a b front s = .ok (r, s1) → ∃ b1, r = .yield b1 ∧ step a b s b1 s1)
    (as : Array α) (b : β) (s : St) (b' : β) (s' : St)
    (h : (forIn as b f) front s = .ok (b', s')) : RunFoldE step as.toList b s b' s' := by
  rw [← Array.forIn_toList] at h
  exact forInE_inv front f step hf _ _ _ _ _ h

theorem runFoldE_append {α β : Type} (step : α → β → St → β → St → Prop) :
    ∀ (l1 l2 : List α) (b : β) (s : St) (b1 : β) (s1 : St) (b2 : β) (s2 : St),
      RunFoldE step l1 b s b1 s1 → RunFoldE step l2 b1 s1 b2 s2 →
      RunFoldE step (l1 ++ l2) b s b2 s2
  | [], _, _, _, _, _, _, _, h1, h2 => by
    obtain ⟨rfl, rfl⟩ := h1
    exact h2
  | _ :: l1, l2, _, _, _, _, _, _, h1, h2 => by
    obtain ⟨b0, s0, hs, hr⟩ := h1
    exact ⟨b0, s0, hs, runFoldE_append step l1 l2 _ _ _ _ _ _ hr h2⟩

theorem runFoldE_flat {α γ β : Type} (step : α → β → St → β → St → Prop) (g : γ → List α) :
    ∀ (l : List γ) (b : β) (s : St) (b' : β) (s' : St),
      RunFoldE (fun x => RunFoldE step (g x)) l b s b' s' → RunFoldE step (l.flatMap g) b s b' s'
  | [], _, _, _, _, h => h
  | x :: l, _, _, _, _, h => by
    obtain ⟨b1, s1, hs, hr⟩ := h
    rw [List.flatMap_cons]
    exact runFoldE_append step _ _ _ _ _ _ _ _ hs (runFoldE_flat step g l _ _ _ _ hr)

theorem runFoldE_mono {α β : Type} (step step' : α → β → St → β → St → Prop)
    (hm : ∀ a b s b1 s1, step a b s b1 s1 → step' a b s b1 s1) :
    ∀ (l : List α) (b : β) (s : St) (b' : β) (s' : St),
      RunFoldE step l b s b' s' → RunFoldE step' l b s b' s'
  | [], _, _, _, _, h => h
  | _ :: l, _, _, _, _, h => by
    obtain ⟨b1, s1, hs, hr⟩ := h
    exact ⟨b1, s1, hm _ _ _ _ _ hs, runFoldE_mono step step' hm l _ _ _ _ hr⟩

theorem runFoldE_map {α γ β : Type} (step : α → β → St → β → St → Prop) (g : γ → α) :
    ∀ (l : List γ) (b : β) (s : St) (b' : β) (s' : St),
      RunFoldE (fun x => step (g x)) l b s b' s' → RunFoldE step (l.map g) b s b' s'
  | [], _, _, _, _, h => h
  | _ :: l, _, _, _, _, h => by
    obtain ⟨b1, s1, hs, hr⟩ := h
    exact ⟨b1, s1, hs, runFoldE_map step g l _ _ _ _ hr⟩

theorem runFoldE_all {α β : Type} (P : α → Prop) (step : α → β → St → β → St → Prop) :
    ∀ (l : List α) (b : β) (s : St) (b' : β) (s' : St),
      RunFoldE (fun a b s b1 s1 => P a ∧ step a b s b1 s1) l b s b' s' →
      (∀ a ∈ l, P a) ∧ RunFoldE step l b s b' s'
  | [], _, _, _, _, h => ⟨fun _ ha => absurd ha (List.not_mem_nil), h⟩
  | a :: l, _, _, _, _, h => by
    obtain ⟨b1, s1, ⟨hp, hs⟩, hr⟩ := h
    obtain ⟨ha, hr'⟩ := runFoldE_all P step l b1 s1 _ _ hr
    refine ⟨fun x hx => ?_, b1, s1, hs, hr'⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hp
    · exact ha x hx

end VerifiableInference.Desc.First.TailClaims.Law
