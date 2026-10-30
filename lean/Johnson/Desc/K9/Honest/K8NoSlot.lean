-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K9/Honest/K8NoSlot.lean (for kind K9's count): THE TIES AND READS OF THE LIST "K8.equations" NAME NO SLOT.
Statements and proofs on the list's own text (Johnson/Desc/First/TailClaims/Equations.lean); no block, no prover; no
goal is stated.

  `Emits Q x`       wherever the routine x returns, the claims that it has laid on the list all meet Q. With the
                    rules for the routines' building stones, after `Tame`
                    (Johnson/Desc/First/TailClaims/EquationsTame.lean), whose shape they follow
  `NoSlot c`        the claim's form has no pair (slot, coefficient)
  `emits_tie`, `emits_read`, `emits_tail`   a tie, a read, and the list's whole text behind its first four claims
                    (`eqTail`, EquationsTotal.lean) lay claims without a slot alone
  `k8_noSlot`       **a yes of "K8.equations": the list is four claims, and then claims that name no slot**
  `k8_drop`         the same, said of `k8.drop 4`

The proof of `k8_noSlot` walks the list's head as the library's `eq_split` does
(Johnson/Desc/First/TailClaims/EquationsAny.lean).
WHAT IS NOT CLAIMED. Anything on the first four claims: three of them name slots. Anything on the entries and runs
that ties and reads name. Nothing on any property.

-/
import Johnson.Desc.First.TailClaims.EquationsAny
import Johnson.Desc.First.TailClaims.EquationsFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9H
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open VerifiableInference.Desc.First.TailClaims VerifiableInference.Desc.First.TailClaims.Law

/-- Wherever x returns, the claims that it has laid all meet Q. -/
def Emits (Q : Claim → Prop) {α : Type} (x : EqM α) : Prop :=
  ∀ (front : Nat) (s s' : St) (a : α), x front s = .ok (a, s') →
    ∃ new : List Claim, s'.2 = s.2 ++ new.toArray ∧ ∀ c ∈ new, Q c

section rules
variable {Q : Claim → Prop}

theorem emits_same (s : St) : ∃ new : List Claim, s.2 = s.2 ++ new.toArray ∧ ∀ c ∈ new, Q c :=
  ⟨[], by simp, fun _ h => nomatch h⟩

theorem Emits.pure {α : Type} (a : α) : Emits Q (Pure.pure a : EqM α) := by
  intro front s s' x h
  rw [((eq_pure_ok _ _ _ _ _).1 h).2]
  exact emits_same s

theorem Emits.bind {α β : Type} {x : EqM α} {f : α → EqM β} (hx : Emits Q x)
    (hf : ∀ a, Emits Q (f a)) : Emits Q (x >>= f) := by
  intro front s s' b h
  obtain ⟨a, s1, h1, h2⟩ := (eq_bind_ok _ _ _ _ _).1 h
  obtain ⟨n1, e1, q1⟩ := hx _ _ _ _ h1
  obtain ⟨n2, e2, q2⟩ := hf a _ _ _ _ h2
  refine ⟨n1 ++ n2, by rw [e2, e1]; simp, fun c hc => ?_⟩
  rcases List.mem_append.1 hc with h | h
  · exact q1 c h
  · exact q2 c h

theorem Emits.ite {α : Type} (c : Prop) [Decidable c] {x x' : EqM α} (h : Emits Q x)
    (h' : Emits Q x') : Emits Q (if c then x else x') := by
  by_cases q : c
  · rw [if_pos q]; exact h
  · rw [if_neg q]; exact h'

theorem Emits.forInList {α β : Type} {f : α → β → EqM (ForInStep β)} (h : ∀ a b, Emits Q (f a b)) :
    ∀ (l : List α) (b : β), Emits Q (forIn l b f)
  | [], b => by
    rw [List.forIn_nil]
    exact Emits.pure b
  | a :: l, b => by
    rw [List.forIn_cons]
    refine Emits.bind (h a b) fun r => ?_
    cases r with
    | done b' => exact Emits.pure b'
    | yield b' => exact Emits.forInList h l b'

theorem Emits.forInArray {α β : Type} {f : α → β → EqM (ForInStep β)} (h : ∀ a b, Emits Q (f a b))
    (as : Array α) (b : β) : Emits Q (forIn as b f) := by
  rw [← Array.forIn_toList]
  exact Emits.forInList h _ b

theorem Emits.mustAs (n : String) (b : Bool) : Emits Q (EqM.mustAs n b) := by
  intro front s s' a h
  rw [(eq_must_ok h).2]
  exact emits_same s

theorem Emits.testAs (n : String) (b : Bool) : Emits Q (EqM.testAs n b) := Emits.mustAs n b

theorem Emits.get {α : Type} (n : String) (o : Option α) : Emits Q (EqM.get n o) := by
  intro front s s' a h
  rw [(eq_get_ok h).2]
  exact emits_same s

theorem Emits.ask {α : Type} (n : String) (f : Fork → Option α) : Emits Q (EqM.ask n f) := by
  intro front s s' a h
  rw [(eq_ask_ok h).2]
  exact emits_same s

theorem Emits.claims : Emits Q EqM.claims := by
  intro front s s' a h
  rw [(eq_claims_ok h).2]
  exact emits_same s

theorem Emits.emit (c : Claim) (hc : Q c) : Emits Q (EqM.emit c) := by
  intro front s s' a h
  rw [emit_ok h]
  exact ⟨[c], push_one _ _, fun d hd => by rw [List.mem_singleton.1 hd]; exact hc⟩

end rules

/-- The claim's form has no pair (slot, coefficient). -/
def NoSlot (c : Claim) : Prop := c.form.slots = #[]

theorem emits_tie (tl : HTailF2) (mu : Nat) : Emits NoSlot (eqTie tl mu) := by
  unfold eqTie
  repeat (first
    | exact Emits.pure _
    | exact Emits.get _ _
    | exact Emits.emit _ rfl
    | apply Emits.bind
    | (show ∀ _, Emits NoSlot _; intro _)
    | (dsimp only))

theorem emits_read (tl : HTailF2) (Fn : HFun) (sg laid : Nat) (sums : E) :
    Emits NoSlot (eqRead tl Fn sg laid sums) := by
  unfold eqRead
  repeat (first
    | exact Emits.pure _
    | exact Emits.get _ _
    | exact Emits.ask _ _
    | exact Emits.mustAs _ _
    | exact Emits.testAs _ _
    | exact Emits.emit _ rfl
    | apply Emits.bind
    | (show ∀ _, Emits NoSlot _; intro _)
    | (dsimp only)
    | split)

theorem emits_weights (tl : HTailF2) : Emits NoSlot (eqWeights tl) := by
  unfold eqWeights
  exact Emits.bind (Emits.ask _ _) fun _ => Emits.get _ _

theorem emits_tail (before : Nat) (tl : HTailF2) (funs : Array HFun) :
    Emits NoSlot (eqTail before tl funs) := by
  unfold eqTail
  repeat (first
    | exact Emits.pure _
    | exact Emits.claims
    | exact Emits.mustAs _ _
    | exact Emits.testAs _ _
    | exact Emits.get _ _
    | exact Emits.ask _ _
    | exact emits_weights _
    | exact emits_tie _ _
    | exact emits_read _ _ _ _ _
    | apply Emits.forInList
    | apply Emits.forInArray
    | apply Emits.ite
    | apply Emits.bind
    | (show ∀ _ _, Emits NoSlot _; intro _ _)
    | (show ∀ _, Emits NoSlot _; intro _)
    | (dsimp only)
    | split)

/-- **A yes of "K8.equations": four claims, and then claims that name no slot.** -/
theorem k8_noSlot {front : Nat} {tl tl' : HTailF2} {funs : Array HFun} {F F1 : Fork}
    {cls : List Claim} (h : equations front tl funs F = .ok (tl', F1, cls)) :
    ∃ four rest : List Claim, cls = four ++ rest ∧ four.length = 4 ∧ ∀ c ∈ rest, NoSlot c := by
  unfold equations at h
  cases e : eqAll tl funs front (F, #[]) with
  | error x => rw [e] at h; cases h
  | ok x =>
    rw [e] at h
    obtain ⟨tlx, Fx, arr⟩ := x
    have h' := Except.ok.inj h
    have hcl : arr.toList = cls := congrArg (fun y => y.2.2) h'
    rw [eqAll_split] at e
    obtain ⟨u1, t1, h1, k1⟩ := (eq_bind_ok _ _ _ _ _).1 e
    rw [(eq_must_ok h1).2] at k1
    obtain ⟨u2, t2, h2, k2⟩ := (eq_bind_ok _ _ _ _ _).1 k1
    rw [(eq_must_ok h2).2] at k2
    obtain ⟨z, t3, h3, k3⟩ := (eq_bind_ok _ _ _ _ _).1 k2
    rw [(eq_ask_ok h3).2] at k3
    obtain ⟨u4, t4, h4, k4⟩ := (eq_bind_ok _ _ _ _ _).1 k3
    rw [(eq_test_ok h4).2] at k4
    obtain ⟨g', t5, h5, k5⟩ := (eq_bind_ok _ _ _ _ _).1 k4
    rw [(eq_get_ok h5).2] at k5
    obtain ⟨u6, t6, h6, k6⟩ := (eq_bind_ok _ _ _ _ _).1 k5
    rw [(eq_must_ok h6).2] at k6
    unfold eqRest at k6
    obtain ⟨before, t7, h7, k7⟩ := (eq_bind_ok _ _ _ _ _).1 k6
    obtain ⟨hbef, et7⟩ := eq_claims_ok h7
    rw [et7] at k7
    obtain ⟨tla, s1, h8, k8⟩ := (eq_bind_ok _ _ _ _ _).1 k7
    obtain ⟨tlb, s2, h9, k9⟩ := (eq_bind_ok _ _ _ _ _).1 k8
    obtain ⟨new, hnew, hq⟩ := emits_tail before tlb funs _ _ _ _ k9
    -- the list's own count in front of its tail: four
    have h44 : front + s2.2.size - before = 4 := by
      unfold eqTail at k9
      obtain ⟨n0, t0, h0, k0⟩ := (eq_bind_ok _ _ _ _ _).1 k9
      obtain ⟨en0, et0⟩ := eq_claims_ok h0
      rw [en0, et0] at k0
      obtain ⟨_, _, hm, _⟩ := (eq_bind_ok _ _ _ _ _).1 k0
      exact beq_iff_eq.1 (eq_must_ok hm).1
    have hsz : s2.2.size = 4 := by
      rw [hbef] at h44
      simp at h44
      omega
    have harr : arr = s2.2 ++ new.toArray := hnew
    refine ⟨s2.2.toList, new, ?_, by simpa using hsz, hq⟩
    rw [← hcl, harr]
    simp

/-- The same, of `k8.drop 4`. -/
theorem k8_drop {front : Nat} {tl tl' : HTailF2} {funs : Array HFun} {F F1 : Fork}
    {cls : List Claim} (h : equations front tl funs F = .ok (tl', F1, cls)) :
    ∀ c ∈ cls.drop 4, NoSlot c := by
  obtain ⟨four, rest, e, h4, hq⟩ := k8_noSlot h
  rw [e, ← h4, List.drop_left]
  exact hq

end VerifiableInference.Desc.K9H

#print axioms VerifiableInference.Desc.K9H.emits_tie
#print axioms VerifiableInference.Desc.K9H.emits_read
#print axioms VerifiableInference.Desc.K9H.emits_tail
#print axioms VerifiableInference.Desc.K9H.k8_noSlot
#print axioms VerifiableInference.Desc.K9H.k8_drop
