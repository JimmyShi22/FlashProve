-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/EquationsTame.lean: two routines of Equations.lean (eqKeys, eqCounts)
change of the record the side alone (slots, marks) and only lay claims behind the list; the adding
changes the sums alone.

Definitions, statements and proofs. No routine of `verify-on-bytes` is named. USED OF ITS
FILES, ON RECORDS AND PLAIN DATA ALONE: the record Fork with its plain functions hide,
hideStep, hideRun, paid; the record Psc.
Main names:
  OnlySide P P': P' is P but for the side. Tame x: where x returns, the record has changed on the side
    alone and the list has only grown at its end. tame_keys, tame_counts.
  addAll_keeps: the adding changes the sums alone, counts the claims, keeps "one coefficient a slot".
Limits: nothing where a step refuses.

-/
import Johnson.Desc.First.TailClaims.EquationsTotal

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSimpArgs false

namespace VerifiableInference.Desc.First.TailClaims.Law
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc

/-- P' is P but for the side. -/
structure OnlySide (P P' : Fork) : Prop where
  trees : P'.trees = P.trees
  ns : P'.ns = P.ns
  LS : P'.LS = P.LS
  c0 : P'.c0 = P.c0
  nClaim : P'.nClaim = P.nClaim
  theta : P'.theta = P.theta
  drawn : P'.thetaDrawnF = P.thetaDrawnF
  plan : P'.planClaimsF = P.planClaimsF
  kapMap : P'.kapMapF = P.kapMapF
  door : P'.doorShutF = P.doorShutF

theorem OnlySide.refl (P : Fork) : OnlySide P P := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem OnlySide.trans {P Q R : Fork} (a : OnlySide P Q) (b : OnlySide Q R) : OnlySide P R :=
  ⟨b.trees.trans a.trees, b.ns.trans a.ns, b.LS.trans a.LS, b.c0.trans a.c0,
    b.nClaim.trans a.nClaim, b.theta.trans a.theta, b.drawn.trans a.drawn, b.plan.trans a.plan,
    b.kapMap.trans a.kapMap, b.door.trans a.door⟩

theorem hide_only {F F' : Fork} {j : Nat} {x f : E} (e : F.hide j x f = some F') :
    OnlySide F F' := by
  unfold Fork.hide at e
  split at e
  · obtain rfl := Option.some.inj e
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases e

theorem hideSteps_only (f : E) : ∀ (l : List E) (j : Nat) (F : Fork) (x : Nat × Fork),
    l.foldlM (Fork.hideStep f) (j, F) = some x → OnlySide F x.2
  | [], j, F, x, e => by
    obtain rfl : (j, F) = x := by simpa using e
    exact OnlySide.refl F
  | y :: l, j, F, x, e => by
    rw [List.foldlM_cons] at e
    cases hH : F.hide j y f with
    | none => simp [Fork.hideStep, hH] at e
    | some H =>
      have e' : l.foldlM (Fork.hideStep f) (j + 1, H) = some x := by
        simpa [Fork.hideStep, hH] using e
      exact (hide_only hH).trans (hideSteps_only f l (j + 1) H x e')

theorem hideRun_only {F F' : Fork} {first : Nat} {v : Array E} {f : E}
    (e : F.hideRun first v f = some F') : OnlySide F F' := by
  unfold Fork.hideRun at e
  rw [← Array.foldlM_toList] at e
  split at e
  · rename_i x hx
    obtain rfl := Option.some.inj e
    exact hideSteps_only f v.toList first F x hx
  · cases e

/-! ## The routines are tame -/

def Tame {α : Type} (x : EqM α) : Prop :=
  ∀ (front : Nat) (s s' : St) (a : α), x front s = .ok (a, s') →
    OnlySide s.1 s'.1 ∧ ∃ new : List Claim, s'.2 = s.2 ++ new.toArray

theorem tame_same (s : St) : OnlySide s.1 s.1 ∧ ∃ new : List Claim, s.2 = s.2 ++ new.toArray :=
  ⟨OnlySide.refl _, [], by simp⟩

theorem Tame.pure {α : Type} (a : α) : Tame (Pure.pure a : EqM α) := by
  intro front s s' x h
  rw [((eq_pure_ok _ _ _ _ _).1 h).2]
  exact tame_same s

theorem Tame.bind {α β : Type} {x : EqM α} {f : α → EqM β} (hx : Tame x)
    (hf : ∀ a, Tame (f a)) : Tame (x >>= f) := by
  intro front s s' b h
  obtain ⟨a, s1, h1, h2⟩ := (eq_bind_ok _ _ _ _ _).1 h
  obtain ⟨o1, n1, e1⟩ := hx _ _ _ _ h1
  obtain ⟨o2, n2, e2⟩ := hf a _ _ _ _ h2
  exact ⟨o1.trans o2, n1 ++ n2, by rw [e2, e1]; simp⟩

theorem Tame.ite {α : Type} (c : Prop) [Decidable c] {x x' : EqM α} (h : Tame x)
    (h' : Tame x') : Tame (if c then x else x') := by
  by_cases q : c
  · rw [if_pos q]; exact h
  · rw [if_neg q]; exact h'

theorem Tame.forInList {α β : Type} {f : α → β → EqM (ForInStep β)} (h : ∀ a b, Tame (f a b)) :
    ∀ (l : List α) (b : β), Tame (forIn l b f)
  | [], b => by
    rw [List.forIn_nil]
    exact Tame.pure b
  | a :: l, b => by
    rw [List.forIn_cons]
    refine Tame.bind (h a b) fun r => ?_
    cases r with
    | done b' => exact Tame.pure b'
    | yield b' => exact Tame.forInList h l b'

theorem Tame.forInArray {α β : Type} {f : α → β → EqM (ForInStep β)} (h : ∀ a b, Tame (f a b))
    (as : Array α) (b : β) : Tame (forIn as b f) := by
  rw [← Array.forIn_toList]
  exact Tame.forInList h _ b

theorem Tame.mustAs (n : String) (b : Bool) : Tame (EqM.mustAs n b) := by
  intro front s s' a h
  rw [(eq_must_ok h).2]
  exact tame_same s

theorem Tame.testAs (n : String) (b : Bool) : Tame (EqM.testAs n b) := Tame.mustAs n b

theorem Tame.get {α : Type} (n : String) (o : Option α) : Tame (EqM.get n o) := by
  intro front s s' a h
  rw [(eq_get_ok h).2]
  exact tame_same s

theorem Tame.ask {α : Type} (n : String) (f : Fork → Option α) : Tame (EqM.ask n f) := by
  intro front s s' a h
  rw [(eq_ask_ok h).2]
  exact tame_same s

theorem Tame.claims : Tame EqM.claims := by
  intro front s s' a h
  rw [(eq_claims_ok h).2]
  exact tame_same s

theorem Tame.emit (c : Claim) : Tame (EqM.emit c) := by
  intro front s s' a h
  rw [emit_ok h]
  exact ⟨OnlySide.refl _, [c], push_one _ _⟩

theorem Tame.paid (i : Nat) : Tame (EqM.paid i) := by
  intro front s s' a h
  obtain ⟨F', hF, rfl⟩ := (eq_liftF_ok _ _ _ _ _).1 h
  obtain rfl : s.1.paid i = F' := congrArg Prod.snd (Except.ok.inj hF)
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, [], by simp⟩

theorem Tame.change (n : String) {f : Fork → Option Fork}
    (hf : ∀ F F', f F = some F' → OnlySide F F') : Tame (EqM.change n f) := by
  intro front s s' a h
  obtain ⟨F', hF, rfl⟩ := (eq_liftF_ok _ _ _ _ _).1 h
  unfold ForkM.change at hF
  cases e : f s.1 with
  | none => rw [e] at hF; cases hF
  | some G =>
    rw [e] at hF
    obtain rfl : G = F' := congrArg Prod.snd (Except.ok.inj hF)
    exact ⟨hf _ _ e, [], by simp⟩

theorem tame_pscRow (p : Psc) (S0 : E) (kept : Aff) : Tame (eqPscRow p S0 kept) := by
  unfold eqPscRow
  exact Tame.bind (Tame.mustAs _ _) fun _ =>
    Tame.bind (Tame.change _ fun _ _ e => hideRun_only e) fun _ => Tame.pure _

theorem tame_keys (tl : HTailF2) : Tame (eqKeys tl) := by
  unfold eqKeys eqPaddingLaid eqJoinAdded
  repeat (first
    | exact Tame.pure _
    | exact Tame.claims
    | exact Tame.mustAs _ _
    | exact Tame.get _ _
    | exact Tame.paid _
    | exact Tame.emit _
    | apply Tame.forInList
    | apply Tame.forInArray
    | apply Tame.ite
    | apply Tame.bind
    | (show ∀ _ _, Tame _; intro _ _)
    | (show ∀ _, Tame _; intro _)
    | (dsimp only)
    | split)

theorem tame_counts (tl : HTailF2) : Tame (eqCounts tl) := by
  unfold eqCounts eqPlanesAdded
  repeat (first
    | exact Tame.pure _
    | exact Tame.mustAs _ _
    | exact Tame.get _ _
    | exact Tame.paid _
    | exact Tame.emit _
    | exact tame_pscRow _ _ _
    | apply Tame.bind
    | (show ∀ _, Tame _; intro _)
    | (dsimp only)
    | split)

/-! ## The adding -/

theorem OnlySums.refl (P : Fork) : OnlySums P P :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem OnlySums.trans {P Q R : Fork} (a : OnlySums P Q) (b : OnlySums Q R) : OnlySums P R :=
  ⟨b.ns.trans a.ns, b.next.trans a.next, b.vp.trans a.vp, b.mf.trans a.mf, b.gotF.trans a.gotF,
    b.owed.trans a.owed, b.theta.trans a.theta, b.drawn.trans a.drawn, b.plan.trans a.plan,
    b.door.trans a.door, b.trees.trans a.trees⟩

theorem addAll_keeps : ∀ (l : List Claim) (A A' : Fork), A.LS.size = A.ns →
    addAll A l = some A' → OnlySums A A' ∧ A'.nClaim = A.nClaim + l.length ∧ A'.LS.size = A'.ns
  | [], A, A', hs, h => by
    obtain rfl : A = A' := Option.some.inj h
    exact ⟨OnlySums.refl A, rfl, hs⟩
  | c :: l, A, A', hs, h => by
    rw [addAll_cons] at h
    obtain ⟨B, hB, h'⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨k, A1, w, A2, a1, _, a2, a3⟩ := addOne (addClaim_one hB)
    obtain ⟨o1, n1, s1⟩ := onlySums_claim hs a1 a2 a3
    obtain ⟨o2, n2, s2⟩ := addAll_keeps l B A' s1 h'
    exact ⟨o1.trans o2, by rw [n2, n1, List.length_cons]; omega, s2⟩

end VerifiableInference.Desc.First.TailClaims.Law
