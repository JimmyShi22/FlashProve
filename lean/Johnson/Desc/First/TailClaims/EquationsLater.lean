-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/EquationsLater.lean: the ledger that "K8.equations" returns, and the
ledger behind the adding of any list to it, are LATER ledgers than the one handed in: what lies under a
slot that is filled stays there; and if the three arrays have one entry a slot in front, so they have
behind (PscRun.Later, OnBytes/Tie/Pv/Psc/PscLater.lean; of a ledger without these sizes that clause says
nothing).

Definitions, statements and proofs. No routine of `verify-on-bytes` is named. USED OF THE FILES
UNDER OnBytes/, ON RECORDS AND PLAIN DATA ALONE: the record Fork; PscRun.Later with Later.refl,
Later.trans, paid_later, hideRun_keeps; PscRun.SlotsSame with SlotsSame.later.
Main names:
  Goes R x: where the routine x returns, its record behind stands in the relation R to its record in
    front. Goes.pure … Goes.change: for a relation that is reflexive and transitive.
  later_all: every routine of Equations.lean leads to a later ledger.
  eq_later: so does "K8.equations". addAll_slots: the adding leaves the slots, where the ledger in front
    has one coefficient a slot.
  eq_link_later: from the ledger at which the list is made to the ledger behind the adding, under that
    same premise at the first.
Limits: from a yes alone.

-/
import Johnson.Desc.First.TailClaims.EquationsFrame
import OnBytes.Tie.Pv.Psc.PscLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open OnBytes.PscRun (Later SlotsSame)

/-- Where the routine returns, its record behind stands in the relation R to its record in front. -/
def Goes (R : Fork → Fork → Prop) {α : Type} (x : EqM α) : Prop :=
  ∀ (front : Nat) (s s' : St) (a : α), x front s = .ok (a, s') → R s.1 s'.1

/-- Reflexive and transitive. -/
structure Pre (R : Fork → Fork → Prop) : Prop where
  refl : ∀ F, R F F
  trans : ∀ {F G H}, R F G → R G H → R F H

section
variable {R : Fork → Fork → Prop} (hR : Pre R)
include hR

theorem Goes.pure {α : Type} (a : α) : Goes R (Pure.pure a : EqM α) := by
  intro front s s' x h
  rw [((eq_pure_ok _ _ _ _ _).1 h).2]
  exact hR.refl _

theorem Goes.bind {α β : Type} {x : EqM α} {f : α → EqM β} (hx : Goes R x)
    (hf : ∀ a, Goes R (f a)) : Goes R (x >>= f) := by
  intro front s s' b h
  obtain ⟨a, s1, h1, h2⟩ := (eq_bind_ok _ _ _ _ _).1 h
  exact hR.trans (hx _ _ _ _ h1) (hf a _ _ _ _ h2)

omit hR in
theorem Goes.ite {α : Type} (c : Prop) [Decidable c] {x x' : EqM α} (h : Goes R x)
    (h' : Goes R x') : Goes R (if c then x else x') := by
  by_cases q : c
  · rw [if_pos q]; exact h
  · rw [if_neg q]; exact h'

theorem Goes.forInList {α β : Type} {f : α → β → EqM (ForInStep β)} (h : ∀ a b, Goes R (f a b)) :
    ∀ (l : List α) (b : β), Goes R (forIn l b f)
  | [], b => by
    rw [List.forIn_nil]
    exact Goes.pure hR b
  | a :: l, b => by
    rw [List.forIn_cons]
    refine Goes.bind hR (h a b) fun r => ?_
    cases r with
    | done b' => exact Goes.pure hR b'
    | yield b' => exact Goes.forInList h l b'

theorem Goes.forInArray {α β : Type} {f : α → β → EqM (ForInStep β)} (h : ∀ a b, Goes R (f a b))
    (as : Array α) (b : β) : Goes R (forIn as b f) := by
  rw [← Array.forIn_toList]
  exact Goes.forInList hR h _ b

theorem Goes.mustAs (n : String) (b : Bool) : Goes R (EqM.mustAs n b) := by
  intro front s s' a h
  rw [(eq_must_ok h).2]
  exact hR.refl _

theorem Goes.testAs (n : String) (b : Bool) : Goes R (EqM.testAs n b) := Goes.mustAs hR n b

theorem Goes.get {α : Type} (n : String) (o : Option α) : Goes R (EqM.get n o) := by
  intro front s s' a h
  rw [(eq_get_ok h).2]
  exact hR.refl _

theorem Goes.ask {α : Type} (n : String) (f : Fork → Option α) : Goes R (EqM.ask n f) := by
  intro front s s' a h
  rw [(eq_ask_ok h).2]
  exact hR.refl _

theorem Goes.claims : Goes R EqM.claims := by
  intro front s s' a h
  rw [(eq_claims_ok h).2]
  exact hR.refl _

theorem Goes.emit (c : Claim) : Goes R (EqM.emit c) := by
  intro front s s' a h
  rw [emit_ok h]
  exact hR.refl _

end

theorem Goes.paid {R : Fork → Fork → Prop} (hp : ∀ F i, R F (F.paid i)) (i : Nat) :
    Goes R (EqM.paid i) := by
  intro front s s' a h
  obtain ⟨F', hF, rfl⟩ := (eq_liftF_ok _ _ _ _ _).1 h
  obtain rfl : s.1.paid i = F' := congrArg Prod.snd (Except.ok.inj hF)
  exact hp _ _

theorem Goes.change {R : Fork → Fork → Prop} (n : String) {f : Fork → Option Fork}
    (hf : ∀ F F', f F = some F' → R F F') : Goes R (EqM.change n f) := by
  intro front s s' a h
  obtain ⟨F', hF, rfl⟩ := (eq_liftF_ok _ _ _ _ _).1 h
  unfold ForkM.change at hF
  cases e : f s.1 with
  | none => rw [e] at hF; cases hF
  | some G =>
    rw [e] at hF
    obtain rfl : G = F' := congrArg Prod.snd (Except.ok.inj hF)
    exact hf _ _ e

/-! ## Later -/

theorem preLater : Pre Later := ⟨Later.refl, fun a b => a.trans b⟩

theorem later_pscRow (p : Psc) (S0 : E) (kept : Aff) : Goes Later (eqPscRow p S0 kept) := by
  unfold eqPscRow
  exact Goes.bind preLater (Goes.mustAs preLater _ _) fun _ =>
    Goes.bind preLater (Goes.change _ fun _ _ e => OnBytes.PscRun.hideRun_keeps e) fun _ =>
      Goes.pure preLater _

theorem later_keys (tl : HTailF2) : Goes Later (eqKeys tl) := by
  unfold eqKeys eqPaddingLaid eqJoinAdded
  repeat (first
    | exact Goes.pure preLater _
    | exact Goes.claims preLater
    | exact Goes.mustAs preLater _ _
    | exact Goes.get preLater _ _
    | exact Goes.paid OnBytes.PscRun.paid_later _
    | exact Goes.emit preLater _
    | apply Goes.forInList preLater
    | apply Goes.forInArray preLater
    | apply Goes.ite
    | apply Goes.bind preLater
    | (show ∀ _ _, Goes Later _; intro _ _)
    | (show ∀ _, Goes Later _; intro _)
    | (dsimp only)
    | split)

theorem later_counts (tl : HTailF2) : Goes Later (eqCounts tl) := by
  unfold eqCounts eqPlanesAdded
  repeat (first
    | exact Goes.pure preLater _
    | exact Goes.mustAs preLater _ _
    | exact Goes.get preLater _ _
    | exact Goes.paid OnBytes.PscRun.paid_later _
    | exact Goes.emit preLater _
    | exact later_pscRow _ _ _
    | apply Goes.bind preLater
    | (show ∀ _, Goes Later _; intro _)
    | (dsimp only)
    | split)

theorem later_tie (tl : HTailF2) (mu : Nat) : Goes Later (eqTie tl mu) := by
  unfold eqTie
  repeat (first
    | exact Goes.pure preLater _
    | exact Goes.get preLater _ _
    | exact Goes.emit preLater _
    | apply Goes.bind preLater
    | (show ∀ _, Goes Later _; intro _)
    | (dsimp only))

theorem later_read (tl : HTailF2) (Fn : HFun) (sg laid : Nat) (sums : E) :
    Goes Later (eqRead tl Fn sg laid sums) := by
  unfold eqRead
  repeat (first
    | exact Goes.pure preLater _
    | exact Goes.get preLater _ _
    | exact Goes.ask preLater _ _
    | exact Goes.mustAs preLater _ _
    | exact Goes.testAs preLater _ _
    | exact Goes.emit preLater _
    | apply Goes.bind preLater
    | (show ∀ _, Goes Later _; intro _)
    | (dsimp only)
    | split)

theorem later_weights (tl : HTailF2) : Goes Later (eqWeights tl) := by
  unfold eqWeights
  exact Goes.bind preLater (Goes.ask preLater _ _) fun _ => Goes.get preLater _ _

theorem later_all (tl : HTailF2) (funs : Array HFun) : Goes Later (eqAll tl funs) := by
  unfold eqAll
  repeat (first
    | exact Goes.pure preLater _
    | exact Goes.claims preLater
    | exact Goes.mustAs preLater _ _
    | exact Goes.testAs preLater _ _
    | exact Goes.get preLater _ _
    | exact Goes.ask preLater _ _
    | exact later_keys _
    | exact later_counts _
    | exact later_weights _
    | exact later_tie _ _
    | exact later_read _ _ _ _ _
    | apply Goes.forInList preLater
    | apply Goes.forInArray preLater
    | apply Goes.ite
    | apply Goes.bind preLater
    | (show ∀ _ _, Goes Later _; intro _ _)
    | (show ∀ _, Goes Later _; intro _)
    | (dsimp only)
    | split)

/-- **The ledger that "K8.equations" returns is a later ledger than the one handed in.** -/
theorem eq_later {front : Nat} {tl tl' : HTailF2} {funs : Array HFun} {F F1 : Fork}
    {cls : List Claim} (h : equations front tl funs F = .ok (tl', F1, cls)) : Later F F1 := by
  unfold equations at h
  cases e : eqAll tl funs front (F, #[]) with
  | error x => rw [e] at h; cases h
  | ok x =>
    rw [e] at h
    obtain ⟨tlx, Fx, arr⟩ := x
    obtain rfl : Fx = F1 := congrArg (fun y => y.2.1) (Except.ok.inj h)
    exact later_all tl funs _ _ _ _ e

/-- The adding leaves the slots. -/
theorem addAll_slots {l : List Claim} {A A' : Fork} (hs : A.LS.size = A.ns)
    (h : addAll A l = some A') : SlotsSame A A' := by
  obtain ⟨o, -, -⟩ := addAll_keeps l A A' hs h
  exact ⟨o.ns, o.next, o.vp, o.mf, o.gotF⟩

/-- **From the ledger at which the list is made to the ledger behind the adding: later.** -/
theorem eq_link_later {front : Nat} {tl tl' : HTailF2} {funs : Array HFun} {F F1 G : Fork}
    {cls l : List Claim} (hs : F.LS.size = F.ns)
    (h : equations front tl funs F = .ok (tl', F1, cls)) (hadd : addAll F1 l = some G) :
    Later F F1 ∧ SlotsSame F1 G ∧ Later F G := by
  have os := eq_side h
  have s1 : F1.LS.size = F1.ns := by
    rw [os.LS, os.ns]
    exact hs
  have a := eq_later h
  have b := addAll_slots s1 hadd
  exact ⟨a, b, a.trans b.later⟩

end VerifiableInference.Desc.First.TailClaims.Law

#print axioms VerifiableInference.Desc.First.TailClaims.Law.eq_later
#print axioms VerifiableInference.Desc.First.TailClaims.Law.eq_link_later
