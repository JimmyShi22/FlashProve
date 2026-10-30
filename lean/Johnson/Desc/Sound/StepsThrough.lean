-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/StepsThrough.lean: THE LAWS `Block.Steps` | `RunsStep` | `AfterStep` | `Calls`
(Johnson/Desc/Sound/FoldSteps.lean) THROUGH Block.lean's OWN MAKERS OF BLOCKS: `roundlessBlock` ·
`Block.andThen` · `Block.lift` · `Block.liftPart` · `Block.inside` · a block with another place
written in; AND TWO RELATIONS AT ONCE (`preAnd`, `stepsAnd`, `runsAnd`, `afterAnd`, `Traced.mono`).
Theorems with their proofs, each by unfolding.

Why. The blocks that ride are made with these makers: a kind's text is typed at its own part of the
record and lifted; two blocks stand at one place by `andThen`; the driver writes the place into a
block. Whoever pays `Steps` at a real block pays it at the kind's own text and carries it through.
(Johnson/Desc/Sound/FoldHeard.lean has the like for
`Leaves` alone.)

Limits. Tools. No block of the protocol is named. `Calls` does not conjoin from two `Calls`: each
has its own "there is": it is owed once, at the conjunction. Nothing on soundness. Terms:
lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.FoldStepsProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S T Cl : Type}

theorem stepsQuiet {R : S → S → Prop} (name : String) (chain : Nat) (link : Option Nat)
    (piece : Nat) (f : S → Except String S) (h : ∀ s s', f s = .ok s' → R s s') :
    (roundlessBlock (Cl := Cl) name chain link piece f).Steps R :=
  fun s _ _ s' H => h s s' H

/-- Another place, another name or another test on the plan written in: the decision is the same. -/
theorem stepsOfDecide {R : S → S → Prop} (b c : Block S Cl) (e : c.decide = b.decide)
    (h : b.Steps R) : c.Steps R :=
  fun s rs gs s' H => h s rs gs s' (e ▸ H)

theorem runsOfClaims {R : S → S → Prop} (b c : Block S Cl) (e : c.claims = b.claims)
    (h : b.RunsStep R) : c.RunsStep R :=
  fun x hx => h x (e ▸ hx)

theorem afterOfAfter {R : S → S → Prop} (b c : Block S Cl) (e : c.after = b.after)
    (h : b.AfterStep R) : c.AfterStep R :=
  fun x hx => h x (e ▸ hx)

theorem callsOfDecide {R : S → S → Prop} {Q : S → List Fmt.RoundView → S → List Cl → S → S → Prop}
    (batch batch' : (S → Except String (List Cl × S)) → Block S Cl)
    (e : ∀ f, (batch' f).decide = (batch f).decide) (h : Calls R Q batch) : Calls R Q batch' :=
  fun f s rs gs s' H => h f s rs gs s' (e f ▸ H)

/-- The like for `CallsAt`: another place, name or test on the plan written into the block. -/
theorem callsAtOfDecide {R : S → S → Prop} {Q : S → List Fmt.RoundView → S → List Cl → S → S → Prop}
    (B B' : Block S Cl) (f : S → Except String (List Cl × S)) (e : B'.decide = B.decide)
    (h : CallsAt R Q B f) : CallsAt R Q B' f :=
  fun s rs gs s' H => h s rs gs s' (e ▸ H)

theorem stepsAndThen {R : S → S → Prop} (hR : Pre R) (name : String) (p q : Block S Cl)
    (hp : p.Steps R) (hq : q.Steps R) : (p.andThen name q).Steps R := by
  intro s rs gs s' H
  obtain ⟨m, hm, H'⟩ := bindOk
    (x := p.decide s (rs.take p.rounds.length) (gs.take p.openings)) H
  exact hR.trans _ _ _ (hp _ _ _ _ hm) (hq _ _ _ _ H')

theorem runsAndThen {R : S → S → Prop} (name : String) (p q : Block S Cl) (hp : p.RunsStep R)
    (hq : q.RunsStep R) : (p.andThen name q).RunsStep R := by
  intro c hc
  rcases List.mem_append.1 hc with h | h
  · exact hp c h
  · exact hq c h

theorem afterAndThen {R : S → S → Prop} (name : String) (p q : Block S Cl) (hp : p.AfterStep R)
    (hq : q.AfterStep R) : (p.andThen name q).AfterStep R := by
  intro c hc
  rcases List.mem_append.1 hc with h | h
  · exact hp c h
  · exact hq c h

/-- A block at a part, laid at a wider record: R₀ at the part gives R at the whole, where laying a
part that stands in R₀ to the part in front gives a record that stands in R to the record in front.
-/
theorem stepsLift {R₀ : S → S → Prop} {R : T → T → Prop} (get : T → S) (set : T → S → T)
    (b : Block S Cl) (hb : b.Steps R₀) (h : ∀ t s', R₀ (get t) s' → R t (set t s')) :
    (b.lift get set).Steps R := by
  intro t rs gs t' H
  obtain ⟨s', hs, e⟩ := mapOk (x := b.decide (get t) rs gs) H
  exact e ▸ h t s' (hb _ _ _ _ hs)

theorem runsLift {R₀ : S → S → Prop} {R : T → T → Prop} (get : T → S) (set : T → S → T)
    (b : Block S Cl) (hb : b.RunsStep R₀) (h : ∀ t s', R₀ (get t) s' → R t (set t s')) :
    (b.lift get set).RunsStep R := by
  intro c hc n t cl t' H
  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
  obtain ⟨y, hy, e⟩ := mapOk (x := c₀.2 n (get t)) H
  have e₂ : set t y.2 = t' := congrArg Prod.snd e
  exact e₂ ▸ h t y.2 (hb c₀ hc₀ n (get t) y.1 y.2 hy)

theorem afterLift {R₀ : S → S → Prop} {R : T → T → Prop} (get : T → S) (set : T → S → T)
    (b : Block S Cl) (hb : b.AfterStep R₀) (h : ∀ t s', R₀ (get t) s' → R t (set t s')) :
    (b.lift get set).AfterStep R := by
  intro c hc t t' H
  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
  obtain ⟨s', hs, e⟩ := mapOk (x := c₀.2 (get t)) H
  exact e ▸ h t s' (hb c₀ hc₀ (get t) s' hs)

theorem stepsLiftPart {R₀ : S → S → Prop} {R : T → T → Prop} (get? : T → Option S)
    (set : T → S → T) (b : Block S Cl) (hb : b.Steps R₀)
    (h : ∀ t p s', get? t = some p → R₀ p s' → R t (set t s')) :
    (b.liftPart get? set).Steps R := by
  intro t rs gs t' H
  obtain ⟨p, hp, H⟩ := bindOk (x := named "the part is not there" (get? t)) H
  obtain ⟨s', hs, e⟩ := mapOk H
  exact e ▸ h t p s' (namedOk hp) (hb _ _ _ _ hs)

theorem runsLiftPart {R₀ : S → S → Prop} {R : T → T → Prop} (get? : T → Option S)
    (set : T → S → T) (b : Block S Cl) (hb : b.RunsStep R₀)
    (h : ∀ t p s', get? t = some p → R₀ p s' → R t (set t s')) :
    (b.liftPart get? set).RunsStep R := by
  intro c hc n t cl t' H
  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
  obtain ⟨p, hp, H⟩ := bindOk (x := named "the part is not there" (get? t)) H
  obtain ⟨y, hy, e⟩ := mapOk H
  have e₂ : set t y.2 = t' := congrArg Prod.snd e
  exact e₂ ▸ h t p y.2 (namedOk hp) (hb c₀ hc₀ n p y.1 y.2 hy)

theorem afterLiftPart {R₀ : S → S → Prop} {R : T → T → Prop} (get? : T → Option S)
    (set : T → S → T) (b : Block S Cl) (hb : b.AfterStep R₀)
    (h : ∀ t p s', get? t = some p → R₀ p s' → R t (set t s')) :
    (b.liftPart get? set).AfterStep R := by
  intro c hc t t' H
  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
  obtain ⟨p, hp, H⟩ := bindOk (x := named "the part is not there" (get? t)) H
  obtain ⟨s', hs, e⟩ := mapOk H
  exact e ▸ h t p s' (namedOk hp) (hb c₀ hc₀ p s' hs)

/-- A block whose own record is born and dies inside it. -/
theorem stepsInside {R₀ : T → T → Prop} {R : S → S → Prop} (enter : S → Except String T)
    (b : Block T Cl) (leave : S → T → Except String S) (hb : b.Steps R₀)
    (h : ∀ s t t' s', enter s = .ok t → R₀ t t' → leave s t' = .ok s' → R s s') :
    (b.inside enter leave).Steps R := by
  intro s rs gs s' H
  obtain ⟨t, ht, H⟩ := bindOk (x := enter s) H
  obtain ⟨t', ht', H⟩ := bindOk (x := b.decide t rs gs) H
  exact h s t t' s' ht (hb _ _ _ _ ht') H

/-! ## Two relations at once -/

theorem preAnd {R₁ R₂ : S → S → Prop} (h₁ : Pre R₁) (h₂ : Pre R₂) :
    Pre fun a b => R₁ a b ∧ R₂ a b :=
  ⟨fun s => ⟨h₁.refl s, h₂.refl s⟩,
    fun a b c x y => ⟨h₁.trans a b c x.1 y.1, h₂.trans a b c x.2 y.2⟩⟩

theorem stepsAnd {R₁ R₂ : S → S → Prop} (b : Block S Cl) (h₁ : b.Steps R₁) (h₂ : b.Steps R₂) :
    b.Steps fun x y => R₁ x y ∧ R₂ x y :=
  fun s rs gs s' H => ⟨h₁ s rs gs s' H, h₂ s rs gs s' H⟩

theorem runsAnd {R₁ R₂ : S → S → Prop} (b : Block S Cl) (h₁ : b.RunsStep R₁)
    (h₂ : b.RunsStep R₂) : b.RunsStep fun x y => R₁ x y ∧ R₂ x y :=
  fun c hc n s cl s' H => ⟨h₁ c hc n s cl s' H, h₂ c hc n s cl s' H⟩

theorem afterAnd {R₁ R₂ : S → S → Prop} (b : Block S Cl) (h₁ : b.AfterStep R₁)
    (h₂ : b.AfterStep R₂) : b.AfterStep fun x y => R₁ x y ∧ R₂ x y :=
  fun c hc s s' H => ⟨h₁ c hc s s' H, h₂ c hc s s' H⟩

/-- **A trace at a stronger relation is a trace at a weaker one, AT THE SAME RECORDS.** -/
theorem Traced.mono {R R' : S → S → Prop} {Q : S → List Fmt.RoundView → S → List Cl → S → S → Prop}
    (hm : ∀ a b, R a b → R' a b) {L : Link S Cl} {h₁ : List (Block S Cl)} {b : Block S Cl}
    {ft : Nat} {s : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {t t₁ u₀ z u e : S} {cls : List Cl}
    (h : Traced R Q L h₁ b ft s rs cols t t₁ u₀ z u e cls) :
    Traced R' Q L h₁ b ft s rs cols t t₁ u₀ z u e cls :=
  ⟨h.front, h.decided, h.behindB, h.heard, hm _ _ h.toBatch, h.batched, h.behindBatch,
    hm _ _ h.toCall, h.called,
    hm _ _ h.along, hm _ _ h.fromCall, h.said, fun name hn => by
      obtain ⟨run, n, v, cl, v', q₁, q₂, q₃, q₄, q₅⟩ := h.runs name hn
      exact ⟨run, n, v, cl, v', q₁, q₂, hm _ _ q₃, hm _ _ q₄, q₅⟩⟩

/-- A block that has no run has the runs' laws for nothing. -/
theorem runsOfBare {R : S → S → Prop} (b : Block S Cl) (h : b.claims = []) : b.RunsStep R :=
  fun c hc => by rw [h] at hc; exact nomatch hc

theorem afterOfBare {R : S → S → Prop} (b : Block S Cl) (h : b.after = []) : b.AfterStep R :=
  fun c hc => by rw [h] at hc; exact nomatch hc

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.preAnd
#print axioms VerifiableInference.Desc.Traced.mono
#print axioms VerifiableInference.Desc.stepsAndThen
#print axioms VerifiableInference.Desc.stepsLift
#print axioms VerifiableInference.Desc.runsLift
#print axioms VerifiableInference.Desc.stepsLiftPart
#print axioms VerifiableInference.Desc.runsLiftPart
#print axioms VerifiableInference.Desc.stepsInside
#print axioms VerifiableInference.Desc.afterLift
#print axioms VerifiableInference.Desc.afterLiftPart
