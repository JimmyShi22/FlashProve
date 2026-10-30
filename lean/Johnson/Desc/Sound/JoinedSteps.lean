-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/JoinedSteps.lean: SEVERAL STEPS UNDER `Block.andThen` IN ONE BLOCK: if one step
of the row calls a gatherer and the others step R, THE ONE BLOCK CALLS THE GATHERER, AND WHAT THE
STEP SAID OF ITS CALL IS KEPT. Theorems with their proofs, each by unfolding.

Why. In the seat that rides, the steps of one link's place of the batching (the draw; the steps of
adding; the tests behind) are joined by `Block.andThen`, by a fold from the left, into ONE block at
that place: they are no members of the link's blocksInOrder list. (Held at
that seat's own text.) `callsWithRight` | `callsWithLeft` (Johnson/Desc/Sound/FoldStepsWith.lean)
carry `CallsWith` through `andThen` and FORGET Q: so the claims were loose again.

  `KeptQ Q`: of the record of the call, the claims and what the call left: "there are a record in
    front, rounds and a record behind with Q". `callsKeptRight`, `callsKeptLeft`, `callsKeptOn`:
    through `andThen`, Q kept.
  `stepsOfCalls`: a block that calls a gatherer steps R, where the gatherer steps R.
  `callsWithOfDecide`: another name, place or test on the plan written in.
  `andThenAll name b l`: b, then the blocks of l, joined from the left: the term of that seat's own
    joining.
  `stepsAndThenAll`: all step: the one block steps. **`callsAndThenAll`**: the row is b :: l₁ ++ B
    :: l₂ (or B stands first: `callsAndThenAllHead`); B calls f with Q; all others step R: the one
    block calls f with `KeptQ Q`.

Limits. Tools: no block of the protocol is named. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.FoldStepsWith

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S Cl Cl' : Type}

/-- Q, kept of the record of the call, the claims and what the call left. -/
def KeptQ (Q : S → List Fmt.RoundView → S → List Cl' → S → S → Prop) :
    S → List Fmt.RoundView → S → List Cl' → S → S → Prop :=
  fun _ _ t cls e _ => ∃ m rs' m', Q m rs' t cls e m'

theorem callsKeptRight {R : S → S → Prop} {Q : S → List Fmt.RoundView → S → List Cl' → S → S → Prop}
    (hR : Pre R) (name : String) (p q : Block S Cl) (f : S → Except String (List Cl' × S))
    (hp : p.Steps R) (hq : CallsWith R Q q f) : CallsWith R (KeptQ Q) (p.andThen name q) f := by
  intro s rs gs s' H
  obtain ⟨m, hm, H'⟩ := bindOk
    (x := p.decide s (rs.take p.rounds.length) (gs.take p.openings)) H
  obtain ⟨t, cls, e, h₁, h₂, h₃, h₄⟩ := hq _ _ _ _ H'
  exact ⟨t, cls, e, hR.trans _ _ _ (hp _ _ _ _ hm) h₁, h₂, h₃, _, _, _, h₄⟩

theorem callsKeptLeft {R : S → S → Prop} {Q : S → List Fmt.RoundView → S → List Cl' → S → S → Prop}
    (hR : Pre R) (name : String) (p q : Block S Cl) (f : S → Except String (List Cl' × S))
    (hp : CallsWith R Q p f) (hq : q.Steps R) : CallsWith R (KeptQ Q) (p.andThen name q) f := by
  intro s rs gs s' H
  obtain ⟨m, hm, H'⟩ := bindOk
    (x := p.decide s (rs.take p.rounds.length) (gs.take p.openings)) H
  obtain ⟨t, cls, e, h₁, h₂, h₃, h₄⟩ := hp _ _ _ _ hm
  exact ⟨t, cls, e, h₁, h₂, hR.trans _ _ _ h₃ (hq _ _ _ _ H'), _, _, _, h₄⟩

/-- On, where Q is kept already. -/
theorem callsKeptOn {R : S → S → Prop} {Q : S → List Fmt.RoundView → S → List Cl' → S → S → Prop}
    (hR : Pre R) (name : String) (p q : Block S Cl) (f : S → Except String (List Cl' × S))
    (hp : CallsWith R (KeptQ Q) p f) (hq : q.Steps R) :
    CallsWith R (KeptQ Q) (p.andThen name q) f := by
  intro s rs gs s' H
  obtain ⟨m, hm, H'⟩ := bindOk
    (x := p.decide s (rs.take p.rounds.length) (gs.take p.openings)) H
  obtain ⟨t, cls, e, h₁, h₂, h₃, h₄⟩ := hp _ _ _ _ hm
  exact ⟨t, cls, e, h₁, h₂, hR.trans _ _ _ h₃ (hq _ _ _ _ H'), h₄⟩

/-- A block that calls a gatherer steps R, where the gatherer steps R. -/
theorem stepsOfCalls {R : S → S → Prop} {Q : S → List Fmt.RoundView → S → List Cl' → S → S → Prop}
    (hR : Pre R) (B : Block S Cl) (f : S → Except String (List Cl' × S))
    (hB : CallsWith R Q B f) (hf : ∀ t cls e, f t = .ok (cls, e) → R t e) : B.Steps R := by
  intro s rs gs s' H
  obtain ⟨t, cls, e, h₁, h₂, h₃, -⟩ := hB _ _ _ _ H
  exact hR.trans _ _ _ h₁ (hR.trans _ _ _ (hf t cls e h₂) h₃)

theorem callsWithOfDecide {R : S → S → Prop}
    {Q : S → List Fmt.RoundView → S → List Cl' → S → S → Prop} (B B' : Block S Cl)
    (f : S → Except String (List Cl' × S)) (e : B'.decide = B.decide) (h : CallsWith R Q B f) :
    CallsWith R Q B' f :=
  fun s rs gs s' H => h s rs gs s' (e ▸ H)

/-- b, then the blocks of l, joined from the left. -/
def andThenAll (name : String) (b : Block S Cl) (l : List (Block S Cl)) : Block S Cl :=
  l.foldl (fun acc x => acc.andThen name x) b

theorem stepsAndThenAll {R : S → S → Prop} (hR : Pre R) (name : String) :
    ∀ (l : List (Block S Cl)) (b : Block S Cl), b.Steps R → (∀ x ∈ l, x.Steps R) →
      (andThenAll name b l).Steps R
  | [], _, hb, _ => hb
  | x :: l, b, hb, hl =>
    stepsAndThenAll hR name l (b.andThen name x)
      (stepsAndThen hR name b x hb (hl x List.mem_cons_self))
      fun y hy => hl y (List.mem_cons_of_mem _ hy)

theorem callsKeptAll {R : S → S → Prop} {Q : S → List Fmt.RoundView → S → List Cl' → S → S → Prop}
    (hR : Pre R) (name : String) (f : S → Except String (List Cl' × S)) :
    ∀ (l : List (Block S Cl)) (b : Block S Cl), CallsWith R (KeptQ Q) b f →
      (∀ x ∈ l, x.Steps R) → CallsWith R (KeptQ Q) (andThenAll name b l) f
  | [], _, hb, _ => hb
  | x :: l, b, hb, hl =>
    callsKeptAll hR name f l (b.andThen name x)
      (callsKeptOn hR name b x f hb (hl x List.mem_cons_self))
      fun y hy => hl y (List.mem_cons_of_mem _ hy)

/-- What a block says of its own call is kept of itself. -/
theorem callsKeptSelf {R : S → S → Prop} {Q : S → List Fmt.RoundView → S → List Cl' → S → S → Prop}
    (B : Block S Cl) (f : S → Except String (List Cl' × S)) (h : CallsWith R Q B f) :
    CallsWith R (KeptQ Q) B f := by
  intro s rs gs s' H
  obtain ⟨t, cls, e, h₁, h₂, h₃, h₄⟩ := h _ _ _ _ H
  exact ⟨t, cls, e, h₁, h₂, h₃, _, _, _, h₄⟩

/-- The step that gathers stands first. -/
theorem callsAndThenAllHead {R : S → S → Prop}
    {Q : S → List Fmt.RoundView → S → List Cl' → S → S → Prop} (hR : Pre R) (name : String)
    (f : S → Except String (List Cl' × S)) (B : Block S Cl) (l : List (Block S Cl))
    (hB : CallsWith R Q B f) (hl : ∀ x ∈ l, x.Steps R) :
    CallsWith R (KeptQ Q) (andThenAll name B l) f :=
  callsKeptAll hR name f l B (callsKeptSelf B f hB) hl

theorem andThenAllApp (name : String) (b : Block S Cl) (l₁ l₂ : List (Block S Cl)) :
    andThenAll name b (l₁ ++ l₂) = andThenAll name (andThenAll name b l₁) l₂ := by
  simp [andThenAll, List.foldl_append]

/-- **One step of the row gathers; the others step: the one block calls the gatherer, Q kept.** -/
theorem callsAndThenAll {R : S → S → Prop} {Q : S → List Fmt.RoundView → S → List Cl' → S → S → Prop}
    (hR : Pre R) (name : String) (f : S → Except String (List Cl' × S)) (b B : Block S Cl)
    (l₁ l₂ : List (Block S Cl)) (hb : b.Steps R) (h₁ : ∀ x ∈ l₁, x.Steps R)
    (hB : CallsWith R Q B f) (h₂ : ∀ x ∈ l₂, x.Steps R) :
    CallsWith R (KeptQ Q) (andThenAll name b (l₁ ++ B :: l₂)) f := by
  rw [andThenAllApp]
  exact callsKeptAll hR name f l₂ _
    (callsKeptRight hR name _ B f (stepsAndThenAll hR name l₁ b hb h₁) hB) h₂

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.callsKeptRight
#print axioms VerifiableInference.Desc.callsKeptLeft
#print axioms VerifiableInference.Desc.stepsOfCalls
#print axioms VerifiableInference.Desc.stepsAndThenAll
#print axioms VerifiableInference.Desc.callsAndThenAllHead
#print axioms VerifiableInference.Desc.callsAndThenAll
