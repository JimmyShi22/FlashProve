-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/BlockKeeps.lean: the format's ways of making a block out of blocks keep what the parts
keep: beside Johnson/Desc/FoldKeeps.lean. No kind is named. Theorems.

  andThen_decides, andThen_whole   two blocks as one.
  lift_decides         a block that is typed at a part of the record and lifted.
  liftPart_decides     the like for a part that is there only at times.
  inside_decides       a block whose own record is born and dies inside it.
  quiet_decides        a block without a round.
What is not claimed: as in Johnson/Desc/FoldKeeps.lean.

-/
import Johnson.Desc.FoldKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Keeps
open VerifiableInference.Desc

variable {S T Cl : Type}

/-- A map of Except that returns: the value beneath returns. -/
theorem emap_ok {α β : Type} {x : Except String α} {f : α → β} {b : β}
    (h : x.map f = .ok b) : ∃ a, x = .ok a ∧ f a = b := by
  cases x with
  | error e => cases h
  | ok a => cases h; exact ⟨a, rfl, rfl⟩

/-- Two blocks as one keep R where both do. -/
theorem andThen_decides (R : S → S → Prop) (ht : ∀ a b c, R a b → R b c → R a c) (n : String)
    (p q : Block S Cl) (hp : Decides R p) (hq : Decides R q) : Decides R (p.andThen n q) := by
  intro s rs gs s' h
  obtain ⟨a, h1, h2⟩ := ebind_ok (x := p.decide s (rs.take p.rounds.length) (gs.take p.openings)) h
  exact ht _ _ _ (hp _ _ _ _ h1) (hq _ _ _ _ h2)

/-- The like with the runs of claims and the runs behind the batching. -/
theorem andThen_whole (R : S → S → Prop) (ht : ∀ a b c, R a b → R b c → R a c) (n : String)
    (p q : Block S Cl) (hp : Whole R p) (hq : Whole R q) : Whole R (p.andThen n q) :=
  ⟨andThen_decides R ht n p q hp.1 hq.1,
    fun c hc => (List.mem_append.1 hc).elim (hp.2.1 c) (hq.2.1 c),
    fun c hc => (List.mem_append.1 hc).elim (hp.2.2 c) (hq.2.2 c)⟩

/-- A lifted block keeps R' where the block keeps R and set carries R over. -/
theorem lift_decides (R : S → S → Prop) (R' : T → T → Prop) (get : T → S) (set : T → S → T)
    (hs : ∀ t x, R (get t) x → R' t (set t x)) (b : Block S Cl) (hb : Decides R b) :
    Decides R' (b.lift get set) := by
  intro t rs gs t' h
  obtain ⟨x, h1, h2⟩ := emap_ok (x := b.decide (get t) rs gs) h
  subst h2
  exact hs t x (hb _ _ _ _ h1)

/-- The like for a part that is there only at times. -/
theorem liftPart_decides (R : S → S → Prop) (R' : T → T → Prop) (get? : T → Option S)
    (set : T → S → T) (hs : ∀ t p x, get? t = some p → R p x → R' t (set t x)) (b : Block S Cl)
    (hb : Decides R b) : Decides R' (b.liftPart get? set) := by
  intro t rs gs t' h
  obtain ⟨p, h0, h1⟩ := ebind_ok (x := named "the part is not there" (get? t)) h
  obtain ⟨x, h2, h3⟩ := emap_ok h1
  subst h3
  exact hs t p x (named_ok h0) (hb _ _ _ _ h2)

/-- A block whose own record is born and dies inside it. -/
theorem inside_decides (R : S → S → Prop) (Q : T → T → Prop) (enter : S → Except String T)
    (b : Block T Cl) (leave : S → T → Except String S)
    (hs : ∀ s t t' s', enter s = .ok t → Q t t' → leave s t' = .ok s' → R s s')
    (hb : Decides Q b) : Decides R (b.inside enter leave) := by
  intro s rs gs s' h
  obtain ⟨t, h0, h1⟩ := ebind_ok (x := enter s) h
  obtain ⟨t', h2, h3⟩ := ebind_ok h1
  exact hs s t t' s' h0 (hb _ _ _ _ h2) h3

/-- A block without a round keeps R where its change of the record does. -/
theorem quiet_decides (R : S → S → Prop) (n : String) (chain : Nat) (link : Option Nat)
    (piece : Nat) (f : S → Except String S) (hf : Fn R f) :
    Decides R (roundlessBlock (Cl := Cl) n chain link piece f) :=
  fun s _ _ s' h => hf s s' h

end VerifiableInference.Desc.Keeps
