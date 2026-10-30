-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/Sources.lean: the block on the taken trees' sources says yes just where the
declared sources are those of the book's trees. Definitions of Prop and theorems.

Main names:
  `Tied own s`: every member of the own group, and the mask, has a tree in the book; each is
    declared by `own`'s rounds as taken from the chain that sent it, under its number; no other tree
    is declared as taken.
  `ExactTied`: a block says yes just where Tied holds, and hands the record on.
  `takenSources_exact`: both ways.
  `idle_not_exact`, `deaf_not_exact`: neither the block that says yes to all nor the one that says
    no to all meets it.

Limits. That the compiler holds an opening to the root that its source names is another file's.
Nothing on soundness or on hiding.
-/
import Johnson.Desc.Third.Law.Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes

namespace VerifiableInference.Desc.Third.Law

/-- **The taken trees' sources are tied**, at the record s, to the declared rounds of the block own.
-/
def Tied {Cl : Type} (own : Block S₃ Cl) (s : S₃) : Prop :=
  ∃ ts, takenOf s = some ts ∧
    (ts.all fun x => opensTaken own.rounds x.1 x.2) = true ∧
    ((own.rounds.flatMap (·.opens)).all fun o =>
      match o.2 with
      | .own _ => true
      | .taken c n => ts.contains (c, n)) = true

/-- **The law, as a property of a block.** -/
def ExactTied {Cl : Type} (own b : Block S₃ Cl) : Prop :=
  ∀ s rs gs s', b.decide s rs gs = .ok s' ↔ s' = s ∧ Tied own s

/-- **The block says yes just where the sources are tied, and hands the record on as it is.** -/
theorem takenSources_exact {Cl : Type} (own : Block S₃ Cl) : ExactTied own (takenSources own) := by
  intro s rs gs s'
  constructor
  · intro h
    simp only [takenSources, roundlessBlock] at h
    obtain ⟨ts, h1, h⟩ := ok_of_bind h
    obtain ⟨_, h2, h⟩ := ok_of_bind h
    obtain ⟨_, h3, h⟩ := ok_of_bind h
    exact ⟨(Except.ok.inj h).symm, ts, some_of_named h1, true_of_need h2, true_of_need h3⟩
  · intro h
    obtain ⟨e, ts, h1, h2, h3⟩ := h
    rw [e]
    simp only [takenSources, roundlessBlock, h1, named, need, bind, Except.bind, h2, ↓reduceIte, pure,
      Except.pure]
    -- h3's "match" and the block's are two auxiliary definitions of one text: equal by unfolding,
    -- not to the letter
    first
      | (erw [if_pos h3]; all_goals (try rfl); done)
      | (split <;> first | rfl | (rename_i hn; exact absurd h3 hn))

/-! ## The statement at the two silly members -/

/-- It says yes to all and hands the record on. -/
def idleB : Block S₃ Unit := roundlessBlock "idle" 3 none 0 fun s => .ok s
/-- It says no to all. -/
def deafB : Block S₃ Unit := roundlessBlock "deaf" 3 none 0 fun _ => .error "no"

/-- No group at all. -/
def bareRecord : S₃ :=
  { st := {}, book := {}, roots := 0
    loc := { w := 0, own := 0, mask := none, border := none, omega := 0, firstTree := 0 } }

/-- The own group is there and has no member; no mask. -/
def loneGroup : S₃ := { bareRecord with st := { groups := #[{ code := 0 }] } }

theorem bare_not_tied {Cl : Type} (own : Block S₃ Cl) : ¬ Tied own bareRecord := by
  intro h
  obtain ⟨ts, h1, _⟩ := h
  have t : takenOf bareRecord = none := by
    first | rfl | simp [takenOf, bareRecord]
  rw [t] at h1
  cases h1

theorem lone_tied : Tied idleB loneGroup := by
  refine ⟨[], ?_, rfl, rfl⟩
  first | rfl | simp [takenOf, loneGroup, bareRecord]

theorem idle_not_exact (own : Block S₃ Unit) : ¬ ExactTied own idleB :=
  fun h => bare_not_tied own ((h bareRecord [] [] bareRecord).1 rfl).2

theorem deaf_not_exact : ¬ ExactTied idleB deafB := by
  intro h
  have t := (h loneGroup [] [] loneGroup).2 ⟨rfl, lone_tied⟩
  cases t

end VerifiableInference.Desc.Third.Law

#print axioms VerifiableInference.Desc.Third.Law.takenSources_exact
#print axioms VerifiableInference.Desc.Third.Law.idle_not_exact
#print axioms VerifiableInference.Desc.Third.Law.deaf_not_exact
