-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/KeyAndThen.lean: Block.andThen IS ASSOCIATIVE IN WHAT IT DECIDES: over Johnson/Desc/Block.lean alone. For the key file's row 1.16: the seat is joined leftwards (((q.andThen f).andThen g).andThen h), the kind K13's files' law of the
joined block is stated rightwards (q.andThen ((f.andThen g).andThen h)): they are not one term; they decide alike.
  openings_andThen      the groups of two blocks joined are the two blocks' groups
  andThen_assoc_decide  (p · q) · r and p · (q · r) decide alike, at all states, rounds and groups, whatever the names
  andThen_left_congr    a joined block's decision reads of its first part: its decision, the number of its rounds and of its groups
  joined4_decide        ((q · f) · g) · h decides as q · ((f · g) · h)
The helper is named Key.foldl_openings (in full: VerifiableInference.Desc.Key.foldl_openings) because Johnson/Top/H0/StepLaws/StepLaws.lean declares VerifiableInference.Desc.foldl_openings with the same statement.
Nothing on soundness.
-/
import Johnson.Desc.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S Cl : Type}

theorem Key.foldl_openings (l : List Fmt.DeclaredRound) (n : Nat) :
    l.foldl (fun n r => n + r.stored.length + r.opens.length) n = n + l.foldl (fun n r => n + r.stored.length + r.opens.length) 0 := by
  induction l generalizing n with
  | nil => simp
  | cons r l ih =>
    simp only [List.foldl_cons]
    rw [ih (n + r.stored.length + r.opens.length), ih (0 + r.stored.length + r.opens.length)]
    omega

theorem openings_andThen (nm : String) (p q : Block S Cl) : (p.andThen nm q).openings = p.openings + q.openings := by
  show (p.rounds ++ q.rounds).foldl _ 0 = _
  rw [List.foldl_append, Key.foldl_openings q.rounds]
  rfl

theorem rounds_andThen (nm : String) (p q : Block S Cl) : (p.andThen nm q).rounds = p.rounds ++ q.rounds := rfl

theorem decide_andThen (nm : String) (p q : Block S Cl) (s : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    (p.andThen nm q).decide s rs gs = (p.decide s (rs.take p.rounds.length) (gs.take p.openings)).bind fun s' =>
      q.decide s' (rs.drop p.rounds.length) (gs.drop p.openings) := rfl

theorem ebind_assoc {ε α β γ : Type} (x : Except ε α) (f : α → Except ε β) (g : β → Except ε γ) :
    (x.bind f).bind g = x.bind fun a => (f a).bind g := by
  cases x <;> rfl

/-- **Joined leftwards and rightwards, three blocks decide alike.** -/
theorem andThen_assoc_decide (n₁ n₂ n₃ n₄ : String) (p q r : Block S Cl) (s : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    ((p.andThen n₁ q).andThen n₂ r).decide s rs gs = (p.andThen n₃ (q.andThen n₄ r)).decide s rs gs := by
  rw [decide_andThen, decide_andThen, decide_andThen, ebind_assoc, openings_andThen, rounds_andThen, List.length_append]
  have t1 : (rs.take (p.rounds.length + q.rounds.length)).take p.rounds.length = rs.take p.rounds.length := by
    rw [List.take_take, Nat.min_eq_left (Nat.le_add_right _ _)]
  have t2 : (gs.take (p.openings + q.openings)).take p.openings = gs.take p.openings := by
    rw [List.take_take, Nat.min_eq_left (Nat.le_add_right _ _)]
  rw [t1, t2]
  congr 1
  funext s'
  rw [decide_andThen]
  have d1 : (rs.take (p.rounds.length + q.rounds.length)).drop p.rounds.length = (rs.drop p.rounds.length).take q.rounds.length := by
    rw [List.drop_take, Nat.add_sub_cancel_left]
  have d2 : (gs.take (p.openings + q.openings)).drop p.openings = (gs.drop p.openings).take q.openings := by
    rw [List.drop_take, Nat.add_sub_cancel_left]
  rw [d1, d2]
  congr 1
  funext s''
  rw [List.drop_drop, List.drop_drop]

/-- A joined block's decision reads of its first part its decision and two numbers. -/
theorem andThen_left_congr (n n' : String) (p p' r : Block S Cl) (hd : ∀ s rs gs, p.decide s rs gs = p'.decide s rs gs)
    (hr : p.rounds.length = p'.rounds.length) (ho : p.openings = p'.openings) (s : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    (p.andThen n r).decide s rs gs = (p'.andThen n' r).decide s rs gs := by
  rw [decide_andThen, decide_andThen, hr, ho, hd]

/-- **The seam.** -/
theorem joined4_decide (a b c a' b' c' : String) (q f g h : Block S Cl) (s : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    (((q.andThen a f).andThen b g).andThen c h).decide s rs gs = (q.andThen a' ((f.andThen b' g).andThen c' h)).decide s rs gs := by
  rw [andThen_left_congr c c ((q.andThen a f).andThen b g) (q.andThen a (f.andThen b' g)) h
    (fun s rs gs => andThen_assoc_decide a b a b' q f g s rs gs)
    (by simp only [rounds_andThen, List.length_append]; omega)
    (by simp only [openings_andThen]; omega)]
  exact andThen_assoc_decide a c a' c' q (f.andThen b' g) h s rs gs

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.andThen_assoc_decide
#print axioms VerifiableInference.Desc.joined4_decide
