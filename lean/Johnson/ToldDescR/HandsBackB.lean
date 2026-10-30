-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/HandsBackB.lean: no soundness is claimed.
A family of reached states that hands back the wrapped step. HandsBack (OwnSitsLast.lean) hands back an accepting step of the sub-protocol itself: the test «every word is below the prime», which «reached», as the files under Johnson/Top/H0/Walk/ say it (Reach, Reach.lean there), has in front of each sub-protocol (Sound.below), is lost there. The earning of a sample's test needs it (a factor whose words spell the prime is no unit).
  HandsBackB bs Rc      whatever is reached at border n + 1 comes, by an accepting step of `Sound.below b`, b the sub-protocol number n, from something reached at border n
  HandsBackB.plain      it hands back in the plain sense too
  handsBackB_below      Reach over the wrapped list is such a family: by its make
  below_step            what the wrapped step holds: the sub-protocol's own step, and viewWordsBelowPrime of the very rounds that its decision reads
No member. Nothing on soundness.
-/
import Johnson.ToldDescR.OwnSitsLast
import Johnson.Desc.Sound.PieceYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc
open VerifiableInference.Desc
open Johnson.Desc.First.Walk.Tied (Reach)

def HandsBackB {T Cl Pp : Type} (bs : List (Block T Cl)) (Rc : ℕ → Pp × T → Prop) : Prop :=
  ∀ (n : ℕ) (z : Pp) (s : T), Rc (n + 1) (z, s) → ∃ (s₀ : T) (b : Block T Cl) (ft : ℕ)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (m : ℕ), Rc n (z, s₀) ∧ bs[n]? = some b ∧
      (Sound.below b).step ft s₀ rs cols = .ok (s, m)

theorem HandsBackB.plain {T Cl Pp : Type} {bs : List (Block T Cl)} {Rc : ℕ → Pp × T → Prop}
    (h : HandsBackB bs Rc) : HandsBack bs Rc := by
  intro n z s r
  obtain ⟨s₀, b, ft, rs, cols, m, r0, hb, hy⟩ := h n z s r
  exact ⟨s₀, b, ft, rs, cols, m, r0, hb, step_of_below hy⟩

theorem handsBackB_below {T Cl Pp : Type} (ft : ℕ) (bs : List (Block T Cl)) (start : Pp → T) :
    HandsBackB bs (Reach ft (bs.map Sound.below) start) := by
  intro n z s h
  cases h with
  | succ h1 hb hy =>
    obtain ⟨R, c, -, y⟩ := hy
    rw [List.getElem?_map] at hb
    obtain ⟨b, hb', rfl⟩ := Option.map_eq_some_iff.1 hb
    exact ⟨_, b, ft, R, c, _, h1, hb', y⟩

/-- What the wrapped step holds. -/
theorem below_step {T Cl : Type} {ft : ℕ} {b : Block T Cl} {s s' : T} {R : List Fmt.RoundView}
    {c : List OpenedColumn} {k : ℕ} (h : (Sound.below b).step ft s R c = .ok (s', k)) :
    b.step ft s R c = .ok (s', k) ∧ ∃ cs' : List (ℕ × ℕ × List UInt64),
      viewWordsBelowPrime ⟨R.map noDigest, cs'⟩ = true := by
  refine ⟨step_of_below h, ?_⟩
  obtain ⟨-, -, -, h4⟩ := (Sound.step_ok_iff ft _ s s' R c k).1 h
  exact ⟨_, (Sound.below_yes b _ _ _ _ h4).1⟩

end ToldDesc

#print axioms ToldDesc.handsBackB_below
#print axioms ToldDesc.below_step
