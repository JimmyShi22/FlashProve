-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/PositionAtPlan.lean: code switching (the kind K2): HOW MANY GENERATORS' ROWS
A SWITCH LAYS, AS A TERM OFF THE REQUEST's SHAPE: K2C/PositionCount.lean's count with the target
read off the plan's groups. NO BLOCK IMPORTS THIS FILE. s, s': the verifier's state in front of
the block and behind it.
  front_target      the front that the switch is handed has the target of a group: at a link and
                    at the head's link the group number s.check.frame.link of the state's frame;
                    at the finish the group that the finish's own part of the state names
  frontAt_fresh     at a link the group that the front names is the one that the front itself has
                    pushed: it has no row
  finish_fresh      the like at the finish, at the state that the way in ("F.0.front") hands to
                    the switch
  target_of_plan    so, at a link or the head's link: where the frame's link number is m and its
                    groups are the shape's (reqGroups): x.T = ((reqGroups shape).getD m {}).target
  yes_position_plan AT A YES, where the front's target is the plan's group m's: the group's list of
  open rows behind is the list in front, then the carried claim, then the kept members' stored
  samples, then gens, with gens.length = t * (1 + (((reqGroups sh).getD m {}).target.kept.toList.map
  (·.shape.mainRows)).sum + 2), t := the number of the positions drawn. THE RIGHT SIDE IS, TO THE
  LETTER, «positionRows sh t m» of a file that is not in this library,
  which is not imported
  here.
LEFT, BY NAME: KeptPos at that target (each kept shape has a main row: a closed fact at a written
shape) · t = the declared round's number of positions (the step's test on the view) · the two
premises of target_of_plan (public; the walk's). No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.PositionCount
import Johnson.Top.H0.Tw.K2C.FinFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (sendByL8 firstFront)

theorem front_target {p : P2} {s : S} {x : _root_.Tw.K2.Front} (h : frontAt p s = some x) :
    (p.stands = .finish ∧ ∃ a G, s.here = .fin a ∧ a.G = some G ∧ x.T = G.target) ∨
      (p.stands ≠ .finish ∧
        ∃ G, s.check.frame.groups[s.check.frame.link]? = some G ∧ x.T = G.target) := by
  unfold frontAt at h
  cases hp : p.stands with
  | link =>
    rw [hp] at h
    simp only at h
    refine Or.inr ⟨(fun e => nomatch e), ?_⟩
    cases hf : firstFront s.st s.check.frame with
    | error e =>
      rw [hf] at h
      cases h
    | ok y =>
      rw [hf] at h
      obtain rfl : y = x := Option.some.inj h
      obtain ⟨L, G, S0, g, a⟩ := (_root_.Tw.K2.firstFront_iff _ _ _).1 hf
      exact ⟨G, a.group, by rw [a.out]⟩
  | head =>
    rw [hp] at h
    refine Or.inr ⟨(fun e => nomatch e), ?_⟩
    cases hh : s.here with
    | head a =>
      rw [hh] at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨G, hG, rfl⟩ := h
      exact ⟨G, hG, rfl⟩
    | between => rw [hh] at h; simp at h
    | lay _ => rw [hh] at h; simp at h
    | att _ => rw [hh] at h; simp at h
    | fin _ => rw [hh] at h; simp at h
    | mem _ => rw [hh] at h; simp at h
  | finish =>
    rw [hp] at h
    refine Or.inl ⟨rfl, ?_⟩
    cases hh : s.here with
    | fin a =>
      rw [hh] at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨G, hG, rfl⟩ := h
      exact ⟨a, G, rfl, hG, rfl⟩
    | between => rw [hh] at h; simp at h
    | lay _ => rw [hh] at h; simp at h
    | att _ => rw [hh] at h; simp at h
    | head _ => rw [hh] at h; simp at h
    | mem _ => rw [hh] at h; simp at h

/-- **At a link the front's group is fresh**: it has no row yet. -/
theorem frontAt_fresh {p : P2} {t : S} {fx : _root_.Tw.K2.Front} (hp : p.stands = .link)
    (h : frontAt p t = some fx) : ∃ G, fx.st.groups[fx.f.group]? = some G ∧ G.rows.size = 0 := by
  unfold frontAt at h
  rw [hp] at h
  simp only at h
  cases hf : firstFront t.st t.check.frame with
  | error e =>
    rw [hf] at h
    cases h
  | ok y =>
    rw [hf] at h
    obtain rfl : y = fx := Option.some.inj h
    obtain ⟨e1, e2⟩ := firstFront_st hf
    refine ⟨freshGroup t.check.frame.shape.code t.check.frame.shape.maskCode, ?_, rfl⟩
    rw [e1, e2]
    simp [withFresh]

/-- **At the finish**: at the state that the way in ("F.0.front") hands to the switch. -/
theorem finish_fresh {p : P2} {s t : S} {fx : _root_.Tw.K2.Front} (hp : p.stands = .finish)
    (he : finishFrontQ s = .ok t) (h : frontAt p t = some fx) :
    ∃ G, fx.st.groups[fx.f.group]? = some G ∧ G.rows.size = 0 := by
  obtain ⟨a, G₀, ha, _, _, _, _, _, _, _, _, hg⟩ := finishFrontQ_fr he
  have hst := finishFrontQ_st he
  unfold frontAt at h
  rw [hp, ha] at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨G, _, rfl⟩ := h
  refine ⟨freshGroup s.check.frame.shape.code s.check.frame.shape.maskCode, ?_, rfl⟩
  show t.st.groups[a.fr.group]? = _
  rw [hst, hg]
  simp [withFresh]

theorem target_of_plan {p : P2} {s : S} {x : _root_.Tw.K2.Front} (h : frontAt p s = some x)
    (hp : p.stands ≠ .finish) {m : Nat} (hm : s.check.frame.link = m)
    (hg : s.check.frame.groups = reqGroups s.check.frame.shape) :
    x.T = ((reqGroups s.check.frame.shape).getD m {}).target := by
  rcases front_target h with ⟨e, _⟩ | ⟨_, G, hG, e⟩
  · exact absurd e hp
  · rw [hm, hg] at hG
    rw [e, Array.getD_eq_getD_getElem?, hG]
    rfl

theorem yes_position_plan {p : P2} {s s' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : decideWith sendByL8 p s [r₁, r₂] gs = .ok s')
    (sh : Params.ReqShape) (m : Nat)
    (hT : ∀ x, frontAt p s = some x → x.T = ((reqGroups sh).getD m {}).target)
    (hK : KeptPos ((reqGroups sh).getD m {}).target) :
    ∃ (x : _root_.Tw.K2.Front) (G : Group) (carried : OnBytes.Row)
      (samples gens : List OnBytes.Row), frontAt p s = some x ∧
      (x.st.groups[x.f.group]?).map (·.rows) = some G.rows ∧
      (s'.st.groups[x.f.group]?).map (·.rows) =
        some (G.rows ++ (carried :: samples ++ gens).toArray) ∧
      gens.length = r₂.drawn.poss.length *
        (1 + (((reqGroups sh).getD m {}).target.kept.toList.map (·.shape.mainRows)).sum + 2) := by
  obtain ⟨x, y, S3, Y, rows, G, c, A⟩ := yes_whole p s r₁ r₂ gs s' h
  have e := hT x A.front
  obtain ⟨carried, samples, gens, k1, k2, k3⟩ := yes_position_rows A (by rw [e]; exact hK)
  refine ⟨x, G, carried, samples, gens, A.front, k2, k1, ?_⟩
  rw [k3, e]
  rfl

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.front_target
#print axioms VerifiableInference.Desc.First.K2.frontAt_fresh
#print axioms VerifiableInference.Desc.First.K2.finish_fresh
#print axioms VerifiableInference.Desc.First.K2.target_of_plan
#print axioms VerifiableInference.Desc.First.K2.yes_position_plan
