-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/Dry/Tied.lean: TWO ORACLE ALGORITHMS RUN SIDE BY SIDE UNDER ONE LIST OF RECORDED ANSWERS AND ONE
TABLE. General in the family of oracles.

General definitions and lemmas. This file states no goal of the release.

InStep (Rom/Handle/Defs.lean) ties a dry run to a run with a table: the two get different answers at
the queries that are not deferred, so it lets each side move alone there. Here both runs have a
table, THE SAME one, and replay THE SAME recorded answers. Then more can be said, and more is
wanted: that the table is the same afterwards, and how the two logs are related.

  TiedL mk R l l' c c'   c, with the log l so far, and c', with the log l' so far, go side by side:
      both stop, with outputs and logs related by R; or both ask THE SAME plain query, and go on
      side by side at every answer; or both ask a deferred query of one oracle, at points that may
      differ, and go on side by side at every answer, each with its own query and that answer
      appended to its log; or both draw from the same range, and go on side by side at every draw.
  TiedL.bind, TiedL.mono   along "c, then g"; a weaker relation.
  TiedL.refl             an algorithm beside itself, for a relation on logs that is kept when one
      and the same entry is appended to both.
  TiedL.map_replay       THE LAW. Replays of one list of recorded answers from one state of the rule
      for the plain queries, with the logs l and l': whatever function of (output, last state) takes
      the same value at all outputs and logs that R relates has THE SAME LAW in both runs. The state
      of the rule for the plain queries, what is left of the recorded answers and the flag "miss"
      are the same in both, step by step.

Limits. Nothing here says when two algorithms are tied.
Terms: lean/GLOSSARY.md.

-/
import Rom.Handle.Laws

set_option autoImplicit false

noncomputable section

namespace Rom
open Prob
variable {S : OSpec} {σ α β γ δ : Type}

/-- **Two algorithms side by side**, with their logs so far. -/
inductive TiedL (mk : Mark S) (R : α → Trace S → β → Trace S → Prop) :
    Trace S → Trace S → OComp S α → OComp S β → Prop
  | done {l l' : Trace S} {a : α} {b : β} : R a l b l' → TiedL mk R l l' (.pure a) (.pure b)
  | plain {l l' : Trace S} {o : S.ι} {q : S.Dom o} {k : S.Rng o → OComp S α}
      {k' : S.Rng o → OComp S β} :
      mk o q = false → (∀ r, TiedL mk R l l' (k r) (k' r)) →
      TiedL mk R l l' (.query o q k) (.query o q k')
  | both {l l' : Trace S} {o : S.ι} {q q' : S.Dom o} {k : S.Rng o → OComp S α}
      {k' : S.Rng o → OComp S β} :
      mk o q = true → mk o q' = true →
      (∀ r, TiedL mk R (l ++ [⟨o, q, r⟩]) (l' ++ [⟨o, q', r⟩]) (k r) (k' r)) →
      TiedL mk R l l' (.query o q k) (.query o q' k')
  | draw {l l' : Trace S} {n : ℕ} {k : Fin (n + 1) → OComp S α} {k' : Fin (n + 1) → OComp S β} :
      (∀ r, TiedL mk R l l' (k r) (k' r)) → TiedL mk R l l' (.sample n k) (.sample n k')

namespace TiedL
variable {mk : Mark S}

/-- A weaker relation. -/
theorem mono {R R' : α → Trace S → β → Trace S → Prop}
    (hR : ∀ a l b l', R a l b l' → R' a l b l') {l l' : Trace S} {c : OComp S α} {c' : OComp S β}
    (hc : TiedL mk R l l' c c') : TiedL mk R' l l' c c' := by
  induction hc with
  | done h => exact .done (hR _ _ _ _ h)
  | plain hm _ ih => exact .plain hm ih
  | both hm hm' _ ih => exact .both hm hm' ih
  | draw _ ih => exact .draw ih

/-- Two algorithms made of parts that go side by side go side by side. -/
theorem bind {R₁ : α → Trace S → β → Trace S → Prop} {R₂ : γ → Trace S → δ → Trace S → Prop}
    {l l' : Trace S} {c : OComp S α} {c' : OComp S β} {g : α → OComp S γ} {g' : β → OComp S δ}
    (hc : TiedL mk R₁ l l' c c')
    (hg : ∀ a l₁ b l₁', R₁ a l₁ b l₁' → TiedL mk R₂ l₁ l₁' (g a) (g' b)) :
    TiedL mk R₂ l l' (c.bind g) (c'.bind g') := by
  induction hc with
  | done h => exact hg _ _ _ _ h
  | plain hm _ ih => exact .plain hm ih
  | both hm hm' _ ih => exact .both hm hm' ih
  | draw _ ih => exact .draw ih

/-- An algorithm beside itself: the same output; a relation on logs that is kept when one entry is
appended to both is kept. -/
theorem refl {Lg : Trace S → Trace S → Prop}
    (hLg : ∀ l l' e, Lg l l' → Lg (l ++ [e]) (l' ++ [e])) (c : OComp S α) :
    ∀ l l', Lg l l' → TiedL mk (fun a l₁ b l₁' => a = b ∧ Lg l₁ l₁') l l' c c := by
  induction c with
  | pure a => exact fun l l' h => .done ⟨rfl, h⟩
  | query o q k ih =>
    intro l l' h
    cases hm : mk o q with
    | false => exact .plain hm fun r => ih r l l' h
    | true => exact .both hm hm fun r => ih r _ _ (hLg l l' _ h)
  | sample n k ih => exact fun l l' h => .draw fun r => ih r l l' h

/-- **THE LAW: replays of one list of recorded answers, from one state of the rule for the plain
queries.** -/
theorem map_replay (h : Handler S σ) {R : α → Trace S → β → Trace S → Prop}
    {H : α × RSt S σ → γ} {H' : β × RSt S σ → γ}
    (hH : ∀ a l b l', R a l b l' → ∀ (s : σ) (Rc : Record S) (ms : Bool),
      H (a, ⟨s, l, Rc, ms⟩) = H' (b, ⟨s, l', Rc, ms⟩))
    {l l' : Trace S} {c : OComp S α} {c' : OComp S β} (hc : TiedL mk R l l' c c') :
    ∀ (s : σ) (Rc : Record S) (ms : Bool),
      (c.interp (Handler.replay mk h) ⟨s, l, Rc, ms⟩).map H =
        (c'.interp (Handler.replay mk h) ⟨s, l', Rc, ms⟩).map H' := by
  induction hc with
  | done hab =>
    intro s Rc ms
    simp only [OComp.interp_pure, PMF.pure_map]
    rw [hH _ _ _ _ hab]
  | plain hm _ ih =>
    intro s Rc ms
    simp only [OComp.interp_query, Handler.replay_of_not h hm, PMF.bind_map, PMF.map_bind,
      Function.comp_def, ih]
  | both hm hm' _ ih =>
    intro s Rc ms
    simp only [OComp.interp_query, Handler.replay_of_mark h hm, Handler.replay_of_mark h hm',
      PMF.bind_map, PMF.map_bind, Function.comp_def, ih]
  | draw _ ih =>
    intro s Rc ms
    simp only [OComp.interp_sample, PMF.map_bind, ih]

end TiedL
end Rom

#print axioms Rom.TiedL.bind
#print axioms Rom.TiedL.refl
#print axioms Rom.TiedL.map_replay
