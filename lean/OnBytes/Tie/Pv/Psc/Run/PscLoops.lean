-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Psc/Run/PscLoops.lean: one round as a step of length one, runs of rounds one after
another, and the rounds of one layer of a product tree.

These serve any caller's loop over roundIn (OnBytes/Model/Psc.lean).

Main names:
  `claimAfter_app`, `Stepped.trans`, `hearMany_append`: two runs of rounds, one after the other.
  `roundIn_stepped`: one round of any form is a Stepped of length one, heard by hearMany.
  `levelRounds_ok`: the rounds of levelRounds: one under the equality weight of a coordinate of rho
    for each variable of the order.
Limits: one direction only, from a success of the model's routine. Nothing is said on what the
challenges are used for afterwards. Nothing is said on hiding.
-/
import OnBytes.Tie.Pv.Psc.Run.PscTsc

namespace OnBytes.Model.Road
open OnBytes.Psc (Weight hearOne hearMany hear claimAfter polyAt hidingWalk)

theorem claimAfter_app : ∀ (ws ws' : List Weight) (rs rs' : List (List E × E)) (R : E),
    rs.length = ws.length →
    claimAfter (ws ++ ws') (rs ++ rs') R = claimAfter ws' rs' (claimAfter ws rs R)
  | [], _, [], _, _, _ => by simp [claimAfter]
  | [], _, _ :: _, _, _, h => by simp at h
  | _ :: _, _, [], _, _, h => by simp at h
  | v :: ws, ws', (q, g) :: rs, rs', R, h => by
    simp only [List.cons_append, claimAfter]
    exact claimAfter_app ws ws' rs rs' _ (by simpa using h)

theorem Stepped.trans {p p1 p2 : Psc} {ws ws' : List Weight} {rs rs' : List (List E × E)}
    (a : Stepped p p1 ws rs) (b : Stepped p1 p2 ws' rs') : Stepped p p2 (ws ++ ws') (rs ++ rs')
        where
  claim := by rw [b.claim, a.claim, claimAfter_app _ _ _ _ _ a.len]
  vars := by rw [b.vars, a.vars, List.append_assoc]
  r := by rw [b.r, a.r, List.map_append, List.append_assoc]
  len := by simp [a.len, b.len]
  sizes := by
    intro x hx
    rw [List.zip_append a.len.symm] at hx
    rcases List.mem_append.1 hx with hx | hx
    · exact a.sizes x hx
    · exact b.sizes x hx
  held := by
    intro w hw
    rcases List.mem_append.1 hw with hw | hw
    · exact a.held w hw
    · exact b.held w hw
  start := b.start.trans a.start
  target := b.target.trans a.target
  eps := b.eps.trans a.eps
  first := b.first.trans a.first
  ended := b.ended.trans a.ended
  rowMade := b.rowMade.trans a.rowMade
  started := b.started.trans a.started

theorem hearMany_append : ∀ (ns ns' : List Nat) (l l' : List (List E × E)) (c c1 c' : Ctx),
    (hearMany ns).Yields c l c1 → (hearMany ns').Yields c1 l' c' →
    (hearMany (ns ++ ns')).Yields c (l ++ l') c'
  | [], ns', l, l', c, c1, c', h1, h2 => by
    simp only [hearMany] at h1
    obtain ⟨rfl, rfl⟩ := (Blk.yields_pure _ _ _ _).1 h1
    exact h2
  | n :: ns, ns', l, l', c, c1, c', h1, h2 => by
    simp only [hearMany] at h1
    obtain ⟨a, ca, ha, k1⟩ := (Blk.yields_bind _ _ _ _ _).1 h1
    obtain ⟨t, cb, hb, k2⟩ := (Blk.yields_bind _ _ _ _ _).1 k1
    obtain ⟨e1, e2⟩ := (Blk.yields_pure _ _ _ _).1 k2
    rw [e1, List.cons_append, List.cons_append]
    rw [e2] at h2
    exact hearMany_cons n (ns ++ ns') a (t ++ l') c ca c' ha (hearMany_append ns ns' t l' ca cb c'
        hb h2)

/-- One round, for any caller's loop, whatever the form. -/
theorem roundIn_stepped (form : RoundForm) (p p' : Psc) (z : E) (degree : Nat) (F G : Fork)
    (c c' : Ctx) (r : E) (h : roundIn form p z degree F c = .ok (((r, p'), G), c')) :
    ∃ w sent, form.weight z degree = some w ∧ p.ended = false ∧
      (hearMany [w.d - 1]).Yields c [(sent, r)] c' ∧ Stepped p p' [w] [(sent, r)] ∧
      G = taken F (w.d - 1) := by
  obtain ⟨w, sent, b1, b2, y1, a1, a2, a3, a4, a5⟩ := roundIn_ok form p p' z degree F G c c' r h
  refine ⟨w, sent, b1, b2, hearMany_cons _ _ _ _ _ _ _ y1 (hearMany_nil _), ?_, a5⟩
  refine Stepped.cons p p' w sent r [] [] a1 a2 a3 ?_
  rw [a4]
  exact Stepped.nil _

/-- The rounds of one layer of a product tree: one round under the equality weight of a coordinate
of rho
for each variable of the order. -/
theorem levelRounds_ok (mu : Nat) (rho : Array E) : ∀ (order : List Nat) (r r' : Array E)
    (p p' : Psc) (F G : Fork) (c c' : Ctx),
    levelRounds mu rho order r p F c = .ok (((r', p'), G), c') →
    ∃ rs, (hearMany (order.map fun _ => 2)).Yields c rs c' ∧
      Stepped p p' (order.map fun v => Weight.equality (rho.getD (mu - 1 - v) zeroE) 3) rs ∧
      (∀ v ∈ order, v < mu ∧ mu - 1 - v < rho.size) ∧ G = taken F (2 * order.length)
  | [], r, r', p, p', F, G, c, c', h => by
    simp only [levelRounds] at h
    obtain ⟨e1, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 h
    obtain ⟨_, e4⟩ := Prod.mk.inj e1
    rw [e4, e2, e3]
    exact ⟨[], hearMany_nil _, Stepped.nil _, by simp, rfl⟩
  | v :: order, r, r', p, p', F, G, c, c', h => by
    simp only [levelRounds] at h
    obtain ⟨_, F0, c0, h0, k0⟩ := (bind_ok _ _ _ _ _).1 h
    obtain ⟨b0, e1, e2⟩ := (must_ok _ _ _ _ _ _).1 h0
    rw [e1, e2] at k0
    obtain ⟨⟨x, p1⟩, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 k0
    obtain ⟨w, sent, b1, _, y1, a1, a2, a3, a4, a5⟩ := roundIn_ok _ _ _ _ _ _ _ _ _ _ h1
    rw [eq2_weight] at b1
    have hw := Option.some.inj b1
    rw [← hw] at y1 a1 a2 a3 a4 a5
    obtain ⟨rs, y2, s2, o2, e3⟩ := levelRounds_ok mu rho order _ _ _ _ _ _ _ _ k1
    rw [a4] at s2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at b0
    refine ⟨(sent, x) :: rs, hearMany_cons _ _ _ _ _ _ _ y1 y2,
        Stepped.cons _ _ _ _ _ _ _ a1 a2 a3 s2,
      ?_, ?_⟩
    · intro u hu
      rcases List.mem_cons.1 hu with rfl | hu
      · exact b0
      · exact o2 u hu
    · rw [e3, a5]
      show taken (taken F 2) (2 * order.length) = taken F (2 * (order.length + 1))
      rw [taken_taken, show 2 + 2 * order.length = 2 * (order.length + 1) by omega]

#print axioms roundIn_stepped
#print axioms levelRounds_ok
#print axioms Stepped.trans
#print axioms hearMany_append

end OnBytes.Model.Road
