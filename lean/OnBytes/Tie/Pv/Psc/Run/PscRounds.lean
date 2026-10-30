-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Psc/Run/PscRounds.lean: the loops over roundIn of OnBytes/Model/Look.lean on a run:
roundsIn and stackRounds.

Main names:
  `roundsLoop_ok`, `roundsIn_ok`: rounds of one form in a row: what was heard (hearMany), how the
    record stepped (Stepped), the challenges in the rounds' order, the slots taken.
  `sum2_weight`: the weight of the form sum2 is Weight.plain 3.
  `stackRounds_ok`: the lam rounds of a batched sumcheck, under plain weights with three
    coefficients. The field rs holds the challenges reversed.
Limits: one direction only, from a success of the model's routine. Other loops over roundIn are not
treated here; roundIn_stepped, Stepped.trans and hearMany_append (PscLoops.lean in this folder)
serve them. No statement has a hypothesis on whether the channel is a view or the dry run. Nothing
is said on hiding.
-/
import OnBytes.Model.Look
import OnBytes.Model.HideLaws
import OnBytes.Tie.Pv.Psc.Run.PscLoops

namespace OnBytes.Model.Road
open OnBytes.Psc (Weight hearOne hearMany claimAfter polyAt)

theorem roundsLoop_ok (form : RoundForm) : ∀ (zs : List (E × Nat)) (a : Array E) (p : Psc)
    (x : Array E × Psc) (F G : Fork) (c c' : Ctx),
    (zs.foldlM (fun (s : Array E × Psc) z => do
        let (r, q) ← roundIn form s.2 z.1 z.2
        pure (s.1.push r, q)) (a, p) : SubM (Array E × Psc)) F c = .ok ((x, G), c') →
    ∃ (ws : List Weight) (rs : List (List E × E)),
      ws.map some = zs.map (fun z => form.weight z.1 z.2) ∧
      (hearMany (ws.map fun w => w.d - 1)).Yields c rs c' ∧ Stepped p x.2 ws rs ∧
      x.1.toList = a.toList ++ rs.map (·.2) ∧ G = taken F (ws.map fun w => w.d - 1).sum
  | [], a, p, x, F, G, c, c', h => by
    simp only [List.foldlM_nil] at h
    obtain ⟨e1, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 h
    rw [e1, e2, e3]
    exact ⟨[], [], rfl, hearMany_nil _, Stepped.nil _, by simp, rfl⟩
  | z :: zs, a, p, x, F, G, c, c', h => by
    simp only [List.foldlM_cons] at h
    obtain ⟨s1, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
    obtain ⟨⟨r, q⟩, F2, c2, h2, k2⟩ := (bind_ok _ _ _ _ _).1 h1
    obtain ⟨e1, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 k2
    obtain ⟨w, sent, b1, _, y1, s1', g1⟩ := roundIn_stepped form p q z.1 z.2 F F2 c c2 r h2
    rw [e1, e2, e3] at k1
    obtain ⟨ws, rs, m2, y2, s2, r2, g2⟩ := roundsLoop_ok form zs _ _ _ _ _ _ _ k1
    refine ⟨w :: ws, (sent, r) :: rs, ?_, ?_, s1'.trans s2, ?_, ?_⟩
    · simp only [List.map_cons, m2, b1]
    · exact hearMany_append [w.d - 1] _ _ _ _ _ _ y1 y2
    · rw [r2]; simp
    · rw [g2, g1, taken_taken]; simp only [List.map_cons, List.sum_cons]

/-- Rounds of one form in a row. -/
theorem roundsIn_ok (form : RoundForm) (p p' : Psc) (zs : List (E × Nat)) (r : Array E) (F G : Fork)
    (c c' : Ctx) (h : roundsIn form p zs F c = .ok (((r, p'), G), c')) :
    ∃ (ws : List Weight) (rs : List (List E × E)),
      ws.map some = zs.map (fun z => form.weight z.1 z.2) ∧
      (hearMany (ws.map fun w => w.d - 1)).Yields c rs c' ∧ Stepped p p' ws rs ∧
      r.toList = rs.map (·.2) ∧ G = taken F (ws.map fun w => w.d - 1).sum := by
  unfold roundsIn at h
  obtain ⟨ws, rs, a1, a2, a3, a4, a5⟩ := roundsLoop_ok form zs #[] p (r, p') F G c c' h
  exact ⟨ws, rs, a1, a2, a3, by simpa using a4, a5⟩

theorem sum2_weight : RoundForm.weight .sum2 zeroE 0 = some (Weight.plain 3) := by
  simp [RoundForm.weight, RoundForm.degreeOK, RoundForm.equality, roundValues]

/-- The lam rounds of a batched sumcheck: plain weights with three coefficients; rs is the
challenges reversed. -/
theorem stackRounds_ok (st st' : Stack) (F G : Fork) (c c' : Ctx)
    (h : stackRounds st F c = .ok ((st', G), c')) :
    ∃ rs : List (List E × E),
      (hearMany ((List.replicate st.lam (Weight.plain 3)).map fun w => w.d - 1)).Yields c rs c' ∧
      Stepped st.p st'.p (List.replicate st.lam (Weight.plain 3)) rs ∧
      st'.rs.toList = (rs.map (·.2)).reverse ∧ st'.lam = st.lam ∧ G = taken F (2 * st.lam) := by
  unfold stackRounds at h
  obtain ⟨⟨r, p⟩, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨e1, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 k1
  obtain ⟨ws, rs, a1, a2, a3, a4, a5⟩ := roundsIn_ok _ _ _ _ _ _ _ _ _ h1
  have hws : ws = List.replicate st.lam (Weight.plain 3) := by
    have : ws.map some = (List.replicate st.lam (Weight.plain 3)).map some := by
      rw [a1, List.map_replicate, List.map_replicate, sum2_weight]
    exact List.map_injective_iff.2 (fun _ _ k => Option.some.inj k) this
  rw [hws] at a2 a3 a5
  refine ⟨rs, by rw [e3]; exact a2, by rw [e1]; exact a3, ?_, by rw [e1], ?_⟩
  · rw [e1]; show r.reverse.toList = _; rw [Array.toList_reverse, a4]
  · rw [e2, a5, List.map_replicate, List.sum_replicate]
    show taken F (st.lam • 2) = _
    rw [smul_eq_mul, Nat.mul_comm]

#print axioms roundsIn_ok
#print axioms stackRounds_ok

end OnBytes.Model.Road
