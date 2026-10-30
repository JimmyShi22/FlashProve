-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Psc/Run/PscWhole.lean: the parts of the block's listener, with fitting sizes, are a
successful run of the block's Psc.verify.

A lemma on the block alone (OnBytes/Iop/Psc.lean). No routine of OnBytes/Model/ and no state of its
sumcheck occurs in this file.

Main names:
  `claimAfter_append`: the running claim after one more round.
  `heardOf`: what the parts of a sumcheck with end values have heard, as the block's record.
  `verify_of`: the round PSC epsilon with one scalar, the rounds of the variables, the round in Y,
    the end values and their closing make Psc.verify succeed, and Psc.run gives what it returns.
    This holds for any mask form, any summand and any list of slots of fitting sizes.
Limits: no failure of Psc.verify depends on a value, so verify_of says nothing on which claim is
shown. It serves only where no further scalar stands before mu in the first message. Nothing is said
on hiding.
-/
import OnBytes.Tie.Pv.Psc.Run.PscRun

namespace OnBytes.Model.Road
open OnBytes.Psc (Weight hearOne hearMany hear claimAfter polyAt)

theorem claimAfter_append : ∀ (ws : List Weight) (rs : List (List E × E)) (w : Weight)
    (x : List E × E) (R : E), rs.length = ws.length →
    claimAfter (ws ++ [w]) (rs ++ [x]) R = polyAt (w.complete x.1 (claimAfter ws rs R)) x.2
  | [], [], _, (_, _), _, _ => rfl
  | [], _ :: _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, h => by simp at h
  | v :: ws, (q, g) :: rs, w, x, R, h => by
    simp only [List.cons_append, claimAfter]
    exact claimAfter_append ws rs w x _ (by simpa using h)

/-- What the parts of a sumcheck with end values have heard, as the block's record. -/
def heardOf (mu eps : E) (rs : List (List E × E)) (sentY : List E) (beta : E) (v : List E) :
    OnBytes.Psc.Heard := ⟨mu, eps, rs ++ [(sentY, beta)], v⟩

/-- The parts of the block's listener, with fitting sizes, are a run of Psc.verify. -/
theorem verify_of (ws : List Weight) (m : MaskForm) (τ : E) (S : OnBytes.Psc.Summand)
    (fresh : List Slot) (mu eps beta : E) (rs : List (List E × E)) (sentY v : List E)
    (c c1 c2 c3 c4 c' : Ctx)
    (h1 : (hearOne "PSC epsilon" .join 1 0).Yields c ([mu], eps) c1)
    (h2 : (hearMany (ws.map fun w => w.d - 1)).Yields c1 rs c2)
    (h3 : (hearOne "PSC Y" .elems S.degree 1).Yields c2 (sentY, beta) c3)
    (h4 : (Blk.recvEs S.shown).Yields c3 v c4) (h5 : (Blk.closeEmpty "PSC values").Yields c4 () c')
    (len : rs.length = ws.length) (sizes : ∀ x ∈ ws.zip rs, x.2.1.length + 1 = x.1.d)
    (fits : ∀ w ∈ ws, w.fits = true) (hY : sentY.length = S.degree) (hv : v.length = S.shown)
    (d1 : 1 ≤ S.degree) (n1 : 1 ≤ S.shown)
    (hf : fresh.length = OnBytes.Psc.masksOf ⟨ws, m, τ⟩ S)
    (ha : (S.coeffs ((rs.map (·.2)) ++ [beta] |>.take ws.length) v).length = 1 + S.kept) :
    ∃ o, (OnBytes.Psc.verify ⟨ws, m, τ⟩ S fresh).Yields c o c' ∧
      OnBytes.Psc.run ⟨ws, m, τ⟩ S fresh (heardOf mu eps rs sentY beta v) = some o := by
  have hs0 : (S.shown == 0) = false := by
    cases hh : S.shown with
    | zero => omega
    | succ k => rfl
  have hd0 : (S.degree == 0) = false := by
    cases hh : S.degree with
    | zero => omega
    | succ k => rfl
  have hvars : OnBytes.Psc.varsOf ⟨ws, m, τ⟩ S = ws ++ [Weight.atZero (S.degree + 1)] := by
    simp [OnBytes.Psc.varsOf, hs0]
  have hsize : OnBytes.Psc.sizeOf ⟨ws, m, τ⟩ S =
      { degree := ws.map (·.d), withY := true, degreeY := S.degree, values := S.shown } := by
    simp only [OnBytes.Psc.sizeOf]
    congr 1
    exact decide_eq_true (by omega)
  have hh : (hear (OnBytes.Psc.sizeOf ⟨ws, m, τ⟩ S)).Yields c (heardOf mu eps rs sentY beta v) c' :=
      by
    rw [hsize]
    refine hear_of (ws.map (·.d)) S.degree S.shown mu eps rs (sentY,
        beta) v c c1 c2 c3 c4 c' h1 ?_ h3 h4 h5
    rw [List.map_map]
    exact h2
  have htest : (OnBytes.Psc.formOK ⟨ws, m, τ⟩ S && fresh.length == OnBytes.Psc.masksOf ⟨ws, m,
      τ⟩ S &&
      (heardOf mu eps rs sentY beta v).rounds.length == (OnBytes.Psc.varsOf ⟨ws, m, τ⟩ S).length &&
      (heardOf mu eps rs sentY beta v).values.length == S.shown &&
      (S.coeffs (((heardOf mu eps rs sentY beta v).rounds.map (·.2)).take ws.length)
        (heardOf mu eps rs sentY beta v).values).length == 1 + S.kept &&
      (((OnBytes.Psc.varsOf ⟨ws, m, τ⟩ S).zip (heardOf mu eps rs sentY beta v).rounds).all
        fun p => p.2.1.length + 1 == p.1.d)) = true := by
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, heardOf, hvars]
    refine ⟨⟨⟨⟨⟨?_, hf⟩, by simp [len]⟩, hv⟩, by simpa using ha⟩, ?_⟩
    · simp only [OnBytes.Psc.formOK, hs0, hd0, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
        decide_eq_true_eq]
      exact ⟨⟨rfl, Or.inl (by omega)⟩, fits⟩
    · intro x hx
      rw [List.zip_append len.symm] at hx
      simp only [List.mem_append, List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact sizes x hx
      · show sentY.length + 1 = S.degree + 1
        rw [hY]
  have hrun : ∃ o, OnBytes.Psc.run ⟨ws, m, τ⟩ S fresh (heardOf mu eps rs sentY beta v) = some o :=
      by
    unfold OnBytes.Psc.run
    simp only []
    rw [if_pos htest]
    exact ⟨_, rfl⟩
  obtain ⟨o, ho⟩ := hrun
  refine ⟨o, ?_, ho⟩
  unfold OnBytes.Psc.verify
  exact (Blk.yields_bind _ _ _ _ _).2 ⟨_, c', hh, (Blk.yields_get _ _ _ _).2 ⟨ho, rfl⟩⟩

end OnBytes.Model.Road
