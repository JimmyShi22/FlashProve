-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/FitsSizes.lean: THE TEST ON THE NAMED POINTS READS LENGTHS ALONE. Whether
the verifier's function for the named points returns (`pointsOf`,
Johnson/Desc/First/Att/Points.lean), how many plane claims and units it lays, and which plane claim
each unit names, hang on the key points through their lengths alone. So the honest side's test
`aloneOk` (Johnson/Desc/K5/Honest/Alone.lean) says the same at any two lists of challenges whose key
points have the same lengths. Statements with their proofs, and one definition of a proposition.

  `SameSizes`, `SameSizes.symm`   two lists of key points: the point of each number has the same
      length in both
  `inner_size`, `piecesOf_size`   a unit's inner point and its pieces, counted
  `foldlM_each`, `foldlM_counts`, `mem_zip_left`   on a fold that may refuse; on zipped lists
  `points_guards`   where the function returns, its tests on numbers have passed: the converse of
      `points_ret` (Johnson/Desc/First/Att/K05PointsRet.lean)
  `points_counts`   how many plane claims it lays and which of them each unit names: of the place's
      numbers and one length alone
  `points_sizes`   **the function at two lists of key points of the same lengths**
  `aloneOk_mono`, `aloneOk_congr`   **the test says the same**

Limits. Lengths and counts alone: nothing is said of a value. That two lists of key points have the
same lengths is a premise. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Law.Lengths
import Johnson.Desc.First.Att.K05PointsRet

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E zeroE)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo UnitG Heard Left Pts RemP ScoreP pointsOf piecesOf
  points_ret)

/-- The key point of each number has the same length in both lists. -/
def SameSizes (zk zk' : Array (Array E)) : Prop :=
  ∀ i, (zk.getD i #[]).size = (zk'.getD i #[]).size

theorem SameSizes.symm {zk zk' : Array (Array E)} (h : SameSizes zk zk') : SameSizes zk' zk :=
  fun i => (h i).symm

/-- A unit's inner point is as long at two key points of one length. -/
theorem inner_size (u : UnitG) {k k' : Array E} (h : k.size = k'.size) :
    (P.inner u k).size = (P.inner u k').size := by
  unfold P.inner
  rw [Array.size_extract, Array.size_extract, h]

/-- A unit has as many weighted pieces as pieces. -/
theorem piecesOf_size (u : UnitG) (k : Array E) : (piecesOf u k).size = u.pcs.length := by
  unfold piecesOf
  rw [List.size_toArray, List.length_mergeSort, List.length_map]

/-! ## 1 Tools -/

/-- Where a fold that may refuse returns, its step has returned at every member. -/
theorem foldlM_each {α β : Type} {step : β → α → Option β} : ∀ (xs : List α) (b r : β),
    xs.foldlM step b = some r → ∀ x ∈ xs, ∃ b1 r1, step b1 x = some r1
  | [], _, _, _, _, hx => by cases hx
  | y :: xs, b, r, h, x, hx => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨b1, h1, h2⟩ := h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨b, b1, h1⟩
    · exact foldlM_each xs b1 r h2 x hx

/-- A fold that lays one plane claim and one unit a step, the unit naming that claim: counted. -/
theorem foldlM_counts {X : Type}
    (step : Array RemP × Array ScoreP → X → Option (Array RemP × Array ScoreP))
    (hstep : ∀ acc x acc1, step acc x = some acc1 →
      ∃ rem k, acc1 = (acc.1.push rem, acc.2.push k) ∧ k.claim = acc.1.size) :
    ∀ (xs : List X) (acc acc' : Array RemP × Array ScoreP), xs.foldlM step acc = some acc' →
      acc'.1.size = acc.1.size + xs.length ∧
        acc'.2.toList.map (·.claim) =
          acc.2.toList.map (·.claim) ++ List.range' acc.1.size xs.length
  | [], acc, acc', h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨rfl, by simp⟩
  | x :: xs, acc, acc', h => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨acc1, h1, h2⟩ := h
    obtain ⟨rem, k, e, hc⟩ := hstep acc x acc1 h1
    obtain ⟨e1, e2⟩ := foldlM_counts step hstep xs acc1 acc' h2
    subst e
    simp only [Array.size_push, Array.toList_push, List.map_append, List.map_cons,
      List.map_nil] at e1 e2
    refine ⟨by rw [e1, List.length_cons]; omega, ?_⟩
    rw [e2, hc, List.length_cons, List.range'_succ, List.append_assoc]
    rfl

/-- Each member of a list stands in the list zipped with one that is no shorter. -/
theorem mem_zip_left {α β : Type} : ∀ (l : List α) (m : List β), l.length ≤ m.length →
    ∀ a ∈ l, ∃ b, (a, b) ∈ l.zip m
  | [], _, _, _, h => by cases h
  | _ :: _, [], h, _, _ => by cases h
  | x :: l, y :: m, h, a, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨y, List.mem_cons_self⟩
    · obtain ⟨b, hb⟩ := mem_zip_left l m (Nat.le_of_succ_le_succ h) a ha
      exact ⟨b, List.mem_cons_of_mem _ hb⟩

/-! ## 2 The function's tests, and its counts -/

/-- **Where the function returns, its tests on numbers have passed.** CONDITIONAL: the return. -/
theorem points_guards {g : Geo} {zk : Array (Array E)} {h : Heard} {L : Left} {p : Pts}
    (hp : pointsOf g zk h L = some p) :
    (g.units .kr [.rm, .rd]).length = h.remainders.size ∧ g.scores.length = h.scores.size ∧
      g.scores.length = L.scores.size ∧
      (∀ u ∈ g.scores, (P.inner u (zk.getD u.call #[])).size =
        (if u.below then g.lgk + (g.lnT - 1) + g.lnT else g.lgk + g.lnT) + 2 * g.lB) ∧
      ∃ uW uX uH, g.single .wl = some uW ∧ g.single .ix = some uX ∧ g.single .wh = some uH ∧
        (piecesOf uW (zk.getD uW.call #[])).size = g.NP ∧
        (piecesOf uX (zk.getD uX.call #[])).size = g.NP ∧
        (piecesOf uH (zk.getD uH.call #[])).size = g.NP ∧
        (P.inner uW (zk.getD uW.call #[])).size = 1 + g.lgk + g.lt + g.ldh ∧
        (P.inner uX (zk.getD uX.call #[])).size = g.lgk + g.lt ∧
        (P.inner uH (zk.getD uH.call #[])).size = g.lgk + g.lt + g.ldh := by
  unfold pointsOf at hp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, K5Law.guard_some, Option.pure_def,
    Option.some.injEq] at hp
  obtain ⟨_, g1, _, g2, a, hf, uW, hW, uX, hX, uH, hH, _, g3, _, g4, -⟩ := hp
  rw [← Array.foldlM_toList, Array.toList_zip, Array.toList_zip] at hf
  simp only [Bool.and_eq_true, beq_iff_eq, List.size_toArray] at g1 g2 g3 g4
  refine ⟨g1, g2.1, g2.2, fun u hu => ?_, uW, uX, uH, hW, hX, hH, g3.1.1, g3.1.2, g3.2, g4.1.1,
    g4.1.2, g4.2⟩
  have lh : h.scores.toList.length = h.scores.size := Array.length_toList
  have lL : L.scores.toList.length = L.scores.size := Array.length_toList
  obtain ⟨b1, hb1⟩ := mem_zip_left g.scores h.scores.toList (by omega) u hu
  obtain ⟨b2, hb2⟩ := mem_zip_left (g.scores.zip h.scores.toList) L.scores.toList
    (by rw [List.length_zip]; omega) _ hb1
  obtain ⟨c1, r1, h1⟩ := foldlM_each _ _ _ hf _ hb2
  simp only [Option.bind_eq_some_iff, K5Law.guard_some, Option.some.injEq, beq_iff_eq] at h1
  exact h1.choose_spec.1

/-- **How many plane claims the function lays, and which of them each unit names**: of the place's
numbers and of one length alone. CONDITIONAL: the return. -/
theorem points_counts {g : Geo} {zk : Array (Array E)} {h : Heard} {L : Left} {p : Pts}
    (hp : pointsOf g zk h L = some p) :
    p.planes.size = h.remainders.size + g.scores.length ∧
      p.scores.toList.map (·.claim) = List.range' h.remainders.size g.scores.length := by
  obtain ⟨n1, n2, n3, -⟩ := points_guards hp
  unfold pointsOf at hp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, K5Law.guard_some, Option.pure_def,
    Option.some.injEq] at hp
  obtain ⟨_, -, _, -, a, hf, uW, -, uX, -, uH, -, _, -, _, -, e⟩ := hp
  rw [← Array.foldlM_toList] at hf
  obtain ⟨e1, e2⟩ := foldlM_counts _ (fun acc x acc1 h1 => by
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h1
    obtain ⟨_, _, e1⟩ := h1
    exact ⟨_, _, e1.symm, rfl⟩) _ _ _ hf
  subst e
  have hx : ((g.scores.toArray.zip h.scores).zip L.scores).toList.length = g.scores.length := by
    simp only [Array.length_toList, Array.size_zip, List.size_toArray]
    omega
  rw [hx] at e1 e2
  simp only [Array.size_map, Array.size_zip, List.size_toArray, n1, Nat.min_self] at e1 e2
  exact ⟨e1, by simpa using e2⟩

/-! ## 3 Two lists of key points of the same lengths -/

/-- **The function at two lists of key points of the same lengths**, and at two values heard and two
lists of rows of the same three lengths: where it returns at one it returns at the other, with as
many plane claims, and with units that name the same plane claims. CONDITIONAL: the lengths are the
same; the function returns at (zk, h, L). -/
theorem points_sizes {g : Geo} {zk zk' : Array (Array E)} {h h' : Heard} {L L' : Left} {p : Pts}
    (hz : SameSizes zk zk') (nR : h.remainders.size = h'.remainders.size)
    (nS : h.scores.size = h'.scores.size) (nL : L.scores.size = L'.scores.size)
    (hp : pointsOf g zk h L = some p) :
    ∃ p', pointsOf g zk' h' L' = some p' ∧ p'.planes.size = p.planes.size ∧
      p'.scores.toList.map (·.claim) = p.scores.toList.map (·.claim) := by
  obtain ⟨n1, n2, n3, hu, uW, uX, uH, sW, sX, sH, pW, pX, pH, zW, zX, zH⟩ := points_guards hp
  obtain ⟨p', hp'⟩ := points_ret (zk := zk') (h := h') (L := L') (n1.trans nR) (n2.trans nS)
    (n3.trans nL)
    (fun u hm => (inner_size u (hz u.call)).symm.trans (hu u hm)) sW sX sH
    ((piecesOf_size _ _).trans ((piecesOf_size _ _).symm.trans pW))
    ((piecesOf_size _ _).trans ((piecesOf_size _ _).symm.trans pX))
    ((piecesOf_size _ _).trans ((piecesOf_size _ _).symm.trans pH))
    ((inner_size uW (hz uW.call)).symm.trans zW) ((inner_size uX (hz uX.call)).symm.trans zX)
    ((inner_size uH (hz uH.call)).symm.trans zH)
  obtain ⟨a1, a2⟩ := points_counts hp
  obtain ⟨b1, b2⟩ := points_counts hp'
  exact ⟨p', hp', by rw [a1, b1, nR], by rw [a2, b2, nR]⟩

/-- The test at challenges whose key points have the same lengths: one way. -/
theorem aloneOk_mono {P : Pub5} {c c' : Chal} (hz : SameSizes c.zk c'.zk)
    (h : aloneOk P c = true) : aloneOk P c' = true := by
  obtain ⟨p, hp, h1, h2, h3⟩ := aloneOk_spec h
  obtain ⟨p2, hp2, e1, e2⟩ := points_sizes (h' := heardAt P c' fun _ => none)
    (L' := blankLeft P.x.score.length) hz (by simp [heardAt]) (by simp [heardAt]) rfl
    (show pointsOf P.g c.zk (heardAt P c fun _ => none) (blankLeft P.x.score.length) = some p
      from hp)
  refine aloneOk_of (show ptsOf P c' = some p2 from hp2) (by rw [e1]; exact h1) ?_ ?_
  · have := congrArg List.length e2
    simp only [List.length_map, Array.length_toList] at this
    rw [this, h2]
  · intro k hk
    have hm : k.claim ∈ p.scores.toList.map (·.claim) := by
      rw [← e2]
      exact List.mem_map.2 ⟨k, Array.mem_toList_iff.2 hk, rfl⟩
    obtain ⟨k0, hk0, e⟩ := List.mem_map.1 hm
    rw [e1, ← e]
    exact h3 k0 (Array.mem_toList_iff.1 hk0)

/-- **THE TEST SAYS THE SAME AT CHALLENGES WHOSE KEY POINTS HAVE THE SAME LENGTHS.** CONDITIONAL: on
just that. The answer does not hang on the place's own challenges. -/
theorem aloneOk_congr {P : Pub5} {c c' : Chal} (hz : SameSizes c.zk c'.zk) :
    aloneOk P c = aloneOk P c' := by
  cases h : aloneOk P c with
  | true => exact (aloneOk_mono hz h).symm
  | false =>
    cases h' : aloneOk P c' with
    | false => rfl
    | true => rw [aloneOk_mono hz.symm h'] at h; cases h

end H2K5.Honest

#print axioms H2K5.Honest.SameSizes.symm
#print axioms H2K5.Honest.inner_size
#print axioms H2K5.Honest.piecesOf_size
#print axioms H2K5.Honest.foldlM_each
#print axioms H2K5.Honest.foldlM_counts
#print axioms H2K5.Honest.mem_zip_left
#print axioms H2K5.Honest.points_guards
#print axioms H2K5.Honest.points_counts
#print axioms H2K5.Honest.points_sizes
#print axioms H2K5.Honest.aloneOk_mono
#print axioms H2K5.Honest.aloneOk_congr
