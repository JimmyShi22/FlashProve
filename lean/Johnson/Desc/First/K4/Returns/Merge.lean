-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/Merge.lean: THE MERGE OF THE WEIGHT CLAIMS RETURNS (flatForkEnd,
OnBytes/K/Kc/QuietLink.lean), in the form of the other laws of this folder: room, "nothing below has
turned", the next slot by number. General laws: nothing is evaluated.

  wsForkRounds_returns   its plain rounds.
  shown_wsForkStart   its start form names the values' slots alone.
  slotsMerge      the slots that it takes.
  **forkEnd_returns**   room, a tape of the shape masked lk 1 1 1 behind the batching round, the
                  merge's three tests on the claims' number and sizes, and every value's slot has
                  been shown. It has no test on values. Behind it, of the slots that it takes, the
                  shown value's alone is filled: its sumcheck is left open.

Limits. Conditional laws. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.K4.Returns.Gated
import OnBytes.K.Kc.QuietLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt
open OnBytes OnBytes.K.Kc D6.Ret
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.PscRun (Sized Filled)

/-- The merge's plain rounds. -/
theorem wsForkRounds_returns : ∀ (n : Nat) (rs : List FlatRound) (rm : Array E) (p : Psc)
    (F : Fork) (m : Nat) (u : Tape), rs.length = n → (∀ x ∈ rs, IsVar x) → Mid p F (2 * n + m) →
    ∃ rm' q G, Fl.wsForkRounds n rm p F (rs ++ u) = some ((rm', q), G, u) ∧ Mid q G m ∧
      q.first = p.first ∧ G.next = F.next + 2 * n ∧ G.ns = F.ns ∧
      (∀ j, Filled G j ↔ Filled F j) ∧ rm'.size = rm.size + n
  | 0, rs, rm, p, F, m, u, hl, _, h => by
    obtain rfl := len_zero hl
    refine ⟨rm, p, F, rfl, by simpa using h, rfl, rfl, rfl, fun _ => Iff.rfl, rfl⟩
  | n + 1, [], _, _, _, _, _, hl, _, _ => by simp at hl
  | n + 1, x :: rs, rm, p, F, m, u, hl, hv, h => by
    obtain ⟨w, sent, c, rfl, hs⟩ := isVar_lit (hv x (List.mem_cons_self ..))
    obtain ⟨q0, b1, b2, b3⟩ := roundInG (n := 2 * n + m) .sum2 zeroE 0 rfl
      (by
        show Mid p F (2 + (2 * n + m))
        have e : 2 * (n + 1) + m = 2 + (2 * n + m) := by omega
        rw [← e]
        exact h) w sent c (rs ++ u) hs
    obtain ⟨rm', q, G, c1, c2, c3, c4, c5, c6, c7⟩ := wsForkRounds_returns n rs (rm.push c) q0 _ m u
      (by simpa using hl) (fun y hy => hv y (List.mem_cons_of_mem _ hy)) b2
    have c4' : G.next = F.next + 2 + 2 * n := c4
    refine ⟨rm', q, G, ?_, c2, c3.trans b3, by omega, c5, fun j => (c6 j).trans filled_next, ?_⟩
    · rw [List.cons_append]
      unfold Fl.wsForkRounds
      exact bindR b1 c1
    · rw [c7, Array.size_push]
      omega

/-- The merge's start form names the values' slots alone. -/
theorem shown_wsForkStart {F : Fork} (sv : Array Nat) (rho : Array E)
    (h : ∀ j ∈ sv.toList, j < F.next ∧ Filled F j) : Shown F (wsForkStart sv rho) := by
  unfold wsForkStart
  rw [← Array.foldl_toList]
  refine shown_foldl (fun y : Nat × E => Aff.slot y.1) (fun y => y.2) _ _
    (fun _ hj => by cases hj) fun y hy => ?_
  have hm : y.1 ∈ sv.toList := by
    rw [Array.toList_zip] at hy
    exact (List.of_mem_zip hy).1
  exact shown_slot (h _ hm).1 (h _ hm).2

/-- The slots that the merge takes. -/
def slotsMerge (lk : Nat) : Nat := 1 + (2 * lk + (1 + 1))

/-- **The merge of the weight claims returns.** x: the element that its batching round draws. -/
theorem forkEnd_returns (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat) {F : Fork} {k : Nat}
    (hR : Room F (slotsMerge lay.lk + k)) (x : E) {t : Tape} (hT : TapeOf (masked lay.lk 1 1 1) t)
    (u : Tape)
    (h1 : (!cl.isEmpty && decide (cl.size ≤ 4096) && sv.size == cl.size) = true)
    (h2 : (cl.all fun c => decide (c.ui < lay.U.size)) = true)
    (h3 : (cl.all fun c => (wsClaimShape lay c).isOk) = true)
    (hs : ∀ j ∈ sv.toList, j < F.next ∧ Filled F j) :
    ∃ wo G, flatForkEnd lay cl sv F
        (⟨some RoundName.batSigma.name, 0, sv.size, [], [x]⟩ :: (t ++ u)) = some (wo, G, u) ∧
      Room G k ∧ Below F G ∧ G.next = F.next + slotsMerge lay.lk ∧
      wo.sFv = F.next + (1 + (2 * lay.lk + 1)) ∧ Filled G wo.sFv ∧ Open wo.p G ∧
      wo.rm.size = lay.lk ∧ wo.p.first = F.next ∧
      ∀ j, F.next ≤ j → j < G.next → (Filled G j ↔ j = wo.sFv) := by
  unfold slotsMerge at hR
  obtain ⟨s0, eps, rs, sY, beta, vals, rfl, b1, b2, b3, b4, b5⟩ := tape_masked hT
  obtain ⟨mu0, rfl⟩ := len_one b1
  have hne : sv.size ≠ 0 := by
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, decide_eq_true_eq] at h1
    obtain ⟨⟨a1, _⟩, a3⟩ := h1
    rw [a3]
    simpa [Array.isEmpty] using a1
  obtain ⟨T, hTC⟩ := (shown_wsForkStart sv (powers x sv.size) hs).public
    (by have := hR.fits; omega)
  obtain ⟨p0, d1, d2, d3⟩ := pscBeginR (n := 2 * lay.lk + (1 + 1 + k))
    (by refine hR.mono ?_; omega) hTC mu0 eps 0
    (rs ++ ⟨some RoundName.pscY.name, 1, 0, sY, [beta]⟩ ::
      ⟨some RoundName.pscValues.name, 0, 0, vals, []⟩ :: u)
  obtain ⟨rm, p1, G1, e1, e2, e3, e4, e5, e6, e7⟩ := wsForkRounds_returns lay.lk rs
    (Array.emptyWithCapacity lay.lk) p0 _ (1 + 1 + k)
    (⟨some RoundName.pscY.name, 1, 0, sY, [beta]⟩ ::
      ⟨some RoundName.pscValues.name, 0, 0, vals, []⟩ :: u) b2 b3 d2
  obtain ⟨p2, G2, f1, f2, f3, f4, f5⟩ := pscEndsR e2 (Nat.le_refl 1) (Nat.le_refl 1) 0 0 sY vals
    beta u b4 b5
  have hnx := f2.next
  have hft := f2.fits
  have e4' : G1.next = F.next + 1 + 2 * lay.lk := e4
  have hF0 := f2.ends 0 (by omega)
  rw [Nat.add_zero] at hF0
  have etape : (⟨some RoundName.pscEpsilon.name, 0, 0, [mu0], [eps]⟩ ::
        (rs ++ [⟨some RoundName.pscY.name, 1, 0, sY, [beta]⟩,
          ⟨some RoundName.pscValues.name, 0, 0, vals, []⟩]) ++ u : Tape) =
        ⟨some RoundName.pscEpsilon.name, 0, 0, [mu0], [eps]⟩ ::
        (rs ++ ⟨some RoundName.pscY.name, 1, 0, sY, [beta]⟩ ::
          ⟨some RoundName.pscValues.name, 0, 0, vals, []⟩ :: u) := by simp
  refine ⟨{ toWsMerged := { fvp := G2.vp.getD (G1.next + 1) zeroE, beta := p2.r.back?.getD zeroE,
                            rm := rm, p := p2, sFv := G1.next + 1 }
            recs := (cl.zip (powers x sv.size)).toList.map fun y =>
              wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 rm)) }, G2, ?_, f2.room,
    ⟨f4.trans e5, fun _ => f2.sized, by omega, fun j hj =>
      (f5 j (by omega)).trans ((e6 j).trans filled_next)⟩, by unfold slotsMerge; omega,
    by show G1.next + 1 = _; omega, hF0, f2.isOpen, by
      show rm.size = _
      rw [e7]
      simp, (f3.trans e3).trans d3, fun j q1 q2 => by
      show Filled G2 j ↔ j = G1.next + 1
      have hfi := f2.first
      have hp : p2.first = F.next := (f3.trans e3).trans d3
      by_cases q : j = G1.next + 1
      · subst q
        exact ⟨fun _ => rfl, fun _ => hF0⟩
      · exact ⟨fun hf => absurd hf (f2.own j (by omega) (by omega)), fun hq => absurd hq q⟩⟩
  rw [etape]
  unfold flatForkEnd
  refine bindR (mustR h1 _ _) ?_
  refine bindR (mustR h2 _ _) ?_
  refine bindR (mustR h3 _ _) ?_
  have hm : Fl.wsForkMerge lay.lk sv F
      (⟨some RoundName.batSigma.name, 0, sv.size, [], [x]⟩ ::
        ⟨some RoundName.pscEpsilon.name, 0, 0, [mu0], [eps]⟩ ::
        (rs ++ ⟨some RoundName.pscY.name, 1, 0, sY, [beta]⟩ ::
          ⟨some RoundName.pscValues.name, 0, 0, vals, []⟩ :: u)) =
      some ((⟨G2.vp.getD (G1.next + 1) zeroE, p2.r.back?.getD zeroE, rm, p2, G1.next + 1⟩,
        powers x sv.size), G2, u) := ?_
  · exact bindR hm rfl
  unfold Fl.wsForkMerge
  refine bindR (batchR sv.size hne x F _) ?_
  refine bindR d1 ?_
  refine bindR e1 ?_
  refine bindR f1 ?_
  refine bindR (shownR (by omega) hF0 u) ?_
  rfl

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.wsForkRounds_returns
#print axioms OnBytes.Desc.First.K4.Rt.shown_wsForkStart
#print axioms OnBytes.Desc.First.K4.Rt.forkEnd_returns
