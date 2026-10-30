-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/FlPort/FoPlaneAt.lean: a carried copy, made by a program, not typed by hand.

Of which file: OnBytes/Tie/Pv/Lookup/Forest/FoPlaneAt.lean, as it lies in this library.
What is carried: those of its declarations that depend on a context of the verifier program's
channel, and no other:
  planeClaims_at
How: by one swap of names throughout: a context becomes a tape; a routine
of the program becomes the library's flat function of the same text (OnBytes/K/Kc/Flat.lean,
OnBytes/K/Kc/FlatHear.lean). The laws on "returns" are those of Johnson/Top/H/FlPort/Kit.lean. Every
other name is the library's own: plain records, pure functions and lemmas on them, used from where
they lie. Those of OnBytes/Tie/Pv/ that the text names, as far as a program sees them:
  FormIs, Later, LedAt, OnMasks, Sized, byVar_len, colsK, countK, countK_congr, dgOf, evalL,
  evalL_append, evalL_muOf, evalL_scale, foldl_add_from, leaves, ledAt_end, ledF, numsF,
  nums_led, ok_parts, onMasks_append, onMasks_hide, onMasks_incTop, onMasks_scale, ordB,
  ordB_len, ordE, ordE_len, pinColK, pin_sum, pin_target, plane_sum_g, planesK, planesK_congr,
  rowRes, sBit, tabF
The comments on the declarations are the library's, under the same swap: where they say "run" or
"view", read: on a tape.

Limits. What is proved here is proved of the flat functions alone, and a flat function tests less of
the plan than the program's routine (the paragraph "Not claimed" in the head of
OnBytes/K/Kc/Flat.lean). Nothing is said where a function refuses. A tie: it has no error term. If
the source file turns, this copy does not follow by itself. In the list of names a use by dot
notation on a hypothesis is not seen, and a short name may stand once too often. That no routine
in a context is reached from a statement or a proof here is meant, and is not shown in this
library.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPlaneAt
import Johnson.Top.H.FlPort.Kit
import Johnson.Desc.First.Look.LookPlanes
import Johnson.Top.H.FlPort.PscWhole
import Johnson.Top.H.FlPort.PscRun
import Johnson.Top.H.FlPort.FoPscForm
import Johnson.Top.H.FlPort.FoTieRun
import Johnson.Top.H.FlPort.FoPlaneRead
import Johnson.Top.H.FlPort.FoPlaneClaims

set_option autoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open Cb Cb.Fo Cb.Fo.PlaneClaims VerifiableInference.Desc.First.Look
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.PscTie _root_.Fo

section
variable {K : Type} [CommRing K]

variable (ρ : OnBytes.Model.Reading K)

theorem planeClaims_at (g : Heard) (lm jLK : ℕ) (θ : K) (t : Trace K) (bit : ℕ → ℕ → Fl Aff)
    (pin : ℕ → Fl Aff) (hb : ∀ e col, Quiet (bit e col)) (hp : ∀ col, Quiet (pin col))
    (F0 F1 F G : Fork) (c c' : Tape) (rows : Array Aff)
    (h : planeClaimsF g lm bit pin F c = .ok ((rows, G), c'))
    (hok : FoNums.ok g.shape = true) (h0 : Later F0 F) (h1 : Later F1 F) (hF : Sized F)
    {mu eps : E} {zd : List (E × ℕ)} {rs : List (List E × E)}
    (hRan : Ran g.leaves (jLK + (FoNums.S g.shape).fEnd) mu eps zd rs)
    (hdg : dgOf zd = dgE (numsF g.shape lm jLK θ)) {tg : K}
    (hC : FormIs ρ F0 g.leaves.start tg
      (incTop (numsF g.shape lm jLK θ).ledT (incT0 (numsF g.shape lm jLK θ) t) t.tabl.reverse))
    (ht : ρ.val g.leaves.target = tg)
    (hEps : ρ.val g.leaves.eps = t.cls.eps) (hFin : ρ.val g.leaves.claim = t.cls.fin)
    (hXs : g.leaves.r.toList.map ρ.val = t.cls.xs)
    (hA : ρ.val g.leavesA = ((List.range (2 ^ g.shape.d)).map fun r =>
      eqN ((byVar (FoNums.ordE g.shape) t.cls.xs).drop FoNums.w) r *
        (t.lam - 1 - tabF g.shape θ r)).sum)
    (hz0 : rdL ρ g.zb0 = (byVar (FoNums.ordE g.shape) t.cls.xs).reverse)
    (hz1 : rdL ρ g.zb1 = (byVar (FoNums.ordB g.shape) t.bits.xs).reverse)
    (hBit : FormIs ρ F1 (Aff.slot g.sBit) (t.bits.v 0)
      [((numsF g.shape lm jLK θ).ledB.sh 0, t.bits.be)]) :
    c' = c ∧ Later F G ∧ Sized G ∧ G.next = F.next ∧
      ∃ r0 r1 r2, rows = #[r0, r1, r2] ∧
        ∀ H, Later G H → ∀ (μ : Pl → K) (entry : ℕ → ℕ → ℕ → K), μ .zero = 0 →
          (∀ col, col < g.shape.NC * 2 ^ (g.shape.kT + 5 - lm) →
            (got (bit 0 col) F c).value ρ (H.worldOf ρ (fun j => μ (.mask j)) entry) =
            colsK g.shape lm (byVar (FoNums.ordE g.shape) t.cls.xs).reverse μ col) →
          (∀ col, col < g.shape.NC * 2 ^ (g.shape.kT + 5 - lm) →
            (got (bit 1 col) F c).value ρ (H.worldOf ρ (fun j => μ (.mask j)) entry) =
            colsK g.shape lm (byVar (FoNums.ordB g.shape) t.bits.xs).reverse μ col) →
          (∀ col, col < g.shape.NC * 2 ^ (g.shape.kT + 5 - lm) →
            (got (pin col) F c).value ρ (H.worldOf ρ (fun j => μ (.mask j)) entry) =
            Pin.pinColK lm μ col) →
          r0.value ρ (H.worldOf ρ (fun j => μ (.mask j)) entry) =
              rowRes μ (rowEnd (numsF g.shape lm jLK θ) t) ∧
          r1.value ρ (H.worldOf ρ (fun j => μ (.mask j)) entry) =
              -rowRes μ (rowBitE (numsF g.shape lm jLK θ) t) ∧
          r2.value ρ (H.worldOf ρ (fun j => μ (.mask j)) entry) =
              rowRes μ (rowNum (numsF g.shape lm jLK θ)) := by
  have hsc : dgE (numsF g.shape lm jLK θ) = (FoNums.S g.shape).scEnd.degs :=
    (nums_led g.shape jLK lm θ).2.2.2.2.2.2
  have hL : LedAt (ledF jLK (FoNums.S g.shape).pEndC) (jLK + (FoNums.S g.shape).fEnd)
      (dgOf zd) 0 := by
    rw [hdg, hsc]
    exact ledAt_end g.shape jLK
  have hv : g.shape.v < 64 := lt_trans (Cb.Fo.ok_parts hok).1.2.2.2.2.1 (by decide)
  obtain ⟨hm, a1, a2, a3, a4, r0, r1, r2, hr, hval⟩ :=
    planeClaims_rows ρ g lm bit pin hb hp F0 F G c c' rows h hRan hC ht h0 hF hL hv []
  have hlm : 5 ≤ lm ∧ lm ≤ g.shape.kT + 5 := by
    unfold planeCols at hm
    by_contra hc
    have : (lm < 5 || lm > g.shape.kT + 5) = true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      omega
    rw [if_pos this] at hm
    exact absurd hm (by decide)
  refine ⟨a1, a2, a3, a4, r0, r1, r2, hr, fun H hH μ entry hz hB0 hB1 hP => ?_⟩
  obtain ⟨v0, v1, v2⟩ := hval H hH (fun j => μ (.mask j)) entry
  have hE : ρ.val eps = t.cls.eps := by
    rw [← hRan.eps_eq]
    exact hEps
  refine ⟨?_, ?_, ?_⟩
  · have hM : OnMasks (hide (ledF jLK (FoNums.S g.shape).pEndC) (dgE (numsF g.shape lm jLK θ))
        t.cls.xs ++ scale t.cls.eps (incTop (numsF g.shape lm jLK θ).ledT
          (incT0 (numsF g.shape lm jLK θ) t) t.tabl.reverse)) :=
      onMasks_append (onMasks_hide _ (fun _ _ => ⟨_, rfl⟩) ⟨_, rfl⟩ _ _)
        (onMasks_scale _ (onMasks_incTop g.shape lm jLK θ t))
    have hP0 : evalL μ (bitsForm (numsF g.shape lm jLK θ) (byVar (FoNums.ordE g.shape) t.cls.xs)) =
        planesK g.shape lm (byVar (FoNums.ordE g.shape) t.cls.xs).reverse
          (colsK g.shape lm (byVar (FoNums.ordE g.shape) t.cls.xs).reverse μ) :=
      plane_sum_g g.shape hok lm jLK hlm.1 hlm.2 θ μ hz _ (by rw [byVar_len, ordE_len])
    have hR : rowRes μ (rowEnd (numsF g.shape lm jLK θ) t) =
        evalL μ (hide (ledF jLK (FoNums.S g.shape).pEndC) (dgE (numsF g.shape lm jLK θ)) t.cls.xs ++
          scale t.cls.eps (incTop (numsF g.shape lm jLK θ).ledT
            (incT0 (numsF g.shape lm jLK θ) t) t.tabl.reverse)) +
          t.cls.eps * ((List.range (2 ^ g.shape.d)).map fun r =>
            eqN ((byVar (FoNums.ordE g.shape) t.cls.xs).drop FoNums.w) r *
              (t.lam - 1 - tabF g.shape θ r)).sum *
            evalL μ (bitsForm (numsF g.shape lm jLK θ) (byVar (FoNums.ordE g.shape) t.cls.xs)) -
          (t.cls.fin - t.cls.eps * 1) := by
      show evalL μ (_ ++ scale _ _) - _ = _
      rw [evalL_append, evalL_scale]
      rfl
    rw [v0, planesK_congr g.shape lm _ _ _ hB0, hdg, hEps, hFin, hXs, hE, hA, hz0, hR, hP0]
    unfold rowRes rowU
    simp only
    rw [evalL_muOf hM μ]
    ring
  · have hP1 : evalL μ (bitsForm (numsF g.shape lm jLK θ) (byVar (FoNums.ordB g.shape) t.bits.xs)) =
        planesK g.shape lm (byVar (FoNums.ordB g.shape) t.bits.xs).reverse
          (colsK g.shape lm (byVar (FoNums.ordB g.shape) t.bits.xs).reverse μ) :=
      plane_sum_g g.shape hok lm jLK hlm.1 hlm.2 θ μ hz _ (by rw [byVar_len, ordB_len])
    have hS := (hBit H ((h1.trans a2).trans hH)).2 (fun j => μ (.mask j)) entry
    rw [Aff.value_slot, evalL_muOf (fun pc hpc => by
      rw [List.mem_singleton.mp hpc]
      exact ⟨_, rfl⟩) μ] at hS
    have hR : rowRes μ (rowBitE (numsF g.shape lm jLK θ) t) =
        evalL μ (bitsForm (numsF g.shape lm jLK θ) (byVar (FoNums.ordB g.shape) t.bits.xs)) +
          evalL μ [((numsF g.shape lm jLK θ).ledB.sh 0, t.bits.be)] - t.bits.v 0 := by
      show evalL μ (_ ++ _) - _ = _
      rw [evalL_append]
      rfl
    rw [v1, planesK_congr g.shape lm _ _ _ hB1, hS, hz1, hR, hP1]
    ring
  · rw [v2, countK_congr g.shape lm _ _ hP]
    unfold rowRes Pin.countK
    rw [Pin.foldl_add_from, show evalL μ (rowNum (numsF g.shape lm jLK θ)).cf = _ from
      Pin.pin_sum g.shape lm jLK θ μ hz (Cb.Fo.ok_parts hok).1.2.2.1 hlm.1 hlm.2,
      PadFac.pin_target g.shape hok]
    ring

end

end Fo.Tp
