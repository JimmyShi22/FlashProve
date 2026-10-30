-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/FlPort/FoLevelLaw.lean: a carried copy, made by a program, not typed by hand.

Of which file: OnBytes/Tie/Pv/Lookup/Forest/FoLevelLaw.lean, as it lies in this library.
What is carried: those of its declarations that depend on a context of the verifier program's
channel, and no other:
  levelLaw
How: by one swap of names throughout: a context becomes a tape; a routine
of the program becomes the library's flat function of the same text (OnBytes/K/Kc/Flat.lean,
OnBytes/K/Kc/FlatHear.lean). The laws on "returns" are those of Johnson/Top/H/FlPort/Kit.lean. Every
other name is the library's own: plain records, pure functions and lemmas on them, used from where
they lie. Those of OnBytes/Tie/Pv/ that the text names, as far as a program sees them:
  Later, Later.refl, LedAt, Sized, byVar_snoc, closed_level, dgOf, dg_level, down_read,
  filled_tile, flEv_level, hideRun_filled, hideRun_later, hideRun_ok, levelEv, lvZd, ran_takeSc,
  rds_level, rowRes, shown_vp, slot_formIs, stored_read, took, took_later, took_sized, walk_len,
  xs_level, zs_level
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
import OnBytes.Tie.Pv.Lookup.Forest.FoLevelLaw
import Johnson.Top.H.FlPort.Kit
import Johnson.Top.H.FlPort.PscWhole
import Johnson.Top.H.FlPort.PscRun
import Johnson.Top.H.FlPort.FoPscForm
import Johnson.Top.H.FlPort.FoTieRun
import Johnson.Top.H.FlPort.FoLevel
import Johnson.Top.H.FlPort.FoRds
import Johnson.Top.H.FlPort.FoHeard
import Johnson.Top.H.FlPort.FoLevelRun

set_option autoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open TwV OnBytes OnBytes.Model OnBytes.PscRun OnBytes.PscTie

section
variable {K : Type} [CommRing K] (ρ : Reading K)

theorem levelLaw : LevelLaw ρ := by
  intro s s' mu order F G c c' pt tg inc L hrun hperm hS hlen hrho hform hL
  obtain ⟨o, hIn, hrows, hrho', hform'⟩ := level_ok _ _ _ _ _ _ _ _ hrun
  obtain ⟨p, m0, eps, rs, sentY, beta, vals, vL, vR, F3, p', hol, hpub, hst, hrl, hv, hq, hsY, hsv,
    hE,
    hR, hsL, hsR, hH3, hvL, hvR, hH7, hor, hrow, hRun⟩ := levelIn_ran _ _ _ _ _ _ _ _ _ hIn
  have hS1 : Sized (took F (1 + 2 * order.length + (2 + 2))) := took_sized _ hS
  obtain ⟨hSame3, hS3, hin3, -⟩ := hideRun_ok _ _ _ _ _ hS1 hH3
  obtain ⟨hSame7, hS7, -, -⟩ := hideRun_ok _ _ _ _ _ hS3 hH7
  have hFF3 : Later F F3 := (took_later F _).trans (hideRun_later hS1 hH3)
  have hL7 : Later F3 G := hideRun_later hS3 hH7
  have htg : ρ.val p.target = tg := (hform F (Later.refl F)).1 _ hpub
  have hxs : p.r.toList.map ρ.val = (rs.map (·.2)).map ρ.val ++ [ρ.val beta] := by
    rw [hR.r_eq]; exact xs_level ρ rs sentY beta
  have h0 := hin3 0 (by omega)
  have h1 := hin3 1 (by omega)
  rw [Nat.add_zero] at h0
  have hvL' : ρ.val vL = (vals.toList.map ρ.val).getD 0 0 := by
    rw [shown_vp hvL, h0.2.2.2.1]
    simp [Array.getD_eq_getD_getElem?, hsv]
  have hvR' : ρ.val vR = (vals.toList.map ρ.val).getD 1 0 := by
    rw [shown_vp hvR, h1.2.2.2.1]
    simp [Array.getD_eq_getD_getElem?, hsv]
  have hw := walk_len hR (by simp)
  have hdg : (dgOf (lvZd mu s.rho order ++ [(zeroE, 3)])).sum = 2 * mu + 2 := by
    show ((lvZd mu s.rho order ++ [(zeroE, 3)]).map fun x : OnBytes.E × ℕ => x.2 - 1).sum = _
    rw [dg_level mu s.rho order hol]
    simp
    omega
  refine ⟨levelEv m0 eps rs sentY beta vals o.tau,
    ⟨ρ.val p.eps, p.r.toList.map ρ.val, ρ.val p.claim, vals.toList.map ρ.val⟩, ρ.val o.tau, o.row,
    hE, rds_level _ _ _ _ _ _ _, closed_level ρ _ _ _ _ _ _ _, hFF3.trans hL7, hS7, ?_, ?_, ?_,
    ?_, hrows, ?_, ?_, ?_⟩
  · have := hSame3.trans hSame7
    rw [hol] at this
    exact this
  · have f1 := (hideRun_filled hS1 hH3).2.1
    have f2 := (hideRun_filled hS3 hH7).2.1
    rw [Array.size_replicate, hw, hdg] at f2
    rw [hsv] at f1
    have f := filled_tile (F0 := F) f1 f2 (by rw [hsL, hol]; omega)
    intro j
    rw [f j, show 1 + (2 * mu + 2) + 2 = 1 + 2 * mu + 4 by omega]
  · intro j hj
    have g1 := (hideRun_filled hS1 hH3).2.2 j (by rw [hsv, hsL, hol]; omega)
    have g2 := (hideRun_filled hS3 hH7).2.2 j (by rw [Array.size_replicate, hw, hdg]; omega)
    exact ⟨g2.1.trans g1.1, g2.2.trans g1.2⟩
  · intro rest
    have h := ran_takeSc ρ hR (some vals.toList) (([], [ρ.val o.tau]) :: rest)
    rw [htg, zs_level ρ mu s.rho order (fun v hv' => (hv v hv').1) pt hlen hrho] at h
    rw [flEv_level, List.append_assoc]
    exact h
  · rw [hrow]
    have hL' : LedAt L F.next (dgOf (lvZd mu s.rho order ++ [(zeroE, 3)])) 2 := by
      show LedAt L F.next ((lvZd mu s.rho order ++ [(zeroE, 3)]).map
        fun x : OnBytes.E × ℕ => x.2 - 1) 2
      rw [dg_level mu s.rho order hol]
      exact hL
    have h := (row_form ρ hR hRun (hst ▸ hform) htg hFF3 hS3 hL'
      (vals.toList.map ρ.val)).2.2.2.2.2
    intro H hH mask entry
    rw [← hrow, h H hH mask entry, Aff.value_empty, mul_zero, add_zero, ρ.mul, hvL', hvR']
    show rowRes _ (rowU L ((lvZd mu s.rho order ++ [(zeroE, 3)]).map
      fun x : OnBytes.E × ℕ => x.2 - 1) _ _ _) = _
    rw [dg_level mu s.rho order hol]
    rfl
  · rw [hrho']
    refine down_read ρ.val o.tau o.r _ ?_
    rw [hor, stored_read ρ.val mu order hperm (rs.map (·.2)) (by simp [hrl, hol])
      (Array.replicate mu zeroE) (by simp)]
    show _ = (byVar order (p.r.toList.map ρ.val)).reverse
    rw [hxs, byVar_snoc order _ _ (by simpa [hrl, hol] using hperm)]
  · rw [hform', hsR]
    have f0 := slot_formIs ρ (hL7.keep _ h0.2.2.1).1
    have f1 := slot_formIs ρ (hL7.keep _ h1.2.2.1).1
    rw [(hL7.keep _ h0.2.2.1).2.1, (hL7.keep _ h0.2.2.1).2.2, h0.2.2.2.1, h0.2.2.2.2] at f0
    rw [(hL7.keep _ h1.2.2.1).2.1, (hL7.keep _ h1.2.2.1).2.2, h1.2.2.2.1, h1.2.2.2.2] at f1
    have f := f0.lin2 ρ f1 (subE oneE o.tau) o.tau
    have e0 : L.sh 0 = .mask o.sL := by
      rw [hL.sh 0 (by omega), hsL, hol]
      simp
      omega
    have e1 : L.sh 1 = .mask (o.sL + 1) := by
      rw [hL.sh 1 (by omega), hsL, hol]
      simp
      omega
    have eb : (⟨ρ.val p.eps, p.r.toList.map ρ.val, ρ.val p.claim, vals.toList.map ρ.val⟩ :
        Sc K).be = ρ.val beta := by
      show (p.r.toList.map ρ.val).getLastD 0 = _
      rw [hxs]
      simp
    have ev0 : ρ.val (vals.getD 0 zeroE) = (vals.toList.map ρ.val).getD 0 0 := by
      simp [Array.getD_eq_getD_getElem?, hsv]
    have ev1 : ρ.val (vals.getD 1 zeroE) = (vals.toList.map ρ.val).getD 1 0 := by
      simp [Array.getD_eq_getD_getElem?, hsv]
    unfold lineTg lineForm
    rw [eb, e0, e1]
    rw [ρ.sub, ρ.one, ev0, ev1] at f
    simpa [scale, Sc.v, mul_comm] using f

end

end Fo.Tp
