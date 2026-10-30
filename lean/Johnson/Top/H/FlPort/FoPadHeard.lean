-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/FlPort/FoPadHeard.lean: a carried copy, made by a program, not typed by hand.

Of which file: OnBytes/Tie/Pv/Lookup/Forest/FoPadHeard.lean, as it lies in this library.
What is carried: those of its declarations that depend on a context of the verifier program's
channel, and no other:
  pad_heard
How: by one swap of names throughout: a context becomes a tape; a routine
of the program becomes the library's flat function of the same text (OnBytes/K/Kc/Flat.lean,
OnBytes/K/Kc/FlatHear.lean). The laws on "returns" are those of Johnson/Top/H/FlPort/Kit.lean. Every
other name is the library's own: plain records, pure functions and lemmas on them, used from where
they lie. Those of OnBytes/Tie/Pv/ that the text names, as far as a program sees them:
  FormIs, HeardIs, Later, Later.refl, RowIs, drop_rev, endsOf, flEv, forN, forTrace,
  forall₂_getD, forall₂_mono, forall₂_of_getD, heard_e, heard_leavesA, heard_tT, heard_zk, ordK,
  pntK, pntK_len, rdL_extract, sBit, slotNo, take_rev, tieRowsR_len, zero_add_fun
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
import OnBytes.Tie.Pv.Lookup.Forest.FoPadHeard
import Johnson.Top.H.FlPort.Kit
import Johnson.Top.H.FlPort.FoR5Run
import Johnson.Top.H.FlPort.PscWhole
import Johnson.Top.H.FlPort.PscRun
import Johnson.Top.H.FlPort.FoPscForm
import Johnson.Top.H.FlPort.FoTieRun
import Johnson.Top.H.FlPort.FoLevel
import Johnson.Top.H.FlPort.FoRds
import Johnson.Top.H.FlPort.FoHeard
import Johnson.Top.H.FlPort.FoLevelRun
import Johnson.Top.H.FlPort.FoDraws
import Johnson.Top.H.FlPort.FoPadCut
import Johnson.Top.H.FlPort.PscRounds
import Johnson.Top.H.FlPort.FoWalks
import Johnson.Top.H.FlPort.FoDescent
import Johnson.Top.H.FlPort.FoPadFlat
import Johnson.Top.H.FlPort.FoR5At
import Johnson.Top.H.FlPort.FoR5
import Johnson.Top.H.FlPort.FoTieNums
import Johnson.Top.H.FlPort.FoTieEnd
import Johnson.Top.H.FlPort.FoTieAll
import Johnson.Top.H.FlPort.FoTieInv
import Johnson.Top.H.FlPort.FoHead
import Johnson.Top.H.FlPort.FoLevelLaw
import Johnson.Top.H.FlPort.FoWalksAt

set_option autoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open TwV FoNums OnBytes OnBytes.Model OnBytes.PscRun OnBytes.PscTie

section
variable {K : Type} [CommRing K] (ρ : Reading K)

theorem pad_heard {lm : ℕ} {pub : Array Nat} {F : Fork} {c c' : Tape} {M : PadMid} {l : List Ev}
    {scs : List (Sc K)} {ptT : Array OnBytes.E} {lvK lvT : List (Sc K × K)}
    {rowsK rowsT : List Aff} {evK evT : List Ev} {D : R5D}
    (R : PadRead ρ lm pub F c c' M l scs ptT lvK lvT rowsK rowsT evK evT D)
    (H : FoNums.ok (M.h pub) = true) :
    HeardIs ρ (M.heard pub F) M.G8 (endsOf (M.h pub) lm F.next (flEv ρ l)) := by
  have l78 : Later M.F7 M.G8 := R.r5.later
  have l68 : Later M.F6 M.G8 := R.table.later.trans l78
  have l58 : Later M.F5 M.G8 := R.keys.later.trans l68
  have hθ : ρ.val M.theta = (endsOf (M.h pub) lm F.next (flEv ρ l)).theta := R.theta.symm
  have hα : ρ.val M.alpha = (endsOf (M.h pub) lm F.next (flEv ρ l)).alpha := by
    show _ = (forTrace (M.h pub) lm F.next (flEv ρ l)).lam
    rw [R.trace]
  have hzb0 : rdA ρ M.zb0 = (endsOf (M.h pub) lm F.next (flEv ρ l)).zb0 := by
    show _ = (byVar (forN (M.h pub) lm F.next (flEv ρ l)).oE
      (forTrace (M.h pub) lm F.next (flEv ρ l)).cls.xs).reverse
    rw [R.trace, R.nums]
    exact R.r5.zb0Is
  have hpn : pntK (forN (M.h pub) lm F.next (flEv ρ l)) (forTrace (M.h pub) lm F.next (flEv ρ l)) =
      pntTop (fun i => ordK (M.h pub) (0 + i)) [] lvK.reverse := by
    unfold pntK
    rw [R.trace, R.nums, zero_add_fun]
    rfl
  have hlen := pntK_len (K := K) (M.h pub) H lm F.next (flEv ρ l)
  have hrho : rdA ρ M.keys.rho =
      (pntK (forN (M.h pub) lm F.next (flEv ρ l))
        (forTrace (M.h pub) lm F.next (flEv ρ l))).reverse := by
    rw [hpn]
    exact R.keys.rho
  have hsz : M.keys.rho.size = (M.h pub).dT + (M.h pub).rK := by
    have := congrArg List.length hrho
    simpa [rdA, hlen] using this
  have hzx : rdA ρ (M.zx pub) = (endsOf (M.h pub) lm F.next (flEv ρ l)).zx := by
    show rdL ρ (M.keys.rho.extract 0 (M.h pub).dT) = ((pntK _ _).drop (M.h pub).rK).reverse
    rw [rdL_extract]
    show List.take ((M.h pub).dT - 0) (List.drop 0 (rdA ρ M.keys.rho)) = _
    rw [hrho, List.drop_zero, Nat.sub_zero]
    exact take_rev _ _ _ hlen
  have hzy : rdA ρ (M.zy pub) = (endsOf (M.h pub) lm F.next (flEv ρ l)).zy := by
    show rdL ρ (M.keys.rho.extract (M.h pub).dT M.keys.rho.size) =
      ((pntK _ _).take (M.h pub).rK).reverse
    rw [rdL_extract]
    show List.take (M.keys.rho.size - (M.h pub).dT) (List.drop (M.h pub).dT (rdA ρ M.keys.rho)) = _
    rw [hrho, hsz]
    exact drop_rev _ _ _ hlen
  have hN := R.nums
  have hT := R.trace
  -- the rows, as lists
  have hrows : List.Forall₂ (RowIs ρ M.G8) (M.table.rows.push M.row).toList
      (endsOf (M.h pub) lm F.next (flEv ρ l)).rows := by
    show List.Forall₂ _ _
      ((tieRowsR (forN (M.h pub) lm F.next (flEv ρ l)) (forTrace (M.h pub) lm F.next (flEv ρ l)).lam
          (forTrace (M.h pub) lm F.next (flEv ρ l)).tie.reverse).reverse ++
        (lvRowsR (forN (M.h pub) lm F.next (flEv ρ l)).ledK 0
          (fK (forN (M.h pub) lm F.next (flEv ρ l)) (forTrace (M.h pub) lm F.next (flEv ρ l)))
          (forTrace (M.h pub) lm F.next (flEv ρ l)).keys.reverse).reverse ++
        (lvRowsR (forN (M.h pub) lm F.next (flEv ρ l)).ledT
          (forN (M.h pub) lm F.next (flEv ρ l)).w
          (incT0 (forN (M.h pub) lm F.next (flEv ρ l)) (forTrace (M.h pub) lm F.next (flEv ρ l)))
          (forTrace (M.h pub) lm F.next (flEv ρ l)).tabl.reverse).reverse ++
        [rowBitU (forN (M.h pub) lm F.next (flEv ρ l)) (forTrace (M.h pub) lm F.next (flEv ρ l))])
    rw [Array.toList_push, R.table.pushed, R.keys.pushed, hN, hT]
    refine List.rel_append (List.rel_append (List.rel_append ?_ ?_) ?_) (.cons ?_ .nil)
    · refine forall₂_of_getD {} ⟨[], 0⟩ _ _ ?_ fun i hi => ?_
      · rw [List.length_reverse, tieRowsR_len, List.length_reverse, R.scsLen]
        exact R.tieN
      · have hi' : i < 31 := by simpa [R.tieN] using hi
        have := (R.tieRows i hi').later ρ l58
        rwa [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, ← List.getD_eq_getElem?_getD]
          at this
    · exact forall₂_mono (fun a b (h : RowIs ρ M.F6 a b) => h.later ρ l68) R.keys.rows0
    · exact forall₂_mono (fun a b (h : RowIs ρ M.F7 a b) => h.later ρ l78) R.table.rows0
    · exact R.bitRow _ rfl
  have hzd : (zdL (5 + (M.h pub).d) (M.h pub).d M.table.rho).map (fun p => ρ.val p.1) =
      (endsOf (M.h pub) lm F.next (flEv ρ l)).lvZs := by
    show _ = inRounds (forN (M.h pub) lm F.next (flEv ρ l)).oE
      (pntTop (forN (M.h pub) lm F.next (flEv ρ l)).oT
        (forTrace (M.h pub) lm F.next (flEv ρ l)).join
        (forTrace (M.h pub) lm F.next (flEv ρ l)).tabl.reverse)
    rw [hN, hT, R.r5.lvZs, zero_add_fun]
    rfl
  have hdg : (zdL (5 + (M.h pub).d) (M.h pub).d M.table.rho).map (fun p => p.2) =
      (endsOf (M.h pub) lm F.next (flEv ρ l)).lvDg.map (· + 1) := by
    show _ = (dgE (forN (M.h pub) lm F.next (flEv ρ l))).map (· + 1)
    rw [hN]
    exact R.lvDg
  have hfirst : M.lv.first = (endsOf (M.h pub) lm F.next (flEv ρ l)).lvFirst :=
    R.r5.lvFirst.trans R.next7
  have htg : ρ.val M.lv.target = (endsOf (M.h pub) lm F.next (flEv ρ l)).lvTg := by
    show _ = tgTop (tgT0 (forN (M.h pub) lm F.next (flEv ρ l))
      (forTrace (M.h pub) lm F.next (flEv ρ l)))
      (forTrace (M.h pub) lm F.next (flEv ρ l)).tabl.reverse
    rw [hN, hT, R.r5.lvTarget]
    exact (R.table.form0 M.F7 (Later.refl _)).1 D.tgL R.r5.target
  exact
    { theta := hθ
      alpha := hα
      a := by
        show _ = fac (forN (M.h pub) lm F.next (flEv ρ l))
          (forTrace (M.h pub) lm F.next (flEv ρ l)).lam
        rw [hN, hT]
        exact R.fac
      nRows := by
        have := hrows.length_eq
        rwa [Array.length_toList] at this
      rows := fun i hi => by
        have := forall₂_getD {} ⟨[], 0⟩ hrows i (by rwa [Array.length_toList])
        rwa [List.getD_eq_getElem?_getD, Array.getElem?_toList, ← Array.getD_eq_getD_getElem?]
          at this
      lvEps := by
        show _ = (forTrace (M.h pub) lm F.next (flEv ρ l)).cls.eps
        rw [hT]
        exact R.r5.lvEps
      lvFin := by
        show _ = (forTrace (M.h pub) lm F.next (flEv ρ l)).cls.fin
        rw [hT]
        exact R.r5.lvFin
      lvXs := by
        show _ = (forTrace (M.h pub) lm F.next (flEv ρ l)).cls.xs
        rw [hT]
        exact R.r5.lvXs
      lvVars := ⟨_, R.r5.lvVars, hzd, hdg⟩
      lvRan := ⟨D.muL, _, _, by
        have := R.r5.ranL
        rw [← R.r5.lvFirst, hfirst, ← this.eps_eq] at this
        exact this, hzd, hdg⟩
      lvSize := by
        have h1 := congrArg List.length R.r5.ranL.r_eq
        have h2 := congrArg List.length R.r5.ranL.vars_eq
        have h3 := R.r5.ranL.fits.length
        simp only [Array.length_toList, List.length_map, eqW] at h1 h2
        show M.lv.r.size = M.lv.vars.size
        omega
      lvFlags := R.r5.lvFlags
      lvTg := htg
      lvStart := by
        show FormIs ρ M.G8 M.lv.start
          (tgTop (tgT0 (forN (M.h pub) lm F.next (flEv ρ l))
            (forTrace (M.h pub) lm F.next (flEv ρ l)))
            (forTrace (M.h pub) lm F.next (flEv ρ l)).tabl.reverse)
          (incTop (forN (M.h pub) lm F.next (flEv ρ l)).ledT
            (incT0 (forN (M.h pub) lm F.next (flEv ρ l))
              (forTrace (M.h pub) lm F.next (flEv ρ l)))
            (forTrace (M.h pub) lm F.next (flEv ρ l)).tabl.reverse)
        rw [hN, hT, R.r5.lvStart]
        exact R.table.form0.later ρ l78
      lvFirst := hfirst
      leavesA := heard_leavesA ρ (M.h pub) H lm F.next (flEv ρ l) M.theta M.alpha M.zb0 hθ hα hzb0
      sBit := by
        show _ = slotNo ((forN (M.h pub) lm F.next (flEv ρ l)).ledB.sh 0)
        rw [hN]
        exact R.sBit
      sBitAt := by
        show FormIs ρ M.G8 (Aff.slot M.sBit) ((forTrace (M.h pub) lm F.next (flEv ρ l)).bits.v 0)
          [(Pl.mask (slotNo ((forN (M.h pub) lm F.next (flEv ρ l)).ledB.sh 0)),
            (forTrace (M.h pub) lm F.next (flEv ρ l)).bits.be)]
        rw [hN, hT, ← R.sBit]
        exact R.sBitAt
      zx := hzx
      zy := hzy
      e := heard_e ρ (M.h pub) H lm F.next (flEv ρ l) (M.zy pub) hzy
      cEnd := by
        show FormIs ρ M.G8 M.keys.form (forTrace (M.h pub) lm F.next (flEv ρ l)).kT
          (incTop (forN (M.h pub) lm F.next (flEv ρ l)).ledK
            (fK (forN (M.h pub) lm F.next (flEv ρ l)) (forTrace (M.h pub) lm F.next (flEv ρ l)))
            (forTrace (M.h pub) lm F.next (flEv ρ l)).keys.reverse)
        rw [hN, hT]
        exact R.keys.form0.later ρ l68
      zb0 := hzb0
      zb1 := by
        show _ = (byVar (forN (M.h pub) lm F.next (flEv ρ l)).oB
          (forTrace (M.h pub) lm F.next (flEv ρ l)).bits.xs).reverse
        rw [hT, hN]
        exact R.r5.zb1Is
      tT := heard_tT ρ (M.h pub) H lm F.next (flEv ρ l) M.zb0 hzb0
      zk := heard_zk ρ (M.h pub) H lm F.next (flEv ρ l) (M.zx pub) (M.zy pub) hzx hzy }

end

end Fo.Tp
