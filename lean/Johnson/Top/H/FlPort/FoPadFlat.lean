-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/FlPort/FoPadFlat.lean: a carried copy, made by a program, not typed by hand.

Of which file: OnBytes/Tie/Pv/Lookup/Forest/FoPadFlat.lean, as it lies in this library.
What is carried: those of its declarations that depend on a context of the verifier program's
channel, and no other:
  PadRead, clean_of, point_size, pad_read
How: by one swap of names throughout: a context becomes a tape; a routine
of the program becomes the library's flat function of the same text (OnBytes/K/Kc/Flat.lean,
OnBytes/K/Kc/FlatHear.lean). The laws on "returns" are those of Johnson/Top/H/FlPort/Kit.lean. Every
other name is the library's own: plain records, pure functions and lemmas on them, used from where
they lie. Those of OnBytes/Tie/Pv/ that the text names, as far as a program sees them:
  FormIs, Later, Later.refl, RowIs, Sized, Stretch, drawsEv, drawsEv_rds, draws_shift, eqForm_eq,
  fTie_off, first_end, first_key0, first_tab0, flEv, flEv_app, forN, forN_of, forTrace,
  forTrace_of, head_fac, key_slots, ledF, leds_key, leds_tab, numsF, ok_parts, ok_v, ordK, ordT,
  owed3, owed3_sized, ran_begin, rhoT, sBit, shiftOf_read, shiftRd, slotNo, tab_slots, thetaOf,
  theta_of, tieGo_len, tieOff, tieTrace, walkSlots
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
import OnBytes.Tie.Pv.Lookup.Forest.FoPadFlat
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
import Johnson.Top.H.FlPort.FoDescent
import Johnson.Top.H.FlPort.FoR5At
import Johnson.Top.H.FlPort.FoR5
import Johnson.Top.H.FlPort.FoTieNums
import Johnson.Top.H.FlPort.FoTieEnd
import Johnson.Top.H.FlPort.FoTieAll
import Johnson.Top.H.FlPort.FoTieInv
import Johnson.Top.H.FlPort.FoHead
import Johnson.Top.H.FlPort.FoLevelLaw

set_option autoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open TwV FoNums OnBytes OnBytes.Model OnBytes.PscRun OnBytes.PscTie Cb.Fo.Walk

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- What the stretches of a run give together. -/
structure PadRead (lm : ℕ) (pub : Array Nat) (F : Fork) (c c' : Tape) (M : PadMid) (l : List Ev)
    (scs : List (Sc K)) (ptT : Array OnBytes.E) (lvK lvT : List (Sc K × K))
    (rowsK rowsT : List Aff) (evK evT : List Ev) (D : R5D) : Prop where
  evs : Evs l c c'
  rds : Rds l
  theta : thetaOf (M.h pub) (flEv ρ l) = ρ.val M.theta
  nums : forN (M.h pub) lm F.next (flEv ρ l) = numsF (M.h pub) lm F.next (ρ.val M.theta)
  trace : forTrace (M.h pub) lm F.next (flEv ρ l) =
    ⟨ρ.val M.alpha, scs, rdA ρ ptT, lvK,
      tgTop (tK (tieTrace (ρ.val M.alpha) scs (rdA ρ ptT))) lvK.reverse, lvT,
      D.cls ρ (5 + (M.h pub).d) (M.h pub).d M.table.rho M.table.form M.F7.next, rdA ρ D.ptZ,
      D.bitsSc ρ (5 + (M.h pub).d) (M.h pub).d M.table.rho M.F7.next⟩
  fac : ρ.val M.a = fac (numsF (M.h pub) lm F.next (ρ.val M.theta)) (ρ.val M.alpha)
  f4 : M.F4 = owed3 F
  tieSt : Stretch M.F4 M.F5 (tieOff 31)
  tieLater : Later M.F4 M.F5
  scsLen : scs.length = 31
  tieN : M.t.rows.size = 31
  tieRows : ∀ i, i < 31 → RowIs ρ M.F5 (M.t.rows.getD i {})
    ((tieRowsR (numsF (M.h pub) lm F.next (ρ.val M.theta)) (ρ.val M.alpha)
      scs.reverse).reverse.getD i ⟨[], 0⟩)
  keys : Walked ρ (ordK (M.h pub)) (fun l => ledF F.next ((S (M.h pub)).pKeyC l)) 0 (M.h pub).v 0
    { rows := M.t.rows, rho := #[], form := Aff.slot M.t.sZ } M.keys M.F5 M.F6 M.c5 M.c6 []
    (tK (tieTrace (ρ.val M.alpha) scs (rdA ρ ptT)))
    (fK (numsF (M.h pub) lm F.next (ρ.val M.theta)) (tieTrace (ρ.val M.alpha) scs (rdA ρ ptT)))
    evK lvK rowsK
  table : Walked ρ ordT (fun l => ledF F.next ((S (M.h pub)).pTabC l)) 5 (M.h pub).d 0
    { rows := M.keys.rows, rho := M.t.rhoT, form := M.t.cT } M.table M.F6 M.F7 M.c6 M.c7
    (rdA ρ ptT)
    (tgT0 (numsF (M.h pub) lm F.next (ρ.val M.theta)) (tieTrace (ρ.val M.alpha) scs (rdA ρ ptT)))
    (incT0 (numsF (M.h pub) lm F.next (ρ.val M.theta))
      (tieTrace (ρ.val M.alpha) scs (rdA ρ ptT)))
    evT lvT rowsT
  next7 : M.F7.next = F.next + (S (M.h pub)).fEnd
  r5 : R5Is ρ (numsF (M.h pub) lm F.next (ρ.val M.theta)) (5 + (M.h pub).d) (M.h pub).d M.table.rho
    M.table.form (pntTop (fun i => ordT (0 + i)) (rdA ρ ptT) lvT.reverse) M.F7 M.G8 M.c7 M.d8 M.lv
    M.zb0 M.zb1 M.sBit M.row D
  bitRow : ∀ t : Trace K,
    t.bits = D.bitsSc ρ (5 + (M.h pub).d) (M.h pub).d M.table.rho M.F7.next →
    RowIs ρ M.G8 M.row (rowBitU (numsF (M.h pub) lm F.next (ρ.val M.theta)) t)
  sBit : M.sBit = slotNo ((numsF (M.h pub) lm F.next (ρ.val M.theta)).ledB.sh 0)
  sBitAt : FormIs ρ M.G8 (Aff.slot M.sBit)
    ((D.bitsSc ρ (5 + (M.h pub).d) (M.h pub).d M.table.rho M.F7.next).v 0)
    [(Pl.mask M.sBit, (D.bitsSc ρ (5 + (M.h pub).d) (M.h pub).d M.table.rho M.F7.next).be)]
  lvDg : (zdL (5 + (M.h pub).d) (M.h pub).d M.table.rho).map (fun p => p.2) =
    (dgE (numsF (M.h pub) lm F.next (ρ.val M.theta))).map (· + 1)

/-- A context behind a row of rounds on a view has no message open. -/
theorem clean_of {l : List Ev} {c c' : Tape} (hl : Rds l) (hc : Clean c) (h : Evs l c c') :
    Clean c' := by
  obtain ⟨_, ht, _⟩ := rds_took Reading.gl hl hc h
  exact ht.2.1

/-- The fresh point between the leaves and the bits has as many coordinates as were asked for. -/
theorem point_size {C : Aff} {zs : List (OnBytes.E × ℕ)} {m : ℕ} {F F1 F2 F3 : Fork}
    {c c1 c2 c3 : Tape} {lv0 lv : Psc} {zb0 z : Array OnBytes.E} (hc : Clean c)
    (h1 : Fl.pscBegin C F c = .ok ((lv0, F1), c1))
    (h2 : Fl.roundsIn .eq lv0 zs F1 c1 = .ok (((zb0, lv), F2), c2))
    (h3 : Fl.point .zero m F2 c2 = .ok ((z, F3), c3)) : z.size = m := by
  obtain ⟨target, mu, eps, _, e1, _, rfl⟩ := pscBegin_ok C F F1 c c1 lv0 h1
  have c1c : Clean c1 := clean_of (.sum mu .pscEpsilon eps .nil) hc e1
  obtain ⟨ns, _, _, e2, _⟩ :=
    ran_roundsIn eqForm_eq (ran_begin C target mu eps F.next) zs F1 F2 c1 c2 zb0 lv h2
  obtain ⟨_, t2, _⟩ := evRounds_took ns c1 c2 c1c e2
  obtain ⟨e3, _⟩ := (point_ok _ _ _ _ _ _ _).1 h3
  obtain ⟨_, _, _, _, hs⟩ := round_point _ _ _ _ _ t2.2.1 e3
  exact hs

/-- Every run on a view that returns, with lawful public numbers. -/
theorem pad_read {calls : Array Call} {pub : Array Nat} {lid : ℕ} {F F' : Fork} {c c' : Tape}
    {g : Forest.Heard} {M : PadMid} (P : PadCut calls pub lid F c g F' c' M) (hF : Sized F)
    (hc : Clean c) (lm : ℕ) (H : FoNums.ok (M.h pub) = true) :
    ∃ l scs ptT lvK lvT rowsK rowsT evK evT D,
      PadRead ρ lm pub F c c' M l scs ptT lvK lvT rowsK rowsT evK evT D := by
  obtain ⟨e4, evD, hz, ha⟩ := head_cut P
  have hS4 : Sized M.F4 := e4 ▸ owed3_sized hF
  have hn4 : M.F4.next = F.next := by rw [e4]; rfl
  have hfac : ρ.val M.a = fac (numsF (M.h pub) lm M.F4.next (ρ.val M.theta)) (ρ.val M.alpha) := by
    rw [ha, hn4]
    exact head_fac ρ (M.h pub) H lm F.next _ _
  have c4c : Clean M.c4 := clean_of (drawsEv_rds _ _ _) hc evD
  obtain ⟨lT, scs, c1, ptT, eT1, rT, eT2, hTie, lat45, hS5, same45, _, nT, rowsT0, _, fZ, rhoT,
      fcT⟩ :=
    tie_nums ρ (M.h pub) lm (ρ.val M.theta) (ρ.val M.alpha) M.a M.F4 M.F5 M.c4 M.c5 hfac hS4 M.t
      P.tie
  have h5 : ptT.size = 5 := point_five c4c eT1 rT eT2
  have st45 := fcT.2.1
  have fcT := fcT.1 h5
  rw [hn4] at hfac rowsT0 fZ fcT
  have evT' : Evs (lT ++ [.point .lkpPlanes 5 ptT]) M.c4 M.c5 := eT1.append eT2
  have rT' : Rds (lT ++ [.point .lkpPlanes 5 ptT]) := rT.append (.point _ _ _ .nil)
  have hd : 10 ≤ (M.h pub).dT := (Cb.Fo.ok_parts H).1.1
  have hn5 : M.F5.next = F.next + (S (M.h pub)).fKey 0 := by
    rw [same45.next]
    show M.F4.next + tieOff 31 = _
    rw [hn4, first_key0, fTie_off (M.h pub) 31 (le_refl _)]
  obtain ⟨evK, lvK, rowsK, WK⟩ := keys_descent ρ (levelLaw ρ) (M.h pub) hd
    (fun l => ledF F.next ((S (M.h pub)).pKeyC l)) _ M.keys M.F5 M.F6 M.c5 M.c6 _ _ P.keys hS5 rfl
    fZ (hn5 ▸ leds_key (M.h pub) F.next)
  have hn6 : M.F6.next = F.next + (S (M.h pub)).fTab 0 := by
    rw [WK.same.next]
    show M.F5.next + walkSlots 0 (M.h pub).v 0 = _
    have := key_slots (M.h pub) (M.h pub).v 0 (by omega)
    rw [Nat.zero_add] at this
    rw [hn5, first_tab0, this, Nat.add_assoc]
  obtain ⟨evT, lvT, rowsT, WT⟩ := table_descent ρ (levelLaw ρ) (M.h pub)
    (fun l => ledF F.next ((S (M.h pub)).pTabC l)) _ M.table M.F6 M.F7 M.c6 M.c7 (rdA ρ ptT) _ _
    P.table WK.sized (by simp [rdA, h5]) rhoT (fcT.later ρ WK.later)
    (hn6 ▸ leds_tab (M.h pub) F.next)
  have hn7 : M.F7.next = F.next + (S (M.h pub)).fEnd := by
    rw [WT.same.next]
    show M.F6.next + walkSlots 5 (M.h pub).d 0 = _
    have := tab_slots (M.h pub) (M.h pub).d 0 (by omega)
    rw [Nat.zero_add] at this
    rw [hn6, first_end, this, Nat.add_assoc]
  have c5c : Clean M.c5 := clean_of rT' c4c evT'
  have c6c : Clean M.c6 := clean_of WK.rds c5c WK.evs
  have c7c : Clean M.c7 := clean_of WT.rds c6c WT.evs
  have hzs : M.pt.size = 5 + (M.h pub).d := point_size c7c P.l1 P.l2 P.l3
  obtain ⟨D, hD, R, rowB, sB, _, sAt, hdg, _⟩ := r5_at ρ (M.h pub) lm F.next (ρ.val M.theta)
      M.table.rho
    M.table.form (pntTop (fun i => ordT (0 + i)) (rdA ρ ptT) lvT.reverse) WT.rho P.size M.F7 M.G1
    M.G2 M.G3 M.G4 M.G5 M.G6 M.G7 M.G8 M.c7 M.d1 M.d2 M.d3 M.d4 M.d5 M.d6 M.d7 M.d8 M.lv0 M.lv M.b0
    M.b1 M.b2 M.b3 M.zb0 M.zb1 M.pt M.sBit M.vBit M.row WT.sized hzs hn7 P.l1 P.l2 P.l3 P.l4 P.l5
    P.l6 P.l7 P.l8
  have htg : ρ.val D.tgL = tgTop (tgT0 (numsF (M.h pub) lm F.next (ρ.val M.theta))
      (tieTrace (ρ.val M.alpha) scs (rdA ρ ptT))) lvT.reverse :=
    (WT.form M.F7 (Later.refl _)).1 D.tgL R.target
  have hfl : flEv ρ (drawsEv (M.h pub) M.theta M.alpha ++ ((lT ++ [.point .lkpPlanes 5 ptT]) ++
      (evK ++ (evT ++ D.evs (5 + (M.h pub).d) (M.h pub).d M.table.rho)))) =
      shiftRd (M.h pub) (ρ.val M.theta) ++ ([], [ρ.val M.alpha]) ::
        (flEv ρ (lT ++ [.point .lkpPlanes 5 ptT]) ++ (flEv ρ evK ++ (flEv ρ evT ++
          flEv ρ (D.evs (5 + (M.h pub).d) (M.h pub).d M.table.rho ++ [])))) := by
    rw [flEv_app ρ ((drawsEv_rds _ _ _).closed ρ), flEv_app ρ (rT'.closed ρ),
      flEv_app ρ WK.closed, flEv_app ρ WT.closed, draws_shift, List.append_nil,
      List.append_assoc]
    rfl
  have hsh := shiftOf_read ρ (M.h pub) M.theta hz
  have hv : (numsF (M.h pub) lm F.next (ρ.val M.theta)).v' + 1 = (M.h pub).v :=
    (Cb.Fo.ok_v H).symm
  refine ⟨_, scs, ptT, lvK, lvT, rowsK, rowsT, evK, evT, D,
    { evs := P.ctx ▸ evD.append (evT'.append (WK.evs.append (WT.evs.append R.evs)))
      rds := (drawsEv_rds _ _ _).append (rT'.append (WK.rds.append (WT.rds.append R.rds)))
      theta := by rw [hfl, theta_of, hsh]
      nums := by rw [hfl, forN_of, hsh]
      trace := ?_
      fac := hfac
      f4 := e4
      tieSt := st45
      tieLater := lat45
      scsLen := by
        have := tieGo_len 31 0 0 (flEv ρ (lT ++ [.point .lkpPlanes 5 ptT]) ++ [])
        rw [hTie] at this
        exact this
      tieN := nT
      tieRows := rowsT0
      keys := WK
      table := WT
      next7 := hn7
      r5 := R
      bitRow := rowB
      sBit := sB
      sBitAt := sAt
      lvDg := hdg }⟩
  rw [hfl]
  refine forTrace_of (M.h pub) lm F.next (ρ.val M.theta) (ρ.val M.alpha) _
    (flEv ρ evK ++ (flEv ρ evT ++
      flEv ρ (D.evs (5 + (M.h pub).d) (M.h pub).d M.table.rho ++ [])))
    (flEv ρ evT ++ flEv ρ (D.evs (5 + (M.h pub).d) (M.h pub).d M.table.rho ++ []))
    (flEv ρ (D.evs (5 + (M.h pub).d) (M.h pub).d M.table.rho ++ []))
    (flH ρ D.muB D.epsB D.rsB' (some D.v.toList) ++ flEv ρ []) (flEv ρ []) scs
    (rdA ρ ptT) lvK _ (pntTop (fun i => ordK (M.h pub) (0 + i)) [] lvK.reverse) lvT
    (tgTop (tgT0 (numsF (M.h pub) lm F.next (ρ.val M.theta))
      (tieTrace (ρ.val M.alpha) scs (rdA ρ ptT))) lvT.reverse)
    (pntTop (fun i => ordT (0 + i)) (rdA ρ ptT) lvT.reverse) _ _ _ ?_ ?_ ?_ ?_ ?_
  · rw [hsh]
    exact hTie _
  · rw [hsh, hv]
    exact WK.flat _
  · rw [hsh]
    exact WT.flat _
  · rw [hsh, ← htg]
    exact R.h4 []
  · rw [hsh]
    exact R.h5 _

end

end Fo.Tp
