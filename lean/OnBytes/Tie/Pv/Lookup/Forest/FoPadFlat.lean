-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoPadFlat.lean.
A run of the byte-level lookup routine, read as the flat function's trace.

OnBytes/Tie/Pv/Lookup/Forest/FoPadCut.lean cuts a run of Forest.pad that returns into the runs of
the routines that it calls.
Each
stretch is read elsewhere: the draws (OnBytes/Tie/Pv/Lookup/Forest/FoHead.lean), the tie
(OnBytes/Tie/Pv/Lookup/Forest/FoTieNums.lean), the two walks
(OnBytes/Tie/Pv/Lookup/Forest/FoDescent.lean, on OnBytes/Tie/Pv/Lookup/Forest/FoLevelLaw.lean), the
leaves and the bits (OnBytes/Tie/Pv/Lookup/Forest/FoR5At.lean). Here they are put
together.

* `key_slots`, `tab_slots`: the first slots of the levels, from the slots that a walk takes.
* `PadRead`: what the stretches give together, for named calls, steps and levels.
* `pad_read`: on a view with no message open (`Clean c`), from a state whose arrays have their sizes
(`Sized F`), with lawful public numbers, every run that returns has it: calls of the channel's
routines that lead from the context before the run to the one after it (`Evs l c c'`)
  are a row of rounds; on these calls read as plain data the flat function's trace is the record of
  the stretches' values, and its public numbers are those at the shift read.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPadCut
import OnBytes.Tie.Pv.Lookup.Forest.FoHead
import OnBytes.Tie.Pv.Lookup.Forest.FoTieNums
import OnBytes.Tie.Pv.Lookup.Forest.FoDescent
import OnBytes.Tie.Pv.Lookup.Forest.FoLevelLaw
import OnBytes.Tie.Pv.Lookup.Forest.FoR5At
import OnBytes.Tie.Pv.Lookup.Forest.FoTraceOf
import OnBytes.Tie.Pv.Lookup.Forest.FoRds
import OnBytes.Tie.Pv.Lookup.Port.FoShape

set_option autoImplicit false

namespace Fo
open TwV FoNums OnBytes OnBytes.Model OnBytes.PscRun OnBytes.PscTie Cb.Fo.Walk

theorem key_slots (h : Sh) : ∀ n l, l + n ≤ h.v →
    (S h).fKey (l + n) = (S h).fKey l + walkSlots 0 n l
  | 0, _, _ => rfl
  | n + 1, l, hl => by
    have e := key_slots h n (l + 1) (by omega)
    have f := first_key h l (by omega)
    show (S h).fKey (l + (n + 1)) = (S h).fKey l + ((1 + 2 * (0 + l) + 4) + walkSlots 0 n (l + 1))
    rw [show l + (n + 1) = l + 1 + n by omega, e, f]
    simp only [layerSlots, sumcheckSlots, roundValues]
    omega

theorem tab_slots (h : Sh) : ∀ n l, l + n ≤ h.d →
    (S h).fTab (l + n) = (S h).fTab l + walkSlots 5 n l
  | 0, _, _ => rfl
  | n + 1, l, hl => by
    have e := tab_slots h n (l + 1) (by omega)
    have f := first_tab h l (by omega)
    show (S h).fTab (l + (n + 1)) = (S h).fTab l + ((1 + 2 * (5 + l) + 4) + walkSlots 5 n (l + 1))
    rw [show l + (n + 1) = l + 1 + n by omega, e, f]
    simp only [layerSlots, sumcheckSlots, roundValues]
    omega

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The shift's round, from the calls of the draws. -/
theorem draws_shift (h : Sh) (θ α : OnBytes.E) :
    flEv ρ (drawsEv h θ α) = shiftRd h (ρ.val θ) ++ [([], [ρ.val α])] := by
  rw [draws_fl]
  unfold shiftRd several
  by_cases hN : h.NC > 1
  · rw [if_pos hN, if_pos (decide_eq_true hN)]
  · rw [if_neg hN, if_neg (by simpa using hN)]

theorem shiftOf_read (h : Sh) (θ : OnBytes.E) (hz : ¬ h.NC > 1 → θ = zeroE) :
    shiftOf h (ρ.val θ) = ρ.val θ := by
  unfold shiftOf several
  by_cases hN : h.NC > 1
  · rw [if_pos (decide_eq_true hN)]
  · rw [if_neg (by simpa using hN), hz hN, ρ.zero]

/-- What the stretches of a run give together. -/
structure PadRead (lm : ℕ) (pub : Array Nat) (F : Fork) (c c' : Ctx) (M : PadMid) (l : List Ev)
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
theorem clean_of {l : List Ev} {c c' : Ctx} (hl : Rds l) (hc : Clean c) (h : Evs l c c') :
    Clean c' := by
  obtain ⟨_, ht, _⟩ := rds_took Reading.gl hl hc h
  exact ht.2.1

/-- The fresh point between the leaves and the bits has as many coordinates as were asked for. -/
theorem point_size {C : Aff} {zs : List (OnBytes.E × ℕ)} {m : ℕ} {F F1 F2 F3 : Fork}
    {c c1 c2 c3 : Ctx} {lv0 lv : Psc} {zb0 z : Array OnBytes.E} (hc : Clean c)
    (h1 : pscBegin C F c = .ok ((lv0, F1), c1))
    (h2 : roundsIn .eq lv0 zs F1 c1 = .ok (((zb0, lv), F2), c2))
    (h3 : SubM.point .zero m F2 c2 = .ok ((z, F3), c3)) : z.size = m := by
  obtain ⟨target, mu, eps, _, e1, _, rfl⟩ := pscBegin_ok C F F1 c c1 lv0 h1
  have c1c : Clean c1 := clean_of (.sum mu .pscEpsilon eps .nil) hc e1
  obtain ⟨ns, _, _, e2, _⟩ :=
    ran_roundsIn eqForm_eq (ran_begin C target mu eps F.next) zs F1 F2 c1 c2 zb0 lv h2
  obtain ⟨_, t2, _⟩ := evRounds_took ns c1 c2 c1c e2
  obtain ⟨e3, _⟩ := (point_ok _ _ _ _ _ _ _).1 h3
  obtain ⟨_, _, _, _, hs⟩ := round_point _ _ _ _ _ t2.2.1 e3
  exact hs

/-- Every run on a view that returns, with lawful public numbers. -/
theorem pad_read {calls : Array Call} {pub : Array Nat} {lid : ℕ} {F F' : Fork} {c c' : Ctx}
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
end Fo
