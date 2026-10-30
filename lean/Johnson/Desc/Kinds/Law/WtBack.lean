-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/WtBack.lean: THE TWO SENTENCES ON THE CLAIM ON THE COMMITTED WEIGHTS AT THE
OUTPUT HEAD, THE WAY BACK: from wtK6 (Law/WtK6.lean) to the merge's sentence wtP1
(Johnson/Top/H0/Fill/FillP1.lean), at the verifier's state in front of the merge.
LIMITS, FIRST. THE REFERENCE SIZES ALONE (V = 202048, d = 5120, lamS = 13, segment 24, the reference
layout): at a smaller size no values can meet the premises. THAT THE CONDITION ON THE STATE (WaSeat)
HOLDS AT ANY STATE IS NOT SHOWN HERE; in it lie the two ties of the top digit's key (LeftTies).
Statements that end in WaK6 and in WaSeat stand in Johnson/P4R/WaK6AtRchAt.lean and
Johnson/K11R/WaSeatAtMg.lean: this file calls neither. THAT A CLAIM LIES AT SUCH A STATE (hcl) IS
NOT SHOWN HERE. A statement that ends in it, with ho, hx, hu and hsv, is reads_of_yes
(Johnson/Top/H0/MergeLaw/OffRecord.lean): it starts from the merge's own accept at that state, so it
does not serve who wants the equation in front of that accept; this file does not call it. On the
step behind the digits' lookup, digits_345 (Johnson/P4R/WaK6At346.lean) has the clause "if a claim
lies behind it, it is weightsClaim's return", not that one lies there. No values are shown at which
the premises hold together. No draw, no error term. Nothing on soundness, on
completeness or on what a proof hides.
WHAT IT IS. Johnson/Desc/Kinds/Law/WtJointAt.lean (wtK6_of_wtP1) and
Johnson/Top/H0/MergeLaw/WtJoinsSeat.lean (wtK6_of_wtP1_seat) lead from wtP1 to wtK6. Each joint of
that way is an equation or holds both ways; here the three theorems that put the joints together
are written the other way. Called, not proved again: weightTrue_says (Law/WeightTwin.lean),
weightAt_keptFo (Law/WeightAtFo.lean), behind_all, twinTies_heardOf, reads_as_Hof
(Law/WeightTwinAt.lean), hOn_at (Law/WeightJoint.lean), claimVal_cellsIn, rd_atWorld_hidden,
rd_atWorld_slot (Law/WtJoint.lean), weightsClaim_head (Johnson/Top/H0/K11Caller/HeadClaim.lean),
maskRows_one (Law/MaskRowsOne.lean), maskRowAt_of_part (Johnson/Desc/Sound/MaskRowAt.lean).
  Came.says_of_weightAt    weightAt_at_quiet's last arrow, turned: WeightAt behind the output head's
                           sub-protocol gives: the hidden value under the slot x.sV reads as the
                           laid claim's sum over the index's digit matrix.
  Came.plain_of_weightAt   weightAt_of_wtP1, turned: the same over the cells within the committed
                           table, and the hidden value written out at the later ledger.
  plain_of_wtK6            THE EQUATION THAT THE MERGE SPENDS: at a state with WaSeat that holds a
                           claim and what the head heard, at a witness whose cells hold an index:
                           wtK6 gives: the claim's value at the witness's cells is what was shown at
                           the slot x.sV less the factor there times the mask row's entry there.
  forms_of_wtK6            the same with the two sides in the merge's order and the mask row as the
                           table's forms read it (Sound.dataQ, at the open segment's part).
  wtP1_of_wtK6_seat        the same as the sentence wtP1.
  wtK6_iff_wtP1_seat       both ways, with wtK6_of_wtP1_seat.
WHAT THE WAY BACK ASKS BEYOND wtK6_of_wtP1_seat's OWN PREMISES, and why. (1) hR: the witness's cells
hold an index: without it wtK6 holds idly and gives nothing. (2) ho, hcl, hx: the state stands in
the head's part and HOLDS A CLAIM and what the head heard: WaK6 says only what a claim is IF one
lies there; wtP1 says that one lies there. (By reading, ho and hx could be had from WaK6; they stand
as premises so that o and x have names. hcl could not.) (3) For wtP1 alone, the clauses that stand
in it under "there are": hn: 2 lk + 3 ≤ nMsg; hu: the claim's unit is one of the layout's; hsv: the
slot is below the merge's number of slots; hni: the index masks' message has an entry.
The closure of this file's imports holds 22 modules under Johnson/Goal/ (counted by a program over
the import lines, comments stripped). One definition of theirs is named here: Meaning.sizesOf
(Johnson/Goal/Meaning/HidPlan.lean), in two steps of plain_of_wtK6's proof, where compCut's
arguments are written out as wtK6's own text has them. No statement of this file names it.

-/
import Johnson.Top.H0.MergeLaw.WtJoinsSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE okE)
open OnBytes.Model (Reading eqTab Fork)
open OnBytes.Road (eqR claimVal Wm)
open OnBytes.Road.Hd (avOf facKK)
open Norm (lt ls d lPd T S2)
open Inst.Model (ppref)
open Inst.Model.Layout (kRef)
open Inst.Model.Head (Hof nV nD)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.First.K11Caller (headClaim cellsIn ewAt)

namespace Came

/-- **From WeightAt behind the output head's sub-protocol to the sum of the claim that the quiet
step makes.** s, s': the states in front of and behind that sub-protocol; sQ: a state that holds
what the head heard as s' does. The letters and the premises are weightAt_at_quiet's
(Law/WeightJoint.lean); its last arrow is turned.
WHAT IT IS NOT: the reference sizes alone; LeftTies is a premise; no property of the protocol. -/
theorem says_of_weightAt (W : OnBytes.Model.Verify.Public) (l : Nat) {s s' sQ : S}
    {rv : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hd : (blockAt W.hS (readsOf W) (workOf W) l).decide s rv gs = .ok s')
    (hWL : WellLaid ((seatAt W.hS (readsOf W)).ledger s)) (hcan : Canonical rv)
    (hplan : (parOf W.hS (workOf W)).ok = true) (hst : SameHeard s' sQ) (hTT : W.T = W.hS.T)
    {V' : Nat} {cov : OnBytes.Model.Head.Covered} (hcov : sQ.covered W.T V' = .ok cov)
    {rows cols : Nat} (hr : rows ≤ Inst.Model.Layout.hRef) (hc : cols ≤ 2 ^ kRef)
    {M : Fin rows → Fin cols → VerifiableInference.OnPublicFiles.Flat.GE} {i : Cm.Idx}
    (hH : VerifiableInference.OnPublicFiles.Flat.Holds M i) :
    ∃ (g : Given) (H : HeardAll) (F1 : Fork) (a : HeadOwn) (gk : OnBytes.Model.Forest.Heard)
      (o' : HeadOwn),
      given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s = .ok g ∧
      hear ((seatAt W.hS (readsOf W)).ledger s) rv = some (H, F1, []) ∧
      s.here = .head a ∧ a.lookHeard = some gk ∧
      sQ.here = .head o' ∧ o'.x = some (heardOf gk H) ∧
      (seatAt W.hS (readsOf W)).ledger s' = F1 ∧
      ∀ (t : OnBytes.Model.Head.Tables)
        {sh : OnBytes.Model.WsShape} (_ : OnBytes.Road.SizedW sh ppref)
        (_ : OnBytes.Model.wsLayOf sh true kRef = .ok W.layers.wsLay) (_ : W.H.lamS = 13)
        {claim : OnBytes.Model.WsClaim}
        (_ : First.Look.weightsClaim (runAt W cov (heardOf gk H) t) W.layers.wsLay = .ok claim),
        ∃ q sg, OnBytes.Model.Head.callNo W.HLy "HD0" = some q ∧
          (W.HLy.calls.getD q default).seg? "HD0" = some sg ∧
          claim = headClaim W.layers.wsLay
            (avOf (runAt W cov (heardOf gk H) t) (ewAt (runAt W cov (heardOf gk H) t) q sg))
            (heardOf gk H).rs ∧
          (LeftTies W g cov (heardOf gk H) t (ewAt (runAt W cov (heardOf gk H) t) q sg) →
            ∀ c : Cells, c.Wh = whOf M → V = nV → d = nD → ∀ mask : Nat → E,
              WeightAt W s' c mask →
              rd (atWorld F1 mask noEnt (OnBytes.Model.Aff.slot (heardOf gk H).sV)) =
                claimVal Reading.gl W.layers.wsLay (fun r c' => ((i.mat r c' : Int) : K))
                  claim) := by
  obtain ⟨g, H, F1, a, gk, Q, hg, hh, ha, hgk, hs', hg', hH', eF, _, hv⟩ :=
    behind_all W l hd hWL hcan
  obtain ⟨o', ho', _, ex, _⟩ := hst.head _ (by rw [hs'])
  have hreq : sQ.req = s.req := by
    rw [hst.req, hs']
  refine ⟨g, H, F1, a, gk, o', hg, hh, ha, hgk, ho', ex, eF,
    fun t sh Z hl hlam claim hk => ?_⟩
  obtain ⟨q, sg, hq, hsg, hcl, _⟩ := First.K11Caller.weightsClaim_head Z hl hk hlam
  refine ⟨q, sg, hq, hsg, hcl, fun hL c hWh hV hd' mask hwt => ?_⟩
  obtain ⟨l2, l3⟩ := hL
  have l1 := zt_size_at W hg hplan
  obtain ⟨hT, hV'⟩ := runAt_sizes W hg cov (heardOf gk H) t
  have hOn := hOn_at W hg hTT hcov hreq
  obtain ⟨g2, H2, e1, e2, hw⟩ := hwt
  obtain rfl : g = g2 := Except.ok.inj (hg'.symm.trans e1)
  obtain rfl : H = H2 := Option.some.inj (hH'.symm.trans e2)
  rw [eF] at hw
  letI : Heard := H.2.2
  have hrH : (rH : Point).size = lt := rH_size hWL hh l1
  have hrs : (rs : Point).size = 13 := (rs_size hWL hh l1).trans (lPd_ref hd')
  have hv' : (logits.end_ 1).var = OnBytes.Model.Aff.slot (heardOf gk H).sV := hv
  have key := weightTrue_says
    (twinTies_heardOf gk H (runAt W cov (heardOf gk H) t) _ rfl hT hV' hOn hrH l2 l3) Z hl
    (fun r c' => ((i.mat r c' : Int) : K)) c hV hd' hrs
    (fun k v hk hv2 => reads_as_Hof hr hc hH hWh (hd' ▸ hk) (hV ▸ hv2)) F1 mask noEnt hw
  rw [hv'] at key
  rw [hcl]
  exact key

/-- **From WeightAt behind the output head's sub-protocol to the merge's equation at a later
state.** sF: the state in front of the merge. Pl: a place whose layout is the public parameters';
cell: a reader of cells that gives the index's digits. The letters and the premises are
weightAt_of_wtP1's (Law/WtJoint.lean), but for the sentence wtP1 and the merge's reader of the mask
row: the mask row stays the letter mask.
WHAT IT IS NOT: as says_of_weightAt; that the hidden value under the slot is the same at both
ledgers is a premise here. -/
theorem plain_of_weightAt (W : OnBytes.Model.Verify.Public) (l : Nat) {s s' sF : S}
    {rv : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hd : (blockAt W.hS (readsOf W) (workOf W) l).decide s rv gs = .ok s')
    (hWL : WellLaid ((seatAt W.hS (readsOf W)).ledger s)) (hcan : Canonical rv)
    (hplan : (parOf W.hS (workOf W)).ok = true) (hst : SameHeard s' sF) (hTT : W.T = W.hS.T)
    {V' : Nat} {cov : OnBytes.Model.Head.Covered} (hcov : sF.covered W.T V' = .ok cov)
    {rows cols : Nat} (hr : rows ≤ Inst.Model.Layout.hRef) (hc : cols ≤ 2 ^ kRef)
    {M : Fin rows → Fin cols → VerifiableInference.OnPublicFiles.Flat.GE} {i : Cm.Idx}
    (hH : VerifiableInference.OnPublicFiles.Flat.Holds M i)
    (Pl : First.K11Caller.Place) (hlay : Pl.lay = W.layers.wsLay)
    (cell : ℕ → ℕ → K) (hcell : ∀ r c, cell r c = ((i.mat r c : Int) : K)) :
    ∃ (g : Given) (H : HeardAll) (F1 : Fork) (a : HeadOwn) (gk : OnBytes.Model.Forest.Heard)
      (o' : HeadOwn),
      given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s = .ok g ∧
      hear ((seatAt W.hS (readsOf W)).ledger s) rv = some (H, F1, []) ∧
      s.here = .head a ∧ a.lookHeard = some gk ∧
      sF.here = .head o' ∧ o'.x = some (heardOf gk H) ∧
      (seatAt W.hS (readsOf W)).ledger s' = F1 ∧
      ∀ (t : OnBytes.Model.Head.Tables)
        {sh : OnBytes.Model.WsShape} (_ : OnBytes.Road.SizedW sh ppref)
        (_ : OnBytes.Model.wsLayOf sh true kRef = .ok W.layers.wsLay) (_ : W.H.lamS = 13)
        {claim : OnBytes.Model.WsClaim}
        (_ : First.Look.weightsClaim (runAt W cov (heardOf gk H) t) W.layers.wsLay = .ok claim),
        ∃ q sg, OnBytes.Model.Head.callNo W.HLy "HD0" = some q ∧
          (W.HLy.calls.getD q default).seg? "HD0" = some sg ∧
          (LeftTies W g cov (heardOf gk H) t (ewAt (runAt W cov (heardOf gk H) t) q sg) →
            ∀ c : Cells, c.Wh = whOf M → V = nV → d = nD → ∀ mask : Nat → E,
              hidden F1 mask (heardOf gk H).sV = hidden o'.F mask (heardOf gk H).sV →
              WeightAt W s' c mask →
              claimVal Reading.gl W.layers.wsLay (cellsIn Pl cell) claim =
                rd (o'.F.vp.getD (heardOf gk H).sV 0) -
                  rd (o'.F.mf.getD (heardOf gk H).sV 0) * rd (mask (heardOf gk H).sV)) := by
  obtain ⟨g, H, F1, a, gk, o', p1, p2, p3, p4, p5, p6, p7, J⟩ :=
    says_of_weightAt W l hd hWL hcan hplan hst hTT hcov hr hc hH
  refine ⟨g, H, F1, a, gk, o', p1, p2, p3, p4, p5, p6, p7, fun t sh Z hl hlam claim hk => ?_⟩
  obtain ⟨q, sg, hq, hsg, hcl, J2⟩ := J t Z hl hlam hk
  refine ⟨q, sg, hq, hsg, fun hL c hWh hV hd' mask hhid hwt => ?_⟩
  have hsays := J2 hL c hWh hV hd' mask hwt
  have hs : 13 ≤ (heardOf gk H).rs.size := by
    have e := (rs_size hWL p2 (zt_size_at W p1 hplan)).trans (lPd_ref hd')
    show 13 ≤ ((H.2.2.logits.r.extract lt (lt + lPd)).reverse).size
    rw [Array.size_reverse]
    exact Nat.le_of_eq e.symm
  have hlP : OnBytes.Model.wsLayOf sh true kRef = .ok Pl.lay := by
    rw [hlay]
    exact hl
  have hcv := claimVal_cellsIn Z Pl hlP cell i hcell
    (avOf (runAt W cov (heardOf gk H) t) (ewAt (runAt W cov (heardOf gk H) t) q sg))
    (heardOf gk H).rs hs
  have hcl' : claim = headClaim Pl.lay
      (avOf (runAt W cov (heardOf gk H) t) (ewAt (runAt W cov (heardOf gk H) t) q sg))
      (heardOf gk H).rs := by
    rw [hlay]
    exact hcl
  rw [← hcl', hlay] at hcv
  rw [hcv, ← hsays, rd_atWorld_hidden, hhid]
  exact (rd_atWorld_hidden _ _ _).symm.trans (rd_atWorld_slot _ _ _)

end Came

end VerifiableInference.Desc.Kinds.Head.Law

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes (E zeroE)
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open OnBytes.Params (ReqLayout)
open OnBytes.Model (Fork Reading)
open OnBytes.Road (claimVal)
open Inst.Model (ppref)
open Inst.Model.Layout (kRef)
open Inst.Model.Head (nV nD)
open VerifiableInference.OnPublicFiles.Flat (GE InRange Holds)
open VerifiableInference.Desc.First (S HeadOwn Numbers)
open VerifiableInference.Desc.First.K11Caller (ewAt cellsIn)
open VerifiableInference.Desc.First.FillP1 (wtP1 wtAt)
open VerifiableInference.Desc.First.MergeLaw (planPlace frontIn)
open VerifiableInference.Desc.Sound (Mem MsgT namedOnce)
open Johnson.Desc.First.ForkMerge (HeadMergeP)

section
variable {rows cols : ℕ} {P Tok : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (msR : List Mem)
  (N : Numbers) (W : OnBytes.Model.Verify.Public) (lay6 : ReqLayout) (num : ℕ → ℕ → ℕ) (n rb : ℕ)

/-- **THE EQUATION THAT THE MERGE SPENDS, FROM wtK6.** At the state a.2, which meets WaSeat, stands
in the head's part and holds a claim and what the head heard (x), and at a witness whose cells hold
an index: the claim's value at the witness's cells, cut to the committed table at a place Pl of the
public parameters' layout, is what was shown at the slot x.sV, less the factor there times the mask
row's entry there, the mask row read by Sound.maskRowAt.
WHAT IT IS NOT: the reference sizes alone. That WaSeat holds at a state, or that a claim lies there,
is not shown here. No values are shown at which the premises hold together. No property of the
protocol. -/
theorem plain_of_wtK6 (hplan : (parOf W.hS (workOf W)).ok = true) (hTT : W.T = W.hS.T)
    (V' : ℕ) (hr : rows ≤ Inst.Model.Layout.hRef) (hc : cols ≤ 2 ^ kRef)
    (Pl : First.K11Caller.Place) (hPl : Pl.lay = W.layers.wsLay)
    (cellOf : Wit (Fin rows → Fin cols → GE) Tok MsgT → ℕ → ℕ → K)
    (hcellOf : ∀ w r c, cellOf w r c =
      if h : r < rows ∧ c < cols then w.cells ⟨r, h.1⟩ ⟨c, h.2⟩ else 0)
    (h1 : namedOnce arr N 24 n = true)
    {sh : OnBytes.Model.WsShape} (Z : OnBytes.Road.SizedW sh ppref)
    (hl : OnBytes.Model.wsLayOf sh true kRef = .ok W.layers.wsLay) (hlam : W.H.lamS = 13)
    (hV2 : W.hS.V = 202048) (hd5 : W.hS.d = 5120) (a : P × S) (y : Strs)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (hWa : WaSeat arr N W n rb V' a.2)
    (hR : InRange w.cells) {o : HeadOwn} {claim : OnBytes.Model.WsClaim}
    {x : OnBytes.Model.Head.Heard} (ho : a.2.here = .head o) (hcl : o.claim = some claim)
    (hx : o.x = some x) (hsv : x.sV < W.H.ns)
    (hk : wtK6 cs arr msR N W lay6 num n rb 24 a y w) :
    claimVal Reading.gl W.layers.wsLay (cellsIn Pl (cellOf w)) claim =
      Reading.gl.val (o.F.vp.getD x.sV zeroE) -
        Reading.gl.val (o.F.mf.getD x.sV zeroE) * Sound.maskRowAt cs arr msR N 24 a w x.sV := by
  obtain ⟨i, hi⟩ := hR
  have hWt := hk rfl ⟨i, hi⟩
  obtain ⟨hWa1, hseat⟩ := hWa
  obtain ⟨s, s', rv, gs, cov, t, hd, hWL, hcan, hK, hcov, hclaim, hLT⟩ := hWa1
  have hst : SameHeard s' a.2 := by
    obtain ⟨o1, o2, ho1, ho2, e1, _, e3, e4, e5, e6, _⟩ := hK
    refine ⟨e6, e5, fun o3 h3 => ?_⟩
    rw [ho1] at h3
    obtain rfl := First.Here.head.inj h3
    exact ⟨o2, ho2, e3, e1, e4⟩
  have hcell : ∀ r c, cellOf w r c = ((i.mat r c : Int) : K) := by
    intro r c
    rw [hcellOf]
    by_cases h : r < rows ∧ c < cols
    · rw [dif_pos h]
      exact hi.1 ⟨r, h.1⟩ ⟨c, h.2⟩
    · rw [dif_neg h, hi.2 r c h]
      simp
  obtain ⟨g, H, F1, a0, gk, o', p1, p2, p3, p4, p5, p6, p8, J⟩ :=
    Came.plain_of_weightAt W 24 hd hWL hcan hplan hst hTT hcov hr hc hi Pl hPl (cellOf w) hcell
  obtain rfl : o = o' := First.Here.head.inj (ho.symm.trans p5)
  obtain rfl : x = heardOf gk H := Option.some.inj (hx.symm.trans p6)
  obtain ⟨q, sg, hq, hsg, J2⟩ := J t Z hl hlam (hclaim o _ claim ho p6 hcl)
  obtain ⟨g2, H2, F2, a2, gk2, Q, b1, b2, b3, b4, b5, _, b7, b8, _, b10⟩ :=
    Came.behind_all W 24 hd hWL hcan
  obtain rfl : g = g2 := Except.ok.inj (p1.symm.trans b1)
  have e2 := Option.some.inj (p2.symm.trans b2)
  obtain rfl : H = H2 := congrArg Prod.fst e2
  obtain rfl : F1 = F2 := congrArg (fun p => p.2.1) e2
  rw [p3] at b3
  obtain rfl := First.Here.head.inj b3
  obtain rfl : gk = gk2 := Option.some.inj (p4.symm.trans b4)
  have hsz := Came.runAt_sizes W p1 cov (heardOf gk H) t
  have hV : V = nV := hsz.2.symm.trans hV2
  have hd' : Norm.d = nD := by
    obtain ⟨_, _, _, _, _, rfl⟩ := Came.given_ok _ _ _ _ p1
    exact hd5
  -- the hidden value under the one slot is the same at both ledgers
  have hhid : hidden F1 (compCut cs arr msR N (Meaning.sizesOf W) (seatLay W lay6 num) W
      (plAt n rb) w).2 (heardOf gk H).sV = hidden o.F (compCut cs arr msR N (Meaning.sizesOf W)
      (seatLay W lay6 num) W (plAt n rb) w).2 (heardOf gk H).sV := by
    obtain ⟨o1, o2, ho1, ho2, _, _, _, _, _, _, hL⟩ := hK
    rw [ho] at ho2
    obtain rfl := First.Here.head.inj ho2
    obtain ⟨x1, hx1, hv, hf⟩ := weightSlot_filled W.hS (readsOf W) ho1 b7
    have ho1' : o1 = { a0 with F := F1, x := some (heardOf gk H), squaresP := some Q } := by
      rw [b5] at ho1
      exact (First.Here.head.inj ho1).symm
    have eslot : OnBytes.Model.Aff.slot (heardOf gk H).sV =
        OnBytes.Model.Aff.slot (x1.tH.sEnd + 1) := b10.symm.trans hv
    have ej : (heardOf gk H).sV = x1.tH.sEnd + 1 := by
      have := congrArg (fun f : OnBytes.Model.Aff => (f.slots.getD 0 (0, zeroE)).1) eslot
      exact this
    have eF : o1.F = F1 := by rw [ho1']
    rw [ej, ← eF]
    exact (hidden_keptFo _ hL hf).symm
  have hWs' := (weightAt_keptFo W hK ⟨H, b7⟩ _ _).mp hWt
  have hfin := J2 (hLT g o _ q sg p1 ho p6 hq hsg) (compCut cs arr msR N (Meaning.sizesOf W)
    (seatLay W lay6 num) W (plAt n rb) w).1.toCells rfl hV hd' (compCut cs arr msR N
    (Meaning.sizesOf W) (seatLay W lay6 num) W (plAt n rb) w).2 hhid hWs'
  rw [maskRows_one cs arr msR N _ _ W n rb h1 a w hseat _ hsv] at hfin
  exact hfin

/-- **THE SAME, THE MASK ROW AS THE TABLE'S FORMS READ IT.** a9: the open segment's part at the
state. The two sides stand in the order in which the merge's law has them. By
Sound.maskRowAt_of_part (Johnson/Desc/Sound/MaskRowAt.lean).
WHAT IT IS NOT: as plain_of_wtK6. -/
theorem forms_of_wtK6 (hplan : (parOf W.hS (workOf W)).ok = true) (hTT : W.T = W.hS.T)
    (V' : ℕ) (hr : rows ≤ Inst.Model.Layout.hRef) (hc : cols ≤ 2 ^ kRef)
    (Pl : First.K11Caller.Place) (hPl : Pl.lay = W.layers.wsLay)
    (cellOf : Wit (Fin rows → Fin cols → GE) Tok MsgT → ℕ → ℕ → K)
    (hcellOf : ∀ w r c, cellOf w r c =
      if h : r < rows ∧ c < cols then w.cells ⟨r, h.1⟩ ⟨c, h.2⟩ else 0)
    (h1 : namedOnce arr N 24 n = true)
    {sh : OnBytes.Model.WsShape} (Z : OnBytes.Road.SizedW sh ppref)
    (hl : OnBytes.Model.wsLayOf sh true kRef = .ok W.layers.wsLay) (hlam : W.H.lamS = 13)
    (hV2 : W.hS.V = 202048) (hd5 : W.hS.d = 5120) (a : P × S) (y : Strs)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (hWa : WaSeat arr N W n rb V' a.2)
    (hR : InRange w.cells) {o : HeadOwn} {claim : OnBytes.Model.WsClaim}
    {x : OnBytes.Model.Head.Heard} (ho : a.2.here = .head o) (hcl : o.claim = some claim)
    (hx : o.x = some x) (hsv : x.sV < W.H.ns) (a9 : K9.Part) (h9 : K9.segAt? a.2 = some a9)
    (hk : wtK6 cs arr msR N W lay6 num n rb 24 a y w) :
    Reading.gl.val (o.F.vp.getD x.sV zeroE) - Reading.gl.val (o.F.mf.getD x.sV zeroE) *
        (Sound.dataQ (N.group 24) a9 (Sound.seatTab cs arr msR w)).mask x.sV =
      claimVal Reading.gl W.layers.wsLay (cellsIn Pl (cellOf w)) claim := by
  rw [← Sound.maskRowAt_of_part cs arr msR N 24 a w x.sV a9 h9]
  exact (plain_of_wtK6 cs arr msR N W lay6 num n rb hplan hTT V' hr hc Pl hPl cellOf hcellOf h1 Z
    hl hlam hV2 hd5 a y w hWa hR ho hcl hx hsv hk).symm

/-- **THE MERGE'S SENTENCE FROM wtK6**, under WaSeat, at maskOf := Sound.maskRowAt cs arr msR N 24.
The premises down to hWa are wtK6_of_wtP1_seat's own, in its words. Beyond them: hR, ho, hcl, hx
(see the head of this file), and the four clauses that stand in wtP1 under "there are": hn, hu, hsv,
hni.
WHAT IT IS NOT: as plain_of_wtK6. -/
theorem wtP1_of_wtK6_seat (hplan : (parOf W.hS (workOf W)).ok = true) (hTT : W.T = W.hS.T)
    (V' : ℕ) (hr : rows ≤ Inst.Model.Layout.hRef) (hc : cols ≤ 2 ^ kRef) (Pm : HeadMergeP)
    (hlay : Pm.lay = W.layers.wsLay) (ni : ℕ)
    (cellOf : Wit (Fin rows → Fin cols → GE) Tok MsgT → ℕ → ℕ → K)
    (hcellOf : ∀ w r c, cellOf w r c =
      if h : r < rows ∧ c < cols then w.cells ⟨r, h.1⟩ ⟨c, h.2⟩ else 0)
    (h1 : namedOnce arr N 24 n = true) (hns : Pm.nMsg ≤ W.H.ns)
    {sh : OnBytes.Model.WsShape} (Z : OnBytes.Road.SizedW sh ppref)
    (hl : OnBytes.Model.wsLayOf sh true kRef = .ok W.layers.wsLay) (hlam : W.H.lamS = 13)
    (hV2 : W.hS.V = 202048) (hd5 : W.hS.d = 5120) (a : P × S) (y : Strs)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (hWa : WaSeat arr N W n rb V' a.2)
    (hR : InRange w.cells) {o : HeadOwn} {claim : OnBytes.Model.WsClaim}
    {x : OnBytes.Model.Head.Heard} (ho : a.2.here = .head o) (hcl : o.claim = some claim)
    (hx : o.x = some x) (hn : 2 * Pm.lay.lk + 3 ≤ Pm.nMsg) (hu : claim.ui < Pm.lay.U.size)
    (hsv : x.sV < Pm.nMsg) (hni : 0 < ni)
    (hk : wtK6 cs arr msR N W lay6 num n rb 24 a y w) :
    wtP1 Pm ni cellOf (Sound.maskRowAt cs arr msR N 24) a y w := by
  have hlP : OnBytes.Model.wsLayOf sh true kRef = .ok Pm.lay := by
    rw [hlay]
    exact hl
  have heq := plain_of_wtK6 cs arr msR N W lay6 num n rb hplan hTT V' hr hc
    (planPlace Pm hlP ⟨claim.ui, hu⟩) hlay cellOf hcellOf h1 Z hl hlam hV2 hd5 a y w hWa hR ho
    hcl hx (Nat.lt_of_lt_of_le hsv hns) hk
  rw [← hlay] at heq
  refine ⟨sh, true, kRef, hlP, hn, ⟨claim.ui, hu⟩, x.sV, hsv, 0, hni,
    ⟨o, claim, x, ho, hcl, hx, rfl, rfl⟩, ?_⟩
  intro b
  unfold frontIn
  rw [ho]
  simp only [hcl, Option.getD_some]
  exact heq

/-- **BOTH WAYS**, under the premises of both.
WHAT IT IS NOT: as plain_of_wtK6. -/
theorem wtK6_iff_wtP1_seat (hplan : (parOf W.hS (workOf W)).ok = true) (hTT : W.T = W.hS.T)
    (V' : ℕ) (hr : rows ≤ Inst.Model.Layout.hRef) (hc : cols ≤ 2 ^ kRef) (Pm : HeadMergeP)
    (hlay : Pm.lay = W.layers.wsLay) (ni : ℕ)
    (cellOf : Wit (Fin rows → Fin cols → GE) Tok MsgT → ℕ → ℕ → K)
    (hcellOf : ∀ w r c, cellOf w r c =
      if h : r < rows ∧ c < cols then w.cells ⟨r, h.1⟩ ⟨c, h.2⟩ else 0)
    (h1 : namedOnce arr N 24 n = true) (hns : Pm.nMsg ≤ W.H.ns)
    {sh : OnBytes.Model.WsShape} (Z : OnBytes.Road.SizedW sh ppref)
    (hl : OnBytes.Model.wsLayOf sh true kRef = .ok W.layers.wsLay) (hlam : W.H.lamS = 13)
    (hV2 : W.hS.V = 202048) (hd5 : W.hS.d = 5120) (a : P × S) (y : Strs)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (hWa : WaSeat arr N W n rb V' a.2)
    (hR : InRange w.cells) {o : HeadOwn} {claim : OnBytes.Model.WsClaim}
    {x : OnBytes.Model.Head.Heard} (ho : a.2.here = .head o) (hcl : o.claim = some claim)
    (hx : o.x = some x) (hn : 2 * Pm.lay.lk + 3 ≤ Pm.nMsg) (hu : claim.ui < Pm.lay.U.size)
    (hsv : x.sV < Pm.nMsg) (hni : 0 < ni) :
    wtK6 cs arr msR N W lay6 num n rb 24 a y w ↔
      wtP1 Pm ni cellOf (Sound.maskRowAt cs arr msR N 24) a y w :=
  ⟨wtP1_of_wtK6_seat cs arr msR N W lay6 num n rb hplan hTT V' hr hc Pm hlay ni cellOf hcellOf h1
      hns Z hl hlam hV2 hd5 a y w hWa hR ho hcl hx hn hu hsv hni,
    wtK6_of_wtP1_seat cs arr msR N W lay6 num n rb hplan hTT V' hr hc Pm hlay ni cellOf hcellOf h1
      hns Z hl hlam hV2 hd5 a y w hWa⟩

end

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.says_of_weightAt
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.plain_of_weightAt
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.plain_of_wtK6
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.forms_of_wtK6
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.wtP1_of_wtK6_seat
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.wtK6_iff_wtP1_seat
