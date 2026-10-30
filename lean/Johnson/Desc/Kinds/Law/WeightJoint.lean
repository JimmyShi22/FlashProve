-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/WeightJoint.lean: from the sentence on the claim that the merge takes at the
head's link to the sentence on the weights in what the output head's block's law opens: ONE THEOREM,
at the carried record's own letters, with all that the files beside it have paid paid.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.Came).
  hOn_at: the tie on the covered positions, where they are made by S.covered (at the head's number
      of positions; at any number of entries of the vocabulary) at a record with the request's words
      of the record in front of the head's block.
  weightAt_at_quiet: s, s': the records in front of and behind the head's block; sQ: the record at
      which the step behind the digits' lookup makes the merge's claim; SameHeard s' sQ
      (Law/HeardStays.lean). Where that step's plain text returns a claim at its own letters: IF the
      hidden value under the slot x.sV, at the ledger behind the head's block, reads as the sum of
      THAT claim over the digit matrix of the index i that the stored table's cells M hold, THEN
      WeightAt W s' c mask, at every c whose weights are whOf M.
  claimVal_written: the sum of the head's claim over an index's digit matrix, written out (two
      lemmas of the library).
  says_of_typed: from the typed claim of the merge's caller's record to the sentence that the joint
      asks.
  weightAt_of_typed: the joint from the typed claim of the merge's caller's record
      (Johnson/Top/H0/K11Caller/HeadClaim.lean: plain_head_says): (G P T).Cl st m a' gives WeightAt,
      under ONE PREMISE THAT JOINS THE TWO WORLDS (hport).

Every letter under "there is", and the clause that pins it. g by given at s; H, F1 by the hearing's
return; a by s.here; gk by a.lookHeard; o' by sQ.here; q by callNo; sg by seg?.
PREMISES THAT NOBODY PAYS HERE, ALL IN THE STATEMENTS. The tests on the plan say yes (K6On's second
clause; at the seated block: its planOk) · SameHeard s' sQ (owed block by block:
Law/HeardStays.lean's head) · W.T = W.hS.T (a public number) · the reference layout AT
W.layers.wsLay (Z, hl) · W.H.lamS = 13 · V = nV · d = nD (public) · LeftTies: TWO: ew and wx of the
top digit's key against the layout's segment "HD0" · Holds M i · c.Wh = whOf M (a choice of the
reading) · hport: the hidden value under the slot, AT THE LEDGER BEHIND THE HEAD'S BLOCK AND AT OUR
MASK ROW, with the typed record's mask entry times its factor, is the typed record's shown value: it
holds three debts in one: the unfolding of a slot's value; that the ledger's two entries under that
slot stay up to the merge; that the two sides speak of one mask row · hW: the typed entries hold i's
digits: the same table of cells on both sides · Fit · the merge's own law, which gives the typed
claim. Limits. THE REFERENCE SIZES ALONE: at the small size every top here is empty: no values below
the full size can meet the premises. Values, not texts. No values are shown at which the premises
hold together. No draw, no error term, nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.HeardStays

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
open VerifiableInference.Desc.First.K11Caller (headClaim ewAt)

namespace Came

/-- **The tie on the covered positions.** -/
theorem hOn_at (W : OnBytes.Model.Verify.Public) {s sQ : S} {g : Given}
    (hg : given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s = .ok g) {T' V' : Nat}
    (hT' : T' = W.hS.T) {cov : OnBytes.Model.Head.Covered} (hcov : sQ.covered T' V' = .ok cov)
    (hreq : sQ.req = s.req) : ∀ i, i < T → cov.hOn.getD i false = checked i := by
  obtain ⟨z, y, _, _, _, rfl⟩ := given_ok _ _ _ _ hg
  intro i hi
  subst hT'
  have e := hOn_of_covered hcov i hi
  have r1 : sQ.rowR = s.rowR := by
    unfold S.rowR S.reqT
    rw [hreq]
  have r2 : sQ.rowE = s.rowE := by
    unfold S.rowE S.reqT
    rw [hreq]
  rw [e, r1, r2]
  rfl

/-- **The joint, at the record at which the merge's claim is made.** -/
theorem weightAt_at_quiet (W : OnBytes.Model.Verify.Public) (l : Nat) {s s' sQ : S}
    {rv : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hd : (blockAt W.hS (readsOf W) (workOf W) l).decide s rv gs = .ok s')
    (hWL : WellLaid ((seatAt W.hS (readsOf W)).ledger s)) (hcan : Canonical rv)
    (hplan : (parOf W.hS (workOf W)).ok = true) (hst : SameHeard s' sQ) (hTT : W.T = W.hS.T) {V' :
        Nat}
    {cov : OnBytes.Model.Head.Covered} (hcov : sQ.covered W.T V' = .ok cov)
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
              rd (atWorld F1 mask noEnt (OnBytes.Model.Aff.slot (heardOf gk H).sV)) =
                claimVal Reading.gl W.layers.wsLay (fun r c' => ((i.mat r c' : Int) : K)) claim →
              WeightAt W s' c mask) := by
  obtain ⟨g, H, F1, a, gk, Q, hg, hh, ha, hgk, hs', hg', hH', eF, _, hv⟩ :=
    behind_all W l hd hWL hcan
  obtain ⟨o', ho', _, ex, _⟩ := hst.head _ (by rw [hs'])
  have hreq : sQ.req = s.req := by
    rw [hst.req, hs']
  refine ⟨g, H, F1, a, gk, o', hg, hh, ha, hgk, ho', ex, eF,
    fun t sh Z hl hlam claim hk => ?_⟩
  obtain ⟨q, sg, hq, hsg, hcl, _⟩ := First.K11Caller.weightsClaim_head Z hl hk hlam
  refine ⟨q, sg, hq, hsg, hcl, fun hL c hWh hV hd' mask hsays => ?_⟩
  obtain ⟨l2, l3⟩ := hL
  have l1 := zt_size_at W hg hplan
  obtain ⟨hT, hV'⟩ := runAt_sizes W hg cov (heardOf gk H) t
  have hOn := hOn_at W hg hTT hcov hreq
  refine ⟨g, H, hg', hH', ?_⟩
  rw [eF]
  letI : Heard := H.2.2
  have hrH : (rH : Point).size = lt := rH_size hWL hh l1
  have hrs : (rs : Point).size = 13 := (rs_size hWL hh l1).trans (lPd_ref hd')
  obtain ⟨_, _, _, _, _, _, _, hsL, _⟩ := hear_parts hWL hh
  have hcc : okE (logits.end_ 1).var.const = true := sumcheck_okEnds hsL 1
  have hv' : (logits.end_ 1).var = OnBytes.Model.Aff.slot (heardOf gk H).sV := hv
  refine weightTrue_of_says
    (twinTies_heardOf gk H (runAt W cov (heardOf gk H) t) _ rfl hT hV' hOn hrH l2 l3) Z hl
    (fun r c' => ((i.mat r c' : Int) : K)) c hV hd' hrs
    (fun k v hk hv2 => reads_as_Hof hr hc hH hWh (hd' ▸ hk) (hV ▸ hv2)) F1 mask noEnt hcc ?_
  rw [hv', hsays, hcl]
  rfl

/-- The sum of the head's claim over an index's digit matrix, written out. -/
theorem claimVal_written {sh : OnBytes.Model.WsShape} (Z : OnBytes.Road.SizedW sh ppref)
    {lay : OnBytes.Model.WsLay} (hl : OnBytes.Model.wsLayOf sh true kRef = .ok lay) (i : Cm.Idx)
    (AV rs' : Array E) (hs : 13 ≤ rs'.size) :
    claimVal Reading.gl lay (fun r c' => ((i.mat r c' : Int) : K)) (headClaim lay AV rs') =
      ∑ v ∈ Finset.range nV, ∑ k ∈ Finset.range nD,
        Reading.gl.val (AV.getD v zeroE) * eqR Reading.gl rs' 0 13 k *
          ((i.index.val.H k v : Int) : K) := by
  unfold headClaim
  rw [OnBytes.Road.Hd.claimVal_head Reading.gl Z hl _ AV rs' hs]
  refine Finset.sum_congr rfl fun v hv => Finset.sum_congr rfl fun k hk => ?_
  rw [← OnBytes.Road.HeadReq.cast_H_eq_Hof i.mat (Finset.mem_range.mp hk)
    (Finset.mem_range.mp hv)]
  rfl

open VerifiableInference.Desc.First.K11Caller (Letters Fit G) in
/-- **From the typed claim of the merge's caller's record to the sentence that the joint asks.**
val:
any element of the field that, with the typed record's mask entry times its factor, is the typed
record's shown value. -/
theorem says_of_typed {sh : OnBytes.Model.WsShape} (Z : OnBytes.Road.SizedW sh ppref)
    (P : First.K11Caller.Place)
    (hl : OnBytes.Model.wsLayOf sh true kRef = .ok P.lay) (a' : Fin P.n) (T' : Letters K P)
    (st : T'.St) (m : P.Cell ⊕ T'.Jm → K) (cl : Fin P.n → OnBytes.Model.WsClaim)
    {R : OnBytes.Model.Head.Run} (hk : First.Look.weightsClaim R P.lay = .ok (cl a'))
    (hlam : R.hp.lamS = 13) (hs : 13 ≤ R.x.rs.size) (F : Fit Reading.gl P T' st cl) (i : Cm.Idx)
    (hW : ∀ rc : P.Cell, m (.inl rc) = ((i.mat rc.1.val rc.2.val : Int) : K)) {val : K}
    (hport : val + m (.inr (T'.nm a')) * (T'.rd st).be a' = (T'.rd st).sh a')
    (hCl : (G P T').Cl st m a') :
    val = claimVal Reading.gl P.lay (fun r c' => ((i.mat r c' : Int) : K)) (cl a') := by
  obtain ⟨q, sg, h1, h2, hiff⟩ := First.K11Caller.plain_head_says OnBytes.Road.gl_numerals Z P hl a'
    T' st m cl hk hlam hs F i hW
  obtain ⟨q2, sg2, k1, k2, hcl, _⟩ := First.K11Caller.weightsClaim_head Z hl hk hlam
  obtain rfl : q = q2 := Option.some.inj (h1.symm.trans k1)
  obtain rfl : sg = sg2 := Option.some.inj (h2.symm.trans k2)
  rw [hcl, claimVal_written Z hl i _ _ hs]
  exact add_right_cancel (hport.trans (hiff.mp hCl).symm)

open VerifiableInference.Desc.First.K11Caller (Letters Fit G) in
/-- **The joint, from the typed claim of the merge's caller's record**, in one theorem. -/
theorem weightAt_of_typed (W : OnBytes.Model.Verify.Public) (l : Nat) {s s' sQ : S}
    {rv : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hd : (blockAt W.hS (readsOf W) (workOf W) l).decide s rv gs = .ok s')
    (hWL : WellLaid ((seatAt W.hS (readsOf W)).ledger s)) (hcan : Canonical rv)
    (hplan : (parOf W.hS (workOf W)).ok = true) (hst : SameHeard s' sQ) (hTT : W.T = W.hS.T) {V' :
        Nat}
    {cov : OnBytes.Model.Head.Covered} (hcov : sQ.covered W.T V' = .ok cov)
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
        (P : First.K11Caller.Place) (_ : P.lay = W.layers.wsLay)
        (_ : OnBytes.Model.wsLayOf sh true kRef = .ok P.lay) (_ : W.H.lamS = 13)
        (a' : Fin P.n) (T' : Letters K P) (st : T'.St) (m : P.Cell ⊕ T'.Jm → K)
        (cl : Fin P.n → OnBytes.Model.WsClaim)
        (_ : First.Look.weightsClaim (runAt W cov (heardOf gk H) t) P.lay = .ok (cl a'))
        (_ : Fit Reading.gl P T' st cl)
        (_ : ∀ rc : P.Cell, m (.inl rc) = ((i.mat rc.1.val rc.2.val : Int) : K)),
        ∃ q sg, OnBytes.Model.Head.callNo W.HLy "HD0" = some q ∧
          (W.HLy.calls.getD q default).seg? "HD0" = some sg ∧
          (LeftTies W g cov (heardOf gk H) t (ewAt (runAt W cov (heardOf gk H) t) q sg) →
            ∀ c : Cells, c.Wh = whOf M → V = nV → d = nD → ∀ mask : Nat → E,
              rd (atWorld F1 mask noEnt (OnBytes.Model.Aff.slot (heardOf gk H).sV)) +
                  m (.inr (T'.nm a')) * (T'.rd st).be a' = (T'.rd st).sh a' →
              (G P T').Cl st m a' → WeightAt W s' c mask) := by
  obtain ⟨g, H, F1, a, gk, o', p1, p2, p3, p4, p5, p6, p7, J⟩ :=
    weightAt_at_quiet W l hd hWL hcan hplan hst hTT hcov hr hc hH
  refine ⟨g, H, F1, a, gk, o', p1, p2, p3, p4, p5, p6, p7,
    fun t sh Z P hPl hl hlam a' T' st m cl hk F hW => ?_⟩
  obtain ⟨q, sg, hq, hsg, _, J2⟩ := J t Z (by rw [← hPl]; exact hl) hlam
    (by rw [← hPl]; exact hk)
  refine ⟨q, sg, hq, hsg, fun hL c hWh hV hd' mask hport hCl => J2 hL c hWh hV hd' mask ?_⟩
  have hs : 13 ≤ (runAt W cov (heardOf gk H) t).x.rs.size := by
    have e := (rs_size hWL p2 (zt_size_at W p1 hplan)).trans (lPd_ref hd')
    show 13 ≤ ((H.2.2.logits.r.extract lt (lt + lPd)).reverse).size
    rw [Array.size_reverse]
    exact Nat.le_of_eq e.symm
  rw [← hPl]
  exact says_of_typed Z P hl a' T' st m cl hk hlam hs F i hW hport hCl

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.hOn_at
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.weightAt_at_quiet
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.claimVal_written
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.says_of_typed
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.weightAt_of_typed
