-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05GuestRow.lean: `whole_row` (Johnson/Desc/First/Att/K05GuestWhole.lean) at
closed parameters whose letter Λ.LE is the reading of the scalar ZC and nothing else: on the left
side the letter LE is gone, and in its place stands the setting `ZcSetting`
(Johnson/Desc/First/Att/K05GuestPaid.lean).

Definitions, statements and proofs.
Main names:
  `TailLinRest`, `tailLin_iff`: `TailLin` is the letter LE at the data heard, and the seven other
    linear claims of the tail.
  `seenAfter_fst`: the first statement stays under what the units have seen.
  `five_of_plan`: the plan's number five is the record's, from the hearing's return
    (`numbers_of_plan`, Johnson/Desc/First/Att/K05Numbers.lean).
  `WholeRowPaidSays`, `whole_row_pay`: for any letters and any base joint A0: `WholeRowSays`, and
    "`Said`, `TailOfP`, `PointsAre`, `SayAt` and Pay give the letter LE at the data heard", give the
    text of `WholeRowSays` with "Pay and `TailLinRest`" where that has `TailLin`.
  `ZcPay`: what stands in the place of LE: there are matrices with `ZcSetting` in the world of the
    message's own mask, and the cells read in them are the message's.
  `pay_closed`: `le_paid` (Johnson/Desc/First/Att/K05GuestPaid.lean) in the form that
    `whole_row_pay` asks.
  `whole_row_paid`: from a yes of `decide`, at any P0 and Λ over the lookup's types and A0 :=
    `forOut`: the count (I), the hearing's return, and at every later ledger `WholeRowPaidSays` at
    `ZcPay`.
  `zcPay_base`: over the committed symbols (`baseOf`, Johnson/Desc/First/Att/K05Caller.lean) `ZcPay`
    is met by `ZcSetting` at the matrices that the message's own symbols spell.
The body of `WholeRowPaidSays` is the text of `WholeRowSays` with that one place replaced.
Premises: those of `whole_row`; hΛ: Λ.LE holds exactly if the reading holds, at the plan's slot five
+ 2, which lies in the ledger.
Used beside these: `seenAfter`, `TailLin`, `numbers_of_plan`, `le_paid`, `whole_row`,
`cellsK`, `matsOf`; no routine in a context.
Limits: those of Johnson/Desc/First/Att/K05GuestWhole.lean and
Johnson/Desc/First/Att/K05GuestPaid.lean. Above all: a chain whose LE is the reading alone says
nothing of the other scalars of that message (ACC, ZO, the two high parts, the index's bits, the
last two): if another statement wants their readings of the same letter, LE grows to a conjunction
and `pay_closed` has to grow with it. `ZcSetting` is shown to be met at no value; that a table is
true is not shown in this file or in what it imports. The lookup's half is tied to no view. Nothing
on an honest prover, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05GuestPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.Rider Cb.LdLkp Cb.LdLkp.Kn Cb.Pv.Att Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers
open OnBytes.Road OnBytes.Road.Rows
open OnBytes.Tie.Pv.Att (PscH SumH TailH UnitsH UnitsClaims seenAfter recOf ownTrs)
open VerifiableInference.OnPublicFiles (LookupCCaller)
open VerifiableInference.Desc.Part
open K5Law (SayAt PointsAre unitReader endsE endsV endsK endsH oldOf sum3Back)
open Cb.Pv.Tail (Size Syms JCell cellValS BaseAt)

section Rest
variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M : Type}

/-- The tail's linear claims but the first. -/
def TailLinRest {X : Type} {T : Tail K M X} (D : TailH ρ T) (x : X) (m : M) : Prop :=
  T.sVM.L (D.x2 x) D.dVM.rd m ∧ T.sVD.L (D.x3 x) D.dVD.rd m ∧
  T.lF (D.x5 x) (Johnson.L5.Layers.rd ρ T.np D.mx) m ∧ T.sF.L (D.x6 x) D.dF.rd m ∧ T.owF (D.dF.nx (D.x6 x)) m ∧
  T.sD.L (D.x8 x) D.dD.rd m ∧ T.sH.L (D.x10 x) D.dH.rd m

theorem tailLin_iff {X : Type} {T : Tail K M X} (D : TailH ρ T) (x : X) (m : M) :
    TailLin D x m ↔ T.sE.L x D.dE.rd m ∧ TailLinRest D x m := Iff.rfl

/-- The first statement stays under what the units have seen. -/
theorem seenAfter_fst {X : Type} : ∀ (us : List (SumL K M (Seen K X))) (d : UnitsH ρ us) (sn : Seen K X),
    (seenAfter us d sn).1 = sn.1
  | [], _, _ => rfl
  | _ :: us, d, sn => seenAfter_fst us d.2 (sn.1, sn.2 ++ [List.ofFn d.1.rd])

end Rest

/-- The plan's number five is the record's. -/
theorem five_of_plan {x : Params.AttentionRounds} {F G : Fork} {rs : List Fmt.RoundView} {h : Heard}
    (hh : hear x (F, rs, 0) = some (h, G, [], 0)) (hz : Sized F) : (numsPlan x F.next).five = h.five := by
  rw [← (numbers_of_plan hh hz).1]
  rfl

section Pay
variable (c : LookupCCaller)
  (P : OwnPar Cb.Gl.E c.Sg.Msg (TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)))
  (A0 : Rels c.Kc (TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)) c.Ex (c.Sg.Msg × c.Wp))

/-- The text of `WholeRowSays` (Johnson/Desc/First/Att/K05GuestWhole.lean) with one place replaced:
where that has `TailLin`, this has "Pay and `TailLinRest`". -/
def WholeRowPaidSays (maskOf : c.Sg.Msg → ℕ → Cb.Gl.E) (x : Params.AttentionRounds) (F G : Fork)
    (rs : List Fmt.RoundView) (h : Heard) (S : Attention.Shape) (zk : Array (Array E))
    (Pts : Reading Cb.Gl.E → TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → Prop)
    (Pay : Reading Cb.Gl.E → TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → c.Sg.Msg → (ℕ → ℕ → ℕ → Cb.Gl.E) →
      Forest.Heard → Runs.In → ℕ → Prop) : Prop :=
  ∃ L : Lists, RoundsAre L.rounds rs ∧ Said x h G L ∧ Sized G ∧ Stays F G ∧
    ∀ (ρ : Reading Cb.Gl.E) (nz : BetasNz ρ L) (x0 : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)), Pts ρ x0 →
      ∃ (du : UnitsH ρ (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units)
        (dt : TailH ρ (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).tail),
        (UnitsOfP (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du x.score h.scores.toList L.planes.flatten L.units ∧
          TailOfP dt x h L ∧
          UnitsVals (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du
            (unitsAdd (ρ := ρ) (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units (landedUnits P _) L.planes.flatten L.units
              (x0, [])) ∧
          TailVals dt (tailAdd (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).tail L h nz (landedTail P _)
            (seenAfter (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du (x0, []))) ∧
          UnitsAreP (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du h.scores.toList ∧ TailIsP dt x h L) ∧
        (UnitsClaims (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du (x0, []) ∧
          dt.Claims (seenAfter (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du (x0, []))) ∧
        (∀ (Ex : ExtSpec) (y : Ex.Str), ((P.own (theMeans Cb.Gl.E P.D P.C P.kap)).ch.R Ex).red.out (x0, y)
          ((P.own (theMeans Cb.Gl.E P.D P.C P.kap)).ch.join Ex (ownTrs (P.own (theMeans Cb.Gl.E P.D P.C P.kap)) du dt)) =
          some ((P.own (theMeans Cb.Gl.E P.D P.C P.kap)).ch.run x0 (ownTrs (P.own (theMeans Cb.Gl.E P.D P.C P.kap)) du dt), y)) ∧
        ∀ (l : Left), leftP (geoOf S) zk h G = some l →
        ∀ (Dn : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → c.Sg.Msg → Prop)
          (m : c.Sg.Msg) (entry : ℕ → ℕ → ℕ → Cb.Gl.E) (gL : Forest.Heard) (i : Runs.In) (Kc : ℕ),
          i.g = geoOf S → PointsAre i.g zk h l i.p → SayAt ρ (G.worldOf ρ (maskOf m) entry) S gL i Kc →
          (∀ (a : c.St₀ × c.Ex.Str) (τ₁ : Tr (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).R.shape) (y : c.Ex.Str)
            (wp : c.Wp), (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).R.red.out a τ₁ = some (x0, y) →
          Good c P A0 Dn m a (Tr.app τ₁ ((ownA c P).ch.join c.Ex (ownTrs (ownA c P) du dt))) →
          A0.relR (x0, y) (m, wp) →
          (Dn x0 m ∧
              (UnitsLin (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du (x0, []) m ∧
                UnitsMeans (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du
                  (unitsAdd (ρ := ρ) (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units (landedUnits P _) L.planes.flatten
                    L.units (x0, [])) 0 (unitReader S gL i Kc) (G.worldOf ρ (maskOf m) entry) m) ∧
              ((Pay ρ x0 m entry gL i Kc ∧
                  TailLinRest dt (seenAfter (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du (x0, [])) m) ∧
                EndsMean (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).tail.sE dt.dE
                  (tailAdd (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).tail L h nz (landedTail P _)
                    (seenAfter (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du (x0, []))).aE
                  (endsE (oldOf S gL i) Kc) (G.worldOf ρ (maskOf m) entry) m ∧
                EndsMean (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).tail.sVM dt.dVM
                  (tailAdd (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).tail L h nz (landedTail P _)
                    (seenAfter (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du (x0, []))).aM
                  (endsV (oldOf S gL i) Kc (sum3Back i.p.d.vpm) i.t.tVM i.t.ptM false i.t.qVM)
                  (G.worldOf ρ (maskOf m) entry) m ∧
                EndsMean (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).tail.sVD dt.dVD
                  (tailAdd (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).tail L h nz (landedTail P _)
                    (seenAfter (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du (x0, []))).aVD
                  (endsV (oldOf S gL i) Kc (sum3Back i.p.d.vpd) i.t.tVD i.t.ptD true i.t.qVD)
                  (G.worldOf ρ (maskOf m) entry) m ∧
                EndsMean (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).tail.sD dt.dD
                  (tailAdd (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).tail L h nz (landedTail P _)
                    (seenAfter (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du (x0, []))).aD
                  (endsK (oldOf S gL i) Kc) (G.worldOf ρ (maskOf m) entry) m ∧
                EndsMean (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).tail.sH dt.dH
                  (tailAdd (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).tail L h nz (landedTail P _)
                    (seenAfter (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du (x0, []))).aH
                  (endsH (oldOf S gL i) Kc) (G.worldOf ρ (maskOf m) entry) m)) →
          (forIn Cb.Gl.E c.h c.L c.R0 c.msg₀).relR a (m, wp) ∧ Three P m) ∧
          ((P.tail (theMeans Cb.Gl.E P.D P.C P.kap)).toTail.owF
              (dt.dF.nx (dt.x6 (seenAfter (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du (x0, [])))) m ↔
            ∀ b : Fin P.D.nb, P.sF.T.map dt.dF.st (P.msg m) (b, false)
              (ldPartIni P.sF.T.nv P.sF.T.deg (pDummy Cb.Gl.E P.sF.T.DY) dt.dF.out.pt) =
                (_root_.Fo.readHeadT (oldOf S gL i) Kc i.t.qF S.atQ ((oldOf S gL i).x.rg S) ((oldOf S gL i).x.rc S)
                  (b.1 / S.HA) (b.1 % S.HA)).value ρ (G.worldOf ρ (maskOf m) entry))

/-- **The letter LE off the left side**, for any letters. -/
theorem whole_row_pay (maskOf : c.Sg.Msg → ℕ → Cb.Gl.E) (x : Params.AttentionRounds) (F G : Fork)
    (rs : List Fmt.RoundView) (h : Heard) (S : Attention.Shape) (zk : Array (Array E))
    (Pts : Reading Cb.Gl.E → TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → Prop)
    (Pay : Reading Cb.Gl.E → TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → c.Sg.Msg → (ℕ → ℕ → ℕ → Cb.Gl.E) →
      Forest.Heard → Runs.In → ℕ → Prop)
    (H : WholeRowSays c P A0 maskOf x F G rs h S zk Pts)
    (hpay : ∀ (L : Lists) (ρ : Reading Cb.Gl.E) (dt : TailH ρ (ownA c P).tail)
      (sn : Seen Cb.Gl.E (TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀))) (l : Left) (m : c.Sg.Msg)
      (entry : ℕ → ℕ → ℕ → Cb.Gl.E) (gL : Forest.Heard) (i : Runs.In) (Kc : ℕ), Said x h G L → TailOfP dt x h L →
      PointsAre i.g zk h l i.p → SayAt ρ (G.worldOf ρ (maskOf m) entry) S gL i Kc → Pay ρ sn.1 m entry gL i Kc →
      P.LE sn dt.dE.rd m) :
    WholeRowPaidSays c P A0 maskOf x F G rs h S zk Pts Pay := by
  obtain ⟨L, a1, a2, a3, a4, a5⟩ := H
  refine ⟨L, a1, a2, a3, a4, fun ρ nz x0 hp => ?_⟩
  obtain ⟨du, dt, b1, b3, b4, b5⟩ := a5 ρ nz x0 hp
  refine ⟨du, dt, b1, b3, b4, fun l hl Dn m entry gL i Kc hg hP hS => ⟨fun a τ₁ y wp h1 hG hF hB => ?_,
    (b5 l hl Dn m entry gL i Kc hg hP hS).2⟩⟩
  refine (b5 l hl Dn m entry gL i Kc hg hP hS).1 a τ₁ y wp h1 hG hF
    ⟨hB.1, hB.2.1, (tailLin_iff dt _ m).2 ⟨?_, hB.2.2.1.2⟩, hB.2.2.2⟩
  refine hpay L ρ dt _ l m entry gL i Kc a2 b1.2.1 hP hS ?_
  rw [seenAfter_fst (ownA c P).units du (x0, [])]
  exact hB.2.2.1.1

end Pay

section Paid
variable (c : LookupCCaller) {M0 : Type}
  (P0 : OwnPar Cb.Gl.E M0 (TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀))) (Λ : Lin P0 c.Sg.Msg)

/-- What stands in the letter LE's place: the setting of linZcF in the world of the message's own
mask, at matrices in which the cells read are the message's. -/
def ZcPay (S : Attention.Shape) (G : Fork) (ρ : Reading Cb.Gl.E)
    (x0 : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)) (m : c.Sg.Msg) (entry : ℕ → ℕ → ℕ → Cb.Gl.E)
    (gL : Forest.Heard) (i : Runs.In) (Kc : ℕ) : Prop :=
  ∃ (tl : HTailF2) (Mm : Mats Cb.Gl.E) (lid : ℕ) (cf : Attention.Cfg) (fs : Model.Forest.Shape),
    ZcSetting ρ (G.worldOf ρ (Λ.maskOf m) entry) tl Kc Mm (oldOf S gL i) lid cf fs P0.C (P0.zOf x0) ∧
      cellsK S Mm = P0.tOf (Λ.restOf m)

/-- The step that pays: at the closed parameters whose Λ.LE is the reading alone. -/
theorem pay_closed (ns : ℕ) (N : Nums)
    (hΛ : ∀ sn r m, Λ.LE sn r m ↔ r P0.iZC - Λ.maskOf m (N.five + 2) =
      AttSeg.rv P0.D P0.C (pubOfZ Cb.Gl.E (P0.zOf sn.1)) (P0.tOf (Λ.restOf m)) .zc)
    (hns : N.five + 2 ≤ ns) (x : Params.AttentionRounds) (hne : x.score ≠ []) (h : Heard) (hN : N.five = h.five)
    (S : Attention.Shape) (hD : L5.dimOf S = P0.D) (zk : Array (Array E)) (G : Fork) (L : Lists)
    (ρ : Reading Cb.Gl.E) (dt : TailH ρ (ownA c (closedOf P0 Λ ns N)).tail)
    (sn : Seen Cb.Gl.E (TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀))) (l : Left) (m : c.Sg.Msg)
    (entry : ℕ → ℕ → ℕ → Cb.Gl.E) (gL : Forest.Heard) (i : Runs.In) (Kc : ℕ) (hs : Said x h G L)
    (ho : TailOfP dt x h L) (hP : PointsAre i.g zk h l i.p)
    (hS : SayAt ρ (G.worldOf ρ (Λ.maskOf m) entry) S gL i Kc)
    (hZ : ZcPay c P0 Λ S G ρ sn.1 m entry gL i Kc) : (closedOf P0 Λ ns N).LE sn dt.dE.rd m := by
  obtain ⟨tl, Mm, lid, cf, fs, Zs, hc⟩ := hZ
  exact le_paid P0 Λ ns N hΛ _ hs hne dt ho entry m hN hns sn Zs hS hP hD hc

/-- **`whole_row` with the letter LE off its left side**, at Λ.LE := the reading alone. -/
theorem whole_row_paid (ok : FoNums.ok c.h = true) (F0 : AttFits c.h P0.D P0.C) (hz : ∀ b, P0.zOf b = b.2.1.pt)
    (hT : P0.D.lT ≤ 16) {St : Type} (seat : Seat St) (p : Par) (st st' : St) (rs : List Fmt.RoundView)
    (hd : decide seat p st rs = .ok st') (hzS : ∀ F, seat.ledger st = some F → Sized F)
    (hΛ : ∀ F, seat.ledger st = some F →
      (∀ sn r m, Λ.LE sn r m ↔ r P0.iZC - Λ.maskOf m ((numsPlan p.own F.next).five + 2) =
        AttSeg.rv P0.D P0.C (pubOfZ Cb.Gl.E (P0.zOf sn.1)) (P0.tOf (Λ.restOf m)) .zc) ∧
      (numsPlan p.own F.next).five + 2 ≤ F.ns)
    (hk4 : P0.kap = 4) (rows : ℕ) (hrec : p.own = recOf P0 rows) (S : Attention.Shape)
    (hDS : P0.D = L5.dimOf S) (Z : Sizes S) (hlt : S.cf.lt = P0.D.lT)
    (hNP : (geoOf S).NP = (size18 P0.D).pairs) (hNP2 : S.NP = P0.D.nb) {u1 u2 : UnitG}
    (hgs : (geoOf S).scores = [u1, u2]) (hb1 : u1.below = true) (hb2 : u2.below = false)
    (zk : Array (Array E)) :
    ∃ (F G : Fork) (h : Heard), seat.ledger st = some F ∧ seat.lay st h G = some st' ∧
      (∀ (Dn : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → c.Sg.Msg → Prop) (m : c.Sg.Msg)
        (a : c.St₀ × c.Ex.Str), (forIn Cb.Gl.E c.h c.L c.R0 c.msg₀).on a →
        Doomed (hostThen c (closedOf P0 Λ F.ns (numsPlan p.own F.next))).shape
          (Err.app (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).e
            ((ownA c (closedOf P0 Λ F.ns (numsPlan p.own F.next))).ch.eps c.Ex))
          (Good c (closedOf P0 Λ F.ns (numsPlan p.own F.next)) (forOut Cb.Gl.E c.h c.L c.R0 c.msg₀) Dn m a)) ∧
      hear p.own (F, rs, 0) = some (h, G, [], 0) ∧
      ∀ G', Stays G G' → G'.ns = G.ns → Sized G' →
        WholeRowPaidSays c (closedOf P0 Λ F.ns (numsPlan p.own F.next)) (forOut Cb.Gl.E c.h c.L c.R0 c.msg₀) Λ.maskOf
          p.own F G' rs h S zk
          (LookAll P0 S zk u1 u2) (ZcPay c P0 Λ S G') := by
  have hne : p.own.score ≠ [] := by rw [hrec]; simp [recOf]
  obtain ⟨F, G, h, a1, a2, aI, ah, a3⟩ := whole_row c P0 Λ ok F0 hz hT seat p st st' rs hd hzS
    (fun F hF => ⟨fun sn r m hL => ((hΛ F hF).1 sn r m).1 hL, (hΛ F hF).2⟩) hk4 rows hrec S hDS Z hlt hNP hNP2
    hgs hb1 hb2 zk
  refine ⟨F, G, h, a1, a2, aI, ah, fun G' q1 q2 q3 => ?_⟩
  exact whole_row_pay c _ _ Λ.maskOf p.own F G' rs h S zk _ _ (a3 G' q1 q2 q3)
    (pay_closed c P0 Λ F.ns _ (hΛ F a1).1 (hΛ F a1).2 p.own hne h (five_of_plan ah (hzS F a1)) S hDS.symm zk G')

end Paid

section Base
variable {s : Size} (c : LookupCCaller)

/-- Over the committed symbols ZcPay is met by the setting at the matrices that the message's own
symbols spell. -/
theorem zcPay_base (S : Attention.Shape) (pl : ℕ → ℕ → ℕ → JCell s) (C : AttSeg.Calls) (npl : ℕ)
    (zOf : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → ℕ → Cb.Gl.E)
    (Λ : Lin (baseOf (K := Cb.Gl.E) S pl C npl zOf) c.Sg.Msg) (G : Fork) (ρ : Reading Cb.Gl.E)
    (x0 : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)) (m : c.Sg.Msg) (entry : ℕ → ℕ → ℕ → Cb.Gl.E)
    (gL : Forest.Heard) (i : Runs.In) (Kc : ℕ) {tl : HTailF2} {lid : ℕ} {cf : Attention.Cfg}
    {fs : Model.Forest.Shape}
    (Zs : ZcSetting ρ (G.worldOf ρ (Λ.maskOf m) entry) tl Kc (matsOf pl (Λ.restOf m)) (oldOf S gL i) lid cf fs C
      (zOf x0)) :
    ZcPay c (baseOf S pl C npl zOf) Λ S G ρ x0 m entry gL i Kc :=
  ⟨tl, matsOf pl (Λ.restOf m), lid, cf, fs, Zs, rfl⟩

end Base

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.five_of_plan
#print axioms VerifiableInference.Desc.First.Att.P.whole_row_pay
#print axioms VerifiableInference.Desc.First.Att.P.pay_closed
#print axioms VerifiableInference.Desc.First.Att.P.whole_row_paid
#print axioms VerifiableInference.Desc.First.Att.P.zcPay_base
