-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Att/HearTie.lean: the tie between the port's routines that receive an attention
sub-proof's own messages and the chain of Cb/Pv/Att/Own.lean: where the routines succeed, the output
of each sumcheck's typed verifier (plainOut) on the transcript made from what they have heard is the
reading of that sumcheck's record, and its target is the reading of the scalars heard from which the
sumcheck starts.

In these routines the port tests nothing of what the prover has sent (its tests are on public
numbers, on the plan's entries and on the numbers of items), and the chain's verifier rejects
nothing, so the tie is an equality of outputs.

Main names:
  SumSize S ws dY: the letters S of a sumcheck have the sizes of what was heard: their degrees give
    the weights ws, and their degree in the further variable is dY.
  D.Of riders H p: the data D (SumH, OnBytes/Tie/Pv/Att/OwnTie.lean) are made of what was heard: its
    riders, as many as the letters say; its lists; and for D.t the target of the port's record p.
  OutIs S D p r: the output D.out is the record's, read: its state is D.st; its eps and its last
    value are the readings of p.eps and p.claim; its point is the reading of the challenges r, then
    of beta; its end values are D.v.
  out_is: OutIs from SumSize, D.Of and Rec (OnBytes/Tie/Pv/Att/HearSaid.lean).
  TailOf, TailIs, tail_is: the six sumchecks behind the score units: the six outputs, and the six
    targets read: the second of the five scalars; the two claims' scalars; the batch of the maxima;
    the batch of the second end values of the score's sumcheck; 0.
  UnitsOf, UnitsAre, units_are: the score units, by recursion on their list: each output, and each
    target read as the last rider.
  hear_tie: if scores, divide and attain succeed one after the other from a state whose arrays on
    slots have their length, there are lists with own_said's facts such that (1) for every reading
    with NzCtx at the first context (OnBytes/Tie/Pv/Psc/Run/NzCtx.lean) the reading of every beta is
    not 0; (2) on a view the stages are rounds of the view, taken off it one by one, that hold these
    lists (heard_view, OnBytes/Tie/Pv/Att/HearView.lean); (3) for every reading, all letters A and
    all data du, dt that are made of these lists and have their sizes: UnitsAre and TailIs.

Under the letters' claims (D.Claim) the chain's run holds these outputs: own_last
(OnBytes/Tie/Pv/Att/OwnTie.lean) unfolds the chain's last claim on them, and tail_run, tail_out
(OnBytes/Tie/Pv/Att/OwnRun.lean) say it of the run behind the score units and of the verifier's
output.

Limits: one direction: from the routines' success. Data du, dt with these lists exist only if the
reading of each beta is not 0 (a field of SumH): by (1) that follows from NzCtx, which is proved
nowhere in this library. Premises that a value of the letters has to pay: the sizes; the letters'
claims (D.Claim), for which the targets' readings are given here. The end values D.v and the states
D.st are free here: which scalar heard is which map's end value is said in
OnBytes/Tie/Pv/Att/Sc3Top.lean and ScdTop.lean (sc3Vals, scdVals). Nothing on soundness, knowledge
soundness or hiding.
-/
import OnBytes.Tie.Pv.Att.HearSaid
import OnBytes.Tie.Pv.Att.HearNz
import OnBytes.Tie.Pv.Att.HearView

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Att
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Attention
open Johnson.L5.Layers Cb.Pv.Att
open OnBytes.Psc (Weight)
open OnBytes.PscRun (Clean)

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M : Type}

/-- The letters have the sizes of what was heard. -/
structure SumSize {X : Type} (S : SumL K M X) (ws : List Weight) (dY : Nat) : Prop where
  ws : ((List.ofFn S.T.deg).map fun d => Weight.plain (d + 1)) = ws
  dY : S.T.DY = dY

/-- The data are made of what was heard. -/
structure SumH.Of {X : Type} {S : SumL K M X} (D : SumH ρ S) (riders : List E) (H : PscH)
    (p : Psc) : Prop where
  r : D.r = riders
  n : S.n = riders.length
  H : D.H = H
  t : D.t = p.target

/-- The output is the record's, read. -/
structure OutIs {X : Type} (S : SumL K M X) (D : SumH ρ S) (p : Psc) (r : Array E) : Prop where
  st : D.out.st = D.st
  eps : D.out.eps = ρ.val p.eps
  fin : D.out.fin = ρ.val p.claim
  ini : ∀ i : Fin S.T.nv, ldPartIni S.T.nv S.T.deg (pDummy K S.T.DY) D.out.pt i =
    ρ.val (r.getD i.1 zeroE)
  last : ldPartLast S.T.nv S.T.deg (pDummy K S.T.DY) D.out.pt = ρ.val D.H.beta
  vals : D.out.vals = D.v

theorem out_is {X : Type} (S : SumL K M X) (D : SumH ρ S) {p : Psc} {r : Array E} {C : Aff}
    {t : E} {ws : List Weight} {dY n : Nat} {riders : List E} {H : PscH} (hs : SumSize S ws dY)
    (hD : D.Of riders H p) (h : Rec p r C t ws dY n H) : OutIs S D p r := by
  have h' : Rec p r C D.t ((List.ofFn S.T.deg).map fun d => Weight.plain (d + 1)) S.T.DY n D.H := by
    rw [hs.ws, hs.dY, hD.H, hD.t, h.target]
    exact h
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := said_out S D p r C n h'
  exact ⟨a1, a2, a3, a4, a5, a6⟩

/-- The data's target is the record's. -/
theorem of_target {X : Type} {S : SumL K M X} {D : SumH ρ S} {p : Psc} {r : Array E} {C : Aff}
    {t : E} {ws : List Weight} {dY n : Nat} {riders : List E} {H : PscH} (hD : D.Of riders H p)
    (h : Rec p r C t ws dY n H) : D.t = t := hD.t.trans h.target

/-! ## The eleven stages behind the score units -/

/-- The tail's data are made of what divide and attain have heard, and have its sizes. -/
structure TailOf {X : Type} {T : Tail K M X} (dt : TailH ρ T) (S : Attention.Shape) (d : Divide)
    (x : Attain) (rE vC : List E) (xV : E) (HE HM HVD : PscH) (dr : Fmt.Drawn) (vM : List E)
    (xF xD xH : E) (HF HD HH : PscH) : Prop where
  zE : SumSize T.sE (ws3 S.nvE) 2
  oE : dt.dE.Of rE HE d.scE.p
  xV : dt.xV = xV
  zM : SumSize T.sVM (ws3 S.nvVM) 2
  oM : dt.dVM.Of vC HM d.vpm.p
  zVD : SumSize T.sVD (ws3 S.nvVD) 2
  oVD : dt.dVD.Of [] HVD d.vpd.p
  pts : dt.pts = dr.elems.map E.ofTriple
  nz : T.nz = dr.elems.length
  mx : dt.mx = vM
  np : T.np = vM.length
  xF : dt.xF = xF
  zF : SumSize T.sF (ws3 S.nvF) 2
  oF : dt.dF.Of [] HF x.scF.p
  xD : dt.xD = xD
  zD : SumSize T.sD (wsD S) (S.cf.lt + 1)
  oD : dt.dD.Of [] HD x.scd.p
  xH : dt.xH = xH
  zH : SumSize T.sH (ws3 S.nvH) 2
  oH : dt.dH.Of [] HH x.scH.p

/-- The six outputs are the records', read, and the six targets are read from what was heard. -/
structure TailIs {X : Type} {T : Tail K M X} (dt : TailH ρ T) (S : Attention.Shape) (d : Divide)
    (x : Attain) (v5 vC vM : List E) (xF xD : E) (HF : PscH) : Prop where
  iE : OutIs T.sE dt.dE d.scE.p d.scE.r
  iM : OutIs T.sVM dt.dVM d.vpm.p d.vpm.r
  iVD : OutIs T.sVD dt.dVD d.vpd.p d.vpd.r
  iF : OutIs T.sF dt.dF x.scF.p x.scF.r
  iD : OutIs T.sD dt.dD x.scd.p x.scd.r
  iH : OutIs T.sH dt.dH x.scH.p x.scH.r
  tE : ρ.val dt.dE.t = ρ.val (v5.getD 1 zeroE)
  tM : ρ.val dt.dVM.t = ρ.val (vC.getD 0 zeroE)
  tVD : ρ.val dt.dVD.t = ρ.val (vC.getD 1 zeroE)
  tF : ρ.val dt.dF.t =
    ∑ b : Fin S.NP, ρ.val ((powers xF S.NP).getD b.1 zeroE) * ρ.val (vM.getD b.1 zeroE)
  tD : ρ.val dt.dD.t =
    ∑ b : Fin S.NP, ρ.val ((powers xD S.NP).getD b.1 zeroE) * ρ.val (HF.v.getD (2 * b.1 + 1) zeroE)
  tH : ρ.val dt.dH.t = 0

theorem tail_is {X : Type} {T : Tail K M X} (dt : TailH ρ T) {S : Attention.Shape} {d : Divide}
    {x : Attain} {pre : List E} {c0 c1 c2 : Ctx} {v5 vI v2 vC : List E} {xV : E}
    {HE HM HVD : PscH} {tE tM tVD : E} {dr : Fmt.Drawn} {vM : List E} {xF xD xH : E}
    {HF HD HH : PscH} {tF tD tH : E}
    (hd : DivideSaid S d pre c0 c1 v5 vI v2 vC xV HE HM HVD tE tM tVD)
    (hx : AttainSaid S x c1 c2 dr vM xF xD xH HF HD HH tF tD tH)
    (h : TailOf dt S d x (pre ++ (v5 ++ (vI ++ v2))) vC xV HE HM HVD dr vM xF xD xH HF HD HH) :
    TailIs dt S d x v5 vC vM xF xD HF where
  iE := out_is T.sE dt.dE h.zE h.oE hd.rE
  iM := out_is T.sVM dt.dVM h.zM h.oM hd.rM
  iVD := out_is T.sVD dt.dVD h.zVD h.oVD hd.rD
  iF := out_is T.sF dt.dF h.zF h.oF hx.rF
  iD := out_is T.sD dt.dD h.zD h.oD hx.rD
  iH := out_is T.sH dt.dH h.zH h.oH hx.rH
  tE := by rw [of_target h.oE hd.rE]; exact hd.tEr K ρ
  tM := by rw [of_target h.oM hd.rM]; exact hd.tMr K ρ
  tVD := by rw [of_target h.oVD hd.rD]; exact hd.tDr K ρ
  tF := by rw [of_target h.oF hx.rF]; exact hx.tFr K ρ
  tD := by rw [of_target h.oD hx.rD]; exact hx.tDr K ρ
  tH := by rw [of_target h.oH hx.rH, hx.tHr K ρ, ρ.zero]

/-! ## The score units -/

/-- The units' data are made of what the score units have heard, and have its sizes. -/
def UnitsOf {X : Type} : (us : List (SumL K M (Seen K X))) → UnitsH ρ us → List Score →
    List StageH → Prop
  | [], _, [], [] => True
  | u :: us, d, k :: ks, .sum riders ws dY H :: l =>
    SumSize u ws dY ∧ d.1.Of riders H k.sc.p ∧ UnitsOf us d.2 ks l
  | _, _, _, _ => False

/-- The units' outputs are the records', read; each target is read as the last rider. -/
def UnitsAre {X : Type} : (us : List (SumL K M (Seen K X))) → UnitsH ρ us → List Score → Prop
  | [], _, [] => True
  | u :: us, d, k :: ks =>
    OutIs u d.1 k.sc.p k.sc.r ∧ ρ.val d.1.t = ρ.val (d.1.r.getD (d.1.r.length - 1) zeroE) ∧
      UnitsAre us d.2 ks
  | _, _, _ => False

theorem units_are {X : Type} (S : Attention.Shape) (zk : Array (Array E)) :
    ∀ (us : List (SumL K M (Seen K X))) (d : UnitsH ρ us) (pu : List (Nat × ACall × Seg))
      (ks : List Score) (pre : List E) (st : List StageH), UnitsSaid S zk pu ks pre st →
      UnitsOf us d ks st → UnitsAre us d ks
  | [], _, _, [], _, [], _, _ => trivial
  | u :: us, d, p :: pu, k :: ks, pre, .sum riders ws dY H :: l, hs, ho => by
    obtain ⟨e1, e2, ⟨v7, t, l7, er, ht, hr⟩, hl⟩ := hs
    obtain ⟨z, o, hn⟩ := ho
    rw [e1, e2] at z
    refine ⟨out_is u d.1 z o hr, ?_, units_are S zk us d.2 pu ks [] l hl hn⟩
    rw [of_target o hr, ht K ρ, o.r, er, List.length_append, l7,
      show pre.length + 7 - 1 = pre.length + 6 by omega, List.getD_append_right _ _ _ _ (by omega),
      show pre.length + 6 - pre.length = 6 by omega]
  | _ :: _, _, [], _ :: _, _, .sum _ _ _ _ :: _, hs, _ => hs.elim
  | [], _, _, _ :: _, _, _, _, ho => ho.elim
  | [], _, _, [], _, _ :: _, _, ho => ho.elim
  | _ :: _, _, _, [], _, _, _, ho => ho.elim
  | _ :: _, _, _, _ :: _, _, [], _, ho => ho.elim
  | _ :: _, _, _, _ :: _, _, .bat _ _ _ :: _, _, ho => ho.elim
  | _ :: _, _, _, _ :: _, _, .point _ :: _, _, ho => ho.elim

/-! ## The whole -/

/-- The tie. -/
theorem hear_tie (S : Attention.Shape) (zk : Array (Array E))
    (sc : Array PlaneClaim × Array Score) (d : Divide) (x : Attain) (F F1 F2 G : Fork)
    (c c1 c2 c' : Ctx) (hs : scores S zk F c = .ok ((sc, F1), c1))
    (hd : divide S zk F1 c1 = .ok ((d, F2), c2)) (hx : attain S F2 c2 = .ok ((x, G), c'))
    (hz : Sized F) :
    ∃ (ks : List Score) (planes : List E) (units : List StageH) (cm : Ctx)
      (v5 vI v2 vC : List E) (xV : E) (HE HM HVD : PscH) (tE tM tVD : E) (dr : Fmt.Drawn)
      (vM : List E) (xF xD xH : E) (HF HD HH : PscH) (tF tD tH : E),
      (sc.2 = ks.toArray ∧ planes.length = 3 * (unitsOf S Table.kr [Seg.rm, Seg.rd]).length ∧
        UnitsSaid S zk (unitsOf S Table.kfd [Seg.fm, Seg.fd]) ks planes units ∧
        HeardAs units c cm ∧
        DivideSaid S d (if unitsOf S Table.kfd [Seg.fm, Seg.fd] = [] then planes else []) cm c2
          v5 vI v2 vC xV HE HM HVD tE tM tVD ∧
        AttainSaid S x c2 c' dr vM xF xD xH HF HD HH tF tD tH ∧ Sized G) ∧
      (∀ (K : Type) [CommRing K] (ρ : Reading K), NzCtx ρ c →
        AllNz ρ units ∧ ρ.val HE.beta ≠ 0 ∧ ρ.val HM.beta ≠ 0 ∧ ρ.val HVD.beta ≠ 0 ∧
          ρ.val HF.beta ≠ 0 ∧ ρ.val HD.beta ≠ 0 ∧ ρ.val HH.beta ≠ 0 ∧ NzCtx ρ c') ∧
      (c.ch.dry = false → ∃ rv : List Fmt.RoundView, c.ch.pending = rv ++ c'.ch.pending ∧
        RoundsAre ((units ++
          ([StageH.sum ((if unitsOf S Table.kfd [Seg.fm, Seg.fd] = [] then planes else []) ++
              (v5 ++ (vI ++ v2))) (ws3 S.nvE) 2 HE, StageH.bat [] 2 xV,
            StageH.sum vC (ws3 S.nvVM) 2 HM, StageH.sum [] (ws3 S.nvVD) 2 HVD] ++
          [StageH.point dr, StageH.bat vM S.NP xF, StageH.sum [] (ws3 S.nvF) 2 HF,
            StageH.bat [] S.NP xD, StageH.sum [] (wsD S) (S.cf.lt + 1) HD, StageH.bat [] S.NP xH,
            StageH.sum [] (ws3 S.nvH) 2 HH])).flatMap StageH.rounds) rv ∧
        c'.ch.dry = false ∧ (Clean c → Clean c')) ∧
      ∀ (K : Type) [Field K] [Fintype K] (ρ : Reading K) (M X : Type) (A : AttOwn K M X)
        (du : UnitsH ρ A.units) (dt : TailH ρ A.tail), UnitsOf A.units du ks units →
        TailOf dt S d x
          ((if unitsOf S Table.kfd [Seg.fm, Seg.fd] = [] then planes else []) ++
            (v5 ++ (vI ++ v2))) vC xV HE HM HVD dr vM xF xD xH HF HD HH →
        UnitsAre A.units du ks ∧ TailIs dt S d x v5 vC vM xF xD HF := by
  obtain ⟨ks, planes, units, cm, v5, vI, v2, vC, xV, HE, HM, HVD, tE, tM, tVD, dr, vM, xF, xD, xH,
    HF, HD, HH, tF, tD, tH, a1, a2, a3, a4, a5, a6, a7⟩ :=
    own_said S zk sc d x F F1 F2 G c c1 c2 c' hs hd hx hz
  refine ⟨ks, planes, units, cm, v5, vI, v2, vC, xV, HE, HM, HVD, tE, tM, tVD, dr, vM, xF, xD, xH,
    HF, HD, HH, tF, tD, tH, ⟨a1, a2, a3, a4, a5, a6, a7⟩, fun K _ ρ hc => ?_,
    fun hv => heard_view _ c c' hv
      (HeardAs.append units _ c cm c' a4 (HeardAs.append _ _ cm c2 c' a5.heard a6.heard)),
    fun K _ _ ρ M X A du dt hu ht =>
      ⟨units_are S zk A.units du _ ks planes units a3 hu, tail_is dt a5 a6 ht⟩⟩
  obtain ⟨n1, k1⟩ := heard_nz ρ units c cm a4 hc
  obtain ⟨⟨nE, nM, nVD, _⟩, k2⟩ := heard_nz ρ _ cm c2 a5.heard k1
  obtain ⟨⟨nF, nD, nH, _⟩, k3⟩ := heard_nz ρ _ c2 c' a6.heard k2
  exact ⟨n1, nE, nM, nVD, nF, nD, nH, k3⟩

end OnBytes.Tie.Pv.Att

#print axioms OnBytes.Tie.Pv.Att.out_is
#print axioms OnBytes.Tie.Pv.Att.tail_is
#print axioms OnBytes.Tie.Pv.Att.units_are
#print axioms OnBytes.Tie.Pv.Att.hear_tie
