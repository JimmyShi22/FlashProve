-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Att/OwnTie.lean: the chain of an attention sub-proof's own rounds
(Cb/Pv/Att/Own.lean) on the typed transcript that is made from what the port has heard: what its
verifier puts out, and what it claims at its end, stage by stage.

The port's routines hear lists of elements (OnBytes/Tie/Pv/Att/HearStages.lean). For a reading ρ of
the port's elements in the field, this file makes from such lists a transcript for each stage of the
chain, and unfolds the chain's last claim on the run.

Main names:
  SumH ρ S: for the letters S of one sumcheck: the riders and what the sumcheck has heard (PscH);
    that the reading of beta is not 0; the end values under their names; a public state st and an
    element t.
  D.rd, D.tr, D.out, D.nx x: the riders read; the stage's transcript (plainTr,
    OnBytes/Tie/Pv/Att/Tr.lean); plainOut at (ρ t, st); the statement behind the stage.
  D.Claim x: the letters' claim at the statement x and the riders read is (ρ t, st). This is what a
    value of the letters has to show, with t the public part of the port's start form.
  owed_stage: what a sumcheck's stage owes on D.tr, under D.Claim x.
  TailH, TailH.trs, TailH.Claims, tail_owed: the eleven stages behind the score units.
  UnitsH, unitsTrs, UnitsClaims, UnitsOwed, seenAfter, units_owed: the score units, by recursion on
    their list.
  own_out: the reduction of A.ch.R Ex, on the joined transcript, puts out A.ch.run x ts.
  own_last: A.ch.Last Dn on that output holds exactly if Dn x m holds; each unit's linear claims and
    output claims hold of its plainOut; and the like for the eleven stages, with owF in the place of
    the output claims of the score at the index.

Limits: no routine of the port occurs here: that the lists are what a run has heard is said in
OnBytes/Tie/Pv/Att/HearStages.lean, and what each plainOut is in the port's records in Sc3Top.lean
and ScdTop.lean. That the reading of each beta is not 0, and every D.Claim, are premises. Nothing on
soundness, knowledge soundness or hiding.
-/
import OnBytes.Tie.Pv.Att.HearStages
import Cb.Pv.Att.ChainLast
import Cb.Pv.Att.OwnVal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Att
open Iop Prob Cb TWhole OnBytes OnBytes.Model Johnson.L5.Layers Cb.Pv.Att

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K) {M : Type}

/-- What one sumcheck has heard, with what the typed side adds. -/
structure SumH {X : Type} (S : SumL K M X) where
  r : List E
  H : PscH
  b : ρ.val H.beta ≠ 0
  v : S.T.A → K
  st : S.T.St
  t : E

namespace SumH
variable {ρ} {X : Type} {S : SumL K M X} (D : SumH ρ S)

/-- the riders, read -/
def rd : Fin S.n → K := Johnson.L5.Layers.rd ρ S.n D.r

/-- the stage's transcript -/
noncomputable def tr : Tr (shapeRN S.T.our.par S.n) :=
  (((), (D.rd, ρ.val D.H.mu)), ρ.val D.H.eps,
    plainTr ρ S.T D.H.rs D.H.sentY D.H.beta D.b D.v)

/-- the sumcheck's output -/
noncomputable def out : S.T.our.par.Out :=
  plainOut ρ S.T D.st D.t D.H.mu D.H.eps D.H.rs D.H.sentY D.H.beta D.b D.v

/-- the statement behind the stage -/
noncomputable def nx (x : X) : S.Nx := ((x, D.rd), D.out)

/-- the letters' claim at x and the riders read -/
def Claim (x : X) : Prop := S.cl x D.rd = (ρ.val D.t, D.st)

end SumH

/-- What a sumcheck's stage owes on the transcript made from what was heard. -/
theorem owed_stage {X : Type} (S : SumL K M X) (D : SumH ρ S) (Ow : S.Nx → M → Prop)
    (next : Ch K M S.Nx) (x : X) (ts : next.Trs) (m : M) (h : D.Claim x) :
    (S.stage Ow next).Owed x (D.tr, ts) m ↔
      S.L x D.rd m ∧ Ow (D.nx x) m ∧ next.Owed (D.nx x) ts m := by
  show S.L x D.rd m ∧
    Ow ((x, D.rd), shortV S.T.our.par S.T.fix (S.cl x D.rd) (unrideN S.T.our.par S.n D.tr)) m ∧
    next.Owed ((x, D.rd), shortV S.T.our.par S.T.fix (S.cl x D.rd)
      (unrideN S.T.our.par S.n D.tr)) ts m ↔ _
  rw [show S.cl x D.rd = (ρ.val D.t, D.st) from h]
  exact Iff.rfl

/-! ## The eleven stages behind the score units -/

/-- What the eleven stages have heard. -/
structure TailH {X : Type} (T : Tail K M X) where
  dE : SumH ρ T.sE
  xV : E
  dVM : SumH ρ T.sVM
  dVD : SumH ρ T.sVD
  pts : List E
  mx : List E
  xF : E
  dF : SumH ρ T.sF
  xD : E
  dD : SumH ρ T.sD
  xH : E
  dH : SumH ρ T.sH

namespace TailH
variable {ρ} {X : Type} {T : Tail K M X} (D : TailH ρ T) (x : X)

noncomputable def x2 : T.sE.Nx × K := (D.dE.nx x, ρ.val D.xV)
noncomputable def x3 : T.sVM.Nx := D.dVM.nx (D.x2 x)
noncomputable def x5 : T.sVD.Nx × (Fin T.nz → K) :=
  (D.dVD.nx (D.x3 x), Johnson.L5.Layers.rd ρ T.nz D.pts)
noncomputable def x6 : ((T.sVD.Nx × (Fin T.nz → K)) × (Fin T.np → K)) × K :=
  ((D.x5 x, Johnson.L5.Layers.rd ρ T.np D.mx), ρ.val D.xF)
noncomputable def x8 : T.sF.Nx × K := (D.dF.nx (D.x6 x), ρ.val D.xD)
noncomputable def x10 : T.sD.Nx × K := (D.dD.nx (D.x8 x), ρ.val D.xH)

/-- The letters' claims, each at the statement that its stage finds. -/
structure Claims : Prop where
  cE : D.dE.Claim x
  cVM : D.dVM.Claim (D.x2 x)
  cVD : D.dVD.Claim (D.x3 x)
  cF : D.dF.Claim (D.x6 x)
  cD : D.dD.Claim (D.x8 x)
  cH : D.dH.Claim (D.x10 x)

/-- The stages' transcripts, from the back. -/
noncomputable def tH : T.chH.Trs := (ρ.val D.xH, (D.dH.tr, ()))
noncomputable def tD : T.chD.Trs := (ρ.val D.xD, (D.dD.tr, D.tH))
noncomputable def tF : T.chF.Trs :=
  ((Johnson.L5.Layers.rd ρ T.np D.mx, ρ.val D.xF), (D.dF.tr, D.tD))
noncomputable def tZ : T.chZ.Trs := (Johnson.L5.Layers.rd ρ T.nz D.pts, D.tF)
noncomputable def tVD : (T.sVD.stage T.sVD.Out T.chZ).Trs := (D.dVD.tr, D.tZ)
noncomputable def tV : T.chV.Trs := (ρ.val D.xV, (D.dVM.tr, D.tVD))

/-- A transcript for each of the eleven stages. -/
noncomputable def trs : T.ch.Trs := (D.dE.tr, D.tV)

/-- What the eleven stages owe. -/
def Owes (m : M) : Prop :=
  T.sE.L x D.dE.rd m ∧ T.sE.Out (D.dE.nx x) m ∧
  T.sVM.L (D.x2 x) D.dVM.rd m ∧ T.sVM.Out (D.x3 x) m ∧
  T.sVD.L (D.x3 x) D.dVD.rd m ∧ T.sVD.Out (D.dVD.nx (D.x3 x)) m ∧
  T.lF (D.x5 x) (Johnson.L5.Layers.rd ρ T.np D.mx) m ∧
  T.sF.L (D.x6 x) D.dF.rd m ∧ T.owF (D.dF.nx (D.x6 x)) m ∧
  T.sD.L (D.x8 x) D.dD.rd m ∧ T.sD.Out (D.dD.nx (D.x8 x)) m ∧
  T.sH.L (D.x10 x) D.dH.rd m ∧ T.sH.Out (D.dH.nx (D.x10 x)) m

end TailH

theorem tail_owed {X : Type} (T : Tail K M X) (D : TailH ρ T) (x : X) (m : M)
    (h : D.Claims x) : T.ch.Owed x D.trs m ↔ D.Owes x m := by
  have e6 := owed_stage ρ T.sH D.dH T.sH.Out (.done _) (D.x10 x) () m h.cH
  have e5 := owed_stage ρ T.sD D.dD T.sD.Out T.chH (D.x8 x) D.tH m h.cD
  have e4 := owed_stage ρ T.sF D.dF T.owF T.chD (D.x6 x) D.tD m h.cF
  have e3 := owed_stage ρ T.sVD D.dVD T.sVD.Out T.chZ (D.x3 x) D.tZ m h.cVD
  have e2 := owed_stage ρ T.sVM D.dVM T.sVM.Out (T.sVD.stage T.sVD.Out T.chZ) (D.x2 x) D.tVD m
    h.cVM
  have e1 := owed_stage ρ T.sE D.dE T.sE.Out T.chV x D.tV m h.cE
  have f6 : T.chH.Owed (D.dD.nx (D.x8 x)) D.tH m ↔
      T.sH.L (D.x10 x) D.dH.rd m ∧ T.sH.Out (D.dH.nx (D.x10 x)) m :=
    e6.trans (and_congr_right' (and_iff_left trivial))
  have f5 : T.chD.Owed (D.dF.nx (D.x6 x)) D.tD m ↔ _ :=
    e5.trans (and_congr_right' (and_congr_right' f6))
  have f4 : T.chZ.Owed (D.dVD.nx (D.x3 x)) D.tZ m ↔
      T.lF (D.x5 x) (Johnson.L5.Layers.rd ρ T.np D.mx) m ∧ _ :=
    and_congr_right' (e4.trans (and_congr_right' (and_congr_right' f5)))
  have f2 : T.chV.Owed (D.dE.nx x) D.tV m ↔ _ :=
    e2.trans (and_congr_right' (and_congr_right' (e3.trans (and_congr_right'
      (and_congr_right' f4)))))
  exact e1.trans (and_congr_right' (and_congr_right' f2))

/-! ## The score units -/

/-- What the score units have heard. -/
def UnitsH {X : Type} : List (SumL K M (Seen K X)) → Type
  | [] => Unit
  | u :: us => SumH ρ u × UnitsH us

variable {ρ}

/-- The first statement and the units' riders, behind the units. -/
def seenAfter {X : Type} : (us : List (SumL K M (Seen K X))) → UnitsH ρ us → Seen K X → Seen K X
  | [], _, s => s
  | _ :: us, d, s => seenAfter us d.2 (s.1, s.2 ++ [List.ofFn d.1.rd])

/-- The units' claims, each at what it has seen. -/
def UnitsClaims {X : Type} : (us : List (SumL K M (Seen K X))) → UnitsH ρ us → Seen K X → Prop
  | [], _, _ => True
  | _ :: us, d, s => d.1.Claim s ∧ UnitsClaims us d.2 (s.1, s.2 ++ [List.ofFn d.1.rd])

/-- What the units owe. -/
def UnitsOwed {X : Type} : (us : List (SumL K M (Seen K X))) → UnitsH ρ us → Seen K X → M → Prop
  | [], _, _, _ => True
  | u :: us, d, s, m => u.L s d.1.rd m ∧ u.T.our.par.OutHolds d.1.out (u.msg m) ∧
      UnitsOwed us d.2 (s.1, s.2 ++ [List.ofFn d.1.rd]) m

/-- A transcript for each stage: the units', then the rest's. -/
noncomputable def unitsTrs {X : Type} (tail : Ch K M (Seen K X)) (ts : tail.Trs) :
    (us : List (SumL K M (Seen K X))) → UnitsH ρ us → {X' : Type} → (pr : X' → Seen K X) →
      (unitsCh us pr tail).Trs
  | [], _, _, pr => tail.trsComap pr ts
  | _ :: us, d, _, _ => (d.1.tr, unitsTrs tail ts us d.2 _)

theorem units_owed {X : Type} (tail : Ch K M (Seen K X)) (ts : tail.Trs) (m : M) :
    ∀ (us : List (SumL K M (Seen K X))) (d : UnitsH ρ us) {X' : Type} (pr : X' → Seen K X)
      (x : X'), UnitsClaims us d (pr x) →
      ((unitsCh us pr tail).Owed x (unitsTrs tail ts us d pr) m ↔
        UnitsOwed us d (pr x) m ∧ tail.Owed (seenAfter us d (pr x)) ts m)
  | [], _, _, pr, x, _ => (Ch.owed_comap tail pr x ts m).trans (and_iff_right trivial).symm
  | u :: us, d, _, pr, x, h => by
    have ih := units_owed tail ts m us d.2
      (fun b : (_ × (Fin u.n → K)) × u.T.our.par.Out =>
        ((pr b.1.1).1, (pr b.1.1).2 ++ [List.ofFn b.1.2])) ((x, d.1.rd), d.1.out) h.2
    show u.L (pr x) d.1.rd m ∧
      u.T.our.par.OutHolds (shortV u.T.our.par u.T.fix (u.cl (pr x) d.1.rd)
        (unrideN u.T.our.par u.n d.1.tr)) (u.msg m) ∧
      (unitsCh us _ tail).Owed ((x, d.1.rd), shortV u.T.our.par u.T.fix (u.cl (pr x) d.1.rd)
        (unrideN u.T.our.par u.n d.1.tr)) (unitsTrs tail ts us d.2 _) m ↔ _
    rw [show u.cl (pr x) d.1.rd = (ρ.val d.1.t, d.1.st) from h.1]
    exact (and_congr_right' (and_congr_right' ih)).trans (by
      simp only [UnitsOwed, seenAfter, and_assoc]
      exact Iff.rfl)

/-! ## The whole -/

section Whole
variable {X : Type} (A : AttOwn K M X) (du : UnitsH ρ A.units) (dt : TailH ρ A.tail)

/-- A transcript for each stage of the own rounds. -/
noncomputable def ownTrs : A.ch.Trs := unitsTrs A.tail.ch dt.trs A.units du _

/-- What the verifier of the own rounds puts out on the joined transcript. -/
theorem own_out (Ex : ExtSpec) (x : X) (y : Ex.Str) :
    (A.ch.R Ex).red.out (x, y) (A.ch.join Ex (ownTrs A du dt)) =
      some (A.ch.run x (ownTrs A du dt), y) :=
  Ch.out_join Ex A.ch (attOwn_fixOK A) x y _

/-- What the chain claims at its end, stage by stage. -/
theorem own_last (Dn : X → M → Prop) (x : X) (m : M) (hu : UnitsClaims A.units du (x, []))
    (ht : dt.Claims (seenAfter A.units du (x, []))) :
    A.ch.Last Dn (A.ch.run x (ownTrs A du dt)) m ↔
      Dn x m ∧ UnitsOwed A.units du (x, []) m ∧ dt.Owes (seenAfter A.units du (x, [])) m :=
  (Ch.last_run A.ch Dn x _ m).trans (and_congr_right' ((units_owed A.tail.ch dt.trs m A.units du
    (fun x => (x, [])) x hu).trans (and_congr_right' (tail_owed ρ A.tail dt _ m ht))))

end Whole

end OnBytes.Tie.Pv.Att

#print axioms OnBytes.Tie.Pv.Att.owed_stage
#print axioms OnBytes.Tie.Pv.Att.tail_owed
#print axioms OnBytes.Tie.Pv.Att.units_owed
#print axioms OnBytes.Tie.Pv.Att.own_out
#print axioms OnBytes.Tie.Pv.Att.own_last
