-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lay/OwnTieL.lean: the chain of a layers' sub-proof's own rounds (Cb/Pv/Lay/Own.lean)
on the typed transcript that is made from what the port has heard: what its verifier puts out, and
what it claims at its end, stage by stage.

The port's routines hear lists of elements. For a reading of the port's elements in the field, this
file makes from such lists a transcript for each stage of the chain, and unfolds the chain's last
claim on the run. It does for the layers what OnBytes/Tie/Pv/Att/OwnTie.lean does for attention.

Main names:
  `StgH ρ S`: for the letters S of one sumcheck: the further scalars and what the sumcheck has heard
    (`PscH`, OnBytes/Tie/Pv/Att/HearStages.lean); that the reading of beta is not 0; the end values
    under their names; a public state st and an element t.
  `StgH.rd`, `StgH.tr`, `StgH.out`, `StgH.nx`: the further scalars read; the stage's transcript
    (`sumTr`, OnBytes/Tie/Pv/Lay/SumTie.lean); `sumOut` at (the reading of t, st); the statement
    behind the stage.
  `StgH.Claim`: the letters' claim at a statement and the further scalars read is (the reading of t,
    st). This is what a value of the letters has to show, with t the port's record's target.
  `owed_stage`: what a sumcheck's stage owes on that transcript, under `StgH.Claim`.
  `TailH`, `TailH.trs`, `TailH.Claims`, `TailH.Owes`, `tail_owed`: the stages from the limbs'
    scalars on: seven sumchecks, three rounds of sent scalars, four draws of an element, two draws
    of a point.
  `ownTrs`, `own_out`, `own_last`: a sub-proof that is not the first: the token point, then these
    stages: the reduction of the chain, on the joined transcript, puts out the chain's run, if every
    pick is lawful; and the chain's last claim on that output holds exactly if the claim carried
    along holds and the stages' debts do.
  `ownTrsF`, `own_outF`, `own_lastF`: the same for the first sub-proof, with its two further points.

Limits: no routine of the port occurs here. That the lists are what a run has heard, what each
`sumOut` is in the port's records (OnBytes/Tie/Pv/Lay/SumSaid.lean, SumTop.lean, LevelTie.lean,
MergeTie.lean), that the reading of each beta is not 0, every `StgH.Claim`, and that the picks are
lawful are premises. Nothing is said on soundness or knowledge soundness.
-/
import OnBytes.Tie.Pv.Lay.SumTie
import OnBytes.Tie.Pv.Att.HearStages
import Cb.Pv.Att.ChainLast
import Cb.Pv.Lay.Own

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Lay.Eng
open Iop Prob Cb TWhole OnBytes OnBytes.Model Johnson.L5.Layers Cb.Pv.Att Cb.Pv.Lay
open OnBytes.Tie.Pv.Att (PscH)

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K) {M : Type}

/-- What one sumcheck has heard, with what the typed side adds. -/
structure StgH {X : Type} (S : Stg K M X) where
  r : List E
  H : PscH
  b : ρ.val H.beta ≠ 0
  v : S.L.S.A → K
  st : S.L.St
  t : E

namespace StgH
variable {ρ} {X : Type} {S : Stg K M X} (D : StgH ρ S)

/-- the further scalars, read -/
def rd : Fin S.n → K := Johnson.L5.Layers.rd ρ S.n D.r

/-- the stage's transcript -/
noncomputable def tr : Tr (shapeRN S.L.T.par S.n) :=
  (((), (D.rd, ρ.val D.H.mu)), ρ.val D.H.eps,
    sumTr ρ S.L D.H.rs D.H.sentY D.H.beta D.b D.v)

/-- the sumcheck's output -/
noncomputable def out : S.L.T.par.Out :=
  sumOut ρ S.L S.F D.st D.t D.H.mu D.H.eps D.H.rs D.H.sentY D.H.beta D.b D.v

/-- the statement behind the stage -/
noncomputable def nx (x : X) : S.Nx := ((x, D.rd), D.out)

/-- the letters' claim at x and the further scalars read -/
def Claim (x : X) : Prop := S.cl x D.rd = (ρ.val D.t, D.st)

end StgH

/-- What a sumcheck's stage owes on the transcript made from what was heard. -/
theorem owed_stage {X : Type} (S : Stg K M X) (D : StgH ρ S) (Ow : S.Nx → M → Prop)
    (next : Ch K M S.Nx) (x : X) (ts : next.Trs) (m : M) (h : D.Claim x) :
    (S.stage Ow next).Owed x (D.tr, ts) m ↔
      S.Lc x D.rd m ∧ Ow (D.nx x) m ∧ next.Owed (D.nx x) ts m := by
  show S.Lc x D.rd m ∧
    Ow ((x, D.rd), shortV S.L.T.par S.F (S.cl x D.rd) (unrideN S.L.T.par S.n D.tr)) m ∧
    next.Owed ((x, D.rd), shortV S.L.T.par S.F (S.cl x D.rd)
      (unrideN S.L.T.par S.n D.tr)) ts m ↔ _
  rw [show S.cl x D.rd = (ρ.val D.t, D.st) from h]
  exact Iff.rfl

/-! ## The stages from the limbs' scalars on -/

/-- What these stages have heard. -/
structure TailH {X : Type} (T : LayTail K M X) where
  sL : List E
  xL : E
  pN : List E
  d1 : StgH ρ T.s1
  x1 : E
  sP : List E
  xP : E
  d2 : StgH ρ T.s2
  d3 : StgH ρ T.s3
  x4 : E
  d4 : StgH ρ T.s4
  d5 : StgH ρ T.s5
  x5 : E
  pR : List E
  d6 : StgH ρ T.s6
  x6 : E
  sW : List E
  xW : E
  d7 : StgH ρ T.s7

namespace TailH
variable {ρ} {X : Type} {T : LayTail K M X} (D : TailH ρ T) (x : X)

def rL : Fin T.nL → K := Johnson.L5.Layers.rd ρ T.nL D.sL
def rN : Fin T.gN → K := Johnson.L5.Layers.rd ρ T.gN D.pN
def rP : Fin T.nP → K := Johnson.L5.Layers.rd ρ T.nP D.sP
def rR : Fin T.gR → K := Johnson.L5.Layers.rd ρ T.gR D.pR
def rW : Fin T.nW → K := Johnson.L5.Layers.rd ρ T.nW D.sW

/-- The statements that the stages find. -/
def y1 : ((X × (Fin T.nL → K)) × K) × (Fin T.gN → K) := (((x, D.rL), ρ.val D.xL), D.rN)
noncomputable def z1 : T.s1.Nx := D.d1.nx (D.y1 x)
noncomputable def y2 : ((T.s1.Nx × K) × (Fin T.nP → K)) × K :=
  (((D.z1 x, ρ.val D.x1), D.rP), ρ.val D.xP)
noncomputable def z2 : T.s2.Nx := D.d2.nx (D.y2 x)
noncomputable def z3 : T.s3.Nx := D.d3.nx (D.z2 x)
noncomputable def y4 : T.s3.Nx × K := (D.z3 x, ρ.val D.x4)
noncomputable def z4 : T.s4.Nx := D.d4.nx (D.y4 x)
noncomputable def z5 : T.s5.Nx := D.d5.nx (D.z4 x)
noncomputable def y6 : (T.s5.Nx × K) × (Fin T.gR → K) := ((D.z5 x, ρ.val D.x5), D.rR)
noncomputable def z6 : T.s6.Nx := D.d6.nx (D.y6 x)
noncomputable def y7 : ((T.s6.Nx × K) × (Fin T.nW → K)) × K :=
  (((D.z6 x, ρ.val D.x6), D.rW), ρ.val D.xW)
noncomputable def z7 : T.s7.Nx := D.d7.nx (D.y7 x)

/-- The letters' claims, each at the statement that its stage finds. -/
structure Claims : Prop where
  c1 : D.d1.Claim (D.y1 x)
  c2 : D.d2.Claim (D.y2 x)
  c3 : D.d3.Claim (D.z2 x)
  c4 : D.d4.Claim (D.y4 x)
  c5 : D.d5.Claim (D.z4 x)
  c6 : D.d6.Claim (D.y6 x)
  c7 : D.d7.Claim (D.y7 x)

/-- The stages' transcripts, from the back. -/
noncomputable def tW : T.chW.Trs := ((D.rW, ρ.val D.xW), (D.d7.tr, ()))
noncomputable def t6 : T.ch6.Trs := (D.d6.tr, (ρ.val D.x6, D.tW))
noncomputable def t5 : T.ch5.Trs := (D.d5.tr, (ρ.val D.x5, (D.rR, D.t6)))
noncomputable def t4 : T.ch4.Trs := (ρ.val D.x4, (D.d4.tr, D.t5))
noncomputable def tP : T.chP.Trs := ((D.rP, ρ.val D.xP), (D.d2.tr, (D.d3.tr, D.t4)))
noncomputable def t1 : T.ch1.Trs := (D.d1.tr, (ρ.val D.x1, D.tP))

/-- A transcript for each stage. -/
noncomputable def trs : T.ch.Trs := ((D.rL, ρ.val D.xL), (D.rN, D.t1))

/-- What the stages owe. -/
def Owes (m : M) : Prop :=
  T.lL x D.rL m ∧
  T.s1.Lc (D.y1 x) D.d1.rd m ∧ T.ow1 (D.z1 x) m ∧
  T.lP (D.z1 x, ρ.val D.x1) D.rP m ∧
  T.s2.Lc (D.y2 x) D.d2.rd m ∧ T.ow2 (D.z2 x) m ∧
  T.s3.Lc (D.z2 x) D.d3.rd m ∧ T.ow3 (D.z3 x) m ∧
  T.s4.Lc (D.y4 x) D.d4.rd m ∧ T.ow4 (D.z4 x) m ∧
  T.s5.Lc (D.z4 x) D.d5.rd m ∧ T.ow5 (D.z5 x) m ∧
  T.s6.Lc (D.y6 x) D.d6.rd m ∧ T.ow6 (D.z6 x) m ∧
  T.lW (D.z6 x, ρ.val D.x6) D.rW m ∧
  T.s7.Lc (D.y7 x) D.d7.rd m ∧ T.s7.Out (D.z7 x) m

end TailH

theorem tail_owed {X : Type} (T : LayTail K M X) (D : TailH ρ T) (x : X) (m : M)
    (h : D.Claims x) : T.ch.Owed x D.trs m ↔ D.Owes x m := by
  have e7 := owed_stage ρ T.s7 D.d7 T.s7.Out (.done _) (D.y7 x) () m h.c7
  have e6 := owed_stage ρ T.s6 D.d6 T.ow6 (.draw (dE K) 1 T.p6 T.chW) (D.y6 x)
    (ρ.val D.x6, D.tW) m h.c6
  have e5 := owed_stage ρ T.s5 D.d5 T.ow5
    (.draw (dE K) 1 T.p5 (.draw (dPt K T.gR) T.eR T.pR T.ch6)) (D.z4 x)
    (ρ.val D.x5, (D.rR, D.t6)) m h.c5
  have e4 := owed_stage ρ T.s4 D.d4 T.ow4 T.ch5 (D.y4 x) D.t5 m h.c4
  have e3 := owed_stage ρ T.s3 D.d3 T.ow3 T.ch4 (D.z2 x) D.t4 m h.c3
  have e2 := owed_stage ρ T.s2 D.d2 T.ow2 (T.s3.stage T.ow3 T.ch4) (D.y2 x) (D.d3.tr, D.t4) m
    h.c2
  have e1 := owed_stage ρ T.s1 D.d1 T.ow1 (.draw (dE K) 1 T.p1 T.chP) (D.y1 x)
    (ρ.val D.x1, D.tP) m h.c1
  have f7 : T.chW.Owed (D.z6 x, ρ.val D.x6) D.tW m ↔
      T.lW (D.z6 x, ρ.val D.x6) D.rW m ∧ T.s7.Lc (D.y7 x) D.d7.rd m ∧ T.s7.Out (D.z7 x) m :=
    and_congr_right' (e7.trans (and_congr_right' (and_iff_left trivial)))
  have f6 : T.ch6.Owed (D.y6 x) D.t6 m ↔ _ :=
    e6.trans (and_congr_right' (and_congr_right' f7))
  have f5 : T.ch5.Owed (D.z4 x) D.t5 m ↔ _ :=
    e5.trans (and_congr_right' (and_congr_right' f6))
  have f4 : T.ch4.Owed (D.z3 x) D.t4 m ↔ _ :=
    e4.trans (and_congr_right' (and_congr_right' f5))
  have f3 : (T.s3.stage T.ow3 T.ch4).Owed (D.z2 x) (D.d3.tr, D.t4) m ↔ _ :=
    e3.trans (and_congr_right' (and_congr_right' f4))
  have fP : T.chP.Owed (D.z1 x, ρ.val D.x1) D.tP m ↔
      T.lP (D.z1 x, ρ.val D.x1) D.rP m ∧ _ :=
    and_congr_right' (e2.trans (and_congr_right' (and_congr_right' f3)))
  have f1 : T.ch1.Owed (D.y1 x) D.t1 m ↔ _ :=
    e1.trans (and_congr_right' (and_congr_right' fP))
  exact and_congr_right' f1

/-! ## The whole -/

section Whole
variable {ρ} {X : Type}

/-- A transcript for each stage of the own rounds of a sub-proof that is not the first. -/
noncomputable def ownTrs (A : LayOwn K M X) (pT : List E) (D : TailH ρ A.tail) : A.ch.Trs :=
  (Johnson.L5.Layers.rd ρ A.gT pT, D.trs)

theorem own_out (A : LayOwn K M X) (pT : List E) (D : TailH ρ A.tail) (hF : A.ch.FixOK)
    (Ex : ExtSpec) (x : X) (y : Ex.Str) :
    (A.ch.R Ex).red.out (x, y) (A.ch.join Ex (ownTrs A pT D)) =
      some (A.ch.run x (ownTrs A pT D), y) :=
  Ch.out_join Ex A.ch hF x y _

theorem own_last (A : LayOwn K M X) (pT : List E) (D : TailH ρ A.tail) (Dn : X → M → Prop)
    (x : X) (m : M) (h : D.Claims (x, Johnson.L5.Layers.rd ρ A.gT pT)) :
    A.ch.Last Dn (A.ch.run x (ownTrs A pT D)) m ↔
      Dn x m ∧ D.Owes (x, Johnson.L5.Layers.rd ρ A.gT pT) m :=
  (Ch.last_run A.ch Dn x _ m).trans (and_congr_right' (tail_owed ρ A.tail D _ m h))

/-- The same for the first sub-proof. -/
noncomputable def ownTrsF (A : LayOwnFirst K M X) (pT pA pB : List E) (D : TailH ρ A.tail) :
    A.ch.Trs :=
  (Johnson.L5.Layers.rd ρ A.gT pT, (Johnson.L5.Layers.rd ρ A.gA pA,
    (Johnson.L5.Layers.rd ρ A.gB pB, D.trs)))

theorem own_outF (A : LayOwnFirst K M X) (pT pA pB : List E) (D : TailH ρ A.tail)
    (hF : A.ch.FixOK) (Ex : ExtSpec) (x : X) (y : Ex.Str) :
    (A.ch.R Ex).red.out (x, y) (A.ch.join Ex (ownTrsF A pT pA pB D)) =
      some (A.ch.run x (ownTrsF A pT pA pB D), y) :=
  Ch.out_join Ex A.ch hF x y _

theorem own_lastF (A : LayOwnFirst K M X) (pT pA pB : List E) (D : TailH ρ A.tail)
    (Dn : X → M → Prop) (x : X) (m : M)
    (h : D.Claims (((x, Johnson.L5.Layers.rd ρ A.gT pT), Johnson.L5.Layers.rd ρ A.gA pA),
      Johnson.L5.Layers.rd ρ A.gB pB)) :
    A.ch.Last Dn (A.ch.run x (ownTrsF A pT pA pB D)) m ↔
      Dn x m ∧ D.Owes (((x, Johnson.L5.Layers.rd ρ A.gT pT), Johnson.L5.Layers.rd ρ A.gA pA),
        Johnson.L5.Layers.rd ρ A.gB pB) m :=
  (Ch.last_run A.ch Dn x _ m).trans (and_congr_right' (tail_owed ρ A.tail D _ m h))

end Whole

end OnBytes.Tie.Pv.Lay.Eng

#print axioms OnBytes.Tie.Pv.Lay.Eng.owed_stage
#print axioms OnBytes.Tie.Pv.Lay.Eng.tail_owed
#print axioms OnBytes.Tie.Pv.Lay.Eng.own_out
#print axioms OnBytes.Tie.Pv.Lay.Eng.own_last
#print axioms OnBytes.Tie.Pv.Lay.Eng.own_outF
#print axioms OnBytes.Tie.Pv.Lay.Eng.own_lastF
