-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/OwnView.lean: WHAT THE CHAIN OF A LAYERS' SUB-PROOF'S OWN ROUNDS PUTS OUT AT
THE IMAGE OF A WRITTEN TRANSCRIPT, BY NAME: the statement `TailH.z7`
(OnBytes/Tie/Pv/Lay/OwnTieL.lean) of data D of words, if D's words are the written rounds' words.
Definitions, statements and proofs. Bookkeeping: no text is read and no count is made.

  `send_view`, `point_view`, `draw_view`: the image of one written round under `mSend`, `mPoint`,
    `mDraw`: the words sent and drawn (`sentE`, `drawnE`, RoundRead.lean), read by `gl`.
  `StgM.Ok`: of a tie W of a stage S to written rounds r (OwnMaps.lean): every message of r holds
    elements alone; r has as many variables' rounds as S has variables; these are of degree 2; the
    further variable's degree is W's.
  `StgWords D W x`: the data D of a stage (`StgH`) are the words of the written rounds' transcript
    x. `stage_is`: then the image of x under the chain's maps is `D.tr`.
  `TailR.lW` … `TailR.l1`, `TailM.mW` … `TailM.m1`: the written rounds and the data of ChMaps.lean
    from each of the library's six cuts of the chain on (`LayTail.chW` … `ch1`).
  `TailR.xL` … `TailR.x7`: the sixteen cuts of a written transcript, one for each stage.
  `TailWords W τ D`: D's words are those of the sixteen cuts. `trs_eq`: then the stages' own images
    (`ChM.trs`, ChView.lean) are `D.trs`.
  `own_val_z7`: a sub-proof that is not the first: under `TailWords`, the token point's words and
    `TailH.Claims`: `(A.ch.val Ex (x, y) (((ownM A dT W).mapsR Ex).view τ)).1 = D.z7 (x, …)`.

NO NEW ARGUMENT: `stage_view` (StageView.lean), `ChM.val_view` (ChView.lean), `own_run_z7`
(TailRun.lean), stage by stage.

Limits. `StgM.Ok`, `TailWords` and `TailH.Claims` ARE PREMISES: nothing here shows that a plan's
rounds, a text's tape or a value of the chain's letters meet them. D's states and targets
(`StgH.st`, `StgH.t`) are tied to nothing here: `TailH.Claims` ties them. At every written
transcript, also where a test of work fails. A sub-proof that is not the first. Nothing on
soundness.
-/
import OnBytes.Desc.First.P1.StageView
import OnBytes.Desc.First.P1.OwnMaps
import OnBytes.Desc.First.P1.TailRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P1
open Iop Prob IOR Cb TWhole Cb.Pv.Lay Cb.Pv.Att Johnson.L5.Layers Johnson.L5.Door
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Tie.Pv.Lay.Eng (StgH TailH ownTrs sumTr)
open _root_.Run (ckP)

local notation "z0" => OnBytes.zeroE

variable {M : Type}

/-! ### One written round -/

theorem send_view (n : ℕ) {d : RDT} (hd : AllE d) (x : Tr (uLT (ckP .two) [d])) :
    (((Maps.step (mSend n d) .nil).view x).1.2, ((Maps.step (mSend n d) .nil).view x).2.1) =
      (rd gl n (sentE d x.1), gl.val ((drawnE d x.2.1).headD z0)) := by
  obtain ⟨m, c, u⟩ := x
  exact Prod.ext (funext fun i => (sent_at d m hd i.val).symm) (drawn_head d m c).symm

theorem point_view (g : ℕ) (d : RDT) (x : Tr (uLT (ckP .two) [d])) :
    ((Maps.step (mPoint g d) .nil).view x).2.1 = rd gl g (drawnE d x.2.1) := by
  obtain ⟨m, c, u⟩ := x
  exact (drawn_vec d m c g).symm

theorem draw_view (d : RDT) (x : Tr (uLT (ckP .two) [d])) :
    ((Maps.step (mDraw d) .nil).view x).2.1 = gl.val ((drawnE d x.2.1).headD z0) := by
  obtain ⟨m, c, u⟩ := x
  exact (drawn_head d m c).symm

/-! ### One sumcheck -/

/-- What is asked of a tie of a stage to written rounds. -/
structure StgM.Ok {X : Type} {S : Stg GE M X} {r : ScR} (W : StgM S r) : Prop where
  e : AllE r.dE
  vs : ∀ d ∈ r.vs, AllE d
  y : AllE r.dY
  v : AllE r.dV
  k : r.vs.length = S.L.S.k
  n : ∀ i, S.L.M.n i = 2
  dy : W.DY = S.L.M.DY

/-- The data of a stage are the words of the written rounds' transcript. -/
structure StgWords {X : Type} {S : Stg GE M X} {r : ScR} (D : StgH gl S) (W : StgM S r)
    (x : Tr (uLT (ckP .two) r.all)) : Prop where
  rid : rd gl S.n D.r = rd gl S.n (sentE r.dE x.1)
  mu : D.H.mu = (sentE r.dE x.1).getD S.n z0
  eps : D.H.eps = (drawnE r.dE x.2.1).headD z0
  rs : D.H.rs = midRs r.dY r.dV r.vs x.2.2
  sentY : D.H.sentY = (midY r.dY r.dV r.vs x.2.2).1
  beta : D.H.beta = (midY r.dY r.dV r.vs x.2.2).2
  v : D.v = fun a => gl.val ((midV r.dY r.dV r.vs x.2.2).getD (W.num a) z0)

theorem sumTr_congr (L : SumL GE) {rs rs' : List (List OnBytes.E × OnBytes.E)}
    {sY sY' : List OnBytes.E} {b b' : OnBytes.E} {hb : gl.val b ≠ 0} {hb' : gl.val b' ≠ 0}
    {v v' : L.S.A → GE} (h1 : rs = rs') (h2 : sY = sY') (h3 : b = b') (h4 : v = v') :
    sumTr gl L rs sY b hb v = sumTr gl L rs' sY' b' hb' v' := by
  subst h1
  subst h2
  subst h3
  subst h4
  rfl

/-- **The image of a sumcheck's written rounds is the stage's transcript of the data.** -/
theorem stage_is {X : Type} {S : Stg GE M X} {r : ScR} {D : StgH gl S} {W : StgM S r}
    (ok : W.Ok) {x : Tr (uLT (ckP .two) r.all)} (h : StgWords D W x) :
    (ChM.rideMaps S.L.T.par S.n r.dE r.vs r.dY r.dV W.DY W.num W.hf).view x = D.tr := by
  have hβ : gl.val (midY r.dY r.dV r.vs x.2.2).2 ≠ 0 := by
    rw [← h.beta]
    exact D.b
  have e := stage_view S.L S.n W.DY W.num W.hf ok.e ok.vs ok.y ok.v ok.k ok.n ok.dy x.1 x.2.1
    x.2.2 hβ
  refine e.trans ?_
  show _ = (((), (rd gl S.n D.r, gl.val D.H.mu)), gl.val D.H.eps,
    sumTr gl S.L D.H.rs D.H.sentY D.H.beta D.b D.v)
  have es : sumTr gl S.L D.H.rs D.H.sentY D.H.beta D.b D.v =
      sumTr gl S.L (midRs r.dY r.dV r.vs x.2.2) (midY r.dY r.dV r.vs x.2.2).1
        (midY r.dY r.dV r.vs x.2.2).2 hβ
        fun a => gl.val ((midV r.dY r.dV r.vs x.2.2).getD (W.num a) z0) :=
    sumTr_congr S.L h.rs h.sentY h.beta h.v
  rw [h.rid, h.mu, h.eps, es]

/-! ### The written rounds and the data, from each of the library's cuts of the chain on -/

namespace TailR
variable (R : TailR)

abbrev lW : List RDT := [R.dW] ++ (R.r7.all ++ [])
abbrev l6 : List RDT := R.r6.all ++ ([R.t6] ++ R.lW)
abbrev l5 : List RDT := R.r5.all ++ ([R.t5] ++ ([R.dR] ++ R.l6))
abbrev l4 : List RDT := [R.d4] ++ (R.r4.all ++ R.l5)
abbrev lP : List RDT := [R.dP] ++ (R.r2.all ++ (R.r3.all ++ R.l4))
abbrev l1 : List RDT := R.r1.all ++ ([R.t1] ++ R.lP)

theorem all_eq : R.all = [R.dL] ++ ([R.dN] ++ R.l1) := rfl

/-! The cuts of a written transcript. -/

def c1 (τ : Tr (uLT (ckP .two) R.all)) : Tr (uLT (ckP .two) R.l1) :=
  Maps.trR [R.dN] R.l1 (Maps.trR [R.dL] ([R.dN] ++ R.l1) τ)
def cP (τ : Tr (uLT (ckP .two) R.all)) : Tr (uLT (ckP .two) R.lP) :=
  Maps.trR [R.t1] R.lP (Maps.trR R.r1.all ([R.t1] ++ R.lP) (R.c1 τ))
def c4 (τ : Tr (uLT (ckP .two) R.all)) : Tr (uLT (ckP .two) R.l4) :=
  Maps.trR R.r3.all R.l4 (Maps.trR R.r2.all (R.r3.all ++ R.l4)
    (Maps.trR [R.dP] (R.r2.all ++ (R.r3.all ++ R.l4)) (R.cP τ)))
def c5 (τ : Tr (uLT (ckP .two) R.all)) : Tr (uLT (ckP .two) R.l5) :=
  Maps.trR R.r4.all R.l5 (Maps.trR [R.d4] (R.r4.all ++ R.l5) (R.c4 τ))
def c6 (τ : Tr (uLT (ckP .two) R.all)) : Tr (uLT (ckP .two) R.l6) :=
  Maps.trR [R.dR] R.l6 (Maps.trR [R.t5] ([R.dR] ++ R.l6)
    (Maps.trR R.r5.all ([R.t5] ++ ([R.dR] ++ R.l6)) (R.c5 τ)))
def cW (τ : Tr (uLT (ckP .two) R.all)) : Tr (uLT (ckP .two) R.lW) :=
  Maps.trR [R.t6] R.lW (Maps.trR R.r6.all ([R.t6] ++ R.lW) (R.c6 τ))

def xL (τ : Tr (uLT (ckP .two) R.all)) : Tr (uLT (ckP .two) [R.dL]) :=
  Maps.trL [R.dL] ([R.dN] ++ R.l1) τ
def xN (τ : Tr (uLT (ckP .two) R.all)) : Tr (uLT (ckP .two) [R.dN]) :=
  Maps.trL [R.dN] R.l1 (Maps.trR [R.dL] ([R.dN] ++ R.l1) τ)
def x1 (τ : Tr (uLT (ckP .two) R.all)) : Tr (uLT (ckP .two) R.r1.all) :=
  Maps.trL R.r1.all ([R.t1] ++ R.lP) (R.c1 τ)
def y1 (τ : Tr (uLT (ckP .two) R.all)) : Tr (uLT (ckP .two) [R.t1]) :=
  Maps.trL [R.t1] R.lP (Maps.trR R.r1.all ([R.t1] ++ R.lP) (R.c1 τ))
def xP (τ : Tr (uLT (ckP .two) R.all)) : Tr (uLT (ckP .two) [R.dP]) :=
  Maps.trL [R.dP] (R.r2.all ++ (R.r3.all ++ R.l4)) (R.cP τ)
def x2 (τ : Tr (uLT (ckP .two) R.all)) : Tr (uLT (ckP .two) R.r2.all) :=
  Maps.trL R.r2.all (R.r3.all ++ R.l4) (Maps.trR [R.dP] (R.r2.all ++ (R.r3.all ++ R.l4)) (R.cP τ))
def x3 (τ : Tr (uLT (ckP .two) R.all)) : Tr (uLT (ckP .two) R.r3.all) :=
  Maps.trL R.r3.all R.l4 (Maps.trR R.r2.all (R.r3.all ++ R.l4)
    (Maps.trR [R.dP] (R.r2.all ++ (R.r3.all ++ R.l4)) (R.cP τ)))
def y4 (τ : Tr (uLT (ckP .two) R.all)) : Tr (uLT (ckP .two) [R.d4]) :=
  Maps.trL [R.d4] (R.r4.all ++ R.l5) (R.c4 τ)
def x4 (τ : Tr (uLT (ckP .two) R.all)) : Tr (uLT (ckP .two) R.r4.all) :=
  Maps.trL R.r4.all R.l5 (Maps.trR [R.d4] (R.r4.all ++ R.l5) (R.c4 τ))
def x5 (τ : Tr (uLT (ckP .two) R.all)) : Tr (uLT (ckP .two) R.r5.all) :=
  Maps.trL R.r5.all ([R.t5] ++ ([R.dR] ++ R.l6)) (R.c5 τ)
def y5 (τ : Tr (uLT (ckP .two) R.all)) : Tr (uLT (ckP .two) [R.t5]) :=
  Maps.trL [R.t5] ([R.dR] ++ R.l6) (Maps.trR R.r5.all ([R.t5] ++ ([R.dR] ++ R.l6)) (R.c5 τ))
def xR (τ : Tr (uLT (ckP .two) R.all)) : Tr (uLT (ckP .two) [R.dR]) :=
  Maps.trL [R.dR] R.l6 (Maps.trR [R.t5] ([R.dR] ++ R.l6)
    (Maps.trR R.r5.all ([R.t5] ++ ([R.dR] ++ R.l6)) (R.c5 τ)))
def x6 (τ : Tr (uLT (ckP .two) R.all)) : Tr (uLT (ckP .two) R.r6.all) :=
  Maps.trL R.r6.all ([R.t6] ++ R.lW) (R.c6 τ)
def y6 (τ : Tr (uLT (ckP .two) R.all)) : Tr (uLT (ckP .two) [R.t6]) :=
  Maps.trL [R.t6] R.lW (Maps.trR R.r6.all ([R.t6] ++ R.lW) (R.c6 τ))
def xW (τ : Tr (uLT (ckP .two) R.all)) : Tr (uLT (ckP .two) [R.dW]) :=
  Maps.trL [R.dW] (R.r7.all ++ []) (R.cW τ)
def x7 (τ : Tr (uLT (ckP .two) R.all)) : Tr (uLT (ckP .two) R.r7.all) :=
  Maps.trL R.r7.all [] (Maps.trR [R.dW] (R.r7.all ++ []) (R.cW τ))

end TailR

namespace TailM
variable {X : Type} {T : LayTail GE M X} {R : TailR} (W : TailM T R)

noncomputable def mW : ChM T.chW R.lW := .send R.dW (W.w7.ride _ (.done _))
noncomputable def m6 : ChM T.ch6 R.l6 := W.w6.ride _ (.draw1 R.t6 W.mW)
noncomputable def m5 : ChM T.ch5 R.l5 := W.w5.ride _ (.draw1 R.t5 (.drawPt R.dR W.m6))
noncomputable def m4 : ChM T.ch4 R.l4 := .draw1 R.d4 (W.w4.ride _ W.m5)
noncomputable def mP : ChM T.chP R.lP := .send R.dP (W.w2.ride _ (W.w3.ride _ W.m4))
noncomputable def m1 : ChM T.ch1 R.l1 := W.w1.ride _ (.draw1 R.t1 W.mP)

theorem chM_eq : W.chM = .send R.dL (.drawPt R.dN W.m1) := rfl

/-- All seven ties are as asked, and the three rounds of sent scalars hold elements alone. -/
structure Ok : Prop where
  l : AllE R.dL
  p : AllE R.dP
  w : AllE R.dW
  s1 : W.w1.Ok
  s2 : W.w2.Ok
  s3 : W.w3.Ok
  s4 : W.w4.Ok
  s5 : W.w5.Ok
  s6 : W.w6.Ok
  s7 : W.w7.Ok

end TailM

/-- The data's words are those of the sixteen cuts of the written transcript. -/
structure TailWords {X : Type} {T : LayTail GE M X} {R : TailR} (W : TailM T R)
    (τ : Tr (uLT (ckP .two) R.all)) (D : TailH gl T) : Prop where
  sL : D.sL = sentE R.dL (R.xL τ).1
  xL : D.xL = (drawnE R.dL (R.xL τ).2.1).headD z0
  pN : D.pN = drawnE R.dN (R.xN τ).2.1
  d1 : StgWords D.d1 W.w1 (R.x1 τ)
  x1 : D.x1 = (drawnE R.t1 (R.y1 τ).2.1).headD z0
  sP : D.sP = sentE R.dP (R.xP τ).1
  xP : D.xP = (drawnE R.dP (R.xP τ).2.1).headD z0
  d2 : StgWords D.d2 W.w2 (R.x2 τ)
  d3 : StgWords D.d3 W.w3 (R.x3 τ)
  x4 : D.x4 = (drawnE R.d4 (R.y4 τ).2.1).headD z0
  d4 : StgWords D.d4 W.w4 (R.x4 τ)
  d5 : StgWords D.d5 W.w5 (R.x5 τ)
  x5 : D.x5 = (drawnE R.t5 (R.y5 τ).2.1).headD z0
  pR : D.pR = drawnE R.dR (R.xR τ).2.1
  d6 : StgWords D.d6 W.w6 (R.x6 τ)
  x6 : D.x6 = (drawnE R.t6 (R.y6 τ).2.1).headD z0
  sW : D.sW = sentE R.dW (R.xW τ).1
  xW : D.xW = (drawnE R.dW (R.xW τ).2.1).headD z0
  d7 : StgWords D.d7 W.w7 (R.x7 τ)

section Trs
variable {X : Type} {T : LayTail GE M X} {R : TailR} {W : TailM T R}
  {τ : Tr (uLT (ckP .two) R.all)} {D : TailH gl T}

theorem trsW (ok : W.Ok) (h : TailWords W τ D) : W.mW.trs (R.cW τ) = D.tW :=
  congrArg₂ Prod.mk
    ((send_view T.nW ok.w (R.xW τ)).trans (by rw [← h.sW, ← h.xW]; rfl))
    (congrArg₂ Prod.mk (stage_is ok.s7 h.d7) rfl)

theorem trs6 (ok : W.Ok) (h : TailWords W τ D) : W.m6.trs (R.c6 τ) = D.t6 :=
  congrArg₂ Prod.mk (stage_is ok.s6 h.d6)
    (congrArg₂ Prod.mk ((draw_view R.t6 (R.y6 τ)).trans (by rw [← h.x6])) (trsW ok h))

theorem trs5 (ok : W.Ok) (h : TailWords W τ D) : W.m5.trs (R.c5 τ) = D.t5 :=
  congrArg₂ Prod.mk (stage_is ok.s5 h.d5)
    (congrArg₂ Prod.mk ((draw_view R.t5 (R.y5 τ)).trans (by rw [← h.x5]))
      (congrArg₂ Prod.mk ((point_view T.gR R.dR (R.xR τ)).trans (by rw [← h.pR]; rfl))
        (trs6 ok h)))

theorem trs4 (ok : W.Ok) (h : TailWords W τ D) : W.m4.trs (R.c4 τ) = D.t4 :=
  congrArg₂ Prod.mk ((draw_view R.d4 (R.y4 τ)).trans (by rw [← h.x4]))
    (congrArg₂ Prod.mk (stage_is ok.s4 h.d4) (trs5 ok h))

theorem trsP (ok : W.Ok) (h : TailWords W τ D) : W.mP.trs (R.cP τ) = D.tP :=
  congrArg₂ Prod.mk
    ((send_view T.nP ok.p (R.xP τ)).trans (by rw [← h.sP, ← h.xP]; rfl))
    (congrArg₂ Prod.mk (stage_is ok.s2 h.d2)
      (congrArg₂ Prod.mk (stage_is ok.s3 h.d3) (trs4 ok h)))

theorem trs1 (ok : W.Ok) (h : TailWords W τ D) : W.m1.trs (R.c1 τ) = D.t1 :=
  congrArg₂ Prod.mk (stage_is ok.s1 h.d1)
    (congrArg₂ Prod.mk ((draw_view R.t1 (R.y1 τ)).trans (by rw [← h.x1])) (trsP ok h))

/-- **The stages' own images are the data's transcripts.** -/
theorem trs_eq (ok : W.Ok) (h : TailWords W τ D) : W.chM.trs τ = D.trs :=
  congrArg₂ Prod.mk
    ((send_view T.nL ok.l (R.xL τ)).trans (by rw [← h.sL, ← h.xL]; rfl))
    (congrArg₂ Prod.mk ((point_view T.gN R.dN (R.xN τ)).trans (by rw [← h.pN]; rfl))
      (trs1 ok h))

end Trs

/-- **What the chain puts out at the image of a written transcript, by name.** -/
theorem own_val_z7 (Ex : ExtSpec) {X : Type} (A : LayOwn GE M X) (dT : RDT) {R : TailR}
    {W : TailM A.tail R} (ok : W.Ok) (τ : Tr (uLT (ckP .two) ([dT] ++ R.all)))
    {pT : List OnBytes.E} {D : TailH gl A.tail}
    (hT : pT = drawnE dT (Maps.trL [dT] R.all τ).2.1)
    (h : TailWords W (Maps.trR [dT] R.all τ) D) (x : X) (y : Ex.Str)
    (hc : D.Claims (x, rd gl A.gT pT)) :
    (A.ch.val Ex (x, y) (((ownM A dT W).mapsR Ex).view τ)).1 = D.z7 (x, rd gl A.gT pT) := by
  rw [ChM.val_view]
  have e : (ownM A dT W).trs τ = ownTrs A pT D :=
    congrArg₂ Prod.mk ((point_view A.gT dT (Maps.trL [dT] R.all τ)).trans (by rw [← hT]))
      (trs_eq ok h)
  show A.ch.run x ((ownM A dT W).trs τ) = _
  rw [e]
  exact own_run_z7 A pT D x hc

end OnBytes.Desc.First.P1

#print axioms OnBytes.Desc.First.P1.stage_is
#print axioms OnBytes.Desc.First.P1.trs_eq
#print axioms OnBytes.Desc.First.P1.own_val_z7
