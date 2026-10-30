-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/P1/OwnMaps.lean: THE WRITTEN ROUNDS OF A LAYERS' SUB-PROOF'S OWN STRETCH, READ
AS THE TYPED ROUNDS OF THE LIBRARY'S CHAIN OF THESE ROUNDS (Cb/Pv/Lay/Own.lean: `LayOwn.ch`,
`LayOwnFirst.ch`). Definitions, and that the maps are as asked. An instance of ChMaps.lean.

  `ScR`: the written rounds of one masked sumcheck: the first, the variables', the further
    variable's, the end values'. `ScR.all`: in a row.
  `StgM S r`: what ties them to a stage S of the chain: that S's formats are as many cube variables
    of degree 2 as r has variables' rounds, then the further variable of degree DY; and a numbering
    of S's end values.
  `TailR`, `TailR.all`: the written rounds of all stages from the limbs' scalars on, in the chain's
    order: the scalars' round, the join's, the squares' sumcheck and its last draw; the products'
    scalars, their sumcheck; the terms' sumcheck; the draw that combines; the batched sumcheck; the
    gated products' and its last draw; the routed join's; the routed gated products' and its last
    draw; the weight claims' round; the merge.
  `TailM T R`, `TailM.chM`: the seven ties, and from them the data of ChMaps.lean for `T.ch`.
  `ownM`, `ownFirstM`: with the token point in front (in the first sub-proof two more points).
  `TailDs`, `TailM.ds`, `ownMaps_ok`, `ownFirstMaps_ok`: what each written round must send and
    draw; then the maps against the shape of the chain's reduction are as asked.

Limits. Shapes and maps alone; no round is skipped. The seven ties and `TailDs` are premises: that
a value of the chain's letters and a plan's stretch meet them is not shown here. Which written
scalar is which typed one is laid down by the maps (in the order in which they are written; the end
values by the numbering) and compared with no text. Nothing on the counts, on the image of a
transcript against what a text has heard, or on any law.
-/
import OnBytes.Desc.First.P1.ChMaps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P1
open Iop Prob IOR Cb TWhole Cb.Pv.Lay Cb.Pv.Att Johnson.L5.Layers Johnson.L5.Door
open OnBytes.Flat OnBytes.Maker OnBytes.Slice

variable {M : Type}

/-- The written rounds of one masked sumcheck. -/
structure ScR where
  dE : RDT
  vs : List RDT
  dY : RDT
  dV : RDT

/-- In a row. -/
def ScR.all (r : ScR) : List RDT := r.dE :: (r.vs ++ [r.dY, r.dV])

/-- What ties them to a stage of the chain. -/
structure StgM {X : Type} (S : Stg GE M X) (r : ScR) where
  DY : ℕ
  num : S.L.T.par.A → ℕ
  hf : S.L.T.par.fmt = List.replicate r.vs.length (pfCube GE 2) ++ [pDummy GE DY]

/-- The stage's data. -/
noncomputable def StgM.ride {X : Type} {S : Stg GE M X} {r : ScR} (W : StgM S r)
    (Ow : S.Nx → M → Prop) {next : Ch GE M S.Nx} {ds : List RDT} (rest : ChM next ds) :
    ChM (S.stage Ow next) (r.all ++ ds) :=
  ChM.ride r.dE r.vs r.dY r.dV W.DY W.num W.hf rest

/-- The written rounds of all stages from the limbs' scalars on. -/
structure TailR where
  dL : RDT
  dN : RDT
  r1 : ScR
  t1 : RDT
  dP : RDT
  r2 : ScR
  r3 : ScR
  d4 : RDT
  r4 : ScR
  r5 : ScR
  t5 : RDT
  dR : RDT
  r6 : ScR
  t6 : RDT
  dW : RDT
  r7 : ScR

/-- In a row, in the chain's order. -/
def TailR.all (R : TailR) : List RDT :=
  [R.dL] ++ ([R.dN] ++ (R.r1.all ++ ([R.t1] ++ ([R.dP] ++ (R.r2.all ++ (R.r3.all ++ ([R.d4] ++
    (R.r4.all ++ (R.r5.all ++ ([R.t5] ++ ([R.dR] ++ (R.r6.all ++ ([R.t6] ++ ([R.dW] ++
      (R.r7.all ++ [])))))))))))))))

/-- The seven ties. -/
structure TailM {X : Type} (T : LayTail GE M X) (R : TailR) where
  w1 : StgM T.s1 R.r1
  w2 : StgM T.s2 R.r2
  w3 : StgM T.s3 R.r3
  w4 : StgM T.s4 R.r4
  w5 : StgM T.s5 R.r5
  w6 : StgM T.s6 R.r6
  w7 : StgM T.s7 R.r7

/-- **The data for the chain from the limbs' scalars on.** -/
noncomputable def TailM.chM {X : Type} {T : LayTail GE M X} {R : TailR} (W : TailM T R) :
    ChM T.ch R.all :=
  .send R.dL (.drawPt R.dN (W.w1.ride _ (.draw1 R.t1 (.send R.dP (W.w2.ride _ (W.w3.ride _
    (.draw1 R.d4 (W.w4.ride _ (W.w5.ride _ (.draw1 R.t5 (.drawPt R.dR (W.w6.ride _
      (.draw1 R.t6 (.send R.dW (W.w7.ride _ (.done _))))))))))))))))

/-- With the token point in front. -/
noncomputable def ownM {X : Type} (A : LayOwn GE M X) (dT : RDT) {R : TailR} (W : TailM A.tail R) :
    ChM A.ch ([dT] ++ R.all) :=
  .drawPt dT W.chM

/-- The first sub-proof's: two more points. -/
noncomputable def ownFirstM {X : Type} (A : LayOwnFirst GE M X) (dT dA dB : RDT) {R : TailR}
    (W : TailM A.tail R) : ChM A.ch ([dT] ++ ([dA] ++ ([dB] ++ R.all))) :=
  .drawPt dT (.drawPt dA (.drawPt dB W.chM))

/-- One element is drawn. -/
def Draws1 (d : RDT) : Prop := ∃ ns a, SendsDraws (toRD d) ns 1 0 a

/-- g elements are drawn. -/
def DrawsPt (g : ℕ) (d : RDT) : Prop := ∃ ns a, SendsDraws (toRD d) ns g 0 a

/-- A sumcheck's written rounds send and draw what is asked. -/
def ScR.Ds (r : ScR) : Prop := PscDs r.dE r.vs r.dY r.dV

/-- What each written round must send and draw. -/
structure TailDs {X : Type} (T : LayTail GE M X) (R : TailR) : Prop where
  l : Draws1 R.dL
  n : DrawsPt T.gN R.dN
  s1 : R.r1.Ds
  t1 : Draws1 R.t1
  p : Draws1 R.dP
  s2 : R.r2.Ds
  s3 : R.r3.Ds
  d4 : Draws1 R.d4
  s4 : R.r4.Ds
  s5 : R.r5.Ds
  t5 : Draws1 R.t5
  r : DrawsPt T.gR R.dR
  s6 : R.r6.Ds
  t6 : Draws1 R.t6
  w : Draws1 R.dW
  s7 : R.r7.Ds

theorem TailM.ds {X : Type} {T : LayTail GE M X} {R : TailR} (W : TailM T R) (H : TailDs T R) :
    W.chM.Ds :=
  And.intro H.l (And.intro H.n (And.intro H.s1 (And.intro H.t1 (And.intro H.p (And.intro H.s2
    (And.intro H.s3 (And.intro H.d4 (And.intro H.s4 (And.intro H.s5 (And.intro H.t5
      (And.intro H.r (And.intro H.s6 (And.intro H.t6 (And.intro H.w (And.intro H.s7
        trivial)))))))))))))))

/-- **The own rounds' maps are as asked.** -/
theorem ownMaps_ok (Ex : ExtSpec) {X : Type} (A : LayOwn GE M X) {dT : RDT} {R : TailR}
    (W : TailM A.tail R) (hT : DrawsPt A.gT dT) (H : TailDs A.tail R) :
    ((ownM A dT W).mapsR Ex).OK :=
  ChM.mapsR_ok Ex _ (And.intro hT (W.ds H))

/-- **The first sub-proof's.** -/
theorem ownFirstMaps_ok (Ex : ExtSpec) {X : Type} (A : LayOwnFirst GE M X) {dT dA dB : RDT}
    {R : TailR} (W : TailM A.tail R) (hT : DrawsPt A.gT dT) (hA : DrawsPt A.gA dA)
    (hB : DrawsPt A.gB dB) (H : TailDs A.tail R) :
    ((ownFirstM A dT dA dB W).mapsR Ex).OK :=
  ChM.mapsR_ok Ex _ (And.intro hT (And.intro hA (And.intro hB (W.ds H))))

end OnBytes.Desc.First.P1

#print axioms OnBytes.Desc.First.P1.ownMaps_ok
#print axioms OnBytes.Desc.First.P1.ownFirstMaps_ok
