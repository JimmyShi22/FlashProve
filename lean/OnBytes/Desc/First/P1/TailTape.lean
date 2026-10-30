-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/TailTape.lean: THE DATA OF THE CHAIN OF A LAYERS' SUB-PROOF'S OWN ROUNDS
(`TailH`, OnBytes/Tie/Pv/Lay/OwnTieL.lean), READ OFF A FLAT TAPE BY FUNCTIONS; and that on the tape
of a written transcript they are the words of the transcript's sixteen cuts (`TailWords`,
OwnView.lean). Definitions, statements and proofs. Lists alone.

  `heardPairs k t`: of the tape's first k rounds: what each sent, with the first word that it drew.
    `pairs_congr`: `msOf ws t`, as pairs, is `heardPairs ws.length t`: the weights do not matter.
  `pscT n k t`: what a masked sumcheck with n further scalars and k variables has heard, if its
    first round is the tape's first.
  `stgT`: the data of a stage (`StgH`) from it, a numbering of the end values, a state and a target.
  `Ks`: the seven sumchecks' numbers of variables. `tc1` … `tcW`: the tape from each of the
    library's six cuts of the chain on.
  `NzT`, `Adds7`, `tailT`: that none of the seven further challenges reads 0; seven states and seven
    targets; the data.
  `TapeCuts`, `tapeCuts`: at each of the sixteen cuts of a written transcript the tape is the cut's.
  `stgT_is`, `tailT_is`: on the tape of a written transcript τ over `R.all`, if R's sumchecks have
    these numbers of variables' rounds: `TailWords W τ (tailT …)`.

NO ARGUMENT: `IsTape.right`, `IsTape.one`, `IsTape.stage` (TapeCut.lean), sixteen times.

Limits. Lists alone: no function's return, no law. The states and targets are free letters. `NzT` is
a premise. That a text's functions read these same words is by unfolding, and is said where a text
is read.
-/
import OnBytes.Desc.First.P1.TapeCut
import OnBytes.Desc.First.P1.OwnView

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P1
open Iop Cb TWhole Cb.Pv.Lay Cb.Pv.Att Johnson.L5.Layers
open OnBytes.K.Kc OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Tie.Pv.Lay.Eng (StgH TailH)
open OnBytes.Tie.Pv.Att (PscH)
open OnBytes.Psc (Weight)
open _root_.Run (ckP)

local notation "z0" => OnBytes.zeroE

variable {M : Type}

/-! ### One sumcheck, off a tape -/

/-- Of the tape's first k rounds: what each sent, with the first word that it drew. -/
def heardPairs (k : ℕ) (t : Tape) : List (List OnBytes.E × OnBytes.E) :=
  (msOf (List.replicate k (Weight.plain 3)) t).map fun m => (m.2.1, m.2.2)

theorem pairs_congr : ∀ (ws : List Weight) (t : Tape),
    (msOf ws t).map (fun m => (m.2.1, m.2.2)) = heardPairs ws.length t
  | [], t => by
    unfold heardPairs
    rw [msOf_nil]
    show [] = (msOf [] t).map _
    rw [msOf_nil]
    rfl
  | _ :: _, [] => rfl
  | w :: ws, r :: t => by
    unfold heardPairs
    show (msOf (w :: ws) (r :: t)).map _ =
      (msOf (Weight.plain 3 :: List.replicate ws.length (Weight.plain 3)) (r :: t)).map _
    rw [msOf_cons, msOf_cons, List.map_cons, List.map_cons, pairs_congr ws t]
    rfl

/-- What a masked sumcheck has heard, if its first round is the tape's first. -/
def pscT (n k : ℕ) (t : Tape) : PscH :=
  ⟨(sentOf t).getD n z0, tapeEps t, heardPairs k (t.drop 1),
    (roundAt (Weight.atZero 1) (t.drop (k + 1))).2.1,
    (roundAt (Weight.atZero 1) (t.drop (k + 1))).2.2, sentOf (t.drop (k + 2))⟩

/-- The data of a stage. -/
def stgT {X : Type} {S : Stg GE M X} (num : S.L.S.A → ℕ) (k : ℕ) (t : Tape)
    (hβ : gl.val (pscT S.n k t).beta ≠ 0) (st : S.L.St) (tg : OnBytes.E) : StgH gl S :=
  ⟨sentOf t, pscT S.n k t, hβ, fun a => gl.val ((pscT S.n k t).v.getD (num a) z0), st, tg⟩

theorem stgT_is {f : Fmt.RoundView → Fmt.RoundView} (hf : KeepsWords f) {X : Type} {S : Stg GE M X} {r : ScR}
    (W : StgM S r) {bs : List RDT} {c : Tr (uLT (ckP .two) (r.all ++ bs))} {t : Tape}
    (h : IsTape f (r.all ++ bs) c t) {k : ℕ} (hk : r.vs.length = k)
    (hβ : gl.val (pscT S.n k t).beta ≠ 0) (st : S.L.St) (tg : OnBytes.E) :
    StgWords (stgT W.num k t hβ st tg) W (Maps.trL r.all bs c) := by
  subst hk
  obtain ⟨a1, a2, a3, a4, a5⟩ := IsTape.stage hf h (List.replicate r.vs.length (Weight.plain 3))
    List.length_replicate (Weight.atZero 1)
  exact ⟨congrArg (rd gl S.n) a1, congrArg (fun l : List OnBytes.E => l.getD S.n z0) a1, a2, a3,
    congrArg (fun x : Weight × List OnBytes.E × OnBytes.E => x.2.1) a4,
    congrArg (fun x : Weight × List OnBytes.E × OnBytes.E => x.2.2) a4,
    funext fun a => congrArg (fun l : List OnBytes.E => gl.val (l.getD (W.num a) z0)) a5⟩

/-! ### The whole tail, off a tape -/

/-- The seven sumchecks' numbers of variables. -/
structure Ks where
  k1 : ℕ
  k2 : ℕ
  k3 : ℕ
  k4 : ℕ
  k5 : ℕ
  k6 : ℕ
  k7 : ℕ

namespace Ks

/-- The tape from each of the library's six cuts of the chain on. -/
def tc1 (_ : Ks) (t : Tape) : Tape := (t.drop 1).drop 1
def tcP (k : Ks) (t : Tape) : Tape := ((k.tc1 t).drop (k.k1 + 3)).drop 1
def tc4 (k : Ks) (t : Tape) : Tape := (((k.tcP t).drop 1).drop (k.k2 + 3)).drop (k.k3 + 3)
def tc5 (k : Ks) (t : Tape) : Tape := ((k.tc4 t).drop 1).drop (k.k4 + 3)
def tc6 (k : Ks) (t : Tape) : Tape := (((k.tc5 t).drop (k.k5 + 3)).drop 1).drop 1
def tcW (k : Ks) (t : Tape) : Tape := ((k.tc6 t).drop (k.k6 + 3)).drop 1

end Ks

/-- None of the seven further challenges reads 0. -/
structure NzT {X : Type} (T : LayTail GE M X) (k : Ks) (t : Tape) : Prop where
  b1 : gl.val (pscT T.s1.n k.k1 (k.tc1 t)).beta ≠ 0
  b2 : gl.val (pscT T.s2.n k.k2 ((k.tcP t).drop 1)).beta ≠ 0
  b3 : gl.val (pscT T.s3.n k.k3 (((k.tcP t).drop 1).drop (k.k2 + 3))).beta ≠ 0
  b4 : gl.val (pscT T.s4.n k.k4 ((k.tc4 t).drop 1)).beta ≠ 0
  b5 : gl.val (pscT T.s5.n k.k5 (k.tc5 t)).beta ≠ 0
  b6 : gl.val (pscT T.s6.n k.k6 (k.tc6 t)).beta ≠ 0
  b7 : gl.val (pscT T.s7.n k.k7 ((k.tcW t).drop 1)).beta ≠ 0

/-- Seven states and seven targets. -/
structure Adds7 {X : Type} (T : LayTail GE M X) where
  st1 : T.s1.L.St
  st2 : T.s2.L.St
  st3 : T.s3.L.St
  st4 : T.s4.L.St
  st5 : T.s5.L.St
  st6 : T.s6.L.St
  st7 : T.s7.L.St
  t1 : OnBytes.E
  t2 : OnBytes.E
  t3 : OnBytes.E
  t4 : OnBytes.E
  t5 : OnBytes.E
  t6 : OnBytes.E
  t7 : OnBytes.E

/-- **The data of the chain from the limbs' scalars on, read off a tape.** -/
def tailT {X : Type} {T : LayTail GE M X} {R : TailR} (W : TailM T R) (k : Ks) (t : Tape)
    (nz : NzT T k t) (a : Adds7 T) : TailH gl T where
  sL := sentOf t
  xL := tapeEps t
  pN := drawnOf (t.drop 1)
  d1 := stgT W.w1.num k.k1 (k.tc1 t) nz.b1 a.st1 a.t1
  x1 := tapeEps ((k.tc1 t).drop (k.k1 + 3))
  sP := sentOf (k.tcP t)
  xP := tapeEps (k.tcP t)
  d2 := stgT W.w2.num k.k2 ((k.tcP t).drop 1) nz.b2 a.st2 a.t2
  d3 := stgT W.w3.num k.k3 (((k.tcP t).drop 1).drop (k.k2 + 3)) nz.b3 a.st3 a.t3
  x4 := tapeEps (k.tc4 t)
  d4 := stgT W.w4.num k.k4 ((k.tc4 t).drop 1) nz.b4 a.st4 a.t4
  d5 := stgT W.w5.num k.k5 (k.tc5 t) nz.b5 a.st5 a.t5
  x5 := tapeEps ((k.tc5 t).drop (k.k5 + 3))
  pR := drawnOf (((k.tc5 t).drop (k.k5 + 3)).drop 1)
  d6 := stgT W.w6.num k.k6 (k.tc6 t) nz.b6 a.st6 a.t6
  x6 := tapeEps ((k.tc6 t).drop (k.k6 + 3))
  sW := sentOf (k.tcW t)
  xW := tapeEps (k.tcW t)
  d7 := stgT W.w7.num k.k7 ((k.tcW t).drop 1) nz.b7 a.st7 a.t7

/-- R's sumchecks have these numbers of variables' rounds. -/
structure Ks.Fit (k : Ks) (R : TailR) : Prop where
  k1 : R.r1.vs.length = k.k1
  k2 : R.r2.vs.length = k.k2
  k3 : R.r3.vs.length = k.k3
  k4 : R.r4.vs.length = k.k4
  k5 : R.r5.vs.length = k.k5
  k6 : R.r6.vs.length = k.k6
  k7 : R.r7.vs.length = k.k7

theorem ScR.all_length (r : ScR) : r.all.length = r.vs.length + 3 := by
  unfold ScR.all
  simp

/-- Behind a sumcheck's rounds. -/
theorem IsTape.past {f : Fmt.RoundView → Fmt.RoundView} {r : ScR} {bs : List RDT}
    {c : Tr (uLT (ckP .two) (r.all ++ bs))} {t : Tape} (h : IsTape f (r.all ++ bs) c t) {k : ℕ}
    (hk : r.vs.length = k) : IsTape f bs (Maps.trR r.all bs c) (t.drop (k + 3)) := by
  have e := h.right
  rw [ScR.all_length, hk] at e
  exact e

/-- At each of the sixteen cuts of a written transcript the tape is the cut's. -/
structure TapeCuts (f : Fmt.RoundView → Fmt.RoundView) (R : TailR) (k : Ks) (τ : Tr (uLT (ckP .two) R.all))
    (t : Tape) : Prop where
  g0 : IsTape f ([R.dL] ++ ([R.dN] ++ R.l1)) τ t
  gN : IsTape f ([R.dN] ++ R.l1) (Maps.trR [R.dL] ([R.dN] ++ R.l1) τ) (t.drop 1)
  g1 : IsTape f (R.r1.all ++ ([R.t1] ++ R.lP)) (R.c1 τ) (k.tc1 t)
  h1 : IsTape f ([R.t1] ++ R.lP) (Maps.trR R.r1.all ([R.t1] ++ R.lP) (R.c1 τ))
    ((k.tc1 t).drop (k.k1 + 3))
  gP : IsTape f ([R.dP] ++ (R.r2.all ++ (R.r3.all ++ R.l4))) (R.cP τ) (k.tcP t)
  g2 : IsTape f (R.r2.all ++ (R.r3.all ++ R.l4))
    (Maps.trR [R.dP] (R.r2.all ++ (R.r3.all ++ R.l4)) (R.cP τ)) ((k.tcP t).drop 1)
  g3 : IsTape f (R.r3.all ++ R.l4)
    (Maps.trR R.r2.all (R.r3.all ++ R.l4)
      (Maps.trR [R.dP] (R.r2.all ++ (R.r3.all ++ R.l4)) (R.cP τ)))
    (((k.tcP t).drop 1).drop (k.k2 + 3))
  g4 : IsTape f ([R.d4] ++ (R.r4.all ++ R.l5)) (R.c4 τ) (k.tc4 t)
  h4 : IsTape f (R.r4.all ++ R.l5) (Maps.trR [R.d4] (R.r4.all ++ R.l5) (R.c4 τ))
    ((k.tc4 t).drop 1)
  g5 : IsTape f (R.r5.all ++ ([R.t5] ++ ([R.dR] ++ R.l6))) (R.c5 τ) (k.tc5 t)
  h5 : IsTape f ([R.t5] ++ ([R.dR] ++ R.l6))
    (Maps.trR R.r5.all ([R.t5] ++ ([R.dR] ++ R.l6)) (R.c5 τ)) ((k.tc5 t).drop (k.k5 + 3))
  hR : IsTape f ([R.dR] ++ R.l6)
    (Maps.trR [R.t5] ([R.dR] ++ R.l6) (Maps.trR R.r5.all ([R.t5] ++ ([R.dR] ++ R.l6)) (R.c5 τ)))
    (((k.tc5 t).drop (k.k5 + 3)).drop 1)
  g6 : IsTape f (R.r6.all ++ ([R.t6] ++ R.lW)) (R.c6 τ) (k.tc6 t)
  h6 : IsTape f ([R.t6] ++ R.lW) (Maps.trR R.r6.all ([R.t6] ++ R.lW) (R.c6 τ))
    ((k.tc6 t).drop (k.k6 + 3))
  gW : IsTape f ([R.dW] ++ (R.r7.all ++ [])) (R.cW τ) (k.tcW t)
  g7 : IsTape f (R.r7.all ++ []) (Maps.trR [R.dW] (R.r7.all ++ []) (R.cW τ)) ((k.tcW t).drop 1)

section Cuts
variable {f : Fmt.RoundView → Fmt.RoundView} {R : TailR} {k : Ks} {τ : Tr (uLT (ckP .two) R.all)} {t : Tape}

theorem cut_1 (h : IsTape f R.all τ t) :
    IsTape f (R.r1.all ++ ([R.t1] ++ R.lP)) (R.c1 τ) (k.tc1 t) :=
  IsTape.right (as := [R.dN]) (IsTape.right (as := [R.dL]) (bs := [R.dN] ++ R.l1) h)

theorem cut_P (hk : k.Fit R) (g1 : IsTape f (R.r1.all ++ ([R.t1] ++ R.lP)) (R.c1 τ) (k.tc1 t)) :
    IsTape f ([R.dP] ++ (R.r2.all ++ (R.r3.all ++ R.l4))) (R.cP τ) (k.tcP t) :=
  IsTape.right (as := [R.t1]) (g1.past hk.k1)

theorem cut_4 (hk : k.Fit R)
    (gP : IsTape f ([R.dP] ++ (R.r2.all ++ (R.r3.all ++ R.l4))) (R.cP τ) (k.tcP t)) :
    IsTape f ([R.d4] ++ (R.r4.all ++ R.l5)) (R.c4 τ) (k.tc4 t) :=
  ((IsTape.right (as := [R.dP]) gP).past hk.k2).past hk.k3

theorem cut_5 (hk : k.Fit R) (g4 : IsTape f ([R.d4] ++ (R.r4.all ++ R.l5)) (R.c4 τ) (k.tc4 t)) :
    IsTape f (R.r5.all ++ ([R.t5] ++ ([R.dR] ++ R.l6))) (R.c5 τ) (k.tc5 t) :=
  (IsTape.right (as := [R.d4]) g4).past hk.k4

theorem cut_6 (hk : k.Fit R)
    (g5 : IsTape f (R.r5.all ++ ([R.t5] ++ ([R.dR] ++ R.l6))) (R.c5 τ) (k.tc5 t)) :
    IsTape f (R.r6.all ++ ([R.t6] ++ R.lW)) (R.c6 τ) (k.tc6 t) :=
  IsTape.right (as := [R.dR]) (IsTape.right (as := [R.t5]) (g5.past hk.k5))

theorem cut_W (hk : k.Fit R) (g6 : IsTape f (R.r6.all ++ ([R.t6] ++ R.lW)) (R.c6 τ) (k.tc6 t)) :
    IsTape f ([R.dW] ++ (R.r7.all ++ [])) (R.cW τ) (k.tcW t) :=
  IsTape.right (as := [R.t6]) (g6.past hk.k6)

/-- All sixteen. -/
theorem tapeCuts (hk : k.Fit R) (h : IsTape f R.all τ t) : TapeCuts f R k τ t :=
  have g1 := cut_1 (k := k) h
  have gP := cut_P hk g1
  have g4 := cut_4 hk gP
  have g5 := cut_5 hk g4
  have g6 := cut_6 hk g5
  have gW := cut_W hk g6
  { g0 := h
    gN := IsTape.right (as := [R.dL]) (bs := [R.dN] ++ R.l1) h
    g1 := g1
    h1 := g1.past hk.k1
    gP := gP
    g2 := IsTape.right (as := [R.dP]) gP
    g3 := (IsTape.right (as := [R.dP]) gP).past hk.k2
    g4 := g4
    h4 := IsTape.right (as := [R.d4]) g4
    g5 := g5
    h5 := g5.past hk.k5
    hR := IsTape.right (as := [R.t5]) (g5.past hk.k5)
    g6 := g6
    h6 := g6.past hk.k6
    gW := gW
    g7 := IsTape.right (as := [R.dW]) gW }

end Cuts

section Words
variable {f : Fmt.RoundView → Fmt.RoundView} (hf : KeepsWords f) {X : Type} {T : LayTail GE M X} {R : TailR}
  (W : TailM T R) {k : Ks} (hk : k.Fit R) {τ : Tr (uLT (ckP .two) R.all)} {t : Tape}
  (c : TapeCuts f R k τ t) (nz : NzT T k t) (a : Adds7 T)
include hf hk c

theorem tw1 : StgWords (tailT W k t nz a).d1 W.w1 (R.x1 τ) :=
  stgT_is hf W.w1 c.g1 hk.k1 nz.b1 a.st1 a.t1
theorem tw2 : StgWords (tailT W k t nz a).d2 W.w2 (R.x2 τ) :=
  stgT_is hf W.w2 c.g2 hk.k2 nz.b2 a.st2 a.t2
theorem tw3 : StgWords (tailT W k t nz a).d3 W.w3 (R.x3 τ) :=
  stgT_is hf W.w3 c.g3 hk.k3 nz.b3 a.st3 a.t3
theorem tw4 : StgWords (tailT W k t nz a).d4 W.w4 (R.x4 τ) :=
  stgT_is hf W.w4 c.h4 hk.k4 nz.b4 a.st4 a.t4
theorem tw5 : StgWords (tailT W k t nz a).d5 W.w5 (R.x5 τ) :=
  stgT_is hf W.w5 c.g5 hk.k5 nz.b5 a.st5 a.t5
theorem tw6 : StgWords (tailT W k t nz a).d6 W.w6 (R.x6 τ) :=
  stgT_is hf W.w6 c.g6 hk.k6 nz.b6 a.st6 a.t6
theorem tw7 : StgWords (tailT W k t nz a).d7 W.w7 (R.x7 τ) :=
  stgT_is hf W.w7 c.g7 hk.k7 nz.b7 a.st7 a.t7

end Words

section Words1
variable {f : Fmt.RoundView → Fmt.RoundView} (hf : KeepsWords f) {X : Type} {T : LayTail GE M X} {R : TailR}
  (W : TailM T R) {k : Ks} {τ : Tr (uLT (ckP .two) R.all)} {t : Tape}
  (c : TapeCuts f R k τ t) (nz : NzT T k t) (a : Adds7 T)
include hf c

theorem w_sL : (tailT W k t nz a).sL = sentE R.dL (R.xL τ).1 := (c.g0.one hf).1
theorem w_xL : (tailT W k t nz a).xL = (drawnE R.dL (R.xL τ).2.1).headD z0 := (c.g0.one hf).2.1
theorem w_pN : (tailT W k t nz a).pN = drawnE R.dN (R.xN τ).2.1 := (c.gN.one hf).2.2
theorem w_x1 : (tailT W k t nz a).x1 = (drawnE R.t1 (R.y1 τ).2.1).headD z0 := (c.h1.one hf).2.1
theorem w_sP : (tailT W k t nz a).sP = sentE R.dP (R.xP τ).1 := (c.gP.one hf).1
theorem w_xP : (tailT W k t nz a).xP = (drawnE R.dP (R.xP τ).2.1).headD z0 := (c.gP.one hf).2.1
theorem w_x4 : (tailT W k t nz a).x4 = (drawnE R.d4 (R.y4 τ).2.1).headD z0 := (c.g4.one hf).2.1
theorem w_x5 : (tailT W k t nz a).x5 = (drawnE R.t5 (R.y5 τ).2.1).headD z0 := (c.h5.one hf).2.1
theorem w_pR : (tailT W k t nz a).pR = drawnE R.dR (R.xR τ).2.1 := (c.hR.one hf).2.2
theorem w_x6 : (tailT W k t nz a).x6 = (drawnE R.t6 (R.y6 τ).2.1).headD z0 := (c.h6.one hf).2.1
theorem w_sW : (tailT W k t nz a).sW = sentE R.dW (R.xW τ).1 := (c.gW.one hf).1
theorem w_xW : (tailT W k t nz a).xW = (drawnE R.dW (R.xW τ).2.1).headD z0 := (c.gW.one hf).2.1

end Words1

/-- **On the tape of a written transcript the data are the words of its sixteen cuts.** -/
theorem tailT_is {f : Fmt.RoundView → Fmt.RoundView} (hf : KeepsWords f) {X : Type} {T : LayTail GE M X}
    {R : TailR} (W : TailM T R) {k : Ks} (hk : k.Fit R) {τ : Tr (uLT (ckP .two) R.all)} {t : Tape}
    (h : IsTape f R.all τ t) (nz : NzT T k t) (a : Adds7 T) : TailWords W τ (tailT W k t nz a) :=
  have c := tapeCuts hk h
  ⟨w_sL hf W c nz a, w_xL hf W c nz a, w_pN hf W c nz a, tw1 hf W hk c nz a, w_x1 hf W c nz a,
    w_sP hf W c nz a, w_xP hf W c nz a, tw2 hf W hk c nz a, tw3 hf W hk c nz a, w_x4 hf W c nz a,
    tw4 hf W hk c nz a, tw5 hf W hk c nz a, w_x5 hf W c nz a, w_pR hf W c nz a,
    tw6 hf W hk c nz a, w_x6 hf W c nz a, w_sW hf W c nz a, w_xW hf W c nz a,
    tw7 hf W hk c nz a⟩

end OnBytes.Desc.First.P1

#print axioms OnBytes.Desc.First.P1.pairs_congr
#print axioms OnBytes.Desc.First.P1.stgT_is
#print axioms OnBytes.Desc.First.P1.tapeCuts
#print axioms OnBytes.Desc.First.P1.tailT_is
