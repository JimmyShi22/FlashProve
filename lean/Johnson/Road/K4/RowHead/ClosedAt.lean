-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/RowHead/ClosedAt.lean: THE MAKERS OF THE LAYERS' PUBLIC PART AND THE LISTING
"front" AT CLOSED VALUES.

What is here. Four closed facts WITHOUT ANY VARIABLE, and six definitions. withPlans
(Johnson/Road/K4/RowHead/Twins.lean) runs six makers on the parameter file's scan and then a test,
with the free numbers, the counts of padding keys, the scales and the rotary table as letters.
afterN is its text at numerals, without the fourth maker: the layers' shape is shapeL, the settings
are setRef, and the layout of the committed weights is a letter but for its 18 column bits. Two of
the facts run it at closed values: the three free constants of the normalisations are 0, the counts
of padding keys and the rotary table are empty, the scales are scC and the layout of the weights is
wC. The two others run the first maker and the fourth by themselves. Each is closed by kernel_rfl
(Johnson/Unfolds/KernelRfl.lean): one comparison by Lean's kernel. WHY CLOSED: the like fact with
free letters in it did not return from an independent proof checker; why is not known.

  `shapeL`, `setRef`, `shapeRef`   the layers' shape, the run's settings and the shape of the
      committed weights at the full size, in numerals.
  `afterN`   withPlans' text at numerals, without its fourth maker.
  `scC`, `wC`   closed scales; a closed layout of the weights.
  `closedSizes`   two sizes and a switch of the first maker's return.
  `closedFrontZero`, `closedFrontOne`   the listing "front" returns at the plan's value, at the
      groups 0 and 1.
  `weightsAt`   the fourth maker returns at shapeRef, with 18 column bits.

Limits. At these closed values alone: that the returns do not hang on the letters is
ClosedJoin.lean's after_letters, over Johnson/Road/K4/C/TwinLetters.lean and FrontLetters.lean; that
the scan has these numerals is ClosedTies.lean's. Only for the parameter files whose scan is Pv v at
some eight free numbers v (the full-size model).
No property is claimed.
-/
import Johnson.Unfolds.KernelRfl
import Johnson.Road.K4.RowHead.Twins
import Johnson.Road.K4.Total.PlanMemberDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.Closed
open OnBytes OnBytes.Model
open OnBytes.Road.K4 (onOk clOf)
open OnBytes.Desc.First.K4.Total (frontB)

/-- The layers' shape at the full size, in numerals; e1, e2, eF: the three free constants of the
normalisations. -/
def shapeL (e1 e2 eF : Nat) : Layer.Shape :=
  {
    prof := 4, lt := 10, L := 48, ll := 2, d := 5120, H := 40, Gk := 8, dh := 128, f := 16384,
    fe := 8192, NE := 128, eps1 := e1, eps2 := e2, epsF := eF, cs := 12, theta0 := 500000,
    hq := 2, hv := 1, ho := 1, hgD := 1, huD := 1, hdD := 1, hr := 1, ut := 1, la := 16,
    nmin := 20, D := 2048, tau := 128, lmaf := 16, NAf := 3, lmad := 15, NAd := 1, lmar := 13,
    lmb := 16, lmq := 16, lmx := 16, wb := #[13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13],
    iota := #[1, 1, 1, 2, 1, 1, 0, 0], seed := 1, gcl := true, rcl := true, xl := 5, lidb := 28,
    eg := 8, smax := 4095 }

/-- The run's settings at the full size, in numerals. -/
def setRef : Settings :=
  { lidb := 28, nminH := 27, tau := 128, pow := 20, powS := 28, powC := 32, hb := 128 }

/-- The shape of the committed weights at the full size, in numerals. -/
def shapeRef : WsShape :=
  { D := 2048, L := 48, d := 5120, dh := 128, dkv := 1024, dq := 5120, f := 16384, fe := 8192,
    NE := 128, V := 202048 }

/-- The library's test withPlans without its fourth maker, at numerals: the layout of the weights is
W with 18 column bits. -/
def afterN (e1 e2 eF : Nat) (pub : Array Nat) (sc : Layer.Scales) (rope : Array Nat) (W : WsLay)
    (f : Layer.Pub → Array Layer.HPlan2 → Bool) : Bool :=
  onOk (Layer.baseNoStops (shapeL e1 e2 eF) VerifierAndGoals.Lines.callsRef) fun y0 =>
    onOk (Forest.shapeNoAsk (clOf y0) y0.h.lidb) fun fo =>
      onOk (Forest.planeCols fo y0.h.lmb) fun kbm =>
        onOk (Layer.Pub.of { y0 with cl := clOf y0, fo := { fo with pub := pub }, kbm := kbm }
            sc rope { W with lk := 18 } 202048 #[] setRef) fun L =>
          onOk (Layer.plansG L) fun G => f L G

/-- Closed scales: no word, no layer. -/
def scC : Layer.Scales := { KL := #[], KW := 0, L := 0 }

/-- A closed layout of the committed weights: no unit, no row. -/
def wC : WsLay := { lk := 0, m0 := 0, U := #[] }

/-- Two sizes and a switch of the first maker's return. -/
theorem closedSizes :
    onOk (Layer.baseNoStops (shapeL 0 0 0) VerifierAndGoals.Lines.callsRef) (fun y0 =>
      y0.dkv == 1024 && y0.dq == 5120 && y0.h.p3) = true := by
  kernel_rfl

/-- Group 0. The whole listing returns at the plan's value. -/
theorem closedFrontZero :
    afterN 0 0 0 #[] scC #[] wC (fun L G => (G[0]?).any fun hp =>
      frontB false L hp 0 L.y.fo) = true := by
  kernel_rfl

/-- Group 1. The whole listing returns at the plan's value. -/
theorem closedFrontOne :
    afterN 0 0 0 #[] scC #[] wC (fun L G => (G[1]?).any fun hp =>
      frontB false L hp 1 L.y.fo) = true := by
  kernel_rfl

/-- The fourth maker returns at the shape in numerals, and its layout has the 18 column bits. -/
theorem weightsAt :
    onOk (wsLayOf shapeRef true 18) (fun lay => lay.lk == 18) = true := by
  kernel_rfl

end OnBytes.Road.K4.Closed

#print axioms OnBytes.Road.K4.Closed.closedSizes
#print axioms OnBytes.Road.K4.Closed.closedFrontZero
#print axioms OnBytes.Road.K4.Closed.closedFrontOne
#print axioms OnBytes.Road.K4.Closed.weightsAt
