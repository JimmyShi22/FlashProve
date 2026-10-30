-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/FlPort/FoPadCut.lean: a carried copy, made by a program, not typed by hand.

Of which file: OnBytes/Tie/Pv/Lookup/Forest/FoPadCut.lean, as it lies in this library.
What is carried: those of its declarations that depend on a context of the verifier program's
channel, and no other:
  PadMid, PadMid.h, PadMid.zx, PadMid.zy, PadMid.zk, PadMid.tT, PadMid.heard, PadCut, pad_cut
How: by one swap of names throughout: a context becomes a tape; a routine
of the program becomes the library's flat function of the same text (OnBytes/K/Kc/Flat.lean,
OnBytes/K/Kc/FlatHear.lean). The laws on "returns" are those of Johnson/Top/H/FlPort/Kit.lean. Every
other name is the library's own: plain records, pure functions and lemmas on them, used from where
they lie. Those of OnBytes/Tie/Pv/ that the text names, as far as a program sees them:
  leaves, owed3, place, rhoT, sBit, toOption_ok
The comments on the declarations are the library's, under the same swap: where they say "run" or
"view", read: on a tape.

Limits. What is proved here is proved of the flat functions alone, and a flat function tests less of
the plan than the program's routine (the paragraph "Not claimed" in the head of
OnBytes/K/Kc/Flat.lean). Nothing is said where a function refuses. A tie: it has no error term. If
the source file turns, this copy does not follow by itself. In the list of names a use by dot
notation on a hypothesis is not seen, and a short name may stand once too often. That no routine
in a context is reached from a statement or a proof here is meant, and is not shown in this
library.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPadCut
import Johnson.Top.H.FlPort.Kit
import Johnson.Top.H.FlPort.PscWhole
import Johnson.Top.H.FlPort.PscRun

set_option autoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open OnBytes OnBytes.Model OnBytes.PscRun

/-- What the routines that lkPad calls return, and the states and contexts between them. -/
structure PadMid where
  /-- the shape, before the numbers of padding keys are filled in -/
  h0 : Forest.Shape
  /-- what lkDraws returns -/
  theta : E
  alpha : E
  a : E
  /-- what lkTie returns -/
  t : Forest.Tie
  /-- the ends of the two walks -/
  keys : Forest.Descent
  table : Forest.Descent
  /-- the leaves' sumcheck: begun; after its rounds -/
  lv0 : Psc
  lv : Psc
  /-- the bits' sumcheck: begun; after its rounds; ended; after its claim -/
  b0 : Psc
  b1 : Psc
  b2 : Psc
  b3 : Psc
  /-- the challenges of the two sumchecks; the point drawn between them -/
  zb0 : Array E
  zb1 : Array E
  pt : Array E
  /-- the slot of the bits' shown value; what was shown; the bits' claim -/
  sBit : ℕ
  vBit : E
  row : Aff
  /-- the states after lkDraws, lkTie and the two walks -/
  F4 : Fork
  F5 : Fork
  F6 : Fork
  F7 : Fork
  /-- the states after each of the eight lines on the leaves and the bits -/
  G1 : Fork
  G2 : Fork
  G3 : Fork
  G4 : Fork
  G5 : Fork
  G6 : Fork
  G7 : Fork
  G8 : Fork
  /-- the contexts, likewise -/
  c4 : Tape
  c5 : Tape
  c6 : Tape
  c7 : Tape
  d1 : Tape
  d2 : Tape
  d3 : Tape
  d4 : Tape
  d5 : Tape
  d6 : Tape
  d7 : Tape
  d8 : Tape

/-- The shape with the numbers of padding keys filled in. -/
def PadMid.h (M : PadMid) (pub : Array Nat) : Forest.Shape := { M.h0 with pub := pub }

/-- The key side's point, cut in two. -/
def PadMid.zx (M : PadMid) (pub : Array Nat) : Array E := M.keys.rho.extract 0 (M.h pub).dT
def PadMid.zy (M : PadMid) (pub : Array Nat) : Array E :=
  M.keys.rho.extract (M.h pub).dT M.keys.rho.size

/-- Each call's point. -/
def PadMid.zk (M : PadMid) (pub : Array Nat) : Array (Array E) :=
  (Array.range (M.h pub).NC).map fun c =>
    (M.zy pub).extract ((M.h pub).rK - (M.h pub).iota.getD c 0) (M.zy pub).size ++ M.zx pub

/-- Each call's table at the leaves' point. -/
def PadMid.tT (M : PadMid) (pub : Array Nat) : Array E :=
  (M.h pub).calls.map fun k => Forest.tableAt k (M.zb0.extract ((M.h pub).kT - k.k) (M.h pub).kT)

/-- The record that lkPad returns. -/
def PadMid.heard (M : PadMid) (pub : Array Nat) (F : Fork) : Forest.Heard where
  shape := M.h pub
  theta := M.theta
  alpha := M.alpha
  a := M.a
  rows := M.table.rows.push M.row
  leaves := M.lv
  leavesA := subE (subE M.alpha oneE)
    (Forest.joinedTableAt (M.h pub) M.theta (M.tT pub)
      (M.zb0.extract (M.h pub).kT ((M.h pub).kT + (M.h pub).cK)))
  sBit := M.sBit
  zx := M.zx pub
  zy := M.zy pub
  e := (Array.range (M.h pub).NC).map (Forest.callWeight (M.h pub) (M.zy pub))
  cEnd := M.keys.form
  zb0 := M.zb0
  zb1 := M.zb1
  tT := M.tT pub
  zk := M.zk pub
  owedObjects := (F.owe "look-up-mask-claims").1
  owedPlanes := ((F.owe "look-up-mask-claims").2.owe "look-up-plane-claims").1
  owedJoin :=
    (((F.owe "look-up-mask-claims").2.owe "look-up-plane-claims").2.owe "look-up-join").1

/-- A run of lkPad, as the chain of the runs of the routines that it calls. -/
structure PadCut (calls : Array Call) (pub : Array Nat) (lid : ℕ) (F : Fork) (c : Tape)
    (g : Forest.Heard) (F' : Fork) (c' : Tape) (M : PadMid) : Prop where
  shape : Forest.shape calls lid = .ok M.h0
  ask : (Forest.pubAsk M.h0 pub).toBool = true
  draws : lkDraws (M.h pub) (owed3 F) c = .ok (((M.theta, M.alpha, M.a), M.F4), M.c4)
  tie : lkTie M.a M.F4 M.c4 = .ok ((M.t, M.F5), M.c5)
  keys : ((List.range (M.h pub).v).foldlM
      (fun (s : Forest.Descent) mu =>
        lkLevel s mu
          (if mu + 1 = (M.h pub).v then Forest.orderForestRange mu (M.h pub).rK
            else orderDefault mu))
      { rows := M.t.rows, rho := #[], form := Aff.slot M.t.sZ }) M.F5 M.c5 =
    .ok ((M.keys, M.F6), M.c6)
  table : ((List.range (M.h pub).d).foldlM
      (fun (s : Forest.Descent) l => lkLevel s (5 + l) (orderDefault (5 + l)))
      { rows := M.keys.rows, rho := M.t.rhoT, form := M.t.cT }) M.F6 M.c6 =
    .ok ((M.table, M.F7), M.c7)
  size : M.table.rho.size = 5 + (M.h pub).d
  l1 : Fl.pscBegin M.table.form M.F7 M.c7 = .ok ((M.lv0, M.G1), M.d1)
  l2 : Fl.roundsIn .eq M.lv0
      ((List.range (5 + (M.h pub).d)).map fun j =>
        (M.table.rho.getD j zeroE, if j < (M.h pub).d then 2 else 1)) M.G1 M.d1 =
    .ok (((M.zb0, M.lv), M.G2), M.d2)
  l3 : Fl.point .zero (5 + (M.h pub).d) M.G2 M.d2 = .ok ((M.pt, M.G3), M.d3)
  l4 : Fl.pscBegin (Aff.ofConst zeroE) M.G3 M.d3 = .ok ((M.b0, M.G4), M.d4)
  l5 : Fl.roundsIn .eq2 M.b0 (M.pt.reverse.toList.map fun z => (z, 0)) M.G4 M.d4 =
    .ok (((M.zb1, M.b1), M.G5), M.d5)
  l6 : Fl.pscEnds M.b1 2 1 M.G5 M.d5 = .ok (((M.sBit, M.b2), M.G6), M.d6)
  l7 : Fl.shown M.sBit M.G6 M.d6 = .ok ((M.vBit, M.G7), M.d7)
  l8 : Fl.pscRow M.b2 (subE (mulE M.vBit M.vBit) M.vBit) {} M.G7 M.d7 =
    .ok (((M.row, M.b3), M.G8), M.d8)
  slots : M.G8.next = F.next + Forest.elems (M.h pub)
  lins : (M.table.rows.push M.row).size = Forest.lins (M.h pub)
  place : ((M.h pub).iota.all fun i => decide (i ≤ (M.h pub).rK)) = true
  point : ((List.range (M.h pub).NC).all fun k =>
    ((M.zk pub).getD k #[]).size == (((M.h pub).calls[k]?).map (·.n)).getD 0) = true
  heard : g = M.heard pub F
  fork : F' = M.G8
  ctx : c' = M.d8

/-- **Every run of lkPad that returns is such a chain.** -/
theorem pad_cut (calls : Array Call) (pub : Array Nat) (lid : ℕ) (F F' : Fork) (c c' : Tape)
    (g : Forest.Heard) (h : lkPad calls pub lid F c = .ok ((g, F'), c')) :
    ∃ M : PadMid, PadCut calls pub lid F c g F' c' M := by
  unfold lkPad at h
  -- the shape
  rw [bind_ok] at h
  obtain ⟨h0, A1, a1, r1, h⟩ := h
  obtain ⟨h0', s1, e1⟩ := (get_ok _ F c _).1 r1
  have x1 : h0 = h0' := congrArg (fun x : (Forest.Shape × Fork) × Tape => x.1.1) e1
  have x2 : A1 = F := congrArg (fun x : (Forest.Shape × Fork) × Tape => x.1.2) e1
  have x3 : a1 = c := congrArg (fun x : (Forest.Shape × Fork) × Tape => x.2) e1
  rw [← x1] at s1
  rw [x2, x3, bind_ok] at h
  obtain ⟨_, A2, a2, r2, h⟩ := h
  obtain ⟨s2, e2⟩ := (must_ok _ F c _).1 r2
  have y2 : A2 = F := congrArg (fun x : (Unit × Fork) × Tape => x.1.2) e2
  have y3 : a2 = c := congrArg (fun x : (Unit × Fork) × Tape => x.2) e2
  rw [y2, y3] at h
  -- the slot and the three owed claims
  rw [bind_ok] at h
  obtain ⟨slot0, A3, a3, r3, h⟩ := h
  have e3 := (slot_ok F c _).1 r3
  have z1 : slot0 = F.next := congrArg (fun x : (ℕ × Fork) × Tape => x.1.1) e3
  have z2 : A3 = F := congrArg (fun x : (ℕ × Fork) × Tape => x.1.2) e3
  have z3 : a3 = c := congrArg (fun x : (ℕ × Fork) × Tape => x.2) e3
  rw [z1, z2, z3, bind_ok] at h
  obtain ⟨o1, B1, b1, r4, h⟩ := h
  have e4 := (owe_ok _ F c _).1 r4
  have u1 : o1 = (F.owe "look-up-mask-claims").1 :=
    congrArg (fun x : (ℕ × Fork) × Tape => x.1.1) e4
  have u2 : B1 = (F.owe "look-up-mask-claims").2 :=
    congrArg (fun x : (ℕ × Fork) × Tape => x.1.2) e4
  have u3 : b1 = c := congrArg (fun x : (ℕ × Fork) × Tape => x.2) e4
  rw [u1, u2, u3, bind_ok] at h
  obtain ⟨o2, B2, b2, r5, h⟩ := h
  have e5 := (owe_ok _ _ c _).1 r5
  have v1 : o2 = ((F.owe "look-up-mask-claims").2.owe "look-up-plane-claims").1 :=
    congrArg (fun x : (ℕ × Fork) × Tape => x.1.1) e5
  have v2 : B2 = ((F.owe "look-up-mask-claims").2.owe "look-up-plane-claims").2 :=
    congrArg (fun x : (ℕ × Fork) × Tape => x.1.2) e5
  have v3 : b2 = c := congrArg (fun x : (ℕ × Fork) × Tape => x.2) e5
  rw [v1, v2, v3, bind_ok] at h
  obtain ⟨o3, B3, b3, r6, h⟩ := h
  have e6 := (owe_ok _ _ c _).1 r6
  have w1 : o3 =
      (((F.owe "look-up-mask-claims").2.owe "look-up-plane-claims").2.owe "look-up-join").1 :=
    congrArg (fun x : (ℕ × Fork) × Tape => x.1.1) e6
  have w2 : B3 = owed3 F := congrArg (fun x : (ℕ × Fork) × Tape => x.1.2) e6
  have w3 : b3 = c := congrArg (fun x : (ℕ × Fork) × Tape => x.2) e6
  rw [w1, w2, w3, bind_ok] at h
  -- the routines
  obtain ⟨⟨theta, alpha, a⟩, F4, c4, q1, h⟩ := h
  rw [bind_ok] at h
  obtain ⟨t, F5, c5, q2, h⟩ := h
  rw [bind_ok] at h
  obtain ⟨keys, F6, c6, q3, h⟩ := h
  rw [bind_ok] at h
  obtain ⟨table, F7, c7, q4, h⟩ := h
  rw [bind_ok] at h
  obtain ⟨_, C1, k1, q5, h⟩ := h
  obtain ⟨s5, e7⟩ := (must_ok _ F7 c7 _).1 q5
  have m2 : C1 = F7 := congrArg (fun x : (Unit × Fork) × Tape => x.1.2) e7
  have m3 : k1 = c7 := congrArg (fun x : (Unit × Fork) × Tape => x.2) e7
  rw [m2, m3, bind_ok] at h
  obtain ⟨lv0, G1, d1, l1, h⟩ := h
  rw [bind_ok] at h
  obtain ⟨⟨zb0, lv⟩, G2, d2, l2, h⟩ := h
  rw [bind_ok] at h
  obtain ⟨pt, G3, d3, l3, h⟩ := h
  rw [bind_ok] at h
  obtain ⟨b0, G4, d4, l4, h⟩ := h
  rw [bind_ok] at h
  obtain ⟨⟨zb1, b1'⟩, G5, d5, l5, h⟩ := h
  rw [bind_ok] at h
  obtain ⟨⟨sBit, b2'⟩, G6, d6, l6, h⟩ := h
  rw [bind_ok] at h
  obtain ⟨vBit, G7, d7, l7, h⟩ := h
  rw [bind_ok] at h
  obtain ⟨⟨row, b3'⟩, G8, d8, l8, h⟩ := h
  -- the three last tests
  rw [bind_ok] at h
  obtain ⟨sl, C2, k2, q6, h⟩ := h
  have e8 := (slot_ok G8 d8 _).1 q6
  have n1 : sl = G8.next := congrArg (fun x : (ℕ × Fork) × Tape => x.1.1) e8
  have n2 : C2 = G8 := congrArg (fun x : (ℕ × Fork) × Tape => x.1.2) e8
  have n3 : k2 = d8 := congrArg (fun x : (ℕ × Fork) × Tape => x.2) e8
  rw [n1, n2, n3, bind_ok] at h
  obtain ⟨_, C3, k3, q7, h⟩ := h
  obtain ⟨s7, e9⟩ := (must_ok _ G8 d8 _).1 q7
  have p2 : C3 = G8 := congrArg (fun x : (Unit × Fork) × Tape => x.1.2) e9
  have p3 : k3 = d8 := congrArg (fun x : (Unit × Fork) × Tape => x.2) e9
  rw [p2, p3, bind_ok] at h
  obtain ⟨_, C4, k4, q8, h⟩ := h
  obtain ⟨s8, e10⟩ := (must_ok _ G8 d8 _).1 q8
  have p4 : C4 = G8 := congrArg (fun x : (Unit × Fork) × Tape => x.1.2) e10
  have p5 : k4 = d8 := congrArg (fun x : (Unit × Fork) × Tape => x.2) e10
  rw [p4, p5] at h
  rw [bind_ok] at h
  obtain ⟨_, C5, k5, q9, h⟩ := h
  obtain ⟨s9, e11⟩ := (must_ok _ G8 d8 _).1 q9
  have p6 : C5 = G8 := congrArg (fun x : (Unit × Fork) × Tape => x.1.2) e11
  have p7 : k5 = d8 := congrArg (fun x : (Unit × Fork) × Tape => x.2) e11
  rw [p6, p7] at h
  have e12 := (pure_ok _ _ _ _).1 h
  have t1 : g = _ := congrArg (fun x : (Forest.Heard × Fork) × Tape => x.1.1) e12
  have t2 : F' = G8 := congrArg (fun x : (Forest.Heard × Fork) × Tape => x.1.2) e12
  have t3 : c' = d8 := congrArg (fun x : (Forest.Heard × Fork) × Tape => x.2) e12
  simp only [Bool.and_eq_true, beq_iff_eq] at s7
  exact ⟨⟨h0, theta, alpha, a, t, keys, table, lv0, lv, b0, b1', b2', b3', zb0, zb1, pt, sBit,
      vBit, row, F4, F5, F6, F7, G1, G2, G3, G4, G5, G6, G7, G8, c4, c5, c6, c7, d1, d2, d3, d4,
      d5, d6, d7, d8⟩,
    ⟨toOption_ok s1, s2, q1, q2, q3, q4, by simpa using s5, l1, l2, l3, l4, l5, l6, l7, l8, s7.1,
      s7.2, s8, s9, t1, t2, t3⟩⟩


end Fo.Tp
