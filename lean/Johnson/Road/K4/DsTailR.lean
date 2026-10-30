-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/DsTailR.lean: K4's WRITTEN ROUNDS ARE «[dT] ++ R.all»: the token point's round and
the sixteen pieces of the record `TailR` (OnBytes/Desc/First/P1/OwnMaps.lean), over which the
library's chain of a layers' sub-proof's own rounds is read off written rounds; THE PIECES AS DATA,
and what each draws. In the first sub-proof (g = 0) two more points stand behind the token point's.
Definitions, statements and proofs.

`scR k f y e`: the written rounds of a masked sumcheck of the table (`masked k f y e`), as a record
`ScR`; `masked_map`, `scR_ds`: they are the table's rows' written rounds, and meet `PscDs`.
`TailNum`, `tailRds n`, `tailR n`: eighteen numbers; the table's text from the limbs' scalars on, at
these numbers; its written rounds as a record `TailR`. `tailRds_map`: in a row these are the text's
rows' written rounds. `numsOf P hp g`, `rounds_eq`: the eighteen numbers of a place; K4's table is
the points' rows and then `tailRds` at them.
`k4Ds_later` (g ≠ 0), `k4Ds_first` (g = 0): EQUATIONS, AT EVERY PLACE p, under no other premise:
`k4Ds p = some ([dT] ++ R.all)`, at g = 0 `some ([dT] ++ ([dA] ++ ([dB] ++ R.all)))`, where R is
`tailR (numsOf p.P p.hp p.g)` and dT, dA, dB are the written rounds of the points' rows.
`Pieces R …`: what the sixteen pieces DRAW (how many elements each sends is left open there); how
many rounds each of the seven sumchecks has for its variables; every message holds elements of the
extension field alone. `tailR_pieces`. `Pieces.tailDs`: at a chain whose letters gN and gR are the
two joins' numbers, that is `TailDs`.
`k4_tail`, `k4_tail_first`: the same under «there are»: dT draws lt elements (dA ls + lt, dB
lPd - ls); `Pieces` holds in K4's own letters: the join's round draws lNI elements, the routed
join's ll - 1; the seven sumchecks have muV, lt, lt, lamS, muH, muH2 and lk rounds for their
variables.

HOW MANY ELEMENTS A ROUND SENDS is not in `Pieces`; it is read off the data: each round of each
piece is `rdOf` of its row, and `rdOf_items` (Johnson/Desc/First/K4/DsTail.lean) says that its
message is the row's `sent` elements. `point_silent`, `tailR_silent`: so the points' rounds, and the
six pieces that the maps read as rounds with an empty message (dN t1 d4 t5 dR t6), send nothing.

Limits. This speaks of the rounds that K4's block DECLARES (its own table's rows as entries): that
the made plan's entries at the place are these is not said here, and «every place» takes in places
that `covers` refuses (DsTail.lean's Limits). THAT A PIECE OF A CHAIN HAS THESE ROUNDS
(`k4Ds par = some pc.ds`) IS WHOEVER CUTS THE CHAIN's TO SHOW: a piece's rounds are a free field.
That a chain's letters (T.gN, T.gR; A.gT, A.gA, A.gB) are K4's numbers is whoever makes the chain's
value's. That muV is lNI + lPd + lt, and the like, stands under a premise in
Johnson/Road/K4/DsTailLens.lean. Nothing on soundness.
-/
import Johnson.Desc.First.K4.DsTail
import OnBytes.Desc.First.P1.OwnMaps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model OnBytes.Model.Layer OnBytes.Maker OnBytes.Slice OnBytes.Flat
open OnBytes.Desc.First.K4 OnBytes.Desc.First.P1

/-! ### A masked sumcheck -/

/-- The further variable's round: one element is drawn, by the rule that never gives 0. -/
theorem y_of_fit {y : Nat} {dY : RDT} (h : Fit { name := .pscY, sent := y, notZero := 1 } dY) :
    PlainDraws (Fmt.dsOf dY.entry dY.kind) ∧ nE (Fmt.dsOf dY.entry dY.kind) = 0 + 1 ∧
      nP (Fmt.dsOf dY.entry dY.kind) = 0 ∧ IsNZ (Fmt.dsOf dY.entry dY.kind) 0 ∧
      dY.entry.logN ≤ 64 := by
  have hE : dY.entry.drawE = 1 := h.drawE
  have hN : dY.entry.drawNZ = 1 := h.drawNZ
  refine ⟨plain_dsOf _ _ h.trits h.kind_ok.1, ?_, ?_, ?_, h.logN⟩
  · rw [nE_dsOf _ _ (by rw [hE, hN]) h.kind_ok.2, hE]
  · rw [nP_dsOf, h.poss]
  · unfold Fmt.dsOf
    rw [h.poss]
    show IsNZ (Fmt.dsElems dY.entry dY.kind ++ _) 0
    refine isNZ_append _ _ _ ?_
    unfold Fmt.dsElems
    rw [if_neg h.kind_ok.2, hE, hN]
    trivial

/-- The written rounds of the table's masked sumcheck `masked k f y e`. -/
def scR (k f y e : Nat) : ScR where
  dE := rdOf { name := .pscEpsilon, sent := f }
  vs := List.replicate k (rdOf { name := .pscRound, sent := 2 })
  dY := rdOf { name := .pscY, sent := y, notZero := 1 }
  dV := rdOf { name := .pscValues, sent := e, drawn := 0 }

/-- They are the rows' written rounds. -/
theorem masked_map (k f y e : Nat) : (masked k f y e).map rdOf = (scR k f y e).all := by
  simp [masked, scR, ScR.all]

/-- They draw what is asked of a masked sumcheck's written rounds. -/
theorem scR_ds (k f y e : Nat) : (scR k f y e).Ds := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := y_of_fit (fit_rdOf { name := .pscY, sent := y, notZero := 1 })
  refine ⟨fit_sd (fit_rdOf { name := .pscEpsilon, sent := f }) (Nat.zero_le 1),
    ⟨fun d hd => ?_, a1, a2, a3, a4, a5,
      fit_sd (fit_rdOf { name := .pscValues, sent := e, drawn := 0 }) (Nat.le_refl 0)⟩⟩
  rw [List.eq_of_mem_replicate hd]
  exact fit_sd (fit_rdOf { name := .pscRound, sent := 2 }) (Nat.zero_le 1)

/-! ### The table from the limbs' scalars on -/

/-- The eighteen numbers of the table's text from the limbs' scalars on: of the three rounds that
batch behind sent scalars, how many are sent and how many rows are batched (sL rL · sP rP · sW rW);
the coordinates of the two joins (gN gR); the seven sumchecks' variables (l1 … l7); the end values
of the second, third and fourth (e2 e3 e4). -/
structure TailNum where
  sL : Nat
  rL : Nat
  gN : Nat
  l1 : Nat
  sP : Nat
  rP : Nat
  l2 : Nat
  e2 : Nat
  l3 : Nat
  e3 : Nat
  l4 : Nat
  e4 : Nat
  l5 : Nat
  gR : Nat
  l6 : Nat
  sW : Nat
  rW : Nat
  l7 : Nat

/-- The table's text from the limbs' scalars on (OnBytes/Desc/First/K4/Rounds.lean, `rounds`, its
stretches 2 to 7), at these numbers. -/
def tailRds (n : TailNum) : List Rd :=
  [batchRd n.sL n.rL, pointRd .join n.gN] ++ layerRds n.l1 ++
  [batchRd n.sP n.rP] ++ masked n.l2 2 2 n.e2 ++
  masked n.l3 2 1 n.e3 ++ [batchRd 0 2] ++
  masked n.l4 1 2 n.e4 ++
  layerRds n.l5 ++ [pointRd .join n.gR] ++ layerRds n.l6 ++
  [batchRd n.sW n.rW] ++ masked n.l7 1 1 1

/-- **The sixteen pieces, as data.** -/
def tailR (n : TailNum) : TailR where
  dL := rdOf (batchRd n.sL n.rL)
  dN := rdOf (pointRd .join n.gN)
  r1 := scR n.l1 1 2 2
  t1 := rdOf { name := .line }
  dP := rdOf (batchRd n.sP n.rP)
  r2 := scR n.l2 2 2 n.e2
  r3 := scR n.l3 2 1 n.e3
  d4 := rdOf (batchRd 0 2)
  r4 := scR n.l4 1 2 n.e4
  r5 := scR n.l5 1 2 2
  t5 := rdOf { name := .line }
  dR := rdOf (pointRd .join n.gR)
  r6 := scR n.l6 1 2 2
  t6 := rdOf { name := .line }
  dW := rdOf (batchRd n.sW n.rW)
  r7 := scR n.l7 1 1 1

/-- **In a row they are the rows' written rounds.** -/
theorem tailRds_map (n : TailNum) : (tailRds n).map rdOf = (tailR n).all := by
  simp only [tailRds, layerRds, List.map_append, masked_map, List.map_cons, tailR, TailR.all,
    List.append_assoc, List.append_nil, List.cons_append, List.nil_append]

/-- The eighteen numbers of a place. -/
def numsOf (P : Pub) (hp : HPlan2) (g : Nat) : TailNum where
  sL := ledNS P.y.h.xl * P.y.NI
  rL := ledNS P.y.h.xl
  gN := P.rd.lNI
  l1 := P.rd.muV
  sP := ledNP P.y.h.xl * P.y.NI
  rP := ledNP P.y.h.xl * P.y.NI
  l2 := P.y.h.lt
  e2 := ledNO P.y.h.xl * P.y.NI
  l3 := P.y.h.lt
  e3 := nEndT P.y
  l4 := hp.lamS
  e4 := 2 + (1 + P.y.LamM) + (hp.NCL - (if g == 0 then 1 else 0))
  l5 := P.rd.muH
  gR := P.y.h.ll - 1
  l6 := P.rd.muH2
  sW := if g == 0 then 1 else 0
  rW := hp.NCL
  l7 := P.wsLay.lk

/-- The rows of the points in front: the token point's; in the first sub-proof two more. -/
def frontRds (P : Pub) (g : Nat) : List Rd :=
  [pointRd .zero P.y.h.lt] ++
    (if g == 0 then [pointRd .zero (P.y.ls + P.y.h.lt), pointRd .zero (P.y.lPd - P.y.ls)] else [])

/-- **K4's table is the points' rows and then `tailRds` at the place's numbers.** -/
theorem rounds_eq (P : Pub) (hp : HPlan2) (g : Nat) :
    rounds P hp g = frontRds P g ++ tailRds (numsOf P hp g) := by
  simp only [rounds, frontRds, tailRds, numsOf, List.append_assoc]

/-! ### At a place: the equations -/

theorem k4Ds_cut (p : Par) :
    k4Ds p = some ((frontRds p.P p.g).map rdOf ++ (tailR (numsOf p.P p.hp p.g)).all) := by
  rw [k4Ds_eq, rounds_eq, List.map_append, tailRds_map]

/-- **K4's written rounds at a sub-proof that is not the first.** -/
theorem k4Ds_later {p : Par} (hg : (p.g == 0) = false) :
    k4Ds p = some ([rdOf (pointRd .zero p.P.y.h.lt)] ++ (tailR (numsOf p.P p.hp p.g)).all) := by
  rw [k4Ds_cut]
  simp only [frontRds, hg, Bool.false_eq_true, if_false, List.append_nil, List.map_cons,
    List.map_nil]

/-- **At the first sub-proof.** -/
theorem k4Ds_first {p : Par} (hg : (p.g == 0) = true) :
    k4Ds p = some ([rdOf (pointRd .zero p.P.y.h.lt)] ++
      ([rdOf (pointRd .zero (p.P.y.ls + p.P.y.h.lt))] ++
        ([rdOf (pointRd .zero (p.P.y.lPd - p.P.y.ls))] ++
          (tailR (numsOf p.P p.hp p.g)).all))) := by
  rw [k4Ds_cut]
  simp only [frontRds, hg, if_true, List.cons_append, List.nil_append, List.map_cons, List.map_nil]

/-! ### What the pieces draw -/

/-- What the sixteen pieces DRAW, in plain numbers: the join's round gN elements, the routed join's
gR, each of the seven other rounds outside the sumchecks one element, a sumcheck's rounds what
`PscDs` says; how many elements a round sends is left open («there is a number»). The seven
sumchecks have l1, …, l7 rounds for their variables. Every item of every message is an element of
the extension field. -/
structure Pieces (R : TailR) (gN gR l1 l2 l3 l4 l5 l6 l7 : Nat) : Prop where
  l : Draws1 R.dL
  n : DrawsPt gN R.dN
  s1 : R.r1.Ds
  t1 : Draws1 R.t1
  p : Draws1 R.dP
  s2 : R.r2.Ds
  s3 : R.r3.Ds
  d4 : Draws1 R.d4
  s4 : R.r4.Ds
  s5 : R.r5.Ds
  t5 : Draws1 R.t5
  r : DrawsPt gR R.dR
  s6 : R.r6.Ds
  t6 : Draws1 R.t6
  w : Draws1 R.dW
  s7 : R.r7.Ds
  n1 : R.r1.vs.length = l1
  n2 : R.r2.vs.length = l2
  n3 : R.r3.vs.length = l3
  n4 : R.r4.vs.length = l4
  n5 : R.r5.vs.length = l5
  n6 : R.r6.vs.length = l6
  n7 : R.r7.vs.length = l7
  allE : ∀ d ∈ R.all, ∀ it ∈ d.items, it = Fmt.Item.e

/-- At a chain whose two letters are these numbers: what OwnMaps.lean asks of the written rounds. -/
theorem Pieces.tailDs {M X : Type} {T : Cb.Pv.Lay.LayTail OnBytes.Slice.GE M X} {R : TailR}
    {l1 l2 l3 l4 l5 l6 l7 : Nat} (h : Pieces R T.gN T.gR l1 l2 l3 l4 l5 l6 l7) : TailDs T R :=
  ⟨h.l, h.n, h.s1, h.t1, h.p, h.s2, h.s3, h.d4, h.s4, h.s5, h.t5, h.r, h.s6, h.t6, h.w, h.s7⟩

/-- What a row's written round draws, where the row draws no fewer elements than it draws by the
rule that never gives 0. -/
theorem rdOf_draws (d : Rd) (hz : d.notZero ≤ d.drawn) : DrawsPt d.drawn (rdOf d) :=
  fit_sd (fit_rdOf d) hz

/-- **The data's pieces draw so.** -/
theorem tailR_pieces (n : TailNum) :
    Pieces (tailR n) n.gN n.gR n.l1 n.l2 n.l3 n.l4 n.l5 n.l6 n.l7 where
  l := rdOf_draws (batchRd n.sL n.rL) (Nat.zero_le 1)
  n := rdOf_draws (pointRd .join n.gN) (Nat.zero_le _)
  s1 := scR_ds _ _ _ _
  t1 := rdOf_draws { name := .line } (Nat.zero_le 1)
  p := rdOf_draws (batchRd n.sP n.rP) (Nat.zero_le 1)
  s2 := scR_ds _ _ _ _
  s3 := scR_ds _ _ _ _
  d4 := rdOf_draws (batchRd 0 2) (Nat.zero_le 1)
  s4 := scR_ds _ _ _ _
  s5 := scR_ds _ _ _ _
  t5 := rdOf_draws { name := .line } (Nat.zero_le 1)
  r := rdOf_draws (pointRd .join n.gR) (Nat.zero_le _)
  s6 := scR_ds _ _ _ _
  t6 := rdOf_draws { name := .line } (Nat.zero_le 1)
  w := rdOf_draws (batchRd n.sW n.rW) (Nat.zero_le 1)
  s7 := scR_ds _ _ _ _
  n1 := by simp [tailR, scR]
  n2 := by simp [tailR, scR]
  n3 := by simp [tailR, scR]
  n4 := by simp [tailR, scR]
  n5 := by simp [tailR, scR]
  n6 := by simp [tailR, scR]
  n7 := by simp [tailR, scR]
  allE := by
    intro d hd
    rw [← tailRds_map] at hd
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hd
    exact (fit_rdOf r).allE

/-- A point's round sends nothing. -/
theorem point_silent (r : RoundName) (n : Nat) : (rdOf (pointRd r n)).items = [] :=
  rdOf_items (pointRd r n)

/-- **The six pieces that the maps read as rounds with an empty message send nothing.** -/
theorem tailR_silent (n : TailNum) :
    (tailR n).dN.items = [] ∧ (tailR n).t1.items = [] ∧ (tailR n).d4.items = [] ∧
      (tailR n).t5.items = [] ∧ (tailR n).dR.items = [] ∧ (tailR n).t6.items = [] :=
  ⟨rdOf_items (pointRd .join n.gN), rdOf_items { name := .line }, rdOf_items (batchRd 0 2),
    rdOf_items { name := .line }, rdOf_items (pointRd .join n.gR), rdOf_items { name := .line }⟩

/-! ### At a place: under «there are» -/

/-- **K4's written rounds are the token point's round and the sixteen pieces**, at a sub-proof that
is not the first. -/
theorem k4_tail {p : Par} (hg : (p.g == 0) = false) :
    ∃ (dT : RDT) (R : TailR), k4Ds p = some ([dT] ++ R.all) ∧ DrawsPt p.P.y.h.lt dT ∧
      Pieces R p.P.rd.lNI (p.P.y.h.ll - 1) p.P.rd.muV p.P.y.h.lt p.P.y.h.lt p.hp.lamS p.P.rd.muH
        p.P.rd.muH2 p.P.wsLay.lk :=
  ⟨_, _, k4Ds_later hg, rdOf_draws (pointRd .zero p.P.y.h.lt) (Nat.zero_le _),
    tailR_pieces (numsOf p.P p.hp p.g)⟩

/-- **The first sub-proof's**: two more points stand behind the token point's round. -/
theorem k4_tail_first {p : Par} (hg : (p.g == 0) = true) :
    ∃ (dT dA dB : RDT) (R : TailR), k4Ds p = some ([dT] ++ ([dA] ++ ([dB] ++ R.all))) ∧
      DrawsPt p.P.y.h.lt dT ∧ DrawsPt (p.P.y.ls + p.P.y.h.lt) dA ∧
      DrawsPt (p.P.y.lPd - p.P.y.ls) dB ∧
      Pieces R p.P.rd.lNI (p.P.y.h.ll - 1) p.P.rd.muV p.P.y.h.lt p.P.y.h.lt p.hp.lamS p.P.rd.muH
        p.P.rd.muH2 p.P.wsLay.lk :=
  ⟨_, _, _, _, k4Ds_first hg, rdOf_draws (pointRd .zero p.P.y.h.lt) (Nat.zero_le _),
    rdOf_draws (pointRd .zero (p.P.y.ls + p.P.y.h.lt)) (Nat.zero_le _),
    rdOf_draws (pointRd .zero (p.P.y.lPd - p.P.y.ls)) (Nat.zero_le _),
    tailR_pieces (numsOf p.P p.hp p.g)⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.scR_ds
#print axioms OnBytes.Road.K4.tailRds_map
#print axioms OnBytes.Road.K4.rounds_eq
#print axioms OnBytes.Road.K4.k4Ds_later
#print axioms OnBytes.Road.K4.k4Ds_first
#print axioms OnBytes.Road.K4.Pieces.tailDs
#print axioms OnBytes.Road.K4.tailR_pieces
#print axioms OnBytes.Road.K4.point_silent
#print axioms OnBytes.Road.K4.tailR_silent
#print axioms OnBytes.Road.K4.k4_tail
#print axioms OnBytes.Road.K4.k4_tail_first
