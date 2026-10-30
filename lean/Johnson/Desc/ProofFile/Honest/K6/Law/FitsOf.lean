-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/FitsOf.lean: THE NAMED PUBLIC PREMISE `headFitsB`
(Honest/K6/Wit.lean: 23 named tests with code on public numbers) ACCEPTS WHEREVER THE PUBLIC NUMBERS
ARE THE FULL SIZE's: from two structures of premises and one premise more (hu: the test on the
weights' unit accepts). NO SCOPE: no set of public files is named here.

What the file holds. `headFitsB_iff`: the test is its seven groups. `headFitsB_congr`: of the ground
it reads the public structure, the number of links and the last link's name. `HeadFull X`: the
numbers of the public structure that the tests read, as written numbers: a premise's form.
`HeadTable Z G`: 25 links, the last one named "H", and the table of steps is the library's written
one: a premise's form. `rowsFit_of`, `roomFits_of`, `pointsFit_of`, `lookRounds_full`: the tests
that read the numbers. `last_unit`, `unitFits_of`: the last unit of the committed weights' layout,
from the verifier's own function's return alone. `steps_written`: the rounds in front of the head's
two steps, off the written table, by the kernel. `headFitsB_of`: ALL 23 ACCEPT. Steps to these:
`cols6` and `lookFace` (written numbers), `lookRounds_of`, `lookRounds_31_19`, `keyPt_full`.

Called. `Hd.NumH` (Johnson/Road/HeadPlace.lean); `Cond.bFull`
(Johnson/Desc/Kinds/Law/K06Condition.lean); `head_unit` (Johnson/Road/HeadWeight.lean), `PublicH.ws`
by `publicH_of_public` (Johnson/Road/HeadMade.lean), `public_parts` (Johnson/Road/HeadPub.lean);
`size_of_pad` (Johnson/Road/FormsKeysLookP.lean), `range_map_getD'`
(Johnson/Road/FormsKeysLook.lean); `last_append` (Johnson/Desc/First/Att/K05Merged.lean);
`keyPt_size` (Honest/K6/Hears/HalfPoint.lean); `cutWritten` (Johnson/AtFull/Cut/CutWrittenLit.lean).

Limits. THE TWO STRUCTURES, AND hu, ARE PREMISES: that any public files meet them is another file's
to show (a joining file, which names the goals' scope; it is not among what this file imports). No
run is spoken of: the tests read public numbers alone. The full size alone. No module under
lean/Johnson/Goal/ is imported, by name or beneath. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K6.Wit
import Johnson.Desc.ProofFile.Honest.K6.Hears.HalfPoint
import Johnson.Road.HeadPlace
import Johnson.Road.HeadMade
import Johnson.Road.HeadPub
import Johnson.Road.HeadWeight
import Johnson.Road.FormsKeysLookP
import Johnson.Desc.Kinds.HeadCallLaw
import Johnson.Desc.Kinds.Law.K06Condition
import Johnson.Desc.First.Att.K05Merged
import Johnson.AtFull.Cut.CutWrittenLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The library's default table of scales is no instance in this file: no statement here can take it
in silence. An instance is taken away, none is added. -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open VerifiableInference.Desc.Kinds.Head (laidOk lJ sizesOf readsNeed callList)
open VerifiableInference.Desc.Kinds.Head.Law (callKeys)
open VerifiableInference.Desc.Kinds (Point)
open OnBytes.Model.Verify (publicOf Public borderOf)
open OnBytes.Road (Hd.NumH)
open Johnson.AtFull.Cut (cutWritten)

/-! ## 1 The assembly; what the test reads of the ground -/

/-- **The test is its seven groups.** No premise. -/
theorem headFitsB_iff (Z : Pub) (G : Ground) :
    headFitsB Z G = true ↔
      (headWhereOf Z G).look.isSome = true ∧ laidOk G.W = true ∧
        headRowsFit (headWhereOf Z G) = true ∧ headRoomFits (headWhereOf Z G) = true ∧
        headUnitFits G.W.layers.wsLay G.W.hS = true ∧ headPointsFit (headWhereOf Z G) = true ∧
        headEndsFit (headWhereOf Z G) = true := by
  have hl : ((headLaidTests (headWhereOf Z G)).map fun t =>
      ("the laid numbers: " ++ t.1, t.2)).all (·.2) = laidOk G.W := by
    rw [List.all_map]
    rfl
  unfold headFitsB headFits headFitsOn
  rw [List.all_cons, List.all_append, hl]
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact Iff.rfl

/-- **Of the ground the test reads the public structure W, the number of links and the last link's
name: no more.** -/
theorem headFitsB_congr (Z : Pub) {G G' : Ground} (hW : G'.W = G.W)
    (hs : G'.built.size = G.built.size)
    (hn : G'.built.back?.map (·.name) = G.built.back?.map (·.name)) :
    headFitsB Z G' = headFitsB Z G := by
  have e : headWhereOf Z G' = headWhereOf Z G := by
    unfold headWhereOf headLookNumbers
    rw [hW, hs]
    cases h1 : G'.built.back? with
    | none =>
      cases h2 : G.built.back? with
      | none => rfl
      | some Y =>
        rw [h1, h2] at hn
        cases hn
    | some Y' =>
      cases h2 : G.built.back? with
      | none =>
        rw [h1, h2] at hn
        cases hn
      | some Y =>
        rw [h1, h2] at hn
        have en : Y'.name = Y.name := Option.some.inj hn
        simp [en]
  unfold headFitsB headFits
  rw [e, hW]

/-! ## 2 The two structures of premises -/

/-- The six calls' numbers of column coordinates at the full size. -/
def cols6 : List Nat := [18, 18, 18, 17, 17, 17]

/-- **THE NUMBERS OF THE PUBLIC STRUCTURE THAT THE TESTS READ, AS WRITTEN NUMBERS: THE FULL
SIZE's.** num: the positions, the parts and the rows and columns of the head's own three matrices.
border: what the head reads of the layers' layout. S2: the features of a block. needZ, needFC,
needRow: how many features the verifier's text reads of the three. lt, ls: the bits of a position
and of a block's row. cols: the kind's own number of column coordinates of each call. NC, dT, rK,
kT, cK, iota: the shape of the lookup on the head's calls. place: that lookup's place and shape, at
link number 24 (the last of `HeadTable`'s 25) and the flag false.
laid: the library's 17 tests on the laid numbers. At two fields it asks more than the tests read
(border: six numbers, of which two are read; num: the width beside). It is a structure of premises:
nothing is claimed of it. -/
structure HeadFull (X : Public) : Prop where
  num : Hd.NumH X.hS X.HLy
  border : borderOf X.y = VerifiableInference.Desc.Kinds.Head.Law.Cond.bFull
  S2 : X.hS.S2 = 64
  needZ : ((readsNeed X.hS).lookup "hf@Z").getD 0 = 19262
  needFC : ((readsNeed X.hS).lookup "hd@zt_FC").getD 0 = 10240
  needRow : ((readsNeed X.hS).lookup "hr@zt_ROW").getD 0 = 120
  lt : X.hS.lt = 10
  ls : X.hS.la - X.hS.lt = 6
  cols : ∀ q, q < 6 →
    @lJ (sizesOf X.hS) (OnBytes.Model.Head.keyFloor X.hS) (callKeys q) = cols6.getD q 0
  NC : X.HLy.fs.NC = 6
  dT : X.HLy.fs.dT = 27
  rK : X.HLy.fs.rK = 4
  kT : X.HLy.fs.kT = 16
  cK : X.HLy.fs.cK = 3
  iota : X.HLy.fs.iota = #[1, 1, 1, 0, 0, 0]
  place : ∃ p, VerifiableInference.Desc.First.Look.placeAt X 24 false = some p ∧
    p.shape = some X.HLy.fs
  laid : laidOk X = true

/-- **What the tests read beside the public structure**: there are 25 links; the last one is named
"H"; the public part's table of steps is the library's written one. It is a structure of premises:
nothing is claimed of it. -/
structure HeadTable (Z : Pub) (G : Ground) : Prop where
  size : G.built.size = 25
  name : G.built.back?.map (·.name) = some "H"
  cuts : Z.cuts = cutWritten

/-! ## 3 The tests that read the public structure -/

section
variable {X : Public}

/-- **"Every matrix has a row for each position."** CONDITIONAL: on `HeadFull`, and on e1, e2, e3:
N's shape, layout and border are X's. The other theorems of this section that take `HeadFull` are
conditional on it likewise. -/
theorem rowsFit_of (Fu : HeadFull X) (N : HeadWhere) (e1 : N.shape = X.hS) (e2 : N.lay = X.HLy)
    (e3 : N.border = borderOf X.y) : headRowsFit N = true := by
  have Nm := Fu.num
  unfold headRowsFit
  rw [e1, e2, e3, Fu.border]
  dsimp only
  rw [Nm.T, Nm.NHf, Nm.m, Nm.k, Nm.mD, Nm.kD, Nm.mR, Nm.kR]
  decide

/-- **"The features have room."** -/
theorem roomFits_of (Fu : HeadFull X) (N : HeadWhere) (e1 : N.shape = X.hS) (e2 : N.lay = X.HLy) :
    headRoomFits N = true := by
  have Nm := Fu.num
  unfold headRoomFits
  rw [e1, e2]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [Fu.needZ, Fu.needFC, Fu.needRow, Fu.S2, Nm.NHf, Nm.k, Nm.fc, Nm.kD, Nm.fcD, Nm.kR, Nm.fcR]
  decide

/-- **THE LAST UNIT OF THE PUBLIC PART's LAYOUT OF THE COMMITTED WEIGHTS IS THE HEAD's**: of kind
13, two digits a weight, the group "x" over the vocabulary and the group "kk" over the coordinates,
in this order. CONDITIONAL: the public part is what the verifier's own function returns: no more. A
call of the library's `head_unit` (Johnson/Road/HeadWeight.lean) at `PublicH.ws`
(Johnson/Road/HeadMade.lean); that the head's shape is made of the same scan as the weights' shape:
`public_parts` (Johnson/Road/HeadPub.lean). -/
theorem last_unit {pol KL : ByteArray} {lay : Option ByteArray}
    (hX : publicOf pol KL lay = .ok X) :
    ∃ u, X.layers.wsLay.U.back? = some u ∧ u.X = 13 ∧ u.nlw = 2 ∧
      u.g.map (fun g => (g.name, g.R)) = [("x", X.hS.V), ("kk", X.hS.d)] := by
  obtain ⟨o, ho⟩ := OnBytes.Road.Hd.head_unit (OnBytes.Road.Hd.publicH_of_public hX).ws
  obtain ⟨P, y, -, eP, ey, eS, -⟩ := OnBytes.Road.Hd.public_parts hX
  refine ⟨_, ho, rfl, rfl, ?_⟩
  rw [eS, eP]
  rfl

/-- **"The weights' unit."** CONDITIONAL: as the last. -/
theorem unitFits_of {pol KL : ByteArray} {lay : Option ByteArray}
    (hX : publicOf pol KL lay = .ok X) : headUnitFits X.layers.wsLay X.hS = true := by
  obtain ⟨u, hu, h1, h2, h3⟩ := last_unit hX
  unfold headUnitFits
  rw [hu]
  show (u.X == 13 && u.nlw == 2 &&
    u.g.map (fun g => (g.name, g.R)) == [("x", X.hS.V), ("kk", X.hS.d)]) = true
  rw [h1, h2, h3]
  simp

/-- A face with the five numbers that the list of stages and a stage's number of rounds read: a
shift; counts of 2 ^ 5 places for bits, of which 32 (the planes) are real; one part with 2 ^ v keys;
a table of 2 ^ d rows; nothing elsewhere. -/
def lookFace (v d : Nat) : K3.LFace :=
  { shifted := true, mu := 5, planes := 32, parts := [v], d := d, orders := fun _ _ => []
    padding := [], leaf := fun _ _ _ => OnBytes.zeroE }

/-- A lookup's number of rounds hangs on its two numbers of bits alone. No premise. -/
theorem lookRounds_of (h : OnBytes.Model.Forest.Shape) :
    headLookRounds h =
      ((K3.stages (lookFace h.v h.d)).map (K3.Stage.rounds (lookFace h.v h.d))).sum := rfl

/-- At 31 and 19 bits: 1,080. By the kernel. -/
theorem lookRounds_31_19 :
    ((K3.stages (lookFace 31 19)).map (K3.Stage.rounds (lookFace 31 19))).sum = 1080 := by
  decide +kernel

/-- The lookup on the head's calls has 1,080 rounds, by the list of stages of the lookup's honest
side (`K3.stages`, Honest/K3/Stages.lean). CONDITIONAL: on `HeadFull`. -/
theorem lookRounds_full (Fu : HeadFull X) : headLookRounds X.HLy.fs = 1080 := by
  have hv : X.HLy.fs.v = 31 := by
    show X.HLy.fs.dT + X.HLy.fs.rK = 31
    rw [Fu.dT, Fu.rK]
  have hd : X.HLy.fs.d = 19 := by
    show X.HLy.fs.kT + X.HLy.fs.cK = 19
    rw [Fu.kT, Fu.cK]
  rw [lookRounds_of, hv, hd]
  exact lookRounds_31_19

/-- **A call's key point, cut off a last point of 31 coordinates at the full size's shape**: its
length, and that it ends as the lookup's point ends. CONDITIONAL: four numbers of the shape; the
point's length; q < 6. The length: a call of the library's `size_of_pad`
(Johnson/Road/FormsKeysLookP.lean), whose three premises are the cut's three lines; the end: the
library's `last_append` (Johnson/Desc/First/Att/K05Merged.lean). The verifier's side of the same two
clauses, at what the lookup has heard, stands in Johnson/Desc/Kinds/Law/K6GivenOfLeft.lean. -/
theorem keyPt_full (h : OnBytes.Model.Forest.Shape) (hNC : h.NC = 6) (hdT : h.dT = 27)
    (hrK : h.rK = 4) (hio : h.iota = #[1, 1, 1, 0, 0, 0]) (pt : Array OnBytes.E)
    (hp : pt.size = 31) (q : Nat) (hq : q < 6) :
    ((K3.keyPtsOf h pt).zk.getD q #[]).size = cols6.getD q 0 + 10 ∧
      Point.last ((K3.keyPtsOf h pt).zk.getD q #[]) 16 = Point.last (K3.keyPtsOf h pt).zx 16 := by
  have hc : q < h.NC := by
    rw [hNC]
    exact hq
  constructor
  · obtain ⟨h0, -, -⟩ := OnBytes.Road.size_of_pad (fo := h) (rho := pt)
      (zx := (K3.keyPtsOf h pt).zx) (zy := (K3.keyPtsOf h pt).zy) (zk := (K3.keyPtsOf h pt).zk)
      rfl rfl rfl hc
    rw [h0, hp, hdT, hrK, hio]
    interval_cases q <;> decide
  · have hz : (K3.keyPtsOf h pt).zk.getD q #[] =
        (K3.keyPtsOf h pt).zy.extract (h.rK - h.iota.getD q 0) (K3.keyPtsOf h pt).zy.size ++
          (K3.keyPtsOf h pt).zx := OnBytes.Road.range_map_getD' _ _ _ hc
    rw [hz]
    refine VerifiableInference.Desc.First.Att.P.last_append _ ?_
    show 16 ≤ (pt.extract 0 h.dT).size
    rw [Array.size_extract, hdT, hp]
    decide

/-- **"The key points' lengths"**, whatever the number of rounds in front of the lookup. -/
theorem pointsFit_of (Fu : HeadFull X) (N : HeadWhere) (e1 : N.shape = X.hS) (base : Nat)
    (e4 : N.look = some (X.HLy.fs, base)) : headPointsFit N = true := by
  have hv : X.HLy.fs.v = 31 := by
    show X.HLy.fs.dT + X.HLy.fs.rK = 31
    rw [Fu.dT, Fu.rK]
  have key := keyPt_full X.HLy.fs Fu.NC Fu.dT Fu.rK Fu.iota
    ((K3.ptsOf (VerifiableInference.Desc.K3.faceOf X.HLy.fs) base
      (headLabels (base + headLookRounds X.HLy.fs))).keyPt 0 X.HLy.fs.v)
    ((Hears.keyPt_size _ _ _ _ _).trans hv)
  have hmem : ∀ c ∈ callList.zipIdx, c.2 < 6 ∧ c.1 = callKeys c.2 := by
    intro c hc
    have hz : callList.zipIdx = [(callKeys 0, 0), (callKeys 1, 1), (callKeys 2, 2),
        (callKeys 3, 3), (callKeys 4, 4), (callKeys 5, 5)] := rfl
    rw [hz] at hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨by decide, rfl⟩
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨by decide, rfl⟩
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨by decide, rfl⟩
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨by decide, rfl⟩
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨by decide, rfl⟩
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨by decide, rfl⟩
    cases hc
  unfold headPointsFit
  rw [e4]
  dsimp only
  rw [e1]
  refine List.all_eq_true.2 fun c hc => ?_
  obtain ⟨hq, hk⟩ := hmem c hc
  obtain ⟨k1, k2⟩ := key c.2 hq
  have hJ : @lJ (sizesOf X.hS) (OnBytes.Model.Head.keyFloor X.hS) c.1 = cols6.getD c.2 0 := by
    rw [hk]
    exact Fu.cols c.2 hq
  rw [Bool.and_eq_true]
  constructor
  · rw [beq_iff_eq]
    show ((K3.keyPtsOf X.HLy.fs _).zk.getD c.2 #[]).size = _ + X.hS.lt
    rw [k1, Fu.lt]
    exact congrArg (· + 10) hJ.symm
  · rw [beq_iff_eq]
    show Point.last ((K3.keyPtsOf X.HLy.fs _).zk.getD c.2 #[]) ((X.hS.la - X.hS.lt) + X.hS.lt) =
      Point.last (K3.keyPtsOf X.HLy.fs _).zx ((X.hS.la - X.hS.lt) + X.hS.lt)
    rw [Fu.ls, Fu.lt]
    exact k2

end

/-! ## 4 The table of steps -/

/-- **The rounds in front of the two steps of the head**, at a public part whose table of steps is
the written one. By the kernel, on the written table. -/
theorem steps_written {Z : Pub} (hc : Z.cuts = cutWritten) :
    Z.roundsBefore? (headLookStep "H") = some 46289 ∧
      Z.roundsBefore? (headOwnStep "H") = some 47369 := by
  unfold Pub.roundsBefore? Pub.roundsBefore
  rw [hc]
  exact ⟨by decide +kernel, by decide +kernel⟩

/-! ## 5 All 23 -/

/-- **THE NAMED PUBLIC PREMISE HOLDS WHEREVER THE PUBLIC NUMBERS ARE THE FULL SIZE's.** CONDITIONAL:
on `HeadFull` at the ground's public structure and on `HeadTable`; hu: the test on the weights' unit
accepts (`unitFits_of` has it where that structure is what the verifier's own function returns). -/
theorem headFitsB_of {Z : Pub} {G : Ground} (Fu : HeadFull G.W) (Tb : HeadTable Z G)
    (hu : headUnitFits G.W.layers.wsLay G.W.hS = true) : headFitsB Z G = true := by
  obtain ⟨t1, t2⟩ := steps_written Tb.cuts
  obtain ⟨Y, hY, hYn⟩ := Option.map_eq_some_iff.1 Tb.name
  have hYn' : Y.name = "H" := hYn
  obtain ⟨pc, ec, sc⟩ := Fu.place
  have hlook : (headWhereOf Z G).look = some (G.W.HLy.fs, 46289) := by
    show headLookNumbers Z G = _
    unfold headLookNumbers
    rw [hY, Tb.size]
    show (VerifiableInference.Desc.First.Look.placeAt G.W 24 false).bind (fun p =>
      p.shape.bind fun h => (Z.roundsBefore? (headLookStep Y.name)).bind fun base =>
        some (h, base)) = _
    rw [ec, hYn']
    show pc.shape.bind (fun h => (Z.roundsBefore? (headLookStep "H")).bind fun base =>
      some (h, base)) = _
    rw [sc, t1]
    rfl
  have hown : (headWhereOf Z G).own = some 47369 := by
    show G.built.back?.bind _ = _
    rw [hY]
    show Z.roundsBefore? (headOwnStep Y.name) = _
    rw [hYn', t2]
  refine (headFitsB_iff Z G).2 ⟨by rw [hlook]; rfl, Fu.laid, rowsFit_of Fu _ rfl rfl rfl,
    roomFits_of Fu _ rfl rfl, hu, pointsFit_of Fu _ rfl 46289 hlook, ?_⟩
  unfold headEndsFit
  rw [hlook, hown]
  show (47369 == 46289 + headLookRounds G.W.HLy.fs) = true
  rw [lookRounds_full Fu]
  rfl

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.headFitsB_iff
#print axioms ProofFile.Honest.K6.headFitsB_congr
#print axioms ProofFile.Honest.K6.rowsFit_of
#print axioms ProofFile.Honest.K6.roomFits_of
#print axioms ProofFile.Honest.K6.last_unit
#print axioms ProofFile.Honest.K6.unitFits_of
#print axioms ProofFile.Honest.K6.lookRounds_of
#print axioms ProofFile.Honest.K6.lookRounds_31_19
#print axioms ProofFile.Honest.K6.lookRounds_full
#print axioms ProofFile.Honest.K6.keyPt_full
#print axioms ProofFile.Honest.K6.pointsFit_of
#print axioms ProofFile.Honest.K6.steps_written
#print axioms ProofFile.Honest.K6.headFitsB_of
