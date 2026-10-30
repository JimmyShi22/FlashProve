-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/TablesP.lean: kind K5: the places and the weight vectors of the segment's tables,
over the kind's own records (Att/Geo.lean, Att/Points.lean).

What a table is. The claims read values of the committed matrices at points. Each reading is a sum
over a block of a matrix's rows under a weight vector; the prover commits to all these sums in one
array; the smallness test ties the array to the matrices. This file says, in the protocol's order,
which tables there are: for each its matrix, its block length, its weight vector and its first entry.

Main names: `Fun1`, `Placed`, `ScoreT`, `TablesP`: the records. `LookIn`: what the lookup's kind hands in
(its point, whether its planes' matrix has a lawful number of row bits, its three weight vectors).
`tablesP`: all tables of a segment.
The routines are Att/Tables.lean's with the records exchanged, and the pure helpers follow the lines
of OnBytes/Model/AttentionTables.lean that their docstrings name; no definition of OnBytes/Model is
called but the field's arithmetic.
What the lookup's kind hands in is taken as it comes: that the three weight vectors are the real ones
where its flag is true is that kind's debt, and no test asks their lengths.
Nor does a test in this file ask the length of any other weight vector, but the tokens' in lng:
T.weights drops the length that it is handed (PlaceM.weights, OnBytes/Model/AttentionTables.lean,
spends that length in the dry run alone).
It refuses at seven places: five tests on numbers (two of them, in lng, read lengths of arrays that
are made of heard values; three read public numbers alone), two on values (the units' inner points
share coordinates with the lookup's point).

Definitions with code; no theorem. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Points

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes

/-- A table, as the smallness test takes it: the matrix's number · the rows in a block · the weights · which vector holds it (2: the array of tables) · its first entry there. -/
structure Fun1 where
  mat : Nat
  len : Nat
  phi : Array E
  tree : Nat
  start : Nat

/-- The tables placed so far: the first free entry · pairs (a table's first entry, its length), the newest first · the tables in their order. -/
structure Placed where
  next : Nat := 0
  tabLen : List (Nat × Nat) := []
  funs : Array Fun1 := #[]

/-- A softmax-table unit's three tables: on the maxima · the queries · the keys. -/
structure ScoreT where
  tM : Nat
  tQ : Nat
  tK : Nat

/-- The tables' first entries, two points, the lengths, and the list for the smallness test. After OnBytes/Model/AttentionHeard.lean (Tables). -/
structure TablesP where
  ptM : Array E
  ptD : Array E
  tA : Nat
  tVM : Nat
  tVD : Nat
  score : Array ScoreT
  hW : Nat
  hX : Nat
  hE : Nat
  hT : Nat
  hPi : Nat
  hR2 : Nat
  tO : Nat
  qO : Nat
  qVM : Nat
  qVD : Nat
  qF : Nat
  qKx : Nat
  tBit0 : Nat
  tBit1 : Nat
  tPin : Nat
  tabLen : List (Nat × Nat)
  funs : Array Fun1

/-- What the lookup's kind hands in. ITS DEBT: where planesOk is true the three vectors are the real ones (in OnBytes/Model phiB gives nothing exactly when planeCols refuses). -/
structure LookIn where
  zx : Array E
  planesOk : Bool
  phiB0 : Array E
  phiB1 : Array E
  phiP : Array E

/-- The tables placed so far; a refusal. -/
abbrev T : Type → Type := StateT Placed Option

/-- A test; the name is dropped. -/
def mustAs (_name : String) (b : Bool) : Option PUnit := if b then some ⟨⟩ else none

/-- The list has a matrix number mat, len is not 0 and divides its rows m, and elems is k (m / len). After AttentionTables.lean:78-81. -/
def fits (mats : Array (Nat × Nat)) (mat len elems : Nat) : Bool :=
  match mats[mat]? with
  | none => false
  | some M => len != 0 && M.1 % len == 0 && elems == M.2 * (M.1 / len)

/-- After AttentionTables.lean:122. -/
def lastCoords (z : Array E) (n : Nat) : Array E := z.extract (z.size - n) z.size

/-- After AttentionTables.lean:125. -/
def lastN (z : Array E) (n : Nat) : Array E := eqTab (lastCoords z n)

/-- Token weights from tile weights. After AttentionTables.lean:132-134. -/
def tok (g : Geo) (hi lo : Array E) : Array E :=
  let el := eqTab lo
  (Array.range g.T).map fun i => mulE (hi.getD (i / g.B) zeroE) (el.getD (i % g.B) zeroE)

/-- The tile rows' and the tile columns' weights of a softmax-table unit at its sumcheck's point. After AttentionTables.lean:151-159. -/
def scoreTiles (g : Geo) (k : ScoreP) : Array E × Array E :=
  let r := k.sc.r
  if k.below then
    tileSums g (eqTab (r.extract g.lgk (g.lgk + g.lnT - 1))) (eqTab (r.extract (g.lgk + g.lnT - 1) (g.lgk + 2 * g.lnT - 1)))
  else
    let e := eqTab (r.extract g.lgk (g.lgk + g.lnT))
    (e, e)

/-- After AttentionTables.lean:167-168. -/
def pointM (g : Geo) (d : DivP) : Array E :=
  d.vpm.r.extract 0 (g.lgk + 2 * g.lnT - 1) ++ d.zilo g ++ lastCoords d.vpm.r g.lB

/-- After AttentionTables.lean:173-174. -/
def pointD (g : Geo) (d : DivP) : Array E :=
  d.vpd.r.extract 0 (g.lgk + g.lnT) ++ d.zilo g ++ lastCoords d.vpd.r g.lB

/-- After AttentionTables.lean:177-178. -/
def mergedPlanes (n : Nat) (zx : Array E) (planes : Array RemP) : Bool :=
  planes.all fun pc => lastCoords pc.z n == lastCoords zx n

/-- After AttentionTables.lean:182-184. -/
def mergedTokens (g : Geo) (zx : Array E) (d : DivP) : Bool :=
  let w := d.ziW ++ d.zcW
  w == d.ziH ++ d.zcH && w == lastCoords zx (g.lt + g.ldh)

/-- After OnBytes/Model/AttentionTables.lean:62-65. -/
def T.getAs {α : Type} (_name : String) (x : Option α) : T α :=
  match x with
  | some a => pure a
  | none => failure

/-- After OnBytes/Model/AttentionTables.lean:70-71. -/
def T.weights (_len : Nat) (f : Unit → Array E) : T (Array E) :=
  pure (f ())

/-- After OnBytes/Model/AttentionTables.lean:74-74. -/
def T.placed : T Placed := fun t => pure (t, t)

/-- After OnBytes/Model/AttentionTables.lean:87-92. -/
def add (mats : Array (Nat × Nat)) (mat len : Nat) (phi : Array E) (elems : Nat) : T Nat :=
  fun t => do
    mustAs "internal-a-table-length" (fits mats mat len elems)
    let table : Fun1 := { mat := mat, len := len, phi := phi, tree := 2, start := t.next }
    pure (t.next, { next := t.next + elems, tabLen := (t.next, elems) :: t.tabLen,
                    funs := t.funs.push table })

/-- After OnBytes/Model/AttentionTables.lean:97-98. -/
def T.total (start : Nat) : T Unit := fun t =>
  pure ((), { t with tabLen := (start, t.next - start) :: t.tabLen })

/-- After OnBytes/Model/AttentionTables.lean:104-110. -/
def addAs (g : Geo) (mats : Array (Nat × Nat)) (phi : Unit → Array E) : T Nat := do
  let phi ← T.weights (2 ^ g.lmS) phi
  let start := (← T.placed).next
  (List.range g.NAs).forM fun q =>
    discard (add mats q (2 ^ g.lmS) phi (g.kAs / g.NAs))
  T.total start
  pure start

/-- After OnBytes/Model/AttentionTables.lean:141-145. -/
def lng (g : Geo) (zc : Array E) (ptk : Unit → Array E) : T (Array E) := do
  let tokens ← T.weights g.T ptk
  mustAs "plan-tensor-layout" (tokens.size == g.T && 2 ^ g.la == 2 ^ g.ls * g.T)
  let c ← T.getAs "plan-tensor-layout" (cutLast zc g.ls)
  T.weights (2 ^ g.la) fun _ => blockRows (eqTab c.2) tokens

/-- After OnBytes/Model/AttentionTables.lean:205-206. -/
def addRow (g : Geo) (mats : Array (Nat × Nat)) (psi : Unit → Array E) : T Nat := do
  add mats g.NAs g.T (← T.weights g.T psi) g.fillH

/-- After OnBytes/Model/AttentionTables.lean:210-213. -/
def addLong (g : Geo) (mats : Array (Nat × Nat)) (mat : Nat) (zc : Array E)
    (ptk : Unit → Array E) (elems : Nat) : T Nat := do
  let phi ← lng g zc ptk
  add mats mat (2 ^ g.la) phi elems

/-- After OnBytes/Model/AttentionTables.lean:218-272. -/
def placeAll (g : Geo) (mats : Array (Nat × Nat)) (nW : Nat) (lk : LookIn) (p : Pts) :
    T TablesP := do
  let (planes, scores, d, x) := (p.planes, p.scores, p.d, p.x)
  let gSo := g.fillO * g.T / 2 ^ g.la
  let gSq := g.fillQ * g.T / 2 ^ g.la
  let mb := 2 ^ g.lmb
  let iAO := g.NAs + 1
  let iBA := g.NAs + 2
  let iQA := g.NAs + 3
  let ptM := pointM g d
  let ptD := pointD g d
  let riE := d.scE.r.extract g.lgk (g.lgk + g.lt)
  mustAs "internal-a-merged-point" (mergedPlanes g.lmS lk.zx planes)
  let tA ← addAs g mats fun _ => lastN lk.zx g.lmS
  let tVM ← addAs g mats fun _ => lastN ptM g.lmS
  let tVD ← addAs g mats fun _ => lastN ptD g.lmS
  let tM ← scores.mapM fun k => addRow g mats fun _ => tok g k.wI k.zi
  let hW ← addRow g mats fun _ => eqTab d.ziW
  let hX ← addRow g mats fun _ => eqTab d.ziX
  let hE ← addRow g mats fun _ => eqTab riE
  let hT ← addRow g mats fun _ => eqTab x.ti
  let hPi ← addRow g mats fun _ => eqTab (x.pi g)
  let hR2 ← addRow g mats fun _ => eqTab (x.ri2 g)
  mustAs "internal-a-merged-point" (mergedTokens g lk.zx d)
  let tO ← addLong g mats iAO d.zcW (fun _ => eqTab d.ziW) gSo
  let tQK ← scores.mapM fun k => do
    let rcK := lastCoords k.sc.r g.ldh
    let tQ ← addLong g mats iQA rcK (fun _ => tok g (scoreTiles g k).1 k.zi) gSq
    let tK ← addLong g mats iQA rcK (fun _ => tok g (scoreTiles g k).2 k.zj) gSq
    pure (tQ, tK)
  let qO ← addLong g mats iQA d.zcW (fun _ => eqTab riE) gSq
  let qVM ← addLong g mats iQA d.zcW (fun _ => tok g d.wJv (lastCoords d.vpm.r g.lB)) gSq
  let qVD ← addLong g mats iQA d.zcW
    (fun _ => tok g (eqTab (d.vpd.r.extract g.lgk (g.lgk + g.lnT)))
      (lastCoords d.vpd.r g.lB)) gSq
  let qF ← addLong g mats iQA (x.rc g) (fun _ => eqTab (x.ri g)) gSq
  let qKx ← addLong g mats iQA (x.rc g) (fun _ => eqTab (x.pj g)) gSq
  mustAs "forest-planes" lk.planesOk
  let phiB0 ← T.weights mb fun _ => lk.phiB0
  let tBit0 ← add mats iBA mb phiB0 g.kbA
  let phiB1 ← T.weights mb fun _ => lk.phiB1
  let tBit1 ← add mats iBA mb phiB1 g.kbA
  let tPin ← add mats iBA mb (← T.weights mb fun _ => lk.phiP) g.kbA
  let t ← T.placed
  mustAs "internal-af-W-length" (t.next == nW)
  let score : Array ScoreT := (tM.zip tQK).map fun y => ⟨y.1, y.2.1, y.2.2⟩
  pure {
    ptM := ptM, ptD := ptD, tA := tA, tVM := tVM, tVD := tVD, score := score,
    hW := hW, hX := hX, hE := hE, hT := hT, hPi := hPi, hR2 := hR2, tO := tO,
    qO := qO, qVM := qVM, qVD := qVD, qF := qF, qKx := qKx,
    tBit0 := tBit0, tBit1 := tBit1, tPin := tPin,
    tabLen := t.tabLen, funs := t.funs }

/-- After OnBytes/Model/AttentionTables.lean:277-280. -/
def tablesP (g : Geo) (mats : Array (Nat × Nat)) (nW : Nat) (lk : LookIn) (p : Pts) :
    Option TablesP := do
  pure (← placeAll g mats nW lk p {}).1


end VerifiableInference.Desc.First.Att.P
