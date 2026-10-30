-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/DeriveLin.lean: the sizes of the test on the committed table, and the plans of the
shared chain and the second chain.

The test on the table (OnBytes/Iop/Lin.lean) runs in a batch of requests and, once, as the
committer's own test in a key file. Its oracle messages: the folded row, which is the table's rows
folded at a drawn point; Omega, the committed matrix times the equality vector of the point that a
batch shares; W, a request's own public vector times the committed matrix. It has three groups of
rows: the folded row's, Omega's and a request's own. A list is the positions that one round draws.
Omega is read at the list of the batch's test on it and at the list of every request's own test. If
the folded row and Omega differ in code (a split), a message of masks is read at the lists of both
their groups; if not, the two are one group. So the groups' positions and random entries depend on
each other, and they are solved together, by iteration upward from 0. The file renders
blocks/frame/lin_frame.h and the routine add_table_chains of blocks/frame/files.h.

Two numbers come from the model's shapes and are arguments here: the rows of the committed matrix
and the mask rows of the message that masks a request's claims.

Main definitions: `LinLines`, `linLines`, `LinSized`, `linSized`, `linSizeOf`, `linPlanShared`,
`linPlanSecond`, `sharedPlan`, `secondPlan`.
What is not claimed: no theorem is stated here. The tests that the finished shape fits itself and
the codes (lin_fault, iopp_fault) are not asked in this file. They are asked in
OnBytes/Params/Configure.lean. Nor do the plans compare the solved stages, from which they price a
proximity test, with the shape's stages under the chain's codes. The C++ ends the process if they
differ (lin_require_sized). Here `linSized` makes both from the same values.
-/
import OnBytes.Iop.Lin
import OnBytes.Params.Derive

namespace OnBytes.Params

/-- What is free in the test on the table: fixed by a line of the parameter file or by the model's
shapes, not derived. The C++ record has four more fields, which no line sets: rows_high,
masks_ahead, masks_ride and columns_elsewhere. `linSized` has their C++ defaults built in: true,
true, true and 0. -/
structure LinLines where
  /-- a row of the table holds 2 ^ kLo columns of the matrix -/
  kLo : Nat
  matrixRows : Nat
  folded : GroupLine
  omega : GroupLine
  own : GroupLine
  /-- the most requests in a batch -/
  requests : Nat
  /-- the mask rows of the oracle message whose entries mask a request's claim -/
  inputMaskRows : Nat
  /-- the committer's own test: a batch of one, at the one-time radius -/
  oneTime : Bool

/-- From the parameter file's lines. `oneTime`: the committer's own test, under the lines whose
names begin with "once-". -/
def linLines (l : Lines) (matrixRows inputMaskRows : Nat) (oneTime : Bool) : LinLines where
  kLo := l.blockLog - l.tableRowsLog
  matrixRows := matrixRows
  folded := if oneTime then l.onceFolded else l.folded
  omega := if oneTime then l.onceOmega else l.omega
  own := if oneTime then l.onceOwn else l.own
  requests := if oneTime then 1 else l.slots
  inputMaskRows := inputMaskRows
  oneTime := oneTime

/-- What follows from the lines for the test on the table. -/
structure LinSized where
  lines : LinLines
  shape : LinShape
  /-- the request's mask message, as the test's group expects it -/
  input : OracleNotice
  table : TableSize
  folded : TestSizes
  /-- read only if the folded row and Omega differ in code -/
  omega : TestSizes
  own : TestSizes
  /-- the batches, counted when begun, that a stored copy of the table covers: a row's random
  entries, less the columns of one one-time test, divided by the columns of a batch. Columns that
  links to other copies open are not subtracted -/
  batches : Nat

/-- The row variables of a group with these members: k for the main rows, h for the mask rows. -/
def linGroupBits (members : List OracleShape) : Nat × Nat :=
  let up := fun (r : Nat) => if r != 0 then pow2AtLeast r else 0
  let h := clog2 (sumT (members.map fun m => up m.maskRows))
  (max (max (clog2 (sumT (members.map fun m => up m.mainRows))) h) 1, h)

/-- A group as it was sized last: the group, its positions so far, and whether its rounds hold. -/
structure Sizing where
  group : GroupSize := {}
  t : Nat := 0
  serves : Bool := false

/-- Sizes one group at given numbers of draws. The positions only grow. During the iteration a group
need not be admissible yet: with too few random entries its main code can have a lower rate than its
mask code. The main code by itself then gives a number of positions that is not too large, and the
iteration goes on. `linSized` tests `serves` after the last turn. -/
def sizeOne (s : Setting) (shape : GroupSize) (line : GroupLine) (scope : Scope)
    (mainDraws maskDraws rows : Nat) (before : Sizing) : Option Sizing :=
  let g : GroupSize :=
    { shape with main := { shape.main with r := tailFor mainDraws },
                 mask := { shape.mask with r := tailFor maskDraws } }
  if g.main.n < g.main.dim || g.mask.n < g.mask.dim then none
  else
    let load : GroupLoad := { cubeBits := stageCubeBits g, messages := 2, batchedRows := rows }
    let sized := sizeGroup s scope g load
    let serves := groupHolds s scope sized load
    let more :=
      if !serves then positionsFromBelow s scope g load (margin s)
      else scopePositions s scope (analysis s sized).mainAt.agree (margin s)
    if more == 0 then none else some ⟨sized, max before.t more, serves⟩

/-- The shapes of the three groups and what the turns of the iteration read. `split`: the folded row
and Omega differ in code, so each has a group of its own. -/
structure LinGroups where
  split : Bool
  shared : Scope
  request : Scope
  foldedShape : GroupSize
  omegaShape : GroupSize
  ownShape : GroupSize
  /-- the rows that are batched on the folded row's group -/
  foldedRows : Nat

/-- The turns of the iteration over all three groups together. x, y, z: the folded row's group,
Omega's and a request's own, as sized last. Omega's rows are opened at the list of the batch's test
on them and at the own list of each of the `requests` requests. The iteration ends when no number
of positions has grown; none if the fuel runs out first. -/
def linTurns (s : Setting) (L : LinLines) (G : LinGroups) :
    Nat → Sizing → Sizing → Sizing → Option (Sizing × Sizing × Sizing)
  | 0, _, _, _ => none
  | fuel + 1, x, y, z => do
    let a := x.t
    let b := y.t
    let c := z.t
    let omegaDraws := (if G.split then b else a) + L.requests * c
    let x' ← sizeOne s G.foldedShape L.folded G.shared (if G.split then a else omegaDraws)
      (if G.split then a + b else a) G.foldedRows x
    let y' ← if G.split then
        sizeOne s G.omegaShape L.omega G.shared omegaDraws (a + b) (1 + 2 * s.samples) y
      else pure y
    let z' ← sizeOne s G.ownShape L.own G.request omegaDraws c (2 + 3 * s.samples) z
    if x'.t == a && y'.t == b && z'.t == c then pure (x', y', z')
    else linTurns s L G fuel x' y' z'

/-- A shape as the reader of a chain's parameter bytes returns it: the word for "no code" where it
has no rows of a kind, and the degree 1 where it has no main rows. -/
def canonical (o : OracleShape) : OracleShape :=
  { o with code := if o.mainRows == 0 then noId else o.code,
           mainDeg := if o.mainRows == 0 then 1 else o.mainDeg,
           maskCode := if o.maskRows == 0 then noId else o.maskCode }

/-- Sizes the test on the table, in this order: the shapes of the oracle messages and groups, which
follow from the message lengths; then positions and random entries, all groups together; then codes
and stages. W's columns may fill its rows to the last place; then the pad of its sample is in a mask
row. `codes` is the list of the codes of the file's chains, to which the test's codes are added. -/
def linSized (s : Setting) (L : LinLines) (T : TableSize) (codes : Codes) :
    Option (LinSized × Codes) := do
  let scopeShared : Scope := if L.oneTime then .once else .shared
  let scopeOwn : Scope := if L.oneTime then .once else .request
  let split := L.folded.logN != L.omega.logN || L.folded.logL != L.omega.logL
  if L.own.logN != L.omega.logN || L.own.logL != L.omega.logL then none
  if split && (L.folded.maskLogN != L.omega.maskLogN || L.folded.maskLogL != L.omega.maskLogL) then
    none
  if T.code.n < T.code.dim then none
  let A := tableAnalysis s T
  if !tableAdmitted T A then none
  let agree := if L.oneTime then A.once.agree else A.later.agree
  let columns := scopePositions s scopeShared agree
  if columns == 0 then none
  let I := indexShapeOf s T
  if 40 < I.v || I.code.ell ≤ 3 * I.answers then none
  let spent := scopePositions s .once A.once.agree
  let batches := if spent < I.code.r then (I.code.r - spent) / columns else 0
  let ellU := 2 ^ L.folded.logL
  let ellO := 2 ^ L.omega.logL
  let matrixColumns := 2 ^ (L.kLo + I.v)
  let message := fun (mainRows maskRows : Nat) =>
    ({ mainRows := mainRows, mainDeg := 3, maskRows := maskRows, answers := s.samples }
      : OracleShape)
  let u := message (linRowsOf (foldedEntries I + s.samples) ellU true) 0
  let omega := message (linRowsOf (L.matrixRows + s.samples) ellO true) 0
  let wRows := linRowsOf matrixColumns ellO true
  let w := message wRows (if wRows * ellO - matrixColumns < s.samples then 1 else 0)
  let sharedSplit := message 0 1
  let input := message 0 L.inputMaskRows
  let withBits := fun (line : GroupLine) (b : Nat × Nat) => { shapeOf line b.1 true with h := b.2 }
  let G : LinGroups :=
    { split, shared := scopeShared, request := scopeOwn
      foldedShape :=
        withBits L.folded (linGroupBits (if split then [u, sharedSplit] else [u, omega]))
      omegaShape := withBits L.omega (linGroupBits [omega, sharedSplit])
      ownShape := withBits L.own (linGroupBits [input, w, omega])
      foldedRows := I.answers + columns + 1 + 2 * s.samples }
  let (x, y, z) ← linTurns s L G 33 {} {} {}
  if !x.serves || (split && !y.serves) || !z.serves then none
  let stU ← solveStages s scopeShared x.group x.t L.folded.stages
  let stO ← if split then
      solveStages s scopeShared y.group y.t L.omega.stages
    else pure []
  let stW ← solveStages s scopeOwn z.group z.t L.own.stages
  let (testU, codes1) := ioppStages stU codes
  let (testOmega, codes2) := ioppStages stO codes1
  let (testOwn, codes3) := ioppStages stW codes2
  match testU, testOwn with
  | gu :: _, gw :: _ =>
    let S : LinShape :=
      { fold := { index := I, u := canonical { u with code := gu.code }, rowsHigh := true,
                  leafClass := 0, columns := columns }
        kLo := L.kLo
        matrixRows := L.matrixRows
        omega := canonical { omega with code := gw.code }
        w := canonical { w with code := gw.code, maskCode := gw.maskCode }
        omegaRowsHigh := true
        wRowsHigh := true
        sharedSplit := canonical { sharedSplit with maskCode := gu.maskCode }
        ownSplit := canonical {}
        omegaLeafClass := 1
        sharedSplitLeafClass := 2
        wLeafClass := 0
        ownSplitLeafClass := 3
        sharedMaskCode := gu.maskCode
        ownMaskCode := gw.maskCode
        masksAhead := true
        testU := testU
        testOmega := testOmega
        testOwn := testOwn
        testOwnOmega := []
        choice := ⟨true⟩ }
    pure (⟨L, S, ⟨canonical { input with maskCode := gw.maskCode }, 0⟩, T, ⟨x.group, x.t, stU⟩,
      ⟨y.group, y.t, stO⟩, ⟨z.group, z.t, stW⟩, batches⟩, codes3)
  | _, _ => none

/-- The variables of the cube of a sample on an oracle message, as the block that sends it has
them. -/
def cubeBitsOf (codes : Codes) (o : OracleShape) : Nat := (Send.cube codes o).bits

/-- The number of trees of one prover's message, which is the number of its roots, by the one rule
that assigns oracle messages to trees (`layTrees`). None if that rule refuses them. -/
def treesOf (codes : Codes) (sent : Array OracleNotice) : Option Nat :=
  (layTrees codes sent).map (·.shapes.size)

/-- What the prover's message with the folded row holds. -/
def linMessageU (S : LinShape) : Option (Array OracleNotice) :=
  (linWithU S).map (#[⟨S.fold.u, S.fold.leafClass⟩] ++ ·)

/-- The first stage's group of a test; the field `group` if the test has no stages. The plans take a
sample's lists from here, the value from which they also price the test's rounds. -/
def TestSizes.first (t : TestSizes) : GroupSize := (t.stages.headD ⟨t.group, t.t, 0⟩).g

/-- The sizes that the plans of the test's rounds read. -/
def linSizeOf (codes : Codes) (x : LinSized) : Option LinSize := do
  let S := x.shape
  let aroundOmega := if S.sharedSplitNeeded then x.omega.first else x.folded.first
  let rootsW ← treesOf codes (← linMessageW S)
  let rootsU ← treesOf codes (← linMessageU S)
  let rootsOmega ← treesOf codes (linMessageOmega S)
  pure { w := ⟨cubeBitsOf codes S.w, [x.own.first]⟩
         u := ⟨cubeBitsOf codes S.fold.u, [x.folded.first]⟩
         omega := ⟨cubeBitsOf codes S.omega, [aroundOmega, x.own.first]⟩
         instances := x.lines.requests
         oneTime := x.lines.oneTime
         kLo := S.kLo
         rowsLog := S.kRow
         besideOmega :=
           if S.sharedSplitNeeded then
             [⟨cubeBitsOf codes S.sharedSplit, [x.folded.first, x.omega.first]⟩]
           else []
         rootsW := rootsW
         rootsU := rootsU
         rootsOmega := rootsOmega }

/-- On a request's first chain, before its seal: W and its sample. -/
def linPlanFirst (codes : Codes) (x : LinSized) : Planning Unit := do
  planLinFirst (← must (linSizeOf codes x))

/-- On the shared chain, from its first round to before its seal. -/
def linPlanShared (codes : Codes) (x : LinSized) : Planning Unit := do
  let s ← theSetting
  let S := x.shape
  let nu ← planLinShared x.table (← must (linSizeOf codes x))
  needs (nu == S.fold.columns)
  let rows := S.fold.index.answers + nu + 1 + 2 * s.samples
  let ahead := if S.masksAhead then 0 else 1
  if S.sharedSplitNeeded then
    planSplit
    planIopp x.folded.stages rows ahead S.choice.masksRide
    planIopp x.omega.stages (1 + 2 * s.samples) 1 S.choice.masksRide
  else planIopp x.folded.stages rows ahead S.choice.masksRide

/-- On a request's second chain: the request's own test. -/
def linPlanSecond (x : LinSized) : Planning Unit := do
  let s ← theSetting
  planIopp x.own.stages (2 + 3 * s.samples) (if x.shape.masksAhead then 0 else 1)
    x.shape.choice.masksRide

/-- The plan of a shared chain. -/
def sharedPlan (s : Setting) (codes : Codes) (x : LinSized) : Except String Planned :=
  finishHeld s (if x.lines.oneTime then .once else .shared) do
    linPlanShared codes x
    planSeal

/-- The plan of a second chain. -/
def secondPlan (s : Setting) (x : LinSized) : Except String Planned :=
  finishHeld s (if x.lines.oneTime then .once else .request) (linPlanSecond x)

/-- The parameter bytes of a shared chain. Only tests call this, and `proofParams`
(OnBytes/Params/DeriveReq.lean), which nothing calls: the program forms them in `configure`
(OnBytes/Params/Configure.lean). `codes` is the whole list of the file's chains. -/
def sharedParams (s : Setting) (codes : Codes) (x : LinSized) (cfg : ByteArray) :
    Except String ByteArray := do
  let p ← sharedPlan s codes x
  pure (Fmt.paramsBytes p.plan cfg
    [("codes", spellCodes codes), ("the test on the table", spellLin x.shape)])

/-- The parameter bytes of a second chain. It has the callers of `sharedParams`. -/
def secondParams (s : Setting) (x : LinSized) (cfg : ByteArray) : Except String ByteArray := do
  let p ← secondPlan s x
  pure (Fmt.paramsBytes p.plan cfg [])

end OnBytes.Params
