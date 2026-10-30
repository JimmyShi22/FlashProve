-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/Equations.lean: the smallness test's equations AS A LIST: a plain
function from the link's part of the carried record to a list of claims (`Claim`,
Johnson/Desc/Claim.lean), each with its place among the powers of the batching element. Nothing is
added to the ledger here: whoever batches adds the list (`addAll`, also in Claim.lean).

In this order: KEYS, one equation on the array of digits; COUNTS, three on the bits of the lookup's
counts; a TIE for each matrix; the READS, matrix by matrix, in the list's order, by rising stretch.
THE DIGITS' LOOKUP's OWN EQUATIONS ARE NOT IN THIS LIST: the rows that its sumchecks left
(`Forest.objects`, OnBytes/Model/Look.lean:425-427; called at OnBytes/Model/Tail.lean:1050) are laid
by the lookup's own block,
which also pays the first of the lookup's three owed marks. Their place: right before this list.
An equation of the first two sorts has the power of its own number in the link's list
(`eqFirst := none`): so the number in front (`front`) counts the lookup's own equations too. A tie
has n + f(mu), a read n + f(N) + tau' q (`eqFirst := some ..`): n: the length of the link's list by
the plan; the inner powers (tau' i' + u) are weights of the runs.

Main names:
  `EqM`: a routine on the sub-proof's state and the list so far, which may refuse under a name.
  `eqKeys`, `eqCounts`, `eqTie`, `eqRead`, `eqWeights`, `eqAll`: the text.
  `lookRows`: how many equations of its own the digits' lookup has: for the count behind them.
  `equations`: the border: the number of claims in front, the record, the list of tables, the
    sub-proof's state: the record behind, the state behind, the list; or a refusal's name.
MADE BY PROGRAM from a file that is not in this repository, which is `verify-on-bytes`'s text token
for token: ten places turned: at seven a claim that was added is laid on the list; at two the factor
theta^(n - number + first), which was taken off the ledger, is 1, and `first` goes into the claim;
the last line's reading of the ledger (lsTail) is struck. The number of claims so far is no reading
of the ledger: it is `front`, which the gatherer hands in, plus the list's length.
THEN BY HAND: the first of the seven (`eqLook`: the lookup's own equations and their owed mark) is
struck with its call in `eqAll`; the count behind it (Tail.lean:1053) is asked of the heard rows.
THAT COUNT HAS TWO HALVES NOW. Asked here: the heard record holds `lookRows` rows: the program's own
test by value, since `Forest.objects` adds one claim for each row. NOT ASKED ANYWHERE YET, a named
debt of whoever gathers the lookup's block's list and this one: that list's length is `lookRows tl`.
(Where this and lean/THEOREM.md differ, the page
holds.)
It cannot be seen from here. Unasked, a list one row short was refused two steps later, without a
name (a run on a stand-in for that block's run).
What the state still bears here, and no claim: the leaves' sumcheck's masking values are laid
(`eqPscRow`: a stand-in, as in Objects.lean); two owed marks are paid (the planes', the keys').
TWO THINGS THAT WANT THE LEDGER AND ARE THE BATCHING's, NOT THIS LIST's: "no earlier equation has
laid a weight on a masking value of this block" (Tail.lean:1046-1047) is asked here of the ledger AS
IT IS HANDED IN: right where the link's earlier equations have been added already, idle where all
claims are gathered first; and lsTail (Tail.lean:1094) can be read only behind the adding.
A DEMAND ON THE DRIVER, which this text cannot see kept: the ledger handed in does not yet bear the
lookup's own equations: the two lists are gathered first and then added, the lookup's in front. The
lookup's masking values lie inside this block's window (Tail.lean:720-725) and its rows read them
(Look.lean:423-427): with the rows added first, that test refused the honest proof (the same run).
Limits: definitions alone; no law. Nothing on soundness.

-/
import Johnson.Desc.Claim
import Johnson.Desc.First.TailClaims.ForkM
import OnBytes.Model.Tail

set_option autoImplicit false

namespace VerifiableInference.Desc.First.TailClaims

open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc

/-- A routine on the sub-proof's state and the list of claims so far; it may refuse under a name. It
is handed the number of claims that stand in front of this list: the gatherer's count. -/
abbrev EqM (α : Type) : Type := ReaderT Nat (StateT (Fork × Array Claim) (Except String)) α

namespace EqM

/-- A routine on the state alone. -/
def liftF {α : Type} (x : ForkM α) : EqM α := fun _ s =>
  match x s.1 with
  | .ok (a, F) => .ok (a, (F, s.2))
  | .error e => .error e

/-- Lays a claim on the list. -/
def emit (c : Claim) : EqM Unit := fun _ s => .ok ((), (s.1, s.2.push c))

/-- The number of claims so far: those in front of this list, and the list's. -/
def claims : EqM Nat := fun front s => .ok (front + s.2.size, s)

def mustAs (name : String) (b : Bool) : EqM Unit := liftF (ForkM.mustAs name b)
def testAs (name : String) (b : Bool) : EqM Unit := liftF (ForkM.testAs name b)
def get {α : Type} (name : String) (x : Option α) : EqM α := liftF (ForkM.get name x)
def ask {α : Type} (name : String) (f : Fork → Option α) : EqM α := liftF (ForkM.ask name f)
def change (name : String) (f : Fork → Option Fork) : EqM Unit := liftF (ForkM.change name f)
def paid (i : Nat) : EqM Unit := liftF (ForkM.paid i)

end EqM

/-! ## Stand-ins for two other files' plain forms -/

/-- `Forest.planesAdded` (Look.lean:431). -/
def eqPlanesAdded (g : Forest.Heard) : EqM Unit := EqM.paid g.owedPlanes

/-- `Forest.joinAdded` (Look.lean:435). -/
def eqJoinAdded (g : Forest.Heard) : EqM Unit := EqM.paid g.owedJoin

/-- `Forest.paddingLaid` (Look.lean:449-450). -/
def eqPaddingLaid (g : Forest.Heard) (laid : Array Nat) : EqM Unit :=
  EqM.mustAs "internal-forest-padding-places" (laid == g.shape.pub)

/-- `pscRow` (Psc.lean:197-200). -/
def eqPscRow (p : Psc) (S0 : E) (kept : Aff := {}) : EqM (Aff × Psc) := do
  EqM.mustAs "pscRow:198" (!p.rowMade && p.started && !p.vars.isEmpty && p.r.size == p.vars.size)
  EqM.change "pscRow:199"
    (·.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE))
  pure (p.rowForm S0 kept, { p with rowMade := true })

/-! ## The claims -/

/-- The claim on the lookup's key vectors, as one claim with runs on ZZ: the program's
`HTailF2.linJoin9` (OnBytes/Model/Tail.lean:828-869), with the places turned that
the head names. -/
def eqKeys (tl : HTailF2) : EqM HTailF2 := do
  let g ← EqM.get "linJoin9:829" tl.heard
  let h := tl.f9
  EqM.mustAs "internal-f-padding-key"
    ([0, 1].all fun q => let c := (tl.zOf q).call; c.tauAt c.t0 == 0)
  let mut constant := zeroE
  let mut runs : Array Run2 := #[]
  let mut read := Forest.noPub h
  -- A piece's column weights are eqTab of its point zc. Pieces with equal points share them.
  let mut point : Array E := #[]
  let mut table : Array E := #[oneE]
  for q in [0, 1] do
    let c := tl.zOf q
    let zk := g.zk.getD q #[]
    let n := c.call.n
    constant := addE constant (mulE (g.e.getD q zeroE) (subE g.alpha (scaleNat g.theta q)))
    for p in c.pieces do
      EqM.mustAs "internal-eq-index"
        (decide (p.b ≤ n) && eqIndexOK (zk.extract 0 (n - p.b)) (p.off / 2 ^ p.b))
      let zc := zk.extract (n - p.b + p.a) (n - p.b + p.a + clog2 p.CP)
      if zc != point then
        point := zc
        table := eqTab zc
      runs := runs.push
        { tree := p.tree, row := p.row, first := p.c0,
          coef := subE zeroE
            (mulE (g.e.getD q zeroE) (eqOne (zk.extract 0 (n - p.b)) (p.off / 2 ^ p.b))),
          w := table, n := p.Cp }
      -- The places that this run reads, counted by tree. All other places count as padding.
      for rr in List.range p.Rp do
        let i := h.iota.getD q 0
        -- C++ refuses here under: internal-f-join-place
        read ← EqM.get "linJoin9:859"
          (placesRead h.dT i (h.first.getD q 0) (2 ^ i + 1) read (p.off + rr * p.CP) p.Cp)
  let ey := eqTab g.zy
  for y in List.range (2 ^ h.rK - h.NT) do
    constant := addE constant (mulE (ey.getD (h.NT + y) zeroE) (subE g.alpha (g.padKey 0)))
  EqM.mustAs "internal-f-join-place" (read.all fun x => decide (x ≤ 2 ^ h.dT))
  eqPaddingLaid g (read.map fun x => 2 ^ h.dT - x)
  let number ← EqM.claims
  EqM.emit { form := Aff.ofConst constant - g.cEnd, runs := runs }
  eqJoinAdded g
  pure { tl with joinObj9 := some number }

/-- The three claims that read the planes of the lookup's counts, on BZ: the program's
`HTailF2.linBits9` (Tail.lean:882-897), with the places turned that
the head names. -/
def eqCounts (tl : HTailF2) : EqM HTailF2 := do
  let g ← EqM.get "linBits9:883" tl.heard
  let h := tl.f9
  let KB := tl.bzColumns
  let runOn (row : Nat) (coef : E) (w : Array E) : Run2 :=
    { tree := tl.ix.BZ, row := row, first := 0, coef := coef, w := w, n := KB }
  let w0 := eqTab (g.zb0.extract 5 (5 + h.kT + h.cK))
  let w1 := eqTab (g.zb1.extract 5 (5 + h.kT + h.cK))
  let bitFactor := mulE g.leaves.eps g.leavesA
  let (leavesRow, _) ← eqPscRow g.leaves oneE
  EqM.emit { form := leavesRow, runs := #[runOn 0 bitFactor w0] }
  EqM.emit { form := Aff.slot g.sBit, runs := #[runOn 1 (subE zeroE oneE) w1] }
  let w := (Array.range KB).map fun u => ofNat (2 ^ (u % 32))
  EqM.emit
    { form := Aff.ofConst (subE zeroE (ofNat (2 ^ h.v - h.padding))), runs := #[runOn 2 oneE w] }
  eqPlanesAdded g
  pure { tl with bitFactor9 := bitFactor }

/-- The tie of matrix mu: the program's `HTailF2.linTie` (Tail.lean:936-949), with the places turned
that the head names. -/
def eqTie (tl : HTailF2) (mu : Nat) : EqM Unit := do
  let s := tl.shp.getD mu {}
  -- C++ refuses here under: internal-sym-point, internal-f-draws, internal-f-zzcol
  let wl ← EqM.get "linTie:939" (tieLeft s (tl.rowX.getD mu #[]) (tl.loX.getD mu #[]))
  let wr ← EqM.get "linTie:940" (tieRight s (tl.loX.getD mu #[]) (tl.gamX.getD mu #[]))
  -- the factor that lifts the claim to theta^(n + first) is laid by whoever adds the claim
  let lead := oneE
  let c0 ← EqM.get "linTie:942" (tl.zzCol mu 0 0)
  let c1 ← EqM.get "linTie:943" (tl.zzCol mu 1 0)
  let ZZ := tl.ix.ZZ
  EqM.emit
    { eqFirst := some (tl.eqFirst.getD mu 0)
      form := lessBeta (mulE lead (mulE (sumE tl.vp) (sumE wl)))
      runs :=
        #[{ tree := ZZ, row := tl.zzRowTies, first := c0, coef := lead, w := wl, n := s.m },
          { tree := ZZ, row := tl.zzRowTies, first := c1, coef := highDigit lead, w := wl,
            n := s.m },
          { tree := tl.gtTree.getD mu 0, row := 0, first := 0, coef := subE zeroE lead, w := wr,
            n := s.J * s.k }] }

/-- The read of segment sg of the table Fn: the program's `HTailF2.linRead` (Tail.lean:977-999),
with the places turned that the head names. -/
def eqRead (tl : HTailF2) (Fn : HFun) (sg laid : Nat) (sums : E) : EqM Unit := do
  let mu := Fn.mat
  -- C++ refuses here under: internal-t2f-unit, internal-f-draws, internal-f-table-index,
  -- internal-f-zzcol
  let tU ← EqM.get "linRead:981" (tl.ix.U.getD Fn.tree none)
  let lead := oneE
  let cols ← EqM.ask "linRead:983" fun F => some (((F.trees[tU]?).map (·.K)).getD 0)
  let k := (tl.mats.getD mu {}).k
  -- The entries' indices rise with the column, so the last column's row is the largest.
  EqM.mustAs "internal-L-row" (cols != 0 &&
    ((tl.tabAt Fn (k - 1) sg).all fun last => decide (last / cols < 2 ^ 32)))
  let (ents, noneIsZero) ← EqM.get "linRead:988"
    (tl.readEnts Fn sg tU cols (subE zeroE lead) (tl.gamV.getD mu #[]) k 0
      (Array.emptyWithCapacity k) true)
  EqM.testAs "internal-f-table-read" noneIsZero
  let f := { lessBeta (mulE lead sums) with ents := ents }
  let c0 ← EqM.get "linRead:993" (tl.zzCol mu 0 (sg * Fn.len))
  let c1 ← EqM.get "linRead:994" (tl.zzCol mu 1 (sg * Fn.len))
  let ZZ := tl.ix.ZZ
  EqM.emit
    { eqFirst := some (tl.eqFirst.getD tl.NM 0 + laid * tl.stepF)
      form := f
      runs :=
        #[{ tree := ZZ, row := tl.zzRowReads, first := c0, coef := lead, w := Fn.phi, n := Fn.len },
          { tree := ZZ, row := tl.zzRowReads, first := c1, coef := highDigit lead, w := Fn.phi,
            n := Fn.len }] }

/-- The batching element's powers and the sums over the drawn matrix's columns: the program's
`HTailF2.weightsF` (Tail.lean:1029-1032). -/
def eqWeights (tl : HTailF2) : EqM HTailF2 := do
  let tl ← EqM.ask "weightsF:1030" fun F => tl.powersF F
  EqM.get "weightsF:1031" ((List.range tl.NM).foldlM (fun (x : HTailF2) mu => x.foldSums mu)
    { tl with gamX := Array.replicate tl.NM #[], gamV := Array.replicate tl.NM #[] })

/-- How many claims of its own the digits' lookup has: `Forest.lins`, written out a second time as a
check (Tail.lean:1051-1053): 31 claims of the lookup's tie, one for each level of the key side (v)
and of the table side (d), one of the bits' sumcheck. -/
def lookRows (tl : HTailF2) : Nat := 31 + tl.f9.v + tl.f9.d + 1

/-- Lays the claims of the smallness test on the list: the program's `HTailF2.objectsF`
(Tail.lean:1042-1095), with the places turned that the head names: the claim on the lookup's key
vectors; the three claims on the planes; one tie for each matrix; the reads. The lookup's own claims
(Tail.lean:1050) are the lookup's block's. -/
def eqAll (tl : HTailF2) (funs : Array HFun) : EqM HTailF2 := do
  EqM.mustAs "internal-f-fun-closed" (tl.funClosed && funs.size == tl.funs.size)
  EqM.mustAs "internal-f-fun-moved" (tl.funsHeld funs)
  -- No claim of the sub-proof's own part has put a weight on a slot of the smallness test.
  EqM.testAs "internal-f-tail-slot"
    (← EqM.ask "objectsF:1047" fun F => some ((F.LS.extract tl.slotA tl.slotB).all isZeroE))
  let g ← EqM.get "objectsF:1048" tl.heard
  -- The lookup's block lays one claim for each of these rows, in front of this list.
  EqM.mustAs "internal-f-exist" (g.rows.size == lookRows tl)
  let before ← EqM.claims
  let tl ← eqKeys tl
  let tl ← eqCounts tl
  EqM.mustAs "internal-f-exist" ((← EqM.claims) - before == 4)
  let tl ← eqWeights tl
  let mut tieObj : Array Nat := #[]
  let mut tiesOn : Array Nat :=
    Array.replicate (← EqM.ask "objectsF:1060" fun F => some F.trees.size) 0
  for mu in List.range tl.NM do
    tieObj := tieObj.push (← EqM.claims)
    eqTie tl mu
    tiesOn := tiesOn.modify (tl.gtTree.getD mu 0) (· + 1)
  let mut rd : Array (Array Bool) := tl.tabLen.map fun n => Array.replicate n false
  let mut laid := 0
  for mu in List.range tl.NM do
    let M := tl.mats.getD mu {}
    for un in [0, 2] do
      for Fn in funs do
        if Fn.mat == mu && Fn.tree == un then
          EqM.mustAs "internal-t2f-unit" (tl.ix.U.getD un none).isSome
          EqM.mustAs "shape-functional"
            (Fn.len != 0 && M.m % Fn.len == 0 && Fn.phi.size == Fn.len)
          let sums := mulE (sumE Fn.phi) (sumE tl.vt)
          for sg in List.range (M.m / Fn.len) do
            -- C++ refuses here under: internal-f-table-read
            rd ← EqM.get "objectsF:1077" (tl.markRead Fn sg rd)
            eqRead tl Fn sg laid sums
            laid := laid + 1
  EqM.mustAs "internal-t2f-functional"
    (funs.all fun Fn => decide (Fn.mat < tl.NM) && (Fn.tree == 0 || Fn.tree == 2))
  EqM.mustAs "internal-f-table-read" (rd.all fun a => a.all id)
  -- C++ refuses here under: internal-t2f-table-outside, internal-t2f-tables-overlap,
  -- internal-f-tables-gap
  let segments1 ← EqM.get "objectsF:1085" (tl.tablesTile funs 0)
  let segments3 ← EqM.get "objectsF:1086" (tl.tablesTile funs 2)
  -- Counted from the claims: one tie on each symbol array and none on any other array, with arrays
  -- and claim indices all different; as many reads as the tables have segments.
  let kinds ← EqM.ask "objectsF:1089" fun F => some (F.trees.map (·.kind))
  EqM.mustAs "internal-f-exist" ((List.range kinds.size).all fun t =>
    tiesOn.getD t 0 == (if kinds.getD t .table == .symbols then 1 else 0))
  EqM.mustAs "internal-f-exist" (tiesOn.foldl (· + ·) 0 == tl.NM && laid == segments1 + segments3)
  EqM.mustAs "internal-f-exist" (allDistinct tieObj.toList && allDistinct tl.gtTree.toList)
  -- lsTail (Tail.lean:1094) is read off the ledger BEHIND the adding: it is laid by whoever adds
  pure { tl with tieObj := tieObj, tiesOn := tiesOn, nX4Laid := laid }

/-- **The border**: a plain function on data. front: the number of the link's claims that stand in
front of this list. -/
def equations (front : Nat) (tl : HTailF2) (funs : Array HFun) (F : Fork) :
    Except String (HTailF2 × Fork × List Claim) :=
  (eqAll tl funs front (F, #[])).map fun x => (x.1, x.2.1, x.2.2.toList)

end VerifiableInference.Desc.First.TailClaims
