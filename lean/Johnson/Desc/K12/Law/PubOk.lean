-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/PubOk.lean: a test, with code, of the public conditions that the library's
chain of a proximity test (the kind K12) asks of a place's declared rounds.

Definitions with code alone. There is no theorem in this file and no Mathlib beneath it, so that the
test can be compiled and run. The theorem that the test's yes gives the conditions is `pub_of_ok`
(Johnson/Desc/K12/Law/ChainOf.lean). The test answers the question whether the public premises of
the law of the kind K12 can be met at all.
Main names:
  `WR`, `writtenOf`: the declared rounds of a place (`H2U.roundsOfNums`) as plain written rounds:
    the entry, the kind by the name (`Fmt.kindOf`), the cut of the message (`Entry.cut`), the tree
    that the round sends, in the order of sending, and the own trees that it opens.
  `pubOk p K`: every public clause that `Chain.Pub` (OnBytes/Slice/ManyBlk.lean) and the type
    `Chain` (`CsFit` at every step) ask of the standard chain over these rounds, as one Boolean. K
    holds the record's codes.
  `pubL`, `pubNo`: the same as a list of named clauses, so that a run can say which clause refuses.
The clauses, stage by stage (a is the stage, b the next one). «idx»: the place names a pair of code
numbers for the stage. «h ≤ k»: the stage in the library's form, with g := k - h, is the place's.
«cut»: the rounds that are left are one round, k times one round, two rounds and the rest; at the
last stage just two. «fit.main», «fit.mask», «fit.powC», «fit.powZ», «fit.short»: `CsFit a b`. «C»,
«Z»: the record's codes at idx are the stage's. «small»: C.a ≤ 32. «seed», «cs», «base»: the
declared round is the format's `rSeed b`, `rCs work a` or `rBase work a` in entry, kind and items
(`IsRd`). «bits»: the sample's cube has the next stage's na variables. «own.*»: of the tree that the
round "SEND seed" sends: 1 ≤ k, the width, and one tree by running `Own.treesMade`
(Johnson/Desc/Own/Trees.lean); at the last stage h = 0, g = 0, the width 12, 2 ^ C.a positions and
the lay. «za»: at the last stage Z.a ≤ C.a.
Limits: A refusal of `Own.treesMade` counts as a no, which is more than `OneTree` asks. The test
makes the declared rounds out of the same numbers against which it holds them; that the declared
rounds are the plan's is tested elsewhere, by the block's comparison of its rounds with the plan's
entries. Nothing on soundness.
Nothing on hiding.

-/
import Johnson.Desc.K12.Frame
import Johnson.Desc.Own.Trees
import OnBytes.Iop.Prox

set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params
open VerifiableInference.Desc.K12 (P12)

/-- A written round as plain data. -/
structure WR where
  entry : Fmt.Entry
  kind : Fmt.Kind
  items : List Fmt.Item
  tree : Option Fmt.Shape
  opens : List Nat
  deriving DecidableEq

def ownOf : Fmt.Shape × Fmt.TreeSource → Option Nat
  | (_, .own n) => some n
  | _ => none

/-- Each declared round that sends a root gets the next shape. Nothing: a name without a kind; two
roots in a round; shapes left over or lacking. -/
def layW : List Fmt.DeclaredRound → List Fmt.Shape → Option (List WR)
  | [], [] => some []
  | [], _ :: _ => none
  | r :: rs, sh =>
    match Fmt.kindOf r.entry.name with
    | none => none
    | some k =>
      if r.entry.roots == 0 then
        (layW rs sh).map (⟨r.entry, k, r.entry.cut, none, r.opens.filterMap ownOf⟩ :: ·)
      else if r.entry.roots == 1 then
        match sh with
        | s :: t => (layW rs t).map
            (⟨r.entry, k, r.entry.cut, some s, r.opens.filterMap ownOf⟩ :: ·)
        | [] => none
      else none

/-- **The place's declared rounds as written rounds.** -/
def writtenOf (N : H2U.TestNums) : Option (List WR) :=
  (H2U.roundsOfNums N).bind fun ds =>
    layW ds (N.sent.zipIdx.map fun t => (N.own t.1.1 t.1.2 (N.free + t.2)).1)

/-- The row variables in the library's form: h + g with g := k - h. -/
def kk (a : Fmt.M1.Stage) : Nat := a.h + (a.k - a.h)

/-- The stage as the library's Sg.st gives it back. -/
def stN (a : Fmt.M1.Stage) : Fmt.M1.Stage := ⟨a.C, a.Z, a.h + (a.k - a.h), a.h, a.t⟩

/-- The stage in the program's form. -/
def ioOf (i : Nat × Nat) (a : Fmt.M1.Stage) : IoppStage :=
    { code := i.1, maskCode := i.2, k := a.k, h := a.h }

abbrev Clauses : Type := List (String × Bool)

def csFitL (s s' : Fmt.M1.Stage) : Clauses :=
  [("fit.main", decide (2 ^ (s'.h + (s'.k - s'.h)) * s'.C.l = s.C.l)),
   ("fit.mask", decide (2 * s.Z.l + s.C.r + 2 * s.Z.r + 1 ≤ 2 ^ s'.h * s'.Z.l)),
   ("fit.powC", decide (s'.C.l = 2 ^ Fmt.M1.lg s'.C.l)),
   ("fit.powZ", decide (s'.Z.l = 2 ^ Fmt.M1.lg s'.Z.l)),
   ("fit.short", decide (s.Z.a ≤ s.C.a))]

def ok (l : Clauses) : Bool := l.all (·.2)

def csFitB (s s' : Fmt.M1.Stage) : Bool := ok (csFitL s s')

def codeB (x : Option OnBytes.Code) (c : Fmt.M1.Code) : Bool := decide (x = some ⟨c.a, c.l, c.r⟩)

def isRdB (w : WR) (r : Fmt.Round) : Bool :=
  decide (w.entry = r.entry) && decide (w.kind = r.kind) && decide (w.items = r.items)

def colWB (t : Option Fmt.Shape) : Nat := (t.map (·.W)).getD 0
def posNB (t : Option Fmt.Shape) : Nat := (t.map (2 ^ ·.a)).getD 0

/-- The messages are laid in one tree, in their order. -/
def oneTreeB (K : Codes) (sent : Array OracleNotice) (logN : Nat) : Bool :=
  match VerifiableInference.Desc.Own.treesMade K sent with
  | none => false
  | some lay =>
    match lay.shapes.toList with
    | [sh] =>
      decide (sh.logN = logN) &&
        (List.range sent.size).all
            (fun i => decide (lay.tree.getD i 0 = 0) && decide (lay.part.getD i 0 = i)) &&
        decide (sh.mainSymbols =
            ((sent.toList.map (·.shape)).map fun s => s.mainRows * s.mainDeg).toArray) &&
        decide (sh.maskSymbols = ((sent.toList.map (·.shape)).map fun s => s.maskRows * 3).toArray)
    | _ => false

def sentMid (cu : IoppStage) (a : Fmt.M1.Stage) : Array OracleNotice :=
  #[⟨(switchTargetStage cu.code cu.maskCode (kk a) a.h 1).shape,
      (switchTargetStage cu.code cu.maskCode (kk a) a.h 1).leafClass⟩] ++
    #[foldMaskNotice (ioppFoldShape cu {})]

def sentLast (cu : IoppStage) (a : Fmt.M1.Stage) : Array OracleNotice :=
  #[⟨(switchTargetStage cu.code cu.maskCode (kk a) a.h 1).shape,
      (switchTargetStage cu.code cu.maskCode (kk a) a.h 1).leafClass⟩] ++
    #[baseMaskNotice cu.code cu.maskCode 1 0]

def lastLayB (K : Codes) (cu : IoppStage) (a : Fmt.M1.Stage) : Bool :=
  match VerifiableInference.Desc.Own.treesMade K (sentLast cu a) with
  | none => false
  | some lay =>
    match lay.shapes.toList with
    | [sh] =>
      decide (sh.logN = a.C.a) &&
        (List.range 2).all
            (fun i => decide (lay.tree.getD i 0 = 0) && decide (lay.part.getD i 0 = i)) &&
        decide (sh.mainSymbols = #[3, 3]) && decide (sh.maskSymbols = #[3, 3])
    | _ => false

/-- Of the tree of the stage a, sent in the round d. -/
def ownL (K : Codes) (a : Fmt.M1.Stage) (cu : IoppStage) (last : Bool) (d : WR) : Clauses :=
  if last then
    [("own.h0", decide (a.h = 0)), ("own.g0", decide (a.k - a.h = 0)),
     ("own.w", decide (colWB d.tree = 12)), ("own.n", decide (posNB d.tree = 2 ^ a.C.a)),
     ("own.lay", lastLayB K cu a)]
  else
    [("own.k1", decide (1 ≤ kk a)),
     ("own.w", decide (colWB d.tree = 3 * 2 ^ kk a + 3 * (2 * 2 ^ a.h))),
     ("own.one", oneTreeB K (sentMid cu a) a.C.a)]

def tag (j : Nat) (l : Clauses) : Clauses := l.map fun x => (toString j ++ ":" ++ x.1, x.2)

/-- The clauses from the stage number j on. l: the written rounds that are left. -/
def walkL (p : P12) (K : Codes) : Nat → Fmt.M1.Stage → List Fmt.M1.Stage → List WR → Clauses
  | j, a, [], l =>
    match p.idx[j]?, l with
    | some i, [_, dB] =>
      tag j [("h ≤ k", decide (a.h ≤ a.k)), ("C", codeB K.base[i.1]? a.C),
          ("Z", codeB K.mask[i.2]? a.Z),
        ("za", decide (a.Z.a ≤ a.C.a)), ("small", decide (a.C.a ≤ 32)),
        ("base", isRdB dB (Fmt.M1.rBase p.nums.work (stN a) 0))]
    | _, _ => [(toString j ++ ":idx, or cut at the last stage", false)]
  | j, a, b :: rest, l =>
    match p.idx[j]?, p.idx[j + 1]?, l with
    | some i, some n, _ :: dT :: l' =>
      match (dT :: l').drop (kk a) with
      | dS :: dC :: l'' =>
        tag j ([("h ≤ k", decide (a.h ≤ a.k)), ("next h ≤ k", decide (b.h ≤ b.k)),
          ("cut", decide ((dT :: l').take (kk a) = List.replicate (kk a) dT))] ++ csFitL a b ++
          [("C", codeB K.base[i.1]? a.C), ("Z", codeB K.mask[i.2]? a.Z),
           ("next C", codeB K.base[n.1]? b.C), ("next Z", codeB K.mask[n.2]? b.Z),
           ("small", decide (a.C.a ≤ 32)),
           ("seed", isRdB dS (Fmt.M1.rSeed (stN b))),
               ("cs", isRdB dC (Fmt.M1.rCs p.nums.work (stN a) 0 0)),
           ("bits", decide
               ((Send.cube K (switchTargetStage n.1 n.2 (kk b) b.h 1).shape).bits = (stN b).na))] ++
          ownL K b (ioOf n b) rest.isEmpty dS) ++ walkL p K (j + 1) b rest l''
      | _ => [(toString j ++ ":cut: no two rounds behind the fold's", false)]
    | _, _, _ => [(toString j ++ ":idx, or cut: no two rounds of a fold", false)]

/-- The named clauses at a place and the record's codes. -/
def pubL (p : P12) (K : Codes) : Clauses :=
  match p.nums.stages, writtenOf p.nums with
  | a :: rest, some (_ :: l) => walkL p K 0 a rest l
  | _, _ => [("no stage, or the declared rounds cannot be written", false)]

/-- The test: every public clause says yes. -/
def pubOk (p : P12) (K : Codes) : Bool := ok (pubL p K)

/-- The clauses that refuse. -/
def pubNo (p : P12) (K : Codes) : List String := ((pubL p K).filter (!·.2)).map (·.1)

end H2K.Pub
