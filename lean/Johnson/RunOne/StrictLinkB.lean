-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/StrictLinkB.lean: A PROBE WITHOUT LAWS: the SECOND compiler's strict verifier of one
slot, along lists and IN NAMED LINES, at an entry file's typed string as assembleS lays it (whole real paths).

WHAT IS RUN, PLAINLY. The letters are those at which the closed check of an entry file runs the LAX verifier
(entryPartO, OnBytes/TypedOracleCompiler/Slice/EntryVerdictRun.lean:64-88): the protocol (PSXE D dec).up, the wire (wqXL D dec []).sh, the
bodies ownES | bodyS, embPXE, the instance handed in (xin := some), the list [r0, r1], the family famOfO at the
format's hash. In the lax verifier's place: the chain (recomputeChain, run by AskShell's runOk), then the fourteen
named tests of behindSteps (OnBytes/Maker/ListedSteps.lean:67-107, general in the protocol): "strict 1-7",
"forests 1-2", "after 1-5": the parts of verifyBSL (OnBytes/TypedOracleCompiler/Compile/Batch/ListedVerifier.lean:117-134).
THE FOUR LISTS ARE MADE HERE, ON THE VERIFIER's SIDE, AND NOTHING IS PROVED OF THEM: own (ownOfTab) and listed
(listedOfTx): the keys of the two tables of which the string's openings are look-ups · the read leaves (rdOfR,
StrictLinkRd.lean: of the protocol's own reads) · the read external positions (lstX: ships, with laws). So a yes here
is a yes of verifyOneProtocol at this string ONLY IF verifyBSL_eq's premises hold of these lists: NOT SHOWN.
(Where this and lean/THEOREM.md differ, the page holds.)
IT IS NOT innerCompiledVerifier's LINK EITHER: verifyLinkProof (Johnson/TypedOracleCompiler/RecCompile/LinkAns.lean:88-91) has xin none, the two records as the
instance, the answers in the list, W's own bodies, the input's compilerParameters.sMT and m. It shares the compiler, the
protocol's make and, by the carrying armStringFull, the string.

`assembleT`: assembleS's text (OnBytes/TypedOracleCompiler/Slice/EntryTyping.lean:78-95) with the two tables as arguments, so that a
row can be added in memory. That assembleT at the file's own tables is assembleS: by reading; no law here.
The three calls: honest (yes) · unread: one row more, a copy of the first
table's first row, at the least place of that tree at which the table has no row (NO: A TEST THAT MUST BE REFUSED:
expected at "strict 3") · again: the same row behind the row of a place that is read (yes).
Limits. Evaluations, no theorems. No commitment ID. Made-up weights. Nothing on soundness.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryVerdictPlaces
import OnBytes.TypedOracleCompiler.Slice.EntryRunMain
import OnBytes.Maker.ListedSteps
import Johnson.RunOne.AskShell
import Johnson.RunOne.StrictLinkRd

set_option autoImplicit false

namespace Johnson.RunOne.StrictB
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD BodyD OwnE bodyS)
open _root_.Run.PQ (View SgX)
open _root_.Run (bytesToBits bytesToDig rootsB)
open TypedOracleCompiler.Run.EntryPageSafe (toBytesT)
open OnBytes.Tie (EntryGround linkAtCfg keyAt AskedE)
open OnBytes.Slice (s0Of seedEntry seedOfDrawnC)
open OnBytes.Slice.Shapes (Cfg scAt)
open TypedOracleCompiler.Slice
open OnBytes.Maker (Steps behindSteps)

/-- (a tree's number, a place) ↦ column, the file's salt, the whole path. -/
abbrev Tab : Type := List ((ℕ × ℕ) × Row)

/-- The two tables that assembleS makes of a chain as read: the own trees'; the stored tables'. -/
def tabsOf (D : XD) (o : _root_.Fmt.ChainOut) : Option (Tab × Tab) :=
  match tabOf (fun op => op.sh.tree) ((opsOf 1 o).filter fun op => !op.sh.stored),
    tabOf (whichOf D) ((opsOf 1 o).filter fun op => op.sh.stored) with
  | some tab, some tx => some (tab, tx)
  | _, _ => none

section
variable {X : Type} (D : XD) (dec : X → View → Bool)

/-- assembleS's text, the two tables being arguments. -/
def assembleT (o : _root_.Fmt.ChainOut) (tab tx : Tab) : Option (OneProtocolProof 256 (PSXE D dec).up) :=
  match o.run, PQ.plainsSL D.C D.ds o.rounds.toList with
  | some run, some pl =>
    some
      { salt := bytesToBits run
        roots := (rootsB o).map bytesToDig
        plains := ((), pl)
        opens := fun p => match p with
          | .inl e => e.elim
          | .inr q => opLS D.C (lookE run tab) 0 D.ds q
        ext := extE D.a D.base.cfg tx
        rtreq := fun _ => false
        slot := 0
        path := []
        rsalt := [] }
  | _, _ => none

/-- Where own openings can stand: none in the round in front; for each round and each of its trees the places
that the table lists under the tree's own number. -/
def ownOfTab (tab : Tab) : Leaves :=
  ([], []) :: D.ds.map fun d =>
    ([], d.trees.map fun s => (tab.filter fun z => z.1.1 == s.tree).map fun z => z.1.2)

/-- Where stored openings can stand. -/
def listedOfTx (a : ℕ) (tx : Tab) : List (Fin (2 ^ a) ⊕ Fin (2 ^ a)) :=
  tx.filterMap fun z =>
    if h : z.1.2 < 2 ^ a then
      some (if z.1.1 == 0 then Sum.inl ⟨z.1.2, h⟩ else Sum.inr ⟨z.1.2, h⟩)
    else none

variable {Bd : Type} (B : BodyD Bd) (E : OwnE Bd D) (early : X → X)
  (Tf : Unit → InteractiveOracleProof Unit (oneExternalString (2 ^ D.a) SgX))

/-- **The chain, then the fourteen named tests.** none: the chain returns nothing. -/
def stagesB (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (D.K + 1) (LXE (Bd := Bd) D early (Tf ()))))
    (cms : List (Dig 256)) (x : X) (π : OneProtocolProof 256 (PSXE D dec).up) (tab tx : Tab) : Option Steps :=
  match (Johnson.RunOne.Ask.runOk (L := LXE (Bd := Bd) D early (Tf ())) (K := D.K + 1)
      (fun _ _ => true) F
      (recomputeChain (L := LXE (Bd := Bd) D early (Tf ())) (K := D.K + 1) .link cms (some x) π.salt π.rtreq
        (PSXE D dec).up.loc.shape (PSXE D dec).up.ann (wqXL D dec []).sh
        (embPXE D early (Tf ())) 0 .first π.roots π.plains) #[] true).1 with
  | none => none
  | some (ρ, rts, ph) =>
    some (behindSteps (L := LXE (Bd := Bd) D early (Tf ())) (K := D.K + 1)
      (256 + 8 * D.base.plan.salt) 256 (PSXE D dec).up (wqXL D dec []).sh (weXL D.a []).less
      (wqXL D dec []).nOpen (wqXL D dec []).maxDepth E.emb B.embE 0 cms x π
      (ownOfTab D tab) (listedOfTx D.a tx)
      (TypedOracleCompiler.Run.Thin.rdOfR (PSXE D dec).S (PSXE D dec).ann (wqXL D dec []).sh
        ((PSXE D dec).reads x ρ
          (effPlains (PSXE D dec).up.loc.shape (PSXE D dec).up.ann rts π.plains)))
      (lstX D dec x ρ) F ρ rts ph)

end

/-- The least number that is no place of the table's rows under the tree t. -/
def freePlace (tab : Tab) (t : ℕ) : ℕ :=
  let ps := (tab.filter fun z => z.1.1 == t).map fun z => z.1.2
  ((List.range (ps.length + 1)).find? fun j => !ps.contains j).getD ps.length

/-- One row more behind the table: the first row's content, under its tree, at the place that pick names. -/
def oneMore (pick : Tab → ℕ → ℕ → ℕ) : Tab → Tab
  | z :: l => (z :: l) ++ [((z.1.1, pick (z :: l) z.1.1 z.1.2), z.2)]
  | [] => []

/-- A line on the error stream, at once. -/
def line (s : String) : IO Unit := do
  IO.eprintln s
  (← IO.getStderr).flush

/-- **The probe** at a ground G and a stored example's folder. It throws where a call does not end as expected. -/
def run (G : EntryGround)
    (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)
    (dir : String) : IO Unit := do
  let O : ByteArray → ByteArray := _root_.Fmt.oracle
  let rd (n : String) : IO ByteArray := IO.FS.readBinFile (dir ++ "/" ++ n)
  let pol ← rd "config/policy.txt"
  let lay ← rd "config/layout.txt"
  let kl ← rd "config/KL.bin"
  let key ← rd "ivk/key.bin"
  let ent ← rd "ivk/leaf/0.bin"
  line s!"read: {dir}: policy {pol.size} | layout {lay.size} | KL {kl.size} | key {key.size} | entry {ent.size} bytes"
  let cfg : Cfg := ⟨pol, lay, kl⟩
  let b₀ := O (toBytesT (scAt cfg))
  let c := _root_.Run.digToBytes (_root_.Run.digS b₀)
  let hc : c.size = 32 := _root_.Run.size_digToBytes _
  let b₁ := O (toBytesT (s0Of (G.bytesAt c)))
  let pd := _root_.Run.digS b₁
  let lg := G.q.link.table.cubeBits
  let s := G.q.link.table.answers
  let first := (keyAt G.q.link.table c key).2.2
  let a ← match convE (linkAtCfg G.q c) first ent with
    | none => throw (IO.userError "the entry file: the strict converter refuses it")
    | some v => pure v
  line s!"parse: the strict converter has read the entry file: yes; rounds {a.out.rounds.size}"
  line s!"fit: the tests on the parsed value (askedFit): {askedFit G.q.link.table a}"
  let D := entryXD G c
  line s!"pins: the description fits the table's shape (pinsFit): {pinsFit D G.q.link.table}"
  let dec := decRun (linkAtCfg G.q c) G.q.link.table.v lg s
  let F := EntryRunTop.famOfO D hc (d1Run lg s) G.q.link.table pd O
  let cms := [bytesToDig a.first.root, bytesToDig a.further.root]
  let x := xOfAskedC lg s a
  line s!"seeds: both tables' seeds, drawn again, are the parsed value's (cmpEL): {cmpEL D (earlyTwo (d1Run lg s)) (seedEntry lg s) (seedOfDrawnC lg s) F cms 0 x.2}"
  let tt ← match tabsOf D a.out with
    | none => throw (IO.userError "typing: a path's vertex was not met")
    | some v => pure v
  match tt.1 with
  | z :: _ =>
    line (s!"typed: depth of the stored tables {D.a}; rounds {D.ds.length}; own rows {tt.1.length}; stored rows " ++
      s!"{tt.2.length}; the change: tree number {z.1.1}; the free place {freePlace tt.1 z.1.1}; the place that has " ++
      s!"a row {z.1.2}; a column has {z.2.1.length} words")
  | [] => throw (IO.userError "the own trees' table has no row: nothing can be changed")
  let calls : List (String × Option String × Tab) :=
    [("honest: the tables as the typing makes them", none, tt.1),
      ("unread: one row more, at a place of the first tree at which nothing is read", some "strict 3",
        oneMore (fun l t _ => freePlace l t) tt.1),
      ("again: the same row more, behind the row of a place that is read", none,
        oneMore (fun _ _ j => j) tt.1)]
  let mut all := true
  for k in calls do
    line s!"=== {k.1}. EXPECTED: {match k.2.1 with | some w => "NO, first at \"" ++ w ++ "\"" | none => "yes"}"
    let π ← match assembleT D dec a.out k.2.2 tt.2 with
      | none => throw (IO.userError "typing: no string is laid")
      | some v => pure v
    let t0 ← IO.monoMsNow
    match stagesB D dec (bodyS D.a D.base.plan.salt) (ownES D (hok c hc)) (earlyTwo (d1Run lg s))
        (fun _ => TSE D (seedEntry lg s)) F cms x π k.2.2 tt.2 with
    | none =>
      line "chain: it returns nothing: NO"
      all := false
    | some st =>
      line s!"chain: it returns a value: yes [{(← IO.monoMsNow) - t0} ms]"
      let mut noes : List String := []
      for y in st do
        let s0 ← IO.monoMsNow
        let v := y.2.get
        line s!"{y.1}: {if v then "yes" else "NO"} [{(← IO.monoMsNow) - s0} ms]"
        unless v do noes := noes ++ [(y.1.splitOn ":").headD y.1]
      let ok := match k.2.1 with
        | some w => noes.head? == some w
        | none => noes.isEmpty
      line s!"said no: {noes}; {if ok then "AS EXPECTED" else "NOT AS EXPECTED"}"
      all := all && ok
  line ("THIS IS NO VERIFICATION: a probe without laws: the second compiler's strict verifier of one slot under the " ++
    "tag link, in named lines, along lists of which nothing is proved; not verifyTwo's link; no commitment ID; " ++
    "no soundness.")
  unless all do throw (IO.userError "a call did not end as expected")

end Johnson.RunOne.StrictB
