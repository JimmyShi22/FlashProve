-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ToyLk.lean: a small made-up example for the machinery of Run/PlanQX.lean.

The example is this library's own. It tests machinery only. Its decision ("every stored column that
is read ends in 7") has nothing of a link in it, and its interface's encoding and decoder are
placeholders. It has two stored tables of four columns and one round that draws five positions, of
which the first two go to the first table and the other three to the second. The protocol runs
through the verifier of Run/PlanQX.lean under two roots, with BLAKE2b behind typed oracle functions.

1. What the file contains. Two ways to a typed proof string.
   (1) The string is made in Lean from the two tables, by the format's own functions for the
   prover's side (the first chain value, the round's query, the draws, the trees' values), with
   whole paths.
   (2) From a file. The file is made by the same functions (32 random bytes, the first table's
   opening, the second's), read by the reader with stored tables (`wholeChainX`, Fmt/Rules8X.lean),
   and typed by Run/PlanQX.lean's `toBPrfX`.

2. What is checked when the file compiles. Nineteen tests (#guard). On typed strings: the honest
string is accepted; refused are wrong or swapped roots, changed words of the opened columns, a
changed bit of every opened leaf's salt, changed paths of either table, another starting value,
another position; an opening of the first table at a position drawn for the second alone is one too
many; the second table's opening there cannot be left out, nor the first table's at 0; the table
whose columns end in 8 is refused by the decision alone. From a file: the honest file is accepted;
the reader's view names the stored columns as `wantedX` does (same keys and positions, same order);
the typed string from the file has the same symbols and salts at all positions as the one made
directly; one changed bit in any byte behind the random bytes, a byte less, a byte more, and swapped
roots are refused by the reader.

3. Theorems.
   `vls_toy`: What is evaluated is the run of `Compile.Batch.vLS`, the function that the scheme's
     verifier applies to a proof's Link string, at the whole wiring `WkL`, for every decision, roots
     and string.

4. What is not claimed. No statement on soundness. Nothing about the programs' files.
Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PlanQX
import Run.PlanPull

set_option autoImplicit false

namespace Run.ToyLk
open Iop Rom Compile Compile.Batch Run.PQ

def cfgL : ByteArray := _root_.Fmt.configDigest [_root_.Fmt.ascii "toy link\n"]
def entL : _root_.Fmt.Entry := { name := "toylk: positions", poss := 5, logN := 2 }
def planL : _root_.Fmt.Plan :=
  { field := .two, salt := 40, nonce := 8, posB := 0, samples := 0, saved := 1, entries := [entL] }
def paramsL : ByteArray := _root_.Fmt.paramsBytes planL cfgL []
def pdL : ByteArray := _root_.Fmt.paramsDigest paramsL
def labL : Nat := 11

structure Tab where
  col  : Nat → List UInt64
  salt : Nat → ByteArray

def tab0 : Tab :=
  ⟨fun x => [UInt64.ofNat (x + 1), UInt64.ofNat (2 * x), 7],
    fun x => _root_.Fmt.pattern 40 (x + 2) 1⟩
def tab1 : Tab :=
  ⟨fun x => [UInt64.ofNat (x + 1), UInt64.ofNat (2 * x), 7],
    fun x => _root_.Fmt.pattern 40 (x + 9) 3⟩
def tab8 : Tab :=
  ⟨fun x => [UInt64.ofNat (x + 1), UInt64.ofNat (2 * x), 8],
    fun x => _root_.Fmt.pattern 40 (x + 9) 3⟩

def Tab.values (T : Tab) : List (List ByteArray) :=
  _root_.Fmt.build cfgL 2
    ((List.range 4).map fun x => _root_.Fmt.leaf 174 0 2 x cfgL (T.col x) (T.salt x))
def Tab.root (T : Tab) : ByteArray := _root_.Fmt.rootOf T.values
/-- The whole path of leaf x, from the leaf's sibling upwards. -/
def Tab.path (T : Tab) (x : Nat) : List (Dig 256) :=
  [bytesToDig ((T.values.getD 2 []).getD (x ^^^ 1) ByteArray.empty),
    bytesToDig ((T.values.getD 1 []).getD ((x / 2) ^^^ 1) ByteArray.empty)]

def stmL (r0 r1 : ByteArray) : ByteArray :=
  _root_.Fmt.tableItem "the first table" r0 [] ++ _root_.Fmt.tableItem "the further table" r1 []

def dsL : List RD := [⟨entL, .positions, [], none, []⟩]
def xsL : List XO := [⟨0, false, 0, 2⟩, ⟨0, true, 2, 3⟩]
def decL : View → Bool := fun v => v.opened.all fun o => o.2.2.getLast? == some 7
abbrev CL : CK := ckP .two
def KL : Nat := kMax (fun e k => (bsRound .two e k).b) dsL

abbrev LL (dec : View → Bool) : BatchProtocol Unit Unit :=
  LkX (I := Unit) (RI := Unit) CL dsL 2 xsL dec (fun _ _ p => (p.val, [0, 0, 7])) (fun _ => some ())

/-- The spellings of the rounds after the first query. -/
def PDL (dec : View → Bool) : PageD (LL dec) .link where
  label := labL
  kind := fun i => if i = 0 then 7 else ((dsL[i - 1]?).map (·.kind.num)).getD 7
  work := fun i => if i = 0 then 0 else ((dsL[i - 1]?).map (·.entry.work)).getD 0
  stm := fun _ => ByteArray.empty
  msg := fun _ rt pl => match pl with
    | .inl _ => ByteArray.empty
    | .inr q => msgSL CL (rt.getD ByteArray.empty) dsL q
  nonce := fun _ pl => match pl with
    | .inl _ => 0
    | .inr q => nonceSL CL dsL q
  leaf := fun s => match s with
    | ⟨.inl p, _⟩ => p.elim
    | ⟨.inr q, col⟩ => leafSL CL 40 dsL ⟨q, col⟩
  cfg := cfgL

/-- The first query: the two digests in its head are the roots: they go into the statement's two
items; the parameters' digest is a constant. -/
def firstL (dec : View → Bool) (K : Nat) (q : FbIn 256 (LL dec) .link) (j : Fin (K + 1)) :
    Option _root_.Fmt.OQ :=
  match q.round, q.head with
  | 0, .f1 [cm, cm'] none salt =>
      if j.val = K then
        some ⟨0, 160, 0, labL, _root_.Fmt.zero32,
            firstBytes pdL (stmL (digToBytes cm) (digToBytes cm')) salt⟩
      else none
  | 0, _ => none
  | _, _ => fbCall (PDL dec) K q j

/-- A leaf: of a stored tree (the symbol carries its position; the start is the configuration's
digest), or of the chain's own. -/
def leafL (dec : View → Bool) (q : LeafIn (LL dec)) : Option _root_.Fmt.OQ :=
  match q.body with
  | some (.inl s) =>
      if bitsToBytes (q.salt.take 256) == cfgL then
        some ⟨0, 174, _root_.Fmt.leafPlace 0 s.2.length ((q.salt.length - 256) / 64), 2 ^ 2 + s.1,
          cfgL, _root_.Fmt.leafBytes s.2 (bitsToBytes (q.salt.drop 256))⟩
      else none
  | _ => leafCall (PDL dec) q

def famL (dec : View → Bool) (O : ByteArray → ByteArray) (K : Nat) : Fam (spec 256 K (LL dec))
  | .leaf, q => ansOf O (leafL dec q)
  | .node, q => ansOf O (nodeCallC cfgL q)
  | .fb .link, q => (fun k => ansOf O (firstL dec K q k.castSucc), ansOf O (firstL dec K q (Fin.last K)))
  | .fb .test, _ => (fun _ _ => false, fun _ => false)
  | .fb .onl, _ => (fun _ _ => false, fun _ => false)
  | .fbw _ _, _ => (fun _ _ => false, fun _ => false)
  | .rleaf, _ => fun _ => false
  | .rnode, _ => fun _ => false
  | .g _, _ => fun _ => false
  | .ann, _ => ()
  | .other, _ => fun _ => false

def rndL : ByteArray := _root_.Fmt.pattern 32 5 22

/-- What the honest prover sees drawn. -/
def drawsL (T0 T1 : Tab) (rnd : ByteArray := rndL) : Option (ByteArray × List Nat) :=
  match _root_.Fmt.startChain labL pdL (stmL T0.root T1.root) (some rnd) with
  | some ⟨some run, rho0⟩ =>
    match _root_.Fmt.Chain.query ⟨labL, rho0, 0⟩ ByteArray.empty .positions 0 0 KL with
    | none => none
    | some (_, vb) =>
      some (run, (_root_.Fmt.drawRound .two entL .positions (_root_.Fmt.rowOf vb)).poss)
  | _ => none

/-- The honest typed string. -/
def piL (dec : View → Bool) (T0 T1 : Tab) (rnd : ByteArray := rndL) :
    Option (OneProtocolProof 256 (skeletonOverBothExternalStrings CL dsL 2 xsL dec).up) :=
  (drawsL T0 T1 rnd).map fun rp =>
    let l0 := _root_.Fmt.listOf (rp.2.take 2)
    let l1 := _root_.Fmt.listOf ((rp.2.drop 2).take 3)
    ⟨bytesToBits rp.1, [], ((), ((), ())), fun _ => none,
      fun p => match p with
        | .inl x =>
          if l0.contains x.val then
            some ⟨(x.val, T0.col x.val), leafSalt cfgL (T0.salt x.val), T0.path x.val⟩
          else none
        | .inr x =>
          if l1.contains x.val then
            some ⟨(x.val, T1.col x.val), leafSalt cfgL (T1.salt x.val), T1.path x.val⟩
          else none,
      fun _ => false, 0, []⟩

def runL (dec : View → Bool) (r0 r1 : ByteArray) (π : OneProtocolProof 256 (skeletonOverBothExternalStrings CL dsL 2 xsL dec).up) :
    Bool :=
  VPX (I := Unit) (RI := Unit) CL KL (chalP .two KL) dsL 2 xsL dec
    (fun _ _ p => (p.val, [0, 0, 7])) (fun _ => some ()) (famL dec _root_.Fmt.oracle (KL + 1))
    (256 + 8 * 40) (bytesToDig r0) (bytesToDig r1) π

/-! ## vLS as a term -/

/-- The whole wiring of the toy's interface: Link's is the protocol's; Test, Batch without a round.
-/
def WkL (dec : View → Bool) : QueryLayout 256 (LL dec) where
  K := KL + 1
  T := ⟨(), WireE.one (2 ^ 2) SgX (0, []), inferInstanceAs (DecidableEq Empty), 0, 2⟩
  Lk := wqX CL KL (chalP .two KL) dsL 2 xsL dec
  B := ⟨(), WireE.one (2 ^ 2) SgX (0, []), inferInstanceAs (DecidableEq Empty), 0, 2⟩
  depth := 2
  depthReq := 0

/-- States that what runs is the run of `Compile.Batch.vLS`: the function that the scheme's verifier
runs on a proof's Link string, under the key's root and the proof's. -/
def Spec.vls_toy : Prop :=
  ∀ (dec : View → Bool) (r0 r1 : ByteArray) (π : OneProtocolProof 256 (skeletonOverBothExternalStrings CL dsL 2 xsL dec).up),
    runL dec r0 r1 π =
      (vLS (WkL dec) (256 + 8 * 40) 256 (bytesToDig r0) (bytesToDig r1) π).det
        (famL dec _root_.Fmt.oracle (KL + 1))

theorem vls_toy : Spec.vls_toy := fun dec r0 r1 π =>
  vpx_eq Unit Unit CL KL (chalP .two KL) dsL 2 xsL dec (fun _ _ p => (p.val, [0, 0, 7]))
    (fun _ => some ()) (famL dec _root_.Fmt.oracle (KL + 1)) (256 + 8 * 40)
    (bytesToDig r0) (bytesToDig r1) π

/-! ## From a file -/

def shL : _root_.Fmt.Shape := { a := 2, W := 3, stored := true, tree := 0 }

/-- The chain as the reader with stored tables needs it. -/
def specL (r0 r1 : ByteArray) : _root_.Fmt.SpecX where
  base := { label := labL, plan := planL, params := paramsL, statement := stmL r0 r1,
            rand := .inFile, cfg := cfgL,
            rounds := [{ entry := entL, kind := .positions, items := [], opens := [] }] }
  stored := [[⟨shL, 40, 0, 0, 2⟩, ⟨shL, 40, 1, 2, 3⟩]]

/-- The file: the random bytes, the first table's opening, the second's. -/
def fileL (T0 T1 : Tab) (rnd : ByteArray := rndL) : ByteArray :=
  match drawsL T0 T1 rnd with
  | none => ByteArray.empty
  | some rp =>
    rnd ++ _root_.Fmt.openingBytes 2 T0.col T0.salt T0.values (_root_.Fmt.listOf (rp.2.take 2)) ++
      _root_.Fmt.openingBytes 2 T1.col T1.salt T1.values (_root_.Fmt.listOf ((rp.2.drop 2).take 3))

inductive WhoL where
  | accepted | verifier | reader
  deriving DecidableEq, Repr

/-- The run on a file: the reader with stored tables, the typing, the verifier `runL` under the two
roots. -/
def runFileL (dec : View → Bool) (r0 r1 file : ByteArray) : WhoL :=
  match (_root_.Fmt.wholeChainX (m := Id) _root_.Fmt.formatHash (specL r0 r1) file).bind
      (toBPrfX 40 cfgL CL dsL 2 xsL dec) with
  | none => .reader
  | some π => if runL dec r0 r1 π then .accepted else .verifier

/-- One bit of byte i flipped. -/
def flipL (b : ByteArray) (i : Nat) : ByteArray := b.set! i (b.get! i ^^^ 1)

/-- The type of the typed strings that the alterations below change. -/
abbrev PiL : Type := OneProtocolProof 256 (skeletonOverBothExternalStrings CL dsL 2 xsL decL).up
def onExt (f : (Fin 4 ⊕ Fin 4) → Opening 256 SgX → Opening 256 SgX) (π : PiL) : PiL :=
  { π with ext := fun p => (π.ext p).map (f p) }
def isL (p : Fin 4 ⊕ Fin 4) : Bool := p.elim (fun _ => true) fun _ => false
/-- Every word of every opened column of one table, raised by 1. -/
def colUp (first : Bool) : PiL → PiL :=
  onExt fun p op =>
    if isL p == first then ⟨(op.sym.1, op.sym.2.map (· + 1)), op.salt, op.path⟩ else op
/-- The last bit of every opened leaf's salt of one table. -/
def saltUp (first : Bool) : PiL → PiL :=
  onExt fun p op =>
    if isL p == first then ⟨op.sym, op.salt.dropLast ++ [!(op.salt.getLast?.getD false)], op.path⟩
    else op
/-- The first bit of the salts: another start. -/
def startUp : PiL → PiL :=
  onExt fun _ op => ⟨op.sym, (!op.salt.headD false) :: op.salt.drop 1, op.path⟩
/-- Every digest of every path of one table. -/
def pathUp (first : Bool) : PiL → PiL :=
  onExt fun p op => if isL p == first then ⟨op.sym, op.salt, op.path.map fun d i => !d i⟩ else op
/-- Every symbol carries the next position. -/
def posUp : PiL → PiL := onExt fun _ op => ⟨(op.sym.1 + 1, op.sym.2), op.salt, op.path⟩
/-- An opening more, where nothing is read (`more`); an opening fewer (`fewer`). -/
def more (T : Tab) (p : Fin 4 ⊕ Fin 4) (π : PiL) : PiL :=
  { π with
    ext := fun q =>
        if q = p then
          some ⟨(p.elim (·.val) (·.val), T.col (p.elim (·.val) (·.val))),
              leafSalt cfgL (T.salt (p.elim (·.val) (·.val))),
              T.path (p.elim (·.val) (·.val))⟩
        else π.ext q }
def fewer (p : Fin 4 ⊕ Fin 4) (π : PiL) : PiL :=
  { π with ext := fun q => if q = p then none else π.ext q }
/-- The two tables' openings changed over. -/
def swap (π : PiL) : PiL := { π with ext := fun q => π.ext (q.elim .inr .inl) }

def tryL (T0 T1 : Tab) (f : PiL → PiL) (r0 r1 : ByteArray) : Option Bool :=
  (piL decL T0 T1).map fun π => runL decL r0 r1 (f π)

end Run.ToyLk

open Run.ToyLk Run.PQ

-- two blocks a verifier's message; the draws 3, 0 | 0, 3, 1: the first table is read at 0, 3, the
-- second at 0, 1, 3
#guard KL = 2 && (drawsL tab0 tab1).map (·.2) == some [3, 0, 0, 3, 1] && okX dsL 2 xsL
-- the honest string is accepted under the two roots
#guard tryL tab0 tab1 id tab0.root tab1.root == some true
-- the two tables have the same columns and other salts: so other roots
#guard tab0.root != tab1.root
-- under other roots: refused: one root wrong; the two changed over
#guard tryL tab0 tab1 id tab1.root tab1.root == some false && tryL tab0 tab1 id tab0.root tab0.root == some false && tryL tab0 tab1 id tab1.root tab0.root == some false
-- the words of the opened columns, a bit of every opened leaf's salt, the paths' digests: of either
-- table: refused
#guard [colUp true, colUp false, saltUp true, saltUp false, pathUp true, pathUp false].map (fun f => tryL tab0 tab1 f tab0.root tab1.root) == List.replicate 6 (some false)
-- another start in the leaves' typed salts; symbols that carry another position: refused
#guard tryL tab0 tab1 startUp tab0.root tab1.root == some false && tryL tab0 tab1 posUp tab0.root tab1.root == some false
-- the cut of the list bites: position 1 is drawn for the second table alone: an opening of the
-- first table there is one too many (the strict format); the second table's opening there cannot be
-- left out; nor the first table's at 0
#guard tryL tab0 tab1 (more tab0 (.inl 1)) tab0.root tab1.root == some false && tryL tab0 tab1 (fewer (.inr 1)) tab0.root tab1.root == some false && tryL tab0 tab1 (fewer (.inl 0)) tab0.root tab1.root == some false
-- an opening where nothing is read (position 2 of either table): refused
#guard tryL tab0 tab1 (more tab0 (.inl 2)) tab0.root tab1.root == some false && tryL tab0 tab1 (more tab1 (.inr 2)) tab0.root tab1.root == some false
-- the two tables' openings changed over: refused
#guard tryL tab0 tab1 swap tab0.root tab1.root == some false
-- another second table, honestly committed and opened, whose columns end in 8: refused; at the
-- decision that asks nothing the same tables' string is accepted: so every hash, the format and the
-- positions are right, and the decision alone refuses
#guard tryL tab0 tab8 id tab0.root tab8.root == some false
#guard (piL (fun _ => true) tab0 tab8).map (runL (fun _ => true) tab0.root tab8.root) == some true

/-! ## From a file -/

#guard (specL tab0.root tab1.root).ok
-- the honest file: read, typed, accepted
#guard runFileL decL tab0.root tab1.root (fileL tab0 tab1) == .accepted
-- the reader's view names the stored columns as the typed side's wantedX does: the same keys and
-- positions in the same order
#guard ((_root_.Fmt.wholeChainX (m := Id) _root_.Fmt.formatHash (specL tab0.root tab1.root) (fileL tab0 tab1)).map fun o => ((_root_.Fmt.viewX (specL tab0.root tab1.root) o).opened.map fun x => (x.1, x.2.1))) == (drawsL tab0 tab1).map fun rp => wantedX 2 dsL xsL [⟨[], rp.2, [], none⟩]
-- the typed string from the file and the one made directly have the same openings (symbols, salts)
-- at every position; the paths may differ where the pruned walk does not read them
#guard ((_root_.Fmt.wholeChainX (m := Id) _root_.Fmt.formatHash (specL tab0.root tab1.root) (fileL tab0 tab1)).bind (toBPrfX 40 cfgL CL dsL 2 xsL decL)).bind (fun π => (piL decL tab0 tab1).map fun π' => (weX 2).all.all fun p => ((π.ext p).map fun o => (o.sym, o.salt)) == ((π'.ext p).map fun o => (o.sym, o.salt))) == some true
-- this reader checks the openings itself: one bit of any byte behind the random bytes: the reader
-- refuses; a byte short, a byte more: the reader
#guard (List.range ((fileL tab0 tab1).size - 32)).all fun i => runFileL decL tab0.root tab1.root (flipL (fileL tab0 tab1) (32 + i)) == .reader
#guard runFileL decL tab0.root tab1.root ((fileL tab0 tab1).extract 0 ((fileL tab0 tab1).size - 1)) == .reader && runFileL decL tab0.root tab1.root ((fileL tab0 tab1).push 0) == .reader
-- under other roots: the reader
#guard runFileL decL tab1.root tab0.root (fileL tab0 tab1) == .reader
-- the other second table, honestly committed and opened: the reader reads it, the verifier (its
-- decision) refuses; at the decision that asks nothing: accepted
#guard runFileL decL tab0.root tab8.root (fileL tab0 tab8) == .verifier && runFileL (fun _ => true) tab0.root tab8.root (fileL tab0 tab8) == .accepted
