-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Print/ToyRun.lean: a test: FROM THE COMPILED PROVER TO THE LIBRARY's VERIFIER's YES,
THROUGH THE BYTES, at one small whole file.

The road: the compiled prover (proveX, OnBytes/Prover/Defs.lean) at coins of the bytes' form
(coinsOf) · its typed string printed (carrierOf) and written as bytes (wrFile) · the library's
reader and maker with its three judged rows (madeFileOf, Johnson/Top/Fire/Code/FileInOf.lean) · the
library's typing (File.toBPrfAt) · the library's compiled verifier (verifyOneProtocol) at the file's own wire
record (wqWhole), under one family g of oracle functions with digests of 256 bits.

Why. The theorems of this folder stand under premises. Here they are met together, with openings in
every tree and in the stored table, and nine turned runs are refused, each at the stage foretold.

The data: chain 1: one round with a bit of work, the items word, root, f, root, two trees; chain 2
(shared): one round that draws a position, the items root, e, one tree; it opens tree 0 and the
stored table; chain 3: one round that draws a position, the items answer, root, one tree; it opens
the trees 2, 3, 1. A stored table of depth 1; a binding tree of depth 1, the place 1; two bytes of a
leaf's own salt.

Main names.
  Ct, chal     A TOY KIT of verifier's messages: one hash block; positions are read off its bits.
    NOT the format's kit.
  g            the oracle functions: each answer's bits are bits of a number made of a code of the
    query. Of a plain part they read the nonce of chain 1's written round alone.
  run, yes     the prover's outcome; the verifier's value at a typed string.
  stage        from bytes: 0 the reader refuses · 1 a judged row says no · 2 the typing lays nothing
    · 3 the verifier says no · 4 yes.
  returns, typed_yes, yes_through, opened   the prover returns and the interactive verifier accepts;
    the typed string is accepted; THROUGH THE BYTES: stage 4; one row is opened in each of the four
    trees and one in the stored table.
  no_*         nine turned runs, each with its stage; at three of them the typed string is accepted
    and the printed one is not.

Limits: a test, by evaluation in Lean's kernel, at one family of functions and one strategy. ONE
WHOLE FILE AT FREE LETTERS: the goals' decoder and verifier stand at letters of the full size alone
and are not run here. The decision on the views and the test on the silent rounds are "true". No
entry's file. The forecasts were written before the calls. Compiling this file took seven to
fourteen minutes in five builds on our machines, and about 15 GiB of memory (sampled in one).
Terms: lean/GLOSSARY.md.
-/
import OnBytes.Prover.Print.Honest
import OnBytes.Prover.Print.Bytes
import Johnson.Top.Fire.Code.FileInOf
import Compile.MerkleList
import Rom.Cache

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Print.ToyRun

open _root_.Run _root_.Run.PQ Compile.Joined Rom
open _root_.Compile (Tag Opening)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch
open OnBytes.Maker OnBytes.Maker.Carrier
open OnBytes.Prover OnBytes.Prover.Print

/-! ## A toy kit of verifier's messages: one hash block; positions are read off its bits -/

def nb : _root_.Fmt.Kind → ℕ
  | .nothing => 0
  | _ => 1

def posAtBit (d : Dig 256) (i : ℕ) : ℕ :=
  (if d ⟨(2 * i) % 256, Nat.mod_lt _ (by decide)⟩ then 1 else 0) +
    (if d ⟨(2 * i + 1) % 256, Nat.mod_lt _ (by decide)⟩ then 2 else 0)

def Ct : CK where
  Ch := fun _ k => Fin (nb k) → Dig 256
  fin := fun _ _ => inferInstance
  ne := fun _ _ => inferInstance
  dr := fun e k u =>
    ⟨[], (List.range e.poss).map fun i =>
      if h : 0 < nb k then posAtBit (u ⟨0, h⟩) i else 0, [], none⟩
  front := ⟨⟨fun i => i.elim0⟩, fun _ => funext fun i => i.elim0⟩

def chal : ∀ e k, (Fin 1 → Dig 256) → Ct.Ch e k := fun _ k => firstBlocks 256 1 (nb k)

/-! ## The data -/

def rdA : RDT :=
  { entry := { name := "a", work := 1 }, kind := .elems, items := [.word, .root, .f, .root],
    trees := [⟨1, 1, false, 0⟩, ⟨0, 2, false, 1⟩], opens := [], stored := [] }
def rdB : RDT :=
  { entry := { name := "b", poss := 1, logN := 1 }, kind := .positions, items := [.root, .e],
    trees := [⟨1, 2, false, 2⟩], opens := [0], stored := [⟨⟨1, 2, true, 0⟩, 2, 0, 0, 1⟩] }
def rdC : RDT :=
  { entry := { name := "c", poss := 1, logN := 1 }, kind := .positions, items := [.answer, .root],
    trees := [⟨1, 1, false, 3⟩], opens := [2, 3, 1], stored := [] }
def D : WholeD := ⟨1, [rdA], [rdB], [rdC], id, id, id⟩

def tF : FrontMsg (List OnBytes.E) := ⟨[], 0⟩
def tJ : JoinMsg (List OnBytes.E) ByteArray := ⟨[], ByteArray.empty⟩
def t3 : ByteArray := ByteArray.empty
def sil : Unit → FrontMsg (List OnBytes.E) → JoinMsg (List OnBytes.E) ByteArray → ByteArray →
    Bool := fun _ _ _ _ => true
def rn : Unit → View → View → View → Bool := fun _ _ _ _ => true

abbrev Q : BatchInteractiveOracleProof Unit (oneExternalString (2 ^ D.a) SgX) := (wholeDesc Ct D tF tJ t3 sil rn).batch
abbrev Prf : Type := OneProtocolProof 256 Q
def wq : ProtocolQueryLayout 256 2 Q := wqWhole Ct 1 chal D tF tJ t3 sil rn

/-! ## The interface record; the body of a leaf is a list of numbers -/

@[reducible] def pT : InteractiveOracleProof Unit (oneExternalString (2 ^ D.a) SgX) where
  shape := []
  blinded := fun _ => false
  extReads := fun _ _ => ∅
  reads := fun _ _ _ => ∅
  accept := fun _ _ _ => true

@[reducible] def pK : InteractiveOracleProof Unit (twoExternalStrings (2 ^ D.a) SgX) where
  shape := []
  blinded := fun _ => false
  extReads := fun _ _ => ∅
  reads := fun _ _ _ => ∅
  accept := fun _ _ _ => true

@[reducible] def L : BatchProtocolWithLeafBody Unit Unit where
  wordLength := 2 ^ D.a
  Symbol := SgX
  EncodingRandomness := Unit
  encodeIndex := fun _ _ _ => (0, [])
  decodeIndex := fun _ => some ()
  offline := pT
  link := pK
  maxBatchSize := 2
  onlineBatch := Q
  honestOfflineProver := _root_.Run.dummyH pT fun _ _ => (0, [])
  honestLinkProver := _root_.Run.dummyH pK fun _ => (fun _ => (0, []), fun _ => (0, []))
  honestOnlineBatchProver := _root_.Run.dummyB Q fun _ _ => (0, [])
  early := id
  late := none
  Bd := List ℕ
  annT := PUnit.unit
  annL := PUnit.unit

def nums (l : List UInt64) : List ℕ := l.map (·.toNat)

def embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L
  | .inl e, _ => nomatch e
  | .inr (.inl p), a => 1 :: nums (colT rdA.trees p a)
  | .inr (.inr (.inl e)), _ => nomatch e
  | .inr (.inr (.inr (.inl p))), a => 2 :: nums (colT rdB.trees p a)
  | .inr (.inr (.inr (.inr (.inl e)))), _ => nomatch e
  | .inr (.inr (.inr (.inr (.inr (.inl p))))), a => 3 :: nums (colT rdC.trees p a)
  | .inr (.inr (.inr (.inr (.inr (.inr e))))), _ => nomatch e

def embE (s : SgX) : Body L := 9 :: s.1 :: nums s.2

/-! ## Oracle functions -/

def bitsN (l : List Bool) : ℕ := l.foldl (fun a b => 2 * a + 1 + b.toNat) 0
def listN (l : List ℕ) : ℕ := l.foldl (fun a b => 4294967311 * a + 1 + b) 0
def digsN (l : List (Dig 256)) : ℕ := listN (l.map fun d => bitsN (List.ofFn d))

def headN : Head 256 Unit → ℕ
  | .f1 cms _ salt => 5 * (digsN cms + 31 * bitsN salt)
  | .f2 _ ρ => 5 * (3 * bitsN ρ) + 1
  | .f3 ρ0 c => 5 * (bitsN ρ0 + 1009 * bitsN c) + 2
  | .f4 cms r => 5 * (digsN cms + 2003 * bitsN r) + 3
  | .f5 ρ0 => 5 * bitsN ρ0 + 4

/-- of a plain part: the nonce of chain 1's written round alone -/
def plainN : PlainPart Q.loc.shape Q.ann → ℕ
  | .inr (.inl (.inr pl)) => 1 + (show (UInt64 × UInt64 × Unit) × ℕ from pl).2
  | _ => 0

def plainT : (t : Tag) → PlainPart (shapeOf L t) (annOf L t) → ℕ
  | .onl, z => plainN z
  | .test, z => nomatch z
  | .link, z => nomatch z

def mix (n c : ℕ) : Bool :=
  let h1 := ((c + 1) * 2654435761 + (n + 1) * 40503) % 4294967296
  let h2 := ((h1 ^^^ (h1 >>> 15)) * 2246822519) % 4294967296
  (h2 ^^^ (h2 >>> 13)) % 2 == 1
def dg (c : ℕ) : Dig 256 := fun i => mix (37 * i.val) c

def fbN {t : Tag} (q : FbIn 256 L t) : ℕ :=
  q.round + 6 * headN q.head + 4001 * digsN q.rt + 97 * plainT t q.plain

def g : Fam (typedOracleFamily 256 2 L)
  | .leaf => fun q => dg (3 + 11 * listN (show List ℕ from q.body) + 5003 * bitsN q.salt)
  | .node => fun q => dg (1 + 13 * bitsN q.1 + 6007 * bitsN q.2)
  | .rleaf => fun q => dg (2 + 17 * bitsN q)
  | .rnode => fun q => dg (4 + 19 * bitsN q.1 + 7001 * bitsN q.2)
  | .fb _ => fun q => (fun j => dg (fbN q + 2 + j.val), dg (fbN q + 1))
  | .fbw _ _ => fun q => (fun j => dg (fbN q + 2 + j.val), dg (fbN q + 1))
  | .g t => fun q => dg (q.round + 3 * bitsN q.ρ + 8009 * digsN q.rt + 101 * plainT t q.plain)
  | .ann => fun _ => ()
  | .other => fun _ => dg 0

/-! ## The strategy, the coins, the outer tree -/

def r1 : ByteArray := _root_.Fmt.pattern 32
def r2 : ByteArray := _root_.Fmt.pattern 32 5 1
def r3 : ByteArray := _root_.Fmt.pattern 32 11 2
def cfg : ByteArray := _root_.Fmt.pattern 32 13 4
def sB : OnBytes.Params.LinBindingShape := ⟨1, 4⟩
def ans : List OnBytes.E := [OnBytes.E.ofTriple (1, 2, 3)]

def oA : (p : PosT rdA.trees) → SymT rdA.trees p
  | .inl x => fun _ => (20 + x.val.toUInt64 : UInt64)
  | .inr (.inl _) => fun i => (30 + i.val.toUInt64 : UInt64)
  | .inr (.inr e) => nomatch e
def oB : (p : PosT rdB.trees) → SymT rdB.trees p
  | .inl x => fun i => (50 + 2 * x.val.toUInt64 + i.val.toUInt64 : UInt64)
  | .inr e => nomatch e
def oC : (p : PosT rdC.trees) → SymT rdC.trees p
  | .inl x => fun _ => (60 + x.val.toUInt64 : UInt64)
  | .inr e => nomatch e

/-- the strategy; b2: the run value that it sends in the joining round -/
def σ (b2 : ByteArray) : Strat Q.loc.shape Unit :=
  (((), (⟨ans, 6⟩ : FrontMsg (List OnBytes.E))), fun _ =>
    ((oA, (((7 : UInt64), ((9 : UInt64), ())), (0 : ℕ))), fun _ =>
      (((), (⟨ans, b2⟩ : JoinMsg (List OnBytes.E) ByteArray)), fun _ =>
        ((oB, (((1 : UInt64), (2 : UInt64), (3 : UInt64)), ())), fun _ =>
          (((), r3), fun _ =>
            ((oC, (((4 : UInt64), (5 : UInt64), (6 : UInt64)), ())), fun _ => ()))))))

/-- the byte coins; a1: the first run value -/
def bc (a1 : ByteArray) : ByteCoins L where
  run1 := a1
  run2 := r2
  run3 := r3
  leaf := fun i b k j => _root_.Fmt.pattern 2 (i + 3 * k + 5 * j + b.toNat) 1
  pad := []
  place := 1
  slotPath := [dg 77]
  slotSalt := _root_.Fmt.pattern 4

def y : (oneExternalString (2 ^ D.a) SgX).Str := fun p => (p.val, [41 + p.val.toUInt64, 42])

/-- the outer tree, made under g; c: the start of its leaves' salts -/
def xt (c : ByteArray) : ℕ → TreeK 256 L := fun _ =>
  (treeO (K := 2) 1 fun j =>
    ⟨if h : j < 2 ^ D.a then embE (y ⟨j, h⟩) else [],
      leafSalt c (_root_.Fmt.pattern 2 (9 + j))⟩).det g

def cms (c : ByteArray) : List (Dig 256) := [(xt c 0).root]

/-! ## The run -/

def run (a1 b2 c : ByteArray) : Res (Prf × Tr Q.loc.shape) :=
  (proveX (L := L) Tag.onl Q wq embS (fun z => z) some (cms c) () y (xt c) (σ b2)
    (coinsOf (chainsOf Ct D tF tJ t3).nJ (chainsOf Ct D tF tJ t3).n3 sB.logLeaves (bc a1))
    fun _ => 40).det g

def yes (c : ByteArray) (π : Prf) : Bool :=
  (verifyOneProtocol (L := L) (256 + 8 * 2) 256 Tag.onl Q wq embS (fun z => z) some embE 1 (cms c) ()
    π).det g

/-- stage 0: the prover returns, and the interactive verifier accepts -/
theorem returns : (match run r1 r2 cfg with
    | .ok z => Q.loc.accept () y z.2
    | _ => false) = true := by decide +kernel

/-- stage 0': the typed string is accepted -/
theorem typed_yes : (match run r1 r2 cfg with
    | .ok z => yes cfg z.1
    | _ => false) = true := by decide +kernel

/-! ## Through the bytes -/

def root : ByteArray := _root_.Fmt.pattern 32 17 5

/-- from bytes: the library's reader and maker with its judged rows, its typing, its
verifier: who refuses. The configuration's digest is the public one, whatever the prover's side has
done. -/
def stage (c b : ByteArray) : ℕ :=
  match LKF.FileInOf.madeFileOf magicProof "toy" cfg b with
  | .error _ => 0
  | .ok m =>
    if m.ok then
      match m.k.toBPrfAt Ct D tF tJ t3 sil rn m.cfg sB m.pF m.pJ m.p3 with
      | none => 2
      | some π => if yes c π then 4 else 3
    else 1

/-- the prover at (a1, b2, c); its string printed; the parsed file turned by f; its bytes by h. 5:
the prover has returned nothing -/
def through (a1 b2 c : ByteArray) (f : Carrier.File → Carrier.File) (h : ByteArray → ByteArray) :
    ℕ :=
  match run a1 b2 c with
  | .ok z => stage c (h (wrFile magicProof (f (carrierOf Ct D tF tJ t3 sil rn root z.1))))
  | _ => 5

def typed (a1 b2 c : ByteArray) : Bool :=
  match run a1 b2 c with
  | .ok z => yes c z.1
  | _ => false

/-- **1. FROM THE PROVER THROUGH THE BYTES TO THE LIBRARY's VERIFIER's YES.** -/
theorem yes_through : through r1 r2 cfg id id = 4 := by decide +kernel

/-- 2. one byte behind the file: the reader refuses -/
theorem no_more : through r1 r2 cfg id (fun b => b.push 0) = 0 := by decide +kernel

/-- 3. the strategy sends another run value in the joining round than the coins hold: the typed
string is accepted; at the printed one the verifier says no -/
theorem no_run2 : (typed r1 r1 cfg, through r1 r1 cfg id id) = (true, 3) := by decide +kernel

/-- 4. the outer tree's leaves are salted from run1, not from the configuration's digest -/
theorem no_cfg : (typed r1 r2 r1, through r1 r2 r1 id id) = (true, 3) := by decide +kernel

/-- 5. every word of every opened own column is turned -/
theorem no_column : through r1 r2 cfg (fun k => { k with
    trees := k.trees.map fun t => { t with
      rows := t.rows.map fun r => { r with column := r.column.map (· + 1) } } }) id = 3 := by
  decide +kernel

/-- 6. the first run value is 32 zero bytes: the typed string is accepted; a judged row says no -/
theorem no_zero : (typed (_root_.Fmt.zeroBytes 32) r2 cfg,
    through (_root_.Fmt.zeroBytes 32) r2 cfg id id) = (true, 1) := by decide +kernel

/-- 7. the seal bears the nonce 1: the typing lays nothing -/
theorem no_seal : through r1 r2 cfg (fun k => { k with
    rounds1 := k.rounds1.dropLast ++ [⟨[], 1⟩] }) id = 2 := by decide +kernel

/-- 8. one row more, at the leaf of tree 3 that is not read -/
theorem no_unread : through r1 r2 cfg (fun k => { k with
    trees := k.trees.map fun t =>
      if t.tree == 3 then
        { t with rows := match t.rows with
            | [r] => if r.leaf == 0 then [r, { r with leaf := 1 }] else [{ r with leaf := 0 }, r]
            | rs => rs }
      else t }) id = 3 := by decide +kernel

/-- 9. the place is 0, not 1 -/
theorem no_place : through r1 r2 cfg (fun k => { k with place := 0 }) id = 3 := by
  decide +kernel

/-- what is opened: the numbers of rows, tree by tree, and in the stored table: so that the yes is
not a yes at nothing -/
theorem opened : (match run r1 r2 cfg with
    | .ok z => ((carrierOf Ct D tF tJ t3 sil rn root z.1).trees.map fun t => t.rows.length,
        (carrierOf Ct D tF tJ t3 sil rn root z.1).stored.length)
    | _ => ([], 0)) = ([1, 1, 1, 1], 1) := by decide +kernel

end Johnson.Prover.Print.ToyRun

#print axioms Johnson.Prover.Print.ToyRun.returns
#print axioms Johnson.Prover.Print.ToyRun.typed_yes
#print axioms Johnson.Prover.Print.ToyRun.yes_through
#print axioms Johnson.Prover.Print.ToyRun.no_more
#print axioms Johnson.Prover.Print.ToyRun.no_run2
#print axioms Johnson.Prover.Print.ToyRun.no_cfg
#print axioms Johnson.Prover.Print.ToyRun.no_column
#print axioms Johnson.Prover.Print.ToyRun.no_zero
#print axioms Johnson.Prover.Print.ToyRun.no_seal
#print axioms Johnson.Prover.Print.ToyRun.no_unread
#print axioms Johnson.Prover.Print.ToyRun.no_place
#print axioms Johnson.Prover.Print.ToyRun.opened
