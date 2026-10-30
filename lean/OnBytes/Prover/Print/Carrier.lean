-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Prover/Print/Carrier.lean: FROM A TYPED PROOF STRING OF A WHOLE FILE (a key file or a proof
file: OneProtocolProof 256 (wholeDesc ...).batch) BACK TO A PARSED FILE (Carrier.File,
OnBytes/Maker/Carrier.lean): the way against File.toBPrfAt (OnBytes/Maker/CarrierTyping.lean).
Definitions only, each with code, and one predicate.

Why. The goals' verifier takes a form that holds parsed files as bytes, and lays typed proof strings
of them. An honest prover makes typed proof strings (OnBytes/Prover/Defs.lean). To hand them to that
verifier they have to be written down.

Called as they stand: colOfSym (OnBytes/Maker/TreesLaws.lean: a symbol as a list of words) · pls₁,
pls₂, pls₃ (OnBytes/TypedOracleCompiler/Joined/Verifier.lean: the three chains' plain parts).

Main names.
  itemsOf, roundsOf   a round's items, the roots laid in at the items "root"; a stretch's rounds.
  rowsOf, treesOf     the opened leaves of one tree, by rising leaf; one entry for every tree.
  storedOf            the opened leaves of the stored table.
  carrierOf root π    THE PARSED FILE. It reads nothing but root and π. run1 is π.salt as bytes;
    run2 and run3 are the joining round's and the seam's plain parts; a leaf's own salt is what
    stands behind the first 256 bits of its typed salt; the seal is laid bare.
  Printable cfg s π   ENOUGH FOR π TO COME BACK (toBPrfAt_carrierOf,
    OnBytes/Prover/Print/Whole.lean; that each clause is forced is not claimed): one clause a
    tie. A predicate on π and public data. It names no goal's form.
  RootsFit D          public: in each round as many items "root" as trees.

Limits. DEFINITIONS ONLY: nothing is proved here. That carrierOf's value comes back under
File.toBPrfAt: OnBytes/Prover/Print/Whole.lean; that the reader of bytes takes it:
OnBytes/Prover/Print/WholeWF.lean. rowsOf and storedOf walk all leaves of a tree: at the full size's
depths that is no program to run. root is an argument: a typed proof string does not hold the stored
table's root. Nothing on bytes (OnBytes/Prover/Print/Bytes.lean). Nothing on soundness or
completeness.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Maker.CarrierTyping
import OnBytes.Maker.TreesLaws
import OnBytes.Maker.SilentParts
import OnBytes.TypedOracleCompiler.Joined.Assemble

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Prover.Print

open _root_.Run _root_.Run.PQ Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile (Opening)
open OnBytes.Maker OnBytes.Maker.Carrier
open TypedOracleCompiler.Compile.Batch (OneProtocolProof)
open TypedOracleCompiler.Joined (opensL opensR pls₁ pls₂ pls₃)

/-! ## Rounds -/

/-- A round's items in their order: the plain part's, and at each item "root" the next of rts. -/
def itemsOf : (l : List _root_.Fmt.Item) → List ByteArray → PlainOf l → List _root_.Fmt.ItemValue
  | [], _, _ => []
  | .root :: l, rts, x => .root (rts.headD ByteArray.empty) :: itemsOf l rts.tail x
  | .f :: l, rts, (x : UInt64 × PlainOf l) => .f x.1 :: itemsOf l rts x.2
  | .word :: l, rts, (x : UInt64 × PlainOf l) => .word x.1 :: itemsOf l rts x.2
  | .e :: l, rts, (x : _root_.Fmt.Ext × PlainOf l) => .e x.1 :: itemsOf l rts x.2
  | .answer :: l, rts, (x : _root_.Fmt.Ext × PlainOf l) => .answer x.1 :: itemsOf l rts x.2

/-- A stretch's rounds: each takes as many of the roots as it has trees. In a round without proof of
work the nonce 0 is laid. -/
def roundsOf (C : CK) : (ds : List RDT) → List (Dig 256) → Plains (uLT C ds) →
    List Carrier.Round
  | [], _, _ => []
  | d :: ds, rts, (pl, r) =>
    (⟨itemsOf d.items ((rts.take d.trees.length).map digToBytes)
        (GPlain.old (W := ℕ) (b := d.entry.work) (P := PlainOf d.items) pl),
      GPlain.nonce (W := ℕ) (b := d.entry.work) (P := PlainOf d.items) pl⟩ : Carrier.Round) ::
      roundsOf C ds (rts.drop d.trees.length) r

/-! ## Opened leaves -/

/-- A leaf's own salt: what stands behind the first 256 bits of its typed salt. -/
def ownSalt (s : Rom.Bits) : ByteArray := bitsToBytes (s.drop 256)

/-- The opened leaves of the stretch's tree number n, by rising leaf. -/
def rowsOf (C : CK) (ds : List RDT)
    (opens : (p : OPos (uLT C ds)) → Option (Opening 256 (OSym (uLT C ds) p))) (n : ℕ) :
    List Carrier.Row :=
  match treeShT ds n with
  | none => []
  | some s => (List.range (2 ^ s.a)).filterMap fun x =>
      (posAtST C ds n x).bind fun p => (opens p).map fun op =>
        (⟨x, colOfSym C ds p op.sym, ownSalt op.salt, op.path.map digToBytes⟩ : Carrier.Row)

/-- One entry for every tree of the stretch. base: the number over the file of its first tree. -/
def treesOf (C : CK) (ds : List RDT) (chain base : ℕ)
    (opens : (p : OPos (uLT C ds)) → Option (Opening 256 (OSym (uLT C ds) p))) :
    List Carrier.TreeRows :=
  (List.range (ds.map (·.trees.length)).sum).map fun n => ⟨base + n, chain, rowsOf C ds opens n⟩

/-- The opened leaves of the stored table, by rising leaf. -/
def storedOf (a : ℕ) (ext : Fin (2 ^ a) → Option (Opening 256 SgX)) : List Carrier.Row :=
  (List.range (2 ^ a)).filterMap fun x =>
    if h : x < 2 ^ a then
      (ext ⟨x, h⟩).map fun op =>
        (⟨x, op.sym.2, ownSalt op.salt, op.path.map digToBytes⟩ : Carrier.Row)
    else none

/-! ## The parsed file -/

section
variable (C : CK) (D : WholeD) (tF : FrontMsg (List OnBytes.E))
  (tJ : JoinMsg (List OnBytes.E) ByteArray) (t3 : ByteArray) {Xi : Type}
  (silent : Xi → FrontMsg (List OnBytes.E) → JoinMsg (List OnBytes.E) ByteArray → ByteArray → Bool)
  (run : Xi → View → View → View → Bool)

/-- The openings at the three stretches' positions (a silent round has none). -/
def op₁ (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch) (q : OPos (uLT C D.ds₁)) :
    Option (Opening 256 (OSym (uLT C D.ds₁) q)) :=
  opensL (s := (chainsOf C D tF tJ t3).c₁)
    (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃) π.opens (.inr q)

def op₂ (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch) (q : OPos (uLT C D.ds₂)) :
    Option (Opening 256 (OSym (uLT C D.ds₂) q)) :=
  opensL (s := (chainsOf C D tF tJ t3).c₂) (u := (chainsOf C D tF tJ t3).c₃)
    (opensR (s := (chainsOf C D tF tJ t3).c₁)
      (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃) π.opens) (.inr q)

def op₃ (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch) (q : OPos (uLT C D.ds₃)) :
    Option (Opening 256 (OSym (uLT C D.ds₃) q)) :=
  opensR (s := (chainsOf C D tF tJ t3).c₂) (u := (chainsOf C D tF tJ t3).c₃)
    (opensR (s := (chainsOf C D tF tJ t3).c₁)
      (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃) π.opens) (.inr q)

/-- **The parsed file of a typed proof string.** root: the stored table's root, which the string
does not hold. -/
def carrierOf (root : ByteArray) (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch) :
    Carrier.File where
  root := root
  answers := (pls₁ (wholeDesc C D tF tJ t3 silent run) π).1.answers.map OnBytes.E.triple
  run1 := bitsToBytes π.salt
  copy := (pls₁ (wholeDesc C D tF tJ t3 silent run) π).1.copy
  rounds1 := roundsOf C D.ds₁ (π.roots.take D.t₁) (pls₁ (wholeDesc C D tF tJ t3 silent run) π).2 ++
    [(⟨[], 0⟩ : Carrier.Round)]
  run2 := (pls₂ (wholeDesc C D tF tJ t3 silent run) π).1.run
  rounds2 := roundsOf C D.ds₂ ((π.roots.drop D.t₁).take D.t₂)
    (pls₂ (wholeDesc C D tF tJ t3 silent run) π).2
  run3 := (pls₃ (wholeDesc C D tF tJ t3 silent run) π).1
  rounds3 := roundsOf C D.ds₃ ((π.roots.drop D.t₁).drop D.t₂)
    (pls₃ (wholeDesc C D tF tJ t3 silent run) π).2
  trees := treesOf C D.ds₁ 0 0 (op₁ C D tF tJ t3 silent run π) ++
    (treesOf C D.ds₂ 1 D.t₁ (op₂ C D tF tJ t3 silent run π) ++
      treesOf C D.ds₃ 2 (D.t₁ + D.t₂) (op₃ C D tF tJ t3 silent run π))
  stored := storedOf D.a π.ext
  bindRoot := digToBytes π.rtreq
  place := π.slot
  places := 2 ^ π.path.length
  slotSalt := bitsToBytes (π.rsalt.take (π.rsalt.length - 64))
  slotPath := π.path.map digToBytes

/-- A typed salt begins with the 256 bits of start, and what follows is whole bytes. -/
def SaltFrom (start : ByteArray) (s : Rom.Bits) : Prop :=
  s.take 256 = bytesToBits start ∧ whole (s.drop 256) = true

/-- **Enough for a typed proof string to come back.** cfg: the configuration's digest; s:
the binding tree's shape. -/
structure Printable (cfg : ByteArray) (s : Params.LinBindingShape)
    (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch) : Prop where
  /-- the first query's salt is 32 bytes -/
  salt : π.salt.length = 256
  /-- so are the two other run values -/
  run2 : (pls₂ (wholeDesc C D tF tJ t3 silent run) π).1.run.size = 32
  run3 : (pls₃ (wholeDesc C D tF tJ t3 silent run) π).1.size = 32
  /-- the joining round repeats the front's answers -/
  answers : (pls₂ (wholeDesc C D tF tJ t3 silent run) π).1.answers =
    (pls₁ (wholeDesc C D tF tJ t3 silent run) π).1.answers
  /-- as many roots as the data's trees -/
  roots : π.roots.length = treesIn D
  /-- a leaf's typed salt begins with the run value of the chain that sent its tree -/
  own₁ : ∀ q op, op₁ C D tF tJ t3 silent run π q = some op →
    SaltFrom (bitsToBytes π.salt) op.salt
  own₂ : ∀ q op, op₂ C D tF tJ t3 silent run π q = some op →
    SaltFrom (pls₂ (wholeDesc C D tF tJ t3 silent run) π).1.run op.salt
  own₃ : ∀ q op, op₃ C D tF tJ t3 silent run π q = some op →
    SaltFrom (pls₃ (wholeDesc C D tF tJ t3 silent run) π).1 op.salt
  /-- a stored leaf's begins with the configuration's digest, and its symbol names its place -/
  ext : ∀ p op, π.ext p = some op → SaltFrom cfg op.salt ∧ op.sym.1 = p.val
  /-- the binding tree -/
  slot : π.slot < 2 ^ s.logLeaves
  path : π.path.length = s.logLeaves
  rsalt : ∃ sl : ByteArray, sl.size = s.saltBytes ∧
    π.rsalt = rsOf (2 ^ s.logLeaves + π.slot) sl

end

/-- Public: in each round of the data as many items "root" as trees. -/
def RootsFit (D : WholeD) : Prop :=
  ∀ d ∈ D.ds₁ ++ (D.ds₂ ++ D.ds₃), d.items.countP (· == .root) = d.trees.length

end OnBytes.Prover.Print
