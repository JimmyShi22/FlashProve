-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Prover/Print/Canon.lean: WHAT THE READER OF BYTES ASKS OF A TYPED PROOF STRING OF A WHOLE
FILE, BESIDE Printable (OnBytes/Prover/Print/Carrier.lean). Two predicates. Definitions only.

Why. The typing of a parsed file tests no word against the prime, no nonce against 2^64 and no
salt's length against 64 bytes; the reader of the bytes (Carrier.read, OnBytes/Maker/Carrier.lean)
does. A typed string can come back under the typing and still have no bytes.

Main names.
  CanonI, CanonP   a round's plain part: the words of items f, e, answer are below the prime; a
    stretch's: so each round's, and its nonce is below 2^64.
  CanonO           an opening: the column's words are below the prime; the own salt has at most 64
    bytes; the path is shorter than 2^64.
  Canon π          on π alone: the answers, the copy's number, the three stretches' plain parts, all
    openings.
  SizesFit D s     public: the data's and the binding tree's numbers fit one word.

Limits. DEFINITIONS ONLY. They name no goal's form. Who pays Canon: the strategy (plain parts, own
columns), the outer tree's committer (stored columns, stored salts), the prover's cap on its
searches (nonces), the coins (own salts). Nothing on soundness or completeness.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Prover.Print.Carrier
import OnBytes.Prover.Print.Bytes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Prover.Print

open _root_.Run _root_.Run.PQ Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile (Opening)
open OnBytes.Maker OnBytes.Maker.Carrier
open TypedOracleCompiler.Compile.Batch (OneProtocolProof)
open TypedOracleCompiler.Joined (pls₁ pls₂ pls₃)

/-- A round's plain part: the words of its elements are below the prime. -/
def CanonI : (l : List _root_.Fmt.Item) → PlainOf l → Prop
  | [], _ => True
  | .root :: l, x => CanonI l x
  | .f :: l, (x : UInt64 × PlainOf l) => Carrier.okF x.1 ∧ CanonI l x.2
  | .word :: l, (x : UInt64 × PlainOf l) => CanonI l x.2
  | .e :: l, (x : _root_.Fmt.Ext × PlainOf l) => Carrier.okE x.1 ∧ CanonI l x.2
  | .answer :: l, (x : _root_.Fmt.Ext × PlainOf l) => Carrier.okE x.1 ∧ CanonI l x.2

/-- A stretch's plain parts. -/
def CanonP (C : CK) : (ds : List RDT) → Plains (uLT C ds) → Prop
  | [], _ => True
  | d :: ds, (pl, r) =>
    CanonI d.items (GPlain.old (W := ℕ) (b := d.entry.work) (P := PlainOf d.items) pl) ∧
      GPlain.nonce (W := ℕ) (b := d.entry.work) (P := PlainOf d.items) pl < 2 ^ 64 ∧
      CanonP C ds r

/-- An opening, its symbol as the list col of words. -/
def CanonO (col : List UInt64) (salt : Rom.Bits) (path : List (Dig 256)) : Prop :=
  (∀ w ∈ col, Carrier.okF w) ∧ col.length < 2 ^ 64 ∧ salt.length ≤ 256 + 8 * 64 ∧
    path.length < 2 ^ 64

section
variable (C : CK) (D : WholeD) (tF : FrontMsg (List OnBytes.E))
  (tJ : JoinMsg (List OnBytes.E) ByteArray) (t3 : ByteArray) {Xi : Type}
  (silent : Xi → FrontMsg (List OnBytes.E) → JoinMsg (List OnBytes.E) ByteArray → ByteArray → Bool)
  (run : Xi → View → View → View → Bool)

/-- **What the reader of bytes asks of a typed proof string.** -/
structure Canon (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch) : Prop where
  answers : ∀ e ∈ (pls₁ (wholeDesc C D tF tJ t3 silent run) π).1.answers, Carrier.okE e.triple
  count : (pls₁ (wholeDesc C D tF tJ t3 silent run) π).1.answers.length < 2 ^ 64
  copy : (pls₁ (wholeDesc C D tF tJ t3 silent run) π).1.copy < 2 ^ 64
  plain₁ : CanonP C D.ds₁ (pls₁ (wholeDesc C D tF tJ t3 silent run) π).2
  plain₂ : CanonP C D.ds₂ (pls₂ (wholeDesc C D tF tJ t3 silent run) π).2
  plain₃ : CanonP C D.ds₃ (pls₃ (wholeDesc C D tF tJ t3 silent run) π).2
  own₁ : ∀ q op, op₁ C D tF tJ t3 silent run π q = some op →
    CanonO (colOfSym C D.ds₁ q op.sym) op.salt op.path
  own₂ : ∀ q op, op₂ C D tF tJ t3 silent run π q = some op →
    CanonO (colOfSym C D.ds₂ q op.sym) op.salt op.path
  own₃ : ∀ q op, op₃ C D tF tJ t3 silent run π q = some op →
    CanonO (colOfSym C D.ds₃ q op.sym) op.salt op.path
  ext : ∀ p op, π.ext p = some op → CanonO op.sym.2 op.salt op.path

end

/-- Public: the data's and the binding tree's numbers fit one word. -/
structure SizesFit (D : WholeD) (s : Params.LinBindingShape) : Prop where
  rounds : D.ds₁.length + 1 < 2 ^ 64 ∧ D.ds₂.length < 2 ^ 64 ∧ D.ds₃.length < 2 ^ 64
  items : ∀ d ∈ D.ds₁ ++ (D.ds₂ ++ D.ds₃), d.items.length < 2 ^ 64
  trees : treesIn D < 2 ^ 64
  depths : ∀ d ∈ D.ds₁ ++ (D.ds₂ ++ D.ds₃), ∀ t ∈ d.trees, t.a < 64
  stored : D.a < 64
  binding : s.logLeaves < 64 ∧ s.saltBytes ≤ 64

end OnBytes.Prover.Print
