-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Prover/Print/ToyBack.lean: a test: at a small whole file's data a written typed proof string
is printed (carrierOf, OnBytes/Prover/Print/Carrier.lean) and the library's typing
(File.toBPrfAt, OnBytes/Maker/CarrierTyping.lean) lays it again: every field comes back. Strings
that break a clause of Printable do not come back.

Why. It holds carrierOf's text against the parser's before anything is proved of it.

The data: chain 1: one round with a bit of work, the items word, root, f, root, two trees (depth 1,
width 1; depth 0, width 2); chain 2: one round, the items root, e, one tree (depth 1, width 2);
chain 3: one round, the items answer, root, one tree (depth 1, width 1). A stored table of depth 1.
A binding tree of depth 1.

Main names.
  D, π₀       the data; the written string: four openings in own trees of all three chains, one in
    the stored table, the place 1 in the binding tree.
  view        a string's fields as lists of numbers, bits and bytes, at ALL positions.
  back        printed and laid again, π₀'s view comes back.
  bent_*      one field turned against a clause of Printable: the view does not come back.
  back_bytes  THROUGH THE BYTES: written by wrFile (OnBytes/Prover/Print/Bytes.lean), read by the
    library's Carrier.read, laid by its typing, the three silent rounds' plain parts made of the
    parsed file as the goals' parser's caller makes them: π₀'s view comes back.
  bent_more, bent_last, big_typed, big_bytes   a byte behind; a byte turned; a column's word = p,
    which the typing takes and the reader of bytes refuses.

Limits: a test, by evaluation in Lean's kernel, at one written string. No prover, no oracle, no
verifier: the reader of bytes and the typing alone.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Prover.Print.Carrier
import OnBytes.Prover.Print.Bytes
import Run.PlanPull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Prover.Print.ToyBack

open _root_.Run _root_.Run.PQ Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile (Opening)
open OnBytes.Maker OnBytes.Maker.Carrier
open TypedOracleCompiler.Compile.Batch (OneProtocolProof)
open TypedOracleCompiler.Joined (opensApp pls₁ pls₂ pls₃)
open OnBytes.Prover.Print

/-! ## The data -/

def rdA : RDT :=
  { entry := { name := "a", work := 1 }, kind := .elems, items := [.word, .root, .f, .root],
    trees := [⟨1, 1, false, 0⟩, ⟨0, 2, false, 1⟩], opens := [], stored := [] }
def rdB : RDT :=
  { entry := { name := "b" }, kind := .elems, items := [.root, .e],
    trees := [⟨1, 2, false, 2⟩], opens := [], stored := [] }
def rdC : RDT :=
  { entry := { name := "c" }, kind := .elems, items := [.answer, .root],
    trees := [⟨1, 1, false, 3⟩], opens := [], stored := [] }
def D : WholeD := ⟨1, [rdA], [rdB], [rdC], id, id, id⟩

abbrev C : CK := ckP .two
def tF : FrontMsg (List OnBytes.E) := ⟨[], 0⟩
def tJ : JoinMsg (List OnBytes.E) ByteArray := ⟨[], ByteArray.empty⟩
def t3 : ByteArray := ByteArray.empty
def sil : Unit → FrontMsg (List OnBytes.E) → JoinMsg (List OnBytes.E) ByteArray → ByteArray →
    Bool := fun _ _ _ _ => true
def rn : Unit → View → View → View → Bool := fun _ _ _ _ => true

abbrev Prf : Type := OneProtocolProof 256 (wholeDesc C D tF tJ t3 sil rn).batch

def r1 : ByteArray := _root_.Fmt.pattern 32
def r2 : ByteArray := _root_.Fmt.pattern 32 5 1
def r3 : ByteArray := _root_.Fmt.pattern 32 11 2
def cfg : ByteArray := _root_.Fmt.pattern 32 13 4
def dg (n : ℕ) : Dig 256 := bytesToDig (_root_.Fmt.pattern 32 n 1)
def sB : Params.LinBindingShape := ⟨1, 4⟩
def ans : List OnBytes.E := [OnBytes.E.ofTriple (1, 2, 3)]

/-! ## The written string -/

/-- the openings of chain 1's stretch, a leaf's salt beginning with the bytes a -/
def oA (a : ByteArray) : (p : OPos (uLT C D.ds₁)) → Option (Opening 256 (OSym (uLT C D.ds₁) p))
  | .inl (.inl x) =>
    if x.val = 1 then some ⟨fun _ => (21 : UInt64), leafSalt a (_root_.Fmt.pattern 2), [dg 4]⟩
    else none
  | .inl (.inr (.inl _)) =>
    some ⟨fun i => (30 + i.val.toUInt64 : UInt64), leafSalt a (_root_.Fmt.pattern 2 3), []⟩
  | .inl (.inr (.inr e)) => nomatch e
  | .inr e => nomatch e

def oB : (p : OPos (uLT C D.ds₂)) → Option (Opening 256 (OSym (uLT C D.ds₂) p))
  | .inl (.inl x) =>
    if x.val = 0 then
      some ⟨fun i => (50 + i.val.toUInt64 : UInt64), leafSalt r2 (_root_.Fmt.pattern 2 4), [dg 8]⟩
    else none
  | .inl (.inr e) => nomatch e
  | .inr e => nomatch e

/-- chain 3's, a leaf's salt beginning with the bytes a -/
def oC (a : ByteArray) : (p : OPos (uLT C D.ds₃)) → Option (Opening 256 (OSym (uLT C D.ds₃) p))
  | .inl (.inl x) =>
    if x.val = 1 then some ⟨fun _ => (60 : UInt64), leafSalt a (_root_.Fmt.pattern 2 6), [dg 9]⟩
    else none
  | .inl (.inr e) => nomatch e
  | .inr e => nomatch e

/-- The string, with four letters to bend: the start of chain 1's leaves' salts, the stored leaf's,
the number in the stored symbol, the index behind the slot's value. -/
def mk (a c : ByteArray) (pl ix : ℕ) : Prf where
  salt := bytesToBits r1
  roots := [dg 1, dg 2, dg 3, dg 10]
  plains := Plains.app (s := (chainsOf C D tF tJ t3).c₁)
    (t := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃)
    ((⟨ans, 6⟩ : FrontMsg (List OnBytes.E)), ((((7 : UInt64), ((9 : UInt64), ())), (3 : ℕ)), ()))
    (Plains.app (s := (chainsOf C D tF tJ t3).c₂) (t := (chainsOf C D tF tJ t3).c₃)
      ((⟨ans, r2⟩ : JoinMsg (List OnBytes.E) ByteArray),
        (((((1 : UInt64), (2 : UInt64), (3 : UInt64)), ())), ()))
      (r3, (((((4 : UInt64), (5 : UInt64), (6 : UInt64)), ())), ())))
  opens := opensApp (s := (chainsOf C D tF tJ t3).c₁)
    (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃) (behind tF (oA a))
    (opensApp (s := (chainsOf C D tF tJ t3).c₂) (u := (chainsOf C D tF tJ t3).c₃)
      (behind tJ oB) (behind t3 (oC r3)))
  ext := fun p =>
    if p.val = 0 then some ⟨(pl, [41, 42]), leafSalt c (_root_.Fmt.pattern 2 9), [dg 5]⟩ else none
  rtreq := dg 6
  slot := 1
  path := [dg 7]
  rsalt := rsOf ix (_root_.Fmt.pattern 4)

def π₀ : Prf := mk r1 cfg 0 3

/-! ## A string's fields as plain data -/

def bitsOf (d : Dig 256) : List Bool := List.ofFn d

def viewO (ds : List RDT)
    (opens : (p : OPos (uLT C ds)) → Option (Opening 256 (OSym (uLT C ds) p))) :
    List (ℕ × ℕ × Option (List UInt64 × List Bool × List (List Bool))) :=
  (List.range (ds.map (·.trees.length)).sum).flatMap fun n =>
    match treeShT ds n with
    | none => []
    | some s => (List.range (2 ^ s.a)).map fun x =>
        (n, x, (posAtST C ds n x).bind fun p => (opens p).map fun op =>
          (colOfSym C ds p op.sym, op.salt, op.path.map bitsOf))

def viewR (l : List Carrier.Round) : List (List _root_.Fmt.ItemValue × ℕ) :=
  l.map fun r => (r.items, r.nonce)

abbrev T3 : Type := UInt64 × UInt64 × UInt64
abbrev VO : Type := List (ℕ × ℕ × Option (List UInt64 × List Bool × List (List Bool)))
abbrev VR : Type := List (List _root_.Fmt.ItemValue × ℕ)
abbrev VT : Type :=
  (List Bool × List (List Bool) × List Bool × ℕ × List (List Bool) × List Bool) ×
    (List T3 × ℕ × List T3 × ByteArray × ByteArray) × (VR × VR × VR) × (VO × VO × VO) ×
    List (Option ((ℕ × List UInt64) × List Bool × List (List Bool)))

def view (π : Prf) : VT :=
  ((π.salt, π.roots.map bitsOf, bitsOf π.rtreq, π.slot, π.path.map bitsOf, π.rsalt),
    ((pls₁ (wholeDesc C D tF tJ t3 sil rn) π).1.answers.map OnBytes.E.triple,
      (pls₁ (wholeDesc C D tF tJ t3 sil rn) π).1.copy,
      (pls₂ (wholeDesc C D tF tJ t3 sil rn) π).1.answers.map OnBytes.E.triple,
      (pls₂ (wholeDesc C D tF tJ t3 sil rn) π).1.run,
      (pls₃ (wholeDesc C D tF tJ t3 sil rn) π).1),
    (viewR (roundsOf C D.ds₁ [] (pls₁ (wholeDesc C D tF tJ t3 sil rn) π).2),
      viewR (roundsOf C D.ds₂ [] (pls₂ (wholeDesc C D tF tJ t3 sil rn) π).2),
      viewR (roundsOf C D.ds₃ [] (pls₃ (wholeDesc C D tF tJ t3 sil rn) π).2)),
    (viewO D.ds₁ (op₁ C D tF tJ t3 sil rn π), viewO D.ds₂ (op₂ C D tF tJ t3 sil rn π),
      viewO D.ds₃ (op₃ C D tF tJ t3 sil rn π)),
    (List.finRange (2 ^ D.a)).map fun p => (π.ext p).map fun op =>
      ((op.sym : SgX), op.salt, op.path.map bitsOf))

/-- printed, then laid again by the library's typing -/
def again (π : Prf) : Option Prf :=
  (carrierOf C D tF tJ t3 sil rn (_root_.Fmt.pattern 32 17 5) π).toBPrfAt C D tF tJ t3 sil rn cfg sB
    (pls₁ (wholeDesc C D tF tJ t3 sil rn) π).1 (pls₂ (wholeDesc C D tF tJ t3 sil rn) π).1
    (pls₃ (wholeDesc C D tF tJ t3 sil rn) π).1

instance : DecidableEq (List UInt64 × List Bool × List (List Bool)) := inferInstance
instance : DecidableEq (Option (List UInt64 × List Bool × List (List Bool))) := inferInstance
instance : DecidableEq VO := inferInstance
instance : DecidableEq (VO × VO × VO) := inferInstance

/-- do two views agree, part by part -/
def same (u v : VT) : Bool :=
  decide (u.1 = v.1) && decide (u.2.1 = v.2.1) && decide (u.2.2.1 = v.2.2.1) &&
    decide (u.2.2.2.1 = v.2.2.2.1) && decide (u.2.2.2.2 = v.2.2.2.2)

def comesBack (π : Prf) : Bool :=
  match again π with
  | none => false
  | some π' => same (view π') (view π)

/-! ## The test -/

/-- **Printed and laid again, every field of π₀ comes back.** -/
theorem back : comesBack π₀ = true := by decide +kernel

/-- chain 1's leaves' salts begin with chain 2's run value (clause own₁) -/
theorem bent_own : comesBack (mk r2 cfg 0 3) = false := by decide +kernel
/-- chain 3's leaf's salt begins with chain 1's run value (clause own₃) -/
theorem bent_own3 :
    comesBack { π₀ with
      opens := opensApp (s := (chainsOf C D tF tJ t3).c₁)
        (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃) (behind tF (oA r1))
        (opensApp (s := (chainsOf C D tF tJ t3).c₂) (u := (chainsOf C D tF tJ t3).c₃)
          (behind tJ oB) (behind t3 (oC r1))) } = false := by decide +kernel
/-- the stored leaf's salt does not begin with the configuration's digest (clause ext) -/
theorem bent_cfg : comesBack (mk r1 r1 0 3) = false := by decide +kernel
/-- the stored symbol names another place (clause ext) -/
theorem bent_place : comesBack (mk r1 cfg 1 3) = false := by decide +kernel
/-- the index behind the slot's value is not 2 ^ depth + slot (clause rsalt) -/
theorem bent_index : comesBack (mk r1 cfg 0 2) = false := by decide +kernel
/-- a root too few (clause roots) -/
theorem bent_roots : comesBack { π₀ with roots := [dg 1, dg 2, dg 3] } = false := by
  decide +kernel
/-- the first query's salt has 255 bits (clause salt) -/
theorem bent_salt : comesBack { π₀ with salt := (bytesToBits r1).take 255 } = false := by
  decide +kernel
/-- no sibling in the binding tree (clause path) -/
theorem bent_path : comesBack { π₀ with path := [] } = false := by decide +kernel
/-- a place beyond the binding tree (clause slot) -/
theorem bent_slot :
    comesBack { π₀ with slot := 2, rsalt := rsOf 4 (_root_.Fmt.pattern 4) } = false := by
  decide +kernel

/-! ## Through the bytes -/

/-- the parsed file's bytes -/
def bytesOf (π : Prf) : ByteArray :=
  wrFile magicProof (carrierOf C D tF tJ t3 sil rn (_root_.Fmt.pattern 32 17 5) π)

/-- from bytes: the library's reader, then its typing; the plain parts of the three silent
rounds are made of the parsed file as the caller of the goals' parser makes them
(Johnson/Top/Fire/Code/FileInOf.lean: ofCarrier) -/
def ofBytes (b : ByteArray) : Option Prf :=
  match OnBytes.Maker.Carrier.read magicProof b with
  | .error _ => none
  | .ok k => k.toBPrfAt C D tF tJ t3 sil rn cfg sB
      (frontOf (k.answers.map OnBytes.E.ofTriple) k.copy)
      ⟨k.answers.map OnBytes.E.ofTriple, k.run2⟩ k.run3

def throughBytes (f : ByteArray → ByteArray) (π : Prf) : Bool :=
  match ofBytes (f (bytesOf π)) with
  | none => false
  | some π' => same (view π') (view π)

/-- **Written as bytes, read by the library's reader, laid by its typing: π₀ comes back.** -/
theorem back_bytes : throughBytes id π₀ = true := by decide +kernel

/-- a byte behind the file: the reader refuses -/
theorem bent_more : throughBytes (fun b => b.push 0) π₀ = false := by decide +kernel
/-- the last byte (of the binding tree's sibling) turned: another string -/
theorem bent_last : throughBytes (fun b => b.set! (b.size - 1) 0) π₀ = false := by decide +kernel
/-- a word that is not below p in the clear: the typing takes it, the reader of bytes does not -/
def πBig : Prf :=
  { π₀ with
    ext := fun p =>
      if p.val = 0 then
        some ⟨(0, [41, 0xFFFFFFFF00000001]), leafSalt cfg (_root_.Fmt.pattern 2 9), [dg 5]⟩
      else none }
theorem big_typed : comesBack πBig = true := by decide +kernel
theorem big_bytes : throughBytes id πBig = false := by decide +kernel

end OnBytes.Prover.Print.ToyBack

#print axioms OnBytes.Prover.Print.ToyBack.back
#print axioms OnBytes.Prover.Print.ToyBack.bent_own
#print axioms OnBytes.Prover.Print.ToyBack.bent_own3
#print axioms OnBytes.Prover.Print.ToyBack.bent_cfg
#print axioms OnBytes.Prover.Print.ToyBack.bent_place
#print axioms OnBytes.Prover.Print.ToyBack.bent_index
#print axioms OnBytes.Prover.Print.ToyBack.bent_roots
#print axioms OnBytes.Prover.Print.ToyBack.bent_salt
#print axioms OnBytes.Prover.Print.ToyBack.bent_path
#print axioms OnBytes.Prover.Print.ToyBack.bent_slot
#print axioms OnBytes.Prover.Print.ToyBack.back_bytes
#print axioms OnBytes.Prover.Print.ToyBack.bent_more
#print axioms OnBytes.Prover.Print.ToyBack.bent_last
#print axioms OnBytes.Prover.Print.ToyBack.big_typed
#print axioms OnBytes.Prover.Print.ToyBack.big_bytes
