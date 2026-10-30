-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ThinBitsGuard.lean: a guard for Run/ThinBits.lean at the size of a real tree. `verifyPB`, the
evaluable form of the compiled verifier with digests as data in the trees' walks, is run by the
evaluator at one round with a tree of depth 15, 74 drawn positions, a pruned walk, digests of 256
bits and 2^192 verifier messages. The honest string is accepted, three altered ones are refused.

Definitions, five guards (`#guard`: the four runs, and before them that the place of the opening too
many is not read), and one statement (`Run.ThinBitsGuard.Spec.vb_eq`) with its proof: what the four
runs evaluate (`VB`) is (Compile.Batch.verifyOneProtocol ..).det at this protocol.

Why it is here: two facts about compiled Lean, no theorems, on which a run at real sizes rests: (1)
no list of all verifier messages is built (Run/ThinDefs.lean's principle); (2) no computed digest is
handed on as a function, so that a vertex of a tree is hashed once (Run/ThinBits.lean): with digests
as functions the same run at depth 10 did not come back. If a change brings either back, this file
does not compile any more: its compile call does not come back, or runs into a cap on memory or
time where one is set. Measured once: each of the four runs below one and a half seconds.

The toy (this library's own; made for this guard alone). One local round: the prover sends 2^15
symbols below 17 as an oracle (salted leaves); the verifier message is a number below 2^192, from
which 74 positions are reckoned; the decision: the symbol at each of them is 3. In the place of a
hash a stub (a small arithmetic mixing on numbers): nothing here is about hashing.
The altered strings: one opened symbol; one given digest; an opening too many, at a place that is
not read.

Limits: this file says nothing on soundness, on the format's bytes, on the cost of the real hash or
of a real protocol's decision. A guard leaves no declaration.

Terms: lean/GLOSSARY.md.
-/
import Run.ThinBitsTieProofs
import Run.TwinKit

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Run.ThinBitsGuard
open Iop Rom Compile Compile.Batch Run.Twin

abbrev E0 : ExtSpec := ⟨Unit, Empty, Unit, fun _ p => p.elim⟩
def we0 : WireE E0 := ⟨[], fun p => p.elim, fun p => p.elim, 0, fun _ => (), inferInstance, false⟩
abbrev DEP : ℕ := 15
abbrev NP : ℕ := 74
abbrev NN : ℕ := 2 ^ DEP
abbrev NC : ℕ := 2 ^ 192

@[reducible] def sA : RS :=
  ⟨Fin NN → Fin 17, Fin NN, fun _ => Fin 17, fun o p => o p, Unit, Fin NC, fun _ => 0, (),
    fun _ => inferInstance, ⟨⟨0, by decide⟩⟩⟩

def posL (c : Fin NC) : List (Fin NN) :=
  (List.range NP).map fun i =>
    ⟨(c.val / (i + 1) + 7919 * i) % NN, Nat.mod_lt _ (Nat.pos_of_ne_zero (by decide))⟩

@[reducible] def P : PS Unit E0 where
  S := [sA]
  blinded := fun _ => true
  extReads := fun _ _ => ∅
  reads := fun _ ρ _ => ((posL ρ.1).map fun x => (Sum.inl x : Fin NN ⊕ Empty)).toFinset
  accept := fun _ _ τ => (posL τ.2.1).all fun x => decide (τ.1.1 x = 3)
  ann := allLo [sA]

@[reducible] def pT : InteractiveOracleProof Unit (oneExternalString 0 Unit) :=
  { shape := up [sA], blinded := fun _ => true, extReads := fun _ _ => ∅,
    reads := fun _ _ _ => ∅, accept := fun _ _ _ => true }
@[reducible] def pL : InteractiveOracleProof Unit (twoExternalStrings 0 Unit) :=
  { shape := [], blinded := fun _ => false, extReads := fun _ _ => ∅,
    reads := fun _ _ _ => ∅, accept := fun _ _ _ => true }
@[reducible] def pB : InteractiveOracleProof Unit (oneExternalString 0 Unit) :=
  { shape := [], blinded := fun _ => false, extReads := fun _ _ => ∅,
    reads := fun _ _ _ => ∅, accept := fun _ _ _ => true }
@[reducible] def Lt : BatchProtocol Unit Unit where
  wordLength := 0
  Symbol := Unit
  EncodingRandomness := Unit
  encodeIndex := fun _ _ _ => ()
  decodeIndex := fun _ => some ()
  offline := pT
  link := pL
  maxBatchSize := 1
  onlineBatch := BatchInteractiveOracleProof.ofProto pB
  honestOfflineProver := { Coin := Unit, ext := fun _ _ => (), strat := fun _ _ _ => ((fun _ => 0, ()), fun _ => ()),
                           Bad := ∅, Hid := fun _ _ => ∅ }
  honestLinkProver := { Coin := Unit, ext := fun _ => (fun _ => (), fun _ => ()), strat := fun _ _ _ => (),
                        Bad := ∅, Hid := fun _ _ => ∅ }
  honestOnlineBatchProver := { Coin0 := Unit, Coin := Unit, ext := fun _ _ => (), strat0 := fun _ _ => (),
                               strat := fun _ _ _ _ => (), Bad := ∅, Hid := fun _ _ => ∅, stop0 := fun _ => false }
  early := id
  late := none

abbrev LAM : ℕ := 256
def natLE (l : List Bool) : ℕ := l.foldr (fun b a => 2 * a + b.toNat) 0
def digOf (n : ℕ) : Dig LAM := fun i => n.testBit i.val
def mix (a b : ℕ) : ℕ := (a * 1000003 + b * 998244353 + 12345) % 2305843009213693951

def wA : WireRB LAM 1 sA.up sA.lo where
  pt := ⟨inferInstanceAs (Fintype (Fin NN)), inferInstanceAs (DecidableEq (Fin NN)), fun f => f,
    fun _ _ => rfl, fun _ => rfl, fun _ => (0 : Fin 17)⟩
  depth0 := 0
  depthJ := DEP
  has0 := false
  hasJ := true
  place := fun p => (p : Fin NN).val
  posAt0 := fun _ => none
  posAtJ := fun j => if h : j < NN then some (⟨j, h⟩ : Fin NN) else none
  chal := fun u =>
    (⟨(natLE (List.ofFn (u 0)) * 6700417 + 1) % NC,
      Nat.mod_lt _ (Nat.pos_of_ne_zero (by decide))⟩ : Fin NC)
  prJ := true

def wqA : ProtocolQueryLayout LAM 1 P.up :=
  ⟨(wA, ()), we0, inferInstanceAs (DecidableEq (Fin NN ⊕ Empty)), NP, DEP⟩

def leafNat : LeafIn Lt → ℕ
  | ⟨some (.inr ⟨.test, ⟨.inl p, a⟩⟩), s⟩ => mix (mix (p : Fin NN).val (a : Fin 17).val) (natLE s)
  | ⟨_, s⟩ => natLE s

/-- The answers as numbers first (data), then wrapped. -/
def famN : (o : Batch.OracleName) → domOf LAM Lt o → ℕ
  | .fb .test, q => mix q.round (match q.rt with | some r => natLE (List.ofFn r) | none => 7)
  | .leaf, q => leafNat q
  | .node, q => mix (natLE q.1) (natLE q.2)
  | _, _ => 0
def decN : (o : Batch.OracleName) → ℕ → rngOf LAM 1 o
  | .fb _, n => (fun _ => digOf n, digOf (n + 1))
  | .fbw _ _, n => (fun _ => digOf n, digOf (n + 1))
  | .leaf, n => digOf n
  | .node, n => digOf n
  | .rleaf, n => digOf n
  | .rnode, n => digOf n
  | .g _, n => digOf n
  | .ann, _ => ()
  | .other, n => digOf n
def fam : Fam (spec LAM 1 Lt) := fun o q => decN o (famN o q)

def saltAt (j : ℕ) : Bits := (List.range 8).map fun i => j.testBit i
def leafN (j : ℕ) : ℕ := mix (mix j 3) (natLE (saltAt j))
def upA (a : Array ℕ) : Array ℕ :=
  Array.ofFn (n := a.size / 2) fun i => mix (a.getD (2 * i.val) 0) (a.getD (2 * i.val + 1) 0)
def levels : Array (Array ℕ) :=
  (List.range DEP).foldl (fun acc _ => acc.push (upA (acc.back?.getD #[])))
    #[Array.ofFn (n := NN) fun i => leafN i.val]
def rootN : ℕ := ((levels.back?.getD #[]).getD 0 0)
def pathOf (j : ℕ) : List (Dig LAM) :=
  (List.range DEP).map fun l => digOf (((levels.getD l #[]).getD ((j >>> l) ^^^ 1) 0))
def theC : Fin NC :=
  wA.chal (fam (.fb .test) ⟨0, .f1 [] none [true, false], some (digOf rootN), .inl (.inr ())⟩).1
def tbl (bad : ℕ) : List (ℕ × Opening LAM (Fin 17)) :=
  (posL theC).map fun x => (x.val, ⟨if x.val = bad then 4 else 3, saltAt x.val, pathOf x.val⟩)

def prf (bad : ℕ) : OneProtocolProof LAM P.up :=
  let t := tbl bad
  ⟨[true, false], [digOf rootN], ((), ()),
    fun p => match p with | .inl q => t.lookup (q : Fin NN).val | .inr e => e.elim,
    fun _ => none, default, 0, []⟩

def VP (π : OneProtocolProof LAM P.up) : Bool :=
  Run.Thin.verifyP (lam := LAM) (K := 1) (fun _ => Lt) fam id none 8 2 .test P wqA
    (fun p a => some (.inr ⟨.test, ⟨p, a⟩⟩)) id (fun _ => none) (fun _ => none) 0 [] () π

def first : ℕ := ((posL theC).headD ⟨0, by decide⟩).val
/-- A given digest altered: the first opening's path, at its lowest place. -/
def prfPath : OneProtocolProof LAM P.up :=
  let t := (tbl NN).map fun e =>
    if e.1 = first then
      (e.1, (⟨e.2.sym, e.2.salt, digOf 12345 :: e.2.path.tail⟩ : Opening LAM (Fin 17)))
    else e
  ⟨[true, false], [digOf rootN], ((), ()),
    fun p => match p with | .inl q => t.lookup (q : Fin NN).val | .inr e => e.elim,
    fun _ => none, default, 0, []⟩
/-- An opening too many: at a place that is not read. -/
def prfMore : OneProtocolProof LAM P.up :=
  let t := (NN - 1, (⟨3, saltAt (NN - 1), pathOf (NN - 1)⟩ : Opening LAM (Fin 17))) :: tbl NN
  ⟨[true, false], [digOf rootN], ((), ()),
    fun p => match p with | .inl q => t.lookup (q : Fin NN).val | .inr e => e.elim,
    fun _ => none, default, 0, []⟩
/-- The verifier `verifyPB` at the toy. -/
def VB (π : OneProtocolProof LAM P.up) : Bool :=
  Run.Thin.verifyPB (lam := LAM) (K := 1) (fun _ => Lt) fam id none 8 2 .test P wqA
    (fun p a => some (.inr ⟨.test, ⟨p, a⟩⟩)) id (fun _ => none) (fun _ => none) 0 [] () π

/-- States: what the four runs evaluate (`VB`) is the run of the library's compiled verifier of one
slot at this protocol. -/
def Spec.vb_eq : Prop :=
  ∀ π : OneProtocolProof LAM P.up, VB π =
    (verifyOneProtocol (lam := LAM) (K := 1) (L := Lt) 8 2 .test P.up wqA
      (fun p a => some (.inr ⟨.test, ⟨p, a⟩⟩)) id (fun _ => none) (fun _ => none) 0 [] () π).det fam

theorem vb_eq : Spec.vb_eq := fun π =>
  Run.Thin.thin_bits Unit Unit LAM 1 Lt fam Unit E0 8 2 .test P wqA
    (fun p a => some (.inr ⟨.test, ⟨p, a⟩⟩)) id (fun _ => none) (fun _ => none) 0 [] () π

#guard ((posL theC).map (·.val)).contains (NN - 1) == false
#guard VB (prf NN)
#guard VB (prf first) == false
#guard VB prfPath == false
#guard VB prfMore == false

end Run.ThinBitsGuard
