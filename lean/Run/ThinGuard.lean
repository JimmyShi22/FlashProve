-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ThinGuard.lean: a guard for Run/ThinDefs.lean. `verifyP`, the evaluable form of the compiled
verifier, is run by the evaluator at a round with 2^192 verifier messages, and ends. The honest
string is accepted, two altered ones are refused.

Definitions, three guards (`#guard`), and one statement (`Run.ThinGuard.Spec.vp_eq`) with its proof:
what the guards run is (Compile.Batch.verifyOneProtocol ..).det at this protocol.

Why it is here: that the evaluator builds no list of verifier messages at `verifyP` is a fact about
this compiler and about how that file is written (no parameter of type `Round`, `Shape`, `InteractiveOracleProof`,
`BatchInteractiveOracleProof`, `BatchProtocol`), no theorem. If a change of either brings the list back, this file does not
compile any more: it takes more memory than a compile was allowed (seen at
such runs: 12 GB reached after some twenty to fifty seconds, and stopped there). Whoever compiles it
without a cap on memory should know that.

The toy (this library's own; made for this guard alone). One local round: the prover sends 8 symbols
below 17 as an oracle (a tree of depth 3, salted leaves); the verifier message is a number below
2^192; the position read is that number modulo 8; the decision: the symbol there is 3. Digests of 16
bits; in the place of a hash a stub (a small arithmetic mixing): nothing here is about hashing. The
maker's side reckons with numbers and wraps them into digests last (a digest is a function of the
bit's number: a definition of that type would be computed anew at every bit).

Limits: this file says nothing on soundness, on the format's bytes or on speed. A guard leaves no
declaration: it is a test by the evaluator when the file is compiled.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.ThinTieProofs
import Run.TwinKit

set_option autoImplicit false

namespace Run.ThinGuard
open Iop Rom Compile Compile.Batch Run.Twin

abbrev E0 : ExtSpec := ⟨Unit, Empty, Unit, fun _ p => p.elim⟩
def we0 : WireE E0 := ⟨[], fun p => p.elim, fun p => p.elim, 0, fun _ => (), inferInstance, false⟩

abbrev NC : ℕ := 6277101735386680763835789423207666416102355444464034512895

@[reducible] def sA : RS :=
  ⟨Fin 8 → Fin 17, Fin 8, fun _ => Fin 17, fun o p => o p, Unit, Fin (NC + 1), fun _ => 0, (),
    fun _ => inferInstance, inferInstance⟩

def posOf (c : Fin (NC + 1)) : Fin 8 := ⟨c.val % 8, Nat.mod_lt _ (by decide)⟩

@[reducible] def P : PS Unit E0 where
  S := [sA]
  blinded := fun _ => true
  extReads := fun _ _ => ∅
  reads := fun _ ρ _ => {Sum.inl (posOf ρ.1)}
  accept := fun _ _ τ => decide (τ.1.1 (posOf τ.2.1) = 3)
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

abbrev LAM : ℕ := 16
def natOf (l : List Bool) : ℕ := l.foldl (fun a b => 2 * a + b.toNat) 0
def digOf (n : ℕ) : Dig LAM := fun i => (n >>> i.val) % 2 == 1
def mix (a b : ℕ) : ℕ := (a * 40503 + b * 30011 + 12345) % 65521

def wA : WireRB LAM 1 sA.up sA.lo where
  pt := ⟨inferInstanceAs (Fintype (Fin 8)), inferInstanceAs (DecidableEq (Fin 8)), fun f => f,
    fun _ _ => rfl, fun _ => rfl, fun _ => (0 : Fin 17)⟩
  depth0 := 0
  depthJ := 3
  has0 := false
  hasJ := true
  place := fun p => (p : Fin 8).val
  posAt0 := fun _ => none
  posAtJ := fun j => if h : j < 8 then some (⟨j, h⟩ : Fin 8) else none
  chal := fun u =>
    (⟨natOf (List.ofFn (u 0)) % (NC + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩ : Fin (NC + 1))

def wqA : ProtocolQueryLayout LAM 1 P.up := ⟨(wA, ()), we0, inferInstanceAs (DecidableEq (Fin 8 ⊕ Empty)), 1, 3⟩

def leafNat : LeafIn Lt → ℕ
  | ⟨some (.inr ⟨.test, ⟨.inl p, a⟩⟩), s⟩ => mix (mix (p : Fin 8).val (a : Fin 17).val) (natOf s)
  | ⟨_, s⟩ => natOf s

def fam : Fam (spec LAM 1 Lt)
  | .fb .test, q =>
    (fun _ => digOf (mix q.round (match q.rt with | some r => natOf (List.ofFn r) | none => 7)),
      digOf 1)
  | .fb _, _ => (fun _ _ => false, fun _ => false)
  | .fbw _ _, _ => (fun _ _ => false, fun _ => false)
  | .leaf, q => digOf (leafNat q)
  | .node, q => digOf (mix (natOf q.1) (natOf q.2))
  | .rleaf, _ => fun _ => false
  | .rnode, _ => fun _ => false
  | .g _, _ => fun _ => false
  | .ann, _ => ()
  | .other, _ => fun _ => false

def msg : Fin 8 → Fin 17 := fun _ => 3
def saltAt (j : ℕ) : Bits := (List.range 4).map fun i => (j >>> i) % 2 == 1
def rv (n : ℕ) : ℕ := natOf (List.ofFn (digOf n))
def leafN (j : Fin 8) : ℕ := leafNat ⟨some (.inr ⟨.test, ⟨.inl j, msg j⟩⟩), saltAt j.val⟩
def nodeN (a b : ℕ) : ℕ := mix (rv a) (rv b)
def lev0 : List ℕ := List.ofFn leafN
def upL : List ℕ → List ℕ
  | a :: b :: l => nodeN a b :: upL l
  | _ => []
def lev1 := upL lev0
def lev2 := upL lev1
def rootN : ℕ := (upL lev2).headD 0
def root : Dig LAM := digOf rootN
def pathOf (j : ℕ) : List (Dig LAM) :=
  [digOf (lev0.getD (j ^^^ 1) 0), digOf (lev1.getD ((j / 2) ^^^ 1) 0),
    digOf (lev2.getD ((j / 4) ^^^ 1) 0)]
def thePos : Fin 8 :=
  posOf (wA.chal (fam (.fb .test) ⟨0, .f1 [] none [true, false], some root, .inl (.inr ())⟩).1)

def prf (sym : Fin 17) (at_ : Fin 8) : OneProtocolProof LAM P.up :=
  ⟨[true, false], [root], ((), ()),
    fun p =>
      match p with
      | .inl q =>
        if q = at_ then some ⟨sym, saltAt (q : Fin 8).val, pathOf (q : Fin 8).val⟩ else none
      | .inr e => e.elim,
    fun _ => none, default, 0, []⟩

/-- The verifier `verifyP` at the toy. -/
def VP (π : OneProtocolProof LAM P.up) : Bool :=
  Run.Thin.verifyP (lam := LAM) (K := 1) (fun _ => Lt) fam id none 4 2 .test P wqA
    (fun p a => some (.inr ⟨.test, ⟨p, a⟩⟩)) id (fun _ => none) (fun _ => none) 0 [] () π

/-- States: what the guards run is the run of the library's compiled verifier of one slot at this
protocol. -/
def Spec.vp_eq : Prop :=
  ∀ π : OneProtocolProof LAM P.up, VP π =
    (verifyOneProtocol (lam := LAM) (K := 1) (L := Lt) 4 2 .test P.up wqA
      (fun p a => some (.inr ⟨.test, ⟨p, a⟩⟩)) id (fun _ => none) (fun _ => none) 0 [] () π).det fam

theorem vp_eq : Spec.vp_eq := fun π =>
  Run.Thin.thin_verify Unit Unit LAM 1 Lt fam Unit E0 4 2 .test P wqA
    (fun p a => some (.inr ⟨.test, ⟨p, a⟩⟩)) id (fun _ => none) (fun _ => none) 0 [] () π

#guard VP (prf 3 thePos)
#guard VP (prf 4 thePos) == false
#guard VP (prf 3 (thePos + 1)) == false

end Run.ThinGuard
