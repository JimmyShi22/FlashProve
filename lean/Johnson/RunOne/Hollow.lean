-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Hollow.lean: carriers of the typed oracles that have code, so that the compiled
verifier of one slot can be run. Each holds what that verifier reads of a carrier, and fixed values
in every other field.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

The compiled verifier verifyOneProtocol (OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean) has a carrier L : BatchProtocolWithLeafBody I X
as a letter. By reading, it reads of L: in its types, the type L.Bd of a leaf's body and, under the
tag t, the shape and the annotation of the protocol of that tag (shapeOf L t, annOf L t:
OnBytes/TypedOracleCompiler/Compile/Batch/Oracles.lean); as values, L.early and L.late alone (recomputeChain; lateInstancePart). It
reads none of wordLength, Symbol, EncodingRandomness, encodeIndex, decodeIndex, maxBatchSize, honestOfflineProver, honestLinkProver, honestOnlineBatchProver, nor the decisions of L's three protocols: the
protocol that it runs is its own argument Q.

Main definitions. noProto E: the protocol without a round, which says no. hollow Q z early late: the
carrier whose protocol under the tag onl is Q, with bodies that are lists of bits; Test and Link are
noProto; the honest sides send each round's fixed message (OnBytes/Flat/Silent.lean).
hollowT Q z: the like with Q's rounds and annotation under the tag test, for a key file.
hollowX X, hollowTX X: hollow and hollowT with the type of instances a letter X.
hollowTB X QT QB: QT's rounds under the tag test and QB's under the tag onl, both at once.
verifyAt, verifyAtT, verifyAtX, verifyAtTX, verifyAtTB: verifyOneProtocol at these carriers; chainAt and its
four sisters: its first half, the chain alone.
Main theorems, each by rfl. At every carrier, under its tag, the shape and the annotation are the
given protocol's (…_shape, …_ann): so the map embP of verifyOneProtocol can be the identity. At hollow and
hollowT a body is a list of bits (…_body). At hollowX and hollowTB the fields early and late are the
arguments. At hollowX and hollowTX a plain part under the other two tags has no value.

Limits. NONE OF THESE IS THE CARRIER OF ANY THEOREM ON SOUNDNESS. The types of typed queries
(LeafIn L, FbIn lam L t, JoiningRoundQuery lam L t) have L itself as their index, so the verifier at one of these
carriers and the verifier at another carrier with the same five things are two terms of two types:
no equation between them is stated or proved here. What a run at one of these carriers shows is
which queries the chain asks and what the decision says at these arguments. Nothing on soundness.
The program does not import this file.


-/
import OnBytes.Flat.Silent
import OnBytes.TypedOracleCompiler.Compile.Batch.Verifier

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne

open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Iop hiding BatchProtocol

/-- The protocol without a round, which says no. -/
def noProto (E : ExtSpec) : InteractiveOracleProof Unit E where
  shape := []
  blinded := fun _ => false
  extReads := fun _ _ => ∅
  reads := fun _ _ _ => ∅
  accept := fun _ _ _ => false

/-- The carrier with Q under the tag onl. z: a symbol, for the fields that nothing reads. -/
def hollow {Y : Type} {n : ℕ} {Sg : Type} (Q : BatchInteractiveOracleProof Y (oneExternalString n Sg)) (z : Sg)
    (early : Y → Y) (late : Option ℕ) : BatchProtocolWithLeafBody Unit Y where
  wordLength := n
  Symbol := Sg
  EncodingRandomness := Unit
  encodeIndex := fun _ _ _ => z
  decodeIndex := fun _ => none
  offline := noProto _
  link := noProto _
  maxBatchSize := 1
  onlineBatch := Q
  honestOfflineProver :=
    { Coin := Unit
      ext := fun _ _ => z
      strat := fun _ _ _ => OnBytes.Flat.silent _ ()
      Bad := ∅
      Hid := fun _ _ => ∅ }
  honestLinkProver :=
    { Coin := Unit
      ext := fun _ => (fun _ => z, fun _ => z)
      strat := fun _ _ _ => OnBytes.Flat.silent _ ()
      Bad := ∅
      Hid := fun _ _ => ∅ }
  honestOnlineBatchProver :=
    { Coin0 := Unit
      Coin := Unit
      ext := fun _ _ => z
      strat0 := fun _ _ => OnBytes.Flat.silent0 _ _
      strat := fun _ _ _ _ => OnBytes.Flat.silentJ _ _
      Bad := ∅
      Hid := fun _ _ => ∅
      stop0 := fun _ => false }
  early := early
  late := late
  Bd := List Bool
  annT := PUnit.unit
  annL := PUnit.unit

section
variable {Y : Type} {n : ℕ} {Sg : Type} (Q : BatchInteractiveOracleProof Y (oneExternalString n Sg)) (z : Sg) (early : Y → Y)
  (late : Option ℕ)

theorem hollow_shape : shapeOf (hollow Q z early late) .onl = Q.loc.shape := rfl

theorem hollow_ann : annOf (hollow Q z early late) .onl = Q.ann := rfl

theorem hollow_body : Body (hollow Q z early late) = List Bool := rfl

/-- The compiled verifier of one slot at the hollow carrier, plain parts written as they are. -/
def verifyAt {K : ℕ} (sMT sFS : ℕ) (wq : ProtocolQueryLayout 256 K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → List Bool) (xin : Y → Option Y)
    (embE : Sg → List Bool) (depthReq : ℕ) (cms : List (Dig 256)) (x : Y) (π : OneProtocolProof 256 Q) :
    TypedOracleComputation 256 K (hollow Q z early late) Bool :=
  verifyOneProtocol sMT sFS .onl Q wq embS id xin embE depthReq cms x π

/-- Its first half: the chain alone. -/
def chainAt {K : ℕ} (wq : ProtocolQueryLayout 256 K Q) (xin : Y → Option Y) (cms : List (Dig 256)) (x : Y)
    (π : OneProtocolProof 256 Q) :
    TypedOracleComputation 256 K (hollow Q z early late) (Option (Rho Q.loc.shape × RootsOfChain 256 Q.loc.shape × Phase 256)) :=
  recomputeChainOfProof .onl Q wq id xin cms x π

end

/-! ## The same under the tag test: for a key file -/

/-- The carrier with Q's rounds and annotation under the tag test. Its own Test has Q's shape and
says no; nothing reads its decisions. The instance's type is Unit: a key file's verifier writes no
instance into a query. -/
def hollowT {Y : Type} {n : ℕ} {Sg : Type} (Q : BatchInteractiveOracleProof Y (oneExternalString n Sg)) (z : Sg) :
    BatchProtocolWithLeafBody Unit Unit where
  wordLength := n
  Symbol := Sg
  EncodingRandomness := Unit
  encodeIndex := fun _ _ _ => z
  decodeIndex := fun _ => none
  offline :=
    { shape := Q.loc.shape
      blinded := fun _ => false
      extReads := fun _ _ => ∅
      reads := fun _ _ _ => ∅
      accept := fun _ _ _ => false }
  link := noProto _
  maxBatchSize := 1
  onlineBatch := ⟨noProto _, PUnit.unit⟩
  honestOfflineProver :=
    { Coin := Unit
      ext := fun _ _ => z
      strat := fun _ _ _ => OnBytes.Flat.silent _ ()
      Bad := ∅
      Hid := fun _ _ => ∅ }
  honestLinkProver :=
    { Coin := Unit
      ext := fun _ => (fun _ => z, fun _ => z)
      strat := fun _ _ _ => OnBytes.Flat.silent _ ()
      Bad := ∅
      Hid := fun _ _ => ∅ }
  honestOnlineBatchProver :=
    { Coin0 := Unit
      Coin := Unit
      ext := fun _ _ => z
      strat0 := fun _ _ => OnBytes.Flat.silent0 _ _
      strat := fun _ _ _ _ => OnBytes.Flat.silentJ _ _
      Bad := ∅
      Hid := fun _ _ => ∅
      stop0 := fun _ => false }
  early := id
  late := none
  Bd := List Bool
  annT := Q.ann
  annL := PUnit.unit

section
variable {Y : Type} {n : ℕ} {Sg : Type} (Q : BatchInteractiveOracleProof Y (oneExternalString n Sg)) (z : Sg)

theorem hollowT_shape : shapeOf (hollowT Q z) .test = Q.loc.shape := rfl

theorem hollowT_ann : annOf (hollowT Q z) .test = Q.ann := rfl

theorem hollowT_body : Body (hollowT Q z) = List Bool := rfl

/-- The compiled verifier of one slot at that carrier, under the tag test, without an instance. -/
def verifyAtT {K : ℕ} (sMT sFS : ℕ) (wq : ProtocolQueryLayout 256 K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → List Bool) (embE : Sg → List Bool)
    (depthReq : ℕ) (cms : List (Dig 256)) (x : Y) (π : OneProtocolProof 256 Q) :
    TypedOracleComputation 256 K (hollowT Q z) Bool :=
  verifyOneProtocol sMT sFS .test Q wq embS id (fun _ => none) embE depthReq cms x π

/-- Its first half: the chain alone. -/
def chainAtT {K : ℕ} (wq : ProtocolQueryLayout 256 K Q) (cms : List (Dig 256)) (x : Y) (π : OneProtocolProof 256 Q) :
    TypedOracleComputation 256 K (hollowT Q z) (Option (Rho Q.loc.shape × RootsOfChain 256 Q.loc.shape × Phase 256)) :=
  recomputeChainOfProof .test Q wq id (fun _ => none) cms x π

end

/-! ## With the type of instances a letter

The typed queries hold an instance (Head lam X), so an equation between the verifier at two carriers
wants one type X of instances at both. In hollow it is Q's own type Y, in hollowT it is Unit. Here
it is a letter, and the carrier's own protocol under the tag has Q's rounds and says no. -/

/-- The protocol without a round, at any type of instances. -/
def noProtoX (X : Type) (E : ExtSpec) : InteractiveOracleProof X E where
  shape := []
  blinded := fun _ => false
  extReads := fun _ _ => ∅
  reads := fun _ _ _ => ∅
  accept := fun _ _ _ => false

/-- Q's rounds, at any type of instances; it says no. -/
def shellX (X : Type) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) : InteractiveOracleProof X E where
  shape := Q.loc.shape
  blinded := fun _ => false
  extReads := fun _ _ => ∅
  reads := fun _ _ _ => ∅
  accept := fun _ _ _ => false

/-- hollow with the type of instances a letter. -/
def hollowX (X : Type) {Y : Type} {n : ℕ} {Sg : Type} (Q : BatchInteractiveOracleProof Y (oneExternalString n Sg)) (z : Sg)
    (early : X → X) (late : Option ℕ) : BatchProtocolWithLeafBody Unit X where
  wordLength := n
  Symbol := Sg
  EncodingRandomness := Unit
  encodeIndex := fun _ _ _ => z
  decodeIndex := fun _ => none
  offline := noProto _
  link := noProto _
  maxBatchSize := 1
  onlineBatch := ⟨shellX X Q, Q.ann⟩
  honestOfflineProver :=
    { Coin := Unit
      ext := fun _ _ => z
      strat := fun _ _ _ => OnBytes.Flat.silent _ ()
      Bad := ∅
      Hid := fun _ _ => ∅ }
  honestLinkProver :=
    { Coin := Unit
      ext := fun _ => (fun _ => z, fun _ => z)
      strat := fun _ _ _ => OnBytes.Flat.silent _ ()
      Bad := ∅
      Hid := fun _ _ => ∅ }
  honestOnlineBatchProver :=
    { Coin0 := Unit
      Coin := Unit
      ext := fun _ _ => z
      strat0 := fun _ _ => OnBytes.Flat.silent0 _ _
      strat := fun _ _ _ _ => OnBytes.Flat.silentJ _ _
      Bad := ∅
      Hid := fun _ _ => ∅
      stop0 := fun _ => false }
  early := early
  late := late
  Bd := List Bool
  annT := PUnit.unit
  annL := PUnit.unit

/-- hollowT with the type of instances a letter. -/
def hollowTX (X : Type) {Y : Type} {n : ℕ} {Sg : Type} (Q : BatchInteractiveOracleProof Y (oneExternalString n Sg)) (z : Sg) :
    BatchProtocolWithLeafBody Unit X where
  wordLength := n
  Symbol := Sg
  EncodingRandomness := Unit
  encodeIndex := fun _ _ _ => z
  decodeIndex := fun _ => none
  offline := shellX Unit Q
  link := noProto _
  maxBatchSize := 1
  onlineBatch := ⟨noProtoX X _, PUnit.unit⟩
  honestOfflineProver :=
    { Coin := Unit
      ext := fun _ _ => z
      strat := fun _ _ _ => OnBytes.Flat.silent _ ()
      Bad := ∅
      Hid := fun _ _ => ∅ }
  honestLinkProver :=
    { Coin := Unit
      ext := fun _ => (fun _ => z, fun _ => z)
      strat := fun _ _ _ => OnBytes.Flat.silent _ ()
      Bad := ∅
      Hid := fun _ _ => ∅ }
  honestOnlineBatchProver :=
    { Coin0 := Unit
      Coin := Unit
      ext := fun _ _ => z
      strat0 := fun _ _ => OnBytes.Flat.silent0 _ _
      strat := fun _ _ _ _ => OnBytes.Flat.silentJ _ _
      Bad := ∅
      Hid := fun _ _ => ∅
      stop0 := fun _ => false }
  early := id
  late := none
  Bd := List Bool
  annT := Q.ann
  annL := PUnit.unit

/-- Both at once: QT's rounds under the tag test, QB's under the tag onl. So a query under the tag
test can be written beside a run under the tag onl: the seeds' two queries of a proof file's arm. -/
def hollowTB (X : Type) {YT YB : Type} {n : ℕ} {Sg : Type} (QT : BatchInteractiveOracleProof YT (oneExternalString n Sg))
    (QB : BatchInteractiveOracleProof YB (oneExternalString n Sg)) (z : Sg) (early : X → X) (late : Option ℕ) : BatchProtocolWithLeafBody Unit X where
  wordLength := n
  Symbol := Sg
  EncodingRandomness := Unit
  encodeIndex := fun _ _ _ => z
  decodeIndex := fun _ => none
  offline := shellX Unit QT
  link := noProto _
  maxBatchSize := 1
  onlineBatch := ⟨shellX X QB, QB.ann⟩
  honestOfflineProver :=
    { Coin := Unit
      ext := fun _ _ => z
      strat := fun _ _ _ => OnBytes.Flat.silent _ ()
      Bad := ∅
      Hid := fun _ _ => ∅ }
  honestLinkProver :=
    { Coin := Unit
      ext := fun _ => (fun _ => z, fun _ => z)
      strat := fun _ _ _ => OnBytes.Flat.silent _ ()
      Bad := ∅
      Hid := fun _ _ => ∅ }
  honestOnlineBatchProver :=
    { Coin0 := Unit
      Coin := Unit
      ext := fun _ _ => z
      strat0 := fun _ _ => OnBytes.Flat.silent0 _ _
      strat := fun _ _ _ _ => OnBytes.Flat.silentJ _ _
      Bad := ∅
      Hid := fun _ _ => ∅
      stop0 := fun _ => false }
  early := early
  late := late
  Bd := List Bool
  annT := QT.ann
  annL := PUnit.unit

section
variable (X : Type) {YT YB : Type} {n : ℕ} {Sg : Type} (QT : BatchInteractiveOracleProof YT (oneExternalString n Sg))
  (QB : BatchInteractiveOracleProof YB (oneExternalString n Sg)) (z : Sg) (early : X → X) (late : Option ℕ)

theorem hollowTB_shapeT : shapeOf (hollowTB X QT QB z early late) .test = QT.loc.shape := rfl

theorem hollowTB_annT : annOf (hollowTB X QT QB z early late) .test = QT.ann := rfl

theorem hollowTB_shapeB : shapeOf (hollowTB X QT QB z early late) .onl = QB.loc.shape := rfl

theorem hollowTB_annB : annOf (hollowTB X QT QB z early late) .onl = QB.ann := rfl

theorem hollowTB_early : (hollowTB X QT QB z early late).early = early := rfl

theorem hollowTB_late : (hollowTB X QT QB z early late).late = late := rfl

/-- The compiled verifier under the tag onl at hollowTB. -/
def verifyAtTB {K : ℕ} (sMT sFS : ℕ) (wq : ProtocolQueryLayout 256 K QB)
    (embS : (p : OPos QB.loc.shape) → OSym QB.loc.shape p → List Bool) (xin : YB → Option X)
    (embE : Sg → List Bool) (depthReq : ℕ) (cms : List (Dig 256)) (x : YB) (π : OneProtocolProof 256 QB) :
    TypedOracleComputation 256 K (hollowTB X QT QB z early late) Bool :=
  verifyOneProtocol sMT sFS .onl QB wq embS id xin embE depthReq cms x π

/-- Its first half: the chain alone. -/
def chainAtTB {K : ℕ} (wq : ProtocolQueryLayout 256 K QB) (xin : YB → Option X) (cms : List (Dig 256)) (x : YB)
    (π : OneProtocolProof 256 QB) :
    TypedOracleComputation 256 K (hollowTB X QT QB z early late)
      (Option (Rho QB.loc.shape × RootsOfChain 256 QB.loc.shape × Phase 256)) :=
  recomputeChainOfProof .onl QB wq id xin cms x π

end

section
variable (X : Type) {Y : Type} {n : ℕ} {Sg : Type} (Q : BatchInteractiveOracleProof Y (oneExternalString n Sg)) (z : Sg)
  (early : X → X) (late : Option ℕ)

theorem hollowX_shape : shapeOf (hollowX X Q z early late) .onl = Q.loc.shape := rfl

theorem hollowX_ann : annOf (hollowX X Q z early late) .onl = Q.ann := rfl

theorem hollowX_early : (hollowX X Q z early late).early = early := rfl

theorem hollowX_late : (hollowX X Q z early late).late = late := rfl

theorem hollowTX_shape : shapeOf (hollowTX X Q z) .test = Q.loc.shape := rfl

theorem hollowTX_ann : annOf (hollowTX X Q z) .test = Q.ann := rfl

/-- Under the other two tags a plain part of hollowX's protocols has no value. -/
theorem hollowX_test : PlainPart (shapeOf (hollowX X Q z early late) .test)
    (annOf (hollowX X Q z early late) .test) = Empty := rfl

theorem hollowX_link : PlainPart (shapeOf (hollowX X Q z early late) .link)
    (annOf (hollowX X Q z early late) .link) = Empty := rfl

theorem hollowTX_onl : PlainPart (shapeOf (hollowTX X Q z) .onl) (annOf (hollowTX X Q z) .onl) = Empty :=
  rfl

theorem hollowTX_link :
    PlainPart (shapeOf (hollowTX X Q z) .link) (annOf (hollowTX X Q z) .link) = Empty := rfl

/-- The compiled verifier at hollowX. -/
def verifyAtX {K : ℕ} (sMT sFS : ℕ) (wq : ProtocolQueryLayout 256 K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → List Bool) (xin : Y → Option X)
    (embE : Sg → List Bool) (depthReq : ℕ) (cms : List (Dig 256)) (x : Y) (π : OneProtocolProof 256 Q) :
    TypedOracleComputation 256 K (hollowX X Q z early late) Bool :=
  verifyOneProtocol sMT sFS .onl Q wq embS id xin embE depthReq cms x π

/-- The compiled verifier at hollowTX. -/
def verifyAtTX {K : ℕ} (sMT sFS : ℕ) (wq : ProtocolQueryLayout 256 K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → List Bool) (embE : Sg → List Bool)
    (depthReq : ℕ) (cms : List (Dig 256)) (x : Y) (π : OneProtocolProof 256 Q) :
    TypedOracleComputation 256 K (hollowTX X Q z) Bool :=
  verifyOneProtocol sMT sFS .test Q wq embS id (fun _ => none) embE depthReq cms x π

/-- The chain alone at hollowX. -/
def chainAtX {K : ℕ} (wq : ProtocolQueryLayout 256 K Q) (xin : Y → Option X) (cms : List (Dig 256)) (x : Y)
    (π : OneProtocolProof 256 Q) :
    TypedOracleComputation 256 K (hollowX X Q z early late)
      (Option (Rho Q.loc.shape × RootsOfChain 256 Q.loc.shape × Phase 256)) :=
  recomputeChainOfProof .onl Q wq id xin cms x π

/-- The chain alone at hollowTX. -/
def chainAtTX {K : ℕ} (wq : ProtocolQueryLayout 256 K Q) (cms : List (Dig 256)) (x : Y) (π : OneProtocolProof 256 Q) :
    TypedOracleComputation 256 K (hollowTX X Q z) (Option (Rho Q.loc.shape × RootsOfChain 256 Q.loc.shape × Phase 256)) :=
  recomputeChainOfProof .test Q wq id (fun _ => none) cms x π

end

end Johnson.RunOne
