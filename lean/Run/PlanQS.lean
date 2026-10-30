-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQS.lean: from a description of a proof's rounds to the compiled verifier, in a form that can
be evaluated; what is evaluated is the run of `Compile.Batch.verifyOneProtocol`.

A proof file of the programs (the C++ implementation that comes with this Lean code) is a chain of
rounds: in each the prover sends a message, a hash of all that went before gives the verifier's
message, and Merkle openings may follow. The format page (docs/format/FORMAT.md, which comes with
the programs)
fixes the bytes. This file takes a description S of such a chain (Fmt/Rules8.lean: `Spec`) and a
decision function dec on what has been read, and makes from them a protocol of the library, its
wiring (the data that say how deep the trees are, where a position stands among a tree's leaves, and
how blocks of a hash answer give a verifier message), and a verifier that Lean's evaluator can run
on a real file.

Why it is written as it is. In the library a round carries, as data, the list of all its verifier
messages. Any function that has a parameter, explicit or implicit, that is a round, a shape, a
protocol or an interface may make the evaluator build that list, which is hopeless already for one
drawn field element. The principle (Run/ThinDefs.lean): the functions written here for the path of
evaluation have no such parameter (seven functions from which the interface and its wiring are made
have one: `dfltSS`, `dfltLS`, `dummyH`, `dummyB`, `Lo3`, `Lb`, `Wb`; so have, by Lean's signatures,
some projections and constructors of the library's records). In the place of such parameters are
skeletons of rounds (Run/TwinDefs.lean: `RS`, `PS`: the list behind a function that is never called)
and the interface behind a function of `Unit`. Here Run/PlanQTypes.lean, PlanQWire.lean,
PlanQPage.lean, PlanQRun.lean are written again in that way.
The parameters are
   C (a choice of challenge types: for each round the type of the verifier's message, and the map
     from such a message to the format's record of what was drawn; `CK` in the code),
   the rounds' data ds,
   the description S,
   the decision dec.
Every recursion but those of the placeholder honest sides (`dfltSS`, `dfltLS`) is on ds; elsewhere
shapes stand in types alone. The proof of work (nonce, test bits) is written into rounds and wiring
from the start.

The two interfaces (`BatchProtocol`, Iop/Batch.lean). The run functions are stated at `LbS`, whose Batch is
the protocol (the tag "onl"; the statement () in the first query). `LtS`, whose Test is the same
protocol, is kept, because later files state or prove facts about it as a term (Run/PlanQSLaws.lean,
Run/PlanPullFace.lean, Run/PlanPullJoin.lean [not in this library], Run/M1Door.lean). Run/BatchS.lean's `batch_same` says
what carries over.

1. What the file contains.
   `s0 C`               The round in front. It sends nothing, and its verifier message is C's at an
                        entry that draws nothing (Run/PlanQTypes.lean: `e0`; `C.Ch e0 .nothing`; one
                        value: C's field `front`). With challenges as hash blocks the verifier
                        message's type is `Fin b → Dig 256`, with b the number of blocks of that
                        entry (b = 0 is a theorem, Run/PlanPull.lean: `b_front`, not a definition):
                        the form that the library's own construction gives a round.
   `roundS C d`, `SL`, `SOf`, `uL`
                        The rounds as skeletons: the plain part with the nonce, the verifier message
                        with the test bits, where the round has work.
   `drawnSL`, `passSL`, `rhoSL`, `rvSL`, `posAtS`, `colAtS`, `viewSL`
                        As in Run/PlanQTypes.lean. `passSL`: all test bits are 0.
   `PSof C ds dec`      The skeleton of the protocol: no statement, no external oracle. It accepts
                        if all tests of work pass and dec accepts the view. Annotation: local rounds
                        (Run/TwinKit.lean: `allLo`).
   `wireS`, `wiresSL`, `wqS`
                        The wiring, as literals: what the library's step for a round with a test
                        makes of Run/PlanQWire.lean's wiring (round by round: Run/PlanQSLaws.lean:
                        `wireS_eq`; the round in front has `wire0S`).
   `dfltSS`, `dfltLS`, `dummyH`, `dummyB`, `Lo3`, `Lb`, `LbS C ds dec`, `Wb`
                        Placeholder honest sides; the interface without an index made of three given
                        protocols; the interface whose Batch is the protocol; its wiring from a
                        wiring of the slot.
   `embPL`, `msgSL`, `nonceSL`, `leafSL`, `PDS`, `plainsSL`, `placeSL`, `symSL`, `TYS`
                        How typed queries are spelled as the format's hash calls, and how what a
                        reader has read is typed. `leafSL`'s first component is `Fmt.leafPlace` (the
                        tree's number) (the number of the column's words) (the number of the salt's
                        words): what stands above the leaves' number in the label's first word.
   `VPC S C K chal dec cm π`, `runStrictC`, `runLaxC S C K chal dec file`
                        The verifier and the two run functions, for every choice of challenge types
                        C, number K of blocks and samplers chal.
   `VP`, `runStrictS`, `runLaxS`
                        The same with challenges as sampled values (a round's verifier message is
                        what the format draws, field elements and positions among them;
                        Run/PlanDrawsQ.lean: `ck`; K := the greatest number of blocks over the
                        rounds), by definition.
   `VP S dec cm π : Bool` is the evaluable form of the compiled verifier. The walks in `VP`'s trees
   are made on digests as data, and the set of positions read is split round by round
   (Run/ThinBits.lean, Run/ThinReads.lean: `verifyPR`). The format's hash is behind the typed
   oracles, in the form that keeps the hash's state behind what all blocks of one answer share
   (Run/CodingFnKeep.lean: `famK`, proved equal to Run/CodingFnThin.lean's `famP` at the format's
   oracle).
   `runStrictS`, `runLaxS S dec file : Who` run a file
     behind the strict reader (this library's rendering of the format page's verifier up to its
     decision)
     and behind the lenient reader (which only cuts the file into its parts and leaves work and
       openings to the verifier; to cut the file, the lenient reader recomputes the hash chain, and
       it refuses some files (what it still asks the hash, what it refuses and what it does not
       test: part 1 of the head of Run/ParseLax.lean)),
     on the readers' fast forms (Fmt/Rules8Fast.lean: `wholeChainF`; Run/ParseLaxFast.lean:
       `parseLaxFP`).

2. What is checked when the file compiles. Only the types and the proofs. Tests: Run/PlanQSToy.lean
   and later files.

3. Theorems, each in a general form and with challenges as sampled values.
   `vpc_eq`, `vp_eq`    `VP S dec cm π` = (`Compile.Batch.verifyOneProtocol` .. (PSof ..).up (wqS ..) .. [cm]
                        () π).det (famP ..), for every S, dec, cm, π. By Run/ThinReads.lean's
                        theorem `thin_reads`, which has no hypothesis beside whatever its arguments
                        hold as proofs.
   `runC_readers`, `run_readers`
                        The two run functions are those on the strict reader and on the lenient
                        reader at the format's hash.

4. What is not claimed, or stands elsewhere.
   That `PSof`'s protocol is `QU` of Run/PlanQPage.lean. That the `verifyOneProtocol` of `vp_eq` is
   `Compile.Batch.vBS` at `LbS`: the two annotations are equal by induction, and by definition only
   at a closed description; this second equation is stated toy by toy (Run/M1RunTie.lean and its
   companion files).
   No law of a wiring. No statement on soundness.
   With challenges as sampled values, the wiring applies the sampler itself. At a round that draws a
   field element its verifier messages are then not exactly uniform, so that wiring does not obey
   the library's laws, and no hypothesis of a compilation theorem is met at it.
   The words "no hypothesis … is met at it" speak of the hypothesis that the wiring obeys the laws.
   In `Spec.bcsSoundBatchG` (Compile/Batch/SpecSoundG.lean) that is `W.OKG` (`QueryLayout.OKG`; the clause
   at stake: `chal_unif` of `WireRB.OKG`; both Iop/BatchWire.lean). Its five other hypotheses do not
   name the wiring. For every choice of challenge types they are had at the interfaces `LtS` and
   `LbS` of this file, the soundness among them at the relation "everything" (`All`,
   Run/M1Door.lean), and empty:
       `psof_local` (Run/PlanQSLaws.lean) at both;
       at `LtS` `lts_sound` and the fields `localL`, `localB`, `cohB` in the proof of `metOf`, whose
         terms do not use its hypothesis `W.OKG` (Run/M1Door.lean);
       at `LbS` `lb_sound` and the fields `localT`, `localL`, `cohB` in the proof of `metB`, whose
         terms do not use its two hypotheses (Run/BatchDoorProofs.lean).
   The choice that meets the laws is challenges as hash blocks (Run/PlanPull.lean: `ckP`; the laws:
   `planPull_okg`, under the hypotheses of its statement), where a round's verifier message is its
   256-bit hash blocks themselves. That the two choices give one verdict on a file: for the two run
   functions behind the lenient reader it is a theorem of a later file (Run/PageIsRunProofs.lean:
   `run_two`: `ok S` and `smallB S file` give `runLaxS S dec file = runLaxSP S dec file`); for the
   run functions behind the strict reader it is only tested.
   That the evaluator builds no list of verifier messages is a fact about this compiler.
   Run/PlanQSToy.lean's tests run these functions at a round with about 2^192 verifier messages for
   each drawn element; that they come back shows it there. How often a vertex is hashed is not
   tested.
   Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Sources. A leaf's label holds its shape by the format page (R2.1, R7.3); this file has not been
held against the page as it ships, and may differ from it, for instance at R7.3.


Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PlanQRun
import Run.TwinKit
import Run.ThinBitsTieProofs
import Run.ThinReads
import Run.CodingFnThin
import Run.ParseThin
import Run.CodingFnKeep
import Run.ParseLaxFast
import Fmt.Rules8Fast

set_option autoImplicit false

namespace Run.PQ
open Iop Rom Compile Compile.Batch
open Run.Twin (RS PS)

/-! ## Rounds as skeletons -/

@[reducible] def roundS (C : CK) (d : RD) : RS where
  Orc := Fin (posN d.tree) → Fin (colW d.tree) → UInt64
  Pos := Fin (posN d.tree)
  Sym := fun _ => Fin (colW d.tree) → UInt64
  rd := fun o p => o p
  Plain := GPlain ℕ d.entry.work (PlainOf d.items)
  Chal := GChal d.entry.work (C.Ch d.entry d.kind)
  dOrc := fun _ _ => 0
  dPlain := GPlain.mk d.entry.work (PlainOf.dflt d.items) default
  finT := fun _ => inferInstance
  ne := inferInstance

/-- The round in front: nothing is sent; its verifier message is C's at an entry that draws nothing
(one value, by C's field `front`; nothing reads it). -/
@[reducible] def s0 (C : CK) : RS where
  Orc := Unit
  Pos := Empty
  Sym := fun _ => Unit
  rd := fun _ p => p.elim
  Plain := Unit
  Chal := C.Ch e0 .nothing
  dOrc := ()
  dPlain := ()
  finT := fun _ => inferInstance
  ne := inferInstance

@[reducible] def SL (C : CK) : List RD → List RS
  | [] => []
  | d :: ds => roundS C d :: SL C ds

abbrev SOf (C : CK) (ds : List RD) : List RS := s0 C :: SL C ds

/-- the shape of the rounds after the round in front: in types alone -/
abbrev uL (C : CK) (ds : List RD) : Shape := Twin.up (SL C ds)

/-! ## The view -/

def drawnSL (C : CK) : (ds : List RD) → Rho (uL C ds) → List _root_.Fmt.Drawn
  | [], _ => []
  | d :: ds, (c, ρ) => C.dr d.entry d.kind (GChal.old (b := d.entry.work) c) :: drawnSL C ds ρ

def passSL (C : CK) : (ds : List RD) → Rho (uL C ds) → Bool
  | [], _ => true
  | d :: ds, (c, ρ) => GChal.pass (b := d.entry.work) c && passSL C ds ρ

def rhoSL (C : CK) : (ds : List RD) → Iop.Tr (uL C ds) → Rho (uL C ds)
  | [], _ => ()
  | _ :: ds, (_, c, τ) => (c, rhoSL C ds τ)

def rvSL (C : CK) : (ds : List RD) → Iop.Tr (uL C ds) → List RV
  | [], _ => []
  | d :: ds, (m, c, τ) =>
    ⟨PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2),
        C.dr d.entry d.kind (GChal.old (b := d.entry.work) c)⟩ :: rvSL C ds τ

def posAtS (C : CK) : (ds : List RD) → Nat → Nat → Option (OPos (uL C ds))
  | [], _, _ => none
  | d :: ds, n, x =>
    if d.tree.isSome then
      if n = 0 then (if h : x < posN d.tree then some (.inl ⟨x, h⟩) else none)
      else (posAtS C ds (n - 1) x).map .inr
    else (posAtS C ds n x).map .inr

def colAtS (C : CK) : (ds : List RD) → Iop.Tr (uL C ds) → Nat → Nat → Option (List UInt64)
  | [], _, _, _ => none
  | d :: ds, (m, _, τ), n, x =>
    if d.tree.isSome then
      if n = 0 then (if h : x < posN d.tree then some (List.ofFn (m.1 ⟨x, h⟩)) else none)
      else colAtS C ds τ (n - 1) x
    else colAtS C ds τ n x

def viewSL (C : CK) (ds : List RD) (τ : Iop.Tr (uL C ds)) : View where
  rounds := rvSL C ds τ
  opened := (wanted ds (drawnSL C ds (rhoSL C ds τ))).filterMap fun nx =>
    (colAtS C ds τ nx.1 nx.2).map fun c => (nx.1, nx.2, c)

/-! ## The protocol's skeleton -/

instance decSL (C : CK) : (ds : List RD) → DecidableEq (OPos (uL C ds))
  | [] => inferInstanceAs (DecidableEq Empty)
  | d :: ds => by
      haveI := decSL C ds
      exact inferInstanceAs (DecidableEq (Fin (posN d.tree) ⊕ OPos (uL C ds)))

instance decOS (C : CK) (ds : List RD) : DecidableEq (OPos (Twin.up (SOf C ds))) :=
  inferInstanceAs (DecidableEq (Empty ⊕ OPos (uL C ds)))

/-- The skeleton of the protocol. -/
@[reducible] def PSof (C : CK) (ds : List RD) (dec : View → Bool) : PS Unit E0 where
  S := SOf C ds
  blinded := fun _ => true
  extReads := fun _ _ => ∅
  reads := fun _ ρ _ =>
    (((wanted ds (drawnSL C ds ρ.2)).filterMap fun nx =>
      (posAtS C ds nx.1 nx.2).map fun p => (Sum.inr p : OPos (Twin.up (SOf C ds))))).toFinset
  accept := fun _ _ τ => passSL C ds (rhoSL C ds τ.2.2) && dec (viewSL C ds τ.2.2)
  ann := Twin.allLo (SOf C ds)

/-! ## The wirings -/

/-- the wiring of a round, with its test -/
def wireS (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (d : RD) :
    WireRB 256 (K + 1) (roundS C d).up (roundS C d).lo where
  pt := ⟨inferInstanceAs (Fintype (Fin (posN d.tree))),
    inferInstanceAs (DecidableEq (Fin (posN d.tree))), fun f => f, fun _ _ => rfl,
    fun _ => rfl, fun _ _ => 0⟩
  depth0 := 0
  depthJ := depthOf d.tree
  has0 := false
  hasJ := d.tree.isSome
  place := fun p => p.val
  posAt0 := fun _ => none
  posAtJ := fun j => if h : j < posN d.tree then some ⟨j, h⟩ else none
  chal := chalGrind (chal d.entry d.kind) d.entry.work
  prJ := true
  gr0 := none
  grJ := grOf Dn (C.Ch d.entry d.kind) (PlainOf d.items) d.entry.work

def wire0S (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) :
    WireRB 256 (K + 1) (s0 C).up (s0 C).lo where
  pt := ⟨inferInstanceAs (Fintype Empty), inferInstanceAs (DecidableEq Empty), fun _ => (),
    fun _ p => p.elim, fun _ => rfl, fun p => p.elim⟩
  depth0 := 0
  depthJ := 0
  has0 := false
  hasJ := false
  place := fun p => p.elim
  posAt0 := fun _ => none
  posAtJ := fun _ => none
  chal := chalGrind (chal e0 .nothing) 0

def wiresSL (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) :
    (ds : List RD) → RoundsQueryLayout 256 (K + 1) (uL C ds) (Twin.allLo (SL C ds))
  | [] => ()
  | d :: ds => (wireS C K chal d, wiresSL C K chal ds)

def wqS (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (ds : List RD) (dec : View → Bool) :
    ProtocolQueryLayout 256 (K + 1) (PSof C ds dec).up :=
  ⟨(wire0S C K chal, wiresSL C K chal ds), we0, decOS C ds, nOpen ds, maxDepth ds⟩

/-! ## The interface whose Test is the protocol -/

/-- The interface whose Test is the protocol itself. -/
@[reducible] def LtS (C : CK) (ds : List RD) (dec : View → Bool) : BatchProtocol Unit Unit where
  wordLength := 0
  Symbol := Unit
  EncodingRandomness := Unit
  encodeIndex := fun _ _ _ => ()
  decodeIndex := fun _ => some ()
  offline := (PSof C ds dec).up.loc
  link := pL
  maxBatchSize := 1
  onlineBatch := BatchInteractiveOracleProof.ofProto pB
  honestOfflineProver := { Coin := Unit, ext := fun _ _ => (), strat := fun _ _ _ => dfltS () _,
                           Bad := ∅, Hid := fun _ _ => ∅ }
  honestLinkProver := { Coin := Unit, ext := fun _ => (fun _ => (), fun _ => ()), strat := fun _ _ _ => (),
                        Bad := ∅, Hid := fun _ _ => ∅ }
  honestOnlineBatchProver := { Coin0 := Unit, Coin := Unit, ext := fun _ _ => (), strat0 := fun _ _ => (),
                               strat := fun _ _ _ _ => (), Bad := ∅, Hid := fun _ _ => ∅, stop0 := fun _ => false }
  early := id
  late := none

end Run.PQ

namespace Run
open Iop Rom Compile Compile.Batch Run.PQ

/-! ## Placeholder honest sides -/

def dfltSS : (s : Shape) → (A : RoundSplits s) → SStrat s A
  | [], _ => ()
  | r :: s, (a, A) => ((a.split (r.dOrc, r.dPlain)).1, fun _ => dfltSS s A)

def dfltLS : (s : Shape) → (A : RoundSplits s) → LStrat s A
  | [], _ => ()
  | r :: s, (a, A) => ((a.split (r.dOrc, r.dPlain)).2, fun _ => dfltLS s A)

/-- the placeholder honest side of a protocol -/
@[reducible] def dummyH {X Wt : Type} {E : ExtSpec} (Q : InteractiveOracleProof X E) (ext : Wt → E.Str) :
    Honest Q Wt :=
  { Coin := Unit, ext := ext, strat := fun _ _ _ => dfltS () _, Bad := ∅, Hid := fun _ _ => ∅ }

/-- the placeholder honest side of a batch -/
@[reducible] def dummyB {X Wt : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof X E) (ext : Wt → E.Str) :
    BatchHonestProver Q Wt :=
  { Coin0 := Unit, Coin := Unit, ext := ext, strat0 := fun _ _ => dfltSS _ _,
    strat := fun _ _ _ _ => dfltLS _ _, Bad := ∅, Hid := fun _ _ => ∅, stop0 := fun _ => false }

/-! ## Interfaces without an index -/

/-- Three given protocols, placeholders as honest sides. -/
@[reducible] def Lo3 (T : InteractiveOracleProof Unit (oneExternalString 0 Unit))
    (Lk : InteractiveOracleProof Unit (twoExternalStrings 0 Unit)) (B : BatchInteractiveOracleProof Unit (oneExternalString 0 Unit)) : BatchProtocol Unit Unit where
  wordLength := 0
  Symbol := Unit
  EncodingRandomness := Unit
  encodeIndex := fun _ _ _ => ()
  decodeIndex := fun _ => some ()
  offline := T
  link := Lk
  maxBatchSize := 1
  onlineBatch := B
  honestOfflineProver := dummyH T fun _ _ => ()
  honestLinkProver := dummyH Lk fun _ => (fun _ => (), fun _ => ())
  honestOnlineBatchProver := dummyB B fun _ _ => ()
  early := id
  late := none

end Run

namespace Run.PQ
open Iop Rom Compile Compile.Batch
open Run.Twin (RS PS)

/-- a given batch; Test and Link without a round -/
@[reducible] def Lb (B : BatchInteractiveOracleProof Unit E0) : BatchProtocol Unit Unit := Lo3 pB pL B

/-- The interface whose Batch is the protocol of `PSof C ds dec`. -/
@[reducible] def LbS (C : CK) (ds : List RD) (dec : View → Bool) : BatchProtocol Unit Unit :=
  Lb (BatchInteractiveOracleProof.ofProto (PSof C ds dec).up.loc)

/-- The wiring of the interface `Lb B`, from a wiring `wB` of its Batch. -/
def Wb {B : BatchInteractiveOracleProof Unit E0} (K : ℕ) (wB : ProtocolQueryLayout 256 K B) : QueryLayout 256 (Lb B) where
  K := K
  T := ⟨(), we0, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  Lk := ⟨(), weL, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  B := wB
  depth := 0
  depthReq := 0


/-- a plain part under the skeleton's annotation as one under the library's annotation of a shape -/
def embPL (C : CK) :
    (ds : List RD) → PlainPart (uL C ds) (Twin.allLo (SL C ds)) → PlainPart (uL C ds) (RoundSplits.allLocal (uL C ds))
  | [], p => p.elim
  | _ :: _, .inl x => .inl x
  | _ :: ds, .inr q => .inr (embPL C ds q)

def msgSL (C : CK) (rt : ByteArray) :
    (ds : List RD) → PlainPart (uL C ds) (RoundSplits.allLocal (uL C ds)) → ByteArray
  | [], p => p.elim
  | d :: _, .inl (.inr p) => PlainOf.bytes rt d.items (GPlain.old (b := d.entry.work) p)
  | _ :: _, .inl (.inl _) => ByteArray.empty
  | _ :: ds, .inr q => msgSL C rt ds q

def nonceSL (C : CK) : (ds : List RD) → PlainPart (uL C ds) (RoundSplits.allLocal (uL C ds)) → Nat
  | [], p => p.elim
  | d :: _, .inl (.inr p) => GPlain.nonce (b := d.entry.work) p
  | _ :: _, .inl (.inl _) => 0
  | _ :: ds, .inr q => nonceSL C ds q

def leafSL (C : CK) (salt : Nat) : (ds : List RD) → SymAny (uL C ds) → Nat × Nat × ByteArray
  | [], ⟨p, _⟩ => p.elim
  | d :: _, ⟨.inl x, col⟩ =>
    (_root_.Fmt.leafPlace (trNo d.tree) (colW d.tree) (salt / 8),
      posN d.tree + x.val,
      _root_.Fmt.colBytes (List.ofFn col) ++
        _root_.Fmt.zeroBytes (_root_.Fmt.fillLen (colW d.tree) salt))
  | _ :: ds, ⟨.inr q, col⟩ => leafSL C salt ds ⟨q, col⟩

/-- How typed queries are spelled as the format's hash calls. -/
def PDS (S : _root_.Fmt.Spec) (C : CK) (dec : View → Bool) : PageD (LbS C (rds S) dec) .onl where
  label := S.label
  kind := fun i => if i = 0 then 7 else ((S.rounds[i - 1]?).map (·.kind.num)).getD 7
  work := fun i => if i = 0 then 0 else ((S.rounds[i - 1]?).map (·.entry.work)).getD 0
  stm := fun _ => S.statement
  msg := fun _ rt pl => match pl with
    | .inl _ => ByteArray.empty
    | .inr q => msgSL C (rt.getD ByteArray.empty) (rds S) q
  nonce := fun _ pl => match pl with
    | .inl _ => 0
    | .inr q => nonceSL C (rds S) q
  leaf := fun s => match s with
    | ⟨.inl p, _⟩ => p.elim
    | ⟨.inr q, col⟩ => leafSL C S.plan.salt (rds S) ⟨q, col⟩
  cfg := S.cfg

def plainsSL (C : CK) : (ds : List RD) → List _root_.Fmt.RoundOut → Option (Plains (uL C ds))
  | [], [] => some ()
  | d :: ds, o :: os =>
    match PlainOf.ofGots d.items o.vals, plainsSL C ds os with
    | some p, some r => some (GPlain.mk d.entry.work p o.nonce, r)
    | _, _ => none
  | _, _ => none

def placeSL (C : CK) : (ds : List RD) → OPos (uL C ds) → Nat × Nat
  | [], p => p.elim
  | d :: _, .inl x => (trNo d.tree, x.val)
  | _ :: ds, .inr q => placeSL C ds q

def symSL (C : CK) : (ds : List RD) → (p : OPos (uL C ds)) → List UInt64 → Option (OSym (uL C ds) p)
  | [], p, _ => p.elim
  | d :: _, .inl _, l =>
    if h : l.length = colW d.tree then some (fun i => l[i.val]'(by rw [h]; exact i.isLt)) else none
  | _ :: ds, .inr q, l => symSL C ds q l

/-- What the parser asks of a protocol. -/
def TYS (S : _root_.Fmt.Spec) (C : CK) (dec : View → Bool) : TypingP (PSof C (rds S) dec) where
  saltBytes := S.plan.salt
  plains := fun os => (plainsSL C (rds S) os.toList).map fun r => ((), r)
  place := fun p => match p with
    | .inl e => e.elim
    | .inr q => placeSL C (rds S) q
  sym := fun p l => match p with
    | .inl e => e.elim
    | .inr q => symSL C (rds S) q l

/-! ## The verifier and its run -/

/-- a plain part of the whole shape, carried over -/
def embPS (C : CK) (ds : List RD) (dec : View → Bool) :
    PlainPart (Twin.up (SOf C ds)) (Twin.allLo (SOf C ds)) →
    PlainPart (Compile.Batch.shapeOf (LbS C ds dec) .onl) (Compile.Batch.annOf (LbS C ds dec) .onl)
  | .inl x => .inl x
  | .inr q => .inr (embPL C ds q)

/-- The verifier, for every choice of challenge types C and samplers `chal`. -/
def VPC (S : _root_.Fmt.Spec) (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (dec : View → Bool) (cm : Dig 256) (π : OneProtocolProof 256 (PSof C (rds S) dec).up) : Bool :=
  Thin.verifyPR (lam := 256) (K := K + 1) (fun _ => LbS C (rds S) dec)
    (famK (fun _ => LbS C (rds S) dec) (PDS S C dec) (K + 1)) id none (256 + 8 * S.plan.salt) 256
    .onl (PSof C (rds S) dec) (wqS C K chal (rds S) dec) (fun p a => some (.inr ⟨Tag.onl, ⟨p, a⟩⟩))
    (embPS C (rds S) dec) some (fun s => some (.inl s)) 0 [cm] () π

/-- States: what is evaluated (`VPC`) is the run of the compiled verifier, for every choice of
challenge types and samplers. -/
def Spec.vpc_eq : Prop :=
  ∀ (S : _root_.Fmt.Spec) (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
      (dec : View → Bool) (cm : Dig 256) (π : OneProtocolProof 256 (PSof C (rds S) dec).up),
    VPC S C K chal dec cm π =
      (verifyOneProtocol (lam := 256) (K := K + 1) (L := LbS C (rds S) dec) (256 + 8 * S.plan.salt) 256 .onl
          (PSof C (rds S) dec).up (wqS C K chal (rds S) dec)
          (fun p a => some (.inr ⟨Tag.onl, ⟨p, a⟩⟩)) (embPS C (rds S) dec) some
          (fun s => some (.inl s)) 0 [cm] () π).det
        (famP (fun _ => LbS C (rds S) dec) _root_.Fmt.oracle (PDS S C dec) (K + 1))

theorem vpc_eq : Spec.vpc_eq := fun S C K chal dec cm π => by
  unfold VPC
  rw [famK_eq]
  exact Thin.thin_reads Unit Unit 256 (K + 1) (LbS C (rds S) dec) _ Unit E0
    (256 + 8 * S.plan.salt) 256 .onl (PSof C (rds S) dec) (wqS C K chal (rds S) dec) _ _ some
    (fun s => some (.inl s)) 0 [cm] () π

def runOnC (S : _root_.Fmt.Spec) (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (dec : View → Bool) (x : Option (List (Dig 256) × OneProtocolProof 256 (PSof C (rds S) dec).up)) : Who :=
  if ok S then
    match x with
    | some ([cm], π) => if VPC S C K chal dec cm π then .accepted else .verifier
    | _ => .reader
  else .limits

/-- The run function through the page's own reader (in the head: the strict reader), for every
choice of challenge types and samplers. -/
def runStrictC (S : _root_.Fmt.Spec) (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (dec : View → Bool) (file : ByteArray) : Who :=
  runOnC S C K chal dec
    ((_root_.Fmt.wholeChainF S file).bind (toBPrfP (PSof C (rds S) dec) (TYS S C dec)))

/-- The run function through the lenient reader, for every choice of challenge types and samplers.
-/
def runLaxC (S : _root_.Fmt.Spec) (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (dec : View → Bool) (file : ByteArray) : Who :=
  runOnC S C K chal dec (parseLaxFP (PSof C (rds S) dec) S (TYS S C dec) file)

/-- States: the two run functions' readers are the page's own reader and the lenient reader at the
format's hash: the fast forms change no value. -/
def Spec.runC_readers : Prop :=
  ∀ (S : _root_.Fmt.Spec) (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
      (dec : View → Bool) (file : ByteArray),
    runStrictC S C K chal dec file =
      runOnC S C K chal dec
        (parseWP (m := Id) _root_.Fmt.formatHash (PSof C (rds S) dec) S (TYS S C dec) file) ∧
    runLaxC S C K chal dec file =
      runOnC S C K chal dec
        (parseLaxWP (m := Id) _root_.Fmt.formatHash (PSof C (rds S) dec) S (TYS S C dec) file)

theorem runC_readers : Spec.runC_readers := by
  intro S C K chal dec file
  refine ⟨?_, ?_⟩
  · unfold runStrictC
    rw [_root_.Fmt.wholeChainF_eq]
    rfl
  · unfold runLaxC
    rw [(laxFast_parse _ S _ file).1]

/-! ## With challenges as sampled values -/

/-- The verifier with challenges as sampled values: the wiring applies each round's sampler. -/
def VP (S : _root_.Fmt.Spec) (dec : View → Bool) (cm : Dig 256)
    (π : OneProtocolProof 256 (PSof (ck S.plan.field) (rds S) dec).up) : Bool :=
  VPC S (ck S.plan.field) (kOf S) (chalOf S.plan.field (kOf S)) dec cm π

/-- States: what is evaluated (`VP`) is the run of the compiled verifier. -/
def Spec.vp_eq : Prop :=
  ∀ (S : _root_.Fmt.Spec) (dec : View → Bool) (cm : Dig 256)
      (π : OneProtocolProof 256 (PSof (ck S.plan.field) (rds S) dec).up),
    VP S dec cm π =
      (verifyOneProtocol (lam := 256) (K := kOf S + 1) (L := LbS (ck S.plan.field) (rds S) dec)
          (256 + 8 * S.plan.salt) 256 .onl (PSof (ck S.plan.field) (rds S) dec).up
          (wqS (ck S.plan.field) (kOf S) (chalOf S.plan.field (kOf S)) (rds S) dec)
          (fun p a => some (.inr ⟨Tag.onl, ⟨p, a⟩⟩)) (embPS (ck S.plan.field) (rds S) dec) some
          (fun s => some (.inl s)) 0 [cm] () π).det
        (famP (fun _ => LbS (ck S.plan.field) (rds S) dec) _root_.Fmt.oracle
          (PDS S (ck S.plan.field) dec) (kOf S + 1))

theorem vp_eq : Spec.vp_eq := fun S dec cm π =>
  vpc_eq S (ck S.plan.field) (kOf S) (chalOf S.plan.field (kOf S)) dec cm π

def runOnS (S : _root_.Fmt.Spec) (dec : View → Bool)
    (x : Option (List (Dig 256) × OneProtocolProof 256 (PSof (ck S.plan.field) (rds S) dec).up)) : Who :=
  runOnC S (ck S.plan.field) (kOf S) (chalOf S.plan.field (kOf S)) dec x

/-- The run function through the page's own reader (in the head: the strict reader). -/
def runStrictS (S : _root_.Fmt.Spec) (dec : View → Bool) (file : ByteArray) : Who :=
  runStrictC S (ck S.plan.field) (kOf S) (chalOf S.plan.field (kOf S)) dec file

/-- The run function through the lenient reader. -/
def runLaxS (S : _root_.Fmt.Spec) (dec : View → Bool) (file : ByteArray) : Who :=
  runLaxC S (ck S.plan.field) (kOf S) (chalOf S.plan.field (kOf S)) dec file

def Spec.run_readers : Prop :=
  ∀ (S : _root_.Fmt.Spec) (dec : View → Bool) (file : ByteArray),
    runStrictS S dec file =
      runOnS S dec
        (parseWP (m := Id) _root_.Fmt.formatHash (PSof (ck S.plan.field) (rds S) dec) S
          (TYS S (ck S.plan.field) dec) file) ∧
    runLaxS S dec file =
      runOnS S dec
        (parseLaxWP (m := Id) _root_.Fmt.formatHash (PSof (ck S.plan.field) (rds S) dec) S
          (TYS S (ck S.plan.field) dec) file)

theorem run_readers : Spec.run_readers := fun S dec file =>
  runC_readers S (ck S.plan.field) (kOf S) (chalOf S.plan.field (kOf S)) dec file

end Run.PQ
