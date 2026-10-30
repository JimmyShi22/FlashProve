-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/EntryRec/RecDefs.lean: an object with records (`Iop.HolographicProtocol`, Hiop/RecInterface.lean) whose Link
is the protocol of a description with two stored tables, the pair of records being the protocol's
instance; and the evaluable form, along the positions read and listed, of what the compiled
verifier with the record (Johnson/RecCompile/Cms.lean, `VC`) does for an entry: two seed queries and
the compiled Link verifier. Definitions alone; the laws are in Johnson/EntryRec/RecLaws.lean.

Why. `VC` calls the library's compiled verifier of one slot (`verifyOneProtocol`) at an object's Link with
the two records as the instance, so that there is one protocol for all records. The forms that run
on an entry file (`VXLO`, OnBytes/RunA/ListedOwnDefs.lean) stand at Run/PlanQX.lean's skeleton
`skeletonOverBothExternalStrings`, whose instance is `Unit` and whose decision holds the records inside: one protocol for each
pair of records. Here the decision takes the records as an argument.

What the file contains.
  `PSofR`: `skeletonOverBothExternalStrings` word for word, but for the instance (a pair of records) and the last conjunct of
    `accept`, which is `dec rr (viewX ..)`. Shape, marking, reads and external reads do not read the
    instance or the decision.
  `wqR`: `wqX` at that skeleton.
  `PS0`: the skeleton of a protocol with one idle round that accepts nothing.
  `LrX`: the object with records. Link is `PSofR`'s protocol. Test and the session are `PS0`'s. The
    honest sides are the library's placeholders. Index, encoding, seeds, answers, "the word has a
    collision at the seed" and the index decoder are letters.
  `embPR`: Run/PlanQX.lean's `embPX` at the carrier of the typed oracles (`HolographicProtocol.carrierC`).
  `VLCO`: `verifyPLO` at the arguments of Johnson/RecCompile/Cms.lean's `vLC`.
  `seedIsO`: one seed's query, asked again and compared (`seedIs`), with a decidable equality of
    seeds given as an instance; `seedIs` itself decides by the field `decS` of the record's wire.
  `VCEO`: the two seeds' queries and `VLCO`, as one form.
In `VLCO` the own trees' openings are `opensOfX 0 C ds a xs (fun _ => true) otabs`: that look-up's
arguments for the salt's length and the decision are idle (OnBytes/RunA/ListedOwnDefs.lean's head).

Limits.
  At `LrX` Test and the session accept nothing. So `VC` itself, which asks a yes of all three
  compiled verifiers, accepts nothing at this object (by reading; no theorem here says it), and
  every statement on "a scheme whose verifier is `VC`" is true and empty at it. What has content
  at this object are statements on the seeds' queries and on the compiled Link verifier alone.
  The oracle functions g are a letter: typed oracle functions at the carrier of this object. No
  family is written here that spells the typed queries as the format's hash calls: the first query
  holds both records, seeds and answers, typed; a seed's query holds the root alone.
  What is said in the heads of OnBytes/RunA/ListedDefs.lean and ListedOwnDefs.lean on what no check
  sees of (π, otabs, tabs), on cfg and on the leaves' salts holds here word for word: cfg decides
  what is hashed and must come from the description.
  These forms have not been run.
  No caller outside this file and RecLaws.lean of `PS0`, `LrX`, `embPR`, `VLCO`, `seedIsO`, `VCEO`.
  Johnson/EntryRec/Defs.lean's `LrG` is the object that is used (LinkWireWithListsOfTrees.lean of this folder); its
  `VLCG` has no caller outside Defs.lean and Laws.lean either. That `LrX` is an instance of `LrG` is
  said by no theorem, and `seedIsO` and `VCEO` have no form at `LrG`. `embPR`, `VLCO`, `seedIsO` and
  `VCEO` are typed at Johnson/RecCompile/Cms.lean, the first form of the compiled verifier with the
  record; no statement carries them to the second form (Johnson/TypedOracleCompiler/RecCompile), over which
  WiringOfTypedOracleCarrier.lean of this folder stands.

-/
import OnBytes.RunA.ListedOwnDefs
import Johnson.RecCompile.Cms

set_option autoImplicit false

namespace OnBytes.RunA

open _root_.Run _root_.Run.PQ _root_.Run.Thin _root_.Run.Twin Iop Rom Compile Compile.Batch
open Compile.Batch.Cms

/-- Run/PlanQX.lean's `skeletonOverBothExternalStrings`, with a pair of records as the instance: the decision reads it. -/
@[reducible] def PSofR (R : Type) (C : CK) (ds : List RD) (a : Nat) (xs : List XO)
    (dec : R × R → View → Bool) : PS (R × R) (twoExternalStrings (2 ^ a) SgX) where
  S := SOf C ds
  blinded := fun _ => true
  extReads := fun _ ρ => ((xWanted a ds xs (drawnSL C ds ρ.2)).filterMap (xPos (2 ^ a))).toFinset
  reads := fun _ ρ _ =>
    (((wanted ds (drawnSL C ds ρ.2)).filterMap fun nx =>
      (posAtS C ds nx.1 nx.2).map fun p => (Sum.inr p : OPos (Twin.up (SOf C ds))))).toFinset
  accept := fun rr y τ =>
    passSL C ds (rhoSL C ds τ.2.2) && everyOpeningHasItsDraws xs (drawnSL C ds (rhoSL C ds τ.2.2)) &&
      symbolsCarryTheirPositions a ds xs (drawnSL C ds (rhoSL C ds τ.2.2)) y && dec rr (viewX C ds a xs y τ.2.2)
  ann := Twin.allLo (SOf C ds)

/-- Run/PlanQX.lean's `wqX` at that skeleton. -/
def wqR (R : Type) (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (ds : List RD)
    (a : Nat) (xs : List XO) (dec : R × R → View → Bool) :
    ProtocolQueryLayout 256 (K + 1) (PSofR R C ds a xs dec).up :=
  ⟨(wire0S C K chal, wiresSL C K chal ds), weX a, decOS C ds,
    nOpen ds + (xs.map (·.count)).sum, max (maxDepth ds) a⟩

/-- The skeleton of a protocol on one string that accepts nothing. It has one round, the round in
front of a description's rounds (nothing is sent, nothing is read): with no round at all the typed
Fiat-Shamir oracle of its tag would have no query, and a seed's query is a query to such an
oracle. -/
@[reducible] def PS0 (Y : Type) (C : CK) (n : Nat) : PS Y (oneExternalString n SgX) where
  S := [s0 C]
  blinded := fun _ => false
  extReads := fun _ _ => ∅
  reads := fun _ _ _ => ∅
  accept := fun _ _ _ => false
  ann := Twin.allLo [s0 C]

section
variable {I X RI Seed Ans : Type} [Fintype RI] [Nonempty RI] [Fintype Seed] [Nonempty Seed]

/-- **The object with records whose Link is the protocol.** Test and the session accept nothing. -/
@[reducible] def LrX (X : Type) (C : CK) (ds : List RD) (a : Nat) (xs : List XO)
    (dec : (Seed × Ans) × (Seed × Ans) → View → Bool) (enc : I → RI → Fin (2 ^ a) → SgX)
    (ans : I → RI → Seed → Ans) (coll : (Fin (2 ^ a) → SgX) → Seed → Prop)
    (dcd : (Fin (2 ^ a) → SgX) → Seed × Ans → Option I) : HolographicProtocol I X where
  wordLength := 2 ^ a
  Symbol := SgX
  EncodingRandomness := RI
  encodeIndex := enc
  OutOfDomainSeed := Seed
  OutOfDomainAnswer := Ans
  honestOutOfDomainAnswer := ans
  hasCollisionAt := coll
  decodeIndex := dcd
  offline := (PS0 _ C (2 ^ a)).up.loc
  link := (PSofR (Seed × Ans) C ds a xs dec).up.loc
  maxBatchSize := 1
  onlineBatch := BatchInteractiveOracleProof.ofProto (PS0 _ C (2 ^ a)).up.loc
  honestOfflineProver := dummyH _ fun w => enc w.1 w.2.1
  honestLinkProver := dummyH _ fun w => (enc w.1 w.2.1.1, enc w.1 w.2.2.1)
  honestOnlineBatchProver := dummyB _ fun w => enc w.1 w.2.1
  early := id
  late := none

variable (X) (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (ds : List RD)
  (a : Nat) (xs : List XO) (dec : (Seed × Ans) × (Seed × Ans) → View → Bool)
  (enc : I → RI → Fin (2 ^ a) → SgX) (ans : I → RI → Seed → Ans)
  (coll : (Fin (2 ^ a) → SgX) → Seed → Prop) (dcd : (Fin (2 ^ a) → SgX) → Seed × Ans → Option I)

/-- A plain part of the whole shape, carried over to the Link of the carrier of the typed oracles
(Run/PlanQX.lean, `embPX`). -/
def embPR :
    PlainPart (Twin.up (SOf C ds)) (Twin.allLo (SOf C ds)) →
    PlainPart (shapeOf (LrX X C ds a xs dec enc ans coll dcd).carrierC .link)
      (annOf (LrX X C ds a xs dec enc ans coll dcd).carrierC .link)
  | .inl x => .inl x
  | .inr q => .inr (embPL C ds q)

/-- **The compiled Link verifier with the two records, along the positions read and listed.** Of
the typed string π all fields but `opens` and `ext` go into the string; the openings are the
library's look-ups in the tables, as in `VXLO`. -/
def VLCO (g : Fam (spec 256 (K + 1) (LrX X C ds a xs dec enc ans coll dcd).carrierC))
    (sMT sFS : ℕ) (cfg : ByteArray) (cm cm' : Dig 256) (rec rec' : Seed × Ans)
    (π : OneProtocolProof 256 (PSofR (Seed × Ans) C ds a xs dec).up)
    (otabs : List (Nat × List (Nat × Row3)))
    (tabs : List (Bool × OpenB × List (List (Dig 256)))) : Bool :=
  verifyPLO (lam := 256) (K := K + 1) (fun _ => (LrX X C ds a xs dec enc ans coll dcd).carrierC) g
    (readsInOrder2 (2 ^ a)) (fun z => (z.1.map id, z.2)) none sMT sFS .link
    (PSofR (Seed × Ans) C ds a xs dec) (wire0Less C K chal, wiresLessSL C K chal ds) (decOS C ds)
    (weLessX a) (nOpen ds + (xs.map (·.count)).sum) (max (maxDepth ds) a)
    (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩)) (embPR X C ds a xs dec enc ans coll dcd)
    (fun rr => some (none, rr.1, rr.2)) (fun s => some (.inl s)) 0 [cm, cm'] (rec, rec')
    { π with
      opens := opensOfX 0 C ds a xs (fun _ => true) otabs
      ext := extOf a cfg tabs }
    (listedX a tabs) (ownListedX ds otabs)

/-- **One seed's query, asked again and compared.** `pl`: the query's fixed plain part; `seed`: how
the answer's blocks give a seed. -/
def seedIsO [DecidableEq Seed]
    (g : Fam (spec 256 (K + 1) (LrX X C ds a xs dec enc ans coll dcd).carrierC)) (t : Tag)
    (pl : PlainPart (shapeOf (LrX X C ds a xs dec enc ans coll dcd).carrierC t)
      (annOf (LrX X C ds a xs dec enc ans coll dcd).carrierC t))
    (seed : (Fin (K + 1) → Dig 256) → Seed) (cm : Dig 256) (s : Seed) : Bool :=
  let ans' : (Fin (K + 1) → Dig 256) × Dig 256 :=
    g (OracleName.fb t)
      (⟨1, .f1 [cm] none [], none, pl⟩ : FbIn 256 (LrX X C ds a xs dec enc ans coll dcd).carrierC t)
  decide (seed ans'.1 = s)

/-- **What the compiled verifier with the record does for an entry, as one form**: the two seeds'
queries, then the compiled Link verifier. -/
def VCEO [DecidableEq Seed]
    (g : Fam (spec 256 (K + 1) (LrX X C ds a xs dec enc ans coll dcd).carrierC)) (t0 t1 : Tag)
    (pl : (t : Tag) → PlainPart (shapeOf (LrX X C ds a xs dec enc ans coll dcd).carrierC t)
      (annOf (LrX X C ds a xs dec enc ans coll dcd).carrierC t))
    (seed : (Fin (K + 1) → Dig 256) → Seed) (sMT sFS : ℕ) (cfg : ByteArray) (cm cm' : Dig 256)
    (rec rec' : Seed × Ans) (π : OneProtocolProof 256 (PSofR (Seed × Ans) C ds a xs dec).up)
    (otabs : List (Nat × List (Nat × Row3)))
    (tabs : List (Bool × OpenB × List (List (Dig 256)))) : Bool :=
  seedIsO X C K ds a xs dec enc ans coll dcd g t0 (pl t0) seed cm rec.1 &&
    seedIsO X C K ds a xs dec enc ans coll dcd g t1 (pl t1) seed cm' rec'.1 &&
    VLCO X C K chal ds a xs dec enc ans coll dcd g sMT sFS cfg cm cm' rec rec' π otabs tabs

end

end OnBytes.RunA
