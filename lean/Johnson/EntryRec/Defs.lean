-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/EntryRec/Defs.lean: every object with records (`Iop.HolographicProtocol`) whose Link has the shape, the
marks and the reads of a description with two stored tables, the pair of records being the instance;
and the evaluable form, along the positions read and listed, of the compiled Link verifier with the
two records (Johnson/RecCompile/Cms.lean, `vLC`) at such an object. Definitions alone; the laws are
in Johnson/EntryRec/Laws.lean.

Johnson/EntryRec/RecDefs.lean has one such object, `LrX`, whose Test and session accept nothing.
Here Test, the session, the number of slots, what is written early and late of an instance, and
the three honest sides are arguments (`RestR`), and so is Link's decision (`acc`): the laws ask that
it equals the decision of the skeleton `PSofR`, by a proof and not by unfolding. So a Link whose
decision is written otherwise, say as "the reduction's verifier returns something", is covered.

What the file contains.
  `protoR`: the protocol with `PSofR`'s shape, marks and reads, and any decision.
  `RestR`: what an object with records holds beside the word length 2 ^ a, the alphabet `SgX` and
    its Link.
  `LrG`: the object.
  `embPG`, `asLinkG`: a plain part, and a typed string, of the skeleton as one of the object's Link:
    the same data.
  `VLCG`: `verifyPLO` (OnBytes/RunA/ListedOwnDefs.lean) at `vLC`'s arguments. d: the depth of the
    request tree.

Limits: those of Johnson/EntryRec/RecDefs.lean's head on the oracle functions (a letter), on cfg
and on what no check sees of (π, otabs, tabs). This form has not been run.

-/
import Johnson.EntryRec.RecDefs

set_option autoImplicit false

namespace OnBytes.RunA

open _root_.Run _root_.Run.PQ _root_.Run.Thin _root_.Run.Twin Iop Rom Compile Compile.Batch
open Compile.Batch.Cms

/-- The protocol with `PSofR`'s shape, marks and reads, and any decision. -/
@[reducible] def protoR (R : Type) (C : CK) (ds : List RD) (a : Nat) (xs : List XO)
    (acc : R × R → (twoExternalStrings (2 ^ a) SgX).Str → Iop.Tr (Twin.up (SOf C ds)) → Bool) :
    InteractiveOracleProof (R × R) (twoExternalStrings (2 ^ a) SgX) where
  shape := Twin.up (SOf C ds)
  blinded := fun _ => true
  extReads := fun _ ρ => ((xWanted a ds xs (drawnSL C ds ρ.2)).filterMap (xPos (2 ^ a))).toFinset
  reads := fun _ ρ _ =>
    (((wanted ds (drawnSL C ds ρ.2)).filterMap fun nx =>
      (posAtS C ds nx.1 nx.2).map fun p => (Sum.inr p : OPos (Twin.up (SOf C ds))))).toFinset
  accept := acc

/-- **What an object with records holds beside its word length, its alphabet and its Link Q.** -/
structure RestR (I X RI Seed Ans : Type) (a : ℕ)
    (Q : InteractiveOracleProof ((Seed × Ans) × (Seed × Ans)) (twoExternalStrings (2 ^ a) SgX)) where
  enc : I → RI → Fin (2 ^ a) → SgX
  ans : I → RI → Seed → Ans
  coll : (Fin (2 ^ a) → SgX) → Seed → Prop
  dcd : (Fin (2 ^ a) → SgX) → Seed × Ans → Option I
  test : InteractiveOracleProof (Seed × Ans) (oneExternalString (2 ^ a) SgX)
  N : ℕ
  bat : BatchInteractiveOracleProof (X × (Seed × Ans)) (oneExternalString (2 ^ a) SgX)
  hT : Honest test (I × RI × Seed)
  hL : Honest Q (I × (RI × Seed) × (RI × Seed))
  hB : BatchHonestProver bat (I × RI × Seed)
  early : X → X
  late : Option ℕ

section
variable {I X RI Seed Ans : Type} [Fintype RI] [Nonempty RI] [Fintype Seed] [Nonempty Seed] {a : ℕ}

/-- **The object with records.** -/
@[reducible] def LrG {Q : InteractiveOracleProof ((Seed × Ans) × (Seed × Ans)) (twoExternalStrings (2 ^ a) SgX)}
    (T : RestR I X RI Seed Ans a Q) : HolographicProtocol I X where
  wordLength := 2 ^ a
  Symbol := SgX
  EncodingRandomness := RI
  encodeIndex := T.enc
  OutOfDomainSeed := Seed
  OutOfDomainAnswer := Ans
  honestOutOfDomainAnswer := T.ans
  hasCollisionAt := T.coll
  decodeIndex := T.dcd
  offline := T.test
  link := Q
  maxBatchSize := T.N
  onlineBatch := T.bat
  honestOfflineProver := T.hT
  honestLinkProver := T.hL
  honestOnlineBatchProver := T.hB
  early := T.early
  late := T.late

variable {C : CK} {ds : List RD} {xs : List XO}
  {acc : (Seed × Ans) × (Seed × Ans) → (twoExternalStrings (2 ^ a) SgX).Str → Iop.Tr (Twin.up (SOf C ds)) → Bool}
  (T : RestR I X RI Seed Ans a (protoR (Seed × Ans) C ds a xs acc))

/-- A plain part of the skeleton's shape as one of the Link of the carrier of the typed oracles. -/
def embPG :
    PlainPart (Twin.up (SOf C ds)) (Twin.allLo (SOf C ds)) →
    PlainPart (shapeOf (LrG T).carrierC .link) (annOf (LrG T).carrierC .link)
  | .inl x => .inl x
  | .inr q => .inr (embPL C ds q)

/-- A typed string of the skeleton as a Link string of the object: the same eight fields. -/
def asLinkG (dec : (Seed × Ans) × (Seed × Ans) → View → Bool)
    (π : OneProtocolProof 256 (PSofR (Seed × Ans) C ds a xs dec).up) :
    OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto (LrG T).link) :=
  ⟨π.salt, π.roots, π.plains, π.opens, π.ext, π.rtreq, π.slot, π.path⟩

/-- **The compiled Link verifier with the two records, along the positions read and listed.** -/
def VLCG (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (dec : (Seed × Ans) × (Seed × Ans) → View → Bool)
    (g : Fam (spec 256 (K + 1) (LrG T).carrierC)) (sMT sFS d : ℕ) (cfg : ByteArray)
    (cm cm' : Dig 256) (rec rec' : Seed × Ans)
    (π : OneProtocolProof 256 (PSofR (Seed × Ans) C ds a xs dec).up)
    (otabs : List (Nat × List (Nat × Row3)))
    (tabs : List (Bool × OpenB × List (List (Dig 256)))) : Bool :=
  verifyPLO (lam := 256) (K := K + 1) (fun _ => (LrG T).carrierC) g
    (readsInOrder2 (2 ^ a)) (fun z => (z.1.map T.early, z.2)) T.late sMT sFS .link
    (PSofR (Seed × Ans) C ds a xs dec) (wire0Less C K chal, wiresLessSL C K chal ds) (decOS C ds)
    (weLessX a) (nOpen ds + (xs.map (·.count)).sum) (max (maxDepth ds) a)
    (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩)) (embPG T)
    (fun rr => some (none, rr.1, rr.2)) (fun s => some (.inl s)) d [cm, cm'] (rec, rec')
    { π with
      opens := opensOfX 0 C ds a xs (fun _ => true) otabs
      ext := extOf a cfg tabs }
    (listedX a tabs) (ownListedX ds otabs)

end

end OnBytes.RunA
