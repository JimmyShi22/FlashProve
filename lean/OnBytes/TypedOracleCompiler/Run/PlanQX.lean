-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PlanQX.lean.
This file is a part of the library's Run/PlanQX.lean (only what the entry's clause holds and
stands on a declaration that the sibling says again), and differs from it where it has to. THE
HEAD BELOW IS THE LIBRARY's AND SPEAKS OF THE LIBRARY's FILE: much of what it announces IS NOT HERE,
and what it says of "one root | one tree a round" is not true of this file. HERE STAND ONLY:
wantedXL, wantedX, xWanted, symbolsCarryTheirPositions, viewX, okX, skeletonOverBothExternalStrings, wqX, LkX, embPX, TYX, toBPrfX.

Run/PlanQX.lean: the generic protocol with two stored tables as external oracles, as the Link
protocol of an interface.

Run/PlanQS.lean turns a description of a proof's rounds into a protocol of the library, with a
wiring and a verifier that can be evaluated. There every Merkle tree is one that the prover sends in
the proof itself (the chain's own trees). An entry file also opens two stored tables, whose roots
stand outside the proof: the first table's in the key, the copy's at the head of the file. This file
adds them as the two external oracles of the library's Link protocol. It is a layer on
Run/PlanQS.lean: rounds, shape, view and the wiring of the own trees are that file's, unchanged, and
the case "no external opening" gives PlanQS's protocol back. Each external string has 2^a symbols,
for a stored tree of depth a.

Sources. The order and the lists of the openings were written against the format page (FORMAT.md,
which comes with the programs), rules R7.19 and R8.7, and R4.6 for the
statement's items. This file is not held against the page as it ships, and may differ from
it, for instance at R7.19; according to a restatement,
in a clause on the record of vertices met, which this file does not render. The
programs are the C++ implementation that comes with this Lean code.

1. What the file contains.
   SgX                  A symbol of a stored table's string: its position and its column. Why the
                        position is part of the symbol: the library's leaf of an external tree holds
                        the symbol alone, while the format hashes a stored leaf under its place.
                        (The same device as in Run/ToyX.lean.)
   XO                   An opening of a stored table: the round behind whose drawn positions it
                        stands; which of the two strings; its part of the draws (from, count).
   storedKey which      The key under which a stored tree's columns stand in a view's list "opened".
                        It is the reader's key (Fmt/Rules8X.lean: 2^16 + the number of the
                        statement's item). So the view keeps its type, and a decision is a function
                        View → Bool as before. The two strings are the statement's items 0 and 1
                        (FORMAT.md, R4.6: the stored tables' items stand before a statement's other
                        items, one item a table); XO has no field for an item.
   wantedX a ds xs Ds   What the drawn positions ask for, round by round: first the stored trees, in
                        the order of xs, each at the list (sorted, each position once) of its own
                        part of the draws, modulo 2^a; then the own trees.
   xWanted, xPos        Of these the stored ones, as positions of the two strings.
   everyOpeningHasItsDraws, symbolsCarryTheirPositions      Two tests inside the verifier. A part has as many draws as it says, so
                        nothing is shortened silently. Every symbol read carries the position at
                        which it was read.
   viewX                The view: "opened" holds the stored columns under their keys, among the own
                        trees' columns.
   partsX, okX ds a xs The limits, as a test on the description. Among them FORMAT.md's R7.19: the
   first n_1 draws go to one tree, the next n_2 to the next, and their sum is the plan's number. Two
   limits are our own. (i) A round with openings of stored tables opens no tree of the chain's own.
   By the letter of R8.7 such a tree would have a part of its own; no file has the case, so it is
   refused, which is the smaller promise. What wantedX says for that case is idle within okX. (ii)
   Strings shorter than the round's range are read at the draws modulo 2^a; this is idle where range
   and depth agree. (For the chain's own trees an edition of FORMAT.md has that rule,
   R13.12, not held against the page that ships; for stored trees it is our own.) skeletonOverBothExternalStrings C ds a xs
   dec The protocol. Shape, reads of own trees and annotation are Run/PlanQS.lean's. The external
   reads are the set of xWanted. It accepts if the tests of work, everyOpeningHasItsDraws and symbolsCarryTheirPositions pass and dec
   accepts viewX.
   weX a, wqX           The wiring of the two strings (the library's WireE.two, with one walk over a
                        pruned set of paths), and of the protocol: own trees as in Run/PlanQS.lean;
                        the count of openings and the greatest depth include the external ones.
   LkX                  The interface. Index type, encoding randomness, encoding and decoder are
                        parameters. Link is the protocol. Test and Batch have no rounds. The honest
                        sides are placeholders.
   embPX, VPX           The evaluable form of the compiled verifier (Run/ThinExtReads.lean:
                        verifyPX, which has a fast test for "is position p read?"), at the tag
                        "link", under the two roots [cm, cm'], at any typed oracle functions g.
   TYX, offStored, storedB, extOf, toBPrfX
                        From what the reader of Fmt/Rules8X.lean has read (wholeChainX's ChainOut)
                        to a proof string of the library's type. The own trees are typed as before,
                        from the rounds with the stored openings taken off. An external opening at p
                        has the symbol (p, column), the salt "the configuration's digest, then the
                        file's salt", and a whole path filled in from the pruned set.

2. What is checked when the file compiles. No test stands in this file. The library's
Run/PlanQX.lean has eight tests (#guard), of the library's own functions, on made-up data: the two
parts' lists (a position drawn for both strings stands under both keys); okX and everyOpeningHasItsDraws at that data;
the limits refuse a round that is not there, a part beyond the draws, strings longer than the range,
the second string's opening before the first's, a gap, an overlap, draws that nobody reads, a part
that does not begin at the first draw, and an own tree in a round that is cut; a symbol that carries
another position is noticed.

3. Theorems.
   vpx_eq               VPX .. = (Compile.Batch.verifyOneProtocol .. Tag.link (skeletonOverBothExternalStrings ..).up (wqX ..) .. [cm,
                        cm'] () π).det g. What is evaluated is the run of the compiled verifier of
                        one slot, at the tag "link", under the two roots. By Run/ThinExtReads.lean's
                        thin_ext.

4. What is not claimed, or stands elsewhere.
   A whole wiring of the interface, and Compile.Batch.vLS itself, are not here. Link's wiring is
   typed at the library's annotation "all rounds local", which is this file's annotation only at a
   closed list of rounds. At a closed list: Run/ToyLk.lean (vls_toy).
   How typed queries are spelled as hash calls: Run/PlanQXRun.lean. The laws of the wiring, and that
   the verifier is local: Run/PlanQXLaws.lean.
   No encoding and no decoder is given. NO STATEMENT ON SOUNDNESS FOLLOWS. The library has a link
   protocol with soundness statements (Cb/Ld/LdLink.lean); nothing connects it with the protocol of
   this file.
   That viewX is the view that the reader forms is not proved. (Run/ToyLk.lean tests, at one file,
   that the reader's list "opened" has the keys and positions of wantedX, in the same order; it does
   not compare the two views.)

Terms: lean/GLOSSARY.md.

-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library: a test by Lean's evaluator, which
   leaves no declaration. So nothing that is checked of declarations is checked of such a run. No
   clause of a soundness theorem of this library speaks of a run. -/
import Run.PlanQX
-- reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.PlanQTypes
-- reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFn
-- reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ParseChain
import OnBytes.TypedOracleCompiler.Run.ParseBS  -- reached in the library through files that are not said again
-- reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFnThin
-- reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFnTag
-- reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinDefs
-- reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ThinDefs
import OnBytes.TypedOracleCompiler.Run.ThinTie  -- reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinDet  -- reached in the library through files that are not said again
-- reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.VerifyDet
-- reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ThinTieProofs
-- reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinDetProofs
import OnBytes.TypedOracleCompiler.Run.TwinTie  -- reached in the library through files that are not said again
-- reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinTiePureProofs
-- reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinTiePure
-- reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.VerifyDetProofs
-- reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ParseThin
-- reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.PlanPull
-- reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.PlanQSLaws
-- reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Compile.Batch.ImplOf
import OnBytes.TypedOracleCompiler.Run.PlanQS
import OnBytes.TypedOracleCompiler.Run.PlanQSMore
import Run.ThinExtReads
import Fmt.Rules8X

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open _root_.Run.Twin (allLo)
export _root_.Run.PQ (SgX XO storedKey xsAt xPos everyOpeningHasItsDraws partsX weX pT1 offStored storedB extOf)
open Run.Twin (RS PS)

/-- What the drawn positions ask for.  (key, position) -/
def wantedXL (a : Nat) (all : List RD) (xs : List XO) :
    Nat → List RD → List _root_.Fmt.Drawn → List (Nat × Nat)
  | i, d :: ds, D :: Ds =>
    ((xsAt xs i).flatMap fun o => (o.list a D).map fun x => (storedKey o.which, x)) ++
    (d.opens.flatMap fun n =>
      match treeSh all n with
      | none => []
      | some s => (_root_.Fmt.listOf (D.poss.map (· % 2 ^ s.a))).map fun x => (n, x)) ++ wantedXL a
          all xs (i + 1) ds Ds
  | _, _, _ => []

def wantedX (a : Nat) (ds : List RD) (xs : List XO) (Ds : List _root_.Fmt.Drawn) :
    List (Nat × Nat) :=
  wantedXL a ds xs 0 ds Ds

/-- of these the stored ones: (which, position) -/
def xWanted (a : Nat) (ds : List RD) (xs : List XO) (Ds : List _root_.Fmt.Drawn) :
    List (Bool × Nat) :=
  (wantedX a ds xs Ds).filterMap fun kx =>
    if kx.1 = storedKey false then some (false, kx.2)
    else if kx.1 = storedKey true then some (true, kx.2)
    else none

/-- every symbol read carries the position at which it was read -/
def symbolsCarryTheirPositions (a : Nat) (ds : List RD) (xs : List XO)
    (Ds : List _root_.Fmt.Drawn) (y : (twoExternalStrings (2 ^ a) SgX).Str) : Bool :=
  (xWanted a ds xs Ds).all fun wx => match xPos (2 ^ a) wx with
    | none => false
    | some p => ((twoExternalStrings (2 ^ a) SgX).rd y p).1 == wx.2

/-- The view -/
def viewX (C : CK) (ds : List RD) (a : Nat) (xs : List XO)
    (y : (twoExternalStrings (2 ^ a) SgX).Str) (τ : Iop.Tr (uL C ds)) : View where
  rounds := rvSL C ds τ
  opened := (wantedX a ds xs (drawnSL C ds (rhoSL C ds τ))).filterMap fun kx =>
    if kx.1 = storedKey false then
      (xPos (2 ^ a) (false, kx.2)).map fun p => (kx.1, kx.2, ((twoExternalStrings (2 ^ a) SgX).rd y p).2)
    else if kx.1 = storedKey true then
      (xPos (2 ^ a) (true, kx.2)).map fun p => (kx.1, kx.2, ((twoExternalStrings (2 ^ a) SgX).rd y p).2)
    else (colAtS C ds τ kx.1 kx.2).map fun c => (kx.1, kx.2, c)

/-- The limits, a test on the description: every external opening stands behind a round that is
there; the strings are no longer than the round's range; IN A ROUND WITH EXTERNAL OPENINGS THE PARTS
LIE ONE BEHIND THE OTHER FROM THE FIRST DRAW ON AND USE UP ALL DRAWS (the page's R7.19), AND NO TREE
OF THE CHAIN'S OWN IS OPENED THERE; THE FIRST STRING'S OPENINGS STAND BEFORE THE SECOND'S in xs; the
chain's own trees have numbers below the keys -/
def okX (ds : List RD) (a : Nat) (xs : List XO) : Bool :=
  (xs.all fun o => match ds[o.round]? with
    | none => false
    | some d => decide (a ≤ d.entry.logN)) &&
  (ds.zipIdx.all fun d =>
    (xsAt xs d.2).isEmpty ||
      (d.1.opens.isEmpty && partsX 0 (xsAt xs d.2) == some d.1.entry.poss)) &&
  (xs.map (·.which)) ==
    (xs.filter (!·.which)).map (·.which) ++ (xs.filter (·.which)).map (·.which) &&
  ds.all fun d => d.opens.all (· < 2 ^ 16)

/-- The skeleton of the protocol with two external strings. -/
@[reducible] def skeletonOverBothExternalStrings (C : CK) (ds : List RD) (a : Nat) (xs : List XO) (dec : View → Bool) :
    PS Unit (twoExternalStrings (2 ^ a) SgX) where
  S := SOf C ds
  blinded := fun _ => true
  extReads := fun _ ρ => ((xWanted a ds xs (drawnSL C ds ρ.2)).filterMap (xPos (2 ^ a))).toFinset
  reads := fun _ ρ _ =>
    (((wanted ds (drawnSL C ds ρ.2)).filterMap fun nx =>
      (posAtS C ds nx.1 nx.2).map fun p => (Sum.inr p : OPos (Twin.up (SOf C ds))))).toFinset
  accept := fun _ y τ =>
    passSL C ds (rhoSL C ds τ.2.2) && everyOpeningHasItsDraws xs (drawnSL C ds (rhoSL C ds τ.2.2)) &&
      symbolsCarryTheirPositions a ds xs (drawnSL C ds (rhoSL C ds τ.2.2)) y && dec (viewX C ds a xs y τ.2.2)
  ann := Twin.allLo (SOf C ds)

def wqX (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (ds : List RD) (a : Nat)
    (xs : List XO) (dec : View → Bool) :
    ProtocolQueryLayout 256 (K + 1) (skeletonOverBothExternalStrings C ds a xs dec).up :=
  ⟨(wire0S C K chal, wiresSL C K chal ds), weX a, decOS C ds,
    nOpen ds + (xs.map (·.count)).sum, max (maxDepth ds) a⟩

section
variable {I RI : Type} [Fintype RI] [Nonempty RI]

/-- The interface whose Link is the protocol. -/
@[reducible] def LkX (Bd : Type) (C : CK) (ds : List RD) (a : Nat) (xs : List XO)
    (dec : View → Bool)
    (enc : I → RI → Fin (2 ^ a) → SgX) (dcd : (Fin (2 ^ a) → SgX) → Option I) : BatchProtocolWithLeafBody I Unit where
  Bd := Bd
  annT := RoundSplits.allLocal _
  annL := RoundSplits.allLocal _
  wordLength := 2 ^ a
  Symbol := SgX
  EncodingRandomness := RI
  encodeIndex := enc
  decodeIndex := dcd
  offline := pT1 (2 ^ a)
  link := (skeletonOverBothExternalStrings C ds a xs dec).up.loc
  maxBatchSize := 1
  onlineBatch := BatchInteractiveOracleProof.ofProto (pT1 (2 ^ a))
  honestOfflineProver := dummyH _ fun w => enc w.1 w.2
  honestLinkProver := dummyH _ fun w => (enc w.1 w.2.1, enc w.1 w.2.2)
  honestOnlineBatchProver := dummyB _ fun w => enc w.1 w.2
  early := id
  late := none

/-- a plain part of the whole shape, carried over to the interface's Link -/
def embPX (Bd : Type) (C : CK) (ds : List RD) (a : Nat) (xs : List XO) (dec : View → Bool)
    (enc : I → RI → Fin (2 ^ a) → SgX) (dcd : (Fin (2 ^ a) → SgX) → Option I) :
    PlainPart (Twin.up (SOf C ds)) (Twin.allLo (SOf C ds)) →
    PlainPart (Compile.Batch.shapeOf (LkX Bd C ds a xs dec enc dcd) .link)
      (Compile.Batch.annOf (LkX Bd C ds a xs dec enc dcd) .link)
  | .inl x => .inl x
  | .inr q => .inr (embPL C ds q)

end

/-! ## Typing what the reader holds -/

/-- what the parser asks of the protocol: as in TYS -/
def TYX (salt : Nat) (C : CK) (ds : List RD) (a : Nat) (xs : List XO) (dec : View → Bool) :
    TypingP (skeletonOverBothExternalStrings C ds a xs dec) where
  saltBytes := salt
  plains := fun os => (plainsSL C ds os.toList).map fun r => ((), r)
  place := fun p => match p with
    | .inl e => e.elim
    | .inr q => placeSL C ds q
  sym := fun p l => match p with
    | .inl e => e.elim
    | .inr q => symSL C ds q l

/-- From what the reader with stored tables holds to the typed Link string. -/
def toBPrfX (salt : Nat) (cfg : ByteArray) (C : CK) (ds : List RD) (a : Nat) (xs : List XO)
    (dec : View → Bool) (o : _root_.Fmt.ChainOut) :
    Option (OneProtocolProof 256 (skeletonOverBothExternalStrings C ds a xs dec).up) :=
  if (storedB xs o).all (fun x => x.2.2.ok salt x.2.1 && x.2.2.a == a) then
    (toBPrfP (skeletonOverBothExternalStrings C ds a xs dec) (TYX salt C ds a xs dec) (offStored xs o)).map fun z =>
      { z.2 with ext := extOf a cfg ((storedB xs o).map fun x => (x.1, x.2.2, x.2.2.paths)) }
  else none

end TypedOracleCompiler.Run.PQ
