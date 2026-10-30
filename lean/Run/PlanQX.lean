-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQX.lean: a protocol made from a description of a proof's rounds, which reads two stored
tables as external oracles and is an interface's Link protocol.

Run/PlanQS.lean turns a description of a proof's rounds into a protocol of the library, with a
wiring and a verifier that can be evaluated. There every Merkle tree is one whose root the prover
sends in the proof itself (the chain's own trees). An entry file also opens two stored tables, whose
roots are outside the proof: the first table's in the key, the copy's at the head of the file (the
copy: the further stored table, whose root the entry file holds; second item of `stmOf`,
Fmt/M3Plan.lean). This file adds them as the two external oracles of the library's Link protocol
(the link's purpose: to show that the copy holds the same table as the first, if that is well
formed: Fmt/M3Entry.lean). It is a layer on Run/PlanQS.lean: rounds, shape, the view's rounds and
own columns (`rvSL`, `colAtS`) and the wiring of the own trees are that file's, unchanged. Each
external string has 2^a symbols, for a stored tree of depth a.

An interface (`BatchProtocol`, Iop/Batch.lean) is the record that the library's compiler takes: an encoding
and a decoder of an index, and three interactive oracle protocols, Test, Link and Batch, with their
honest sides; Link has two external strings. A wiring (`ProtocolQueryLayout`, Iop/BatchWire.lean) is the data
that say how deep the trees are, where a position stands among a tree's leaves, and how blocks of a
hash answer give a verifier message. A view (`View`, Fmt/View.lean) has, for each round, the items
read and what was drawn, and the list "opened" of the opened columns.

Sources. The order and the lists of the openings were written against the format page
(docs/format/FORMAT.md, which comes with the programs), rules R7.19 and R8.7,
and R4.6 for the
statement's items. This file has not been held against the page as it ships, and may differ from
it, for instance at R7.19; according
to a restatement, in a clause on the record of vertices met, which this file does not render. The
programs are the C++ implementation that comes with this Lean code.

1. What the file contains.
   `SgX`: a symbol of a stored table's string: its position and its column. Why the position is part
     of the symbol: the library's leaf of an external tree holds the symbol alone, while the format
     hashes a stored leaf under its place. (The same device as in Run/ToyX.lean.)
   `XO`: an opening of a stored table: the round whose drawn positions it follows; which of the two
     strings; its part of the draws (from, count).
   `storedKey which`: the key under which a stored tree's columns are listed in a view's list
     "opened". It is the reader's key (Fmt/Rules8X.lean: 2^16 + the number of the statement's item).
     So the view keeps its type, and a decision is a function `View → Bool` as in Run/PlanQS.lean.
     The two strings are the statement's items 0 and 1 (FORMAT.md, R4.6: the stored tables' items
     stand before a statement's other items, one item a table); `XO` has no field for an item.
   `wantedX a ds xs Ds`: what the drawn positions ask for, round by round: first the stored trees,
     in the order of xs; then the own trees.
   `everyOpeningHasItsDraws`, `symbolsCarryTheirPositions`: two tests inside the verifier. A part has as many draws as it says, so
     nothing is shortened silently. Every symbol read carries the position at which it was read.
   `viewX`: the view: "opened" holds the stored columns under their keys, among the own trees'
     columns.
   `partsX`, `okX ds a xs`: the limits, as a test on the description. Among them FORMAT.md's R7.19:
     the first n_1 draws go to one tree, the next n_2 to the next, and their sum is the plan's
     number. Two limits are this library's own.
     (i) A round with openings of stored tables opens no tree of the chain's own. By the letter of
     R8.7 such a tree would have a part of its own. The entry file's description (`specX`,
     Fmt/M3Plan.lean) has not the case, so it is refused, which is the smaller promise. What
     `wantedX` says for that case is idle within `okX`.
     (ii) Strings shorter than the round's range are read at the draws modulo 2^a (by `XO.list`;
     `okX` itself tests that a string is no longer than the range). This is idle where range and
     depth agree. (For the chain's own trees an edition of FORMAT.md has that rule,
     R13.12, not held against the page that ships; for
     stored trees it is this library's own.)
     No definition or theorem of this file asks for `okX`; the run function tests it first
     (Run/PlanQXRun.lean: `D.ok`).
   `skeletonOverBothExternalStrings C ds a xs dec`: the protocol. C, K, chal: as in Run/PlanQS.lean (`CK`:
     Run/PlanQTypes.lean). Shape, reads of own trees and annotation are Run/PlanQS.lean's. The
     external reads are the set of `xWanted`. It accepts if the proof-of-work tests, `everyOpeningHasItsDraws` and
     `symbolsCarryTheirPositions` pass and dec accepts `viewX`.
   `weX a`: the wiring of the two strings: the library's `WireE.two`, with one walk over a pruned
     set of paths.
   `wqX`: the wiring of the protocol. The count of openings and the greatest depth include the
     external ones.
   `LkX`: the interface. Index type, encoding randomness (a finite, nonempty type), encoding and
     decoder are parameters. Test and Batch have no rounds. The honest sides are placeholders.
   `embPX`, `VPX`: the evaluable form of the compiled verifier (Run/ThinExtReads.lean: `verifyPX`,
     which has a fast test for "is position p read?").
   `TYX`, `offStored`, `storedB`, `extOf`, `toBPrfX`: from what the reader of Fmt/Rules8X.lean has
     read (the `ChainOut` of `wholeChainX`) to a proof string of the library's type. An external
     opening at p has the symbol (p, column), the salt "the configuration's digest, then the file's
     salt", and a whole path filled in from the pruned set.

2. What is checked when the file compiles. Eight tests (#guard) on made-up data: the two parts'
   lists (a position drawn for both strings stands under both keys); `okX` and `everyOpeningHasItsDraws` at that data;
   the limits refuse a round that is not there, a part beyond the draws, strings longer than the
   range, the second string's opening before the first's, a gap, an overlap, draws that nobody
   reads, a part that does not begin at the first draw, and an own tree in a round that is cut; a
   symbol that carries another position is noticed.

3. Theorems. Many statements of this library are written twice: a definition in the namespace `Spec`
   states a proposition, and a theorem of the same name outside that namespace proves it
   (lean/GLOSSARY.md).
   `vpx_eq`: for all arguments (the type RI of the encoding randomness finite and nonempty): VPX ..
     = (Compile.Batch.verifyOneProtocol .. Tag.link (skeletonOverBothExternalStrings ..).up (wqX ..) .. [cm, cm'] () π).det g.

Notation:
  `sMT`: the length of the salt of a leaf (Compile/Batch/Verifier.lean);
  `C`: a choice of challenge types: for each round the type of the verifier's message
    (Run/PlanQS.lean);
  `K`: the number of blocks from which a verifier message is made;
  `chal`: the samplers, from `K` 256-bit blocks to a verifier message;
  `ds`: a list of rounds' data (`List PQ.RD`, Run/PlanQTypes.lean);
  `g`: the typed oracle functions, one for each oracle name (`Fam`, Rom/OSpec.lean);
  `.det g`: the run's result under g, every coin toss yielding 0 (`OComp.det`, Rom/Cache.lean).

4. What is not claimed, or stands elsewhere.
   A whole wiring of the interface, and `Compile.Batch.vLS` itself, are not here. Link's wiring is
   typed at the library's annotation "all rounds local", which is by definition this file's
   annotation only at a closed list of rounds. At a closed list: Run/ToyLk.lean (`vls_toy`).
   How typed queries are spelled as hash calls: Run/PlanQXRun.lean. The laws of the wiring, and that
   the verifier is local: Run/PlanQXLaws.lean.
   No encoding and no decoder is given. No statement on soundness follows. The library has a link
   protocol with soundness statements (Cb/Ld/LdLink.lean); nothing in Run/ or Fmt/ connects it with
   the protocol of this file.
   That `viewX` is the view that the reader forms is not proved. (Run/ToyLk.lean tests, at one file,
   that the reader's list "opened" has the keys and positions of `wantedX`, in the same order; it
   does not compare the two views.)
   Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PlanQS
-- Run.PlanPullProto, and not Run.PlanPullFace above it: that module imports CompileK, and with it
-- Top, of which this file needs nothing.
import Run.PlanPullProto
import Run.ThinExtReads
import Fmt.Rules8X

set_option autoImplicit false

namespace Run.PQ
open Iop Rom Compile Compile.Batch
open Run.Twin (RS PS)

/-- a symbol: its position, its column -/
abbrev SgX : Type := Nat × List UInt64

/-- an external opening -/
structure XO where
  round : Nat
  which : Bool
  from_ : Nat
  count : Nat

/-- the key under which a stored tree's columns stand in a view's list "opened" -/
def storedKey (which : Bool) : Nat := _root_.Fmt.storedKey (if which then 1 else 0)

/-- an opening's part of a round's draws, as drawn -/
def XO.raw (o : XO) (D : _root_.Fmt.Drawn) : List Nat := (D.poss.drop o.from_).take o.count

/-- the list at which the string is read: sorted, each position once, modulo the strings' length -/
def XO.list (a : Nat) (o : XO) (D : _root_.Fmt.Drawn) : List Nat :=
  _root_.Fmt.listOf ((o.raw D).map (· % 2 ^ a))

/-- the external openings of round i -/
def xsAt (xs : List XO) (i : Nat) : List XO := xs.filter (·.round == i)

/-- What the drawn positions ask for, as pairs (key, position). -/
def wantedXL (a : Nat) (all : List RD) (xs : List XO) :
    Nat → List RD → List _root_.Fmt.Drawn → List (Nat × Nat)
  | i, d :: ds, D :: Ds =>
    ((xsAt xs i).flatMap fun o => (o.list a D).map fun x => (storedKey o.which, x)) ++
    (d.opens.flatMap fun n =>
      match treeSh all n with
      | none => []
      | some s => (_root_.Fmt.listOf (D.poss.map (· % 2 ^ s.a))).map fun x => (n, x)) ++ wantedXL a all xs (i + 1) ds Ds
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

def xPos (n : Nat) (wx : Bool × Nat) : Option (Fin n ⊕ Fin n) :=
  if h : wx.2 < n then some (if wx.1 then .inr ⟨wx.2, h⟩ else .inl ⟨wx.2, h⟩) else none

/-- Nothing is shortened in silence: every opening's part has as many draws as it says. -/
def everyOpeningHasItsDraws (xs : List XO) (Ds : List _root_.Fmt.Drawn) : Bool :=
  xs.all fun o => match Ds[o.round]? with
    | none => false
    | some D => (o.raw D).length == o.count

/-- every symbol read carries the position at which it was read -/
def symbolsCarryTheirPositions (a : Nat) (ds : List RD) (xs : List XO)
    (Ds : List _root_.Fmt.Drawn) (y : (twoExternalStrings (2 ^ a) SgX).Str) : Bool :=
  (xWanted a ds xs Ds).all fun wx => match xPos (2 ^ a) wx with
    | none => false
    | some p => ((twoExternalStrings (2 ^ a) SgX).rd y p).1 == wx.2

/-- The view. -/
def viewX (C : CK) (ds : List RD) (a : Nat) (xs : List XO)
    (y : (twoExternalStrings (2 ^ a) SgX).Str) (τ : Iop.Tr (uL C ds)) : View where
  rounds := rvSL C ds τ
  opened := (wantedX a ds xs (drawnSL C ds (rhoSL C ds τ))).filterMap fun kx =>
    if kx.1 = storedKey false then
      (xPos (2 ^ a) (false, kx.2)).map fun p => (kx.1, kx.2, ((twoExternalStrings (2 ^ a) SgX).rd y p).2)
    else if kx.1 = storedKey true then
      (xPos (2 ^ a) (true, kx.2)).map fun p => (kx.1, kx.2, ((twoExternalStrings (2 ^ a) SgX).rd y p).2)
    else (colAtS C ds τ kx.1 kx.2).map fun c => (kx.1, kx.2, c)

/-- If the parts follow one another, without gap or overlap, from draw number i on: the number of
the draw after the last part; else none. -/
def partsX : Nat → List XO → Option Nat
  | i, [] => some i
  | i, o :: os => if o.from_ == i then partsX (i + o.count) os else none

/-- The limits, a test on the description: every external opening stands behind a round that is
there; the strings are no longer than the round's range; in a round with external openings the parts
lie one behind the other from the first draw on and use up all draws (the page's R7.19), and no tree
of the chain's own is opened there; the first string's openings stand before the second's in xs; the
chain's own trees that are opened have numbers below the keys. -/
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

/-- The skeleton (`PS`, Run/TwinDefs.lean) of the protocol with two external strings. -/
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

/-- the wiring of the two strings -/
def weX (a : Nat) : WireE (twoExternalStrings (2 ^ a) SgX) :=
  { WireE.two (2 ^ a) SgX (0, []) with pr := true, depth := a }

def wqX (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (ds : List RD) (a : Nat)
    (xs : List XO) (dec : View → Bool) :
    ProtocolQueryLayout 256 (K + 1) (skeletonOverBothExternalStrings C ds a xs dec).up :=
  ⟨(wire0S C K chal, wiresSL C K chal ds), weX a, decOS C ds,
    nOpen ds + (xs.map (·.count)).sum, max (maxDepth ds) a⟩

/-- protocols without a round on one string -/
@[reducible] def pT1 (n : Nat) : InteractiveOracleProof Unit (oneExternalString n SgX) :=
  { shape := [], blinded := fun _ => false, extReads := fun _ _ => ∅,
    reads := fun _ _ _ => ∅, accept := fun _ _ _ => true }

section
variable {I RI : Type} [Fintype RI] [Nonempty RI]

/-- The interface whose Link is the protocol. -/
@[reducible] def LkX (C : CK) (ds : List RD) (a : Nat) (xs : List XO) (dec : View → Bool)
    (enc : I → RI → Fin (2 ^ a) → SgX) (dcd : (Fin (2 ^ a) → SgX) → Option I) : BatchProtocol I Unit where
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
def embPX (C : CK) (ds : List RD) (a : Nat) (xs : List XO) (dec : View → Bool)
    (enc : I → RI → Fin (2 ^ a) → SgX) (dcd : (Fin (2 ^ a) → SgX) → Option I) :
    PlainPart (Twin.up (SOf C ds)) (Twin.allLo (SOf C ds)) →
    PlainPart (Compile.Batch.shapeOf (LkX C ds a xs dec enc dcd) .link)
      (Compile.Batch.annOf (LkX C ds a xs dec enc dcd) .link)
  | .inl x => .inl x
  | .inr q => .inr (embPL C ds q)

/-- The evaluable form of the compiled verifier under two roots, at any typed oracle functions g. -/
def VPX (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (ds : List RD) (a : Nat)
    (xs : List XO) (dec : View → Bool) (enc : I → RI → Fin (2 ^ a) → SgX)
    (dcd : (Fin (2 ^ a) → SgX) → Option I) (g : Fam (spec 256 (K + 1) (LkX C ds a xs dec enc dcd)))
    (sMT : Nat) (cm cm' : Dig 256) (π : OneProtocolProof 256 (skeletonOverBothExternalStrings C ds a xs dec).up) : Bool :=
  Thin.verifyPX (lam := 256) (K := K + 1) (fun _ => LkX C ds a xs dec enc dcd) g
    (Thin.maskOf (Thin.idx2 (2 ^ a))) (Thin.maskBit (Thin.idx2 (2 ^ a))) id none sMT 256 .link
    (skeletonOverBothExternalStrings C ds a xs dec) (wqX C K chal ds a xs dec) (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
    (embPX C ds a xs dec enc dcd) (fun _ => none) (fun s => some (.inl s)) 0 [cm, cm'] () π

end

/-- States that, for all arguments (RI finite and nonempty), what runs (`VPX`) is the run of the
compiled verifier of one slot, at the tag "link", under the two roots. -/
def Spec.vpx_eq : Prop :=
  ∀ (I RI : Type) [Fintype RI] [Nonempty RI] (C : CK) (K : Nat)
      (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (ds : List RD) (a : Nat) (xs : List XO)
      (dec : View → Bool) (enc : I → RI → Fin (2 ^ a) → SgX) (dcd : (Fin (2 ^ a) → SgX) → Option I)
      (g : Fam (spec 256 (K + 1) (LkX C ds a xs dec enc dcd))) (sMT : Nat) (cm cm' : Dig 256)
      (π : OneProtocolProof 256 (skeletonOverBothExternalStrings C ds a xs dec).up),
    VPX C K chal ds a xs dec enc dcd g sMT cm cm' π =
      (verifyOneProtocol (lam := 256) (K := K + 1) (L := LkX C ds a xs dec enc dcd) sMT 256 .link
        (skeletonOverBothExternalStrings C ds a xs dec).up (wqX C K chal ds a xs dec)
        (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩)) (embPX C ds a xs dec enc dcd) (fun _ => none)
        (fun s => some (.inl s)) 0 [cm, cm'] () π).det g

theorem vpx_eq : Spec.vpx_eq := fun I _ _ _ C K chal ds a xs dec enc dcd g sMT cm cm' π =>
  Thin.thin_ext I Unit 256 (K + 1) (LkX C ds a xs dec enc dcd) g Unit (twoExternalStrings (2 ^ a) SgX)
    (Thin.idx2 (2 ^ a)) sMT 256 .link (skeletonOverBothExternalStrings C ds a xs dec) (wqX C K chal ds a xs dec) _ _
    (fun _ => none) (fun s => some (.inl s)) 0 [cm, cm'] () π (Thin.idx2_inj (2 ^ a))

/-! ## Typing what the reader holds -/

/-- what the parser asks of the protocol: as in Run/PlanQS.lean (`TYS`) -/
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

/-- the rounds with the stored trees' openings taken off (they stand first in a round) -/
def offStored (xs : List XO) (o : _root_.Fmt.ChainOut) : _root_.Fmt.ChainOut :=
  { o with
    rounds := (o.rounds.toList.zipIdx.map fun r =>
        { r.1 with opens := r.1.opens.drop (xsAt xs r.2).length }).toArray }

/-- the stored trees' openings, each with its string -/
def storedB (xs : List XO) (o : _root_.Fmt.ChainOut) : List (Bool × Nat × OpenB) :=
  o.rounds.toList.zipIdx.flatMap fun r =>
    ((xsAt xs r.2).zip r.1.opens).map fun y =>
      (y.1.which, y.2.1.W, ⟨y.2.1.a, y.2.2.1, y.2.2.2.cols, y.2.2.2.salts, y.2.2.2.given⟩)

/-- the opening at a position of the two strings -/
def extOf (a : Nat) (cfg : ByteArray) (tabs : List (Bool × OpenB × List (List (Dig 256))))
    (p : Fin (2 ^ a) ⊕ Fin (2 ^ a)) : Option (Opening 256 SgX) :=
  let w := p.elim (fun _ => false) fun _ => true
  let x := p.elim (·.val) (·.val)
  (tabs.lookup w).bind fun O => O.1.atP (fun c => some (x, c)) cfg O.2 x

/-- From what the reader with stored tables holds to the typed Link string. -/
def toBPrfX (salt : Nat) (cfg : ByteArray) (C : CK) (ds : List RD) (a : Nat) (xs : List XO)
    (dec : View → Bool) (o : _root_.Fmt.ChainOut) :
    Option (OneProtocolProof 256 (skeletonOverBothExternalStrings C ds a xs dec).up) :=
  if (storedB xs o).all (fun x => x.2.2.ok salt x.2.1 && x.2.2.a == a) then
    (toBPrfP (skeletonOverBothExternalStrings C ds a xs dec) (TYX salt C ds a xs dec) (offStored xs o)).map fun z =>
      { z.2 with ext := extOf a cfg ((storedB xs o).map fun x => (x.1, x.2.2, x.2.2.paths)) }
  else none

end Run.PQ

/-! ## Tests of the definitions: made-up data -/

namespace Run.PQ.XG
open Run.PQ

def d0 : RD := ⟨{ name := "LINK", poss := 5, logN := 2 }, .positions, [], none, []⟩
def xs : List XO := [⟨0, false, 0, 2⟩, ⟨0, true, 2, 3⟩]
def D0 : _root_.Fmt.Drawn := ⟨[], [3, 1, 3, 3, 0], [], none⟩

-- the first two draws are the first string's, the last three the second's; each part's own list: sorted, each position once WITHIN the part; position 3 is drawn for both and stands under both keys
#guard wantedX 2 [d0] xs [D0] = [(65536, 1), (65536, 3), (65537, 0), (65537, 3)]
#guard xWanted 2 [d0] xs [D0] = [(false, 1), (false, 3), (true, 0), (true, 3)]
#guard okX [d0] 2 xs && everyOpeningHasItsDraws xs [D0]
-- the limits bite: a round that is not there; a part beyond the draws; strings longer than the round's range; the second string's opening before the first's
#guard !okX [d0] 2 [⟨1, false, 0, 2⟩] && !okX [d0] 2 [⟨0, false, 4, 2⟩] && !okX [d0] 3 xs && !okX [d0] 2 xs.reverse
-- R7.19: a gap between the parts; parts that overlap; draws that nobody reads; a part that does not
-- begin at the first draw: refused.
-- This library's own: an own tree opened in a round that is cut: refused
#guard !okX [d0] 2 [⟨0, false, 0, 2⟩, ⟨0, true, 3, 2⟩] && !okX [d0] 2 [⟨0, false, 0, 3⟩, ⟨0, true, 2, 3⟩] && !okX [d0] 2 [⟨0, false, 0, 2⟩] && !okX [d0] 2 [⟨0, false, 1, 4⟩] && !okX [{ d0 with opens := [0] }] 2 xs
-- nothing is shortened in silence
#guard !everyOpeningHasItsDraws [⟨1, false, 0, 2⟩] [D0] && !everyOpeningHasItsDraws [⟨0, false, 4, 2⟩] [D0]
-- a symbol that carries another position is seen
#guard symbolsCarryTheirPositions 2 [d0] xs [D0] (fun p => (p.val, [7]), fun p => (p.val, [8]))
#guard !symbolsCarryTheirPositions 2 [d0] xs [D0] (fun p => (p.val, [7]), fun p => (if p.val = 3 then 2 else p.val, [8]))

end Run.PQ.XG
