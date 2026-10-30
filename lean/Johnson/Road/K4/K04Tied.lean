-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K04Tied.lean: K4's PIECE AT THE PROOF FILE's DESCRIPTION IS TIED AT THE TABLE OF
JOINTS, AT EACH OF THE TWELVE GROUPS, UNDER NAMED LINES; AND SO THE KIND K4's SHARE OF THE CHAIN OF
PROMISES (`KindTied … K4`). Two Lean structures, definitions and theorems: a joining of other
files' rules; no new argument.

OBJECT: q: the piece at number 28 g + 4 of the first row of three rows of pieces that hold the
blocks of the description `descAt Z A B c` (`OfDesc`); its block is the strict reading, lifted over
the public part, of the block that `k04_sits_desc` (K04Sits.lean) names. USER: `k04_law_of`
(Johnson/Road/K4/K04LawOf.lean) calls `k04_kindTied_own`; meant: the chain of promises, whose entry
k is `TiedBy` (Johnson/Desc/Sound/TiedBy.lean). LETTERS: the table's (links, ps, N, Mg), its
extractor E, the three rows T, the value's (U but for the four that `seatU` fixes, part, dec): data
of the structures; lw: free; the table of scales: a letter in all but `k04_kindTied`, pinned by
hscl.

  `hearsAs_seatOf`: a block that narrows the lot's block `ProofFile.k4Block x` hears as K4's own block at
    the first chain's verifier's state: `hearsAs_of_yes` over `ProofFile.k4Block_under`.
  `seatU U X x`: the reference value's letters with four fixed by make: the layout is the public
    parameters', the seat the first chain's verifier's state, n0 the number of elements that the
    lookup hears, ns the plan's number of slots: so four premises of `RefSeat.k4_own_refS` (hU, hy,
    hn, hQ) are concluded, at first := 0 and Q3 := `LeftQ (parOf x).hp.ns`
    (Johnson/Desc/First/Look/K3LeftItem.lean).
  `K4PieceAt q ds`: three facts on the piece, which read no value of the public part: its rounds are
    ds, no round behind them, its errors are the cap.
  `K4Asks`: WHAT IS ASKED AT A MEMBER x OF THE LOT's LIST AND A VALUE z OF THE PUBLIC PART, as one
    structure WHOSE DATA MAY ALL HANG ON z (dec must: the table's item on the stored table is meant
    to decode it with what the key file publishes on that table, which stands in the public part;
    one dec for every z could not be met): all premises of `RefSeat.k4_own_refS` (CloseAtTable.lean)
    but these four, the piece's three, hscl, hg, `PublicSteps`, Ex, fe, lw, hP, hG, `HearsAs`,
    `AtK4`, the block and the extractor, at X := G₀.W and p := `parOf x`, at that z and every block
    B' that narrows the lot's block and whose yes bears no mark (`SeatOf`); and `K4Riders`
    (K4RidesFenced.lean) likewise.
  `seatLaws_k4`: `SeatLaws links ps k q N Mg (ProofFile.k4Block x)` (Johnson/Desc/Sound/TiedSeat.lean):
    the four things that the table's tie asks of a kind at a seat: (1) the row's own law:
    `RefSeat.k4_own_refS` · (2) what rides, fenced: `k4_rides_fenced` · (3) a mark stays:
    `mark_stays` (K4AtTable.lean) · (4) "decodes" rides: `K4Keeps`' line dec, which is asked at a
    yes, with no fence.
  `K4AsksF`, `seatLaws_k4F`: the like at the first group: `RefSeat.k4_own_refSF`
    (CloseAtTableFirst.lean) for the row's own law: the rounds are `dsFirst`, the value and the
    letters the first group's (`atRecF`, `lettersOfF`); no bound on the group; THREE PUBLIC LINES
    MORE: hla ((layerShape X.P).la = 16), hV (the vocabulary is ppref's), NE (`EmbNums`). The other
    three of the four are the same calls: they name no group.
  `K4Here c Z G₀ g x b`: what comes with the lot's member of group g: the membership, the group, the
    segment's number (2 g), what `par_sits` says, and the block: b is entry 28 g + 4 of c's flat
    list, not the last, and declares K4's rounds at x's parameters.
  `k04_tied_of_laws`: at an opening of the description, in the goals' scope, g < 12: if `SeatLaws`
    holds at every x that comes with some b under `K4Here`, and the table's extractor lays nothing
    at this row, then q with that extractor is tied at the table's own words: `K3Lot.tied_of_alone`.
  `k04_tied`, `k04_tiedF`: the same under `K4Asks` where g is not 0, under `K4AsksF` where it is.
  `K4OwnAt`, `seatLaws_k4_own`, `k04_kindTied_own`: ONE FORM FOR ALL TWELVE GROUPS:
    `SeatLaws` reads four things alone: the piece's own law at every narrowing block and public
    part, the riders, that a mark stays (no premise), and "the stored table decodes" past a yes: so
    whoever has a theorem that ends in the piece's own law can spend it here: no table of scales, no
    type of messages, no `K4Lines` in that top.
  `k04_places_full` (K04Places.lean, cut out of this file; called here): at the driver's WRITTEN
    list of places for the full list of segments, `flatPlacesOf linksFull true`: an entry of the
    kind K4 stands at a number 28 g + 4, g < 12, and is the address (1, 2 g, 3, K4): SO THE TWELVE
    ARE ALL THE PLACES OF THE KIND IN THAT LIST. By the kernel (`decide +kernel`), after the model
    `K3Lot.k03_places_full`.
  `k4HereB`, `k4HereB_full`, `atK4_full`: the other way round, by the kernel too: at g < 12 the
    written list has that address at number 28 g + 4, and the list of segments a layers' segment at
    2 g: `AtK4 linksFull (flatPlacesOf linksFull true) (28 g + 4) (2 g) (k4PlaceAt g)`: SO IN
    `k04_kindTied` THE TABLE's k, m AND pl ARE TIED TO g.
  `k04_kindTied`: `KindTied N Mg linksFull (flatPlacesOf linksFull true) E (T.p₁ :: T.l₁) K4`: every
    piece of the first row that stands at a number at which that list names the kind K4 is tied
    there: the form in which `eachTied_of_kinds` takes a kind's share (both in
    Johnson/Desc/Sound/TiedPlaces.lean).
  `k04_kindTied_tiled`: the same at rows that tile the first chain's data: of `K4PieceAt`'s three,
    the rounds and «no round behind» are CONCLUDED at all twelve places (`k04_piece_later`,
    `k04_piece_first`); in their place: hD, ht, hd, three lines on T; hcap stays.

Limits. K04_law IS NOT PROVED BY THIS. `K4Asks` AND `K4AsksF` ARE PREMISES, WHOLE: they are shown at
no filling of the table's meaning and at no place. THEY HAVE BEEN HELD AGAINST THE MEANT
FILLING BY READING. FOUR FAULTS ARE MENDED HERE OR BENEATH (one table of scales
for all groups; one dec for every value of the public part; `K4Riders`' line same asked outside the
promise; `K4Keeps`' line dec fenced where the tie's fourth clause has no fence), AND A FIFTH:
`K4Lines`' line wo could not be met at its layer's sentence, which holds of every witness
where the link's frame's reader gives no row: `K4Lines` takes the table's promise behind the
block (here `onQ … (k + 1)`), in which the public item hasRow stands. ONE CLASH IS KNOWN AND STANDS,
IN THE FIRST GROUP ALONE: `K4Lines`' line idn, as `K4AsksF` asks it, wants a tie of the verifier's
state's own request's words (of which the seat's tokens are a function) to the public part's
request, and neither the promise in front nor the four read items hold one: AS WORDED IT CANNOT BE
MET AT THE MEANT FILLING. A cure beside the table: one conjunct more of
the meaning's inOrder: the state's request's words are the public part's; it is not beneath this
file, and each kind then owes that its yes leaves these words. SO `k04_tiedF`, AND WITH IT
`k04_kindTied`, HOLD FOR NOTHING THERE. NOT HELD AGAINST THE MEANT FILLING: `K4Keeps`' lines pub and
pubP; `K4Lines`' lines forms, wo, planes, keys, rider, and idn in the later groups; `K4Riders`' line
objects. NO MEMBER OF `K4Lines` OR OF `K4Riders` IS TYPED. ASKED AT ALL STATES OF THE
VERIFIER, with no fence: `K4Front`'s lines left, look, leftOn; `K4Lines`' line pin. SO K4's TWELVE
PIECES MAY NOT BE COUNTED AS TIED. CONCLUDED IN THE TOPS, no line: `PublicSteps`
(`publicSteps_of` at the opening), the bound on the group, that the table of scales is the member's
group's; fixed by make: Ex := Fr.E, fe := the strings; lw is a letter under «for all». WHAT STAYS,
among the structures' lines: `RefPub` (`refPub_in_scope`, Johnson/Road/K4/RefInScope.lean, has it in
the goals' scope at every g < 12; not called here) · for the
first group hla, hV, NE (theorems of other files in the goals' scope; not called here) · `K4Front`,
`K4Keeps`, `K4Lines`, `K4Riders`, the structures being asked at every z, two of these four at every
such B'. THE PIECE's THREE (`K4PieceAt`): its rounds are K4's, no round behind them, its errors are
the cap: in `k04_kindTied` T is a letter: the three, and the piece's base at which `K4Keeps`,
`K4Lines`, `K4Riders` are asked, are lines on T; in `k04_kindTied_tiled` the first two are
concluded, at rows that tile the first chain's data; the errors' line can be met at the maker's own
rows alone, and the piece's base is tied to the table's Numbers by nothing. In `k04_kindTied`
eleven of the twelve places go through `K4Asks`, the first group's (number 4) through `K4AsksF`,
EACH ASKED AT ITS OWN GROUP's TABLE OF SCALES (`sclX Bs.G₀.W g`): the tops below it ask that the
table is the group's (hscl), and the groups' tables differ wherever the scale file's words do: one
table for all groups could be met only where all groups have the same scales. `k04_places_full`
speaks of the written list: that the description's own flat list has these places is the driver's
law and is not called here. `OfDesc` and "onlineDescription returns" (inside the opening) are premises. The
seat, the wrappers, the flat list and the lift are other files', called. The reference sizes alone;
the second hash function `OnBytes.secondHashFunction` alone.

(Where this and lean/THEOREM.md differ,
the page holds.) Nothing on soundness.
-/
import Johnson.Road.K4.K04Places
import Johnson.Road.K4.K4RidesFenced
import Johnson.Road.K4.CloseAtTableFirst
import Johnson.Road.K4.PieceLater
import Johnson.Road.K4.PieceFirst
import Johnson.Desc.First.Look.K3LeftItem
import Johnson.P5K3R.SitsAny
import Johnson.Desc.Sound.TiedPlaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop Cb.Pv.Att Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End
open OnBytes OnBytes.K.Kc OnBytes.Flat OnBytes.Maker KObj
open OnBytes.Model (Fork Forest.elems)
open OnBytes.Model.Verify (Public layerShape)
open VerifiableInference.PlanWritten (PublicSteps publicSteps_of)
open VerifiableInference.OnPublicFiles (LeftQ)
open OnBytes.Desc.First.K4 (Par seatS blockAtS hearsAs_atS)
open _root_.Run (ckP)
open VerifiableInference.Desc (Block Link FileDescription KindName)
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers flatPlacesOf)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain.K04 (HearsAs hearsAs_of_yes)
open Inst.Model (Scl ppref)
open Meaning.Emb (EmbNums)
open Inst.Model.FFSeg (LW)

/-- **A block that narrows the lot's block hears as K4's own block at the first chain's verifier's
state.** -/
theorem hearsAs_seatOf {x : Bool × Par} {B' : Block S ProofFile.Cl} (h : SeatOf (ProofFile.k4Block x) B') :
    HearsAs seatS (parOf x) B' :=
  hearsAs_of_yes seatS (parOf x) (blockAtS (parOf x)) B'
    (fun s rs gs t hy => ProofFile.k4Block_under x s rs gs t (h.1.2 s rs gs t hy))
    (hearsAs_atS (parOf x))

/-- The test: at each of the twelve numbers the written list has K4's address, and the list of
segments a layers' segment at 2 g. -/
def k4HereB : Bool :=
  (List.range 12).all fun g =>
    decide ((flatPlacesOf linksFull true)[28 * g + 4]? = some (k4PlaceAt g)) &&
      decide (linksFull[2 * g]? = some ModelPart.layers)

set_option maxRecDepth 1000000 in
theorem k4HereB_full : k4HereB = true := by decide +kernel

/-- **`AtK4` at the written lists**: block number 28 g + 4 stands at piece 3 of the layers' segment
2 g, at K4's address there. -/
theorem atK4_full (g : ℕ) (hg : g < 12) :
    AtK4 linksFull (flatPlacesOf linksFull true) (28 * g + 4) (2 * g) (k4PlaceAt g) := by
  have h := List.all_eq_true.1 k4HereB_full g (List.mem_range.2 hg)
  obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h
  exact ⟨of_decide_eq_true h1, rfl, of_decide_eq_true h2, rfl⟩

variable {P W : Type} {Fr : Frame} [scl : Scl] {M : Type}

/-- The piece over the verifier's state that holds the strict reading of B', with q's base, rounds,
back and errors, and the identity as its extractor: as `SeatLaws` writes it. -/
abbrev twinOf (q : Piece (ckP .two) Fr (P × S) ProofFile.Cl W) (B' : Block S ProofFile.Cl) :
    Piece (ckP .two) Fr S ProofFile.Cl W :=
  ⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩

/-- The reference value's letters with four of them fixed: the layout is the public parameters', the
seat the first chain's verifier's state, n0 the number of elements that the lookup hears, ns the
plan's number of slots. -/
abbrev seatU (U : RefSeat M S) (X : Public) (x : Bool × Par) : RefSeat M S :=
  { U with
    y := X.layers.y, L := seatS, n0 := Forest.elems X.layers.y.fo, ns := (parOf x).hp.ns }

/-- **Three facts on the piece**, which read no value of the public part: its rounds are ds, it puts
no round behind them, its errors are the cap. -/
structure K4PieceAt (q : Piece (ckP .two) Fr (P × S) ProofFile.Cl W) (ds : List RDT) : Prop where
  hds : q.ds = ds
  hback : q.back = []
  hcap : q.err = Err.cap 128 (uLT (ckP .two) q.ds)

/-- **What is asked at a member x of the lot's list AND A VALUE z OF THE PUBLIC PART.** All its data
may hang on z. -/
structure K4Asks (X : Public) (x : Bool × Par) (links : List ModelPart)
    (ps : List VerifiableInference.Desc.Place) (k m : ℕ) (pl : VerifiableInference.Desc.Place)
    (q : Piece (ckP .two) Fr (P × S) ProofFile.Cl W) (N : Numbers) (Mg : Meaning P W) (M : Type)
    (hg : (parOf x).g < 12) (z : P) where
  U : RefSeat M S
  part : W → M
  dec : S × Fr.E.Str → M
  pl' : VerifiableInference.Desc.Place
  B : RefPub X (parOf x).g
  front : K4Front Mg z links ps m (parOf x).P.y.fo (parOf x).P.y.h.lmb 0
    (LeftQ (parOf x).hp.ns)
  keeps : ∀ B', SeatOf (ProofFile.k4Block x) B' →
    K4Keeps N Mg z links ps k m pl pl' (twinOf q B') (parOf x)
  lines : K4Lines N Mg z m ((seatU U X x).atRec X (parOf x) hg) part (parOf x)
    (((seatU U X x).atRec X (parOf x) hg).lettersOf part (parOf x) 0 (parOf x).P.y.fo
      (LeftQ (parOf x).hp.ns) (tableOn0 N Mg z links ps k) (keptS (parOf x))
      (tableCtx0 N Mg z m) dec) dec q.base (onQ N Mg links ps (fun s => (z, s)) (k + 1))
  riders : ∀ B', SeatOf (ProofFile.k4Block x) B' →
    K4Riders N Mg z links ps k m (twinOf q B') (parOf x)

/-- **What `SeatLaws` reads of K4's block at one public part**, as one Lean structure: the piece's
own law at every block that narrows the lot's, the riders, and "the stored table decodes" past a
yes. One form for all twelve groups. -/
structure K4OwnAt (x : Bool × Par) (links : List ModelPart) (ps : List VerifiableInference.Desc.Place)
    (k m : ℕ) (q : Piece (ckP .two) Fr (P × S) ProofFile.Cl W) (N : Numbers) (Mg : Meaning P W) (z : P) :
    Prop where
  own : ∀ B', SeatOf (ProofFile.k4Block x) B' →
    (twinOf q B').Own (onQ N Mg links ps (fun s => (z, s)) k)
      (onQ N Mg links ps (fun s => (z, s)) (k + 1)) (meansQ N Mg (fun s => (z, s)))
      (insQ links ps k) (outsQ links ps k)
  riders : ∀ B', SeatOf (ProofFile.k4Block x) B' →
    K4Riders N Mg z links ps k m (twinOf q B') (parOf x)
  dec : ∀ B', SeatOf (ProofFile.k4Block x) B' → ∀ a τ fo o G,
    Yes seatS (parOf x) (twinOf q B') a τ fo o G → Mg.decodes (z, a.1) (strsOf Fr a.2) →
    Mg.decodes (z, (behindOf seatS (twinOf q B') a τ o G).1)
      (strsOf Fr (behindOf seatS (twinOf q B') a τ o G).2)

omit scl in
/-- **`SeatLaws` at the lot's block from `K4OwnAt`**, where the piece puts no round behind. -/
theorem seatLaws_k4_own {x : Bool × Par} {links : List ModelPart}
    {ps : List VerifiableInference.Desc.Place} {k m : ℕ}
    {q : Piece (ckP .two) Fr (P × S) ProofFile.Cl W} {N : Numbers} {Mg : Meaning P W}
    (hback : q.back = []) (Q : ∀ z : P, K4OwnAt x links ps k m q N Mg z) :
    SeatLaws links ps k q N Mg (ProofFile.k4Block x) := by
  refine ⟨fun B' hB z => (Q z).own B' hB, fun B' hB z a τ b w i ha hu h hb' hr ho hi => ?_,
    fun B' hB a τ b h hm => ?_, fun B' hB z a τ b h hd => ?_⟩
  · exact k4_rides_fenced N Mg z ((Q z).riders B' hB) (q := twinOf q B') rfl (hearsAs_seatOf hB)
      hback a τ b w i ha hu h hb' hr ho hi
  · exact mark_stays (q := twinOf q B') rfl (hearsAs_seatOf hB) hback a τ b h hm
  · obtain ⟨_, fo, o, G, yy, rfl⟩ :=
      yes_of_out seatS (pc := twinOf q B') (hearsAs_seatOf hB) rfl hback a b τ h
    exact (Q z).dec B' hB a τ fo o G yy hd

/-- **The four things that the table's tie asks of a kind at a seat, at K4's lot's block.** -/
theorem seatLaws_k4 {X : Public} {x : Bool × Par} {links : List ModelPart}
    {ps : List VerifiableInference.Desc.Place} {k m : ℕ} {pl : VerifiableInference.Desc.Place}
    {q : Piece (ckP .two) Fr (P × S) ProofFile.Cl W} {N : Numbers} {Mg : Meaning P W}
    {pol KL : ByteArray} (hscl : scl = sclX X (parOf x).g) (hg : (parOf x).g < 12)
    (St : PublicSteps pol KL X) (lw : ℕ → LW Cb.Gl.E) (Pc : K4PieceAt q (dsLater (parOf x)))
    (Q : ∀ z : P, Nonempty (K4Asks X x links ps k m pl q N Mg M hg z))
    (at4 : AtK4 links ps k m pl)
    (hP : (parOf x).P = { X.layers with tokv := X.layers.tokv })
    (hG : X.G[(parOf x).g]? = some (parOf x).hp) (hg0 : ((parOf x).g == 0) = false) :
    SeatLaws links ps k q N Mg (ProofFile.k4Block x) := by
  refine ⟨fun B' hB z => ?_, fun B' hB z a τ b w i ha hu h hb' hr ho hi => ?_,
    fun B' hB a τ b h hm => ?_, fun B' hB z a τ b h hd => ?_⟩
  · obtain ⟨Q⟩ := Q z
    exact RefSeat.k4_own_refS hscl (seatU Q.U X x) rfl hg St Q.B hP hG hg0 rfl Fr.E B'
      (twinOf q B') Pc.hds (fun a => a.2) Q.part Pc.hback Pc.hcap lw (Nat.zero_add _).symm
      (fun F hF => Nat.le_succ_of_le (Nat.le_of_eq hF.2.1)) rfl (hearsAs_seatOf hB)
      (fun _ _ _ _ _ => rfl) N Mg z at4 Q.front (Q.keeps B' hB) Q.lines
  · obtain ⟨Q⟩ := Q z
    exact k4_rides_fenced N Mg z (Q.riders B' hB) (q := twinOf q B') rfl (hearsAs_seatOf hB)
      Pc.hback a τ b w i ha hu h hb' hr ho hi
  · exact mark_stays (q := twinOf q B') rfl (hearsAs_seatOf hB) Pc.hback a τ b h hm
  · obtain ⟨Q⟩ := Q z
    obtain ⟨_, fo, o, G, yy, rfl⟩ :=
      yes_of_out seatS (pc := twinOf q B') (hearsAs_seatOf hB) rfl Pc.hback a b τ h
    exact (Q.keeps B' hB).dec a τ fo o G yy hd

/-- **What is asked at the lot's member x of the first group and a value z of the public part.** As
`K4Asks`, at the first group's value and letters, with three public lines more. -/
structure K4AsksF (X : Public) (x : Bool × Par) (links : List ModelPart)
    (ps : List VerifiableInference.Desc.Place) (k m : ℕ) (pl : VerifiableInference.Desc.Place)
    (q : Piece (ckP .two) Fr (P × S) ProofFile.Cl W) (N : Numbers) (Mg : Meaning P W) (M : Type)
    (z : P) where
  U : RefSeat M S
  part : W → M
  dec : S × Fr.E.Str → M
  pl' : VerifiableInference.Desc.Place
  B : RefPub X (parOf x).g
  hla : (layerShape X.P).la = 16
  hV : (parOf x).P.V = ppref.V
  NE : EmbNums (parOf x).P.y
  front : K4Front Mg z links ps m (parOf x).P.y.fo (parOf x).P.y.h.lmb 0
    (LeftQ (parOf x).hp.ns)
  keeps : ∀ B', SeatOf (ProofFile.k4Block x) B' →
    K4Keeps N Mg z links ps k m pl pl' (twinOf q B') (parOf x)
  lines : K4Lines N Mg z m ((seatU U X x).atRecF X (parOf x)).toPlan4K part (parOf x)
    (((seatU U X x).atRecF X (parOf x)).lettersOfF part (parOf x) 0 (parOf x).P.y.fo
      (LeftQ (parOf x).hp.ns) (tableOn0 N Mg z links ps k) (keptS (parOf x))
      (tableCtx0 N Mg z m) dec) dec q.base (onQ N Mg links ps (fun s => (z, s)) (k + 1))
  riders : ∀ B', SeatOf (ProofFile.k4Block x) B' →
    K4Riders N Mg z links ps k m (twinOf q B') (parOf x)

/-- **The same four at K4's lot's block of the first group.** -/
theorem seatLaws_k4F {X : Public} {x : Bool × Par} {links : List ModelPart}
    {ps : List VerifiableInference.Desc.Place} {k m : ℕ} {pl : VerifiableInference.Desc.Place}
    {q : Piece (ckP .two) Fr (P × S) ProofFile.Cl W} {N : Numbers} {Mg : Meaning P W}
    {pol KL : ByteArray} (hscl : scl = sclX X (parOf x).g) (St : PublicSteps pol KL X)
    (lw : ℕ → LW Cb.Gl.E) (Pc : K4PieceAt q (dsFirst (parOf x)))
    (Q : ∀ z : P, Nonempty (K4AsksF X x links ps k m pl q N Mg M z))
    (at4 : AtK4 links ps k m pl)
    (hP : (parOf x).P = { X.layers with tokv := X.layers.tokv })
    (hG : X.G[(parOf x).g]? = some (parOf x).hp) (hg0 : ((parOf x).g == 0) = true) :
    SeatLaws links ps k q N Mg (ProofFile.k4Block x) := by
  refine ⟨fun B' hB z => ?_, fun B' hB z a τ b w i ha hu h hb' hr ho hi => ?_,
    fun B' hB a τ b h hm => ?_, fun B' hB z a τ b h hd => ?_⟩
  · obtain ⟨Q⟩ := Q z
    exact RefSeat.k4_own_refSF hscl (seatU Q.U X x) rfl St Q.B hP hG hg0 Q.hla rfl Fr.E B'
      (twinOf q B') Pc.hds (fun a => a.2) Q.part Pc.hback Pc.hcap lw (Nat.zero_add _).symm
      (fun F hF => Nat.le_succ_of_le (Nat.le_of_eq hF.2.1)) Q.hV Q.NE rfl (hearsAs_seatOf hB)
      (fun _ _ _ _ _ => rfl) N Mg z at4 Q.front (Q.keeps B' hB) Q.lines
  · obtain ⟨Q⟩ := Q z
    exact k4_rides_fenced N Mg z (Q.riders B' hB) (q := twinOf q B') rfl (hearsAs_seatOf hB)
      Pc.hback a τ b w i ha hu h hb' hr ho hi
  · exact mark_stays (q := twinOf q B') rfl (hearsAs_seatOf hB) Pc.hback a τ b h hm
  · obtain ⟨Q⟩ := Q z
    obtain ⟨_, fo, o, G, yy, rfl⟩ :=
      yes_of_out seatS (pc := twinOf q B') (hearsAs_seatOf hB) rfl Pc.hback a b τ h
    exact (Q.keeps B' hB).dec a τ fo o G yy hd

/-- **What comes with the lot's member of group g**, at a first chain c: x is a member of the lot's
list, of that group, at the public parameters' layers and the group's plan; b is entry number 28 g +
4 of c's flat list, not the last; b declares K4's rounds at x's parameters. -/
structure K4Here (c : VerifiableInference.Desc.Chain S ProofFile.Cl) (Z : ProofFile.Pub) (G₀ : ProofFile.Ground)
    (g : ℕ) (x : Bool × Par) (b : Block S ProofFile.Cl) : Prop where
  mem : x ∈ ProofFile.k4From Z G₀ G₀.built.toList 0 none
  hg : x.2.g = g
  link : x.2.link = 2 * g
  P : (parOf x).P = { G₀.W.layers with tokv := G₀.W.layers.tokv }
  G : G₀.W.G[(parOf x).g]? = some (parOf x).hp
  flat : c.blocksInOrder[28 * g + 4]? = some b
  more : 28 * g + 4 + 1 < c.blocksInOrder.length
  decl : Declares b (parOf x)

omit scl in
/-- **K4's piece at the proof file's description is tied at the table, at any of the twelve groups,
where `SeatLaws` holds at the lot's member of that group**: for public files in the goals' scope
that `VerifierAndGoals.readFiles` reads, at an opening of the proof file's description (so `onlineDescription` returns,
at the second hash function `OnBytes.secondHashFunction`), for three rows of pieces that hold that
description's blocks (`OfDesc`), the table's extractor laying nothing at this row (hE): the member
comes with what `par_sits` says of it. -/
theorem k04_tied_of_laws {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray}
    {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    {D : WholeD} {all : List LeftT} {X₁ X₂ W : Type}
    {T : ThreeAt (ckP .two) D all (descAt Z A B c) X₁ X₂ W} (hT : OfDesc _ T) (g : ℕ)
    (hg : g < 12)
    {q : Piece (ckP .two) (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) ProofFile.Cl W}
    (hq : (T.p₁ :: T.l₁)[28 * g + 4]? = some q) (links : List ModelPart)
    (ps : List VerifiableInference.Desc.Place) (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (E : (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (hE : ∀ a b w, E a b w = w)
    (H : ∀ x b, K4Here c Z Bs.G₀ g x b → SeatLaws links ps (28 * g + 4) q N Mg (ProofFile.k4Block x)) :
    TiedBy N Mg links ps (fun a => a) (28 * g + 4) (q.withMap E)
      (onQ N Mg links ps (fun a => a) (28 * g + 4))
      (onQ N Mg links ps (fun a => a) (28 * g + 4 + 1))
      (relAt (meansQ N Mg fun a => a) (insQ links ps (28 * g + 4)))
      (relAt (meansQ N Mg fun a => a) (outsQ links ps (28 * g + 4))) := by
  obtain ⟨Lk, b, x, e1, e2, e3, e4, e5, e6, _⟩ := IM.k4_of hS hR O g hg
  have Hs : K4SitsAt c Z Bs.G₀ g Lk b x := ⟨e1, e2, e3, e4, e6⟩
  have hi : IM.flatIx c (2 * g) 2 = 28 * g + 4 := by
    rw [IM.flatIx_scope hS hR O (by omega) 2]
    omega
  have hf : c.blocksInOrder[28 * g + 4]? = some b := by
    rw [← hi]
    exact IM.hear_at_flat e1 e2
  obtain ⟨Lk', b8, _, _, f1, f2, _⟩ := IM.k8_of_layers hS hR O g hg
  have hi8 : IM.flatIx c (2 * g) 4 = 28 * g + 6 := by
    rw [IM.flatIx_scope hS hR O (by omega) 4]
    omega
  have hf8 : c.blocksInOrder[28 * g + 6]? = some b8 := by
    rw [← hi8]
    exact IM.hear_at_flat f1 f2
  have hl : 28 * g + 6 < c.blocksInOrder.length := (List.getElem?_eq_some_iff.1 hf8).1
  exact K3Lot.tied_of_alone hT hf e4 (fun e => nomatch e) hq links ps N Mg E hE
    (H x b ⟨e3, e6, e5, (par_sits Hs).1, (par_sits Hs).2, hf, by omega, declares_alone e4⟩)

/-- **In a group that is not the first**: for public files in the goals' scope that
`VerifierAndGoals.readFiles` reads, at an opening of the proof file's description (so `onlineDescription` returns, at
the second hash function `OnBytes.secondHashFunction`), for three rows of pieces that hold that description's
blocks (`OfDesc`), the table's extractor laying nothing at this row (hE), the table's lists having
K4's row at number 28 g + 4 (at4), the table of scales being the group's (hscl): where at the lot's
member of that group `K4PieceAt` holds of the piece at K4's later rounds and `K4Asks` at every value
of the public part. -/
theorem k04_tied {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    {D : WholeD} {all : List LeftT} {X₁ X₂ W : Type}
    {T : ThreeAt (ckP .two) D all (descAt Z A B c) X₁ X₂ W} (hT : OfDesc _ T) (g : ℕ)
    (hg : g < 12) (hg0 : (g == 0) = false)
    {q : Piece (ckP .two) (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) ProofFile.Cl W}
    (hq : (T.p₁ :: T.l₁)[28 * g + 4]? = some q) (links : List ModelPart)
    (ps : List VerifiableInference.Desc.Place) (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (E : (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (hE : ∀ a b w, E a b w = w) {m : ℕ} {pl : VerifiableInference.Desc.Place}
    (at4 : AtK4 links ps (28 * g + 4) m pl) (hscl : scl = sclX Bs.G₀.W g)
    (lw : ℕ → LW Cb.Gl.E)
    (H : ∀ x b, ∀ h : K4Here c Z Bs.G₀ g x b,
      K4PieceAt q (dsLater (parOf x)) ∧
        ∀ z, Nonempty (K4Asks Bs.G₀.W x links ps (28 * g + 4) m pl q N Mg M
          (lt_of_eq_of_lt h.hg hg) z)) :
    TiedBy N Mg links ps (fun a => a) (28 * g + 4) (q.withMap E)
      (onQ N Mg links ps (fun a => a) (28 * g + 4))
      (onQ N Mg links ps (fun a => a) (28 * g + 4 + 1))
      (relAt (meansQ N Mg fun a => a) (insQ links ps (28 * g + 4)))
      (relAt (meansQ N Mg fun a => a) (outsQ links ps (28 * g + 4))) :=
  k04_tied_of_laws hS hR O hT g hg hq links ps N Mg E hE fun x b h => by
    obtain ⟨Pc, Q⟩ := H x b h
    have hs : scl = sclX Bs.G₀.W (parOf x).g := by
      show scl = sclX Bs.G₀.W x.2.g
      rw [h.hg]
      exact hscl
    refine seatLaws_k4 hs (lt_of_eq_of_lt h.hg hg) (publicSteps_of O.public) lw Pc Q at4 h.P h.G ?_
    show (x.2.g == 0) = false
    rw [h.hg]
    exact hg0

/-- **In the first group**: for public files in the goals' scope that `VerifierAndGoals.readFiles` reads, at
an opening of the proof file's description (so `onlineDescription` returns, at the second hash function
`OnBytes.secondHashFunction`), for three rows of pieces that hold that description's blocks (`OfDesc`), the
table's extractor laying nothing at this row (hE), the table's lists having K4's row at number 28 g
+ 4 (at4), the table of scales being the group's (hscl): where at the lot's member of that group
`K4PieceAt` holds of the piece at K4's first group's rounds and `K4AsksF` at every value of the
public part. FOR NOTHING AT THE MEANT FILLING: `K4Lines`' line idn cannot be met in the first
group as it is worded: see Limits. -/
theorem k04_tiedF {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    {D : WholeD} {all : List LeftT} {X₁ X₂ W : Type}
    {T : ThreeAt (ckP .two) D all (descAt Z A B c) X₁ X₂ W} (hT : OfDesc _ T) (g : ℕ)
    (hg : g < 12) (hg0 : (g == 0) = true)
    {q : Piece (ckP .two) (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) ProofFile.Cl W}
    (hq : (T.p₁ :: T.l₁)[28 * g + 4]? = some q) (links : List ModelPart)
    (ps : List VerifiableInference.Desc.Place) (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (E : (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (hE : ∀ a b w, E a b w = w) {m : ℕ} {pl : VerifiableInference.Desc.Place}
    (at4 : AtK4 links ps (28 * g + 4) m pl) (hscl : scl = sclX Bs.G₀.W g)
    (lw : ℕ → LW Cb.Gl.E)
    (H : ∀ x b, K4Here c Z Bs.G₀ g x b →
      K4PieceAt q (dsFirst (parOf x)) ∧
        ∀ z, Nonempty (K4AsksF Bs.G₀.W x links ps (28 * g + 4) m pl q N Mg M z)) :
    TiedBy N Mg links ps (fun a => a) (28 * g + 4) (q.withMap E)
      (onQ N Mg links ps (fun a => a) (28 * g + 4))
      (onQ N Mg links ps (fun a => a) (28 * g + 4 + 1))
      (relAt (meansQ N Mg fun a => a) (insQ links ps (28 * g + 4)))
      (relAt (meansQ N Mg fun a => a) (outsQ links ps (28 * g + 4))) :=
  k04_tied_of_laws hS hR O hT g hg hq links ps N Mg E hE fun x b h => by
    obtain ⟨Pc, Q⟩ := H x b h
    have hs : scl = sclX Bs.G₀.W (parOf x).g := by
      show scl = sclX Bs.G₀.W x.2.g
      rw [h.hg]
      exact hscl
    refine seatLaws_k4F hs (publicSteps_of O.public) lw Pc Q at4 h.P h.G ?_
    show (x.2.g == 0) = true
    rw [h.hg]
    exact hg0

omit scl in
/-- **The kind K4's share of the chain of promises, at the proof file's description**: for public
files in the goals' scope that `VerifierAndGoals.readFiles` reads, at an opening of the description (so
`onlineDescription` returns, at `OnBytes.secondHashFunction`), for three rows of pieces that hold its blocks (`OfDesc`),
at the driver's written lists, the table's extractor laying nothing at the twelve numbers (hE):
under `K4PieceAt` and `K4Asks` at the eleven later groups, `K4PieceAt` and `K4AsksF` at the first,
EACH AT ITS OWN GROUP's TABLE OF SCALES `sclX Bs.G₀.W g`: no table of scales is a letter of this
statement. FOR NOTHING AT THE MEANT FILLING: `K4Lines`' line idn cannot be met in the first
group as it is worded: see Limits. -/
theorem k04_kindTied {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    {D : WholeD} {all : List LeftT} {X₁ X₂ W : Type}
    {T : ThreeAt (ckP .two) D all (descAt Z A B c) X₁ X₂ W} (hT : OfDesc _ T) (N : Numbers)
    (Mg : Meaning ProofFile.InstPub W)
    (E : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (hE : ∀ g, g < 12 → ∀ a b w, E (28 * g + 4) a b w = w) (lw : ℕ → LW Cb.Gl.E)
    (H : ∀ g, ∀ hg : g < 12, (g == 0) = false → ∀ q, (T.p₁ :: T.l₁)[28 * g + 4]? = some q →
      ∀ x b, ∀ h : K4Here c Z Bs.G₀ g x b,
        K4PieceAt q (dsLater (parOf x)) ∧
          ∀ z, Nonempty (K4Asks (scl := sclX Bs.G₀.W g) Bs.G₀.W x linksFull
            (flatPlacesOf linksFull true) (28 * g + 4) (2 * g) (k4PlaceAt g) q N Mg M
            (lt_of_eq_of_lt h.hg hg) z))
    (H0 : ∀ q, (T.p₁ :: T.l₁)[28 * 0 + 4]? = some q →
      ∀ x b, K4Here c Z Bs.G₀ 0 x b →
        K4PieceAt q (dsFirst (parOf x)) ∧
          ∀ z, Nonempty (K4AsksF (scl := sclX Bs.G₀.W 0) Bs.G₀.W x linksFull
            (flatPlacesOf linksFull true) (28 * 0 + 4) (2 * 0) (k4PlaceAt 0) q N Mg M z)) :
    KindTied N Mg linksFull (flatPlacesOf linksFull true) E (T.p₁ :: T.l₁) KindName.K4 := by
  intro i q a hq ha hk
  obtain ⟨g, hg, rfl, -⟩ := k04_places_full i a ha hk
  by_cases h0 : g = 0
  · subst h0
    exact (k04_tiedF (scl := sclX Bs.G₀.W 0) hS hR O hT 0 hg rfl hq linksFull _ N Mg (E _)
      (hE 0 hg) (atK4_full 0 hg) rfl lw (H0 q hq)).tiedAt
  · have hg0 : (g == 0) = false := by simpa using h0
    exact (k04_tied (scl := sclX Bs.G₀.W g) hS hR O hT g hg hg0 hq linksFull _ N Mg (E _)
      (hE g hg) (atK4_full g hg) rfl lw (H g hg hg0 q hq)).tiedAt

omit scl in
/-- **The same at rows that tile the first chain's data**: as `k04_kindTied`, with two of the
piece's three facts CONCLUDED (`k04_piece_later`, `k04_piece_first`: PieceLater.lean,
PieceFirst.lean): in their place three lines on the rows T: the description's data at a file are D
(hD), the first row is tiled (ht), its rounds are D's first chain's (hd). That the pieces' errors
are the cap (hcap) stays a premise. FOR NOTHING AT THE MEANT FILLING: `K4Lines`' line idn
cannot be met in the first group as it is worded: see Limits. -/
theorem k04_kindTied_tiled {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    {D : WholeD} {all : List LeftT} {X₁ X₂ W : Type}
    {T : ThreeAt (ckP .two) D all (descAt Z A B c) X₁ X₂ W} (hT : OfDesc _ T) (file : String)
    (hD : (descAt Z A B c).data file = .ok D) (ht : Tiled T.p₁ T.l₁)
    (hd : rowData T.p₁ T.l₁ = D.ds₁) (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (E : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (hE : ∀ g, g < 12 → ∀ a b w, E (28 * g + 4) a b w = w) (lw : ℕ → LW Cb.Gl.E)
    (hcap : ∀ g, g < 12 → ∀ q, (T.p₁ :: T.l₁)[28 * g + 4]? = some q →
      q.err = Err.cap 128 (uLT (ckP .two) q.ds))
    (H : ∀ g, ∀ hg : g < 12, (g == 0) = false → ∀ q, (T.p₁ :: T.l₁)[28 * g + 4]? = some q →
      ∀ x b, ∀ h : K4Here c Z Bs.G₀ g x b,
        ∀ z, Nonempty (K4Asks (scl := sclX Bs.G₀.W g) Bs.G₀.W x linksFull
          (flatPlacesOf linksFull true) (28 * g + 4) (2 * g) (k4PlaceAt g) q N Mg M
          (lt_of_eq_of_lt h.hg hg) z))
    (H0 : ∀ q, (T.p₁ :: T.l₁)[28 * 0 + 4]? = some q →
      ∀ x b, K4Here c Z Bs.G₀ 0 x b →
        ∀ z, Nonempty (K4AsksF (scl := sclX Bs.G₀.W 0) Bs.G₀.W x linksFull
          (flatPlacesOf linksFull true) (28 * 0 + 4) (2 * 0) (k4PlaceAt 0) q N Mg M z)) :
    KindTied N Mg linksFull (flatPlacesOf linksFull true) E (T.p₁ :: T.l₁) KindName.K4 :=
  k04_kindTied hS hR O hT N Mg E hE lw
    (fun g hg hg0 q hq x b h => by
      have hg0' : ((parOf x).g == 0) = false := by
        show (x.2.g == 0) = false
        rw [h.hg]
        exact hg0
      obtain ⟨_, hb, hs⟩ :=
        k04_piece_later (descAt Z A B c) file D hD T hT ht hd hq h.flat h.more h.decl hg0'
      exact ⟨⟨hs, hb, hcap g hg q hq⟩, H g hg hg0 q hq x b h⟩)
    (fun q hq x b h => by
      have hg0' : ((parOf x).g == 0) = true := by
        show (x.2.g == 0) = true
        rw [h.hg]
        rfl
      obtain ⟨_, hb, hs⟩ :=
        k04_piece_first (descAt Z A B c) file D hD T hT ht hd hq h.flat h.more h.decl hg0'
      exact ⟨⟨hs, hb, hcap 0 (by omega) q hq⟩, H0 q hq x b h⟩)

omit scl in
/-- **The kind K4's share of the chain of promises from `K4OwnAt`**, at all twelve groups in one
form: in the goals' scope (hS, hR), at an opening O, for rows T that hold the description's blocks
(hT): where the table's extractor lays nothing at the twelve numbers (hE), and at every group,
piece, member of the lot and public part the piece puts no round behind and `K4OwnAt` holds (H). -/
theorem k04_kindTied_own {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    {D : WholeD} {all : List LeftT} {X₁ X₂ W : Type}
    {T : ThreeAt (ckP .two) D all (descAt Z A B c) X₁ X₂ W} (hT : OfDesc _ T) (N : Numbers)
    (Mg : Meaning ProofFile.InstPub W)
    (E : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (hE : ∀ g, g < 12 → ∀ a b w, E (28 * g + 4) a b w = w)
    (H : ∀ g, g < 12 → ∀ q, (T.p₁ :: T.l₁)[28 * g + 4]? = some q →
      ∀ x b, K4Here c Z Bs.G₀ g x b →
        q.back = [] ∧ ∀ z, K4OwnAt x linksFull (flatPlacesOf linksFull true) (28 * g + 4) (2 * g)
          q N Mg z) :
    KindTied N Mg linksFull (flatPlacesOf linksFull true) E (T.p₁ :: T.l₁) KindName.K4 := by
  intro i q a hq ha hk
  obtain ⟨g, hg, rfl, -⟩ := k04_places_full i a ha hk
  exact (k04_tied_of_laws hS hR O hT g hg hq linksFull _ N Mg (E _) (hE g hg) fun x b h =>
    seatLaws_k4_own (H g hg q hq x b h).1 (H g hg q hq x b h).2).tiedAt

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k04_kindTied_tiled
#print axioms OnBytes.Road.K4.seatLaws_k4_own
#print axioms OnBytes.Road.K4.k04_kindTied_own
#print axioms OnBytes.Road.K4.k4HereB_full
#print axioms OnBytes.Road.K4.atK4_full
#print axioms OnBytes.Road.K4.k04_kindTied
#print axioms OnBytes.Road.K4.hearsAs_seatOf
#print axioms OnBytes.Road.K4.seatLaws_k4
#print axioms OnBytes.Road.K4.seatLaws_k4F
#print axioms OnBytes.Road.K4.k04_tied_of_laws
#print axioms OnBytes.Road.K4.k04_tied
#print axioms OnBytes.Road.K4.k04_tiedF
