-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4Means.lean: ONE STRUCTURE OF EQUATIONS: WHAT K4's FILES READ OF THE TABLE OF
JOINTS' MEANING, AS FAR AS A LAYER SAYS IT, OVER A LETTER Mg: each field says "Mg's field, or
Mg's sentence at an item, IS its owner's own term". (Two fields are lines on the sentences without a
test, not equations.) NO FIELD IS A LAW. Why: a theorem that names the one composed filling
depends on all of it: a theorem under this structure depends only on the structure's fields (a
further name that is open across K4's sub-protocol would add one): the structure is to be proved
once for each filling. A LIGHT FILE: it imports the table, K4's own layer, and
the owners' files whose terms stand on the right sides: no law of K4's road, and not the composed
term. Definitions alone.

  `K4Data`: THE OWNERS' DATA, as letters: of the oracles' layer (cs · G · arr · smp · ms · decT) ·
    of the model's relation's (hd · put · H · headPart · digitsPart) · of the runs' forms' (Rd ·
    runs · St · wt · N) · of "in order" (base · shape · layout · reqW · reqB) · of the pile's (rw13)
    · of the table's own, K4's and the proximity test's door's layers (nsOf · links · nextOf · d12)
    · of the lookups' (D3 · L3) · of the pending row's (d1; free0 · fvs: the index masks' fresh
    ledger's count of free entries, and which segments leave a pending row: LETTERS OF THIS
    STRUCTURE's OWN, TIED TO NOTHING HERE) · of K4's own second layer (sd) · and WHAT LIES BENEATH
    ALL LAYERS at two fields that layers lay in part (worthBase · moreL).
  **`K4Means Mg D`**: THE STRUCTURE. (A) WHAT THE ROW READS OR CLOSES: pin · pinW · constr (with
    decIs: the relation's decoder is the oracles') · worth. (B) WHAT IT OPENS: formsT · wo. (C) WHAT
    RIDES: pile · row · constr · formsT. (D) THE PROMISE's OWN FIELDS: decodes · inOrder (five
    conjuncts) · held · shown · noColl · more. (E) PUBLIC ITEMS: asked or dropped: ledger ·
    freeAbove · look · callerIn (at feed-forward segments) · linkFresh · left (its Bool, and its
    sentence) · rowsBare · lookLeft · room · kept: unheard · lookOut · liveIs · the weights' one ·
    the proximity test's door's four · the open segment's frame and the ledger's arrays (sentIs ·
    treesAre) · indexIs · indexThere · formsInT · made: lookIn · leftOn (Bool and sentence) · hasRow
    · formsInT.

THE SENTENCES WITHOUT A TEST (pubP): at left and leftOn the lookups' own; AT EVERY OTHER ITEM THE
SENTENCE READS NO STATE (pubPRides), AND AT lookIn IT HOLDS (pubPLookIn: K4's row makes lookIn m 7).
Not asked: that it holds at an item for which nobody answers: the composed meaning's closed base
says False there.

BESIDE THE STRUCTURE: five equations more, on the pile's three names and two of the approximate
range proof's, stand in `K4PileNames` (Riders/KeptNames.lean).
The names that only carry a fact on every reached state across many kinds'
sub-protocols ARE NOT IN the composed meaning's door: THIRTEEN (the weights' one · the proximity
test's door's four · the pile's three · "pile.room" · "frame.liveIs" · "K8.lay7" · "K8.onThird" ·
"K8.funsThird"), and four conjuncts of "in order": a theorem here that spends, keeps or makes one of
them stands at a WIDER meaning than the composed one (a bridge's side), and is carried to it by a
bridge under facts on reached states that are owed.

Limits. EQUATIONS: nothing is proved of any sub-protocol. A theorem under this structure is worth
what the letters are worth: at a wrong letter (nsOf · nextOf · N · Rd …) the promise in front of
K4's sub-protocol may be met by no unmarked state, and all that is asked inside it holds for
nothing. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.

-/
import Johnson.Desc.Sound.BordersForms
import Johnson.P5J.MeansQ
import Johnson.Meaning.ReqBytes
import Johnson.Desc.First.FillKeeper
import Johnson.Desc.First.FillK4
import Johnson.Desc.First.FillSent
import Johnson.Desc.First.FillBare
import Johnson.Desc.First.FillStart
import Johnson.Desc.First.FillReqIs
import Johnson.Desc.First.FillWeights
import Johnson.Desc.K12.Door.FillK12
import Johnson.Desc.K13.Law.FillK13
import Johnson.Desc.First.Close.Law.FillRowFirst
import Johnson.Desc.First.Look.K3FillWorth
import Johnson.Top.H0.Fill.FillP1
import Johnson.Top.H0.Walk.FrameEntriesDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open Johnson.Pack (sigOf)
open VerifiableInference.Desc (Place FileDescription Wit Strs smpHeld)
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers Pub More rowSays wordsAtFirst eqsB reqIsB
  ledgerB freeAboveB unheardB weightsB)
open VerifiableInference.Desc.First.FillK4 (isLay lookLayB callerInLayB)
open VerifiableInference.Desc.First.FillSent (SentData sentIsB treesAreB)
open VerifiableInference.Desc.First.FillBare (rowsBareB lookLeftB)
open VerifiableInference.Desc.First.Look (Sent liveItem liveIsB k3OnOutAt k3LookInAt)
open VerifiableInference.OnPublicFiles (K3Letters worthK3 linkFreshB k3LeftItemAt k3LeftOnItemAt)
open VerifiableInference.Desc.K9 (Readers formsInT)
open VerifiableInference.Desc.K12.Door (K12Data atFirstBook atFirstSeats atFirstShapes atFirstFits)
open VerifiableInference.Desc.K13 (indexIsC indexThereC)
open VerifiableInference.Desc.K13.Law (RowsTrue inOrderK13)
open VerifiableInference.Desc.Sound (Sending Mem MsgT Stated decodesOf pinWOf pinJT shownJT noCollJT
  formsTQ seatTab)

/-- The committed table's cells, as the model's relation's layer decodes them. -/
abbrev CellsK (rows cols : ℕ) : Type := Fin rows → Fin cols → VerifiableInference.OnPublicFiles.Flat.GE

/-- The index of the model's commitment (its owner's own type). -/
abbrev IdxM : Type := open Inst.Model Inst.Model.All in Cm.Idx

/-- **The owners' data, as letters.** -/
structure K4Data (Xi P Tok : Type) (rows cols nR kC : ℕ) (X : Verify.Public) where
  cs : Codes
  G : FileDescription Xi
  arr : ℕ → ℕ → ℕ
  smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp
  ms : List Mem
  decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option (CellsK rows cols)
  hd : ℕ
  put : P5J.TReq → Fin Inst.Model.ppref.V → P5J.TReq
  H : P5J.HidAt X P (Wit (CellsK rows cols) Tok MsgT) rows cols
  headPart : P5J.TPart → IdxM → P × S → Strs → Wit (CellsK rows cols) Tok MsgT → Prop
  digitsPart : ℕ → P × S → Strs → Wit (CellsK rows cols) Tok MsgT → Prop
  Rd : ℕ → Readers
  runs : ℕ → ℕ → String → List (ℕ × String)
  St : Stated
  wt : ℕ → P × S → Strs → Wit (CellsK rows cols) Tok MsgT → Prop
  N : Numbers
  base : P × S → Bool
  shape : Params.ReqShape
  layout : Params.ReqLayout
  reqW : P → Array UInt32
  reqB : P → ByteArray
  rw13 : P × S → Wit (CellsK rows cols) Tok MsgT →
    VerifiableInference.Desc.K13.Law.Wit VerifiableInference.OnPublicFiles.Flat.GE nR kC
  nsOf : ℕ → Option ℕ
  links : List ModelPart
  nextOf : ℕ → Option ℕ
  d12 : K12Data
  /-- the lookups': the public parameters' data, what "worth" reads beside (their public parameters:
  X) -/
  D3 : Sent
  L3 : K3Letters (CellsK rows cols) Tok
  /-- the pending row's: the public parameters' numbers (its reader of the witness is the pile's:
  rw13) -/
  d1 : VerifiableInference.Desc.First.FillP1.PubData
  /-- the index masks' fresh ledger's count of free entries; which segments leave a pending row -/
  free0 : ℕ
  fvs : List Bool
  /-- what says "worth" at the pieces that are none of the lookups' -/
  worthBase : ℕ → ℕ → String → P × S → Strs → Wit (CellsK rows cols) Tok MsgT → Prop
  /-- the door's filling: all layers' merged -/
  moreL : More
  /-- K4's own second layer's: the public parameters' side of the open segment's frame and of the
  ledger's arrays
  -/
  sd : SentData

variable {Xi P Tok : Type} {rows cols nR kC : ℕ} {X : Verify.Public}

/-- **THE STRUCTURE: 44 fields: 42 equations and two lines (pubPRides · pubPLookIn).** -/
structure K4Means (Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT))
    (D : K4Data Xi P Tok rows cols nR kC X) : Prop where
  pin : Mg.pin = pinJT D.cs D.G D.arr D.smp D.ms
  pinW : Mg.pinW = pinWOf D.decT
  constr : Mg.constr = P5J.constrQAt D.hd D.put D.H D.headPart D.digitsPart
  decIs : D.H.dec = fun a y => D.decT y.cell a
  worth : Mg.worth = worthK3 X D.D3 D.L3 D.worthBase
  formsT : Mg.formsT = fun m k r (a : P × S) y w => (∀ p ∈ D.runs m k r,
    formsTQ (D.Rd m) D.St (D.N.sent m 0) p.1 p.2 a.2 (seatTab D.cs D.arr D.ms w)) ∧
      (r = "weights" → D.wt m a y w)
  wo : Mg.wo = VerifiableInference.Desc.First.FillP1.woAt D.d1 D.rw13
  pile : Mg.pile = fun x _ w => RowsTrue (D.rw13 x) x.2 w
  row : Mg.row = rowSays D.N (wordsAtFirst D.arr)
  decodes : Mg.decodes = decodesOf D.decT
  inOrder : ∀ a : P × S, Mg.inOrder a =
    ((((D.base a && eqsB D.cs D.shape D.layout a.2) && reqIsB (D.reqW a.1) a.2) &&
      inOrderK13 D.cs D.shape D.layout a.2) && (_root_.Meaning.backReq (D.reqB a.1)).isSome)
  held : Mg.held = fun j t (a : P × S) => smpHeld a.2.st a.2.book j t
  shown : Mg.shown = shownJT D.cs D.G D.ms
  noColl : Mg.noColl = noCollJT D.cs D.G D.smp D.ms
  more : Mg.more = D.moreL
  ledger : ∀ m a, Mg.pub (.ledger m) a = ledgerB a.2
  freeAbove : ∀ m a, Mg.pub (.freeAbove m) a = (D.nsOf m).any fun n => freeAboveB n a.2
  unheard : ∀ a, Mg.pub .unheard a = unheardB a.2
  look : ∀ m a, isLay D.links m = true → Mg.pub (.look m) a = lookLayB a.2
  callerIn : ∀ m a, isLay D.links m = true →
    Mg.pub (.callerIn m) a = (D.nextOf m).any fun n => callerInLayB n a.2
  weightsOk : ∀ a, Mg.pub (.more none "K13.weightsOk") a = weightsB a.2
  bookInOrder : ∀ a, Mg.pub (.more none "K12.bookInOrder") a = atFirstBook D.d12.ft a.2
  seatsCarried : ∀ a, Mg.pub (.more none "K12.seatsCarried") a = atFirstSeats D.d12.L a.2
  msgShapes : ∀ a, Mg.pub (.more none "K12.msgShapes") a = atFirstShapes D.d12.M a.2
  bookFits : ∀ a, Mg.pub (.more none "K12.bookFits") a = atFirstFits a.2
  sentIs : ∀ m a, Mg.pub (.more (some m) "frame.sentIs") a = sentIsB D.sd m a.2
  treesAre : ∀ m a, Mg.pub (.more (some m) "ledger.treesAre") a = treesAreB D.sd m a.2
  rowsBare : ∀ m a, isLay D.links m = true →
    Mg.pub (.more (some m) "K4.rowsBare") a = rowsBareB a.2
  lookLeft : ∀ m a, isLay D.links m = true →
    Mg.pub (.more (some m) "K4.lookLeft") a = lookLeftB a.2
  indexIs : ∀ a, Mg.pub .indexIs a = indexIsC D.N.indexNo a.2
  indexThere : ∀ a, Mg.pub .indexThere a = indexThereC a.2
  formsInT : ∀ m k r a, Mg.pub (.formsInT m k r) a =
    (D.runs m k r).all fun p => formsInT (D.Rd m) (D.N.sent m 0) p.1 p.2 a.2
  hasRow : ∀ m a, Mg.pub (.hasRow m) a =
    Johnson.Desc.First.Walk.Law.hasRow D.d1.lay (D.d1.ncl m) D.d1.lin a.2
  room : ∀ m a, Mg.pub (.more (some m) "pile.room") a =
    Johnson.Desc.First.Walk.Tied.roomIsB D.free0 D.fvs m a.2
  linkFresh : ∀ m a, Mg.pub (.linkFresh m) a = linkFreshB (D.D3.arrayOf.getD m #[]) a.2
  lookIn : ∀ m dg a, Mg.pub (.lookIn m (VerifiableInference.Desc.K3.pieceAt X m dg)) a =
    k3LookInAt X D.D3 m dg a.2
  lookOut : ∀ m dg a, Mg.pub (.lookOut m (VerifiableInference.Desc.K3.pieceAt X m dg)) a =
    k3OnOutAt X m dg a.2
  liveIs : ∀ m a, Mg.pub (liveItem m) a = liveIsB D.D3 a.2
  leftB : ∀ m a, Mg.pub (.left m) a = true
  leftOnB : ∀ m a, Mg.pub (.leftOn m) a = true
  left : ∀ m a, Mg.pubP (.left m) a = k3LeftItemAt X m a.2
  leftOn : ∀ m a, Mg.pubP (.leftOn m) a = k3LeftOnItemAt X m a.2
  pubPRides : ∀ q z s s', (∀ m, q ≠ .left m) → (∀ m, q ≠ .leftOn m) → Mg.pubP q (z, s) →
    Mg.pubP q (z, s')
  pubPLookIn : ∀ m j a, Mg.pubP (.lookIn m j) a

end OnBytes.Road.K4
