-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/MgAll.lean: the meaning of the claims that are open between two sub-protocols
of a request's own rounds, composed from all authors' parts: ONE TERM `mgAll 𝔇 Mg` of `Meaning`
(Johnson/Desc/First/Borders.lean). EIGHTEEN PARTS; ALL THEIR PARAMETERS IN ONE
STRUCTURE; EVERY FIELD OF `Meaning` IS GIVEN BY A PART (the parts' own parameters, the fields of
𝔇, are open here).
Why. Each kind of sub-protocol has a law: "if the claims behind it hold, so do those in front, but
for a small error". These laws meet at ONE meaning of the claims. As long as each law takes its
share of that meaning as premises, nobody holds the one term at which all these premises are true
together.
THE PARTS, from the innermost:
  the table's own (`fillKeeper`, Johnson/Desc/First/FillKeeper.lean): pub at ledger, freeAbove,
    unheard;
  the claim at the last point (`fillWrow`, Johnson/Desc/Sound/FillWrow.lean): wrow;
  the linear claims on a group of oracle messages (`First.fillRowFirst`,
    Johnson/Desc/First/Close/Law/FillRowFirst.lean): row; more;
  the feed-forward sub-protocol's two names (`FillBare.fillBare`,
    Johnson/Desc/First/FillBare.lean): pub; more;
  what has been sent, behind a segment's second sending (`FillSent.fillSent1`,
    Johnson/Desc/First/FillSentLater.lean): pub at one name; more;
  what has been sent, behind its first sending (`FillSent.fillSent`,
    Johnson/Desc/First/FillSent.lean): pub at two names; more;
  attention's (`H2K5.Door.fillK5`, Johnson/Desc/First/Att/Door/FillK5.lean): pub at look, callerIn
    and four names at an attention segment; more;
  the approximate range proof's tie, the pending claim on the weights, the carried word
    (`First.FillP1.fillP1`, Johnson/Top/H0/Fill/FillP1.lean): tie, wo, carry; pub at hasRow; pubP
    (True there);
  the feed-forward sub-protocol's (`FillK4.fillK4`, Johnson/Desc/First/FillK4.lean): pub at look,
    callerIn at a feed-forward segment;
  the output head's (`Kinds.Head.fillK6K7`, Johnson/Stored/FillK6K7.lean): pub at tokenSmall, and
    at look at its segment;
  the output head's lookup argument (`OnPublicFiles.fillK3HeadG`,
    Johnson/Desc/First/Look/K3HeadFillG.lean): worth at one place, UNDER A GUARD ON THE WITNESS:
    its cells are in range;
  the lookup arguments' (`OnPublicFiles.fillK3All`, Johnson/Desc/First/Look/K3FillWorth.lean): worth at
    the other places; pubP at left, leftOn; pub at lookIn, lookOut, linkFresh, left, leftOn;
  the last sub-protocols' (`K13.Law.fillK13`, Johnson/Desc/K13/Law/FillK13.lean): pile, pileOne;
    pub at noneSent, indexIs, indexThere, frontOk, evalLaid, one name; more;
  `shut` (here): "in order" is Mg's own; the names that leave are taken out of the list of extra
    public tests (`More.strike`, Johnson/Desc/First/SmallDoor.lean: out of what each row asks, makes
    and drops, and out of the start list);
  the request's bytes (`P5J.withReq`, Johnson/P5J/TieAt.lean): inOrder (conjoined): "the request
    file's bytes in the public part are a request's": a test on the public part alone;
  the oracle messages' six (`meaningSig`, Johnson/Desc/Sound/BordersFill.lean): pin, noColl,
    shown, held, pinW, decodes;
  the model's relation in its parts (`P5J.meaningQAt`, Johnson/P5J/MeansQ.lean, at the output
    head's segment's number `headLink X`): constr (AND decodes: see beneath);
  the claims on linear forms (`meaningForms`, Johnson/Desc/Sound/BordersForms.lean): forms,
    formsT, totalB, total; pub at formsIn, formsInT, totalIn.
ONE PART HAS A GUARD (the output head's lookup argument).



Why `shut`: a public test that
says a fact which holds at EVERY state that the verifier reaches would be asked from the start
on, or over whole segments, and be kept by every sub-protocol of every author. Such facts are
proved once, along the run, outside this term (Johnson/Desc/First/SmallDoor.lean names the
thirteen that leave). WHOEVER SPENDS ONE TAKES IT FROM THERE.
WHAT IS SAID.
  `MgData`: ALL PARAMETERS OF THE PARTS, IN ONE STRUCTURE, over those of the public tests
    (`First.PubData0`, Johnson/Desc/First/PubAll.lean). MADE FROM OTHER PARAMETERS, SO THAT
    NOTHING STANDS TWICE (each a definition `MgData.‹name›`, or written in place): the output
    head's segment's number (`headLink X`), its shape (X.hS), the number of its array of the reads
    (`iU3At X`), its sizes, policy and addresses (`k3SizesAt X`, `k3PolicyAt X`, `k3AdrAt X`); the
    feed-forward sub-protocol's slot numbers (`FillK4.nextOfPlan X`); what the lookup arguments
    read (`sent`: the term's own codes, shape, layout; the built segments' lists of arrays); `l3`
    (the term's own arr; the committed table as an oracle message, its reader of a cell and the
    witness's message FIXED: `k3StoredAt`); the readers of the claims on linear forms and what
    follows a batching (`Rd`, `after`: from the links lk); the map of names (`runs`); `ah`; the
    stated functions (`St`: one, with three arms); the witness's words (`rdW`) and the reader of
    the pending claims (`rw13`: pile, pileOne and wo read through it); the table of cells that the
    tie reads (`A1`: the accessor of the claims on linear forms); from the built segments `built`:
    the numbers of slots and what has been sent (`pubD`'s nsOf, dS, dS1). A later part's
    parameters are new fields: the term's list of arguments stands.
  `oneDec decT H`: ONE DECODER: how a witness is read (H), with its decoder of the committed table
    SET TO the oracle messages' part's own decT. `dec_is_cells`: so the matrix of which constr
    speaks, where pinW holds, IS the witness's cells. `oneDec_self`: where H's decoder is decT
    already, nothing turns.
  `fillK3Both`, `mgBelow`, `shut`: the lookup arguments' part over the output head's; the thirteen
    parts beneath; see above.
  `mgAll 𝔇 Mg`: the parts, one over the other, over a meaning Mg that answers wherever no part
    does.
  `mgAll_pub`: its public tests ARE the function with code `First.pubAll 𝔇.pubD`: what a run
    evaluates is what the laws speak of.
  `mgAll_forms` ... `mgAll_pubP`: each field is its part's own term.
  `mgAll_inOrder_at`, `mgAll_more`: "in order" and the list of extra public tests at the term.
  `mgAll_decodes`: the one field that two parts give OUTRIGHT is the oracle messages' own
    sentence.
  `mgAll_is_tower`: **WHERE headLink X = 24 THE TERM IS THE MEANING AT WHICH THE TOP-LEVEL LAWS
    ARE STATED** (meaningQ over meaningSig over withReq over a parameter), at that parameter :=
    the part for the claims on linear forms over all that lies beneath.
  `codeKeeper` ... `codeK13`: definitions WITH code that call a part's pub: they compile only if
    that part has code. THAT IS ALL THAT THEY SHOW.
Limits: a composing. EVERY FIELD OF 𝔇 IS A PARAMETER HERE. FOUR OF THEM HAVE THE VERY TYPE OF A
SENTENCE OF `Meaning`: cr1 (carry := 𝔇.cr1 outright), wt, headPart, digitsPart: THERE THE FIELD OF
`Meaning` IS GIVEN IN NAME ALONE until the parameter has its closed term. Of Mg are still read:
pub at request, and at an item outside every part's own test; pubP outside left, leftOn and
hasRow; worth outside the lookup arguments' places and names; more; inOrder. The parts that give
sentences are noncomputable: so `mgAll` has no code: its pub is run through `First.pubAll` and
`mgAll_pub`.
pile is open from the start of the request's own rounds: every sub-protocol in front of the one
that closes it owes its going back.
PARAMETERS THAT ARE MEANT TO AGREE AND ARE TIED BY NOTHING HERE: 𝔇.links with X and with 𝔇.built
(which segment is of which sort: three tests read it); 𝔇.built and 𝔇.lk with X; 𝔇.ms with 𝔇.seat3
and 𝔇.rad3; 𝔇.P13.lin with 𝔇.d1.lin; 𝔇.d1.ncl with 𝔇.built: whoever fills 𝔇 owes these. TWO TERMS
THAT ARE MADE HERE REST ON A READING: `iU3At X` (another author's one line; its two lemmas unseen
here) and the output head's sizes (`k3SizesAt X`: the lookup arguments' own; the output head's
authors' own sizes have one field written otherwise: whether the two are one is said by nobody).
The attention part's list of a segment's own seats is 𝔇.N.sent m 0: it holds the carried message
and the kept copies beside the segment's own.
SILENT DEFAULTS: `after` at a number without a link is an error; `Rd` there answers nowhere; `A1`
is 0 where no segment is open.
Nothing says that any witness meets the claims at this term. No soundness is claimed.

-/
import Johnson.Desc.Sound.BordersForms
import Johnson.P5J.MeansQ
import Johnson.P5J.TieAt
import Johnson.Desc.First.PubAll
import Johnson.Desc.First.SmallDoor
import Johnson.Desc.First.Look.K3HeadFillG
import Johnson.Desc.First.Look.K3LettersAt
import Johnson.Top.H0.Fill.FillP1
import Johnson.Desc.Sound.FillWrow
import Johnson.Desc.First.Att.Door.FillK5
import Johnson.Desc.First.K4NextOf
import Johnson.Desc.First.Batch.ReadersAt
import Johnson.Desc.Sound.StatedAll
import Johnson.Desc.K13.Law.ReaderByBook
import Johnson.Desc.Sound.CellsAt
import Johnson.Desc.First.Close.Law.FillRowFirst
import Johnson.Desc.K13.Law.FillK13

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers Pub fillKeeper pubKeeper pubAll
  fillRowFirst PubData PubData0)
open VerifiableInference.Desc.First.FillK4 (fillK4)
open VerifiableInference.Desc.Kinds.Head (fillK6K7)
open VerifiableInference.Desc.First.Look (Sent K3Data)
open VerifiableInference.OnPublicFiles (K3Letters fillK3All fillK3Head fillK3HeadG headLink k3StoredAt)
open VerifiableInference.Desc.K13.Law (DataK13 fillK13)
open VerifiableInference.Desc.K9 (Readers)

/-- The committed table's cells, as the part for the model's relation decodes them. -/
abbrev CellsQ (rows cols : ℕ) : Type := Fin rows → Fin cols → VerifiableInference.OnPublicFiles.Flat.GE

/-- The index of the model's commitment (its owner's own type). -/
abbrev IdxQ : Type := open Inst.Model Inst.Model.All in Cm.Idx

/-- **ALL PARAMETERS OF THE COMPOSED MEANING, IN ONE STRUCTURE**, over those of the public tests
(`First.PubData0`). A later part's parameters are new fields: the term's list of arguments stands.
-/
structure MgData (Xi P Tok : Type) (rows cols nR : ℕ) (X : OnBytes.Model.Verify.Public) extends
    PubData0 where
  /-- the oracles' six -/
  G : FileDescription Xi
  arr : ℕ → ℕ → ℕ
  smp : P × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp
  ms : List Mem
  decT : (ℕ → Option (ℕ × List UInt64)) → P × First.S → Option (CellsQ rows cols)
  /-- the model's relation in its parts -/
  put : P5J.TReq → Fin Inst.Model.ppref.V → P5J.TReq
  H : P5J.HidAt X P (Wit (CellsQ rows cols) Tok MsgT) rows cols
  headPart : P5J.TPart → IdxQ → P × First.S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop
  digitsPart : ℕ → P × First.S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop
  /-- the request; the start -/
  reqB : P → ByteArray
  shape : OnBytes.Params.ReqShape
  layout : OnBytes.Params.ReqLayout
  /-- the runs' forms: the chain's links; the stated functions, by the sort of the open segment -/
  lk : ℕ → Option (Link First.S Claim)
  uL : ℕ → UFn
  uA : ℕ → UFn
  uH : ℕ → UFn
  wt : ℕ → P × First.S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop
  rw : ℕ → First.S → Bool
  /-- the last sub-protocols' -/
  mat13 : CellsQ rows cols → Fin nR → (Fin P13.lin.kCol → Bool) → GE
  /-- the lookups', and the head's calls' -/
  rad3 : OnBytes.OracleShape → ℕ
  seat3 : ℕ → Bool → ℕ → ℕ × ℕ
  rq : P → Kinds.Head.Request
  /-- the carried word's -/
  cr1 : ℕ → P × First.S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}

/-- **One decoder, by the make.** -/
def oneDec (decT : (ℕ → Option (ℕ × List UInt64)) → P × First.S → Option (CellsQ rows cols))
    (H : P5J.HidAt X P (Wit (CellsQ rows cols) Tok MsgT) rows cols) :
    P5J.HidAt X P (Wit (CellsQ rows cols) Tok MsgT) rows cols :=
  { H with dec := fun a y => decT y.cell a }

/-- Where H's decoder is that one already, nothing turns. -/
theorem oneDec_self
    (decT : (ℕ → Option (ℕ × List UInt64)) → P × First.S → Option (CellsQ rows cols))
    (H : P5J.HidAt X P (Wit (CellsQ rows cols) Tok MsgT) rows cols)
    (h : H.dec = fun a y => decT y.cell a) : oneDec decT H = H := by
  cases H
  subst h
  rfl

/-- What that decoder gives, where the committed table's pin holds, is the witness's cells. -/
theorem dec_is_cells
    (decT : (ℕ → Option (ℕ × List UInt64)) → P × First.S → Option (CellsQ rows cols))
    (H : P5J.HidAt X P (Wit (CellsQ rows cols) Tok MsgT) rows cols)
    (a : P × First.S) (y : Strs) (w : Wit (CellsQ rows cols) Tok MsgT)
    (M : CellsQ rows cols) (h1 : (oneDec decT H).dec a y = some M) (h2 : pinWOf decT a y w) :
    M = w.cells := Option.some.inj (h1.symm.trans h2)

variable (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- The number of the output head's array of the reads, off the public parameters. -/
def iU3At (X : OnBytes.Model.Verify.Public) : ℕ := (X.H.tl.ix.U.getD 2 none).getD 0

/-- What the plan sends, as the lookups read it: THE TERM's OWN codes, shape and layout. -/
def MgData.sent : Sent := ⟨𝔇.cs, 𝔇.shape, 𝔇.layout, 𝔇.built.map (·.arrayOf)⟩

/-- What the field worth reads beside: the term's own arr; the committed table as an oracle message,
its reader of a cell and the witness's message are FIXED (`k3StoredAt`). -/
noncomputable def MgData.l3 : K3Letters (CellsQ rows cols) Tok := k3StoredAt 𝔇.rad3 𝔇.arr 𝔇.seat3

/-- The runs' readers: off the chain's links and the public parameters. -/
def MgData.Rd : ℕ → Readers := K9.readersAt 𝔇.lk X (headLink X)

/-- The map of names: the table's own, at the chain's sorts of segments. -/
def MgData.runs : ℕ → ℕ → String → List (ℕ × String) := runsAt 𝔇.links

/-- Of which runs the forms may name what is ahead: the approximate range proof's own run alone. -/
def MgData.ah (_ : MgData Xi P Tok rows cols nR X) : ℕ → String → Bool :=
  fun _ n => n == "K8.equations"

/-- The stated functions: ONE, with three arms by the sort of the open segment. -/
def MgData.St : Stated := Stated.of (uBySort 𝔇.uL 𝔇.uA 𝔇.uH)

/-- What follows the batching in segment m: the link's own sub-protocols behind it. -/
def MgData.after (m : ℕ) (s : First.S) : Except String First.S :=
  match 𝔇.lk m with
  | some L => L.runBehind s
  | none => .error "the first chain has no link of that number"

/-- The witness's words, read through the book in the verifier's state: ONE reader for the row at
the
last point and for the pile of pending rows. -/
def MgData.rdW (a : P × First.S) (w : Wit (CellsQ rows cols) Tok MsgT) : OnBytes.Means.Words GE :=
  wordsFirst 𝔇.arr a.2.st a.2.book w

/-- The reader of the pile of pending rows: the matrix off the witness's cells; the masks off these
words. -/
def MgData.rw13 : P × First.S → Wit (CellsQ rows cols) Tok MsgT →
    K13.Law.Wit GE nR 𝔇.P13.lin.kCol := K13.Law.rwBook 𝔇.arr 𝔇.mat13

/-- The table of cells that the tie reads: THE SAME accessor through which forms, formsT and total
read the witness. -/
noncomputable def MgData.A1 :
    ℕ → P × First.S → Wit (CellsQ rows cols) Tok MsgT → ℕ → ℕ → ℕ → Cb.Gl.E :=
  cellsAt 𝔇.cs 𝔇.arr 𝔇.ms 𝔇.N

/-- The public tests' parameters as the composed term makes them: from the public parameters X, the
built segments and the term's own parameters. -/
def MgData.pubD : PubData :=
  { 𝔇.toPubData0 with
    mH := headLink X
    hShape := X.hS
    iU3 := iU3At X
    nextOf := First.FillK4.nextOfPlan X
    Rd := 𝔇.Rd
    runs := 𝔇.runs
    ah := 𝔇.ah
    nsOf := fun m => (𝔇.built[m]?).map (·.ns)
    dS := First.FillSent.sentDataAt 𝔇.shape 𝔇.N 𝔇.links (First.flatPlacesOf 𝔇.links true) 𝔇.built
    dS1 := First.FillSent.sentData1At 𝔇.shape 𝔇.N 𝔇.links (First.flatPlacesOf 𝔇.links true) 𝔇.built
    d3 := K3Data.of X 𝔇.sent
    d5 := { links := 𝔇.links, W := X, ownOf := fun m => 𝔇.N.sent m 0, shape := 𝔇.shape } }

/-- The data of the last sub-protocols' part, from the one structure of parameters. -/
def d13 : DataK13 P (Wit (CellsQ rows cols) Tok MsgT) nR :=
  ⟨𝔇.P13, 𝔇.cs, 𝔇.shape, 𝔇.layout, 𝔇.N, 𝔇.rw13⟩

/-- The lookup arguments' part over the part for the output head's lookup argument. -/
noncomputable def fillK3Both (M : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) :
    Meaning P (Wit (CellsQ rows cols) Tok MsgT) :=
  letI := VerifiableInference.OnPublicFiles.k3SizesAt X
  letI := VerifiableInference.OnPublicFiles.k3PolicyAt X
  fillK3All X 𝔇.sent 𝔇.l3 (fillK3HeadG X 𝔇.sent 𝔇.l3 (VerifiableInference.OnPublicFiles.k3AdrAt X) 𝔇.rq
    (fun w => VerifiableInference.OnPublicFiles.Flat.InRange w.cells) M)

/-- The parts beneath: the other authors' and the table's own. -/
noncomputable def mgBelow : Meaning P (Wit (CellsQ rows cols) Tok MsgT) :=
  fillK13 (d13 𝔇) (fillK3Both 𝔇
    (fillK6K7 X.hS (iU3At X) (headLink X) (fillK4 𝔇.links (First.FillK4.nextOfPlan X)
      (First.FillP1.fillP1 𝔇.d1 𝔇.rw13 𝔇.A1 𝔇.cr1
        (H2K5.Door.fillK5 𝔇.pubD.d5 (First.FillSent.fillSent 𝔇.pubD.dS
          (First.FillSent.fillSent1 𝔇.pubD.dS1 (First.FillBare.fillBare 𝔇.links
            (fillRowFirst 𝔇.arr 𝔇.N (fillWrow 𝔇.P13 𝔇.rdW (fillKeeper 𝔇.pubD.nsOf Mg)))))))))))

/-- **The table asks no test that says a fact on every reached state**: "in order" is Mg's own
again,
and the names that leave (`First.leavesName`) are taken out of the list of extra public tests. -/
def shut (Mg M : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) :
    Meaning P (Wit (CellsQ rows cols) Tok MsgT) :=
  { M with inOrder := Mg.inOrder, more := M.more.strike First.leavesName }

/-- **THE ONE TERM.** -/
noncomputable def mgAll : Meaning P (Wit (CellsQ rows cols) Tok MsgT) :=
  meaningForms 𝔇.cs 𝔇.arr 𝔇.ms 𝔇.Rd 𝔇.runs 𝔇.St 𝔇.after 𝔇.N 𝔇.wt 𝔇.rw 𝔇.ah
    (P5J.meaningQAt (headLink X) 𝔇.put (oneDec 𝔇.decT 𝔇.H) 𝔇.headPart 𝔇.digitsPart
      (meaningSig 𝔇.cs 𝔇.G 𝔇.arr 𝔇.smp 𝔇.ms 𝔇.decT
        (P5J.withReq 𝔇.reqB (shut Mg (mgBelow 𝔇 Mg)))))

/-- What a run evaluates is what the laws speak of. -/
theorem mgAll_pub : (mgAll 𝔇 Mg).pub = pubAll 𝔇.pubD Mg.pub := rfl

theorem mgAll_forms : (mgAll 𝔇 Mg).forms = fun m k r (a : P × First.S) y w =>
    (∀ p ∈ 𝔇.runs m k r,
      if 𝔇.ah p.1 p.2 = true then
        formsQA (𝔇.N.sent m) (𝔇.N.group m) (𝔇.Rd m) p.1 p.2 a.2 (seatTab 𝔇.cs 𝔇.arr 𝔇.ms w)
      else formsQ (𝔇.Rd m) (𝔇.N.group m) p.1 p.2 a.2 (seatTab 𝔇.cs 𝔇.arr 𝔇.ms w)) ∧
      (r = "weights" → 𝔇.wt m a y w) := rfl

theorem mgAll_formsT : (mgAll 𝔇 Mg).formsT = fun m k r (a : P × First.S) y w =>
    (∀ p ∈ 𝔇.runs m k r,
      formsTQ (𝔇.Rd m) 𝔇.St (𝔇.N.sent m 0) p.1 p.2 a.2 (seatTab 𝔇.cs 𝔇.arr 𝔇.ms w)) ∧
      (r = "weights" → 𝔇.wt m a y w) := rfl

theorem mgAll_total : (mgAll 𝔇 Mg).total = fun m (a : P × First.S) _ w =>
    totalQ (𝔇.N.group m) a.2 (seatTab 𝔇.cs 𝔇.arr 𝔇.ms w) ∧ 𝔇.rw m a.2 = true := rfl

theorem mgAll_totalB : (mgAll 𝔇 Mg).totalB = fun m (a : P × First.S) _ w =>
    totalBQ (𝔇.after m) (𝔇.N.group m) a.2 (seatTab 𝔇.cs 𝔇.arr 𝔇.ms w) ∧ 𝔇.rw m a.2 = true := rfl

theorem mgAll_constr : (mgAll 𝔇 Mg).constr =
    P5J.constrQAt (headLink X) 𝔇.put (oneDec 𝔇.decT 𝔇.H) 𝔇.headPart 𝔇.digitsPart := rfl

theorem mgAll_pin : (mgAll 𝔇 Mg).pin = pinJT 𝔇.cs 𝔇.G 𝔇.arr 𝔇.smp 𝔇.ms := rfl

theorem mgAll_noColl : (mgAll 𝔇 Mg).noColl = noCollJT 𝔇.cs 𝔇.G 𝔇.smp 𝔇.ms := rfl

theorem mgAll_shown : (mgAll 𝔇 Mg).shown = shownJT 𝔇.cs 𝔇.G 𝔇.ms := rfl

theorem mgAll_held :
    (mgAll 𝔇 Mg).held = fun j t (a : P × First.S) => smpHeld a.2.st a.2.book j t := rfl

theorem mgAll_pinW : (mgAll 𝔇 Mg).pinW = pinWOf 𝔇.decT := rfl

/-- The field that two parts give outright is the oracle messages' own sentence, by `oneDec`. -/
theorem mgAll_decodes : (mgAll 𝔇 Mg).decodes = decodesOf 𝔇.decT := rfl

/-- "In order": Mg's own, and a test on the public part alone. -/
theorem mgAll_inOrder_at (a : P × First.S) : (mgAll 𝔇 Mg).inOrder a =
    (Mg.inOrder a && (_root_.Meaning.backReq (𝔇.reqB a.1)).isSome) := rfl

theorem mgAll_row : (mgAll 𝔇 Mg).row = (fillRowFirst 𝔇.arr 𝔇.N Mg).row := rfl

theorem mgAll_pile : (mgAll 𝔇 Mg).pile = (fillK13 (d13 𝔇) Mg).pile := rfl

theorem mgAll_pileOne : (mgAll 𝔇 Mg).pileOne = (fillK13 (d13 𝔇) Mg).pileOne := rfl

theorem mgAll_more : (mgAll 𝔇 Mg).more = (mgBelow 𝔇 Mg).more.strike First.leavesName := rfl

theorem mgAll_tie : (mgAll 𝔇 Mg).tie = First.K8.tieK8Rec 𝔇.A1 := rfl

theorem mgAll_wo : (mgAll 𝔇 Mg).wo = First.FillP1.woAt 𝔇.d1 𝔇.rw13 := rfl

theorem mgAll_carry : (mgAll 𝔇 Mg).carry = 𝔇.cr1 := rfl

theorem mgAll_wrow : (mgAll 𝔇 Mg).wrow = fun a _ w => K13.Law.WRow 𝔇.P13 a.2 (𝔇.rdW a w) := rfl

theorem mgAll_worth : (mgAll 𝔇 Mg).worth = (fillK3Both 𝔇 Mg).worth := by
  unfold mgAll shut mgBelow meaningForms P5J.meaningQAt meaningSig P5J.withReq fillK13 fillK3Both
    fillK3All VerifiableInference.OnPublicFiles.fillK3Worth First.Look.fillK3 fillK3HeadG fillK3Head
    fillK6K7 fillK4 First.FillP1.fillP1 H2K5.Door.fillK5 First.FillSent.fillSent
    First.FillSent.fillSent1 First.FillBare.fillBare fillRowFirst First.fillRow fillWrow fillKeeper
  rfl

theorem mgAll_pubP : (mgAll 𝔇 Mg).pubP =
    (First.Look.fillK3 X 𝔇.sent (First.FillP1.fillP1 𝔇.d1 𝔇.rw13 𝔇.A1 𝔇.cr1 Mg)).pubP := rfl

/-- **At the full size's number the term is the meaning at which the top-level laws are stated.** -/
theorem mgAll_is_tower (h : headLink X = 24) :
    mgAll 𝔇 Mg =
      P5J.meaningQ 𝔇.put (oneDec 𝔇.decT 𝔇.H) 𝔇.headPart 𝔇.digitsPart
        (meaningSig 𝔇.cs 𝔇.G 𝔇.arr 𝔇.smp 𝔇.ms 𝔇.decT
          (P5J.withReq 𝔇.reqB
            (meaningForms 𝔇.cs 𝔇.arr 𝔇.ms 𝔇.Rd 𝔇.runs 𝔇.St 𝔇.after 𝔇.N 𝔇.wt 𝔇.rw 𝔇.ah
              (shut Mg (mgBelow 𝔇 Mg))))) := by
  unfold mgAll
  rw [h]
  rfl

end

/-! ## Has each part code? Definitions with code that call its pub. -/

section
variable {Xi P Tok : Type} {rows cols : ℕ} {X : OnBytes.Model.Verify.Public}

def codeKeeper (nsOf : ℕ → Option ℕ) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
    (q : Pub) (a : P × First.S) : Bool := (fillKeeper nsOf Mg).pub q a

def codeReq (reqB : P → ByteArray) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
    (q : Pub) (a : P × First.S) : Bool := (P5J.withReq reqB Mg).pub q a

def codeSig (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
    (smp : P × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem)
    (decT : (ℕ → Option (ℕ × List UInt64)) → P × First.S → Option (CellsQ rows cols))
    (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (q : Pub) (a : P × First.S) : Bool :=
  (meaningSig cs G arr smp ms decT Mg).pub q a

def codeQ (hd : ℕ) (put : P5J.TReq → Fin Inst.Model.ppref.V → P5J.TReq)
    (H : P5J.HidAt X P (Wit (CellsQ rows cols) Tok MsgT) rows cols)
    (headPart : P5J.TPart → IdxQ → P × First.S → Strs →
      Wit (CellsQ rows cols) Tok MsgT → Prop)
    (digitsPart : ℕ → P × First.S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop)
    (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (q : Pub) (a : P × First.S) : Bool :=
  (P5J.meaningQAt hd put H headPart digitsPart Mg).pub q a

def codeForms (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (Rd : ℕ → Readers)
    (runs : ℕ → ℕ → String → List (ℕ × String)) (St : Stated)
    (after : ℕ → First.S → Except String First.S) (N : Numbers)
    (wt : ℕ → P × First.S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop) (rw : ℕ → First.S → Bool)
    (ah : ℕ → String → Bool)
    (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (q : Pub) (a : P × First.S) : Bool :=
  (meaningForms cs arr ms Rd runs St after N wt rw ah Mg).pub q a

def codeK4 (links : List ModelPart) (nextOf : ℕ → Option ℕ)
    (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (q : Pub) (a : P × First.S) : Bool :=
  (fillK4 links nextOf Mg).pub q a

def codeK6K7 (h : OnBytes.Model.Head.Shape) (iU3 mH : ℕ)
    (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (q : Pub) (a : P × First.S) : Bool :=
  (fillK6K7 h iU3 mH Mg).pub q a

def codeK13 {nR : ℕ} (D : DataK13 P (Wit (CellsQ rows cols) Tok MsgT) nR)
    (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (q : Pub) (a : P × First.S) : Bool :=
  (fillK13 D Mg).pub q a

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.oneDec_self
#print axioms VerifiableInference.Desc.Sound.dec_is_cells
#print axioms VerifiableInference.Desc.Sound.mgAll_pub
#print axioms VerifiableInference.Desc.Sound.mgAll_forms
#print axioms VerifiableInference.Desc.Sound.mgAll_formsT
#print axioms VerifiableInference.Desc.Sound.mgAll_total
#print axioms VerifiableInference.Desc.Sound.mgAll_totalB
#print axioms VerifiableInference.Desc.Sound.mgAll_constr
#print axioms VerifiableInference.Desc.Sound.mgAll_pin
#print axioms VerifiableInference.Desc.Sound.mgAll_noColl
#print axioms VerifiableInference.Desc.Sound.mgAll_shown
#print axioms VerifiableInference.Desc.Sound.mgAll_held
#print axioms VerifiableInference.Desc.Sound.mgAll_pinW
#print axioms VerifiableInference.Desc.Sound.mgAll_decodes
#print axioms VerifiableInference.Desc.Sound.mgAll_inOrder_at
#print axioms VerifiableInference.Desc.Sound.mgAll_row
#print axioms VerifiableInference.Desc.Sound.mgAll_pile
#print axioms VerifiableInference.Desc.Sound.mgAll_pileOne
#print axioms VerifiableInference.Desc.Sound.mgAll_more
#print axioms VerifiableInference.Desc.Sound.mgAll_tie
#print axioms VerifiableInference.Desc.Sound.mgAll_wo
#print axioms VerifiableInference.Desc.Sound.mgAll_carry
#print axioms VerifiableInference.Desc.Sound.mgAll_wrow
#print axioms VerifiableInference.Desc.Sound.mgAll_worth
#print axioms VerifiableInference.Desc.Sound.mgAll_pubP
#print axioms VerifiableInference.Desc.Sound.mgAll_is_tower
