-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/LettersAt.lean: THE ONE FILE OF CLOSED LETTERS: THE VALUES, AT THE SEATED DESCRIPTION's OWN TERM, OF THE LETTERS THAT THE TABLE OF JOINTS, THE COMPOSED MEANING (mgAll) AND THE TOPS' LAWS SHARE. Definitions, each a function of the term's four letters (o · Zp · Np · cF) and of nothing else; a few lemmas that say what they are. THE VALUES ALONE: the structure 𝔇At stands in Johnson/P5J/LettersRec.lean, so that this file, the named tests and the one head hang on NO text of the composed meaning. Over the makers at Johnson.P5T.*. front_cons | front_zero stand here [as the file lies, front_zero stands here; front_cons is not in this library]: IT TAKES EACH VALUE AS IT COMES.
A joint build of the files of several groups.

THE FOUR LETTERS ARE FUNCTIONS OF THE THREE PUBLIC FILES WHERE THE VALUE IS LAID (Johnson/P5J/LaidOpens.lean: laid_opens).
CLOSED HERE (namespace P5J.At), with whose text each is:
  G       the seated description: F0T o Zp Np cF (Johnson/P5J/AtTerm.lean)
  cs · shape · layout   the first chain's parameters' codes, request's shape and layout (off the plan)
  links · mH · ps       the segments' sorts at the full size (fullLinks, Johnson/P5J/MeansQ.lean: twelve times layers, attention; then the head) · the head's segment's number (mH_is: the place of .head in links, by the kernel) · the written list of places
  told    what each block of the first chain tells (toldOf, Johnson/Desc/Sound/PieceFence.lean)
  pseats · seats        the plan's seats of the first chain (planSeats Zp Zp.D.1, Johnson/P5T/PlanSeats.lean: AT Zp.D.1, the public part's own declared rounds of the first chain: the term at which two files of evaluations ran it: PlanNumbersRun.lean [not in this library] · OnAtWalk.lean [not in this library]) · their (tree, tenant)
  N       ((numbersOf pseats).withRows shape (possAt cF.blocksInOrder 25) 25).withTold ps told: the table's files' Numbers.atBlocks (Johnson/Desc/First/NumbersAtBlocks.lean), BUT AT THE WRITTEN LIST ps in the place of the blocks' own places (N_atBlocks: one where these two lists are one)
  c₀      the zero table (the extractor lays it only where the decoder is silent)
  pseatsAll · arr · num   the seats of ALL THREE chains (planSeatsAll Zp Zp.D) · arrOf over them: ONE arr FOR ALL THREE TABLES · the witness's number of (link, message), at the same list
  rad · ms  the sampled oracle messages' radii off the rows of the sendings (sendRowsOf), at one letter more: lay (0 where the rows have none) · the members: shapes and seats by the make off pseats, the radii rad's (P5T.msAtR)
  d₀ · H  the first request (a default that is reached nowhere inside "in order") · hidAtSeat at these letters, AT THE SEATS AS A FUNCTION OF THE LABEL: seatBy (fLay layout num) X (sizesOf X) (by report: every fence's law ends in that form; headPart | wt bear it inside; SeatsNamed is then paid without scope); arr and num off one list (pseatsAll) by their own definitions: UNDER THREE PREMISES ON THE PLAN, each with a test with code: laidThere (it fences the seats' silent (0, 0, 0)) · SeatsNamed · GroupsSeated
  lk · rw   the first chain's links by number · the rows' fit at a segment's batching round
  (𝔇At, the structure of the composed meaning's letters with these values laid: Johnson/P5J/LettersRec.lean)
  smp     the reader of samples by the message's fixed number (smpNamed cs seats): WITHOUT CODE
  nsOf    the plan's number of slots of a segment's ledger
  reqB · reqW · get    the request's bytes, its words, the tables' reader
  X       the program's public data (Verify.Public): the public part's own (Zp.p.X)
  put · Tok · tokOf · f   the request with a reply laid (putReq) · a token as a number · the token that the verifier's state has heard, else 0 · a number as a token of the vocabulary, else 0 (Johnson/P5J/TokTerms.lean)
NOT CLOSED, NAMED SO THAT NOBODY TAKES THE FILE FOR WHOLE: decT := dtK E o Zp Np cF hs 0: E (the tower's coding, with pp) is a letter still, hs a premise on the plan · H's three premises · every field of mgAll's structure of letters that no value here fills.
err := 0 IS SAFE FOR decT ALONE (its value is one at every err: decK_err := rfl, declared nowhere in this library): err is the sample map's COUNT of bad seeds: a law that asks "the sample map is OK" is unpayable at 0: whoever calls such a law calls it at ITS err' and crosses by decK_err | dcdAt_err | collAt_err (none of them declared in this library): NOBODY LAYS 0 INTO A COUNT.
LEMMAS: mH_is · N_atBlocks · noRec_decT (the decoder does not read the first chain's state: the stored table's conduit's premise) · told_is (toldOf is the "oracles.flatten" of the files of evaluations) · front_at (no tree and no message in front of the front block, at N) · ps_head.

Limits. Definitions and their unfoldings. The full size alone. NO MEMBER. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.TieAtTerm
import Johnson.Desc.First.FillStart
import Johnson.P5T.NumbersOf
import Johnson.P5T.NumOfPlan
import Johnson.P5T.MembersByMake
import Johnson.P5J.HidAtList
import Johnson.Desc.ProofFile.LinkAt
import Johnson.P5T.RowsFitAt
import Johnson.P5T.ArrAll
import Johnson.Desc.Sound.SmpNamed
import Johnson.Desc.Sound.PieceFence
import Johnson.P5J.TokTerms
import Johnson.Desc.First.NumbersAtBlocks
import Johnson.Desc.First.Look.K3StoredThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J.At
open VerifiableInference.Desc (FileDescription Chain Block Place Oracle)
open VerifiableInference.Desc.First (Numbers ModelPart flatPlacesOf frontPlace)
open VerifiableInference.Desc.Sound (toldOf smpNamed Sending)

variable (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)

/-- The seated description. -/
abbrev G : FileDescription ProofFile.Inst := F0T o Zp Np cF

/-- The first chain's parameters' codes, the request's shape, its layout. -/
def cs : OnBytes.Codes := Zp.made.p.chains.proof.first.codes
def shape : OnBytes.Params.ReqShape := Zp.made.p.chains.proof.first.shape
def layout : OnBytes.Params.ReqLayout := Zp.made.p.chains.proof.first.layout

/-- The segments' sorts at the full size; the head's segment's number; the written list of places. -/
def links : List ModelPart := fullLinks
def mH : ℕ := 24
def ps : List Place := flatPlacesOf fullLinks true

/-- What each block of the first chain tells. -/
def told : List (List Oracle) := toldOf cF.blocksInOrder

/-- The plan's seats of the first chain; their (tree, tenant). -/
def pseats : List P5T.PSeat := P5T.planSeats Zp Zp.D.1
def seats : List (ℕ × ℕ) := (pseats Zp).map fun p => (p.j, p.t)

/-- **The table's numbers**: the seats off the plan (numbersOf) · rowsAt off the plan's shape and the blocks' declared positions (withRows) · treesAt | msgsAt off what the blocks tell (withTold), AT THE WRITTEN LIST OF PLACES. -/
def N : Numbers :=
  ((P5T.numbersOf (pseats Zp)).withRows (shape Zp) (VerifiableInference.Desc.First.possAt cF.blocksInOrder links.length)
    links.length).withTold ps (told cF)

/-- The plan's seats of all three chains, the first chain's first: at the public part's own declared rounds. -/
def pseatsAll : List P5T.PSeat := P5T.planSeatsAll Zp Zp.D

/-- **The numbers of the witness's messages: OVER ALL THREE CHAINS' SEATS: ONE arr FOR ALL THREE TABLES** (by report: arrOf gives every seat outside its list one number: over the first chain's list alone the later chains' tenants would all bear one number, and their pins would pin one component of the witness to different messages). TWO TERMS HAVE RUN
(one large run at all three chains' seats, THERE AT THE DESCRIPTION's declared rounds, here at the public part's Zp.D: that these two are one is said by nothing here; two runs at the first chain's seats alone); that the terms agree at every seat of the first chain is a theorem: P5T.arrOf_all | numOfPlan_all (Johnson/P5T/ArrAll.lean). -/
def arr : ℕ → ℕ → ℕ := P5T.arrOf (pseatsAll Zp)

/-- The witness's number of (link l, message k): read at the same list as arr. -/
def num : ℕ → ℕ → ℕ := P5T.numOfPlan (pseatsAll Zp)

/-- The radii of the sampled oracle messages, by (sending, place): off the rows of the sendings at the three public files: lay IS ONE LETTER MORE. 0 WHERE THE ROWS HAVE NONE: whoever reads a radius takes the named test P5T.radIsB beside. -/
def rad (lay : ByteArray) : ℕ → ℕ → ℕ := P5T.radOf ((P5T.rowsAt? Zp.pol lay Zp.KL).getD [])

/-- **The members**: SHAPES AND SEATS BY THE MAKE OFF THE PLAN's SEATS (the first chain's list), the radii off the rows of the sendings. -/
def ms (lay : ByteArray) : List VerifiableInference.Desc.Sound.Mem := P5T.msAtR Zp (rad Zp lay)

/-- The reader of samples. WITHOUT CODE (its text chooses a seed with the kept row's matrix): a walk cannot evaluate it: a twin with code is owed by smpNamed's file (Johnson/Desc/Sound/SmpNamed.lean). -/
noncomputable def smp (a : ProofFile.InstPub × TS) (s : Sending) (i : Fin s.l.length) :
    Option ((Johnson.Pack.sigOf (cs Zp) s.l).om i).Smp := smpNamed (cs Zp) (seats Zp) a s i

/-- The plan's number of slots of a segment's ledger. -/
def nsOf (m : ℕ) : Option ℕ := (Zp.made.p.built.links[m]?).map (·.ns)

/-- The request's bytes; its words; what the instance asks; the tables' reader. -/
def reqB (q : ProofFile.InstPub) : ByteArray := q.request
def reqW (q : ProofFile.InstPub) : Array UInt32 := OnBytes.Model.Verify.words32 q.request
def get (a : ProofFile.InstPub × TS) : ProofFile.InstPub × TS := (a.1, a.2)

/-- The program's public data. -/
def X : OnBytes.Model.Verify.Public := Zp.p.X

/-- The request with a reply laid; a token as a number; the token heard; a number as a token. -/
def put : TReq → Fin Inst.Model.ppref.V → TReq := OnBytes.Flat.putReq
abbrev Tok : Type := ℕ
def tokOf (a : ProofFile.InstPub × TS) : Tok := tokOfHeard a
def f : Tok → Fin Inst.Model.ppref.V := tokVOf

/-- **The one decoder**, at err := 0. err is the sample map's number of bad seeds, which a count may read: the decoder, the collision and the reader of the out-of-domain sample do not (decK_err := rfl, declared nowhere in this library: free). STILL LETTERS: the tower's coding E (with pp); A PREMISE: hs, the test on the plan's shape. -/
noncomputable def decT {pp : Inst.Model.ScalesAndPolicy}
    (E : OnBytes.Flat.Coding (OnBytes.Flat.claimsReqAt (OnBytes.Slice.frS.toDecR OnBytes.Slice.frZ 402653181)
      OnBytes.Flat.numsFull pp))
    (hs : Desc.K14.Law.fullShapeB (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S = true) :
    (ℕ → Option (ℕ × List UInt64)) → ProofFile.InstPub × TS → Option (CellsM OnBytes.Flat.numsFull) :=
  dtK E o Zp Np cF hs 0

/-- The zero table. -/
def c₀ : CellsM OnBytes.Flat.numsFull := fun _ _ => 0

/-- The first chain's links, by number (ProofFile.linkAt, Johnson/Desc/ProofFile/LinkAt.lean: off the public part alone): the segments' readers and "what runs behind" are made of it. NOTHING where the chain cannot be made or has no link of that number. -/
def lk (m : ℕ) : Option (VerifiableInference.Desc.Link TS ProofFile.Cl) := ProofFile.linkAt Zp m

/-- Do the rows fit at segment m's batching round? FALSE where the plan has no such round. -/
def rw (m : ℕ) (s : TS) : Bool := P5T.rwAt Zp m s

/-- The first request: what "req" answers where the bytes are no request's: reached nowhere inside "in order". -/
def d₀ : TReq := OnBytes.Flat.firstReq

section Rec
variable {pp : Inst.Model.ScalesAndPolicy}
  (E : OnBytes.Flat.Coding (OnBytes.Flat.claimsReqAt (OnBytes.Slice.frS.toDecR OnBytes.Slice.frZ 402653181)
    OnBytes.Flat.numsFull pp))
  (hs : Desc.K14.Law.fullShapeB (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S = true)
  (lay : ByteArray)
  (hL : Meaning.laidThere (X Zp) (Meaning.sizesOf (X Zp)) (layout Zp) = true)
  (hN : VerifiableInference.Desc.Sound.SeatsNamed (arr Zp) (N Zp cF) (Meaning.sizesOf (X Zp))
    (Meaning.seatBy (Meaning.fLay (layout Zp) (num Zp)) (X Zp) (Meaning.sizesOf (X Zp))))
  (hG : VerifiableInference.Desc.Sound.GroupsSeated (ms Zp lay) (N Zp cF))

/-- **How a witness is read.** -/
noncomputable def H : HidAt (X Zp) ProofFile.InstPub
    (VerifiableInference.Desc.Wit (CellsM OnBytes.Flat.numsFull) Tok VerifiableInference.Desc.Sound.MsgT)
    OnBytes.Flat.numsFull.rows (colsAt OnBytes.Flat.numsFull) :=
  have _ := hL
  hidAtSeat (X Zp) (cs Zp) (arr Zp) (ms Zp lay) (N Zp cF) (Meaning.sizesOf (X Zp))
    (Meaning.seatBy (Meaning.fLay (layout Zp) (num Zp)) (X Zp) (Meaning.sizesOf (X Zp))) tokVOf
    (fun a => (Meaning.backReq (reqB a.1)).getD d₀) (fun a y => decT o Zp Np cF E hs y.cell a) hN hG

end Rec

/-- The head's segment's number is the place of the head in the list of sorts. -/
theorem mH_is : links[mH]? = some ModelPart.head ∧ links.length = mH + 1 := by decide

/-- toldOf is the term of the files of evaluations. -/
theorem told_is : told cF = cF.blocksInOrder.map fun b => b.oracles.flatten := by
  unfold told toldOf
  simp [List.flatMap_id]

/-- **N is the table's files' "numbers closed over the blocks"** (Numbers.atBlocks), where the blocks' own places are the written list. -/
theorem N_atBlocks (h : VerifiableInference.Desc.First.blockPlaces cF.blocksInOrder = ps) :
    N Zp cF = (P5T.numbersOf (pseats Zp)).atBlocks (shape Zp) links cF.blocksInOrder := by
  unfold N VerifiableInference.Desc.First.Numbers.atBlocks
  rw [h, told_is]
  rfl

/-- **The one decoder does not read the first chain's state.** -/
theorem noRec_decT {pp : Inst.Model.ScalesAndPolicy}
    (E : OnBytes.Flat.Coding (OnBytes.Flat.claimsReqAt (OnBytes.Slice.frS.toDecR OnBytes.Slice.frZ 402653181)
      OnBytes.Flat.numsFull pp))
    (hs : Desc.K14.Law.fullShapeB (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S = true) :
    VerifiableInference.Desc.First.Look.Stored.NoRec (decT o Zp Np cF E hs) := fun _ _ _ _ => rfl

/-- A list whose first member is a begins with a. (Said of a letter: so that no closed list is unfolded.) -/
theorem cons_of_head {α : Type} : ∀ (l : List α) (a : α), l[0]? = some a → ∃ t, l = a :: t
  | [], _, h => by cases h
  | b :: t, a, h => ⟨t, by rw [show b = a from Option.some.inj h]⟩

/-- The written list begins with the front's place. -/
theorem ps_head : ∃ l, ps = frontPlace :: l := cons_of_head _ _ front_first_full

/-- At the numbers off what the blocks tell, no tree and no message stand in front of the front block: any numbers, any telling. -/
theorem front_zero (N₀ : Numbers) (tl : List (List Oracle)) :
    (N₀.withTold ps tl).treesAt (some frontPlace) = 0 ∧ (N₀.withTold ps tl).msgsAt (some frontPlace) = 0 := by
  obtain ⟨l, hl⟩ := ps_head
  rw [hl]
  exact VerifiableInference.Desc.First.withTold_front N₀ frontPlace l tl

/-- No tree and no message stand in front of the front block, at N. -/
theorem front_at : (N Zp cF).treesAt (some frontPlace) = 0 ∧ (N Zp cF).msgsAt (some frontPlace) = 0 :=
  front_zero _ _

end P5J.At

#print axioms P5J.At.mH_is
#print axioms P5J.At.told_is
#print axioms P5J.At.N_atBlocks
#print axioms P5J.At.noRec_decT
#print axioms P5J.At.ps_head
#print axioms P5J.At.front_at
