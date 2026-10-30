-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/HonestTrace/ConstrAtThread.lean

The library's sentence for the items "constr m p" at the first chain's honest side as
Johnson/Desc/ProofFile/Honest/Thread/FirstHead.lean sets it up (lettersHead). Conditional lemmas:
under lettersHead's premises h : AtMgA ..., at a served request and under three conditions on the
parameter Q, a Script (ScriptTies), the sentence of 97 of the 100 such items that are open at the
chain's start holds of the witness that Q makes. The type T of the input's own trace is a letter, as
it is in lettersHead. No member of AtMgA and none of ScriptTies is shown here.
This file states no goal.
It imports two modules under Johnson/Goal/ directly: Johnson/Goal/HonestTrace/ConstrAtTrace.lean and
Johnson/Goal/HonestTrace/SeatsApartAtHead.lean.

The setting. lettersHead takes h : AtMgA ..., a structure of premises on the public files, and Q :
Script ..., which says what the honest prover's messages are as functions of a run's coins k, its
input v and the challenges heard. Q has no body there: it is a parameter. Q.wit k v hd is the
witness made of it. "means v (Item.constr m p) a y w" unfolds to constrQAt (Johnson/P5J/MeansQ.lean)
at the library's hidAtSeat, with the constant decoder "some (Q.cells v)". Four letters: T is the
type of the input's field "trace"; Tr (Johnson/HonestTrace/Full.lean) is the type of a trace of
integers; τ is such a trace; rd is a function from inputs to such traces.

Main definitions and theorems:
* "ScriptSymsAt Z Zp cF Q k v τ": at every list of challenges hd, SymsOfTrace
  (Johnson/Goal/HonestTrace/ConstrAtTrace.lean) at the layout's seats, the messages of Q.wit k v hd
  and τ. "ScriptSyms Z Zp cF Q rd": the same at all k and v, at τ := rd v. "scriptSymsAt_of_syms":
  from the second to the first, at an input with rd v = τ. "ScriptSymsRaw Zp Q rd": the like
  equation on Q.msg itself, place by place. It is another sentence: hidAtSeat reads through readAt,
  which at a place of a pad yields the pad; under h no seat inside the sizes lies at such a place.
* "syms_of_raw": under h: ScriptSymsRaw gives ScriptSyms.
* "ScriptSymsRawOn Zp Q k v τ P": the equation of ScriptSymsRaw at one k, one v and τ, at every hd,
  on the entries a of the sub-proofs m with P m a. "rawOn_of_raw": ScriptSymsRaw gives it at every k
  and v, at rd v, on all entries. "rawOn_of_two": on the entries that P₁ picks and on those that P₂
  picks it gives it on all, where each pair (m, a) is picked by one of the two.
  "scriptSymsAt_of_rawOn": under h, on all entries it gives ScriptSymsAt at that k, v and τ.
* "scriptSymsRaw_member": where the layout's seats are apart (SeatsApart,
  Johnson/Goal/HonestTrace/SeatsApartOfLayout.lean), some Script meets ScriptSymsRaw, at every rd;
  it differs from a given one in main rows alone. "scriptSyms_member": under h and SeatsApart, some
  Script meets ScriptSyms. "scriptSyms_member_at_head": under h alone, by seatsApart_at_head
  (Johnson/Goal/HonestTrace/SeatsApartAtHead.lean).
* "ScriptTies Z Zp cF Q k v i x": three conditions: Q.cells v holds the index i; the request's
  bytes, read back, with Q's token laid in where the outcome is well formed, are x; ScriptSymsAt at
  k, v and theTrace X i x. "scriptTies_of_rawOn": under h, the first two and ScriptSymsRawOn at
  theTrace X i x, on the entries that two such predicates pick, give ScriptTies.
* "SeatsFixed Zp Q": Q.fixedMsg is 0 at every number of a message that a seat inside the sizes
  names. "scriptSymsAt_of_nil": under h and SeatsFixed, SymsOfTrace at the empty list of challenges
  gives ScriptSymsAt. "ScriptTiesAtNil": the first two conditions of ScriptTies, SeatsFixed, and
  SymsOfTrace at the empty list. "scriptTies_of_nil": under h it gives ScriptTies.
* "constr_at_thread": under h, at a served request and under ScriptTies: the sentence of Item.constr
  m p holds of Q.wit k v ds, at every state s, all strings y and every list ds, for p among idn,
  lookCalls, rider, small and m < 24, and for m = 24 and p = small. "items_constr_at_thread": the
  same as Thread.Items at the one item, the form in which the honest side asks it.
* "ridesPastAt_constr": under h: RidesPastAt (Johnson/Desc/ProofFile/Honest/Thread/Shares.lean) for
  Item.constr m p at every border number b, every m and each of the four parts.
* "scriptTies_and_trace_iff": at T := Tr: ScriptTies' first two conditions, v.trace = theTrace X i x
  and ScriptSymsAt at v.trace hold together exactly where ScriptTies holds and v.trace = theTrace X
  i x.

Nearest kin. The clause cells says of one input that the Script's cells hold an index; i is a free
letter, and nothing here ties it to the input's own index. A form of that sentence under the name
"CellsAreIndex" is not in the library as this file enters it. The clause on the messages has three
kin: "msg_of_laysCells_all" (Johnson/Desc/ProofFile/Honest/K5/Law/ReaderReadsOwn.lean); the field
msgs of "K1Seated" (Johnson/Desc/ProofFile/Honest/K1/Seated.lean; its sister field pads speaks of
pads, which the clause here leaves free); and "main_is_packed", which is not in the library yet
either. The first two speak at valid inputs and at lists of challenges no shorter than a bound; the
clause here speaks at every list, the empty one too. The sentence v.trace = theTrace X i x, which
stands on both sides of scriptTies_and_trace_iff, is kin to TraceOwn
(Johnson/FrontRoad/TracePremises.lean), TraceOwnAt (Johnson/FrontRoad/TraceOwnAtSpec.lean) and the
third clause of ReadyInput (Johnson/Desc/ProofFile/Honest/Thread/ReadyInput.lean). NO LEMMA HERE
JOINS ANY TWO OF THESE FORMS: such a lemma is wanted before two of them stand side by side as
premises.

Limits. These are conditional lemmas. THIS FILE SHOWS NO MEMBER OF AtMgA, the structure of premises
under which all its theorems but scriptSymsAt_of_syms, rawOn_of_raw, rawOn_of_two,
scriptSymsRaw_member and scriptTies_and_trace_iff stand. The library has one at every Z in scope at
which the goals' reader returns and the test protocolDataWellFormed accepts (head_of_live,
Johnson/Goal/Meaning/ServedChains.lean; protocolDataWellFormed, Johnson/Goal/Description/Live.lean, wants the
verifier's three values laid and, of them, an accept of dataWellFormedAtFullSizeDepth), and, in its side library, members
with no premise at two stored sets of full-size public files: VerifierAndGoals.storedPublicFiles (headMember_zFull,
AtFullSide/Top/HeadMemberAtFull.lean) and VerifierAndGoals.zGap (headMember_zGap,
AtFullSide/Top/HeadMemberAtGap.lean). None of these theorems is called here. NO MEMBER OF ScriptTies
IS SHOWN, HERE OR ELSEWHERE IN THE LIBRARY: so no theorem that takes it is shown to speak of any
Script, witness or run. Of the three clauses one, the clause on the messages, has a member under h,
at every rd, at a Script made for it; that it can be met only where the seats are apart is not
shown. The member that is shown is not shown to be an honest Script: its tables are the given
Script's, whatever its messages are. That much stands in the statement of scriptSymsRaw_member
alone: the two other members' statements keep the cells, the token and the pads, and are silent on
table, fixed, fixedMsg and the mask rows. ScriptSyms, ScriptSymsRaw and the members end at rd v, the
tie asks theTrace X i x: a caller brings rd v = theTrace X i x. rd is any function: a constant will
do, and it need not read the field "trace". P in ScriptSymsRawOn is the caller's, any predicate: the
cut shows neither half; a half whose predicate picks nothing holds idly, and the other half then has
to hold on all entries. The cover in rawOn_of_two and scriptTies_of_rawOn ranges over all pairs of
numbers, also beyond the 25 sub-proofs and their lists: that is more than the equation needs, and
two predicates that cover the entries and nothing else do not meet it. ScriptSymsRawOn is asked at
every hd, the empty list too. ScriptTies ties the input's own field "trace" to nothing. ON THE COINS
k: ScriptSyms and ScriptSymsRaw bind k under "for all": they are conditions on the Script.
ScriptSymsAt, ScriptSymsRawOn, ScriptTies and ScriptTiesAtNil stand at the coins of one run: whoever
measures over coins needs such a form at every k that the measure reaches. Of ScriptTies nothing
here shows that; ScriptSymsAt at every k follows from ScriptSyms, whose one member is at a Script
made for it. The clause req has THREE silent defaults. Where the request's bytes are not read back
it takes P5J.At.d₀. P5J.tokVOf yields 0 from the size of the vocabulary on. And OnBytes.Flat.putReq
(Johnson/Flat/TiesAtReq.lean) lays the token in only if the outcome is well formed; else it hands
the request back untouched: that is so where the request ends before the window's end and the token
is not 0 (putReq_else). So the clause can hold at an input whose bytes no reader takes; and from the
clause nobody may conclude that the reply of x is Q's token: before the window's end that reply is 0
at every token. OF THE FOUR CLAUSES AT Tr: they give ScriptTies; ScriptTies is not shown to give
them, and names v.trace nowhere. Each theorem under ScriptTies holds under the four clauses too, by
the first half of scriptTies_and_trace_iff and one call; that is stated of none. ScriptTiesAtNil has
no clause on v.trace, and no form of it with such a clause is stated. Under the seats three further
defaults answer in silence: Meaning.fLay gives (0, 0, 0) where the layout's reader finds no seat
(Johnson/Goal/Meaning/HidSeatsOf.lean); Meaning.labAt takes an empty entry's label past the end of
the plan's list (Johnson/Goal/Meaning/HidPlan.lean); readAt gives the message that is 0 everywhere
where its sub-proof's group has nobody with that number (Johnson/Desc/Sound/ReadAt.lean). The five
definitions and two structures take no h, so they can be written down where these defaults answer.
Four theorems take neither h nor SeatsApart (scriptSymsAt_of_syms, rawOn_of_raw, rawOn_of_two,
scriptTies_and_trace_iff): they hand these forms on from premise to conclusion unopened, and so hold
where the defaults answer too. The other eleven stand under h or under SeatsApart; that these
premises keep the defaults out is not stated here. SeatsFixed and ScriptTiesAtNil are conditions
too: no theorem of this file shows them of a Script (SeatsFixed holds by its text where Q.fixedMsg
is 0 everywhere, and scriptSymsRaw_member keeps the given fixedMsg: not joined here). That no seat
inside the sizes lies at a place of a pad of its own sub-proof's copy is had under h: the test
h.toAtMg.offC (Johnson/P5J/HidBearsAtMg.lean) is no field of AtMgA, but accepts under it by
offC_ofHead (Johnson/Top/H0/K2Ties/AtHead.lean), whose own limits come with it: the full size alone;
at the concrete earlier hash; from the test madePinnedAt, one of the entry tests that the verifier
asks of the proof file (LPFD.lawsAsk, Johnson/Desc/Laid/ProofAsks.lean), whose accept is drawn from
the fields "scope" and "laid" (pin_head, beside offC_ofHead): a verifier whose entry tests lack it
gives no such h. ScriptSymsAt is asked at every hd, the empty list too, because the items are open
from the start, where nothing has been heard, and are asked at every continuation. constr_at_thread
SPEAKS OF THE WITNESS Q.wit k v ds ALONE. items_constr_at_thread has the form in which a share
ExchangeAt ends; ExchangeAt itself is shown here of no item: it wants ScriptTies at the input behind
the step. NEITHER GIVES RidesPastAt, which is asked at every witness; that is ridesPastAt_constr,
which reads no trace and no condition on Q. Three of the 100 items are not treated: the head's idn,
lookCalls and rider (they are treated in Johnson/Goal/HonestTrace/ConstrHeadAtThread.lean).
ridesPastAt_constr is at all 100, and says of no item that it holds. That an input which the honest
side calls valid comes with an i and x that are served and meet ScriptTies is not shown here; nor
that the chain's start has the run's own input, nor what Thread.opened 0 holds. All is at the full
size.

Not claimed: that an honest prover's witness meets any relation; anything on what a verifier
accepts; any property of the protocol. No property of a release, of a verifier or of a prover is
claimed.
-/
import Johnson.Goal.HonestTrace.ConstrAtTrace
import Johnson.Goal.HonestTrace.SeatsApartAtHead
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.Shares
import Johnson.P5J.RowsAtMg
import Johnson.P5J.HidBearsAtMg
import Johnson.Top.H0.K2Ties.AtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model Inst.Model.All
open OnBytes.Road OnBytes.Road.L5 OnBytes.Road.Rows.Norms
open OnBytes.Model.Verify (publicOf layerShape borderOf)
open OnBytes.Model.Layer (Lay matIx)
open VerifiableInference.OnPublicFiles.Flat (Holds GE)
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.Sound (MsgT Mem readAt SeatsNamed GroupsSeated)
open VerifiableInference.Desc.First (Numbers)
open Meaning (Hid hidOf mgOf maOf ownOf symAt Msgs msgOf seat0 seatBy Follows labAt)
open P5J (TPart TReq TS HidAt partG partA parts4 constrQAt hidAtSeat ownQ)
open Cb.Pv.Tail (Size Base)

variable {Z : VerifierAndGoals.PublicFiles}

section AtThreads
open ProofFile.Honest ProofFile.Honest.FirstThread
open P5J (AtMgA CellsM)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (Item)
open OnBytes.Maker (WholeD)

variable {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl} {xp : VerifiableInference.Desc.First.Look.Place}


/-- **The condition on the Script's messages, at one run's coins k, its input v and a trace τ**: at
every list of challenges hd, the symbols at the layout's seats, read as hidAtSeat reads them in the
witness Q.wit k v hd, are the library's packing of τ (SymsOfTrace). T, the type of the input's own
field "trace", is a letter, and that field is not read. constr_at_thread takes this condition at τ
:= theTrace X i x. The empty list is among the hd: the items are open from the start, where nothing
has been heard. The condition is on symbols and not on matrices because Base (Cb/Pv/Tail/Base.lean)
is a sentence on symbols. A member of this clause is shown under h, at a Script made for it
(scriptSyms_member_at_head). Of ScriptTies whole no member is shown. -/
def ScriptSymsAt {Bk : ProverCoinCounts} {W₀ Rc T : Type} (Z : VerifierAndGoals.PublicFiles) (Zp : ProofFile.Pub)
    (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (k : Coins Bk) (v : Local W₀ Rc ProofFile.Inst T) (τ : Tr) : Prop :=
  ∀ hd : List Fmt.Drawn,
    SymsOfTrace (P5J.At.X Zp) (Meaning.sizesOf (P5J.At.X Zp))
      (seatBy (Meaning.fLay (P5J.At.layout Zp) (P5J.At.num Zp)) (P5J.At.X Zp)
        (Meaning.sizesOf (P5J.At.X Zp)))
      (fun m => readAt (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) m
        (Q.wit k v hd))
      τ

/-- The same at all coins and all inputs, at the trace rd v that a reader rd makes of the input: an
equation on Q and rd alone. rd is any function: it need not read the input's field "trace". It is
more than constr_at_thread takes; how it gives the clause syms of ScriptTies: scriptSymsAt_of_syms.
-/
def ScriptSyms {Bk : ProverCoinCounts} {W₀ Rc T : Type} (Z : VerifierAndGoals.PublicFiles) (Zp : ProofFile.Pub)
    (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (rd : Local W₀ Rc ProofFile.Inst T → Tr) : Prop :=
  ∀ (k : Coins Bk) (v : Local W₀ Rc ProofFile.Inst T), ScriptSymsAt Z Zp cF Q k v (rd v)

/-- From ScriptSyms at a reader rd to the condition at a trace τ: at an input v with rd v = τ. -/
theorem scriptSymsAt_of_syms {Bk : ProverCoinCounts} {W₀ Rc T : Type}
    {Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    {rd : Local W₀ Rc ProofFile.Inst T → Tr} (S : ScriptSyms Z Zp cF Q rd) (k : Coins Bk)
    {v : Local W₀ Rc ProofFile.Inst T} {τ : Tr} (e : rd v = τ) : ScriptSymsAt Z Zp cF Q k v τ :=
  e ▸ S k v

/-- The like equation on Q.msg itself, place by place: for each of the 25 sub-proofs, each entry a
of its list and each row of symbols i' and column c inside the sizes, the message whose number the
seat names holds, in the main row and at the place that the seat names, the entry (i', c) of msgOf
at rd v and the entry's label. It gives ScriptSyms under h (syms_of_raw); the converse is not shown.
It fixes the main rows at the layout's seats alone: every other place of a main row, every mask row
and every pad is left free; it says nothing of what is encoded, sent or opened. -/
def ScriptSymsRaw {Bk : ProverCoinCounts} {W₀ Rc T : Type} (Zp : ProofFile.Pub)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (rd : Local W₀ Rc ProofFile.Inst T → Tr) : Prop :=
  let X := P5J.At.X Zp
  let s := Meaning.sizesOf X
  let f := Meaning.fLay (P5J.At.layout Zp) (P5J.At.num Zp)
  ∀ (k : Coins Bk) (v : Local W₀ Rc ProofFile.Inst T) (hd : List Fmt.Drawn), ∀ m < 25, ∀ a < (s m).NM,
    ∀ i' < Alg.symRows ((s m).m a), ∀ c < (s m).k a,
      Q.msg (f (Meaning.labAt X m a) i' c).1 k v
          (hd.take (Q.fixedMsg (f (Meaning.labAt X m a) i' c).1)) false
          (f (Meaning.labAt X m a) i' c).2.1 (f (Meaning.labAt X m a) i' c).2.2 =
        msgOf s (rd v) (Meaning.labAt X m a) false i' c

/-- **Under h : AtMgA ..., ScriptSymsRaw gives ScriptSyms.** By symAt_readAt
(Johnson/P5J/HidBears.lean): where no seat inside the sizes lies at a place of a pad of its own
sub-proof's copy (PlacesOffPad), the symbols that readAt yields are those of the witness's own
messages. AtMg.placesOff (Johnson/P5J/HidBearsAtMg.lean) gives that condition at an accept of the
test h.toAtMg.offC, and the test accepts under h by offC_ofHead (Johnson/Top/H0/K2Ties/AtHead.lean).
-/
theorem syms_of_raw (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xp) {Bk : ProverCoinCounts} {W₀ Rc T : Type}
    {Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    {rd : Local W₀ Rc ProofFile.Inst T → Tr} (R : ScriptSymsRaw Zp Q rd) : ScriptSyms Z Zp cF Q rd := by
  intro k v hd m hm
  rw [P5J.symAt_readAt h.plan.hN h.plan.hG
    (h.toAtMg.placesOff (VerifiableInference.Desc.First.K2Ties.offC_ofHead h.toAtMg))]
  funext μ i' c
  exact R k v hd m hm μ.val μ.isLt i'.val i'.isLt c.val c.isLt

/-- **The equation of ScriptSymsRaw at one run's coins k, one input v and a trace τ, on the entries
that P picks**: at every list of challenges hd, for each sub-proof m < 25 and each entry a of its
list with P m a. P is any predicate on the pair of numbers: at "fun _ _ => True" all entries are
asked. It fixes the main rows at the layout's seats alone: every other place of a main row, every
mask row and every pad is left free; it says nothing of what is encoded, sent or opened. -/
def ScriptSymsRawOn {Bk : ProverCoinCounts} {W₀ Rc T : Type} (Zp : ProofFile.Pub)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (k : Coins Bk) (v : Local W₀ Rc ProofFile.Inst T) (τ : Tr) (P : ℕ → ℕ → Prop) : Prop :=
  let X := P5J.At.X Zp
  let s := Meaning.sizesOf X
  let f := Meaning.fLay (P5J.At.layout Zp) (P5J.At.num Zp)
  ∀ hd : List Fmt.Drawn, ∀ m < 25, ∀ a < (s m).NM, P m a →
    ∀ i' < Alg.symRows ((s m).m a), ∀ c < (s m).k a,
      Q.msg (f (Meaning.labAt X m a) i' c).1 k v
          (hd.take (Q.fixedMsg (f (Meaning.labAt X m a) i' c).1)) false
          (f (Meaning.labAt X m a) i' c).2.1 (f (Meaning.labAt X m a) i' c).2.2 =
        msgOf s τ (Meaning.labAt X m a) false i' c

/-- ScriptSymsRaw at a reader rd gives that equation at every k and v, at rd v, on all entries. -/
theorem rawOn_of_raw {Bk : ProverCoinCounts} {W₀ Rc T : Type}
    {Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    {rd : Local W₀ Rc ProofFile.Inst T → Tr} (R : ScriptSymsRaw Zp Q rd) (k : Coins Bk)
    (v : Local W₀ Rc ProofFile.Inst T) : ScriptSymsRawOn Zp Q k v (rd v) fun _ _ => True :=
  fun hd m hm a ha _ => R k v hd m hm a ha

/-- **Cut in two**: the equation on the entries that P₁ picks and on those that P₂ picks give it on
all entries, where each pair of numbers is picked by one of the two. Both predicates are the
caller's. -/
theorem rawOn_of_two {Bk : ProverCoinCounts} {W₀ Rc T : Type}
    {Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    {k : Coins Bk} {v : Local W₀ Rc ProofFile.Inst T} {τ : Tr} {P₁ P₂ : ℕ → ℕ → Prop}
    (hP : ∀ m a, P₁ m a ∨ P₂ m a) (R₁ : ScriptSymsRawOn Zp Q k v τ P₁)
    (R₂ : ScriptSymsRawOn Zp Q k v τ P₂) : ScriptSymsRawOn Zp Q k v τ fun _ _ => True := by
  intro hd m hm a ha _
  rcases hP m a with h₁ | h₂
  · exact R₁ hd m hm a ha h₁
  · exact R₂ hd m hm a ha h₂

/-- **Under h : AtMgA ..., the equation on all entries, at one k, one v and τ, gives ScriptSymsAt
there.** The steps of syms_of_raw, which are pointwise in k and v. SeatsFixed is not asked. -/
theorem scriptSymsAt_of_rawOn (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xp) {Bk : ProverCoinCounts}
    {W₀ Rc T : Type}
    {Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    {k : Coins Bk} {v : Local W₀ Rc ProofFile.Inst T} {τ : Tr}
    (R : ScriptSymsRawOn Zp Q k v τ fun _ _ => True) : ScriptSymsAt Z Zp cF Q k v τ := by
  intro hd m hm
  rw [P5J.symAt_readAt h.plan.hN h.plan.hG
    (h.toAtMg.placesOff (VerifiableInference.Desc.First.K2Ties.offC_ofHead h.toAtMg))]
  funext μ i' c
  exact R hd m hm μ.val μ.isLt trivial i'.val i'.isLt c.val c.isLt

/-- **Where the layout's seats are apart, ScriptSymsRaw has a member**, at every reader rd. The
premise is SeatsApart (Johnson/Goal/HonestTrace/SeatsApartOfLayout.lean): inside the sizes, two
seats that name one message, row and place are the seats of one label, one row of symbols and one
column. Elsewhere nothing is shown: where two seats inside the sizes name one place and rd v packs
two values there, the equation of ScriptSymsRaw fails at v, at every k and hd, whatever Q is: one
entry of Q.msg would have two values. ScriptSymsAt fails there too where both sub-proofs read Q.msg
at that place; at a place of a pad each reads its own pad. The reader and the owner of a borrowed
matrix do not clash: a seat is a function of the label. None of this is stated as a lemma. From any
given Script Q₀: in a main
row, at a place that some seat inside the sizes names, the member's message holds the packed value;
everywhere else, and in every mask row, Q₀'s (so the proof; the statement keeps the mask rows). Its
cells, token, pads, fixedMsg, table and fixed are Q₀'s: SO ITS TABLES ARE Q₀'s, WHATEVER ITS
MESSAGES ARE: that they are made of its messages is not shown. The member is made by choice and has
no code. -/
theorem scriptSymsRaw_member {Bk : ProverCoinCounts} {W₀ Rc T : Type}
    (A : SeatsApart (P5J.At.X Zp) (Meaning.sizesOf (P5J.At.X Zp))
      (Meaning.fLay (P5J.At.layout Zp) (P5J.At.num Zp)))
    (Q₀ : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (rd : Local W₀ Rc ProofFile.Inst T → Tr) :
    ∃ Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT,
      ScriptSymsRaw Zp Q rd ∧ Q.cells = Q₀.cells ∧ Q.tok = Q₀.tok ∧ Q.pad = Q₀.pad ∧
        Q.fixedMsg = Q₀.fixedMsg ∧ Q.table = Q₀.table ∧ Q.fixed = Q₀.fixed ∧
        ∀ n k v hd r p, Q.msg n k v hd true r p = Q₀.msg n k v hd true r p := by
  classical
  let X := P5J.At.X Zp
  let s := Meaning.sizesOf X
  let f := Meaning.fLay (P5J.At.layout Zp) (P5J.At.num Zp)
  let Pr : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ × ℕ → Prop := fun n r p q =>
    q.1 < 25 ∧ q.2.1 < (s q.1).NM ∧ q.2.2.1 < Alg.symRows ((s q.1).m q.2.1) ∧
      q.2.2.2 < (s q.1).k q.2.1 ∧ f (labAt X q.1 q.2.1) q.2.2.1 q.2.2.2 = (n, r, p)
  refine ⟨{ Q₀ with
    msg := fun n k v hd b r p =>
      if hq : b = false ∧ ∃ q, Pr n r p q then
        msgOf s (rd v) (labAt X hq.2.choose.1 hq.2.choose.2.1) false hq.2.choose.2.2.1
          hq.2.choose.2.2.2
      else Q₀.msg n k v hd b r p }, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · intro k v hd m hm a ha i' hi c hc
    have hq : false = false ∧ ∃ q, Pr (f (labAt X m a) i' c).1 (f (labAt X m a) i' c).2.1
        (f (labAt X m a) i' c).2.2 q :=
      ⟨rfl, (m, a, i', c), hm, ha, hi, hc, rfl⟩
    obtain ⟨g1, g2, g3, g4, g5⟩ := hq.2.choose_spec
    obtain ⟨e1, e2, e3⟩ := A _ g1 _ g2 _ g3 _ g4 m hm a ha i' hi c hc g5
    show (if hq : false = false ∧ ∃ q, Pr _ _ _ q then _ else _) = _
    rw [dif_pos hq, e1, e2, e3]
  · intro n k v hd r p
    dsimp only
    rw [dif_neg]
    rintro ⟨hb, -⟩
    exact Bool.noConfusion hb

/-- **What a member of ScriptSyms takes, in one statement**: under h : AtMgA ... and SeatsApart at
the layout's seats, some Script meets ScriptSyms at the reader rd, with the cells, token and pads of
any given Script Q₀. -/
theorem scriptSyms_member (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xp) {Bk : ProverCoinCounts}
    {W₀ Rc T : Type}
    (A : SeatsApart (P5J.At.X Zp) (Meaning.sizesOf (P5J.At.X Zp))
      (Meaning.fLay (P5J.At.layout Zp) (P5J.At.num Zp)))
    (Q₀ : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (rd : Local W₀ Rc ProofFile.Inst T → Tr) :
    ∃ Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT,
      ScriptSyms Z Zp cF Q rd ∧ Q.cells = Q₀.cells ∧ Q.tok = Q₀.tok ∧ Q.pad = Q₀.pad := by
  obtain ⟨Q, R, e1, e2, e3, -⟩ := scriptSymsRaw_member A Q₀ rd
  exact ⟨Q, syms_of_raw h R, e1, e2, e3⟩

/-- The same under h alone: the seats are apart under h by seatsApart_at_head
(Johnson/Goal/HonestTrace/SeatsApartAtHead.lean). -/
theorem scriptSyms_member_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xp) {Bk : ProverCoinCounts}
    {W₀ Rc T : Type}
    (Q₀ : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (rd : Local W₀ Rc ProofFile.Inst T → Tr) :
    ∃ Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT,
      ScriptSyms Z Zp cF Q rd ∧ Q.cells = Q₀.cells ∧ Q.tok = Q₀.tok ∧ Q.pad = Q₀.pad :=
  scriptSyms_member h (seatsApart_at_head h) Q₀ rd

/-- **What constr_at_thread takes of the Script**, at one run's coins k and input v, an index i and
a request x. Three clauses. The input's own field "trace" is tied to nothing. -/
structure ScriptTies {Bk : ProverCoinCounts} {W₀ Rc T : Type} (Z : VerifierAndGoals.PublicFiles) (Zp : ProofFile.Pub)
    (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (k : Coins Bk) (v : Local W₀ Rc ProofFile.Inst T) (i : Cm.Idx) (x : Instance ppref) : Prop where
  /-- the Script's cells hold the index -/
  cells : Holds (Q.cells v) i
  /-- the request file's bytes, read back, with the Script's token laid in if the outcome is well
  formed (else untouched), are the request -/
  req : (OnBytes.Flat.putReq ((Meaning.backReq v.x.pub.request).getD P5J.At.d₀)
    (P5J.tokVOf (Q.tok v))).val = x
  /-- the symbols at the layout's seats are the packing of theTrace at i and x -/
  syms : ScriptSymsAt Z Zp cF Q k v (theTrace (P5J.At.X Zp) i x)

/-- **ScriptTies from its first two clauses and the equation on Q.msg, cut in two by predicates of
the caller's**, under h : AtMgA .... -/
theorem scriptTies_of_rawOn (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xp) {Bk : ProverCoinCounts}
    {W₀ Rc T : Type}
    {Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    {k : Coins Bk} {v : Local W₀ Rc ProofFile.Inst T} {i : Cm.Idx} {x : Instance ppref}
    {P₁ P₂ : ℕ → ℕ → Prop} (hP : ∀ m a, P₁ m a ∨ P₂ m a) (hc : Holds (Q.cells v) i)
    (hr : (OnBytes.Flat.putReq ((Meaning.backReq v.x.pub.request).getD P5J.At.d₀)
      (P5J.tokVOf (Q.tok v))).val = x)
    (R₁ : ScriptSymsRawOn Zp Q k v (theTrace (P5J.At.X Zp) i x) P₁)
    (R₂ : ScriptSymsRawOn Zp Q k v (theTrace (P5J.At.X Zp) i x) P₂) :
    ScriptTies Z Zp cF Q k v i x :=
  ⟨hc, hr, scriptSymsAt_of_rawOn h (rawOn_of_two hP R₁ R₂)⟩

/-- **The messages that the layout's seats name turn with no challenge**: Q.fixedMsg n = 0 at the
number n of every message that a seat inside the sizes names. Script.wit
(Johnson/Desc/ProofFile/Honest/Thread/First.lean) lays message n as Q.msg n k v (hd.take (Q.fixedMsg
n)): where Q.fixedMsg n = 0 that is Q.msg n k v [] at every hd. It is a condition on Q: no theorem
of this file shows it of a Script. -/
def SeatsFixed {Bk : ProverCoinCounts} {W₀ Rc T : Type} (Zp : ProofFile.Pub)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT) :
    Prop :=
  let X := P5J.At.X Zp
  let s := Meaning.sizesOf X
  let f := Meaning.fLay (P5J.At.layout Zp) (P5J.At.num Zp)
  ∀ m < 25, ∀ a < (s m).NM, ∀ i' < Alg.symRows ((s m).m a), ∀ c < (s m).k a,
    Q.fixedMsg (f (Meaning.labAt X m a) i' c).1 = 0

/-- **From the empty list of challenges to every list.** Under h : AtMgA ... and SeatsFixed: if at
hd := [] the symbols at the layout's seats are the packing of τ (SymsOfTrace), then so at every hd:
ScriptSymsAt at k, v and τ. h is taken for one step, symAt_readAt: off the pads the symbols that
readAt yields are those of the witness's own messages. Whether h can be spared is not looked into
here. -/
theorem scriptSymsAt_of_nil (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xp) {Bk : ProverCoinCounts}
    {W₀ Rc T : Type}
    {Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    (F : SeatsFixed Zp Q) {k : Coins Bk} {v : Local W₀ Rc ProofFile.Inst T} {τ : Tr}
    (S0 : SymsOfTrace (P5J.At.X Zp) (Meaning.sizesOf (P5J.At.X Zp))
      (seatBy (Meaning.fLay (P5J.At.layout Zp) (P5J.At.num Zp)) (P5J.At.X Zp)
        (Meaning.sizesOf (P5J.At.X Zp)))
      (fun m => readAt (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) m
        (Q.wit k v []))
      τ) : ScriptSymsAt Z Zp cF Q k v τ := by
  intro hd m hm
  have O := h.toAtMg.placesOff (VerifiableInference.Desc.First.K2Ties.offC_ofHead h.toAtMg)
  rw [← S0 m hm, P5J.symAt_readAt h.plan.hN h.plan.hG O, P5J.symAt_readAt h.plan.hN h.plan.hG O]
  funext μ i' c
  show Q.msg _ k v (hd.take (Q.fixedMsg _)) false _ _ = Q.msg _ k v (([] : List Fmt.Drawn).take
    (Q.fixedMsg _)) false _ _
  have e : Q.fixedMsg (seatBy (Meaning.fLay (P5J.At.layout Zp) (P5J.At.num Zp)) (P5J.At.X Zp)
      (Meaning.sizesOf (P5J.At.X Zp)) m μ i'.val c.val).1 = 0 :=
    F m hm μ.val μ.isLt i'.val i'.isLt c.val c.isLt
  rw [e, List.take_zero, List.take_zero]

/-- **Four conditions that under h give ScriptTies** (scriptTies_of_nil): its first two; SeatsFixed;
and SymsOfTrace at the empty list of challenges alone. The converse is not shown. -/
structure ScriptTiesAtNil {Bk : ProverCoinCounts} {W₀ Rc T : Type} (Z : VerifierAndGoals.PublicFiles) (Zp : ProofFile.Pub)
    (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (k : Coins Bk) (v : Local W₀ Rc ProofFile.Inst T) (i : Cm.Idx) (x : Instance ppref) : Prop where
  /-- the Script's cells hold the index -/
  cells : Holds (Q.cells v) i
  /-- the request file's bytes, read back, with the Script's token laid in if the outcome is well
  formed (else untouched), are the request -/
  req : (OnBytes.Flat.putReq ((Meaning.backReq v.x.pub.request).getD P5J.At.d₀)
    (P5J.tokVOf (Q.tok v))).val = x
  /-- the messages that the layout's seats name turn with no challenge -/
  fixed : SeatsFixed Zp Q
  /-- at the empty list of challenges the symbols at the layout's seats are the packing of theTrace
  at i and x -/
  syms0 : SymsOfTrace (P5J.At.X Zp) (Meaning.sizesOf (P5J.At.X Zp))
      (seatBy (Meaning.fLay (P5J.At.layout Zp) (P5J.At.num Zp)) (P5J.At.X Zp)
        (Meaning.sizesOf (P5J.At.X Zp)))
      (fun m => readAt (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) m
        (Q.wit k v []))
      (theTrace (P5J.At.X Zp) i x)

/-- Under h : AtMgA ..., ScriptTiesAtNil gives ScriptTies at the same k, v, i and x. -/
theorem scriptTies_of_nil (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xp) {Bk : ProverCoinCounts}
    {W₀ Rc T : Type}
    {Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    {k : Coins Bk} {v : Local W₀ Rc ProofFile.Inst T} {i : Cm.Idx} {x : Instance ppref}
    (Ti : ScriptTiesAtNil Z Zp cF Q k v i x) : ScriptTies Z Zp cF Q k v i x :=
  ⟨Ti.cells, Ti.req, scriptSymsAt_of_nil h Ti.fixed Ti.syms0⟩

/-- **The sentence of 97 items at the Script's witness.** Under h : AtMgA ..., at a served request
and under ScriptTies: for p among idn, lookCalls, rider, small and m < 24, and for m = 24 and p =
small, "means v (Item.constr m p)" holds at the pair (v.x.pub, s), the strings y and the witness
Q.wit k v ds, for every state s, all y and every list ds. w₁, the last argument of lettersHead, is
arbitrary: it enters the field "valid" alone. The theorem speaks of the witness Q.wit k v ds alone:
it does not give RidesPastAt, which is asked at every witness. -/
theorem constr_at_thread (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xp) {Bk : ProverCoinCounts}
    {W₀ Rc Ky T X₀ X' : Type} (H : Prover W₀ Rc ProofFile.Inst Ky T X₀ X')
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : ℕ → TS → Option String) (carryX : ℕ → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : ℕ) (Vd : Local W₀ Rc ProofFile.Inst T → Prop)
    (Rd : ℕ → Local W₀ Rc ProofFile.Inst T → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w₁ : Local W₀ Rc ProofFile.Inst T) (k : Coins Bk) (v : Local W₀ Rc ProofFile.Inst T) {i : Cm.Idx}
    {x : Instance ppref} (Sv : ServesAt (P5J.At.X Zp) i x) (Ti : ScriptTies Z Zp cF Q k v i x)
    (s : TS) (y : Strs) (ds : List Fmt.Drawn) {m : ℕ} {p : TPart} (hp : p ∈ parts4)
    (hm : m < 24 ∨ (m = 24 ∧ p = .small)) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.means v (Item.constr m p)
      (v.x.pub, s) y (Q.wit k v ds) := by
  have hZ := h.scope
  have hR := h.reads
  have hP := h.pubOne
  have Fo : Follows (P5J.At.X Zp) (Meaning.sizesOf (P5J.At.X Zp)) :=
    Meaning.follows_of_core hP (Hd.core_of_scope hZ hR hP)
  have hb : ∀ k < 25, (Meaning.sizesOf (P5J.At.X Zp) k).beta = 2 ^ 17 := fun _ _ => rfl
  have hr : ∀ k < 25, (Meaning.sizesOf (P5J.At.X Zp) k).rad = 2 ^ 20 := fun _ _ => rfl
  have S := Ti.syms ds
  show constrQAt (VerifiableInference.OnPublicFiles.headLink (P5J.At.X Zp)) h.𝔇.put
    (VerifiableInference.Desc.Sound.oneDec (fun _ _ => some (Q.cells v)) h.𝔇.H) h.𝔇.headPart
    h.𝔇.digitsPart m p (v.x.pub, s) y (Q.wit k v ds)
  rw [P5J.headLink_in_scope hZ hR hP]
  rcases hm with hm | ⟨rfl, rfl⟩
  · exact constr_layers
      (tiesAt_hidAtSeat (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF)
        (Meaning.sizesOf (P5J.At.X Zp)) _ P5J.tokVOf
        (fun a => (Meaning.backReq (P5J.At.reqB a.1)).getD P5J.At.d₀)
        (fun _ _ => some (Q.cells v)) h.plan.hN h.plan.hG hZ hR hP Sv Fo hb hr OnBytes.Flat.putReq
        (v.x.pub, s) y (Q.wit k v ds) (fun M hM => (Option.some.inj hM) ▸ Ti.cells) Ti.req S)
      (meetsAll_theTrace hZ hR hP Sv) _ _ hm hp
  · exact constr_head_small (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF)
      (Meaning.sizesOf (P5J.At.X Zp)) _ P5J.tokVOf
      (fun a => (Meaning.backReq (P5J.At.reqB a.1)).getD P5J.At.d₀)
      (fun _ _ => some (Q.cells v)) h.plan.hN h.plan.hG hZ hR hP Sv Fo hb hr OnBytes.Flat.putReq
      (v.x.pub, s) y (Q.wit k v ds) S _ _ _ _ _

/-- **The same in the form in which the honest side asks it**: Thread.Items at the one item, at a
value mm of Mid whose input meets ScriptTies, at every state s and all oracles E: for every
continuation ds of the challenges heard, the item's sentence holds at Thread.seat, Thread.strs and
Thread.wit. It is the form in which ExchangeAt (Johnson/Desc/ProofFile/Honest/Thread/Shares.lean)
ends. -/
theorem items_constr_at_thread (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xp) {Bk : ProverCoinCounts}
    {W₀ Rc Ky T X₀ X' : Type} (H : Prover W₀ Rc ProofFile.Inst Ky T X₀ X')
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : ℕ → TS → Option String) (carryX : ℕ → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : ℕ) (Vd : Local W₀ Rc ProofFile.Inst T → Prop)
    (Rd : ℕ → Local W₀ Rc ProofFile.Inst T → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w₁ : Local W₀ Rc ProofFile.Inst T) (k : Coins Bk) (mm : Mid (Local W₀ Rc ProofFile.Inst T) X')
    {i : Cm.Idx} {x : Instance ppref} (Sv : ServesAt (P5J.At.X Zp) i x)
    (Ti : ScriptTies Z Zp cF Q k mm.st.input i x) (s : TS) (E : Env) {m : ℕ} {p : TPart}
    (hp : p ∈ parts4) (hm : m < 24 ∨ (m = 24 ∧ p = .small)) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Items [Item.constr m p] k s
      mm E := by
  intro ds j hj
  obtain rfl := List.mem_singleton.1 hj
  exact constr_at_thread h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ k mm.st.input Sv Ti s _
    (mm.st.heard ++ ds) hp hm

/-- **RidesPastAt at the items constr m p**: under h : AtMgA ..., at every border number b, every m
and each of the four parts of parts4: RidesPastAt at Item.constr m p. At such a part the sentence
reads of the pair its public half alone and of the strings nothing, since the decoder is a constant:
so the sentence in front and the sentence behind are one by unfolding. No trace and no condition on
Q is read. -/
theorem ridesPastAt_constr (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xp) {Bk : ProverCoinCounts}
    {W₀ Rc Ky T X₀ X' : Type} (H : Prover W₀ Rc ProofFile.Inst Ky T X₀ X')
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : ℕ → TS → Option String) (carryX : ℕ → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : ℕ) (Vd : Local W₀ Rc ProofFile.Inst T → Prop)
    (Rd : ℕ → Local W₀ Rc ProofFile.Inst T → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst T) (b m : ℕ) {p : TPart} (hp : p ∈ parts4) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b
      (Item.constr m p) := by
  intro k s mm E s' ps v _ _ h0
  simp only [parts4, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> exact h0

/-! ## At the type Tr: ScriptTies beside a clause on the input's own trace -/

/-- **At inputs whose field "trace" is of the type Tr**: four clauses, written out on the left:
ScriptTies' first two; that field is theTrace at i and x; and the condition on the symbols said of
that field. They hold exactly where ScriptTies holds and that field is theTrace at i and x. So each
lemma that takes ScriptTies holds under the four clauses too, by the first half of this and one
call: that is stated of none. ScriptTies names that field nowhere. Whether ScriptTies can hold where
the clause on that field fails is not shown: no member of it is shown. -/
theorem scriptTies_and_trace_iff {Bk : ProverCoinCounts} {W₀ Rc : Type}
    {Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    {k : Coins Bk} {v : Local W₀ Rc ProofFile.Inst Tr} {i : Cm.Idx} {x : Instance ppref} :
    (Holds (Q.cells v) i ∧
      (OnBytes.Flat.putReq ((Meaning.backReq v.x.pub.request).getD P5J.At.d₀)
        (P5J.tokVOf (Q.tok v))).val = x ∧
      v.trace = theTrace (P5J.At.X Zp) i x ∧ ScriptSymsAt Z Zp cF Q k v v.trace) ↔
      ScriptTies Z Zp cF Q k v i x ∧ v.trace = theTrace (P5J.At.X Zp) i x := by
  constructor
  · rintro ⟨hc, hr, e, S⟩
    rw [e] at S
    exact ⟨⟨hc, hr, S⟩, e⟩
  · rintro ⟨Ti, e⟩
    refine ⟨Ti.cells, Ti.req, e, ?_⟩
    rw [e]
    exact Ti.syms

end AtThreads

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.scriptSymsAt_of_syms
#print axioms OnBytes.HonestTrace.syms_of_raw
#print axioms OnBytes.HonestTrace.rawOn_of_raw
#print axioms OnBytes.HonestTrace.rawOn_of_two
#print axioms OnBytes.HonestTrace.scriptSymsAt_of_rawOn
#print axioms OnBytes.HonestTrace.scriptSymsRaw_member
#print axioms OnBytes.HonestTrace.scriptSyms_member
#print axioms OnBytes.HonestTrace.scriptSyms_member_at_head
#print axioms OnBytes.HonestTrace.scriptTies_of_rawOn
#print axioms OnBytes.HonestTrace.scriptSymsAt_of_nil
#print axioms OnBytes.HonestTrace.scriptTies_of_nil
#print axioms OnBytes.HonestTrace.constr_at_thread
#print axioms OnBytes.HonestTrace.items_constr_at_thread
#print axioms OnBytes.HonestTrace.ridesPastAt_constr
#print axioms OnBytes.HonestTrace.scriptTies_and_trace_iff
#print axioms OnBytes.HonestTrace.ScriptSymsAt
#print axioms OnBytes.HonestTrace.ScriptSyms
#print axioms OnBytes.HonestTrace.ScriptSymsRaw
#print axioms OnBytes.HonestTrace.ScriptSymsRawOn
#print axioms OnBytes.HonestTrace.ScriptTies
#print axioms OnBytes.HonestTrace.SeatsFixed
#print axioms OnBytes.HonestTrace.ScriptTiesAtNil
