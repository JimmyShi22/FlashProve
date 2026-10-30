-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/Seated.lean: kind K13, the members' batching: ALL THAT THE KIND's
STATEMENTS AT ITS MEMBER ASK OF THE FIRST CHAIN's THREAD, GATHERED IN ONE STRUCTURE (`K13Seated`),
and what follows from it: `Plays`, `Behind`, the share of `Exchange` at the item "pileOne", and
`RidesPast` (Honest/Thread/Pays.lean); and `Accepted`, from one premise more. The words thread and
border are explained in the head of Honest/Thread/Thr.lean; member and fall in that of
Honest/Thread/Pays.lean.
THIS IS ONE OF TWO FORMS: where `rides` is laid as a list of clauses, call `K13Riders`
(SeatedRiders.lean of this folder); the two differ in the fields on `rides` alone.

In which parameters it is general. The thread is `L.thread`, with L : `FirstThread.Letters`
(Honest/Thread/First.lean) A VARIABLE: every field of L is free; of L.valid nothing is taken but the
antecedent of `MatTie`. A CHOICE: the statements name items (`Item.pile`, `Item.pileOne`,
`Item.unmarked`), and the type of a thread's items is itself a field of a thread T. Every fact on
L's fields that a proof uses is a field of `K13Seated`.

The fields, and what each needs.
  place, opened, passes: on the written lists (L.ps, L.links): the kind's place has the number b;
    "pile" is open in front of it; "unmarked" alone goes past it. Evaluations at written lists.
  member, isAtM3: on L.bs and L.hs: the member's form; the kind's half at its place; the member
    returns just where the kind's own sub-protocol `atM3 P` does.
  table, pub, noPub: on L.N and L.MgP: what the library's promise `onAt` reads at the two borders.
  reads: on L.Mg: the two items say that the rows on the table are true at a reader rd.
  mat: on L.Q.cells and rd: the reader's matrix is the one that the half's reader of the index
    gives.
  coins: on L.Q.msg, rd and the book of coins: the reader's mask entries under the slots that the
    verifier takes are the coins that the book lends the sumcheck's part.
  rows: on the pile's filler: where the reply that the state holds is the one asked, it agrees with
    the state's pile in the rows' weights and column points.
  keepsIs: ON L.keeps b, pointwise (an "if and only if" at every pair of states): it is `K13KeepsAll
    P` (Johnson/Desc/K13/Honest/KeepsAllM3.lean): what the kind's step leaves of the state as it
    was, no mark of failure behind, and by how much the step moves the ledgers.
  ridesIs: ON L.rides AT b AND b + 1, pointwise: the reply that the state holds is the one asked
    (`ReplyIs`: IT SPEAKS OF ONE VALUE THAT IS SENT IN THE CLEAR), beside other clauses R, a
    variable.
  others: on R: it goes over the kind's step: asked at what the verifier's taking of the mask
    entries returns and at the announcement that the plan gives, and nowhere else. WHAT THAT STEP
    WRITES (`withClaim`, Johnson/Desc/K13/Honest/SubProtocols.lean): three fields of the state: `st`
    (the ledger of the index masks' message alone: `K13KeepsAll` says what stays and how that ledger
    moves), `rowsOwed` (laid to none) and `here` (the chain stands at its end, with the announcement
    of W's message, no number handed on, and the claim). A clause that reads none of these three
    meets it; so does one that reads of `st` what the taking leaves. The reply's clause is shown
    here to go over.
WHICH STATEMENT USES WHICH FIELDS (by the proofs). `Plays`: member alone. `Behind`: place, isAtM3
(that the member returns only where `atM3 P` does), table, pub, noPub, keepsIs, ridesIs, others:
none of the three ties. The share at "pileOne": place, opened, member, isAtM3, reads, mat, coins,
rows, ridesIs (at b). `RidesPast`: passes, keepsIs. `Accepted`: place, member, isAtM3 (that the
member returns wherever `atM3 P` does), and the premise on the guards.
Main names:
  `K13Seated`: **the structure.**
  `K13Seated.reply`, `.rides`, `.keeps`: from `ridesIs`, `others` and `keepsIs`: the thread gives
    `ReplyIs` at b; behind the member's accepted step L.rides holds at b + 1 and L.keeps at b.
  `k13_seated`: **the four statements from the structure.**
  `k13_seated_accepted`: `Accepted` at every `fall`, from it and: the thread's sentence in front
    gives the nine guards (`K13Guards`, Debts.lean of this folder).

What is not claimed. That `K13Seated` holds at any L. THE HEAVY HALF OF `Accepted` IS A PREMISE. Of
`Exchange` the items "pinW" and "pinI" are not treated here. No instance of the structure is typed.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K13.ExchangeAtM3
import Johnson.Desc.ProofFile.Honest.K13.BehindAtM3
import Johnson.Desc.ProofFile.Honest.K13.ReplyAtM3
import Johnson.Desc.ProofFile.Honest.K13.RidesAtM3
import Johnson.Desc.K13.Honest.KeepsAllM3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open OnBytes.Slice (GE)
open VerifiableInference.Desc.First (S Item pubSets)
open VerifiableInference.Desc.Ground (takeMasksP)
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (Wit RowM3 dOf)
open VerifiableInference.Desc.K13.Honest (PubM3 withClaim K13KeepsAll withClaim_keepsAll)
open ProofFile.Honest.FirstThread (Letters)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X Pp Cells Tok M : Type}

/-- **All that the kind's statements at its member ask of the first chain's thread.** Cl': the type
of claims at which `atM3 P` is taken. rd: the reader of a matrix with mask entries off the thread's
witness. asked: the instance's asked token. R: the other clauses of L.rides. -/
structure K13Seated (L : Letters Bk Cl W₀ Rc Xi Tr X Pp Cells Tok M) (b : Nat)
    (weights : W₀ → Weights) (pile : PileOf Xi) (P : Where) (Cl' : Type)
    (rd : Pp × S → VerifiableInference.Desc.Wit Cells Tok M → Wit GE P.lin.matrixRows P.lin.kCol)
    (asked : Xi → E) (R : Nat → Local W₀ Rc Xi Tr → S → Prop) : Prop where
  place : L.ps[b]? = some ⟨1, none, 3, .K13⟩
  opened : Item.pile ∈ L.thread.opened b
  passes : passBy (L.thread.opened b) (L.thread.row b) = [Item.unmarked]
  member : AtK13 L.thread b weights pile P
  isAtM3 : MemberIs L.thread.bs b P Cl'
  table : RowM3 L.N L.MgP.more L.links L.ps b
  pub : PubM3 P L.N L.MgP
  noPub : ((pubSets L.MgP.more L.links L.ps)[b]?).getD [] = []
  reads : K13Reads L P rd
  mat : MatTie L weights pile P rd
  coins : CoinsTie L b weights pile P rd
  rows : RowsTie L b pile asked
  keepsIs : ∀ s s', L.keeps b s s' ↔ K13KeepsAll P s s'
  ridesIs : ∀ c, c = b ∨ c = b + 1 → ∀ w s, L.rides c w s ↔ ReplyIs asked w.x s ∧ R c w s
  others : ∀ w s t msg row,
    takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol) = some t →
    linMessageW P.lin = some msg → R b w s → R (b + 1) w (withClaim s t.2.st msg row)

variable {L : Letters Bk Cl W₀ Rc Xi Tr X Pp Cells Tok M} {b : Nat} {weights : W₀ → Weights}
  {pile : PileOf Xi} {P : Where} {Cl' : Type}
  {rd : Pp × S → VerifiableInference.Desc.Wit Cells Tok M → Wit GE P.lin.matrixRows P.lin.kCol}
  {asked : Xi → E} {R : Nat → Local W₀ Rc Xi Tr → S → Prop}

/-- At the border in front the thread gives: the reply that the state holds is the one asked. -/
theorem K13Seated.reply (h : K13Seated L b weights pile P Cl' rd asked R) : ReplyRides L b asked :=
  replyRides_of_rides L fun w s q => ((h.ridesIs b (Or.inl rfl) w s).1 q).1

/-- Behind the member's accepted step L.rides holds at the next border: the clause of `Behind`. -/
theorem K13Seated.rides (h : K13Seated L b weights pile P Cl' rd asked R) :
    ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m En ds y cols s',
      Thr L.thread b k s m En → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m En ds y cols s' → L.rides (b + 1) y.2.st.input s' := by
  intro blk hb k s m En ds y cols s' hT _ hS
  obtain ⟨-, t, msg, row, ht, hm, rfl, e2⟩ := k13_from_step h.isAtM3 hb hS
  obtain ⟨q1, q2⟩ := (h.ridesIs b (Or.inl rfl) _ _).1 hT.2.2.2.2.2.1
  rw [e2]
  exact (h.ridesIs (b + 1) (Or.inr rfl) _ _).2
    ⟨replyIs_withClaim _ msg row q1, h.others _ _ t msg row ht hm q2⟩

/-- Behind the member's accepted step L.keeps holds: the clause of `Behind`. -/
theorem K13Seated.keeps (h : K13Seated L b weights pile P Cl' rd asked R) :
    ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m En ds y cols s',
      Thr L.thread b k s m En → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m En ds y cols s' → L.keeps b s s' := by
  intro blk hb k s m En ds y cols s' hT _ hS
  obtain ⟨-, t, msg, row, ht, -, rfl, -⟩ := k13_from_step h.isAtM3 hb hS
  exact (h.keepsIs _ _).2 (withClaim_keepsAll (k13_form_front L h.place hT.2.2.1).1 ht msg row)

/-- **From the structure: it plays; behind the member's accepted step the thread's form, `rides` and
`keeps` hold; the item "pileOne" holds behind; what goes past the member says behind what it says
in front.** -/
theorem k13_seated (h : K13Seated L b weights pile P Cl' rd asked R) :
    Plays L.thread b ∧ Behind L.thread b ∧ ExchangeOf L.thread b [Item.pileOne] ∧
      RidesPast L.thread b :=
  ⟨k13_thread_plays h.member,
    k13_thread_behind (Cl' := Cl') L h.table h.pub h.noPub h.isAtM3.back h.rides h.keeps,
    k13_pileOne h.place h.opened h.member h.isAtM3 h.reads h.mat h.coins h.rows h.reply,
    k13_thread_rides L h.passes fun _ s _ _ s' _ hk => ((h.keepsIs s s').1 hk).1.1⟩

/-- **It is accepted**, at every `fall`: from the structure, and: the thread's sentence in front
gives the nine guards. -/
theorem k13_seated_accepted (h : K13Seated L b weights pile P Cl' rd asked R)
    (hG : ∀ k s m En, Thr L.thread b k s m En → K13Guards P s)
    (fall : Nat → S → List Fmt.Drawn → Option String) : Accepted L.thread fall b :=
  k13_thread_accepted (Cl' := Cl') h.member
    (fun blk hb _ s _ _ hT rs gs t' q =>
      h.isAtM3.forth blk hb s rs gs t' (k13_form_front L h.place hT.2.2.1).1 q) hG fall

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.K13Seated.reply
#print axioms ProofFile.Honest.K13.K13Seated.rides
#print axioms ProofFile.Honest.K13.K13Seated.keeps
#print axioms ProofFile.Honest.K13.k13_seated
#print axioms ProofFile.Honest.K13.k13_seated_accepted
