-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/SeatedRiders.lean: kind K13, the members' batching: WHAT THE
KIND's STATEMENTS AT ITS MEMBER ASK OF THE FIRST CHAIN's THREAD WHERE `rides` IS THE REPLY's
SENTENCE BESIDE A LIST OF CLAUSES (`ridersOf`, Honest/Thread/Riders.lean; the form of
Honest/Thread/RidersAnd.lean), GATHERED IN ONE STRUCTURE (`K13Riders`), and what follows: `Plays`,
`Behind`, the share of `Exchange` at "pileOne", `RidesPast` (Honest/Thread/Pays.lean).
THIS IS THE STRUCTURE TO CALL. `K13Seated` (Seated.lean of this folder) is the other form: it has
the same fields but for the two on `rides`. The two can hold of one L together: at
R := `ridersOf cs`, where b₀ is at most b.

By `behind_of_keeps_and` (RidersAnd.lean) a member's `Behind` comes down to: the thread's form
behind; the member's clause of `keeps`; that the one sentence beside the list goes over the member's
step; the clauses that the member itself lays. That a clause of another member stays past this one
is drawn from `keeps` alone (`StaysBy`), and is a premise of `k13_riders`, not a field: by the head
of Honest/Thread/Riders.lean it is shown by whoever lays the thread.
The fields that differ from `K13Seated`'s:
  ridesAre: ON L.rides, pointwise, at every border: from the border b₀ on "the reply that the state
    holds is the one asked" (`ReplyIs`: it speaks of one value that is sent in the clear
    (`replyPart`, Honest/K7.lean: no coin; of its input it reads the instance alone)), beside
    `ridersOf cs`, cs a variable.
  replyLo: b₀ is at most b.
  noneLaid: ON cs: no clause begins at the border b + 1: the kind's member lays none.
Main names:
  `K13Riders`: **the structure.**
  `K13Riders.reply`: the thread gives `ReplyIs` at b.
  `K13Riders.formKeeps`: behind the member's accepted step: the thread's form, and `keeps`.
  `K13Riders.replyOver`: behind it the reply's sentence holds at the next border.
  `k13_riders`: **the four statements.**

On imports. RidersAnd.lean imports the frame's file on the thread at the library's hypothesis
(Honest/Thread/FirstHead.lean), and ExchangeAtM3.lean of this folder imports FromThreadAt.lean: so
this file, general as its statements are, stands over that hypothesis's imports.

What is not claimed. That `K13Riders` holds at any L. `StaysBy` for any clause. `Accepted`. No
instance is typed. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K13.Seated
import Johnson.Desc.ProofFile.Honest.Thread.RidersAnd
import Johnson.Desc.K13.Honest.KeepsAllM3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open OnBytes.Slice (GE)
open VerifiableInference.Desc.First (S Item pubSets)
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (Wit RowM3)
open VerifiableInference.Desc.K13.Honest (PubM3 K13KeepsAll withClaim_keepsAll)
open ProofFile.Honest.FirstThread (Letters)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X Pp Cells Tok M : Type}

/-- **What the kind's statements at its member ask of the thread, where `rides` is a list of
clauses.** cs: the clauses. b₀: from which border on the reply's sentence speaks. -/
structure K13Riders (L : Letters Bk Cl W₀ Rc Xi Tr X Pp Cells Tok M) (b : Nat)
    (weights : W₀ → Weights) (pile : PileOf Xi) (P : Where) (Cl' : Type)
    (rd : Pp × S → VerifiableInference.Desc.Wit Cells Tok M → Wit GE P.lin.matrixRows P.lin.kCol)
    (asked : Xi → E) (cs : List (RiderCl (Local W₀ Rc Xi Tr) S)) (b₀ : Nat) : Prop where
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
  ridesAre : ∀ c w s, L.rides c w s ↔ (b₀ ≤ c → ReplyIs asked w.x s) ∧ ridersOf cs c w s
  replyLo : b₀ ≤ b
  noneLaid : ∀ c ∈ cs, c.lo ≠ b + 1

variable {L : Letters Bk Cl W₀ Rc Xi Tr X Pp Cells Tok M} {b : Nat} {weights : W₀ → Weights}
  {pile : PileOf Xi} {P : Where} {Cl' : Type}
  {rd : Pp × S → VerifiableInference.Desc.Wit Cells Tok M → Wit GE P.lin.matrixRows P.lin.kCol}
  {asked : Xi → E} {cs : List (RiderCl (Local W₀ Rc Xi Tr) S)} {b₀ : Nat}

/-- At the border in front the thread gives: the reply that the state holds is the one asked. -/
theorem K13Riders.reply (h : K13Riders L b weights pile P Cl' rd asked cs b₀) :
    ReplyRides L b asked :=
  replyRides_of_rides L fun w s q => ((h.ridesAre b w s).1 q).1 h.replyLo

/-- Behind the member's accepted step: the thread's form at the next border, and `keeps`. -/
theorem K13Riders.formKeeps (h : K13Riders L b weights pile P Cl' rd asked cs b₀) :
    ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m En ds y cols s',
      Thr L.thread b k s m En → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m En ds y cols s' →
      L.thread.Form (b + 1) k s' y.2 ∧ L.thread.keeps b s s' := by
  intro blk hb k s m En ds y cols s' hT _ hS
  refine ⟨k13_thread_form_behind (Cl' := Cl') L h.table h.pub h.noPub (h.isAtM3.back blk hb s)
    hT.2.2.1 hS, ?_⟩
  obtain ⟨-, t, msg, row, ht, -, rfl, -⟩ := k13_from_step h.isAtM3 hb hS
  exact (h.keepsIs _ _).2 (withClaim_keepsAll (k13_form_front L h.place hT.2.2.1).1 ht msg row)

/-- Behind the member's accepted step the reply's sentence holds at the next border. -/
theorem K13Riders.replyOver (h : K13Riders L b weights pile P Cl' rd asked cs b₀) :
    ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m En ds y cols s',
      Thr L.thread b k s m En → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m En ds y cols s' →
      b₀ ≤ b + 1 → ReplyIs asked m.st.input.x s' := by
  intro blk hb k s m En ds y cols s' hT _ hS _
  obtain ⟨-, t, msg, row, -, -, rfl, -⟩ := k13_from_step h.isAtM3 hb hS
  exact replyIs_withClaim _ msg row (h.reply k s m En hT)

/-- **From the structure, and that the other members' clauses stay past this one: it plays;
`Behind`; the item "pileOne" holds behind; what goes past the member says behind what it says in
front.** -/
theorem k13_riders (h : K13Riders L b weights pile P Cl' rd asked cs b₀)
    (hst : ∀ c ∈ cs, c.lo ≤ b → b + 1 ≤ c.hi → StaysBy L.thread b c) :
    Plays L.thread b ∧ Behind L.thread b ∧ ExchangeOf L.thread b [Item.pileOne] ∧
      RidesPast L.thread b :=
  ⟨k13_thread_plays h.member,
    behind_of_keeps_and L.thread h.ridesAre h.formKeeps h.replyOver hst
      fun c hc e => absurd e (h.noneLaid c hc),
    k13_pileOne h.place h.opened h.member h.isAtM3 h.reads h.mat h.coins h.rows h.reply,
    k13_thread_rides L h.passes fun _ s _ _ s' _ hk => ((h.keepsIs s s').1 hk).1.1⟩

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.K13Riders.reply
#print axioms ProofFile.Honest.K13.K13Riders.formKeeps
#print axioms ProofFile.Honest.K13.K13Riders.replyOver
#print axioms ProofFile.Honest.K13.k13_riders
