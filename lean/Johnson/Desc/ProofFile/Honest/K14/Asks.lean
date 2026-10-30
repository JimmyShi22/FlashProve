-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/Asks.lean: kind K14 (the linear claim's shared rounds; the members
1 to 8 of the shared chain): ALL THAT THE KIND's STATEMENTS AT ITS MEMBERS ASK OF THE SHARED CHAIN's
THREAD, GATHERED IN ONE STRUCTURE (K14Asks), and what follows from it at each of the eight members:
Plays, Exchange, RidesPast and Accepted (Honest/Thread/Pays.lean), and of Behind the form behind and
keeps (FormKeeps, Honest/K14/Debts2.lean). OF THE LETTER L.rides NOTHING IS ASKED: the eight lay no
clause of it; a whole Behind follows under three premises on that letter: it is a list of clauses;
each clause that speaks on both sides of the member stays by keeps; no clause begins at the border
behind the member (k14_behind).

In which parameters it is general. The thread is L.thread, with L : SharedThread.Letters
(Honest/Thread/Shared.lean) A VARIABLE: every field of L is free, and every fact on a field that a
proof spends is a field of K14Asks. Accepted is stated AT EVERY FALL: the kind has none. (Plays,
FitsAt and Accepted, which name no item, are also stated at a bare thread T: eight_Play, eight_Fits,
Honest/K14/PaidAll.lean; accepted_at, Honest/K14/AcceptedAt.lean.)

THE FIELDS, and on which letter each is.
  letters   NINE EQUATIONS, one a letter (Asked, Honest/K14/LettersVar.lean): split · Mg · shape ·
            order · bs · wit · first · item · keeps. Four of them (Mg, shape, wit, keeps) fix the
            letter at this kind's items, borders, messages and members, and leave it free elsewhere
  plan      public: PlanFacts, and the plan's own test at both sendings (Plan2,
            Honest/K14/Debts2.lean). It holds at the two typed shapes, at some sentU and layO, where
            the plan's list beforePoint is not empty (plan2_key, plan2_real,
            Honest/K14/Thread2Member.lean)
  shapes    public: three facts on the shapes of the two sendings' messages (SendShapes,
            Honest/K14/SendingsShows.lean: a structure of sentences, no test). It follows where a
            test with code accepts (carriersFit, Honest/K14/SendingsShapes.lean), and it holds at
            the two typed shapes (sendShapes_of, sendShapes_key, sendShapes_real,
            Honest/K14/SendingsShowsAt.lean)
  point, zeta   public: the numbers of the two challenges that the kind's parts read, among the
            chain's rounds from 0
  halves    on L.hs: the halves stand at different places; the kind's four are among them; and, on A
            and not on L.hs: A has Q's shape (HalvesIn, Honest/K14/AcceptedAll.lean: three fields)
  sends     on L.hs: the two sendings' two are among them (SendsIn, there)
  tenant    on L.N: no two of the three sampled messages share a place and a tree
  treesU, treesO   on L.table and L.fixed, at the three trees of the two sendings (TreesLaid,
            Honest/K14/SendingsPaid.lean). Plays alone spends them
  cols, tab   on L.stored, at valid inputs: the committed table has its columns, of the declared
            width; each holds the rows' own symbols. tab reads with defaults: a column that L.stored
            does not return counts as the empty list, an entry beyond a column's end as 0. cols
            names its item and its range by readsAtLoc, tab by Q.item and the code's logN: no field
            says that the two agree
  key, seeds, ans   on a valid input's key: its sizes fit; no seed of it has the factor 0
            (Honest/K14/KeySeeds.lean); each of its OOD answers is its row's own
  book      on the book of coins: every entry by which the part at "SPLIT" spends coins (its spender
            is that part, its once is true) names as owner the sender of the split's mask message,
            and starts where that message's coins begin. That there is such an entry is not asked:
            at a book with none the field says nothing

OF L.valid NOTHING IS TAKEN BUT FIVE IMPLICATIONS FROM IT (cols, tab, key, seeds, ans). EACH IS A
DEBT: it is to be shown of the committer's make, at every coin and seed; IT IS NOT MET BY LAYING THE
FACT INTO valid (the rule of use in Honest/Thread/Thr.lean's head, at the letter valid).

WHOSE EACH FIELD IS TO SHOW.
  letters   whoever lays the thread: nine equations on its letters. At the letters at the IOP as
            written in Lean they hold where this kind's makers are laid
            (Honest/K14/AskedAtShared.lean)
  plan, shapes, book   no lemma on a prover: sentences on public data, to be shown at the plan and
            at the book of coins. Two of plan's three fields are tests with code; the third,
            PlanFacts, is a structure of sentences. plan at the shared chain's own parameters, under
            the library's head: Honest/K14/PlanAtHead.lean. shapes follows from the test carriersFit
            (above). book follows from the test bookSplitFits (book_of_fits,
            Honest/K14/Thread2Full.lean)
  point, zeta, and of halves the field that A has Q's shape   the caller's choice of A
  halves (its two other fields), sends, tenant, treesU, treesO   whoever lays the thread: on its
            halves, its numbers and its trees' tables. halves and sends are shown at the shared
            chain's own parameters and the filling's own readers, for letters whose halves are the
            list that the frame's filling lays for the shared chain (a premise there), under
            premises on the public part (halves_now, halves_shared, Honest/K14/AtFilling.lean)
  cols, tab, ans   lemmas on the committer's make: the committed table, and the answers in the key
            that it makes: with key and seeds, below
  key, seeds   lemmas on the key's maker: at every key that the library's own maker of keys returns,
            and for seeds at the format's own seeds at any plain hash: the library has them in its
            own forms: tableKey_fits (OnBytes/Params/EntryRoundsRecord.lean), tableKey_nz
            (OnBytes/Slice/KeyTableRec.lean), seedOK_recordSeedsW (OnBytes/Slice/SeedWords.lean).
            ALL FIVE (cols, tab, key, seeds, ans), as the structure FiveFields
            (Honest/K14/FiveFields.lean), stand at every input whose key the committer makes of its
            index and coins (validAt), at every public part that the maker (pubPlain) returns of
            public files in the goals' scope: fiveFieldsK14_inScope
            (Johnson/Bind/ForProver/FiveFieldsAt.lean); at the prover that onlineProverFromPublicFiles returns, under the
            library's hypothesis AtMgA and the caller's hv: five_of_validAt; validAt_made (hA alone)
            (AtFullSide/K14/FiveValid.lean): NOT IN FRONT OF A LAW OVER COINS (the rule:
            Johnson/Bind/ForProver/FiveFieldsAt.lean's head). That FiveFields' rows are those that
            K14Asks names: rw_holds2 (Honest/K14/FiveFieldsAsks.lean). That a run's explicit input
            is the committer's made input is not claimed there. key's own sentence at the offline
            plan's index shape: keyFits_of_relation (E2E/OfflineOwnKeyFits.lean)

  K14Asks         **the structure**
  k14_asks        **the five sentences at each member b, 1 ≤ b ≤ 8**
  k14_behind, k14_behind_and   a whole Behind at each of them, under premises on the letter rides:
                  calls of behind_of_formKeeps (Honest/K14/Debts2.lean: itself a call of
                  behind_of_keeps, Honest/Thread/Riders.lean) and of behind_of_keeps_and
                  (Honest/Thread/RidersAnd.lean)

What is not claimed. That K14Asks holds at any L: no term of it is typed. That the thread's sentence
in front holds at any stand. With what the prover holds laid as holds2, tab and ans are sentences on
rowsOf (Honest/K14/Parts.lean), its places between the matrix's entries and the pads included.
Nothing on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.LettersVar
import Johnson.Desc.ProofFile.Honest.K14.Plays2
import Johnson.Desc.ProofFile.Honest.K14.Rides2
import Johnson.Desc.ProofFile.Honest.K14.ColsPaid
import Johnson.Desc.ProofFile.Honest.K14.SendingsShows
import Johnson.Desc.ProofFile.Honest.Thread.RidersAnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes OnBytes.Params
open OnBytes.Means (Words)
open OnBytes.Slice (rdE)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Own (keyFits)
open Desc.K14 (P14 St)
open Desc.K14.Honest
open Desc.K14.Law (genK)

variable {Bk : ProverCoinCounts} {W₀ Rc X₀ P₁ Cl Wt : Type}

/-- **All that the kind's statements at its eight members ask of the shared chain's thread.** ℓ: how
this kind's sentences read a witness. c, tests, last: the planner's chains, the two proximity tests
and the chain's closing, of which L.bs is made. A: the public data of the kind's four halves.
weights, rand: the readers of the input. -/
structure K14Asks (ℓ : WitLens Wt) (L : SharedThread.Letters Bk St Cl W₀ Rc TableKey X₀ P₁ Wt)
    (Q : P14) (sentU : Array OracleNotice) (layO : TreeLay) (c : Model.Verify.Chains)
    (tests : List (Block St Unit)) (last : List (Block St Unit) → Block St Unit) (A : Data)
    (weights : W₀ → Weights) (rand : Rc → TableRand) : Prop where
  letters : Asked ℓ L Q sentU c tests last (holds2 Q weights rand)
  plan : Plan2 Q sentU layO
  shapes : SendShapes Q
  point : A.atPoint = 0
  zeta : A.atZeta = 6
  halves : HalvesIn Q (othersOf ℓ L c tests last (holds2 Q weights rand)) A weights
  sends : SendsIn Q (othersOf ℓ L c tests last (holds2 Q weights rand)) A weights rand
  tenant : Function.Injective L.N.tenant
  treesU : TreesLaid L.thread 2 (jobU ⟨Q, 0⟩) (witOf Q weights rand)
  treesO : TreesLaid L.thread 5 (jobOmega ⟨Q, 0⟩) (witOf Q weights rand)
  cols : ∀ w, L.valid w → ∀ p < 2 ^ (Desc.K14.readsAtLoc Q.S.fold Q.item).sh.a,
    ∃ u, L.stored w (Desc.K14.readsAtLoc Q.S.fold Q.item).item p = some u ∧
      u.length = (Desc.K14.readsAtLoc Q.S.fold Q.item).sh.W
  tab : ∀ (k : Coins Bk) w, L.valid w → ∀ x < 2 ^ Q.par.S.fold.index.code.logN,
    ∀ r < Q.par.S.fold.index.rows,
      rdE.val (ofF (((L.stored w Q.item x).getD []).toArray.getD r 0)) =
        genK rdE Q.par.S.fold x ((holds2 Q weights rand k w).Rw r)
  key : ∀ w, L.valid w → keyFits w.key Q.par.S.fold.index = true
  seeds : ∀ w, L.valid w → noZeroFactor w.key = true
  ans : ∀ (k : Coins Bk) w, L.valid w → OwnAnswers Q w.key (holds2 Q weights rand k w)
  book : ∀ e ∈ Bk.ahead, e.spender = ⟨place 8, 0⟩ → e.once = true →
    e.owner = ⟨sendPlace 5, 0⟩ ∧ e.start = ⟨0, offsetOf (jobOmega ⟨Q, 0⟩).Q.codes
      (jobOmega ⟨Q, 0⟩).Q.sent (jobOmega ⟨Q, 0⟩).sort 1⟩

variable {ℓ : WitLens Wt} {L : SharedThread.Letters Bk St Cl W₀ Rc TableKey X₀ P₁ Wt} {Q : P14}
  {sentU : Array OracleNotice} {layO : TreeLay} {c : Model.Verify.Chains}
  {tests : List (Block St Unit)} {last : List (Block St Unit) → Block St Unit} {A : Data}
  {weights : W₀ → Weights} {rand : Rc → TableRand}

/-- **From the structure, at each member b of the eight: it plays; behind its accepted step the
thread's form and keeps hold (of L.rides nothing is asked and nothing said); every item that is owed
there holds behind; what goes past says behind what it says in front; and its step returns, at every
fall.** -/
theorem k14_asks (h : K14Asks ℓ L Q sentU layO c tests last A weights rand)
    (fall : Nat → St → List Fmt.Drawn → Option String) (b : Nat) (h1 : 1 ≤ b) (h8 : b ≤ 8) :
    Plays L.thread b ∧ FormKeeps L.thread b ∧ Exchange L.thread b ∧ RidesPast L.thread b ∧
      Accepted L.thread fall b := by
  obtain ⟨hL, hQ, hSh, h0, h6, H, Hs, hN, tU, tO, hcol, hTab, hkey, hseeds, hAns, he⟩ := h
  obtain ⟨S, p, z⟩ := A
  obtain rfl : p = 0 := h0
  obtain rfl : z = 6 := h6
  have e := letters_eq hL
  generalize hOO : othersOf ℓ L c tests last (holds2 Q weights rand) = O at e H Hs
  have oN : O.N = L.N := by rw [← hOO]; rfl
  have oV : O.valid = L.valid := by rw [← hOO]; rfl
  have oS : O.stored = L.stored := by rw [← hOO]; rfl
  have oH : O.holds = holds2 Q weights rand := by rw [← hOO]; rfl
  rw [← oN] at hN
  rw [← oV] at hcol hTab hkey hseeds hAns
  rw [← oS] at hcol hTab
  rw [← oH] at hTab hAns
  subst e
  obtain ⟨B⟩ := hQ.eight
  have E8 := atEight2 B sentU Cl H
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := plays2 hQ Cl H Hs tU tO hcol
  have hhU : HalfIn O (sendPlace 2) (jobU ⟨Q, 0⟩) (witOf Q weights rand) :=
    find_of_mem _ { place := sendPlace 2, parts := _ } H.apart
      (Hs _ (by rw [sendHalves_eq]; exact List.mem_cons_self ..))
  have hhO : HalfIn O (sendPlace 5) (jobOmega ⟨Q, 0⟩) (witOf Q weights rand) :=
    find_of_mem _ { place := sendPlace 5, parts := _ } H.apart
      (Hs _ (by rw [sendHalves_eq]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have acc := accepted_all hQ Cl H Hs fall b h1 h8 (fun _ => hkey) fun _ => hseeds
  match b, h1, h8, acc with
  | 1, _, _, a => exact ⟨q1, formKeeps1 hQ O Cl hkey, exchange1 hQ O Cl hkey hAns hTab,
      ridesPast1 O Cl, a⟩
  | 2, _, _, a => exact ⟨q2, formKeeps2 hQ O Cl, exchange2_of hQ O Cl hN weights rand hhU oH hSh,
      ridesPast2 O Cl, a⟩
  | 3, _, _, a => exact ⟨q3, formKeeps3 hQ O Cl, exchange3 hQ O Cl hN hAns, ridesPast3 O Cl, a⟩
  | 4, _, _, a => exact ⟨q4, formKeeps4 hQ O Cl, exchange4_of_tab hQ O Cl hN hTab,
      ridesPast4 O Cl, a⟩
  | 5, _, _, a => exact ⟨q5, formKeeps5 hQ O Cl, exchange5_of hQ O Cl hN weights rand hhO oH hSh,
      ridesPast5 O Cl, a⟩
  | 6, _, _, a => exact ⟨q6, formKeeps6 hQ O Cl, exchange6 O Cl, ridesPast6 O Cl, a⟩
  | 7, _, _, a => exact ⟨q7, formKeeps7 hQ O Cl, exchange7 hQ O Cl hN, ridesPast7 O Cl, a⟩
  | 8, _, _, a => exact ⟨q8, formKeeps8 hQ O Cl, exchange8_book hQ O Cl hN ⟨S, 0, 6⟩ weights rand
      (atSplit_of E8 hQ.facts.two) H.shape rfl rfl oH he, ridesPast8 O Cl, a⟩

/-- **A WHOLE «Behind» at each member b of the eight, UNDER THREE PREMISES ON THE LETTER rides.**
hr: the letter is a list of clauses (Honest/Thread/Riders.lean: ridersOf). hst: each clause that
speaks on both sides of the member stays by the member's clause of keeps. hno: no clause of the list
begins at the border behind the member: a premise on the list, no fact; it is meant for a list into
which the eight lay no clause. -/
theorem k14_behind (h : K14Asks ℓ L Q sentU layO c tests last A weights rand)
    {cs : List (RiderCl (Common W₀ Rc TableKey) St)}
    (hr : ∀ b w s, L.thread.rides b w s ↔ ridersOf cs b w s) (b : Nat) (h1 : 1 ≤ b) (h8 : b ≤ 8)
    (hst : ∀ x ∈ cs, x.lo ≤ b → b + 1 ≤ x.hi → StaysBy L.thread b x)
    (hno : ∀ x ∈ cs, x.lo ≠ b + 1) : Behind L.thread b :=
  behind_of_formKeeps hr (k14_asks h (fun _ _ _ => none) b h1 h8).2.1 hst hno

/-- The like where the letter rides is a sentence R₀ and a list of clauses (Honest/Thread/
RidersAnd.lean): h₀: R₀ holds behind the member's accepted step: whoever lays R₀ shows it. A call of
behind_of_keeps_and. -/
theorem k14_behind_and (h : K14Asks ℓ L Q sentU layO c tests last A weights rand)
    {R₀ : Nat → Common W₀ Rc TableKey → St → Prop}
    {cs : List (RiderCl (Common W₀ Rc TableKey) St)}
    (hr : ∀ b w s, L.thread.rides b w s ↔ R₀ b w s ∧ ridersOf cs b w s) (b : Nat) (h1 : 1 ≤ b)
    (h8 : b ≤ 8)
    (h₀ : ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s', Thr L.thread b k s m E →
      drawsFit blk.rounds ds = true → L.thread.Stepped blk k s m E ds y cols s' →
      R₀ (b + 1) m.st.input s')
    (hst : ∀ x ∈ cs, x.lo ≤ b → b + 1 ≤ x.hi → StaysBy L.thread b x)
    (hno : ∀ x ∈ cs, x.lo ≠ b + 1) : Behind L.thread b :=
  behind_of_keeps_and L.thread hr (k14_asks h (fun _ _ _ => none) b h1 h8).2.1 h₀ hst
    fun x hx e => absurd e (hno x hx)

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.k14_behind_and
#print axioms ProofFile.Honest.K14.k14_asks
#print axioms ProofFile.Honest.K14.k14_behind
