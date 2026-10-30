-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/WholeT.lean: CONDITIONAL: the debts of the member at an
attention segment's own rounds (kind K5), in one statement, WITH THE `Thread` T A VARIABLE, and with
no premise that says that a form is worth 0. A joining: one call.

  `k5_owes_whole_T`   CONDITIONAL: **`Plays` T b, `Behind` T b, `Exchange` T b, and `Accepted` T
                      fall b for every fall**, at b := `borderOf g`

What is joined: `k5_owes_T` (Honest/K5/Law/DebtsT.lean), whose two named premises on values are
shown by `sayOwedT_of` (Honest/K5/Law/SayOwedT.lean) and `joinOwedT_script`
(Honest/K5/Law/JoinT.lean).

THE PREMISES, ALL, and who is meant to pay each.
  h : `P5J.AtMgA`: the hypothesis on the public input: not shown here.
  R : `K5AtT` (Honest/K5/Law/AtT.lean): what eight of T's letters are, in nine fields: whoever lays
      T, by unfolding.
  hg, ha: g is below 12; a is the plan of group g.
  Hs : `K5Seated` (Honest/K5/Law/Seated.lean): the member, the half in T.hs, the public data:
      whoever lays T.hs and makes the public data.
  hfit, hb: the test T.fits: an evaluation.
  Kp, Rd: sentences on T.keeps and T.rides: whoever lays them. They carry two of the four clauses of
      `Behind`.
  hans: `AnsReadsRest`: a sentence on the honest side's letter ans, which has no text here; at
      `ansJT` it holds with no premise (`ansReadsRest_JT`, Honest/K5/Law/AtHeadLetters.lean),
      because the laid pin reads no oracle and, of the state, the statement alone: the weight has
      moved, not gone (that file's head).
  hP: the public data hold the plan's shape and numbers: by the make of the public data.
  TWO PREMISES BEAR ON VALUES OUTRIGHT (hans hands on whatever the letter ans says of them):
  Sc : `K5Script` (Honest/K5/Law/Script.lean): three ties between the witness, the book's coins, the
      trace's cells and the state's key points. IT IS NOT SHOWN.
  hV : `IdnOwed` T.valid (Honest/K5/Law/IdnAt.lean): every valid input's cells meet the library's
      three families of identities. SHOWN OF NO `valid`.

Limits. Conditional; none of the premises is shown to be met, but R at one `Thread` (`k5AtT_thrAt`)
and hans at `ansJT`. At a T.valid that no input meets every premise here can hold, and the statement
then says nothing: what counts, and what is not shown, is a T at which `Thr` T b has a member
and Sc holds. The riders' debt (`RidesPast`) is not among the conclusions. At the library's full
size and the format's second hash function alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.SayOwedT
import Johnson.Desc.ProofFile.Honest.K5.Law.JoinT

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Strs Chain)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (seatTab)
open H2K5.Honest (K5Keeps)
open ProofFile.Honest.FirstThread (WtF)
open P5J (AtMgA TS CellsM)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  {T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst}
  {g : Nat} {it : Item → T.ι} {pb : T.P → ProofFile.InstPub} {wt : T.Wt → WtF}
  {ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop} {test : Nat → TS → Option String}
  {carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop}
  {cq : (Local W₀ Rc ProofFile.Inst Tr) → CellsM OnBytes.Flat.numsFull}

/-- **THE MEMBER's DEBTS IN ONE STATEMENT, WITH T A VARIABLE AND NO PREMISE THAT SAYS THAT A FORM IS
WORTH 0**: it plays; behind its yes; the exchange; it is accepted, for every fall. CONDITIONAL:
every premise stands in the file's head with who is meant to pay it. It bears on values through Sc
and hV, and through whatever the letter ans says of them (hans); neither Sc nor hV is shown. The
riders' debt is not among the conclusions. -/
theorem k5_owes_whole_T (R : K5AtT h T g it pb wt ans test carryX cq) {n : Nat} (hg : g < 12)
    {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl} (Hs : K5Seated T (borderOf g) cells Z5 (parAt Zp g a) blk)
    (hfit : T.fits n = true) (hb : borderOf g < n)
    (Kp : ∀ s s', K5Keeps s s' → T.keeps (borderOf g) s s')
    (Rd : ∀ w s s', T.rides (borderOf g) w s → K5Keeps s s' → T.rides (borderOf g + 1) w s')
    (hans : AnsReadsRest ans ((P5J.At.N Zp cF).sent (2 * g + 1) 0))
    (Sc : K5Script T (borderOf g) cells Z5 a blk (h.𝔇.pubD.N.sent (2 * g + 1) 0)
      fun v => seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms (wt v))
    (hP : Z5.P = ⟨a.S, a.own⟩) (hV : IdnOwed T.valid cells Z5) :
    Plays T (borderOf g) ∧ Behind T (borderOf g) ∧ Exchange T (borderOf g) ∧
      ∀ fall, Accepted T fall (borderOf g) :=
  k5_owes_T h R hg ha Hs hfit hb Kp Rd hans (sayOwedT_of h R hg ha Hs Sc hP hV)
    (joinOwedT_script h R hg ha Hs hfit hb Sc hP)

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5_owes_whole_T
