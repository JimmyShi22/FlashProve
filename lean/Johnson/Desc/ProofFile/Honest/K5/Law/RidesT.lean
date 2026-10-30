-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/RidesT.lean: CONDITIONAL: ALL the debts of the member at an
attention segment's own rounds (kind K5) in one statement, WITH THE `Thread` T A VARIABLE: the four
conjuncts of `Owes` and the one of `Yes` (Honest/Thread/File.lean) at that member. A joining: two
calls.

  `k5_owes_all_T`   CONDITIONAL: **`Plays`, `Behind`, `Exchange`, `RidesPast` at T b, and `Accepted`
                    T fall b for every fall**, at b := `borderOf g`

What is joined: `k5_owes_whole_T` (Honest/K5/Law/WholeT.lean) and `k5_ridesPast_T`
(Honest/K5/Law/RidesPast.lean).

THE PREMISES: those of `k5_owes_whole_T` (its file's head lists them with who is meant to pay each),
and for the riders:
  R : `K5RidersT` (Honest/K5/Law/RidersT.lean): which of T's items ride, what T.means says of them,
      what T.keeps gives: whoever lays T.
  hidx : `AnsOn` at the index masks' tenant: what the honest side's letter ans says there of a state
      and strings it says of every state that `K5Keeps` ties to it, at strings that agree with these
      at the stored table and at every tree sent in front of the border (`StrsKept`): whoever lays
      ans.
With Kp, the field `keeps` of R pins T.keeps at the border to `K5Keeps`.
TWO PREMISES BEAR ON VALUES, as in `k5_owes_whole_T`: Sc (`K5Script`): NOT SHOWN; hV
(`IdnOwed` T.valid): SHOWN OF NO `valid`.

Limits. Conditional; none of the premises is shown to be met, but the two structures at one
`Thread`. At a T.valid that no input meets every premise here can hold, and the statement then says
nothing. It speaks of one member of the chain: `Owes` and `Yes` ask the same at every member. At the
library's full size and the format's second hash function alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.RidesPast
import Johnson.Desc.ProofFile.Honest.K5.Law.WholeT

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

/-- **ALL OF THE MEMBER's DEBTS IN ONE STATEMENT, WITH T A VARIABLE**: it plays; behind its yes; the
exchange; the riders; it is accepted, for every fall. CONDITIONAL: the premises stand in the file's
head. It bears on values through Sc and hV alone; neither is shown. -/
theorem k5_owes_all_T (A : K5AtT h T g it pb wt ans test carryX cq)
    (R : K5RidersT h T g it pb wt ans test carryX cq) {n : Nat} (hg : g < 12)
    {a : Attention.Plan} (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl} (Hs : K5Seated T (borderOf g) cells Z5 (parAt Zp g a) blk)
    (hfit : T.fits n = true) (hb : borderOf g < n)
    (Kp : ∀ s s', K5Keeps s s' → T.keeps (borderOf g) s s')
    (Rd : ∀ w s s', T.rides (borderOf g) w s → K5Keeps s s' → T.rides (borderOf g + 1) w s')
    (hans : AnsReadsRest ans ((P5J.At.N Zp cF).sent (2 * g + 1) 0))
    (hidx : AnsOn ans (P5J.At.N Zp cF).index (treesTo cF.blocksInOrder (borderOf g)))
    (Sc : K5Script T (borderOf g) cells Z5 a blk (h.𝔇.pubD.N.sent (2 * g + 1) 0)
      fun v => seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms (wt v))
    (hP : Z5.P = ⟨a.S, a.own⟩) (hV : IdnOwed T.valid cells Z5) :
    (Plays T (borderOf g) ∧ Behind T (borderOf g) ∧ Exchange T (borderOf g) ∧
      RidesPast T (borderOf g)) ∧ ∀ fall, Accepted T fall (borderOf g) := by
  obtain ⟨h1, h2, h3, h4⟩ := k5_owes_whole_T h A hg ha Hs hfit hb Kp Rd hans Sc hP hV
  exact ⟨⟨h1, h2, h3, k5_ridesPast_T h hg A R hidx⟩, h4⟩

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5_owes_all_T
