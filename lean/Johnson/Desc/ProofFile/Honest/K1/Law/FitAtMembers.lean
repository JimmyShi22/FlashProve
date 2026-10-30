-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/FitAtMembers.lean: THE SHARED "SENDING" (the kind K1): THREE
PUBLIC FACTS AT EACH OF THE KIND's 52 MEMBERS ON THE FIRST CHAIN, IN THE FORMS IN WHICH A JOIN OF
THE SENDERS' LOTS ASKS THEM OF K1's JOBS: the member's block states as many trees as the job's plan
has · the plan's trees can be laid · the book A.B of the prover that onlineProverFromPublicFiles returns has the part's
count. PUBLIC DATA ALONE: places, plans, counts: how many coins a part has, never what they are.
Four theorems; no definition. BY CALLS. A TRIAL THAT COUNTS IN NO COLUMN.

- count_of_oracles: where a block's oracle messages are K1.oracles P, it states P.trees.length
    trees: by unfolding. (The step stands as an inner "have" in Honest/K1/OwnTreesK1.lean and
    PlaysS.lean.)
- fits_at_members: UNDER h, O AND THE THREE PLANS' EQUATIONS: at each x of k1MembersW J₂ Jl Jw and
    each block at the flat list's number x.1: the count of its trees is the plan's.
- lays_at_members: under the same: Own.treesCan at x's plan: three calls: condPort at the plan, the
    sealed cond_parts (Johnson/Desc/K1/Law/Port6.lean) and can_of_own
    (Johnson/Desc/AtSeats/CountsAtSend.lean).
- coins_at_members: UNDER h, O, hA AND THE THREE JOBS' EQUATIONS: at each x: the record's field
    hasCoins (K1Seated, Honest/K1/Seated.lean), to the letter, at Bk := A.B.

WHICH LAW GIVES WHAT. The member's shape: k1_two_inScope, k1_fifty_inScope (MemberInScope.lean),
k1_w_inScope (MemberAtW.lean) at the message that msg_w_head names (FitsAtW.lean) · condPort:
port_first, port_later, parL_later (PiecesAndPort.lean), port_w_head (FitsAtW.lean) · hasCoins:
hasCoins_two_at_book, hasCoins_fifty_at_book, hasCoins_w_at_book (HasCoinsAtBook.lean) · A.Z = Zp
and A.G = Bs.G₀: ProofFile's atPure_at_laid_ground (Honest/AtHeadGround.lean).

Who calls. ProofFile's fits_at_head, lays_at_head, coins_at_head (Honest/Thread/JoinAtHead.lean; a trial
, at the list byNo cF.blocksInOrder (k1Jobs no Dt Dd Zp Bs.G₀), behind byNo_at_head: for three fields
of JoinFit (Honest/Thread/JoinFit.lean): fits and lays in joinFit_head, coins in joinFit_head_book.

Kin. For the count, by a longer road and with "flatten": the sealed told_counts
(Johnson/Desc/K1/Law/ToldCounts.lean: under Own.treesCan, (oracles P).flatten.length = (layOf
P).shapes.size) with trees_eq_lay (Johnson/Desc/K13/Law/RootsBehind.lean: the plan's trees' number
is that size): not called.

THE JOBS. J₂, Jl, Jw are letters. The first two laws ask their PLANS alone (hP₂, hPl, hPw: the three
premises of AgreeFar.lean); the third asks the jobs (hJ₂, hJl, hJw), at any numbers no and any data
Dt, Dd: a caller meets all six by rfl or by later_plan_head (LotJobsAtHead.lean).

Limits. THE HEAD IS A HYPOTHESIS; so is hA: that onlineProverFromPublicFiles returns is not said here; the filling P is a
letter. NO SCRIPT, NO LOT, NO RECORD OF ANOTHER SENDER AND NO TIE IS NAMED: the file stands beneath
the join, not over it. THE FULL SIZE ALONE. THE FORMAT's EARLIER HASH. THE FIRST CHAIN ALONE. That a
block stands at the number x.1 is fits_at_members' premise hb: stands_two and its fellows
(MembersStand.lean) have it. Nothing on any run, coin's value, thread or measure. A walk by text
along the lines of imports rings thrice in its closure: Johnson/Desc/K1/Law/HandsMoreAtLater.lean,
Johnson/Desc/K14/Law/SharedConst.lean, Honest/Thread/First.lean; its own code names no measure. The
sentence for whoever calls, in marks: "Whoever calls one of these in
front of a law over coins names h, O and (for the third) hA beside it: they are premises, paid
nowhere here." No property is claimed.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.AtSeats.CountsAtSend
import Johnson.Desc.ProofFile.Honest.AtHeadGround
import Johnson.Desc.ProofFile.Honest.K1.Law.LotsAtAll
import Johnson.Desc.ProofFile.Honest.K1.Law.MemberInScope
import Johnson.Desc.ProofFile.Honest.K1.Law.MemberAtW
import Johnson.Desc.ProofFile.Honest.K1.Law.FitsAtW
import Johnson.Desc.ProofFile.Honest.K1.Law.PiecesAndPort
import Johnson.Desc.ProofFile.Honest.K1.Law.HasCoinsAtBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open _root_.Desc.K14.Law (seatZ secondAt)

/-- Where a block's oracle messages are the plan's, it states as many trees as the plan has. -/
theorem count_of_oracles {St Cl : Type} {blk : Block St Cl} {P : K1.Par}
    (e : blk.oracles = K1.oracles P) : (blk.oracles.flatMap id).length = P.trees.length := by
  rw [e]
  simp [K1.oracles]

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block TS ProofFile.Cl)} {Xi X : Type}

section
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
  (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
    (seatZ Zp Np) (secondAt Zp Np))
  {J₂ : SendJob (PlaceIn Xi) X} {Jl : ℕ → Bool → SendJob (PlaceIn Xi) X}
  {Jw : SendJob (PlaceIn Xi) X}
  (hP₂ : J₂.P = K1.firstPar Bs.G₀.first (K1.gpOf Zp))
  (hPl : ∀ l, l < 25 → ∀ d, (Jl l d).P = K1.parL Zp Bs.G₀ l d)
  (hPw : Jw.P = K1.parW Zp.first (wGp Zp) 4 wMsgFull)
include h O hP₂ hPl hPw

/-- h, O AND THE THREE PLANS' EQUATIONS ARE PREMISES. **AT EACH OF THE 52: THE MEMBER's BLOCK STATES
AS MANY TREES AS THE JOB's PLAN HAS.** -/
theorem fits_at_members {x : ℕ × SendJob (PlaceIn Xi) X} (hx : x ∈ k1MembersW J₂ Jl Jw)
    (blk : Block TS ProofFile.Cl) (hb : cF.blocksInOrder[x.1]? = some blk) :
    (blk.oracles.flatMap id).length = x.2.P.trees.length := by
  rcases mem_k1MembersW.1 hx with hx | rfl
  · obtain rfl | ⟨l, hl, d, rfl⟩ := mem_k1Members.1 hx <;> dsimp only at hb ⊢
    · rw [hP₂]
      exact count_of_oracles (k1_two_inScope h.scope h.reads O hb).1.2.2
    · rw [hPl l hl d]
      exact count_of_oracles (k1_fifty_inScope h.scope h.reads O hl d hb).1.2.2
  · dsimp only at hb ⊢
    obtain ⟨msg, hmsg, h1, -, -⟩ := k1_w_inScope h.scope h.reads O hb
    obtain rfl : msg = wMsgFull := Option.some.inj (hmsg.symm.trans (msg_w_head h O))
    rw [hPw]
    exact count_of_oracles h1.2.2

/-- h, O AND THE THREE PLANS' EQUATIONS ARE PREMISES. **AT EACH OF THE 52: THE PLAN's TREES CAN BE
LAID.** -/
theorem lays_at_members {x : ℕ × SendJob (PlaceIn Xi) X} (hx : x ∈ k1MembersW J₂ Jl Jw) :
    Own.treesCan x.2.P.codes x.2.P.sent = true := by
  have hp1 := K1.pin1_atAll h
  rcases mem_k1MembersW.1 hx with hx | rfl
  · obtain rfl | ⟨l, hl, d, rfl⟩ := mem_k1Members.1 hx <;> dsimp only
    · rw [hP₂]
      exact K1.can_of_own (K1.cond_parts _ _
        (port_first _ _ (K1.hc_atAll h O hp1) (K1.hs_atAll h O hp1))).1
    · rw [hPl l hl d, parL_later]
      exact K1.can_of_own (K1.cond_parts _ _
        (port_later _ _ (K1.hc_atAll h O hp1) (K1.hs_atAll h O hp1) hl _
          (by cases d; exact Or.inl rfl; exact Or.inr rfl))).1
  · dsimp only
    rw [hPw]
    exact K1.can_of_own (K1.cond_parts _ _ (port_w_head h O)).1

end

/-- h, O, hA AND THE THREE JOBS' EQUATIONS ARE PREMISES. **AT EACH OF THE 52: hasCoins AT A.B.** How
many coins the part has at the book: a count. -/
theorem coins_at_members (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    {W₀ Rc Tr X₀ Xa : Type} {P : OnlineProverParts W₀ Rc Tr X₀ Xa} {A : OnlineProverWithDescription W₀ Rc Tr X₀ Xa}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (no : Place → ℕ) (Dt Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi)
    {J₂ : SendJob (PlaceIn Xi) X} {Jl : ℕ → Bool → SendJob (PlaceIn Xi) X}
    {Jw : SendJob (PlaceIn Xi) X}
    (hJ₂ : J₂ = placeJob (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) (no ⟨1, some 0, 1, .K1⟩)
      (firstFold Bs.G₀.first) (Dt Zp Bs.G₀))
    (hJl : ∀ l d, Jl l d = laterJobAt Bs.G₀.first (K1.gpOf Zp) l (IM.k1Ix l d + 1)
      (if d then 2 else 1) (no ⟨1, some l, IM.k1Ix l d + 1, .K1⟩) (Dt Zp Bs.G₀))
    (hJw : Jw = wJobAt Zp.first (wGp Zp) 4 wMsgFull (no ⟨1, none, 4, .K1⟩) (Dd Zp Bs.G₀))
    {x : ℕ × SendJob (PlaceIn Xi) X} (hx : x ∈ k1MembersW J₂ Jl Jw) :
    dueAt (A.B.rowsOf 0) ⟨x.2.P.place, 0⟩ = dueR x.2.P x.2.ride := by
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  rcases mem_k1MembersW.1 hx with hx | rfl
  · obtain rfl | ⟨l, hl, d, rfl⟩ := mem_k1Members.1 hx <;> dsimp only
    · exact hasCoins_two_at_book h hA _ _ (by rw [hJ₂, eZ, eG])
    · exact hasCoins_fifty_at_book h hA hl d _ _ (by rw [hJl, eZ, eG])
  · exact hasCoins_w_at_book h hA _ _ hJw

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.count_of_oracles
#print axioms ProofFile.Honest.K1.fits_at_members
#print axioms ProofFile.Honest.K1.lays_at_members
#print axioms ProofFile.Honest.K1.coins_at_members
