-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/JoinAtHead.lean: the join of the senders' lots
(Honest/Thread/Join.lean) under the library's head, that is, at the full size, where the public part
is a parameter and no test can be evaluated. What `agreeB`, `foundB`, `placesB` and K1's half of
`numsB` give at written data comes here from lemmas of the authors of the shared sending (K1) and
from closed facts on the library's written list of places.

  1  `k1Jobs` K1's jobs at a public part and a ground: its own lot's, then the job at W's sending.
     Both lists can be short or empty at a public part that lacks the numbers; under the head they
     have 52 jobs
  2  `byNo_at_head` under the head the jobs, each with the number of its own place, are the list by
     written numbers `k1MembersW` at three written jobs: K1's authors' `members_by_border`
  3  `join_msgsAgree_head`, `join_padsAgree_head` under the head the joined lists agree, if the
     other senders' lots agree among themselves and stand far from K1's sendings (hfarM, hfarP)
  4  `join_tie_k1_head` so K1's tie holds at the joined `Script` at each of the 52 members
  5  `found_of_lt`, `numbers_lt_head`, `ps_nodup`, `places_written`, `places_at_head`,
     `flat_length_head`, `found_at_head`, `nums_at_head`, `fits_at_head`, `lays_at_head`,
     `coins_at_head` what the head pays of `JoinFit` beyond "agree"; the last three are K1's
     authors' (Honest/K1/Law/FitAtMembers.lean)
  6  `joinFit_head`, `joinFit_head_book` under the head the list is fit (`JoinFit`,
     Honest/Thread/JoinFit.lean), under the premises that the docstrings list

Limits.
  * Under the head: a hypothesis. The full size and the format's second hash function alone.
  * hfarM and hfarP are premises on the other senders' lots: each bears the witness's number, or
    sits at the seat, of a seat of the plan's list in none of K1's 52 sendings; for a lot of
    messages no kept copy's. They are proved here of no list.
  * Four premises of `joinFit_head` are four fields of `JoinFit` as they stand (hown, htrees,
    hcoins, hwhole); three of `joinFit_head_book` (hown, htrees, hwhole). They are proved here of no
    description and no record of the other senders.
  * The list of seats stays a parameter here too.
  * At the description's own ground. That a prover's ground is this one is not said here.
  * `join_tie_k1_head` asks nothing of the book: its docstring says what that means for whoever
    quotes the lemma. It does not ask that each seat is owned: `join_tie_k1_fit` at `joinFit_head`
    does.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.JoinFit
import Johnson.Desc.ProofFile.Honest.K1.Law.MembersByBorder
import Johnson.Desc.ProofFile.Honest.K1.Law.AgreeFar
import Johnson.Desc.ProofFile.Honest.K1.Law.FitAtMembers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K1 (momL)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open OnBytes.Maker (WholeD)
open OnBytes.SendSim.Seat (wJobs)
open _root_.Desc.K14.Law (seatZ secondAt)
open ProofFile.Honest.K1

variable {Bk : ProverCoinCounts} {Cl Wl Xi X Cells Tok : Type}

/-! ## 1 K1's jobs -/

/-- **K1's jobs at a public part and a ground**: its own lot's, then the job at W's sending. -/
def k1Jobs (no : Place → Nat) (Dt Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) : List (SendJob (PlaceIn Xi) X) :=
  lotJobs no Dt Z G ++ wJobs no Dd Z G

/-! ## 2 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x₀ : First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block S ProofFile.Cl)}

/-- The opening's job, written. -/
abbrev headJ₂ (Zp : ProofFile.Pub) (G : ProofFile.Ground) (no : Place → Nat)
    (Dt : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) : SendJob (PlaceIn Xi) X :=
  placeJob (K1.firstPar G.first (K1.gpOf Zp)) (no ⟨1, some 0, 1, .K1⟩) (firstFold G.first) (Dt Zp G)

/-- The later jobs, written. -/
abbrev headJl (Zp : ProofFile.Pub) (G : ProofFile.Ground) (no : Place → Nat)
    (Dt : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (l : ℕ) (d : Bool) : SendJob (PlaceIn Xi) X :=
  laterJobAt G.first (K1.gpOf Zp) l (IM.k1Ix l d + 1) (if d then 2 else 1)
    (no ⟨1, some l, IM.k1Ix l d + 1, .K1⟩) (Dt Zp G)

/-- The job at W's sending, written. -/
abbrev headJw (Zp : ProofFile.Pub) (G : ProofFile.Ground) (no : Place → Nat)
    (Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) : SendJob (PlaceIn Xi) X :=
  wJobAt Zp.first (wGp Zp) 4 wMsgFull (no ⟨1, none, 4, .K1⟩) (Dd Zp G)

section
variable (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
  (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
    (seatZ Zp Np) (secondAt Zp Np))
  (no : Place → Nat) (Dt Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi)
include h O

/-- **Under the head the jobs, each with the number of its own place, are the list by written
numbers.** -/
theorem byNo_at_head :
    byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀) =
      k1MembersW (headJ₂ Zp Bs.G₀ no Dt) (headJl Zp Bs.G₀ no Dt) (headJw Zp Bs.G₀ no Dd) :=
  members_by_border h O no Dt Dd

/-- **Under the head the joined lots of messages agree**, if the others' agree among themselves and
each of them bears the witness's number at a seat of the plan's list that is no kept copy's and
stands in none of K1's 52 sendings. -/
theorem join_msgsAgree_head (front : Nat) (wit : Wl → PlaceIn Xi) (own₀ : X) {Oth : Others Bk Wl}
    (hml : MsgsAgree Oth.ml)
    (hfarM : ∀ L' ∈ Oth.ml, ∃ j t q,
      ((P5J.At.pseatsAll Zp).find? fun p => p.j == j && p.t == t) = some q ∧
        L'.n = P5J.At.arr Zp j t ∧ (∀ l' k', q.role ≠ .kept l' k') ∧ q.send ≠ 0 ∧
        (∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d) ∧ q.send ≠ 81) :
    MsgsAgree (joinMl cF.blocksInOrder front (P5J.At.arr Zp) wit own₀
      (byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀)) Oth) := by
  unfold joinMl
  rw [byNo_at_head h O no Dt Dd]
  exact k1_msgsAgree_with h O (two_plan_head Zp Bs.G₀ _ _)
    (fun l _ d => later_plan_head Zp Bs.G₀ l d _ _) (w_plan_head Zp _ _) front wit own₀ hml hfarM

/-- **Under the head the joined lots of pads agree**, if the others' agree among themselves and each
of them sits at a seat of the plan's list in none of K1's 52 sendings. -/
theorem join_padsAgree_head {Oth : Others Bk Wl} (hpl : PadsAgree Oth.pl)
    (hfarP : ∀ L' ∈ Oth.pl, ∃ q ∈ P5J.At.pseatsAll Zp, L'.j = q.j ∧ L'.t = q.t ∧ q.send ≠ 0 ∧
      (∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d) ∧ q.send ≠ 81) :
    PadsAgree (joinPl cF.blocksInOrder (byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀)) Oth) := by
  unfold joinPl
  rw [byNo_at_head h O no Dt Dd]
  exact k1_padsAgree_with h O (two_plan_head Zp Bs.G₀ _ _)
    (fun l _ d => later_plan_head Zp Bs.G₀ l d _ _) (w_plan_head Zp _ _) hpl hfarP

/-- **Under the head K1's tie holds at the joined `Script`, at each of K1's members.** At a book
whose count at the part's address does not cover the part's due this law holds for nothing, and it
is never quoted as if it spoke there: hasCoins is neither asked nor paid here: whoever quotes this
law at a book names hasCoins at that book beside it. -/
theorem join_tie_k1_head (front : Nat) (wit : Wl → PlaceIn Xi) (own₀ : X) {Oth : Others Bk Wl}
    (hml : MsgsAgree Oth.ml) (hpl : PadsAgree Oth.pl)
    (hfarM : ∀ L' ∈ Oth.ml, ∃ j t q,
      ((P5J.At.pseatsAll Zp).find? fun p => p.j == j && p.t == t) = some q ∧
        L'.n = P5J.At.arr Zp j t ∧ (∀ l' k', q.role ≠ .kept l' k') ∧ q.send ≠ 0 ∧
        (∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d) ∧ q.send ≠ 81)
    (hfarP : ∀ L' ∈ Oth.pl, ∃ q ∈ P5J.At.pseatsAll Zp, L'.j = q.j ∧ L'.t = q.t ∧ q.send ≠ 0 ∧
      (∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d) ∧ q.send ≠ 81)
    (cells : Wl → Cells) (tok : Wl → Tok) (Vd : Wl → Prop)
    {x : Nat × SendJob (PlaceIn Xi) X}
    (hx : x ∈ byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀)) :
    (∀ n, n < x.2.P.sent.size →
      OwnMsgs (joinQ cF.blocksInOrder front cells tok (P5J.At.arr Zp) wit own₀
          (byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀)) Oth) Vd
        (front + roundsTo cF.blocksInOrder x.1)
        (P5J.At.arr Zp (seatAtMember cF.blocksInOrder x.1 x.2.P n).1 (seatAtMember cF.blocksInOrder x.1 x.2.P n).2)
        (front + roundsTo cF.blocksInOrder x.1) (msgTxt 0 wit x.2 own₀ n)) ∧
    ∀ n, n < x.2.P.sent.size →
      OwnPads (joinQ cF.blocksInOrder front cells tok (P5J.At.arr Zp) wit own₀
          (byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀)) Oth) Vd
        (seatAtMember cF.blocksInOrder x.1 x.2.P n).1 (seatAtMember cF.blocksInOrder x.1 x.2.P n).2
        (fun k _ => padTxt 0 x.2 n k) :=
  join_tie_k1_of (join_msgsAgree_head h O no Dt Dd front wit own₀ hml hfarM)
    (join_padsAgree_head h O no Dt Dd hpl hfarP) cells tok Vd hx

/-! ## 3 What the head pays of `JoinFit` beyond "agree" -/

end

/-- A job of `byNo`'s list whose number lies below the flat list's length: its number bears a block
at the job's place. -/
theorem found_of_lt {bs : List (Block S Cl)} {js : List (SendJob (PlaceIn Xi) X)} :
    ∀ x ∈ byNo bs js, x.1 < bs.length → ∃ blk, bs[x.1]? = some blk ∧ blk.place = x.2.P.place := by
  intro x hx hlt
  unfold byNo at hx
  obtain ⟨J, -, rfl⟩ := List.mem_map.1 hx
  have hlt' : bs.findIdx (fun y : Block S Cl => y.place == J.P.place) < bs.length := hlt
  show ∃ blk, bs[bs.findIdx (fun y : Block S Cl => y.place == J.P.place)]? = some blk ∧
    blk.place = J.P.place
  refine ⟨bs[bs.findIdx (fun y : Block S Cl => y.place == J.P.place)]'hlt',
    List.getElem?_eq_getElem hlt', ?_⟩
  exact beq_iff_eq.1
    (List.findIdx_getElem (p := fun y : Block S Cl => y.place == J.P.place) (w := hlt'))

/-- The 52 written numbers lie below 358. A closed fact. -/
theorem numbers_lt_head (J₂ : SendJob (PlaceIn Xi) X) (Jl : ℕ → Bool → SendJob (PlaceIn Xi) X)
    (Jw : SendJob (PlaceIn Xi) X) : ∀ n ∈ (k1MembersW J₂ Jl Jw).map (·.1), n < 358 := by
  unfold k1MembersW k1Members
  rw [List.map_append, List.map_cons, List.map_flatMap]
  show ∀ n ∈ (2 :: (List.range 25).flatMap (fun l => [K1.noL l false, K1.noL l true]) ++ [356]),
    n < 358
  decide +kernel

/-- No place stands twice in the library's written list of places. A closed fact. -/
theorem ps_nodup : P5J.At.ps.Nodup := by decide +kernel

section
variable (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
include h

/-- Under the head the flat list's places are the written list. -/
theorem places_written : cF.blocksInOrder.map (·.place) = P5J.At.ps :=
  P5J.At.places_paid h.scope h.reads h.laid

/-- **Under the head no place stands twice in the flat list.** -/
theorem places_at_head : (cF.blocksInOrder.map (·.place)).Nodup := by
  rw [places_written h]
  exact ps_nodup

/-- Under the head the flat list has 358 members. -/
theorem flat_length_head : cF.blocksInOrder.length = 358 := by
  have l := congrArg List.length (places_written h)
  rw [List.length_map] at l
  rw [l]
  exact congrArg Prod.snd bordersW_bites

end

section
variable (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
  (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
    (seatZ Zp Np) (secondAt Zp Np))
  (no : Place → Nat) (Dt Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi)
include h O

/-- **Under the head each of K1's 52 numbers bears a block at the job's place.** -/
theorem found_at_head : ∀ x ∈ byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀),
    ∃ blk, cF.blocksInOrder[x.1]? = some blk ∧ blk.place = x.2.P.place := by
  intro x hx
  refine found_of_lt x hx ?_
  rw [flat_length_head h]
  refine numbers_lt_head (X := X) (headJ₂ Zp Bs.G₀ no Dt) (headJl Zp Bs.G₀ no Dt)
    (headJw Zp Bs.G₀ no Dd) x.1 ?_
  rw [← byNo_at_head h O no Dt Dd]
  exact List.mem_map.2 ⟨x, hx, rfl⟩

/-- **Under the head no number stands twice among K1's 52.** -/
theorem nums_at_head : ((byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀)).map (·.1)).Nodup := by
  rw [byNo_at_head h O no Dt Dd]
  exact k1MembersW_nodup _ _ _

/-- **Under the head the block at each of K1's 52 numbers declares as many trees as the job's plan
has**: K1's authors' `fits_at_members`. -/
theorem fits_at_head : ∀ x ∈ byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀), ∀ blk,
    cF.blocksInOrder[x.1]? = some blk → (blk.oracles.flatMap id).length = x.2.P.trees.length := by
  intro x hx blk hb
  rw [byNo_at_head h O no Dt Dd] at hx
  exact fits_at_members h O (two_plan_head Zp Bs.G₀ _ _)
    (fun l _ d => later_plan_head Zp Bs.G₀ l d _ _) (w_plan_head Zp _ _) hx blk hb

/-- **Under the head the trees of each of K1's 52 plans can be laid**: K1's authors'
`lays_at_members`. -/
theorem lays_at_head : ∀ x ∈ byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀),
    Own.treesCan x.2.P.codes x.2.P.sent = true := by
  intro x hx
  rw [byNo_at_head h O no Dt Dd] at hx
  exact lays_at_members h O (two_plan_head Zp Bs.G₀ _ _)
    (fun l _ d => later_plan_head Zp Bs.G₀ l d _ _) (w_plan_head Zp _ _) hx

/-- **Under the head, at the book that `onlineProverFromPublicFiles` returns, the count at each of K1's 52 addresses is
the part's due**: K1's authors' `coins_at_members`. -/
theorem coins_at_head {W₀ Rc Tr X₀ Xa : Type} {P : OnlineProverParts W₀ Rc Tr X₀ Xa}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ Xa} (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    ∀ x ∈ byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀),
      dueAt (A.B.rowsOf 0) ⟨x.2.P.place, 0⟩ = dueR x.2.P x.2.ride := by
  intro x hx
  rw [byNo_at_head h O no Dt Dd] at hx
  exact coins_at_members h O hA no Dt Dd rfl (fun _ _ => rfl) rfl hx

/-- **Under the head the list is fit.** Paid here, from the head: that the joined lists agree (from
hml, hpl, hfarM, hfarP), that each job's number bears a block at the job's place with the plan's
count of trees, that each plan's trees can be laid, that no place stands twice, and K1's half of "no
number twice". The others' half of that: htn, hdis. Four premises are fields of `JoinFit` as they
stand and are handed through: hown, htrees, hcoins, hwhole. `joinFit_head_book` pays hcoins at the
book that `onlineProverFromPublicFiles` returns. -/
theorem joinFit_head (front : Nat) (seats : List (Nat × Nat)) (wit : Wl → PlaceIn Xi) (own₀ : X)
    {Oth : Others Bk Wl} (hml : MsgsAgree Oth.ml) (hpl : PadsAgree Oth.pl)
    (hfarM : ∀ L' ∈ Oth.ml, ∃ j t q,
      ((P5J.At.pseatsAll Zp).find? fun p => p.j == j && p.t == t) = some q ∧
        L'.n = P5J.At.arr Zp j t ∧ (∀ l' k', q.role ≠ .kept l' k') ∧ q.send ≠ 0 ∧
        (∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d) ∧ q.send ≠ 81)
    (hfarP : ∀ L' ∈ Oth.pl, ∃ q ∈ P5J.At.pseatsAll Zp, L'.j = q.j ∧ L'.t = q.t ∧ q.send ≠ 0 ∧
      (∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d) ∧ q.send ≠ 81)
    (hown : ∀ s ∈ seats,
      (∃ L ∈ joinMl cF.blocksInOrder front (P5J.At.arr Zp) wit own₀
          (byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀)) Oth, L.n = P5J.At.arr Zp s.1 s.2) ∧
        ∃ L ∈ joinPl cF.blocksInOrder (byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀)) Oth,
          L.j = s.1 ∧ L.t = s.2)
    (htn : Oth.tn.Nodup)
    (hdis : ∀ b ∈ Oth.tn, b ∉ (byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀)).map (·.1))
    (htrees : ∀ b blk, cF.blocksInOrder[b]? = some blk → (blk.oracles.flatMap id).length ≠ 0 →
      b ∈ (byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀)).map (·.1) ++ Oth.tn)
    (hcoins : ∀ x ∈ byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀),
      dueAt (Bk.rowsOf 0) ⟨x.2.P.place, 0⟩ = dueR x.2.P x.2.ride)
    (hwhole : ∀ s ∈ flatSeats cF.blocksInOrder, s ∈ seats) :
    JoinFit cF.blocksInOrder front (P5J.At.arr Zp) seats wit own₀
      (byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀)) Oth :=
  ⟨join_msgsAgree_head h O no Dt Dd front wit own₀ hml hfarM,
    join_padsAgree_head h O no Dt Dd hpl hfarP, hown,
    List.Nodup.append (nums_at_head h O no Dt Dd) htn fun _ ha hb => hdis _ hb ha, htrees,
    found_at_head h O no Dt Dd, fits_at_head h O no Dt Dd, places_at_head h, hcoins, hwhole,
    lays_at_head h O no Dt Dd⟩

/-- **The same at the book that `onlineProverFromPublicFiles` returns**: hcoins is paid by `coins_at_head`. Three
premises are fields of `JoinFit` as they stand: hown, htrees, hwhole. -/
theorem joinFit_head_book {W₀ Rc Tr X₀ Xa : Type} {P : OnlineProverParts W₀ Rc Tr X₀ Xa}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ Xa} (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (front : Nat) (seats : List (Nat × Nat)) (wit : Wl → PlaceIn Xi) (own₀ : X)
    {Oth : Others A.B Wl} (hml : MsgsAgree Oth.ml) (hpl : PadsAgree Oth.pl)
    (hfarM : ∀ L' ∈ Oth.ml, ∃ j t q,
      ((P5J.At.pseatsAll Zp).find? fun p => p.j == j && p.t == t) = some q ∧
        L'.n = P5J.At.arr Zp j t ∧ (∀ l' k', q.role ≠ .kept l' k') ∧ q.send ≠ 0 ∧
        (∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d) ∧ q.send ≠ 81)
    (hfarP : ∀ L' ∈ Oth.pl, ∃ q ∈ P5J.At.pseatsAll Zp, L'.j = q.j ∧ L'.t = q.t ∧ q.send ≠ 0 ∧
      (∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d) ∧ q.send ≠ 81)
    (hown : ∀ s ∈ seats,
      (∃ L ∈ joinMl cF.blocksInOrder front (P5J.At.arr Zp) wit own₀
          (byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀)) Oth, L.n = P5J.At.arr Zp s.1 s.2) ∧
        ∃ L ∈ joinPl cF.blocksInOrder (byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀)) Oth,
          L.j = s.1 ∧ L.t = s.2)
    (htn : Oth.tn.Nodup)
    (hdis : ∀ b ∈ Oth.tn, b ∉ (byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀)).map (·.1))
    (htrees : ∀ b blk, cF.blocksInOrder[b]? = some blk → (blk.oracles.flatMap id).length ≠ 0 →
      b ∈ (byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀)).map (·.1) ++ Oth.tn)
    (hwhole : ∀ s ∈ flatSeats cF.blocksInOrder, s ∈ seats) :
    JoinFit cF.blocksInOrder front (P5J.At.arr Zp) seats wit own₀
      (byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀)) Oth :=
  joinFit_head h O no Dt Dd front seats wit own₀ hml hpl hfarM hfarP hown htn hdis htrees
    (coins_at_head h O no Dt Dd hA) hwhole

end

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k1Jobs
#print axioms ProofFile.Honest.FirstThread.headJ₂
#print axioms ProofFile.Honest.FirstThread.headJl
#print axioms ProofFile.Honest.FirstThread.headJw
#print axioms ProofFile.Honest.FirstThread.byNo_at_head
#print axioms ProofFile.Honest.FirstThread.join_msgsAgree_head
#print axioms ProofFile.Honest.FirstThread.join_padsAgree_head
#print axioms ProofFile.Honest.FirstThread.join_tie_k1_head
#print axioms ProofFile.Honest.FirstThread.found_of_lt
#print axioms ProofFile.Honest.FirstThread.numbers_lt_head
#print axioms ProofFile.Honest.FirstThread.ps_nodup
#print axioms ProofFile.Honest.FirstThread.places_written
#print axioms ProofFile.Honest.FirstThread.places_at_head
#print axioms ProofFile.Honest.FirstThread.flat_length_head
#print axioms ProofFile.Honest.FirstThread.found_at_head
#print axioms ProofFile.Honest.FirstThread.nums_at_head
#print axioms ProofFile.Honest.FirstThread.fits_at_head
#print axioms ProofFile.Honest.FirstThread.lays_at_head
#print axioms ProofFile.Honest.FirstThread.coins_at_head
#print axioms ProofFile.Honest.FirstThread.joinFit_head
#print axioms ProofFile.Honest.FirstThread.joinFit_head_book
