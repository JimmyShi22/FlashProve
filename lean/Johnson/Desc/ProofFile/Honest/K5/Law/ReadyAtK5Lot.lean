-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/ReadyAtK5Lot.lean: IT IS NOT THE HONEST PROVER: OF THE ELEVEN
KINDS THAT HAVE A SIDE IN THE FIRST CHAIN TEN SEND NOTHING HERE, AND THE OTHER TWO CHAINS HAVE NO
SIDE. Conditional: under the library's head, at a filling whose one lot is the lot of the kind K5
(the attention sub-protocol's own rounds) and which lays no side in the shared and the second chain:
WHERE THE MAKER `onlineProverFromPublicFiles` RETURNS A, `ready` (Honest/Frame.lean) RETURNS AT THE HEAD's DESCRIPTION,
A's BOOK AND A's PROVER, at every index in range, every request with a trace, every rc and every
run's coins. Statements with their proofs; no definition; nothing is evaluated.

  `k5Lot_place_at_head`  each side of the lot stands at the kind's place of a group below 12 (near
                         kin, without the head: `k5LotK_place`, LotClean.lean)
  `k5_member_steps`      `chainSteps` returns at the kind's member of group g by itself, at the
                         maker's book, wherever the list of sides has the kind's side there
  `ready_at_k5Lot`       **the statement**

What it is for. "`ready` returns" is a premise of the laws that enter a thread's invariant at the
first chain's start. This file shows that it can be met at the real description and the real book of
coins at the full size: at a THIN prover. The description, the book and the twelve sides are the
real ones; all other members of the three chains are played by nobody. WHY A THIN PROVER MEETS THE
REAL BOOK: the maker makes its book of the description and the sendings before it looks at the
filling: the book is the whole book whatever the lots. Which premise it is meant for: hR, "`ready`
returns", of the laws on a thread's invariant at border 0 (`enters_head`,
Honest/Thread/EntersHead.lean), at a filling with the wanted trace; their premises on a `Script`
name no prover and are not touched. By the frame's `ready_any` (Honest/Law/ReadyAny.lean) one return
gives the return at every index in range, request with a trace, rc and run's coins: "at every" is no
more than "at one" here.

The premises. h: the library's head (`P5J.AtMgA`). hL, hS, h2: the filling's three lists. hA: the
maker returns A. hi: the index is in the filling's range. ht: the request has a trace.

By. `ready_of_parts`, `chainSteps_of_members`, `chainSteps_bare` (ReadyOfParts.lean);
`chainSteps_side` (the same file); `rounds_of_cut` (Honest/Small/RoundsOfCut.lean);
`k5_bookFits_at_maker`, `k5_partsCut` (BookFits5.lean); `k5_lends_paid_fill` (FillFoot.lean) with
`lends5_iff` (LendsHalf.lean); `k5LotK_find_K3` (LotFind.lean); `twice_firstOf`,
`k5LotK_places_once` (LotClean.lean); `atPure_tests`, `atPure_ok` (Honest/AtPureLaw.lean);
`planOk_all` (Honest/Thread/File.lean); `shaped_parts` (Honest/Law/Data.lean).

Limits. NOT THE HONEST PROVER: see the first lines. NEVER UNDER A LAW OVER COINS, NEVER AS "THE
PROVER", never as a ground that anything is simulated. "`ready` returns" says nothing on whether a
part plays, a round is reached or a verifier accepts; whether a run of this prover can be accepted
is not looked at here. THAT `onlineProverFromPublicFiles` RETURNS AT ANY FILLING WITH THESE THREE LISTS IS NOT SHOWN IN
THIS FILE: THE LAW MAY HOLD OF NOTHING.
That an index is in range and that a request has a trace are premises here too.
The full size and the earlier hash `OnBytes.secondHashFunction` alone. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.ReadyOfParts
import Johnson.Desc.ProofFile.Honest.K5.Law.BookFits5
import Johnson.Desc.ProofFile.Honest.K5.Law.FillFoot
import Johnson.Desc.ProofFile.Honest.K5.Law.LendsHalf
import Johnson.Desc.ProofFile.Honest.K5.Law.LotFind
import Johnson.Desc.ProofFile.Honest.K5.Law.LotClean
import Johnson.Desc.ProofFile.Honest.Small.RoundsOfCut
import Johnson.Desc.ProofFile.Honest.Thread.File
import Johnson.Desc.ProofFile.Honest.Law.Data

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block FileDescription Place Chain)
open H2K5.Honest (shapes)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **Each side of the lot stands at the kind's place of a group below 12.** CONDITIONAL: h; hG: G
is the ground that is made of the head's public part. -/
theorem k5Lot_place_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {W₀ Rc Tr X : Type} (cells : Tr → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)) :
    ∀ q ∈ (k5LotK (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) cells keyOf).halves Zp G,
      ∃ j, j < 12 ∧ q.place = placeOf j := by
  intro q hq
  rw [halves_k5LotK] at hq
  unfold halvesBy at hq
  rw [H2K5.Row.k5Places_scope h.scope h.reads h.laid.pub hG, List.filterMap_map] at hq
  obtain ⟨j, hj, e⟩ := List.mem_filterMap.1 hq
  obtain ⟨Y, hY, rfl⟩ := Option.map_eq_some_iff.1 e
  have e0 : Y.link = 2 * j + 1 := seatAtK_link _ _ _ _ hY
  refine ⟨j, List.mem_range.1 hj, ?_⟩
  show (⟨1, some Y.link, 3, .K5⟩ : Place) = placeOf j
  rw [e0]

/-- **`chainSteps` returns at the kind's member of group g by itself, at the maker's book**,
wherever the list of sides has the kind's side at the member's place. CONDITIONAL: h; g is below
12; hA; blk is the member and a the plan of group g; hf. -/
theorem k5_member_steps (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {g : Nat} (hg : g < 12)
    {W₀ Rc X₀ X : Type} {P : OnlineProverParts W₀ Rc Cells X₀ X} {A : OnlineProverWithDescription W₀ Rc Cells X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) {a : OnBytes.Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {blk : Block TS ProofFile.Cl}
    (Dc : DecidesAs (parAt Zp g a) blk)
    {hs : List (Placed (Local W₀ Rc ProofFile.Inst Cells) (Local W₀ Rc ProofFile.Inst Cells) X)}
    (hf : (hs.find? fun q => q.place == blk.place) =
      some (k5Half id (seatOf keyOfK3 Zp A.G cF g a)))
    (v : Option (Local W₀ Rc ProofFile.Inst Cells)) (k : Coins A.B) :
    ∃ l, chainSteps A.B (A.B.rowsOf 0) (k.look 0) v [blk] hs = .ok l := by
  have hB := k5_bookFits_at_maker h hg hA ha (keyOf := keyOfK3)
  simp only [bookFits, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hB
  obtain ⟨⟨b1, b2⟩, b3⟩ := hB
  have hpl : blk.place = (seatOf keyOfK3 Zp A.G cF g a).place := Dc.place
  have hcut := half_cut (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) id
    (seatOf keyOfK3 Zp A.G cF g a)
  have hn : (k5Half (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) id
      (seatOf keyOfK3 Zp A.G cF g a)).parts.length =
      (shapes (seatOf keyOfK3 Zp A.G cF g a).P.x).length := by
    have e := congrArg List.length hcut
    rw [List.length_map] at e
    rw [e]
    exact List.length_map _
  have hk : blk.place.kind = .K5 := by rw [hpl]; rfl
  have hc : (k5Half (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) id
      (seatOf keyOfK3 Zp A.G cF g a)).parts.map (·.moves.length) = partsCut blk := by
    rw [hcut, k5_partsCut blk (parAt Zp g a) hk Dc.rounds]
    rfl
  obtain ⟨c, hc'⟩ := (lends5_iff (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) A.B id
    (seatOf keyOfK3 Zp A.G cF g a)).2 (k5_lends_paid_fill h hg hA a ha) k
  rw [← hpl] at b1 b2 b3 hc'
  rw [← hn] at b2 b3
  rw [← hcut] at b1
  exact ⟨_, chainSteps_side A.B (A.B.rowsOf 0) (k.look 0) v blk hs _ hf
    (by rw [Dc.oracles, Dc.rounds, List.length_map]) (rounds_of_cut hc) b1 b2 b3 c hc'⟩

/-- IT IS NOT THE HONEST PROVER: TEN OF THE ELEVEN KINDS SEND NOTHING. **AT A FILLING WHOSE ONE LOT
IS K5's, `ready` RETURNS AT THE HEAD's DESCRIPTION AND THE MAKER's BOOK AND PROVER**, at every index
in range, every request with a trace, every rc and every run's coins. CONDITIONAL: h; hL, hS, h2:
the filling's three lists; hA; hi; ht. It says nothing on whether a part plays. -/
theorem ready_at_k5Lot (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {W₀ Rc X₀ X : Type}
    {P : OnlineProverParts W₀ Rc Cells X₀ X} {A : OnlineProverWithDescription W₀ Rc Cells X₀ X}
    (hL : P.lots = [k5LotK id keyOfK3]) (hS : ∀ Z' G', P.shared Z' G' = [])
    (h2 : ∀ Z' G', P.second Z' G' = [])
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) {w₀ : W₀} {x : ProofFile.Inst} {tr : Cells}
    (hi : P.inRange w₀ = true) (ht : P.trace Zp w₀ x = some tr) (rc : Rc) (k : Coins A.B) :
    ∃ R, ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.B A.H w₀ rc x k = .ok R := by
  obtain ⟨e1, eG, e3, eT, -, eI, -, eF1, eSh, eSe, -, -⟩ := atPure_ok hA
  have eZ : A.Z = Zp := Except.ok.inj (e1.symm.trans h.laid.pub)
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF := Except.ok.inj (e3.symm.trans h.laid.value)
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some A.G := by
    rw [← eZ]
    exact eG
  obtain ⟨hw, s1, s2, s3, hd⟩ := atPure_tests hA
  rw [eF] at hw s1 s2 s3
  have hp : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).placesOk = true :=
    Johnson.RunOne.Sound.placesOk_of_planOk _ h.laid.planOk
  obtain ⟨sh1, sh2, sh3⟩ := planOk_all h.laid.planOk
  have eH1 : A.H.first = (k5LotK id keyOfK3).halves Zp A.G := by
    rw [eF1, hL, eZ]
    show ([k5LotK id keyOfK3].flatMap fun L => L.halves Zp A.G) = _
    rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have eH2 : A.H.shared = [] := eSh.trans (hS _ _)
  have eH3 : A.H.second = [] := eSe.trans (h2 _ _)
  have t1 : twice A.H.first = [] := by
    rw [eH1]
    exact k5LotK_no_twice id keyOfK3 Zp A.G
  have hT : readyTests (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.B A.H w₀ = .ok () := by
    have i1 : A.H.inRange w₀ = true := by
      rw [eI]
      exact hi
    unfold readyTests
    rw [List.isEmpty_iff.1 s1, List.isEmpty_iff.1 s2, List.isEmpty_iff.1 s3, t1, eH2, eH3, hp,
      hd, i1, hw]
    rfl
  have hn : ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.map (·.place)).Nodup :=
    (List.nodup_append.1 (List.nodup_append.1 (orderOf_nodup hp)).1).1
  refine ready_of_parts hT (tr := tr) (by rw [eT, eZ]; exact ht) ?_ ?_ ?_
  · refine chainSteps_of_members _ _ _ _ _ _ fun b hb => ?_
    cases hf : A.H.first.find? fun q => q.place == b.place with
    | none => exact chainSteps_bare _ _ _ _ _ (shaped_parts (sh1 b hb).2).1 hf
    | some q =>
      have hq : q ∈ (k5LotK id keyOfK3).halves Zp A.G := eH1 ▸ List.mem_of_find?_eq_some hf
      have hqp : q.place = b.place := by simpa using List.find?_some hf
      obtain ⟨j, hj, ej⟩ := k5Lot_place_at_head h hG id keyOfK3 q hq
      obtain ⟨blk, a, hm, Pl, Dc⟩ := k5_member h hj
      have hbm : blk ∈ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder := List.mem_of_getElem? hm
      have hbp : blk.place = placeOf j := Dc.place
      obtain rfl : b = blk := List.inj_on_of_nodup_map hn hb hbm (by rw [← hqp, ej, hbp])
      have hf' : (A.H.first.find? fun q => q.place == b.place) =
          some (k5Half id (seatOf keyOfK3 Zp A.G cF j a)) := by
        rw [eH1, hbp]
        exact k5LotK_find_K3 h hj hG id Pl.plan
      exact k5_member_steps h hj hA Pl.plan Dc hf' _ k
  · refine chainSteps_of_members _ _ _ _ _ _ fun b hb => ?_
    refine chainSteps_bare _ _ _ _ _ (shaped_parts (sh2 b hb).2).1 ?_
    rw [eH2]
    rfl
  · refine chainSteps_of_members _ _ _ _ _ _ fun b hb => ?_
    refine chainSteps_bare _ _ _ _ _ (shaped_parts (sh3 b hb).2).1 ?_
    rw [eH3]
    rfl

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5Lot_place_at_head
#print axioms ProofFile.Honest.K5.k5_member_steps
#print axioms ProofFile.Honest.K5.ready_at_k5Lot
