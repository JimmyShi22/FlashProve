-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/K6GoodHanded.lean: AT THE STATE THAT THE FRAME's FIELD HANDS IN FRONT OF THE OUTPUT
HEAD's SEGMENT's BATCHING (the member number 347) THE INVARIANT `K6GoodAt` OF THE OUTPUT HEAD's OWN ROUNDS
(Honest/K6/GoodLaw/Runs.lean) HOLDS AT THE WRITTEN NUMBERS 1995 AND 2168, WHERE THE LISTED MARKS HAVE BEEN SILENT. A
joining of other houses' lemmas with ours; statements and proofs; no definition; no goal is stated.
  `headWindow_head` that sub-protocol's window has 173 slots at the full size: the lines inside
      `k6Pub_in_scope` (Johnson/Desc/Kinds/Law/K6PubInScope.lean), at `headWindow`
  `k6Good_behind` behind the member number 341's own accepting step from a state reached at 341, at rounds whose words
      are below the prime and whose drawn values fit, where that sub-protocol's first test names no failing clause:
      `good_at_member` (Honest/K6/GoodLaw/AtHead.lean), its premises paid: `k6Left_341` · `canonical_of_rounds`
      (Honest/K9/K6LeftReached.lean) · `good_of_silent` (Honest/K6/GoodSilent.lean) · `good_bare`. hLook stays
  `k6Good_rides` along the verifier's fold over the five members 342 to 346: `P1K8.rel_rides` at
      `five_decide_frontLater` · `k6GoodAt_of_frontLater` (Honest/K6/GoodLaw/Rides/Members.lean)
  **`k6Good_handed`** `P1K8.pair_handed` at 340 and 341 · hLook: the lookups' `back_cEnd_link` and `P1K8.keeps_six` ·
      the ledger's next slot is 1995: `P1K8.clause_at_step`'s second half and `numbers_head` · 173: `headWindow_head`
WHAT IS NOT CLAIMED. That any walk returns. ARGUED, STATED IN NO THEOREM:
AT A FILLING WITH NO SIDE OF THE CLOSING (K10), AS `widerFillAt` (`k10_ten`, Honest/K10/AtFill.lean), NO STEP IS TAKEN
BEHIND NUMBER 12; THE PREMISES HERE STAND AT 347: AT SUCH A FILLING THE THEOREM SPEAKS OF NOTHING. At the shipped filling
(onlineFilling), which has the closings, nothing here shows the premises met. (The statement stands in the walk's words: the
link from the frame's field to these premises is the smallness test's house's; it is not called here.) Nor that the marks
are silent at any run; how often a mark speaks. NO MEMBER. Where a listed challenge reads 0 the theorem says nothing: that
is the mark's share. MORE MARKS ARE ASKED THAN ARE SPENT: of the lookups' hundred one (at the calls'
site of 24, for the numeral 1995 alone) · of `part4Marks`' two the first · the fit's at the members 340 and 341. IT STANDS
OVER MANY FILES OF OTHER HOUSES THAT ARE NO PART OF THE SEALED LIBRARY (laws.11): Honest/K6/ (GoodLaw/ · GoodSilent.lean
· GoodMark.lean · K6Marks.lean) · Johnson/P1K8R/ · the lookups' Honest/K3/ · the frame's Honest/Law/
(`mark_silent` · `marksQuiet`), Honest/Thread/ and Honest/ itself (`walk`), and all that these import. `k6Good_handed`
stands under set_option maxHeartbeats 1000000. `k6Good_handed` is called by Honest/K9/GoodHeadHandedMarks.lean alone;
the three others here alone. At the full size and the format's second hash function alone, as h. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.K6LeftReached
import Johnson.Desc.ProofFile.Honest.K9.HeadNumbers
import Johnson.P1K8R.TwoStepsAtWalk
import Johnson.P1K8R.ClausesAtLinks
import Johnson.P1K8R.KeepsBetween
import Johnson.P1K9R.AreadyClosed
import Johnson.P1K2R.SitsDoor
import Johnson.Desc.Kinds.Law.K6PubInScope
import Johnson.Desc.ProofFile.Honest.K6.K6Marks
import Johnson.Desc.ProofFile.Honest.K6.GoodLaw.Rides.Members

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open VerifiableInference.OnPublicFiles (okRoundsE)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest (Lay Mid Step walk Mark markOf marksQuiet mark_silent drawsFit)
open ProofFile.Honest.K3.Good (k3Marks)
open ProofFile.Honest.K3.Law.AtThr (site_at_all_fifty back_cEnd_link)
open ProofFile.Honest.K6 (part4Marks headParAt headPlace goodK6Says good_of_silent)
open ProofFile.Honest.K6.GoodLaw (K6GoodAt headWindow good_at_member good_bare k6GoodAt_of_frontLater)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {W Y : Type}

/-- **The window of the output head's own rounds has 173 slots at the full size.** -/
theorem headWindow_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    headWindow (Kinds.Head.parOf (P5J.At.X Zp).hS (Kinds.Head.Law.workOf (P5J.At.X Zp))) = 173 := by
  have N := Kinds.Head.Law.InScope.numbers_in_scope h.scope h.reads h.pubOne
  unfold ProofFile.Honest.K6.GoodLaw.headWindow ProofFile.Honest.K6.headLt ProofFile.Honest.K6.headLPd Kinds.Norm.lPd
  show 41 + 8 * (P5J.At.X Zp).hS.lt + 4 * OnBytes.Model.clog2 (P5J.At.X Zp).hS.d = 173
  rw [N.lt, N.d]
  decide

/-- **THE INVARIANT BEHIND THE MEMBER's OWN ACCEPTING STEP FROM A STATE REACHED AT 341**, in the step's coin: no
thread. -/
theorem k6Good_behind (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {blk : Block S ProofFile.Cl}
    (hb : cF.blocksInOrder[341]? = some blk)
    (M : Kinds.Head.Law.K6MemberIs (P5J.At.X Zp) 24 ProofFile.sameReply IM.k6Place blk)
    {zp : ProofFile.InstPub} {sk sl : S} {R : List Fmt.RoundView} {d : List Desc.OpenedColumn} {n : ℕ}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 341 (zp, sk)) (k3 : blk.step 0 sk R d = .ok (sl, n))
    (k4 : okRoundsE R = true) (hdf : drawsFit blk.rounds (R.map (·.drawn)) = true)
    (hsay : goodK6Says (Kinds.Head.parOf (P5J.At.X Zp).hS (Kinds.Head.Law.workOf (P5J.At.X Zp))) (R.map (·.drawn)) =
        none)
    (hLook : ∀ gl, sl.lookHeard? = some gl → Kinds.Head.Law.SlotsIn 0
      ((Kinds.Head.seatAt (P5J.At.X Zp).hS (Kinds.Head.Law.readsOf (P5J.At.X Zp))).ledger sk).next gl.cEnd) :
    K6GoodAt (P5J.At.X Zp).hS (Kinds.Head.Law.readsOf (P5J.At.X Zp)) (Kinds.Head.parOf (P5J.At.X Zp).hS
        (Kinds.Head.Law.workOf (P5J.At.X Zp)))
      ((Kinds.Head.seatAt (P5J.At.X Zp).hS (Kinds.Head.Law.readsOf (P5J.At.X Zp))).ledger sk).next
      (((Kinds.Head.seatAt (P5J.At.X Zp).hS (Kinds.Head.Law.readsOf (P5J.At.X Zp))).ledger sk).next +
        headWindow (Kinds.Head.parOf (P5J.At.X Zp).hS (Kinds.Head.Law.workOf (P5J.At.X Zp)))) sl := by
  have hrounds : blk.rounds = (Kinds.Head.parOf (P5J.At.X Zp).hS (Kinds.Head.Law.workOf (P5J.At.X Zp))).rounds :=
      M.rounds.trans rfl
  rw [hrounds] at hdf
  obtain ⟨-, g1, g2⟩ := good_of_silent _ IM.k6Place [] (R.map (·.drawn)) hdf (by
    show (goodK6Says _ (R.map (·.drawn))).isSome = false
    rw [hsay]
    rfl)
  have hnd : (R.map noDigest).map (·.drawn) = (R.map (·.drawn)).map bare := by
    rw [List.map_map, List.map_map]
    rfl
  exact good_at_member M (by decide) (fun _ _ e => P4.same_of_eq e)
    (P5J.flat_ok h.toAtMg blk (List.mem_of_getElem? hb)) k3 (canonical_of_rounds k4) (k6Left_341 h hr)
    (by rw [hnd, (good_bare _ _).1]; exact g1) (by rw [hnd, (good_bare _ _).2]; exact g2) hLook

/-- **THE INVARIANT RIDES THE VERIFIER's FOLD OVER THE FIVE MEMBERS 342 TO 346.** b and e are letters. -/
theorem k6Good_rides (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (hlen : 347 ≤ cF.blocksInOrder.length) {sl s' : S}
    {r₂ r₃ : List Fmt.RoundView} {c₂ c₃ : List Desc.OpenedColumn}
    (hfold : foldBlocks 0 ((cF.blocksInOrder.take 347).drop 342) sl r₂ c₂ = .ok (s', r₃, c₃)) {b e : ℕ}
    (k : K6GoodAt (P5J.At.X Zp).hS (Kinds.Head.Law.readsOf (P5J.At.X Zp)) (Kinds.Head.parOf (P5J.At.X Zp).hS
        (Kinds.Head.Law.workOf (P5J.At.X Zp))) b e sl) :
    K6GoodAt (P5J.At.X Zp).hS (Kinds.Head.Law.readsOf (P5J.At.X Zp)) (Kinds.Head.parOf (P5J.At.X Zp).hS
        (Kinds.Head.Law.workOf (P5J.At.X Zp))) b e s' := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hFL : LinkJoin.FrontLater sl s' :=
    P1K8.rel_rides (R := LinkJoin.FrontLater) (fun s => ⟨rfl, LinkJoin.laterZ_refl s⟩) LinkJoin.frontLater_trans
      cF.blocksInOrder 342 5
      (fun i hi => by
        have hlt : 342 + i < cF.blocksInOrder.length := by omega
        exact ⟨_, List.getElem?_eq_getElem hlt,
          Kinds.Head.Law.Five.five_decide_frontLater h.scope h.reads O (P1K2.flat_planOk O h.laid.planOk)
            (by omega) (by omega) (List.getElem?_eq_getElem hlt)⟩)
      hfold
  exact k6GoodAt_of_frontLater hFL k

set_option maxHeartbeats 1000000 in
/-- **AT THE STATE THAT THE FRAME's FIELD HANDS IN FRONT OF THE HEAD's SEGMENT's BATCHING THE INVARIANT OF THE OUTPUT
HEAD's OWN ROUNDS HOLDS AT THE WRITTEN NUMBERS**, where the listed marks are silent. -/
theorem k6Good_handed (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G₀ G₁ : ProofFile.Ground)
    (hG : G₁.W = (P5J.At.X Zp)) (ms : List Mark)
    (hsub : ∀ mk ∈ k3Marks Zp G₀, mk ∈ ms) (hsubK : ∀ mk ∈ part4Marks Zp G₁, mk ∈ ms)
    {A t : List (Block S ProofFile.Cl)} {b : Block S ProofFile.Cl} (hall : cF.blocksInOrder = A ++ b :: t)
    (hfit : ∀ d ∈ A, (⟨d.place,
      fun _ own => if drawsFit d.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ : Mark) ∈ ms)
    (hA : A.length = 347) (hpos : 0 < b.rounds.length)
    (L : Lay) (hft : L.firstTree = 0) {a₀ z : ProofFile.Honest.ChainProgress S ProofFile.Cl W Y} {zp : ProofFile.InstPub} {s' : S}
    {m₀ : Option (Mid W Y)} {ss : List (Step W Y)} {fr : List Fmt.Drawn}
    (hm : m₀.isSome = true)
    (ha : ProofFile.Honest.ChainProgress.start L cF.blocksInOrder m₀ (some (ProofFile.startS Zp zp)) [] = .ok a₀)
    (hn : fr.length = (A.flatMap (·.rounds)).length) (hq : marksQuiet ms A [] fr = true)
    (hz : walk L ss fr a₀ = .ok z) (hv : z.ver = some s') :
    K6GoodAt (P5J.At.X Zp).hS (Kinds.Head.Law.readsOf (P5J.At.X Zp))
      (Kinds.Head.parOf (P5J.At.X Zp).hS (Kinds.Head.Law.workOf (P5J.At.X Zp))) 1995 2168 s' := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hlen : 347 ≤ cF.blocksInOrder.length := by
    rw [hall, List.length_append]
    omega
  have inA : ∀ {i : ℕ} {d : Block S ProofFile.Cl}, i < 347 → cF.blocksInOrder[i]? = some d → d ∈ A := by
    intro i d hi hd
    rw [hall, List.getElem?_append_left (by omega)] at hd
    exact List.mem_of_getElem? hd
  -- the calls' site and its written numbers
  obtain ⟨pC, pD, hC, hD⟩ := P1K9.bothPlaces_at_head h 24 (by omega)
  obtain ⟨f0, -, hsC, -, spC, -, eC, -⟩ := numbers_head h hC hD
  obtain ⟨s, hs, el, hd, -, -⟩ := site_at_all_fifty h 24 (by omega) false
  obtain ⟨q1, q2⟩ := P1K8.site_pars s hs
  rw [el, hd] at q1
  obtain rfl : s.p = pC := Option.some.inj (q1.symm.trans hC)
  obtain rfl : s.shape = hsC := Option.some.inj (q2.symm.trans spC)
  have hbC : borderOf 24 false = 340 := rfl
  -- the two members, and the walk's two steps
  obtain ⟨blk₁, hb₁⟩ : ∃ blk₁, cF.blocksInOrder[340]? = some blk₁ := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨blk₂, hb₂, M⟩ := P4.k6_member_at_mg h.toAtMg
  obtain ⟨sj, sk, sl, R₁, R₂, d₁, d₂, r₂, r₃, c₂, c₃, f₁, f₂, -, g3, -, hs1, -, k3, k4, hs2, -, hr1, -, hfold⟩ :=
    P1K8.pair_handed cF.blocksInOrder (ProofFile.startS Zp) zp (n := 340) hb₁ hb₂ ms hall hfit (by omega) hpos L hft hm ha hn hq hz hv
  rw [hA] at hfold
  -- the ledger's next slot in front of the head's own rounds is 1995
  obtain ⟨-, G, hG', hGn⟩ := P1K8.clause_at_step h G₀ s hs (by omega) (blk := blk₁) (by
    rw [el, hd, hbC]
    exact hb₁) ms hsub (hfit blk₁ (inA (by omega) hb₁)) g3 hs1
  have hnext : ((Kinds.Head.seatAt (P5J.At.X Zp).hS (Kinds.Head.Law.readsOf (P5J.At.X Zp))).ledger sk).next = 1995 := by
    show (sk.fork?.getD {}).next = 1995
    rw [hG']
    show G.next = 1995
    omega
  -- hLook: the form in which the calls' lookup's key side ended names slots below that next slot
  obtain ⟨F, H, G₂, -, -, eH, eG₂, -, hce⟩ := back_cEnd_link h s hs (by omega) hd blk₁ (by
    rw [el, hbC]
    exact hb₁) 0 sj sk d₁.length R₁ d₁ g3
  have hd2 := ((Sound.step_ok_iff 0 blk₂ sk sl R₂ d₂ d₂.length).1 k3).2.2.2
  obtain ⟨b6, hb6, hk6⟩ := P1K8.keeps_six h.scope h.reads O h.laid.planOk 0 (by omega)
  obtain rfl : blk₂ = b6 := Option.some.inj (hb₂.symm.trans hb6)
  have hLook : ∀ gl, sl.lookHeard? = some gl → Kinds.Head.Law.SlotsIn 0
      ((Kinds.Head.seatAt (P5J.At.X Zp).hS (Kinds.Head.Law.readsOf (P5J.At.X Zp))).ledger sk).next gl.cEnd := by
    intro gl hgl y hy
    obtain rfl : H = gl := Option.some.inj ((hk6 sk _ _ sl hd2 H eH).symm.trans hgl)
    refine ⟨Nat.zero_le _, ?_⟩
    show y.1 < (sk.fork?.getD {}).next
    rw [show sk.fork? = some G₂ from eG₂]
    exact (hce y hy).2
  -- that sub-protocol's first mark is silent; the rounds' drawn values fit
  have hpar : headParAt G₁ = (Kinds.Head.parOf (P5J.At.X Zp).hS (Kinds.Head.Law.workOf (P5J.At.X Zp))) := by
    show Kinds.Head.parOf G₁.W.hS (Kinds.Head.Law.workOf G₁.W) = _
    rw [hG]
  have hp2 : blk₂.place = headPlace 24 4 := by
    obtain ⟨_, _, _, _, hla⟩ := M
    exact IM.alone_place hla
  have hsay : goodK6Says (headParAt G₁) (R₂.map (·.drawn)) = none :=
    mark_silent (hsubK _ List.mem_cons_self) (by
      show (markOf ms (headPlace 24 4) f₂ (R₂.map (·.drawn))).isSome = false
      rw [← hp2, hs2]
      rfl)
  rw [hpar] at hsay
  -- the law at the step; the numbers; the carriage
  have K := k6Good_behind h hb₂ M hr1 k3 k4 (P1K8.fit_at_silent blk₂ (hfit blk₂ (inA (by omega) hb₂)) hs2) hsay hLook
  rw [hnext, headWindow_head h] at K
  exact k6Good_rides h hlen hfold K

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.headWindow_head
#print axioms ProofFile.Honest.K9.k6Good_behind
#print axioms ProofFile.Honest.K9.k6Good_rides
#print axioms ProofFile.Honest.K9.k6Good_handed
