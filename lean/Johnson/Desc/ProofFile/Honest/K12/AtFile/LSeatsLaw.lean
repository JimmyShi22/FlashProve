-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LSeatsLaw.lean: THE SENTENCE `FitsAtEveryReachedRecord`
(LSeatsStatement.lean) IS A THEOREM: under the library's head (`P5J.AtMgA` at `OnBytes.secondHashFunction`), at
every state that the first chain's sub-protocols' steps reach at border 354, `FrontAsksD` at the
record that the way into the closing proximity test returns there gives `FitsAtL` (ClosingData.lean)
at its own plain data. No shape of a state is written, and no run on shapes is made.

  `freshIsNoMember_of_guard`   a clause of the guard that `Good`
                           (Johnson/Desc/K12/Law/FirstOkLaw.lean) does not hold
  `writtenSeat_places`     what a written seat says of the lists
  `fits_of_written_seats`  THE ARGUMENT, no state named: from the closed test `closingSeatsTest`,
                           what the guard has made and found good, a member, and "every part of a
                           tree is the written seat"
  `fits_at_every_raw_record`   the theorem at what the sub-protocols' own steps reach, at every
                               border,
                           under `P5J.AtMg`
  `fits_at_every_reached_record`   THE THEOREM

The argument. The one declared opening names tree 76, so the plain data have one tree, and its
number is 76, counted from the test's first tree, 0; the book is in order from 0 on, so its place is
76. Every seat of the plain data sits in that
tree. By the written list just the messages 185 and 186 do. The fresh table has no main row: it is
186. It is no member: every member is 185. There is a member. Two members would each fill all
2 ^ kk rows and could not lie apart: there is one. The other clauses are read off the two written
seats.

By what. `foldFacts_raw` (Honest/Thread/ReachFacts.lean) with `laid_at_head`, `startB_at_head`,
`sendsB_of_madeRow`; `written354_of_pins` (Johnson/Loose/H2K12/ClosedOfPins354.lean); `made_of`,
`good_of_ok`, `keyAt_of` (FirstOkLaw.lean); `common_of`
(Johnson/Desc/K12/Honest/Shape/TestDoor.lean);
`closeLedgers_get` (OnBytes/Slice/BlkProxEarlierMessagesAndGroups.lean); `closingSeats_written` (LSeatsWritten.lean);
`p12_at_head`, `places_head`, `enterFinish_ok`, `msgs_sorted`, `reach_raw`, `Fmt.listOf_mem`.

Limits.
- `FrontAsksD` is a premise. It is shown at no state here. Of it three fields are spent: door (the
  group; there is a member), came, plain (what the guard makes, and that it finds it good).
- Nothing says that a state is reached at border 354.
- The full size alone; the format's second hash function. A closed line of Lean's kernel lies beneath.
- Nothing on completeness, on soundness or on hiding.
NOT IN FRONT OF A LAW OVER COINS: `fits_at_every_raw_record` and `fits_at_every_reached_record` bear
this label; the rule is at its home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean. Their
ground: "reached", the way in's return and `FrontAsksD` tie the letters s, T and Dp to a run's
coins.
Terms: the head of LShapeTest.lean; Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LSeatsWritten
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LSeatsStatement
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.Desc.K12.Honest.Shape.TestDoor
import Fmt.Rules6Laws
import Johnson.AtFull.Shape.TestNumbersAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open OnBytes (OracleShape TreeShape GroupLayout GroupRow layTrees)
open VerifiableInference.Desc.K12 (P12 T12 enterFinish)
open VerifiableInference.Desc.K12.Door (msgsOfChain)
open VerifiableInference.Desc.K13.Law (LFull)
open H2K.First (Plain Seat1 gpL ok oM kk keyAt_of good_of_ok made_of entered)
open H2K.Sw (Part1P)
open H2K.Member (piLFull)
open ProofFile.Honest.K12 (stA)

local notation "Laid" => VerifiableInference.Desc.K12.Door.Laid

/-- A clause of the guard: the fresh table is no member. -/
theorem freshIsNoMember_of_guard (p : P12) (a : Fmt.M1.Stage) (row : GroupRow) (D : Plain)
    (h : ok (gpL p a row D) = true) :
    D.L.members.contains D.fresh.id = false := by
  unfold ok gpL at h
  dsimp only at h
  rw [List.all_append, Bool.and_eq_true] at h
  obtain ⟨-, ht⟩ := h
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at ht
  obtain ⟨_, _, _, _, _, _, _, _, _, t10, _, _, _, _, _⟩ := ht
  simpa using t10

/-- What a written seat says of the lists. -/
theorem writtenSeat_places {M : List OracleShape} {L : Laid} {o : ℕ} {σ : Seat1}
    (h : writtenSeat M L o = some σ) : L.places[o]? = some (σ.t, σ.part) ∧ σ.num = σ.t := by
  unfold writtenSeat at h
  obtain ⟨sh, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨q, hq, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨tsh, -, h⟩ := Option.map_eq_some_iff.1 h
  subst h
  exact ⟨hq, rfl⟩

/-- **The argument**, no state named. -/
theorem fits_of_written_seats {M : List OracleShape} {L : Laid} {q : P12} {pl : K2.SwitchPlace}
    (hW : closingSeatsTest M L q pl = true) {t : T12} {Lg : GroupLayout} {Dp : Plain}
    (hMade : H2K.First.Made q t (stA q) Lg Dp)
    (hGood : H2K.First.Good q.nums.firstTree (stA q) {} Dp)
    (hNo : Dp.L.members.contains Dp.fresh.id = false) (hSome : 0 < Lg.members.size)
    (hSeat : ∀ o sh num tsh t' p', Part1P Dp.st Dp.book o sh num tsh t' p' →
      writtenSeat M L o = some ⟨o, sh, t', p', tsh, num⟩) :
    ∃ s u Ly, FitsAtL q pl Dp s u Ly := by
  unfold closingSeatsTest at hW
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    decide_eq_true_eq] at hW
  obtain ⟨⟨⟨w1, w2⟩, w3⟩, w4⟩ := hW
  split at w4
  · rename_i s₀ f₀ Ly h185 h186 hLy
    simp only [Bool.and_eq_true, decide_eq_true_eq, seatIsTest_iff] at w4
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨v1, -⟩, -⟩, -⟩, v3⟩, v4⟩, v5⟩, v6⟩, v7⟩, v8⟩, v9⟩, v10⟩, v11⟩ := w4
    unfold closingPlaceTest at v3
    simp only [Bool.and_eq_true, decide_eq_true_eq] at v3
    obtain ⟨⟨⟨⟨⟨⟨p1, p2⟩, p3⟩, p4⟩, p5⟩, p6⟩, p7⟩ := v3
    -- each seat is written
    have sF : writtenSeat M L Dp.fresh.id = some Dp.fresh := hSeat _ _ _ _ _ _ hMade.fresh
    have sM : ∀ i : Fin Dp.mems.length,
        writtenSeat M L (Dp.mems.get i).id = some (Dp.mems.get i) :=
      fun i => hSeat _ _ _ _ _ _ (hMade.mem i).2
    -- a written seat in tree 76 is that of 185 or of 186
    have two : ∀ o σ, writtenSeat M L o = some σ → σ.t = 76 → o = 185 ∨ o = 186 := by
      intro o σ hσ ht
      obtain ⟨hq, -⟩ := writtenSeat_places hσ
      have ho : o < L.places.length := (List.getElem?_eq_some_iff.1 hq).1
      have k := List.all_eq_true.1 w3 o (List.mem_range.2 ho)
      rw [List.getD_eq_getElem?_getD, hq, Option.getD_some] at k
      simp only [Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at k
      rcases k with (k | k) | k
      · exact absurd ht k
      · exact Or.inl k
      · exact Or.inr k
    -- the one tree
    have hk : Dp.ts.map (H2K.First.keyAt q.nums.firstTree Dp.book) = [76] := by
      rw [← hGood.keys, hMade.opens]
      exact w2
    obtain ⟨u, hu, hku⟩ : ∃ u, Dp.ts = [u] ∧ H2K.First.keyAt q.nums.firstTree Dp.book u = 76 := by
      cases hts : Dp.ts with
      | nil =>
        rw [hts] at hk
        cases hk
      | cons u r =>
        rw [hts] at hk
        cases r with
        | nil => exact ⟨u, rfl, by simpa using hk⟩
        | cons _ _ => simp at hk
    have inTs : ∀ z, z ∈ Dp.mems.map (·.t) ++ [Dp.fresh.t] → z = u := by
      intro z hz
      have : z ∈ Dp.ts := by
        rw [hMade.ts]
        exact (Fmt.listOf_mem _ _).2 hz
      rw [hu] at this
      simpa using this
    have fT : Dp.fresh.t = u := inTs _ (List.mem_append_right _ (List.mem_singleton.2 rfl))
    have mT : ∀ i : Fin Dp.mems.length, (Dp.mems.get i).t = u := fun i =>
      inTs _ (List.mem_append_left _ (List.mem_map.2 ⟨_, List.get_mem _ i, rfl⟩))
    have u76 : u = 76 := by
      have a := (keyAt_of (F := q.nums.firstTree) hMade.fresh).1
      rw [fT, hku, (writtenSeat_places sF).2, fT, w1] at a
      exact a.symm
    -- the fresh table is message 186
    have fIs : Dp.fresh = f₀ ∧ Dp.fresh.id = 186 := by
      rcases two _ _ sF (fT.trans u76) with e | e
      · rw [e, h185] at sF
        have e' : s₀ = Dp.fresh := Option.some.inj sF
        rw [e', hGood.fMain] at v1
        exact absurd v1 (Nat.lt_irrefl 0)
      · rw [e, h186] at sF
        exact ⟨(Option.some.inj sF).symm, e⟩
    -- every member is message 185
    have mIs : ∀ i : Fin Dp.mems.length, Dp.mems.get i = s₀ := by
      intro i
      have si := sM i
      rcases two _ _ si ((mT i).trans u76) with e | e
      · rw [e, h185] at si
        exact (Option.some.inj si).symm
      · exfalso
        have hm := (hMade.mem i).1
        rw [e, ← fIs.2, ← hMade.lay] at hm
        have : Dp.L.members.contains Dp.fresh.id = true := by
          rw [Array.contains_iff_mem]
          exact Array.mem_of_getElem? hm
        rw [hNo] at this
        cases this
    -- there is just one member
    have hpos : 0 < 2 ^ kk (stA q) := Nat.pos_of_ne_zero (by positivity)
    have room : ∀ i : Fin Dp.mems.length, oM Dp.L i = 0 := by
      intro i
      have a := hGood.roomM i
      rw [mIs i, v9] at a
      omega
    have hlen : Dp.mems.length = 1 := by
      have h0 : 0 < Dp.mems.length := by
        rw [← hMade.size]
        exact hSome
      by_contra hne
      have h2 : 1 < Dp.mems.length := by omega
      have a := hGood.apartM ⟨0, h0⟩ ⟨1, h2⟩ (by simp)
      rw [room ⟨0, h0⟩, room ⟨1, h2⟩, mIs, mIs, v9] at a
      omega
    have hmems : Dp.mems = [s₀] := by
      obtain ⟨m, hm⟩ := List.length_eq_one_iff.1 hlen
      have a := mIs ⟨0, by omega⟩
      simp only [hm, List.get_eq_getElem, List.getElem_cons_zero] at a
      rw [hm, a]
    have part0 := (hMade.mem ⟨0, by omega⟩).2
    rw [mIs] at part0
    have s0T : s₀.t = u := by
      have a := mT ⟨0, by omega⟩
      rwa [mIs] at a
    refine ⟨s₀, u, Ly, ?_⟩
    exact
      { plan := p1, lay := hLy, two := p2, count := p3, mems := hmems, ts := hu, seat := v4
        fresh := by rw [fIs.1]; exact v5
        tree0 := p4, tree1 := p5, some0 := p6, at0 := s0T, at1 := fT
        rowsF := by rw [fIs.1]; exact v6
        deg := v7, noMask := v8, rows := v9, logRows := p7
        first := room ⟨0, by omega⟩
        depth := by
          rw [← s0T, (keyAt_of (F := q.nums.firstTree) part0).2]
          exact v10
        width := by
          obtain ⟨T, hT, e1, -⟩ := part0.tree
          unfold H2K.First.widthAt
          rw [← s0T, hT, Option.map_some, Option.getD_some, e1]
          exact v11 }
  · cases w4

open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (below)
open VerifiableInference.Desc.K12.Door (seatsCarriedB bookInOrderB msgShapesB)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open ProofFile.Honest.K12 (TestJob FrontAsksD)
open ProofFile.Honest.Sh (doorB common_of)
open Johnson.Prover.Link (batT)
open P5J (AtMgA)

/-- **At every record reached by the sub-protocols' own steps**, at whichever border: the form with
the weaker premises. -/
theorem fits_at_every_raw_record {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    (h' : P5J.AtMg OnBytes.secondHashFunction Z D₀ r Zp Np cF)
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {pl : K2.SwitchPlace}
    (hf : finishAt Zp G = some pl) {b : ℕ} {pI : ProofFile.InstPub} {s : S}
    (hReach : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) b (pI, s)) {T : T12}
    (hEnter : enterFinish s = .ok T) {W X : Type} (J : TestJob W X) (w : W) (fr : Front X)
    (hp : J.p = H2U.p12OfMade Zp.made) (hJ : J.rec₀ w fr = T) {K : OnBytes.Codes} {Dp : Plain}
    (A : FrontAsksD J w fr K Dp) : ∃ s₁ u Ly, FitsAtL J.p pl Dp s₁ u Ly := by
  have eq : J.p = piLFull := hp.trans (Johnson.AtFull.Shape.p12_at_head h')
  obtain ⟨o, -, -, hfail, hT⟩ := VerifiableInference.Desc.K12.Seat.enterFinish_ok s T hEnter
  have hm : s.failed = none := Option.isNone_iff_eq_none.1 hfail
  -- the library's facts at s
  have F := ProofFile.Honest.FirstThread.foldFacts_raw h'
    (fun k (a : ProofFile.InstPub × S) => Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a) (fun a => a)
    (fun _ _ e => e) (P5J.laid_at_head h') (P5J.startB_at_head h')
    (P5J.sendsB_of_madeRow h' (P5J.madeRow_at_head h'))
  have b1 : bookInOrderB 0 s.book s.roots = true := F.bookInOrder b (pI, s) hReach hm
  have b2 : seatsCarriedB LFull s.book = true := F.seatsCarried b (pI, s) hReach hm
  have b3 : msgShapesB (msgsOfChain Zp.made.proof.1) s.st = true :=
    F.msgShapes b (pI, s) hReach hm
  have Wr := H2K12.written354_of_pins h'.scope h'.laid.pub h'.pins.1
    (h'.laid.run ▸ LPFD.Full.laidPOf_of h'.laid.value h'.laid.planOk h'.laid.data h'.laid.asks)
  rw [Wr.sends, OnBytes.Road.K4.msgs_sorted] at b3
  -- the closed line at the finish
  have eF : finishAt Zp G = finishW := by
    unfold finishAt finishW
    rw [places_head h' hG]
  have hW : closingSeatsTest OnBytes.Road.K4.mW LFull piLFull pl = true := by
    have k := closingSeats_written
    rw [← eF, hf] at k
    exact k
  -- the door, the guard
  have hd := A.door
  unfold doorB at hd
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hd
  obtain ⟨⟨⟨hc, -⟩, -⟩, -⟩ := hd
  obtain ⟨G', C⟩ := common_of hc
  obtain ⟨hD, hok, -, -⟩ := A.plain G' C.group
  have hMade := made_of _ _ _ _ _ hD
  have hGood := good_of_ok _ _ _ _ hok
  have hNo := freshIsNoMember_of_guard _ _ _ _ hok
  obtain ⟨j, hj, -⟩ := C.main
  -- the statement and the book of the plain data
  obtain ⟨id, hid⟩ := Option.isSome_iff_exists.1 A.came
  obtain ⟨cu, -, hent⟩ := hMade.ent
  have hmask : (batT (J.rec₀ w fr) G' {}).mask = some id := hid
  unfold entered at hent
  rw [hmask] at hent
  have e3 := Option.some.inj hent
  have eSt : Dp.st = OnBytes.Slice.begun (J.rec₀ w fr).st (J.rec₀ w fr).g G' :=
    (congrArg (·.2.1) e3).symm
  have eBk : Dp.book = s.book := by
    have a : Dp.book = (J.rec₀ w fr).book := (congrArg (·.2.2) e3).symm
    rw [a, hJ, hT]
  have eS : (J.rec₀ w fr).st = s.st := by rw [hJ, hT]
  rw [eq] at hMade hGood ⊢
  refine fits_of_written_seats hW hMade hGood hNo (Nat.lt_of_le_of_lt (Nat.zero_le j) hj)
    fun o' sh num tsh t' p' hP => ?_
  rw [eBk] at hP
  refine writtenSeat_of_part b3 b2 b1 (fun a y hy => ?_) hP
  rw [eSt, eS] at hy
  have hy' : (OnBytes.Slice.closeLedgers s.st G'.members.toList).oracles[a]? = some y := hy
  rw [OnBytes.Slice.ProxRun.closeLedgers_get] at hy'
  obtain ⟨y₀, hy₀, rfl⟩ := Option.map_eq_some_iff.1 hy'
  refine ⟨y₀, hy₀, ?_⟩
  split <;> rfl

/-- **THE THEOREM**: the sentence of LSeatsStatement.lean. -/
theorem fits_at_every_reached_record : FitsAtEveryReachedRecord :=
  fun h _ hG _ hf _ _ hReach _ hEnter _ _ J w fr hp hJ _ _ A =>
    fits_at_every_raw_record h.toAtMg hG hf (reach_raw hReach) hEnter J w fr hp hJ A

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.fits_at_every_raw_record
#print axioms ProofFile.Honest.K12.AtProof.fits_at_every_reached_record
#print axioms ProofFile.Honest.K12.AtProof.freshIsNoMember_of_guard
#print axioms ProofFile.Honest.K12.AtProof.writtenSeat_places
#print axioms ProofFile.Honest.K12.AtProof.fits_of_written_seats
