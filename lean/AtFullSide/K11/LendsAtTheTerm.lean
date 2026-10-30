-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K11/LendsAtTheTerm.lean: the proofs of K11Lends and K11SimulatorOwed, two statements of
E2E/K11AtTheTerm.lean, on the kind K11, the merge at the output head.

  merge_names, merge_cut     the names of the kind's rounds, and how the book's maker cuts them:
                             one round, then lk + 3
  merge_plain_names          no round of the kind is named "SEND seed" or "FOLD epsilon"
  merge_parts                the kind's side is cut the same way
  k11_book_at_member         at a member of the kind the maker's book has that cut, and has no row
                             and no entry beyond the side's two parts
  k11_unspent_at             no entry of the book spends a coin of the kind's row
  k11_side_is                every side of the kind at the maker's prover is the kind's side
  k11_place_is               the kind's side stands at the library's place for the kind
  k11_lent_at                at the maker's book the kind's row is lent, at every run's coins
  k11_pays                   the kind pays, at any filling with no other side of the kind
  k11Lends                   the first statement
  k11SimulatorOwed           the second statement; k11SimulatorOwedBase at the base prover
  filter_firstOf, k11_filter_at, k11_split, k11_filter_base
                             the sides of the kind, as a list, are the kind's side, once
  stopAt_none, k11_no_stop   the kind's row has no stop
  k11Lends_at_description    the first statement at the description's first chain
  k11_stands                 a block stands at the kind's place, and the search there finds the
                             kind's side
  k11_one_side, k11_lot_apart   the base prover has one side of the kind; the lot has one
  k11_seat, k11_onFromS, k11_bud, k11_onFromS_laid, k11_bud_laid, k11_onFromS_base
                             the rule's forms of the seat, of On and of bud at this row

Limits. Those of the two statements. The library's head and the maker's return are premises. The
lending rests on the closed fact in LendsWritten.lean of this folder. Nothing here says what a part
sends or that a verifier accepts.
-/
import AtFullSide.K11.AtTheTerm
import AtFullSide.K11.LotsAnswerAtTheBook
import Johnson.Desc.ProofFile.Honest.Law.Rule.Lends
import Johnson.Desc.ProofFile.Honest.Thread.OnSaid
import Johnson.Desc.ProofFile.Honest.Small.CutOfBook
import Johnson.Desc.ProofFile.Honest.Small.StepsOfBook
import Johnson.Desc.ProofFile.Honest.K5.Law.BookFits5
import Johnson.Desc.ProofFile.Honest.K11.Plays.Accepted
import Johnson.Desc.ProofFile.Honest.K11.Plays.Proofs
import Johnson.RunOne.Sound.KeyListsAtFK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K11
open VerifiableInference.Desc (Block Chain Place KindName)
open OnBytes.Maker (WholeD)
open OnBytes.Model (WsClaim)
open OnBytes.HonestTrace (Sz)
open P5J (AtMgA TS)
open ProofFile (SecondHashFunctionArgument)
open ProofFile.Honest
open ProofFile.Honest.K11
open ProofFile.Honest.FirstThread
open ProofFile.Honest.SumLaw (lift_moves_count)
open AtPublicFiles.AtFiles.HonestTerm.K11Term
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind mergeEntries)
open Johnson.Desc.First.ForkMerge.Exchange (headMergeAtFull placeOfLot)

/-! ## 1 The cut of the kind's rounds -/

/-- The names of the kind's rounds: the batching round, then a masked sumcheck. -/
theorem merge_names (lk work : Nat) :
    ((mergeEntries lk 1 work).map fun e => ({ entry := e } : Fmt.DeclaredRound)).map
        (·.entry.name) =
      ("BAT-sigma" :: []) ++ (("PSC epsilon" :: (((headMergeShape lk).vs.map fun _ => "PSC round") ++
        ["PSC Y", "PSC values"])) ++ []) := by
  simp [mergeEntries, headMergeShape, OnBytes.Model.RoundName.name, List.map_replicate]

/-- At the kind K11 the cut is the list of units. -/
theorem cutOfNames_K11 (ns : List String) :
    cutOfNames KindName.K11 ns = unitsOf ns.length ns := by
  unfold cutOfNames
  cases unitsOf ns.length ns with
  | nil => rfl
  | cons a rest => rfl

/-- A batching round and one masked sumcheck make two units. -/
theorem units_two (u : List String) (K : Nat)
    (hu : unitLen ("PSC epsilon" :: u) = u.length + 1) :
    unitsOf (K + 2) (("BAT-sigma" :: []) ++ (("PSC epsilon" :: u) ++ [])) =
      [1, u.length + 1] := by
  have h1 : unitLen (("BAT-sigma" :: []) ++ (("PSC epsilon" :: u) ++ [])) =
      ("BAT-sigma" :: ([] : List String)).length := by
    simp [unitLen]
  have h2 : unitLen (("PSC epsilon" :: u) ++ []) = ("PSC epsilon" :: u).length := by
    rw [List.append_nil, hu]
    rfl
  rw [ProofFile.Honest.K5.units_cons "BAT-sigma" [] _ (K + 1) h1,
    ProofFile.Honest.K5.units_cons "PSC epsilon" u [] K h2]
  cases K <;> rfl

/-- **The book's maker cuts the kind's rounds into one and lk + 3.** -/
theorem merge_cut (lk work : Nat) :
    cutOfNames KindName.K11
        (((mergeEntries lk 1 work).map fun e => ({ entry := e } : Fmt.DeclaredRound)).map
          (·.entry.name)) =
      [1, lk + 3] := by
  have hs : (headMergeShape lk).vs.length = lk := by simp [headMergeShape]
  have hL : (((headMergeShape lk).vs.map fun _ => "PSC round") ++
      ["PSC Y", "PSC values"]).length = lk + 2 := by
    simp [headMergeShape]
  have hu : unitLen ("PSC epsilon" :: (((headMergeShape lk).vs.map fun _ => "PSC round") ++
      ["PSC Y", "PSC values"])) =
      (((headMergeShape lk).vs.map fun _ => "PSC round") ++ ["PSC Y", "PSC values"]).length + 1 := by
    rw [hL]
    exact (ProofFile.Honest.K5.unitLen_sum _ []).trans (by rw [hs])
  have hn : (("BAT-sigma" :: []) ++ (("PSC epsilon" ::
      (((headMergeShape lk).vs.map fun _ => "PSC round") ++ ["PSC Y", "PSC values"])) ++
        [])).length = lk + 2 + 2 := by
    simp [headMergeShape]
  rw [merge_names, cutOfNames_K11, hn]
  exact (units_two _ (lk + 2) hu).trans (congrArg (fun n => [1, n + 1]) hL)

/-- No round of the kind is named "SEND seed" or "FOLD epsilon". -/
theorem merge_plain_names (lk work : Nat) :
    ∀ r ∈ (mergeEntries lk 1 work).map (fun e => ({ entry := e } : Fmt.DeclaredRound)),
      r.entry.name ≠ "SEND seed" ∧ r.entry.name ≠ "FOLD epsilon" := by
  intro r hr
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hr
  simp only [mergeEntries, List.mem_cons, List.mem_append, List.mem_replicate, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl | ⟨_, rfl⟩ | rfl | rfl <;> simp [OnBytes.Model.RoundName.name]

/-- The kind's side has two parts, of one round and of lk + 3. -/
theorem merge_parts {W₀ Rc Xi Tr X : Type} (P : HeadMergeP)
    (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights) :
    (headMergeHalf (Rc := Rc) (Tr := Tr) (X := X) claims weights P).parts.map
        (·.moves.length) =
      [1, P.lay.lk + 3] := by
  have hmv : (headMergeSum (Rc := Rc) (Tr := Tr) (X := X) P claims weights).moves.length =
      P.lay.lk + 3 := by
    show ((sumPart (V := Unit) _ _ (headMergeJob P.lay)).lift _ _ _ _).moves.length = _
    rw [lift_moves_count]
    show (List.replicate P.lay.lk _).length + 3 = _
    rw [List.length_replicate]
  show [1, (headMergeSum (Rc := Rc) (Tr := Tr) (X := X) P claims weights).moves.length] = _
  rw [hmv]

/-! ## 2 The maker's book at a member of the kind -/

variable {W₀ Rc Tr X₀ X : Type} {Pf : OnlineProverParts W₀ Rc Tr X₀ X} {weights : W₀ → Weights}
  {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase}

/-- **At a member of the kind the maker's book has the kind's cut, and no row and no entry beyond
two parts.** The filling is any at which the maker returns. -/
theorem k11_book_at_member (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL Pf = .ok A) {b : Block TS ProofFile.Cl}
    (hb : b ∈ cF.blocksInOrder) (hk : b.place.kind = KindName.K11) {lk work : Nat}
    (hr : b.rounds = (mergeEntries lk 1 work).map fun e => ({ entry := e } : Fmt.DeclaredRound)) :
    A.B.cuts.lookup b.place = some [1, lk + 3] ∧
      (A.B.rowsOf 0).any (fun q => q.1.place == b.place && decide (2 ≤ q.1.part)) = false ∧
      A.B.ahead.any (fun e => e.spender.place == b.place && decide (2 ≤ e.spender.part)) =
        false := by
  obtain ⟨B, -, hW, -, -, hall⟩ := AtFullSide.K14.makers_book_one h
  obtain ⟨eB, -⟩ := hall _ _ _ _ _ Pf A hA
  rw [eB]
  have hp : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).placesOk = true :=
    Johnson.RunOne.Sound.placesOk_of_planOk _ h.laid.planOk
  have hbF : b ∈ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder := hb
  have hcut : partsCut b = [1, lk + 3] := by
    unfold partsCut
    rw [hk, hr]
    exact merge_cut lk work
  have hne : b.rounds ≠ [] := by
    intro e
    have hl := congrArg List.length (hr.symm.trans e)
    rw [List.length_map, mergeEntries_length] at hl
    simp at hl
  have hplain : ∀ q ∈ b.rounds,
      q.entry.name ≠ "SEND seed" ∧ q.entry.name ≠ "FOLD epsilon" := by
    intro q hq
    rw [hr] at hq
    exact merge_plain_names lk work q hq
  have hc := bookWhole_cut_first hW hp hbF hne
  obtain ⟨c2, c3⟩ := bookWhole_tests_at hW hp hbF (fun q hq => (hplain q hq).1)
    (fun q hq => (hplain q hq).2) (n := 2)
    (Nat.le_of_eq (congrArg List.length hcut))
  exact ⟨hc.trans (congrArg some hcut), c2, c3⟩

/-- No entry of the book of a return, at any filling, lets a part spend a coin of a part of the
kind's row. -/
theorem k11_unspent_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL Pf = .ok A) {Q : HeadMergeP}
    (hp : headMergePlace Q = k11At) (j : Nat) (q : Addr) :
    A.B.spentBy ⟨headMergePlace Q, j⟩ q = [] := by
  have eA := (AtFullSide.K14.makers_ahead_at_atPure h hA).1
  unfold ProverCoinCounts.spentBy
  rw [List.filter_eq_nil_iff]
  intro e he hb
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  obtain ⟨⟨ho, -⟩, hon⟩ := hb
  have ht : ownsNoSpent e = true := List.all_eq_true.1 k11_owns_no_spent_run e (eA ▸ he)
  have hpl : e.owner.place = k11At := by
    rw [ho]
    exact hp
  simp [ownsNoSpent, hon, hpl] at ht

/-! ## 3 The kind's side at a filling -/

/-- The kind's side, at a reader of the index. -/
abbrev k11Side {W₀ Rc Tr X : Type} (weights : W₀ → Weights) (Zp : ProofFile.Pub) (G : ProofFile.Ground) :
    Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X :=
  headMergeHalf (headClaimsByPlace Zp G) weights (_root_.K11.parOf Zp G)

/-- Every lot of the filling has no side of the kind, or the kind's lot's sides. -/
abbrev K11Alone (Pf : OnlineProverParts W₀ Rc Tr X₀ X) (weights : W₀ → Weights) (A : OnlineProverWithDescription W₀ Rc Tr X₀ X) :
    Prop :=
  ∀ M ∈ Pf.lots, (∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ KindName.K11) ∨
    M.halves A.Z A.G = (headMergeLot headClaimsByPlace weights).halves A.Z A.G

/-- **Every side of the kind at the maker's prover is the kind's side.** -/
theorem k11_side_is (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL Pf = .ok A)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hho : K11Alone Pf weights A) {g : Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X}
    (hg : g ∈ A.H.first) (hk : g.place.kind = KindName.K11) : g = k11Side weights Zp Bs.G₀ := by
  obtain ⟨e1, eG, -, -, -, -, -, eF, -⟩ := atPure_ok hA
  have eZ : A.Z = Zp := Except.ok.inj (e1.symm.trans h.laid.pub)
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some A.G := by
    rw [← eZ]
    exact eG
  have eG' : A.G = Bs.G₀ := Option.some.inj (hG.symm.trans (IM.base_made hB).2.2.1)
  rw [eF] at hg
  obtain ⟨M, hMl, hgM⟩ := List.mem_flatMap.1 hg
  have hgM' : g ∈ M.halves A.Z A.G := hgM
  rcases hho M hMl with hn | he
  · exact absurd hk (hn g hgM')
  · rw [he, eZ, eG'] at hgM'
    exact List.mem_singleton.1 hgM'

/-- The kind's side stands at the library's place for the kind. -/
theorem k11_place_is (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    headMergePlace (_root_.K11.parOf Zp Bs.G₀) = IM.k11Place := by
  obtain ⟨Bs', _, _, hB', _, _, _, _, _, hl⟩ := headMergeAtFull Z D r Zp Np cF x h
  obtain rfl : Bs' = Bs := Except.ok.inj (hB'.symm.trans hB)
  exact (headMergePlaceIs _).trans (placeOfLot Zp _ hl)

/-- **At the maker's book the kind's row is lent, at every run's coins.** -/
theorem k11_lent_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL Pf = .ok A)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {a : Place}
    (ha : a = IM.k11Place) (k : Coins A.B) :
    ∃ c, lendRow A.B (A.B.rowsOf 0) (k.look 0) a
      (k11Side (Rc := Rc) (Tr := Tr) (X := X) weights Zp Bs.G₀).parts 0 = .ok c := by
  subst ha
  obtain ⟨B, -, hW, -, -, hall⟩ := AtFullSide.K14.makers_book_one h
  obtain ⟨eB, -⟩ := hall _ _ _ _ _ Pf A hA
  have hl : ProofFile.Honest.K11.k11Lends A.B 0 IM.k11Place (_root_.K11.parOf Zp Bs.G₀) = true := by
    rw [eB]
    exact k11Lends_at_book h hB hW
  exact (lentIff A.B W₀ Rc ProofFile.Inst Tr X 0 IM.k11Place (_root_.K11.parOf Zp Bs.G₀)
    (headClaimsByPlace Zp Bs.G₀) weights k).2 hl

/-- **The kind pays at any filling at which the maker returns and no lot but the kind's lays a side
of the kind.** -/
theorem k11_pays (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL Pf = .ok A) (hho : K11Alone Pf weights A) :
    KindPays A.B 0 cF.blocksInOrder A.H.first KindName.K11 := by
  obtain ⟨Bs, name, hB, hm⟩ := headMergeMemberAtFull Z D r Zp Np cF x h (places_nodup h)
  intro g hg hk
  obtain rfl := k11_side_is h hA hB hho hg hk
  have hpl := k11_place_is h hB
  refine sidePays_of_tests A.B 0 cF.blocksInOrder _ fun b hb hbp => ?_
  have hmem := List.mem_of_find?_eq_some hm
  have eb : b = IM.seatedAs ProofFile.sameReply (headClaimMergeKind (_root_.K11.parOf Zp Bs.G₀)) name
      (headMergePlace (_root_.K11.parOf Zp Bs.G₀)) :=
    List.inj_on_of_nodup_map (places_nodup h) hb hmem hbp
  have hr : b.rounds = (mergeEntries (_root_.K11.parOf Zp Bs.G₀).lay.lk 1
      (_root_.K11.parOf Zp Bs.G₀).work).map fun e => ({ entry := e } : Fmt.DeclaredRound) := by
    subst eb
    rfl
  have ho : b.oracles.length = (_root_.K11.parOf Zp Bs.G₀).lay.lk + 4 := by
    subst eb
    show (List.replicate ((_root_.K11.parOf Zp Bs.G₀).lay.lk + 4) _).length = _
    rw [List.length_replicate]
  have hlen : b.rounds.length = (_root_.K11.parOf Zp Bs.G₀).lay.lk + 4 := by
    rw [hr, List.length_map, mergeEntries_length]
  have hbk : b.place = IM.k11Place := hbp.trans hpl
  obtain ⟨c1, c2, c3⟩ := k11_book_at_member h hA hb (congrArg Place.kind hbk) hr
  obtain ⟨c, hc⟩ := k11_lent_at (Rc := Rc) (Tr := Tr) (X := X) (weights := weights) h hA hB hbk
    (default : ProofFile.Honest.Coins A.B)
  exact ⟨ho.trans hlen.symm,
    (half_rounds (_root_.K11.parOf Zp Bs.G₀) (headClaimsByPlace Zp Bs.G₀)
      weights).trans hlen.symm,
    c1.trans (congrArg some (merge_parts (_root_.K11.parOf Zp Bs.G₀) (headClaimsByPlace Zp Bs.G₀)
      weights).symm), c2, c3, default, c, hc⟩

/-! ## 4 The two statements -/

/-- At the base prover no lot but the kind's lays a side of the kind. -/
theorem k11_alone_base {W₀ : Type} {I : WiderIn W₀} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (hM : baseMaker I Z = .ok A) :
    K11Alone (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref openHonest) (I.weights Zp) A := by
  obtain ⟨e1, -⟩ := atPure_ok hM
  have eZ : A.Z = Zp := Except.ok.inj (e1.symm.trans h.laid.pub)
  subst eZ
  exact k11_ho I OnBytes.secondHashFunction Sz.ref openHonest A.Z A.G

/-- **The book lends the kind's side.** -/
theorem k11Lends : K11Lends :=
  fun _ _ _ _ _ _ _ _ _ _ hM h => k11_pays h hM (k11_alone_base h hM)

/-- **The simulator of the kind K11, at any filling that lays the kind's lot and no other side of the
kind.** -/
theorem k11SimulatorOwed : K11SimulatorOwed := by
  intro W₀ Rc Tr X₀ X Pf weights Z D r Zp Np cF x A Bs hA h hB hex hho
  have hpl := k11_place_is h hB
  have found := (halfAtAnyFillHead Z D r Zp Np cF x h W₀ Rc Tr X₀ X Pf A Bs headClaimsByPlace
    weights hB hA hex hho).2.2
  unfold K11OwedAt
  refine ⟨?_, ?_, ?_⟩
  · show (A.H.first.find? fun g => g.place == headMergePlace (_root_.K11.parOf Zp Bs.G₀)) =
      some (k11Side weights Zp Bs.G₀)
    rw [hpl]
    exact found
  · intro fs earlier σ hσ
    exact headMergeGoodAtFull W₀ Rc ProofFile.Inst Tr X Z D r Zp Np cF x Bs fs σ .own A.B _ 0 0 _
      (headClaimsByPlace Zp Bs.G₀) weights h (places_nodup h) hB hσ
      fun j q => k11_unspent_at h hA hpl j q
  · intro k mid run st called hcalled σ hσ u hu
    refine ⟨True.intro, fun hcu => ?_⟩
    obtain ⟨m, hm⟩ := hcalled _ hcu
    obtain ⟨c, hc⟩ := k11_lent_at (Rc := Rc) (Tr := Tr) (X := X) (weights := weights) h hA hB
      (a := (k11Row (Rc := Rc) (Tr := Tr) (X := X) weights Zp Bs.G₀).place) hpl k
    have hσ' : ((cF.blocksInOrder.find? fun b =>
        b.place == (k11Row (Rc := Rc) (Tr := Tr) (X := X) weights Zp Bs.G₀).place).map fun b =>
        ({ block := b, row := (k11Row (Rc := Rc) (Tr := Tr) (X := X) weights Zp Bs.G₀).row
           fall := fallOf ([] : List (Fall TS))
             (k11Row (Rc := Rc) (Tr := Tr) (X := X) weights Zp Bs.G₀).place } :
          Side TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst)) =
        some σ := hσ
    obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.1 hσ'
    have hu' : u ∈ membersOf (k11Row (Rc := Rc) (Tr := Tr) (X := X) weights Zp Bs.G₀).row 0
        (b.rounds.zip b.oracles) := hu
    obtain ⟨c', hc'⟩ := row_lent (k := k) (ch := 0)
      (k11Row (Rc := Rc) (Tr := Tr) (X := X) weights Zp Bs.G₀).row 0 _ c hc u hu'
    have e : carriedAt A.B k 0
        ⟨(k11Row (Rc := Rc) (Tr := Tr) (X := X) weights Zp Bs.G₀).place, u.number⟩ u.part =
        .ok c'.2.2 := by
      unfold carriedAt
      rw [hc']
      rfl
    exact ⟨c'.2.2, m, e, hm, True.intro⟩

/-- **The simulator at the base prover.** -/
theorem k11SimulatorOwedBase : K11SimulatorOwedBase := by
  intro W₀ I Z D r Zp Np cF x A Bs hM h hB
  obtain ⟨e1, -⟩ := atPure_ok hM
  have eZ : A.Z = Zp := Except.ok.inj (e1.symm.trans h.laid.pub)
  subst eZ
  exact k11SimulatorOwed _ _ _ _ _ _ (I.weights A.Z) Z D r A.Z Np cF x A Bs hM h hB
    (k11_hex I OnBytes.secondHashFunction Sz.ref openHonest A.Z A.G)
    (k11_ho I OnBytes.secondHashFunction Sz.ref openHonest A.Z A.G)

/-! ## 5 The kind's sides as a list -/

/-- Where every lot in front of L and behind it has no side that the test takes, the sides that the
test takes are L's. -/
theorem filter_firstOf {V W Y : Type} (Zq : ProofFile.Pub) (G : ProofFile.Ground)
    (p : Placed V W Y → Bool) (pre post : List (HLot V W Y)) (L : HLot V W Y)
    (hpre : ∀ M ∈ pre, ∀ y ∈ M.halves Zq G, p y = false)
    (hpost : ∀ M ∈ post, ∀ y ∈ M.halves Zq G, p y = false) :
    (firstOf Zq G (pre ++ L :: post)).filter p = (L.halves Zq G).filter p := by
  have none_of : ∀ l : List (HLot V W Y), (∀ M ∈ l, ∀ y ∈ M.halves Zq G, p y = false) →
      (l.flatMap fun M => M.halves Zq G).filter p = [] := by
    intro l hl
    rw [List.filter_eq_nil_iff]
    intro y hy
    obtain ⟨M, hM, hyM⟩ := List.mem_flatMap.1 hy
    simp [hl M hM y hyM]
  show ((pre ++ L :: post).flatMap fun M => M.halves Zq G).filter p = _
  rw [List.flatMap_append, List.flatMap_cons, List.filter_append, List.filter_append,
    none_of pre hpre, none_of post hpost]
  simp

/-- **At a filling whose lots are some lots with no side of the kind, then the kind's lot once, then
some more with none, the sides of the kind at the maker's prover are just the kind's side.** -/
theorem k11_filter_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL Pf = .ok A)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    {pre post : List (HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X)}
    {L : HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X}
    (hl : Pf.lots = pre ++ L :: post)
    (hL : L.halves A.Z A.G = (headMergeLot headClaimsByPlace weights).halves A.Z A.G)
    (hpre : ∀ M ∈ pre, ∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ KindName.K11)
    (hpost : ∀ M ∈ post, ∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ KindName.K11) :
    (A.H.first.filter fun g => g.place.kind == KindName.K11) = [k11Side weights Zp Bs.G₀] := by
  obtain ⟨e1, eG, -, -, -, -, -, eF, -⟩ := atPure_ok hA
  have eZ : A.Z = Zp := Except.ok.inj (e1.symm.trans h.laid.pub)
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some A.G := by
    rw [← eZ]
    exact eG
  have eG' : A.G = Bs.G₀ := Option.some.inj (hG.symm.trans (IM.base_made hB).2.2.1)
  have off : ∀ (l : List (HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X)),
      (∀ M ∈ l, ∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ KindName.K11) →
      ∀ M ∈ l, ∀ y ∈ M.halves A.Z A.G, (y.place.kind == KindName.K11) = false :=
    fun l hn M hM y hy => beq_eq_false_iff_ne.2 (hn M hM y hy)
  rw [eF, hl, filter_firstOf A.Z A.G _ pre post L (off pre hpre) (off post hpost), hL, eZ, eG']
  rfl

/-- **The lots of the base filling: some with no side of the kind, the kind's lot, and some more.** -/
theorem k11_split {W₀ : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : Sz) (O : OnlineProverArguments)
    (Zq : ProofFile.Pub) (G : ProofFile.Ground) :
    ∃ pre post : List (HLot (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit),
      (onlineProverPartsInUse I o S O).lots =
        pre ++ (HLot.byPub I.weights (LongLots.plain o S O).k11) :: post ∧
      (∀ M ∈ pre, ∀ y ∈ M.halves Zq G, y.place.kind ≠ KindName.K11) ∧
      ∀ M ∈ post, ∀ y ∈ M.halves Zq G, y.place.kind ≠ KindName.K11 := by
  have hk : ∀ q ∈ (widerPairs I o S O).take 3 ++ (widerPairs I o S O).drop 4,
      q.2 ≠ KindName.K11 := by
    intro q hq e
    have he : ((widerPairs I o S O).take 3 ++
        (widerPairs I o S O).drop 4).map (·.2) =
        [KindName.K1, KindName.K2, KindName.K7, KindName.K13, KindName.K3, KindName.K4, KindName.K5,
          KindName.K6, KindName.K8] := rfl
    have hm : q.2 ∈ [KindName.K1, KindName.K2, KindName.K7, KindName.K13, KindName.K3, KindName.K4,
        KindName.K5, KindName.K6, KindName.K8] := he ▸ List.mem_map.2 ⟨q, hq, rfl⟩
    rw [e] at hm
    exact absurd hm (by decide)
  refine ⟨((widerPairs I o S O).take 3).map (·.1),
    ((widerPairs I o S O).drop 4).map (·.1) ++
      [closeLotAt I S, proxLotAt I S, wLotAt I o O], rfl, ?_, ?_⟩
  · intro M hM y hy e
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hM
    exact hk q (List.mem_append_left _ hq)
      (((FirstFill.widerKinds I o S O Zq G).all q (List.mem_of_mem_take hq) y hy).symm.trans e)
  · intro M hM y hy e
    rcases List.mem_append.1 hM with h1 | h2
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h1
      exact hk q (List.mem_append_right _ hq)
        (((FirstFill.widerKinds I o S O Zq G).all q (List.mem_of_mem_drop hq) y hy).symm.trans e)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
      rcases h2 with rfl | rfl | rfl
      · exact absurd (e.symm.trans (closeLotAt_kinds I S Zq G y hy)) (by decide)
      · exact absurd (e.symm.trans (proxLotAt_kinds I S Zq G y hy)) (by decide)
      · exact absurd (e.symm.trans (wLot_kind I o O Zq G y hy)) (by decide)

/-- What the kind's lot holds. -/
theorem k11_lot_halves {W₀ : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : Sz) (O : OnlineProverArguments)
    (Zq : ProofFile.Pub) (G : ProofFile.Ground) :
    (HLot.byPub I.weights (LongLots.plain o S O).k11 :
        HLot (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit).halves Zq G =
      (headMergeLot O.claims (I.weights Zq)).halves Zq G :=
  rfl

/-- **The sides of the kind at the base prover, as a list: the kind's side, once.** -/
theorem k11_filter_base {W₀ : Type} {I : WiderIn W₀} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (hM : baseMaker I Z = .ok A)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    (A.H.first.filter fun g => g.place.kind == KindName.K11) =
      [k11Side (I.weights Zp) Zp Bs.G₀] := by
  obtain ⟨e1, -⟩ := atPure_ok hM
  have eZ : A.Z = Zp := Except.ok.inj (e1.symm.trans h.laid.pub)
  subst eZ
  obtain ⟨pre, post, hl, hp, hq⟩ := k11_split I OnBytes.secondHashFunction Sz.ref openHonest A.Z A.G
  exact k11_filter_at (Pf := onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref openHonest)
    (weights := I.weights A.Z) h hM hB hl (k11_lot_halves I OnBytes.secondHashFunction Sz.ref openHonest A.Z A.G)
    hp hq

/-! ## 6 The kind has no stop -/

/-- A part whose two stops say nothing does not stop. -/
theorem stopAt_none {V W Y : Type} (p : Part V W Y) (hb : ∀ a b, p.bad a b = none)
    (hh : ∀ w a b, p.hid w a b = none) (v : Option V) (loc ds : List Fmt.Drawn) :
    p.stopAt v loc ds = none := by
  unfold Part.stopAt
  try dsimp only
  refine List.findSome?_eq_none_iff.2 fun j _ => ?_
  cases v <;> simp [hb, hh]

/-- **The kind's row has no stop**, at every view and every list of challenges. -/
theorem k11_no_stop (weights : W₀ → Weights) (Zq : ProofFile.Pub) (G : ProofFile.Ground)
    (v : Option (Local W₀ Rc ProofFile.Inst Tr)) (loc ds : List Fmt.Drawn) :
    rowStopAt v (k11Row (Rc := Rc) (Tr := Tr) (X := X) weights Zq G).half.parts loc ds = none := by
  have h0 : ∀ l d, (headMergeDraw :
      Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X).stopAt v l d = none :=
    fun l d => stopAt_none _ (fun _ _ => rfl) (fun _ _ _ => rfl) v l d
  have h1 : ∀ l d, (headMergeSum (Rc := Rc) (Tr := Tr) (X := X) (_root_.K11.parOf Zq G)
      (headClaimsByPlace Zq G) weights).stopAt v l d = none :=
    fun l d => stopAt_none _ (fun _ _ => rfl) (fun _ _ _ => rfl) v l d
  show ((headMergeDraw :
      Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X).stopAt v loc _).or
    (((headMergeSum (Rc := Rc) (Tr := Tr) (X := X) (_root_.K11.parOf Zq G)
      (headClaimsByPlace Zq G) weights).stopAt v _ _).or none) = none
  rw [h0, h1]
  rfl

/-! ## 7 Beside the statements -/

/-- **The first statement at the description's own first chain.** -/
theorem k11Lends_at_description {W₀ : Type} {I : WiderIn W₀} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (hM : baseMaker I Z = .ok A) :
    KindPays A.B 0 (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder A.H.first KindName.K11 :=
  k11Lends W₀ I Z D r Zp Np cF x A hM h

/-- **A block of the chain stands at the kind's place, and the search at that place finds the
kind's side by name**: so the statements do not hold for want of a side. -/
theorem k11_stands {W₀ : Type} {I : WiderIn W₀} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (hM : baseMaker I Z = .ok A)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    (∃ b ∈ cF.blocksInOrder, b.place = IM.k11Place) ∧
      (A.H.first.find? fun q => q.place == IM.k11Place) = some (k11Side (I.weights Zp) Zp Bs.G₀) := by
  obtain ⟨Bs', name, hB', hm⟩ := headMergeMemberAtFull Z D r Zp Np cF x h (places_nodup h)
  exact ⟨⟨_, List.mem_of_find?_eq_some hm, k11_place_is h hB'⟩, k11_found h hM hB⟩

/-- **The base prover has one side of the kind.** -/
theorem k11_one_side {W₀ : Type} {I : WiderIn W₀} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (hM : baseMaker I Z = .ok A)
    {g g' : Placed (Input W₀) (Input W₀) Unit} (hg : g ∈ A.H.first)
    (hk : g.place.kind = KindName.K11) (hg' : g' ∈ A.H.first)
    (hk' : g'.place.kind = KindName.K11) : g = g' := by
  obtain ⟨Bs, -, hB, -⟩ := headMergeMemberAtFull Z D r Zp Np cF x h (places_nodup h)
  exact (k11_side_is h hM hB (k11_alone_base h hM) hg hk).trans
    (k11_side_is h hM hB (k11_alone_base h hM) hg' hk').symm

/-- **The rule's form of the seat**: a member of the chain stands at the row's place. -/
theorem k11_seat (weights : W₀ → Weights) (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    cF.blocksInOrder.any (fun b =>
               b.place == (k11Row (Rc := Rc) (Tr := Tr) (X := X) weights Zp Bs.G₀).place) = true := by
  obtain ⟨Bs', name, hB', hm⟩ := headMergeMemberAtFull Z D r Zp Np cF x h (places_nodup h)
  obtain rfl : Bs' = Bs := Except.ok.inj (hB'.symm.trans hB)
  exact List.any_eq_true.2 ⟨_, List.mem_of_find?_eq_some hm, beq_iff_eq.2 rfl⟩

/-- **The rule's form of On**: at every thread, letter and border. On is True at this row. -/
theorem k11_onFromS {Bk : ProverCoinCounts}
    (T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (weights : W₀ → Weights)
    (Zq : ProofFile.Pub) (G : ProofFile.Ground) (b : Nat) (len : Nat → Nat → Nat) :
    OnFromS T Said (k11Lettered weights Zq G Bk) b len :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ => True.intro

/-- **What BudDebts asks of this row holds at all its arguments.** bud is True at this row. -/
theorem k11_bud {Bk : ProverCoinCounts} (weights : W₀ → Weights) (Zq : ProofFile.Pub) (G : ProofFile.Ground) (n : Nat)
    (ds : List Fmt.Drawn) (asks : List (List (List Nat))) :
    (k11Lettered (Rc := Rc) (Tr := Tr) (X := X) weights Zq G Bk).bud n ds asks :=
  True.intro

/-- **The rule's form of On at the row laid on any threads**: On is True at this row. -/
theorem k11_onFromS_laid {Bk : ProverCoinCounts}
    (T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (Tf : Local W₀ Rc ProofFile.Inst Tr →
      Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst)
    (Sd : Local W₀ Rc ProofFile.Inst Tr → Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (bs : List (Block TS ProofFile.Cl)) (weights : W₀ → Weights) (Zq : ProofFile.Pub) (G : ProofFile.Ground)
    (b : Nat) (len : Nat → Nat → Nat) :
    OnFromS T Said ((k11Row weights Zq G).lay Tf Sd bs) b len :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ => True.intro

/-- **What BudDebts asks of the row laid on any threads holds at all its arguments.** -/
theorem k11_bud_laid {Bk : ProverCoinCounts}
    (Tf : Local W₀ Rc ProofFile.Inst Tr →
      Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst)
    (Sd : Local W₀ Rc ProofFile.Inst Tr → Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (bs : List (Block TS ProofFile.Cl)) (weights : W₀ → Weights) (Zq : ProofFile.Pub) (G : ProofFile.Ground)
    (n : Nat) (ds : List Fmt.Drawn) (asks : List (List (List Nat))) :
    ((k11Row weights Zq G).lay Tf Sd bs).bud n ds asks :=
  True.intro

/-- **The rule's form of On at the base thread and its row, at the kind's border.** -/
theorem k11_onFromS_base {W₀ : Type} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (Q : Script A.B (Input W₀) (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok
      VerifiableInference.Desc.Sound.MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → VerifiableInference.Desc.Strs → WtF → Prop)
    (item n₁ n₂ : Nat) (Vd : Input W₀ → Prop) (ν : Nat) (st : Nat → TS → Prop)
    (R : Nat → Option OnBytes.Model.Forest.Heard → Prop)
    (f : KindName → Place → TS → TS → Prop) (w : Input W₀)
    (Said : Nat → Coins A.B → Mid (Input W₀) Unit → Prop)
    (Sd : Input W₀ → Nat → Coins A.B → Mid (Input W₀) Unit → Prop)
    (weights : W₀ → Weights) (G : ProofFile.Ground) (len : Nat → Nat → Nat) :
    OnFromS (baseThread h A Q test carryX item n₁ n₂ Vd ν st R f w) Said
      ((k11Row weights Zp G).lay (baseThread h A Q test carryX item n₁ n₂ Vd ν st R f) Sd cF.blocksInOrder)
      346 len :=
  k11_onFromS_laid _ _ _ _ _ _ _ _ _ _

/-- The kind's lot lays one side, so its places stand apart. -/
theorem k11_lot_apart
    (claims : ProofFile.Pub → ProofFile.Ground → ProofFile.Inst → List Fmt.Drawn → List WsClaim)
    (weights : W₀ → Weights) (Zq : ProofFile.Pub) (G : ProofFile.Ground) :
    (((headMergeLot (Rc := Rc) (Tr := Tr) (X := X) claims weights).halves Zq G).map
      (·.place)).Nodup :=
  List.nodup_singleton _

end AtFullSide.K11

#print axioms AtFullSide.K11.merge_names
#print axioms AtFullSide.K11.cutOfNames_K11
#print axioms AtFullSide.K11.units_two
#print axioms AtFullSide.K11.merge_cut
#print axioms AtFullSide.K11.merge_plain_names
#print axioms AtFullSide.K11.merge_parts
#print axioms AtFullSide.K11.k11_book_at_member
#print axioms AtFullSide.K11.k11_unspent_at
#print axioms AtFullSide.K11.k11_side_is
#print axioms AtFullSide.K11.k11_place_is
#print axioms AtFullSide.K11.k11_lent_at
#print axioms AtFullSide.K11.k11_pays
#print axioms AtFullSide.K11.k11_alone_base
#print axioms AtFullSide.K11.k11Lends
#print axioms AtFullSide.K11.k11SimulatorOwed
#print axioms AtFullSide.K11.k11SimulatorOwedBase
#print axioms AtFullSide.K11.filter_firstOf
#print axioms AtFullSide.K11.k11_filter_at
#print axioms AtFullSide.K11.k11_split
#print axioms AtFullSide.K11.k11_lot_halves
#print axioms AtFullSide.K11.k11_filter_base
#print axioms AtFullSide.K11.stopAt_none
#print axioms AtFullSide.K11.k11_no_stop
#print axioms AtFullSide.K11.k11Lends_at_description
#print axioms AtFullSide.K11.k11_stands
#print axioms AtFullSide.K11.k11_one_side
#print axioms AtFullSide.K11.k11_seat
#print axioms AtFullSide.K11.k11_onFromS
#print axioms AtFullSide.K11.k11_bud
#print axioms AtFullSide.K11.k11_onFromS_laid
#print axioms AtFullSide.K11.k11_bud_laid
#print axioms AtFullSide.K11.k11_onFromS_base
#print axioms AtFullSide.K11.k11_lot_apart
