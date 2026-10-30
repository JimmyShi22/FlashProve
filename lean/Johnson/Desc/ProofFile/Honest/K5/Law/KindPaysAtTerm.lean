-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/KindPaysAtTerm.lean: the kind K5 (an attention segment's own
rounds) pays for its sides at the maker's return at the online filling of E2E/TheHonestProver.lean,
the return from which that file makes its family of online provers (`onlineProverAt`,
`onlineProver`). No definition.

  `k5Half_thru`, `k5LotK_thru`   K5's side and lot read through are K5's side and lot at the new
                              types: they read of their input the trace alone
  `sidePays_k5`                each side of K5's lot pays, at the maker's book, at any filling
  `kindPays_k5_at_term`        **under the library's head, wherever the maker returns A: every side
                              of kind K5 in A's first chain pays**: one call of `kindPays_online`
  `k5_find_at_term`            a search at the place of group j finds K5's side there
  `k5_sender_at_term`          so that this is not met for want of sides: at each of the twelve
                              groups there is a plan, a member of the description's list stands at
                              the group's place, and a search there finds K5's side
  `placeOf_injective`          the twelve places differ
  `k5_side_at_term`            a shorter form of the last: a side and a member at the place
  `kindPays_k5_at_return`      the first theorem, at the description that the maker returned
  `kindPays_k5_at_family`      the same at the description that the online provers stand over
  `kindPays_k5_shared`, `kindPays_k5_second`   K5 pays at the other two chains: it has no side there
  `k5_pays_where_files_pass`   payment and sides without the head: at every return of the maker,
                              where the public files pass the library's three tests

What this is. One kind's share of the field `pays₁` of `ReadyDebts` (Honest/Law/ReadyOfSides.lean),
which `ready_of_sides` joins into a return of `ready`: `chainSteps` returns at the member at each of
K5's sides, at every view and every run's coins. So the rounds of these places are prepared.

What this is not. It is not acceptance: nothing here says that a part plays, that a round is
reached, or that the verifier's block accepts what K5 sends. It says nothing of the other kinds. It
is not the return of `ready`, whose other debts lie elsewhere.

The premises. h: the library's head, at the public files Z. hA: the maker returns A. The last theorem
asks no head: scope, read, hl are tests on the public files.

Limits.
  * `hA` is a premise here. `makerReturns` (AtFullSide/Honest/HonestProverLaws.lean) gives
    it where the public files pass. That file stands in the side library AtFullSide, and this file
    does not import it: where the two are not joined, the last theorem may
    hold of nothing.
  * That any public files pass the three tests is evaluated, not proved: no theorem here or beneath
    gives such files.
  * The full size and the format's second hash function alone.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.ReadyOfSidesAtLots
import Johnson.Desc.ProofFile.Honest.K5.Law.FindAtBase
import Johnson.Desc.ProofFile.Honest.Law.KindPaysOnline
import Johnson.P5J.HeadExistsAtName
import Johnson.Goal.Skeleton.OwedOfLive

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain FileDescription KindName Place)
open P5J (AtMgA TS)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open ProofFile.Honest.Term (OnlineReturn onlineMaker matrixInput tableCoins onlineBase onlinePairs onlineLot
  kindPays_online)

/-! ## 1 K5's lot read through -/

section
variable {W₀ W₀' Rc Rc' Xi Tr X : Type}

/-- **K5's side read through is K5's side**: a part reads of its input the trace alone. `g`, `rd`:
any. -/
theorem k5Half_thru (g : W₀' → W₀) (rd : Rc' → Rc) (cells : Tr → Cells) (Y : Seat5) :
    (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Y).thru (Local.thru g rd)
        (Local.thru g rd) =
      k5Half (W₀ := W₀') (Rc := Rc') (Xi := Xi) (X := X) cells Y := by
  show (⟨Y.place, ((k5Row Y).map fun p =>
      p.lift (fun _ => ()) (fun t : Local W₀ Rc Xi Tr => inOf Y.P.S Y.link (cells t.trace))
        (fun _ => ()) fun x _ => x).map (Part.thru (Local.thru g rd) (Local.thru g rd))⟩ :
      Placed (Local W₀' Rc' Xi Tr) (Local W₀' Rc' Xi Tr) X) =
    ⟨Y.place, (k5Row Y).map fun p =>
      p.lift (fun _ => ()) (fun t : Local W₀' Rc' Xi Tr => inOf Y.P.S Y.link (cells t.trace))
        (fun _ => ()) fun x _ => x⟩
  rw [List.map_map]
  exact congrArg (Placed.mk Y.place) (List.map_congr_left fun p _ =>
    Part.lift_thru (Local.thru g rd) (Local.thru g rd) (fun _ => ())
      (fun t : Local W₀ Rc Xi Tr => inOf Y.P.S Y.link (cells t.trace)) (fun _ => ())
      (fun x _ => x) p)

/-- **K5's lot read through is K5's lot.** `g`, `rd`: any. -/
theorem k5LotK_thru (g : W₀' → W₀) (rd : Rc' → Rc) (cells : Tr → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)) :
    (k5LotK (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells keyOf).thru (Local.thru g rd)
        (Local.thru g rd) =
      k5LotK (W₀ := W₀') (Rc := Rc') (Xi := Xi) (X := X) cells keyOf := by
  refine HLot.ext' rfl (funext fun Z => funext fun G => ?_)
  show ((H2K5.k5Places G).filterMap fun y =>
      (seatAtK keyOf Z G y.1 y.2.1 y.2.2).map
        (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells)).map
        (Placed.thru (Local.thru g rd) (Local.thru g rd)) =
    (H2K5.k5Places G).filterMap fun y =>
      (seatAtK keyOf Z G y.1 y.2.1 y.2.2).map
        (k5Half (W₀ := W₀') (Rc := Rc') (Xi := Xi) (X := X) cells)
  rw [List.map_filterMap]
  refine congrArg (fun f => List.filterMap f (H2K5.k5Places G)) (funext fun y => ?_)
  cases seatAtK keyOf Z G y.1 y.2.1 y.2.2 with
  | none => rfl
  | some Y => exact congrArg some (k5Half_thru g rd cells Y)

end

/-! ## 2 Each side of K5's lot pays -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **Each side of K5's lot pays, at the maker's book, at any filling.** It speaks at every view,
so it asks for no member of the view's type. Conditional: h; hA. -/
theorem sidePays_k5 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {W₀ Rc X₀ X : Type}
    {P : OnlineProverParts W₀ Rc Cells X₀ X} {A : OnlineProverWithDescription W₀ Rc Cells X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    ∀ q ∈ (k5LotK (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) id keyOfK3).halves Zp A.G,
      SidePays A.B 0 (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder q := by
  obtain ⟨e1, eG, -⟩ := atPure_ok hA
  have eZ : A.Z = Zp := Except.ok.inj (e1.symm.trans h.laid.pub)
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some A.G := by
    rw [← eZ]
    exact eG
  have hp : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).placesOk = true :=
    Johnson.RunOne.Sound.placesOk_of_planOk _ h.laid.planOk
  have hn : ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.map (·.place)).Nodup :=
    (List.nodup_append.1 (List.nodup_append.1 (orderOf_nodup hp)).1).1
  have once := k5LotK_places_once (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) id keyOfK3 Zp A.G
  intro q hq b hb hbq hs hf v k
  obtain ⟨j, hj, ej⟩ := k5Lot_place_at_head h hG id keyOfK3 q hq
  obtain ⟨blk, a, hm, Pl, Dc⟩ := k5_member h hj
  have hbm : blk ∈ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder := List.mem_of_getElem? hm
  have hbp : blk.place = placeOf j := Dc.place
  obtain rfl : b = blk := List.inj_on_of_nodup_map hn hb hbm (by rw [hbq, ej, hbp])
  have hfind := k5LotK_find_K3 (W₀ := W₀) (Rc := Rc) (X := X) h hj hG id Pl.plan
  have hmem := List.mem_of_find?_eq_some hfind
  have hpl : (k5Half (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) id
      (seatOf keyOfK3 Zp A.G cF j a)).place = placeOf j := by
    simpa using List.find?_some hfind
  obtain rfl : q = k5Half id (seatOf keyOfK3 Zp A.G cF j a) :=
    List.inj_on_of_nodup_map once hq hmem (by rw [ej, hpl])
  exact k5_member_steps h hj hA Pl.plan Dc hf v k

/-! ## 3 At the online filling -/

/-- K5's lot as the online filling holds it is K5's lot at the return's types. -/
theorem k5_onlineLot (files : VerifierAndGoals.PublicFiles) :
    onlineLot files (k5LotK id keyOfK3) =
      k5LotK (W₀ := FullSizeMatrix) (Rc := (protocolAtFiles files).EncodingRandomness) (Xi := ProofFile.Inst) (X := Unit) id keyOfK3 :=
  k5LotK_thru id (tableCoins files) id keyOfK3

/-- **The kind K5 pays at the maker's return**: under the library's head, wherever the maker returns
A, every side of kind K5 in A's first chain pays. It is not acceptance. Conditional: h; hA. -/
theorem kindPays_k5_at_term (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) :
    KindPays A.B 0 (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder A.H.first KindName.K5 := by
  obtain ⟨e1, -⟩ := atPure_ok hA
  have eZ : A.Z = Zp := Except.ok.inj (e1.symm.trans h.laid.pub)
  refine kindPays_online hA (L := k5LotK id keyOfK3) (fun q hq => ?_)
    (k5_pair_only _ _ _ _)
  rw [k5_onlineLot, eZ] at hq
  exact sidePays_k5 h hA q hq

/-- K5's lot lies in the base filling. -/
theorem k5_lot_mem : (k5LotK id keyOfK3 : HLot (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
    (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit) ∈ onlineBase.lots := by
  rw [fillPairs_lots]
  exact List.mem_map.2 ⟨_, k5_pair_mem _ _ _ _, rfl⟩

/-- **What a search at the place of group j finds in A's first chain: K5's side there.** Conditional:
h; hA; ha: the plan of group j. -/
theorem k5_find_at_term (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) {j : Nat} (hj : j < 12) {a : OnBytes.Attention.Plan}
    (ha : (P5J.At.X Zp).A[j]? = some a) :
    A.H.first.find? (fun q => q.place == placeOf j) =
      some (k5Half id (seatOf keyOfK3 Zp A.G cF j a)) := by
  obtain ⟨e1, eG, -⟩ := atPure_ok hA
  have eZ : A.Z = Zp := Except.ok.inj (e1.symm.trans h.laid.pub)
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some A.G := by
    rw [← eZ]
    exact eG
  have hfind := k5LotK_find_K3 (W₀ := FullSizeMatrix) (Rc := (protocolAtFiles Z).EncodingRandomness) (X := Unit) h hj hG id ha
  have hlot : k5LotK (W₀ := FullSizeMatrix) (Rc := (protocolAtFiles Z).EncodingRandomness) (Xi := ProofFile.Inst) (X := Unit) id keyOfK3 ∈
      (ProofFile.Honest.Term.onlineFilling Z).lots := by
    rw [← k5_onlineLot]
    exact List.mem_map_of_mem k5_lot_mem
  refine atPure_first_find_kind hA hlot (fun M' hM' => ?_) (by rw [eZ]; exact hfind)
  obtain ⟨M, hM, rfl⟩ := List.mem_map.1
    (hM' : M' ∈ onlineBase.lots.map
      (HLot.thru (Local.thru id (tableCoins Z)) (Local.thru id (tableCoins Z))))
  rcases lot_alone _ _ _ _ (k5_pair_only _ _ _ _) A.Z A.G M hM with rfl | hn
  · exact Or.inr (congrFun (congrFun (congrArg HLot.halves (k5_onlineLot Z)) _) _)
  · refine Or.inl fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1
      (hx : x ∈ (M.halves A.Z A.G).map
        (Placed.thru (Local.thru id (tableCoins Z)) (Local.thru id (tableCoins Z))))
    exact hn y hy

/-- **At each of the twelve groups K5's sender stands**: there is a plan of the group, a member of the
description's list stands at the group's place, and a search at that place in A's first chain finds
K5's side. So the theorem on payment is not met for want of sides. Conditional: h; hA. -/
theorem k5_sender_at_term (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) {j : Nat} (hj : j < 12) :
    ∃ a, (P5J.At.X Zp).A[j]? = some a ∧
      (∃ b ∈ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder, b.place = placeOf j) ∧
      A.H.first.find? (fun q => q.place == placeOf j) =
        some (k5Half id (seatOf keyOfK3 Zp A.G cF j a)) := by
  obtain ⟨blk, a, hm, Pl, Dc⟩ := k5_member h hj
  exact ⟨a, Pl.plan, ⟨blk, List.mem_of_getElem? hm, Dc.place⟩, k5_find_at_term h hA hj Pl.plan⟩

/-- **The twelve places differ.** -/
theorem placeOf_injective : Function.Injective placeOf := by
  intro i j e
  have hl : some (2 * i + 1) = some (2 * j + 1) := congrArg Place.link e
  have := Option.some.inj hl
  omega

/-- **At each of the twelve groups a side stands in A's first chain, at the place of a member of the
description's list.** Conditional: h; hA. -/
theorem k5_side_at_term (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) {j : Nat} (hj : j < 12) :
    ∃ q ∈ A.H.first, ∃ b ∈ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder,
      b.place = q.place ∧ q.place = placeOf j ∧ q.place.kind = KindName.K5 := by
  obtain ⟨a, -, ⟨b, hb, hbp⟩, hf⟩ := k5_sender_at_term h hA hj
  have hq := List.mem_of_find?_eq_some hf
  have e : (k5Half (W₀ := FullSizeMatrix) (Rc := (protocolAtFiles Z).EncodingRandomness) (Xi := ProofFile.Inst) (X := Unit) id
      (seatOf keyOfK3 Zp A.G cF j a)).place = placeOf j := by
    simpa using List.find?_some hf
  exact ⟨_, hq, b, hb, hbp.trans e.symm, e, by rw [e]⟩

/-- **The same at the description that the maker returned.** Conditional: h; hA. -/
theorem kindPays_k5_at_return (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) : KindPays A.B 0 A.F.first.blocksInOrder A.H.first KindName.K5 := by
  obtain ⟨-, -, e3, -⟩ := atPure_ok hA
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF := Except.ok.inj (e3.symm.trans h.laid.value)
  rw [eF]
  exact kindPays_k5_at_term h hA

/-- **At the description that the online provers stand over**: at the places and the first chain
that `onlineProver` reads off the maker's public part. Conditional: h; hA. -/
theorem kindPays_k5_at_family (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) {places : H2U.Places4} {firstChain : Chain TS ProofFile.Cl}
    (hPlaces : H2U.placesOfMade A.Z.made = .ok places)
    (hChain : ProofFile.onlineFirstChainAt A.Z = .ok firstChain) :
    KindPays A.B 0 (descZ A.Z places firstChain).first.blocksInOrder A.H.first KindName.K5 := by
  rw [(ProofFile.Honest.Term.online_desc_at_head h hA hPlaces hChain).1]
  exact kindPays_k5_at_term h hA

/-- **K5 pays at the shared chain, for want of sides.** Conditional: h; hA. -/
theorem kindPays_k5_shared (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) : KindPays A.B 1 A.F.shared.blocksInOrder A.H.shared KindName.K5 :=
  ProofFile.Honest.Term.kindPays_online_shared_none h hA (by decide)

/-- **K5 pays at the second chain, for want of sides.** Conditional: hA. -/
theorem kindPays_k5_second {A : OnlineReturn Z} (hA : onlineMaker Z = .ok A) :
    KindPays A.B 2 A.F.second.blocksInOrder A.H.second KindName.K5 :=
  ProofFile.Honest.Term.kindPays_online_second_none hA (by decide)

/-- **Without the head, at every return of the maker**: where the public files are in scope, can be
read and pass the library's test, K5 pays at the return, and its sender stands at each of the twelve
groups. It is not acceptance. Conditional: the three tests; hA. That the maker returns is not shown
here. -/
theorem k5_pays_where_files_pass (Z : VerifierAndGoals.PublicFiles) {pp : Inst.Model.ScalesAndPolicy}
    (scope : VerifierAndGoals.InScope Z = true) (read : VerifierAndGoals.readFiles Z = .ok pp)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) :
    KindPays A.B 0 A.F.first.blocksInOrder A.H.first KindName.K5 ∧
      ∀ j, j < 12 → ∃ q ∈ A.H.first, ∃ b ∈ A.F.first.blocksInOrder,
        b.place = q.place ∧ q.place = placeOf j := by
  obtain ⟨Zp, Np, cF, x, h⟩ := P5J.head_exists_at_name Z scope read hl (P5J.owed_of_live hl)
  refine ⟨kindPays_k5_at_return h hA, fun j hj => ?_⟩
  obtain ⟨-, -, e3, -⟩ := atPure_ok hA
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF := Except.ok.inj (e3.symm.trans h.laid.value)
  rw [eF]
  obtain ⟨q, hq, b, hb, e1, e2, -⟩ := k5_side_at_term h hA hj
  exact ⟨q, hq, b, hb, e1, e2⟩

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5Half_thru
#print axioms ProofFile.Honest.K5.k5LotK_thru
#print axioms ProofFile.Honest.K5.sidePays_k5
#print axioms ProofFile.Honest.K5.k5_onlineLot
#print axioms ProofFile.Honest.K5.kindPays_k5_at_term
#print axioms ProofFile.Honest.K5.k5_lot_mem
#print axioms ProofFile.Honest.K5.k5_find_at_term
#print axioms ProofFile.Honest.K5.k5_sender_at_term
#print axioms ProofFile.Honest.K5.placeOf_injective
#print axioms ProofFile.Honest.K5.k5_side_at_term
#print axioms ProofFile.Honest.K5.kindPays_k5_at_return
#print axioms ProofFile.Honest.K5.kindPays_k5_at_family
#print axioms ProofFile.Honest.K5.kindPays_k5_shared
#print axioms ProofFile.Honest.K5.kindPays_k5_second
#print axioms ProofFile.Honest.K5.k5_pays_where_files_pass
