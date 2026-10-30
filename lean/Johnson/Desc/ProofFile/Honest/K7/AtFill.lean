-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K7/AtFill.lean: the round that names the next token (kind K7) at a
filling: the ten lots of `widerFillAt`, read through or not. What the prover's sides hold at the kind,
and what the kind owes at the description.

  `replyLot_mem`   the lot stands among the ten lots
  `k7_only`   a half of the kind K7 comes from that lot alone
  `replySLot_mem_through`, `k7_only_through`   the same under `OnlineProverParts.through`: read through, the lot is
                   `replySLot` without its simulators
  `reply_half_only`, `reply_found_at`   where `onlineProverFromPublicFiles` returns: among the first chain's sides a half of the
                   kind is the kind's half, and the look-up by the place finds it
  `atPure_strays`, `side_on_chain`, `none_at_k7_elsewhere`   where `onlineProverFromPublicFiles` returns no side stands off
                   its chain, so none of the shared or second chain stands at the place
  `k7_block_stands`   a sub-protocol of the description stands at the place
  `reply_good_at_desc`   fits, exact, fresh and `ShowsSome` at the description's own first chain and a
                   whole book, at every On and bud
  `reply_good_at_chain`   the same at the chain c of `IM.Open`
  `plan_gives_places`, `no_k7_later`   the tests on the plan hold the test on the places; no
                   sub-protocol of the shared or the second chain is of the kind
  `ReplyClosed`, `reply_closing`   all of it, as one statement, at a return of `onlineProverFromPublicFiles`
  `reply_no_stop`, `reply_on`, `reply_bud`   the part never stops; the row's On and bud ask nothing

The sheet of the kinds. (a) The rows are one term of `Pub → Ground`; the tie at the base
filling is in AtFullSide/Honest/K7AtTerm.lean. (d′) No fall: `fallsHead` (Law/FallsHead.lean) has no record at
a place of the kind, and the part has no stop. (e′) The part spends and carries nothing, so no entry
names it as spender and nothing of it is owed beside. `Good` here is stated at A := B := False. That
the description passes `placesOk`, or `planOk` which
holds it, is a premise: `onlineProverFromPublicFiles` does not test it. This file proves nothing about soundness, completeness,
hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K7.AtSeat
import Johnson.Desc.ProofFile.Honest.K7.AtBook
import Johnson.Desc.ProofFile.Honest.K7.AtThru
import Johnson.Desc.ProofFile.Honest.ThruK13
import Johnson.Desc.ProofFile.Honest.Thread.FirstFillAll
import Johnson.Desc.Sound.KindsLater
import Johnson.ToldDescR.PlacesAtTable
import Johnson.ToldDescR.PureChainOfOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Chain FileDescription Place KindName)
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)

variable {W₀ W₀' Rc' : Type}

/-- The lot stands among the ten lots. -/
theorem replyLot_mem (I : WiderIn W₀) (o : SecondHashFunctionArgument) (Sz : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    replyLot ∈ (widerFillAt I o Sz O).lots := by
  rw [widerFillAt_lots]
  exact List.mem_map.2 ⟨(replyLot, .K7), by
    unfold widerPairs
    exact .tail _ (.tail _ (.head _)), rfl⟩

/-- **A half of the kind K7 comes from the lot alone.** -/
theorem k7_only (I : WiderIn W₀) (o : SecondHashFunctionArgument) (Sz : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (Zq : Pub) (G : Ground) :
    ∀ M ∈ (widerFillAt I o Sz O).lots, ∀ x ∈ M.halves Zq G, x.place.kind = .K7 →
      M = replyLot := by
  intro M hM x hx hk
  rw [widerFillAt_lots] at hM
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hM
  have hk' := (FirstFill.widerKinds I o Sz O Zq G).all q hq x hx
  have e : q.2 = KindName.K7 := hk'.symm.trans hk
  have hm : ((replyLot, KindName.K7) :
      HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit × KindName) ∈
      widerPairs I o Sz O := by
    unfold widerPairs
    exact .tail _ (.tail _ (.head _))
  have e' := List.inj_on_of_nodup_map widerPairs_nodup hq hm e
  rw [e']

/-- **Read through, the lot is `replySLot` without its simulators**, at a filling that holds the lot. -/
theorem replySLot_mem_through {X₀ : Type} {Fl : OnlineProverParts W₀ IndexCommitterCoins Cells X₀ Unit} (hl : replyLot ∈ Fl.lots)
    (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (d : W₀') :
    (replySLot (W₀ := W₀') (Rc := Rc') (Tr := Cells) (X := Unit)).toHLot ∈
      (OnlineProverParts.through g rd d Fl).lots :=
  List.mem_map.2 ⟨replyLot, hl, (replySLot_thru g rd).symm⟩

/-- **A half of the kind comes from the lot alone, read through**, where that holds of the filling. -/
theorem k7_only_through {X₀ : Type} {Fl : OnlineProverParts W₀ IndexCommitterCoins Cells X₀ Unit} {Zq : Pub} {G : Ground}
    (hu : ∀ M ∈ Fl.lots, ∀ x ∈ M.halves Zq G, x.place.kind = .K7 → M = replyLot)
    (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (d : W₀') :
    ∀ M ∈ (OnlineProverParts.through g rd d Fl).lots, ∀ x ∈ M.halves Zq G,
      x.place.kind = .K7 → M = replyLot := by
  intro M hM x hx hk
  obtain ⟨M₀, hM₀, rfl⟩ := List.mem_map.1 hM
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  rw [hu M₀ hM₀ y hy hk]
  exact replyLot_thru g rd

section
variable {Rc Tr X₀ X : Type} {Fl : OnlineProverParts W₀ Rc Tr X₀ X}

/-- **Among the sides, a half of the kind is the kind's half.** -/
theorem reply_half_only {Tr' : Type} {Zp : Pub} {G : Ground}
    {ls : List (HLot (Local W₀ Rc Inst Tr') (Local W₀ Rc Inst Tr') X)}
    (hu : ∀ M ∈ ls, ∀ x ∈ M.halves Zp G, x.place.kind = .K7 → M = replyLot)
    (hsz : G.built.size = 25) :
    ∀ x ∈ firstOf Zp G ls, x.place.kind = .K7 → x = replyHalf 24 1 G.W.hS.V := by
  intro x hx hk
  obtain ⟨M, hM, hxM⟩ := List.mem_flatMap.1 hx
  obtain rfl := hu M hM x hxM hk
  have hs : x ∈ [replyHalf (W₀ := W₀) (Rc := Rc) (Tr := Tr') (X := X) (G.built.size - 1) 1
      G.W.hS.V] := hxM
  rw [hsz] at hs
  exact List.mem_singleton.1 hs

/-- **The look-up by the place finds the kind's half**, with no test on doubled places. -/
theorem reply_found_at {Tr' : Type} {Zp : Pub} {G : Ground}
    {ls : List (HLot (Local W₀ Rc Inst Tr') (Local W₀ Rc Inst Tr') X)} (hl : replyLot ∈ ls)
    (hu : ∀ M ∈ ls, ∀ x ∈ M.halves Zp G, x.place.kind = .K7 → M = replyLot)
    (hsz : G.built.size = 25) :
    (firstOf Zp G ls).find? (fun x => x.place == IM.k7Place) =
      some (replyHalf 24 1 G.W.hS.V) := by
  have hm : replyHalf (W₀ := W₀) (Rc := Rc) (Tr := Tr') (X := X) 24 1 G.W.hS.V ∈
      firstOf Zp G ls := by
    unfold firstOf
    refine List.mem_flatMap.2 ⟨replyLot, hl, ?_⟩
    show _ ∈ [replyHalf (G.built.size - 1) 1 G.W.hS.V]
    rw [hsz]
    exact List.mem_singleton.2 rfl
  have hsome : ((firstOf Zp G ls).find? fun x => x.place == IM.k7Place).isSome = true :=
    List.find?_isSome.2 ⟨_, hm, beq_self_eq_true _⟩
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hsome
  have e₀ := List.find?_some hy
  have hp : y.place = IM.k7Place := beq_iff_eq.1 e₀
  rw [hy, reply_half_only hu hsz y (List.mem_of_find?_eq_some hy) (by rw [hp])]

end

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
  {Bk : ProverCoinCounts}

/-- **Where `onlineProverFromPublicFiles` returns, no side stands off its chain.** -/
theorem atPure_strays {W₀ Rc Tr X₀ X : Type} {o : SecondHashFunctionArgument} {pol lay' KL : ByteArray}
    {Fl : OnlineProverParts W₀ Rc Tr X₀ X} {R : OnlineProverWithDescription W₀ Rc Tr X₀ X} (h : onlineProverFromPublicFiles o pol lay' KL Fl = .ok R) :
    strays R.F.first.blocksInOrder R.H.first = [] ∧ strays R.F.shared.blocksInOrder R.H.shared = [] ∧
      strays R.F.second.blocksInOrder R.H.second = [] := by
  unfold onlineProverFromPublicFiles at h
  obtain ⟨Z', _, h⟩ := bind_ok h
  obtain ⟨G', _, h⟩ := bind_ok h
  obtain ⟨F', _, h⟩ := bind_ok h
  obtain ⟨cs, _, h⟩ := bind_ok h
  split at h
  · obtain ⟨B', _, h⟩ := bind_ok h
    dsimp only at h
    split at h
    · cases h
    · rename_i hc
      split at h
      · cases h
      · cases h
        have hc' : (strays F'.first.blocksInOrder (firstOf Z' G' Fl.lots) = [] ∧
            strays F'.shared.blocksInOrder (Fl.shared Z' G') = []) ∧
            strays F'.second.blocksInOrder (Fl.second Z' G') = [] := by
          simpa [Bool.or_eq_true, not_or] using hc
        exact ⟨hc'.1.1, hc'.1.2, hc'.2⟩
  · cases h

/-- Where the strays are none, a side stands at a sub-protocol of the list. -/
theorem side_on_chain {St Cl' V W X : Type} {bs : List (Block St Cl')} {hs : List (Placed V W X)}
    (h : strays bs hs = []) {x : Placed V W X} (hx : x ∈ hs) : ∃ b ∈ bs, b.place = x.place := by
  have h1 := List.filter_eq_nil_iff.1 (List.map_eq_nil_iff.1 h) x hx
  have h2 : (bs.any fun b => b.place == x.place) = true := by
    simpa using h1
  obtain ⟨b, hb, e⟩ := List.any_eq_true.1 h2
  exact ⟨b, hb, beq_iff_eq.1 e⟩

/-- **No side of the shared or of the second chain stands at the place**, where `onlineProverFromPublicFiles` returns. -/
theorem none_at_k7_elsewhere {W₀ Rc Tr X₀ X : Type} {o : SecondHashFunctionArgument} {pol lay' KL : ByteArray}
    {Fl : OnlineProverParts W₀ Rc Tr X₀ X} {R : OnlineProverWithDescription W₀ Rc Tr X₀ X} (h : onlineProverFromPublicFiles o pol lay' KL Fl = .ok R)
    (hp : R.F.placesOk = true) :
    (∀ x ∈ R.H.shared, x.place ≠ IM.k7Place) ∧ ∀ x ∈ R.H.second, x.place ≠ IM.k7Place := by
  obtain ⟨-, h2, h3⟩ := atPure_strays h
  refine ⟨fun x hx e => ?_, fun x hx e => ?_⟩
  · obtain ⟨b, hb, hpl⟩ := side_on_chain h2 hx
    have hc := chain_shared hp _ (List.mem_map.2 ⟨b, hb, rfl⟩)
    rw [hpl, e] at hc
    cases hc
  · obtain ⟨b, hb, hpl⟩ := side_on_chain h3 hx
    have hc := chain_second hp _ (List.mem_map.2 ⟨b, hb, rfl⟩)
    rw [hpl, e] at hc
    cases hc

/-- **A sub-protocol of the description stands at the place, with the kind's round and no oracle
message.** -/
theorem k7_block_stands (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ b ∈ F.first.blocksInOrder, b.place = IM.k7Place ∧
      b.rounds = VerifiableInference.Desc.Kinds.Reply.rounds ∧ b.oracles = [[]] := by
  obtain ⟨b, hb, hp, hr, ho, -⟩ := k7_at_flat hS hR O
  obtain rfl := O.desc
  exact ⟨b, List.mem_of_getElem? hb, hp, hr, ho⟩

/-- **The seat's test at the place.** -/
theorem k7_seat (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    F.first.blocksInOrder.any (fun b => b.place == IM.k7Place) = true := by
  obtain ⟨b, hb, hp, -, -⟩ := k7_block_stands hS hR O
  exact List.any_eq_true.2 ⟨b, hb, by rw [hp]; exact beq_self_eq_true _⟩

/-- **Fits, exact and fresh at the description's own first chain**, at a whole book, at every On and
bud. -/
theorem reply_good_at_desc {W₀ Rc Tr X : Type} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hw : bookWhole F p0 p1 p2 M = .ok Bk) (hp : F.placesOk = true)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (ord : List Place) (chain firstTree : Nat)
    (fs : List (Fall F.S₁))
    (σ : Side F.S₁ F.Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst)
    (On : (u : Member (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst) →
      CsAll u.part.carries → Mid (Local W₀ Rc Inst Tr) X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
    (hσ : Side.seated F.first.blocksInOrder IM.k7Place (replyRow 24 1) fs = some σ) :
    Good pre Face.own σ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False)
      On bud ∧ ShowsSome pre Face.own σ chain firstTree On bud := by
  have hk := reply_spent_of_open hS hR O hw hp
  obtain rfl := O.desc
  obtain ⟨hpl, hr⟩ := seated_place hσ
  obtain ⟨b', hf, e⟩ := Option.map_eq_some_iff.1 hσ
  have hb := reply_block_at_scope hS hR O
  have hb' := hb b' hf
  obtain rfl := e
  exact ⟨reply_good pre Bk ord chain firstTree hr ⟨hpl, hb'.1, hb'.2⟩ (by rw [hpl]; exact hk),
    reply_shows_some pre chain firstTree hr ⟨hpl, hb'.1, hb'.2⟩⟩

/-- **Fits, exact and fresh at the chain c of `IM.Open`**, at a whole book, at every On and bud. -/
theorem reply_good_at_chain {W₀ Rc Tr X : Type} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hw : bookWhole F p0 p1 p2 M = .ok Bk) (hp : F.placesOk = true)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (ord : List Place) (chain firstTree : Nat)
    (fs : List (Fall S)) (σ : Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst)
    (On : (u : Member (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst) →
      CsAll u.part.carries → Mid (Local W₀ Rc Inst Tr) X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
    (hσ : Side.seated c.blocksInOrder IM.k7Place (replyRow 24 1) fs = some σ) :
    Good pre Face.own σ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False)
      On bud ∧ ShowsSome pre Face.own σ chain firstTree On bud := by
  have hk := reply_spent_of_open hS hR O hw hp
  obtain ⟨hpl, hr⟩ := seated_place hσ
  obtain ⟨b', hf, e⟩ := Option.map_eq_some_iff.1 hσ
  have hb := reply_block_at_scope hS hR O
  have hb' := hb b' hf
  obtain rfl := e
  exact ⟨reply_good pre Bk ord chain firstTree hr ⟨hpl, hb'.1, hb'.2⟩ (by rw [hpl]; exact hk),
    reply_shows_some pre chain firstTree hr ⟨hpl, hb'.1, hb'.2⟩⟩

end

/-- The tests on the plan hold the test on the places. -/
theorem plan_gives_places {Xi : Type} {F : FileDescription Xi} (h : F.planOk = true) :
    F.placesOk = true :=
  ((F.planOk_ok).1 h).places

/-- **No sub-protocol of the shared or of the second chain is of the kind K7**, at a description that
passes its tests on the plan. -/
theorem no_k7_later {o : SecondHashFunctionArgument} {pol lay' KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (hd : ProofFile.onlineDescription o pol lay' KL = .ok F) (hplan : F.planOk = true) :
    (∀ b ∈ F.shared.blocksInOrder, b.place.kind ≠ .K7) ∧ ∀ b ∈ F.second.blocksInOrder, b.place.kind ≠ .K7 := by
  obtain ⟨Z', N, -, -, hs, -⟩ := ToldDesc.shared_fits_descPure hd hplan
  obtain ⟨hl, -⟩ := ToldDesc.last_fits_descPure hd
  have hs' := beq_iff_eq.1 hs
  have hl' := beq_iff_eq.1 hl
  refine ⟨fun b hb e => ?_, fun b hb e => ?_⟩
  · have hm : b.place ∈ VerifiableInference.Desc.Shared.sharedPlaces N.O.isSome := by
      rw [← hs']
      exact List.mem_map.2 ⟨b, hb, rfl⟩
    rcases VerifiableInference.Desc.Sound.sharedPlaces_kinds _ _ hm with h | h | h | h <;>
      rw [e] at h <;> cases h
  · have hm : b.place ∈ VerifiableInference.Desc.Last.lastPlaces := by
      rw [← hl']
      exact List.mem_map.2 ⟨b, hb, rfl⟩
    rcases VerifiableInference.Desc.Sound.lastPlaces_kinds _ hm with h | h | h <;>
      rw [e] at h <;> cases h

/-- **WHAT THE KIND HOLDS AT A RETURN OF `onlineProverFromPublicFiles`.** Of the sides: the look-up at the place finds the
kind's half, every half of the kind in the first chain is it, and none stands in the other two. Of the
description: a sub-protocol stands at the place, and fits, exact and fresh hold at the returned book,
at the description's first chain and at the chain that `onlineFirstChainAt` makes. -/
def ReplyClosed {W₀ Rc Tr X₀ X : Type} (R : OnlineProverWithDescription W₀ Rc Tr X₀ X) : Prop :=
    R.H.first.find? (fun x => x.place == IM.k7Place) = some (replyHalf 24 1 R.G.W.hS.V) ∧
    (∀ x ∈ R.H.first, x.place.kind = .K7 → x = replyHalf 24 1 R.G.W.hS.V) ∧
    (∀ x ∈ R.H.shared, x.place.kind ≠ .K7) ∧ (∀ x ∈ R.H.second, x.place.kind ≠ .K7) ∧
    R.F.first.blocksInOrder.any (fun b => b.place == IM.k7Place) = true ∧
    (∀ (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (ord : List Place) (chain firstTree : Nat)
      (fs : List (Fall R.F.S₁))
      (σ : Side R.F.S₁ R.F.Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst)
      (On : (u : Member (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst) →
        CsAll u.part.carries → Mid (Local W₀ Rc Inst Tr) X → Before → Prop)
      (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop),
      Side.seated R.F.first.blocksInOrder IM.k7Place (replyRow 24 1) fs = some σ →
      Good pre Face.own σ R.B ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False)
        On bud ∧ ShowsSome pre Face.own σ chain firstTree On bud) ∧
    ∃ c : Chain S Cl, ProofFile.onlineFirstChainAt R.Z = .ok c ∧
      (∃ b : Block S Cl, c.blocksInOrder[338]? = some b ∧ b.place = IM.k7Place) ∧
      ∀ (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (ord : List Place) (chain firstTree : Nat)
        (fs : List (Fall S)) (σ : Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst)
        (On : (u : Member (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst) →
          CsAll u.part.carries → Mid (Local W₀ Rc Inst Tr) X → Before → Prop)
        (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop),
        Side.seated c.blocksInOrder IM.k7Place (replyRow 24 1) fs = some σ →
        Good pre Face.own σ R.B ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False)
          On bud ∧ ShowsSome pre Face.own σ chain firstTree On bud

/-- **THE CLOSING**: it holds where `onlineProverFromPublicFiles` returns, in scope, at a filling that lays the lot and no
other half of the kind, and where the description passes its tests on the plan. -/
theorem reply_closing {W₀ Rc Tr X₀ X : Type} {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy}
    {lay : ByteArray} {Fl : OnlineProverParts W₀ Rc Tr X₀ X} {R : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (h : onlineProverFromPublicFiles OnBytes.secondHashFunction P.pol lay P.KL Fl = .ok R) (hplan : R.F.planOk = true)
    (hl : replyLot ∈ Fl.lots)
    (hu : ∀ M ∈ Fl.lots, ∀ x ∈ M.halves R.Z R.G, x.place.kind = .K7 → M = replyLot) :
    ReplyClosed R := by
  unfold ReplyClosed
  obtain ⟨hZ, hG, hF, -, -, -, -, hf, -⟩ := atPure_ok h
  have hsz : R.G.built.size = 25 := (IM.ground_gets hS hR hZ hG).1
  have hp := plan_gives_places hplan
  obtain ⟨-, -, -, -, p0, p1, p2, -, hB⟩ := atPure_book h
  obtain ⟨Bs, base, c, Sh, Se, O⟩ := atPure_open (X := X) h
  obtain ⟨-, h2, h3⟩ := atPure_strays h
  obtain ⟨n2, n3⟩ := no_k7_later hF hplan
  obtain ⟨b, hb, hbp, -⟩ := k7_at_flat hS hR O
  refine ⟨?_, ?_, fun x hx e => ?_, fun x hx e => ?_, k7_seat hS hR O, ?_, c,
    ToldDesc.pureChainAt_of_open O, ⟨b, hb, hbp⟩, ?_⟩
  · rw [hf]
    exact reply_found_at hl hu hsz
  · rw [hf]
    exact reply_half_only hu hsz
  · obtain ⟨b, hb, hpl⟩ := side_on_chain h2 hx
    exact n2 b hb (by rw [hpl]; exact e)
  · obtain ⟨b, hb, hpl⟩ := side_on_chain h3 hx
    exact n3 b hb (by rw [hpl]; exact e)
  · intro pre ord chain firstTree fs σ On bud hσ
    exact reply_good_at_desc hS hR O hB hp pre ord chain firstTree fs σ On bud hσ
  · intro pre ord chain firstTree fs σ On bud hσ
    exact reply_good_at_chain hS hR O hB hp pre ord chain firstTree fs σ On bud hσ

variable {W₀ Rc Tr X : Type}

/-- **The part never stops.** -/
theorem reply_no_stop (v : Option (Local W₀ Rc Inst Tr)) (loc ds : List Fmt.Drawn) :
    (replyPart : Part (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X).stopAt v loc ds = none := by
  unfold Part.stopAt
  simp [replyPart]

/-- The row's On asks nothing. -/
theorem reply_on (link piece : Nat)
    (u : Member (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst) (ca : CsAll u.part.carries)
    (m : Mid (Local W₀ Rc Inst Tr) X) (f : Before) :
    (replyUnlettered link piece).On u ca m f := trivial

/-- The row's bud asks nothing. -/
theorem reply_bud (link piece n : Nat) (ds : List Fmt.Drawn) (asks : List (List (List Nat))) :
    (replyUnlettered (W₀ := W₀) (Rc := Rc) (Tr := Tr) (X := X) link piece).bud n ds asks := trivial

end ProofFile.Honest

#print axioms ProofFile.Honest.replyLot_mem
#print axioms ProofFile.Honest.replySLot_mem_through
#print axioms ProofFile.Honest.k7_only
#print axioms ProofFile.Honest.k7_only_through
#print axioms ProofFile.Honest.reply_half_only
#print axioms ProofFile.Honest.reply_found_at
#print axioms ProofFile.Honest.atPure_strays
#print axioms ProofFile.Honest.side_on_chain
#print axioms ProofFile.Honest.none_at_k7_elsewhere
#print axioms ProofFile.Honest.k7_block_stands
#print axioms ProofFile.Honest.k7_seat
#print axioms ProofFile.Honest.reply_good_at_desc
#print axioms ProofFile.Honest.reply_good_at_chain
#print axioms ProofFile.Honest.plan_gives_places
#print axioms ProofFile.Honest.no_k7_later
#print axioms ProofFile.Honest.ReplyClosed
#print axioms ProofFile.Honest.reply_closing
#print axioms ProofFile.Honest.reply_no_stop
#print axioms ProofFile.Honest.reply_on
#print axioms ProofFile.Honest.reply_bud
