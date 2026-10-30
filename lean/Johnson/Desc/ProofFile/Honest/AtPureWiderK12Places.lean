-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/AtPureWiderK12Places.lean: where the sides of `proxLotAt`
(Honest/AtPureWiderK12.lean) stand: at the test's place alone, which is a place of the first chain:
so none is a stray and no two of them stand at one place. No definition; seventeen lemmas.

  `proxPlace`          the planner's record bears the test's place, at every public part: so the
                       third of `proxLotAt`'s tests never says no
  `proxPlace_stands`   wherever the first chain is made a block of it stands at the test's place:
                       so the second never says no either
  `proxLotAt_made`     wherever the first chain is made `proxLotAt` is the authors' list
  `proxLotOf_none`, `proxLotOf_unfit`   no side where the plan has no finish, or `fitsL` says no
  `proxLotOf_short`    the authors' list has no side, or one
  `proxLotOf_place`    every side of the authors' list stands at the planner's record's place
  `proxLotOf_form`     it is the authors' list under `widerFillOwn`'s own two binders
  `proxLotAt_sub`      a side of `proxLotAt` is a side of `proxLotOf`
  `proxLotAt_place`, `proxLotAt_kinds`   it stands at `K12.AtProof.placeL`; its kind is K12
  `proxLotAt_in_chain`   that place is a place of the first chain
  `proxLotAt_clean`    at an opened description: no stray
  `proxLotAt_once`, `proxLotAt_no_twice`   at every public part and ground: no two sides of the
                       list at one place; the frame's own test finds no double among them
  `atPure_prox_arm`    wherever `onlineProverFromPublicFiles` returns, the first chain is made: the arm for an error is
                       not taken
  `atPure_prox`        so there `proxLotAt` is the authors' list

By what. `K10.strays_nil` and `K10.twice_nil` (Honest/K10/LotAll.lean), which speak of any list of
sides; `K12.AtProof.halves_lotAtDoor`, the list's authors'; `IM.p12_place`
(Johnson/IMR/LotKinds.lean); `ProofFile.Law.chainBy_places`
(Johnson/Desc/ProofFile/Law/OrderCovered.lean);
`ToldDesc.pureChainAt_of_open` (Johnson/ToldDescR/PureChainOfOpen.lean); `atPure_open`
(Honest/AtPureWiderK10.lean).

Limits.
  * Of a side these statements read its place alone. THE TWO PARTS CANNOT REFUSE: that a side stands
    at the test's place is no ground that they play (Honest/AtPureWiderK12.lean, Limits).
  * Nothing here says that the list has a side: `K12.AtProof.finishAt` and `K12.AtProof.fitsL` are
    paid by nothing here.
  * That no side of ANOTHER list stands at the test's place is not said here: the frame runs `twice`
    over all lists' sides joined. `eleven_not_K12` (Honest/AtPureWiderK12Kinds.lean) says it of the
    eleven, under `FirstFill.LongKinds`.
  * That `onlineProverFromPublicFiles` returns at `widerFillOwnCP` is not stated here: `proxLotAt_clean` is one of the
    things that such a statement wants.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.AtPureWiderK12
import Johnson.Desc.ProofFile.Honest.K10.LotAll
import Johnson.IMR.LotKinds
import Johnson.Desc.ProofFile.Law.OrderCovered

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Chain FileDescription KindName)

variable {W₀ X : Type}

/-! ## 1 The authors' list -/

/-- **The planner's record for the first chain's test bears the test's place**, at every public
part: the sealed `IM.p12_place` (Johnson/IMR/LotKinds.lean), at the name `K12.AtProof.placeL`. -/
theorem proxPlace (Z : Pub) : (H2U.p12OfMade Z.made).place = K12.AtProof.placeL :=
  IM.p12_place Z.made

/-- **Wherever the first chain is made a block of it stands at the test's place.** The places of a
chain that `chainBy` returns are the driver's table (`ProofFile.Law.chainBy_places`), and behind the
segments that table has the kinds K2 and K12 at the pieces 1 and 2. -/
theorem proxPlace_stands {Z : Pub} {cF : Chain VerifiableInference.Desc.First.S ProofFile.Cl}
    (h : ProofFile.onlineFirstChainAt Z = .ok cF) : cF.blocksInOrder.any (·.place == K12.AtProof.placeL) = true := by
  have h' : (ProofFile.partsOf Z (ProofFile.pureSeat ProofFile.emptySecondHashFunction Z)).bind (fun P =>
                        P.base.bind fun base => ProofFile.chainBy Z base P.frames P.road) = .ok cF := h
  obtain ⟨P, _, h₁⟩ := bind_ok h'
  obtain ⟨base, _, hc⟩ := bind_ok h₁
  have hp : K12.AtProof.placeL = ⟨1, none, 2, KindName.K12⟩ :=
    (proxPlace Z).symm.trans (IM.p12_place Z.made)
  have hm : K12.AtProof.placeL ∈ cF.blocksInOrder.map (·.place) := by
    rw [ProofFile.Law.chainBy_places hc, hp]
    unfold VerifiableInference.Desc.First.flatPlacesOf
    refine List.mem_append_left _ (List.mem_append_right _ ?_)
    generalize (base.any fun b => b.place.kind == KindName.K13) = several
    cases several <;> decide
  obtain ⟨b, hb, eb⟩ := List.mem_map.1 hm
  exact List.any_eq_true.2 ⟨b, hb, by rw [eb]; exact beq_self_eq_true _⟩

/-- Where the plan has no finish the authors' list has no side. -/
theorem proxLotOf_none (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) {Z : Pub} {G : Ground}
    (hf : K12.AtProof.finishAt Z G = none) : (proxLotOf (X := X) I S).halves Z G = [] := by
  unfold proxLotOf K12.AtProof.lotAtDoor K12.AtProof.lotL K12.AtProof.lotOf
  simp [hf]

/-- Where the public test on the two places says no the authors' list has no side. -/
theorem proxLotOf_unfit (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) {Z : Pub} {G : Ground}
    {pl : K2.SwitchPlace} (hf : K12.AtProof.finishAt Z G = some pl)
    (hn : K12.AtProof.fitsL (H2U.p12OfMade Z.made) pl = false) :
    (proxLotOf (X := X) I S).halves Z G = [] := by
  unfold proxLotOf K12.AtProof.lotAtDoor K12.AtProof.lotL K12.AtProof.lotOf
  simp [hf, hn]

/-- **The authors' list has no side, or one, and that one at the planner's record's place.** -/
theorem proxLotOf_short (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (Z : Pub) (G : Ground) :
    (proxLotOf (X := X) I S).halves Z G = [] ∨
      ∃ g, (proxLotOf (X := X) I S).halves Z G = [g] ∧
        g.place = (H2U.p12OfMade Z.made).place := by
  cases hf : K12.AtProof.finishAt Z G with
  | none => exact Or.inl (proxLotOf_none I S hf)
  | some pl =>
    cases hfit : K12.AtProof.fitsL (H2U.p12OfMade Z.made) pl with
    | false => exact Or.inl (proxLotOf_unfit I S hf hfit)
    | true => exact Or.inr ⟨_, K12.AtProof.halves_lotAtDoor _ _ _ Z G pl hf hfit, rfl⟩

/-- Every side of the authors' list stands at the planner's record's place. -/
theorem proxLotOf_place (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (Z : Pub) (G : Ground) :
    ∀ x ∈ (proxLotOf (X := X) I S).halves Z G, x.place = (H2U.p12OfMade Z.made).place := by
  intro x hx
  rcases proxLotOf_short (X := X) I S Z G with h | ⟨g, h, hg⟩
  · rw [h] at hx
    cases hx
  · rw [h] at hx
    obtain rfl := List.mem_singleton.1 hx
    exact hg

/-- **It is the authors' list under `widerFillOwn`'s own two binders**, beside `K2.switchLot`. -/
theorem proxLotOf_form (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (Z : Pub) (G : Ground) :
    (proxLotOf (X := X) I S).halves Z G =
      (HLot.byPub I.weights fun wt => HLot.byRows (widerRows S) fun D =>
        (K12.AtProof.lotAtDoor (fun _ _ => D)
          (fun _ _ (w : Local W₀ IndexCommitterCoins Inst Cells) => ⟨w.trace, wt w.w₀, w.rc⟩)
          (fun Z G => K2.lotClosingAt G.first.layout (K2.segmentsOf Z G)) :
          HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) X)).halves Z G := rfl

/-! ## 2 The list behind its three tests -/

/-- A side of `proxLotAt` is a side of `proxLotOf`, and the first chain is made and has a block at
the test's place. -/
theorem proxLotAt_sub (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) {Z : Pub} {G : Ground}
    {x : Placed (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) X}
    (hx : x ∈ (proxLotAt (X := X) I S).halves Z G) :
    x ∈ (proxLotOf (X := X) I S).halves Z G ∧
      ∃ cF, ProofFile.onlineFirstChainAt Z = .ok cF ∧
        cF.blocksInOrder.any (·.place == K12.AtProof.placeL) = true := by
  have hq : ((H2U.p12OfMade Z.made).place == K12.AtProof.placeL) = true := by
    rw [proxPlace]
    exact beq_self_eq_true _
  cases h : ProofFile.onlineFirstChainAt Z with
  | error e =>
    rw [proxLotAt_error I S G h] at hx
    cases hx
  | ok cF =>
    cases hb : cF.blocksInOrder.any (·.place == K12.AtProof.placeL) with
    | false =>
      rw [proxLotAt_else I S G h (by rw [hb]; rfl)] at hx
      cases hx
    | true =>
      rw [proxLotAt_ok I S G h hb hq] at hx
      exact ⟨hx, cF, rfl, hb⟩

/-- **Wherever the first chain is made the list is the authors' list**: the two other tests say yes
there. -/
theorem proxLotAt_made (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) {Z : Pub} (G : Ground)
    {cF : Chain VerifiableInference.Desc.First.S ProofFile.Cl} (h : ProofFile.onlineFirstChainAt Z = .ok cF) :
    (proxLotAt (X := X) I S).halves Z G = (proxLotOf I S).halves Z G :=
  proxLotAt_ok I S G h (proxPlace_stands h) (by rw [proxPlace]; exact beq_self_eq_true _)

/-- **Every side of the list stands at the test's place.** -/
theorem proxLotAt_place (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (Z : Pub) (G : Ground) :
    ∀ x ∈ (proxLotAt (X := X) I S).halves Z G, x.place = K12.AtProof.placeL := fun x hx =>
  (proxLotOf_place I S Z G x (proxLotAt_sub I S hx).1).trans (proxPlace Z)

/-- Every side of the list stands at a place of the kind K12. -/
theorem proxLotAt_kinds (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (Z : Pub) (G : Ground) :
    ∀ x ∈ (proxLotAt (X := X) I S).halves Z G, x.place.kind = KindName.K12 := by
  intro x hx
  rw [proxLotAt_place I S Z G x hx]
  rfl

/-- **The place of each side of the list is a place of the first chain.** -/
theorem proxLotAt_in_chain (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) {Z : Pub} (G : Ground)
    {cF : Chain VerifiableInference.Desc.First.S ProofFile.Cl} (h : ProofFile.onlineFirstChainAt Z = .ok cF) :
    ∀ x ∈ (proxLotAt (X := X) I S).halves Z G, x.place ∈ cF.blocksInOrder.map (·.place) := by
  intro x hx
  obtain ⟨-, c', h', hb⟩ := proxLotAt_sub I S hx
  obtain rfl : c' = cF := Except.ok.inj (h'.symm.trans h)
  obtain ⟨b, hb1, hb2⟩ := List.any_eq_true.1 hb
  rw [proxLotAt_place I S Z G x hx, ← eq_of_beq hb2]
  exact List.mem_map_of_mem hb1

/-- **At an opened description no side of the list is a stray.** -/
theorem proxLotAt_clean (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (G : Ground)
    {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription Inst} {Z : Pub}
    {Bs : ProofFile.PureBase} {base : List (Block VerifiableInference.Desc.First.S ProofFile.Cl)}
    {c : Chain VerifiableInference.Desc.First.S ProofFile.Cl} {Sh : ProofFile.SharedSeat}
    {Se : ProofFile.SecondSeat} (O : IM.Open o pol lay KL F Z Bs base c Sh Se) :
    strays F.first.blocksInOrder ((proxLotAt (X := X) I S).halves Z G) = [] := by
  have key := proxLotAt_in_chain (X := X) I S G (ToldDesc.pureChainAt_of_open O)
  obtain rfl := O.desc
  exact K10.strays_nil key

/-- **No two sides of the list stand at one place**: it has one side at most. -/
theorem proxLotAt_once (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (Z : Pub) (G : Ground) :
    (((proxLotAt (X := X) I S).halves Z G).map (·.place)).Nodup := by
  have hq : ((H2U.p12OfMade Z.made).place == K12.AtProof.placeL) = true := by
    rw [proxPlace]
    exact beq_self_eq_true _
  cases h : ProofFile.onlineFirstChainAt Z with
  | error e =>
    rw [proxLotAt_error I S G h]
    exact List.nodup_nil
  | ok cF =>
    cases hb : cF.blocksInOrder.any (·.place == K12.AtProof.placeL) with
    | false =>
      rw [proxLotAt_else I S G h (by rw [hb]; rfl)]
      exact List.nodup_nil
    | true =>
      rw [proxLotAt_ok I S G h hb hq]
      rcases proxLotOf_short (X := X) I S Z G with e | ⟨g, e, -⟩
      · rw [e]
        exact List.nodup_nil
      · rw [e]
        exact List.nodup_singleton _

/-- The frame's own test finds no double among them. -/
theorem proxLotAt_no_twice (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (Z : Pub) (G : Ground) :
    twice ((proxLotAt (X := X) I S).halves Z G) = [] :=
  K10.twice_nil (proxLotAt_once I S Z G)

/-! ## 3 Where `onlineProverFromPublicFiles` returns -/

/-- **WHERE `onlineProverFromPublicFiles` RETURNS A, AT ANY CHOICE OF FIELDS AND ANY o, THE FIRST CHAIN IS MADE AT A.Z**:
`proxLotAt`'s arm for an error is not taken there. -/
theorem atPure_prox_arm {Rc Tr X₀ Y : Type} {o : SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {P : OnlineProverParts W₀ Rc Tr X₀ Y} {A : OnlineProverWithDescription W₀ Rc Tr X₀ Y} (h : onlineProverFromPublicFiles o pol lay KL P = .ok A) :
    ∃ c, ProofFile.onlineFirstChainAt A.Z = .ok c := by
  obtain ⟨Bs, base, c, Sh, Se, O⟩ := atPure_open h
  exact ⟨c, ToldDesc.pureChainAt_of_open O⟩

/-- **So where `onlineProverFromPublicFiles` returns A the list is the authors' list**, at A's public part and every
ground. -/
theorem atPure_prox {Rc Tr X₀ Y : Type} {o : SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {P : OnlineProverParts W₀ Rc Tr X₀ Y} {A : OnlineProverWithDescription W₀ Rc Tr X₀ Y} (h : onlineProverFromPublicFiles o pol lay KL P = .ok A)
    (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (G : Ground) :
    (proxLotAt (X := X) I S).halves A.Z G = (proxLotOf I S).halves A.Z G := by
  obtain ⟨c, hc⟩ := atPure_prox_arm h
  exact proxLotAt_made I S G hc

end ProofFile.Honest

#print axioms ProofFile.Honest.proxPlace
#print axioms ProofFile.Honest.proxPlace_stands
#print axioms ProofFile.Honest.proxLotAt_made
#print axioms ProofFile.Honest.atPure_prox
#print axioms ProofFile.Honest.proxLotOf_none
#print axioms ProofFile.Honest.proxLotOf_unfit
#print axioms ProofFile.Honest.proxLotOf_short
#print axioms ProofFile.Honest.proxLotOf_place
#print axioms ProofFile.Honest.proxLotOf_form
#print axioms ProofFile.Honest.proxLotAt_sub
#print axioms ProofFile.Honest.proxLotAt_place
#print axioms ProofFile.Honest.proxLotAt_kinds
#print axioms ProofFile.Honest.proxLotAt_in_chain
#print axioms ProofFile.Honest.proxLotAt_clean
#print axioms ProofFile.Honest.proxLotAt_once
#print axioms ProofFile.Honest.proxLotAt_no_twice
#print axioms ProofFile.Honest.atPure_prox_arm
