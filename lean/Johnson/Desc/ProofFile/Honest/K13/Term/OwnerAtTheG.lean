-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K13/Term/OwnerAtTheG.lean: the members' batching (kind K13): the coins
that the kind's second part spends, at the lists by their name. The part spends one block of 37
coins of the first segment's opening, a sender of the kind K1 at the place ⟨1, some 0, 1, K1⟩
(`k13_spentBy_owner`, `k13_spentBy_other`, AtFullSide/K13/EntryAtBook.lean). That these are uniform
and independent of what the owner shows is the owner's field fresh of `Good`, at the spender's
address. Here that field is had at the lists `theGOfReturn made h T K` (E2E/TheG.lean), at a return
of the maker at the base filling, with no premise that the kind K1 pays. Four definitions;
statements with their proofs.

  `k1LotAtBase`, `wLotAtBase`   the kind K1's two lots with their simulators
     (Johnson/Desc/ProofFile/Honest/K1/Sim/AtFill.lean), at the base filling
  `k1_slots_by_name`, `otherLotsLayNoSideOfK1`   of the filling's thirteen lots: which bear these
     two names, and that no other lays a side of the kind K1. No premise
  `kindRowsWithK13sAndItsOwnersLotsExist`   a value K that lays the kind's lot and these two exists.
     No premise
  `OwnerFreshAtK13`, `ownerFreshAtK13_at_the_sides`, `ownerFreshAtK13_at_theGOfReturn`   **the
     owner's field fresh at the kind's address**, at each list at a place of the kind K1 and each
     side of it, at the list's own bound: in scope, live, where K lays the kind K1's two lots. By
     `owner_fresh_at_return` (AtFullSide/K1/GoodAtReturn.lean)
  `OwnerStands`, `ownerStands_at_the_sides`, `ownerStands_at_theGOfReturn`   a list stands at the
     owner's place, with a side: so the statement above does not hold for want of a list
  `k13_and_its_owner_at_some_rows`   with no premise on K: there is a K at which the kind's row and
     the owner's list stand, the kind pays, and the owner's field fresh holds at the kind's address

How it stands to another statement. `OwnerFreshK13` (KindPaysAtTheG.lean) is drawn from the
premise that the kind K1 pays, and is one projection of that premise: it pays nothing and nothing
takes it. The statements here tie the field to the
lists.

Limits.
  * The rule that yields the statement on zero knowledge takes "every kind pays", the kind K1 among
    them, and not this statement: so this is no premise of that rule. It says, at the lists, what
    guards the kind's 37 masked values.
  * The field speaks of the coins that the book's `spentBy` lists at the owner and the spender. At
    51 of the 52 lists of the kind K1 that list is empty, and the field holds for that reason. At
    the first segment's opening it is one block of 37 coins; no statement of this file says so.
  * The field stands at the list's own bound on the read positions. How wide that bound is, is not
    said here: where it allowed no position, the field would say little.
  * Where the opening's job does not fit its place, sender and simulator both give the error value,
    and fresh speaks of coins alone, not of a showing. That the job fits is not shown here. It is
    shown at every return of the maker, under the premise live of this file's statements:
    `fits_at_return`, with `shows_some_at_return`
    (Johnson/Desc/ProofFile/Honest/K1/Sim/ShowsAtReturn.lean).
  * That each coin is spent once is a sentence on the book, and not here.
  * The witness lays three lots alone. h and T are arguments. At the base filling's return.
  * One sender at a time; challenges that the sender's rounds can draw; positions within the list's
    bound.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.K13.Term.StandsAtTheG
import AtFullSide.K1.GoodAtReturn

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13
open VerifiableInference.Desc (Chain KindName FileDescription)
open ProofFile.Honest.Term (matrixInput baseMaker baseFilling)
open ProofFile.Honest.FirstThread (HeadAtReturn firstThread)
open OnBytes.SendSim.At OnBytes.SendSim.Seat
open ProofFile.Honest.K1 ProofFile.Honest.K1.Sim
open AtPublicFiles.TheSides (Letters theSides overlaySlots overlayLot find_name rows_of_overlay KindRows
  castSides castSides_of)
open AtPublicFiles.TheG (ThreadParts theLetters theG theGOfReturn)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge

/-- The owner's kind's first lot with its simulators, at the base filling: the first segment's
opening, each link's reads and digits. -/
noncomputable abbrev k1LotAtBase :
    SLot (Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit Inst :=
  K1.Sim.lotS matrixInput id id OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref

/-- The owner's kind's second lot with its simulator, at the base filling: the sending of W. -/
noncomputable abbrev wLotAtBase :
    SLot (Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit Inst :=
  K1.Sim.wS matrixInput id id OnBytes.secondHashFunction openHonest

/-! ## 1 A value of the kinds' rows that lays the three lots -/

/-- **A lot of the base filling that bears the name of one of the kind K1's two lots is that lot of
the filling.** No premise: the thirteen names are told apart one by one. -/
theorem k1_slots_by_name :
    ∀ L ∈ (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref
      openHonest).lots,
      (L.name = k1LotAtBase.name → L = HLot.byPub matrixInput.weights
        (LongLots.plain (X := Unit) OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest).k1) ∧
      (L.name = wLotAtBase.name →
        L = wLotAt (X := Unit) matrixInput OnBytes.secondHashFunction openHonest) := by
  intro L hL
  rw [widerFillAtCPUOWM_lots, widerFillAt_lots] at hL
  simp only [widerPairs, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hL
  rcases hL with (((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl) | rfl) | rfl
  all_goals
    refine ⟨fun hn => ?_, fun hn => ?_⟩ <;> first | exact absurd hn (by decide) | rfl

/-- **A value of the kinds' rows that lays the kind's lot and its owner's kind's two lots exists**,
at the base filling, at every public part and ground. It lays these three alone. -/
theorem kindRowsWithK13sAndItsOwnersLotsExist (files : VerifierAndGoals.PublicFiles) (Zq : Pub) (G : Ground) :
    ∃ K : KindRows (baseFilling files) Zq G,
      k13LotAtBase Zq ∈ K.lots ∧ k1LotAtBase ∈ K.lots ∧ wLotAtBase ∈ K.lots :=
  ⟨{ lots := [k13LotAtBase Zq, k1LotAtBase, wLotAtBase]
     named := fun s hs => by
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
       rcases hs with rfl | rfl | rfl <;> rfl
     apart := by
       show ["K13: the members' batching", k1LotAtBase.name, wLotAtBase.name].Nodup
       decide
     lots_fit := fun L hL s hs => by
       have hm := List.mem_of_find?_eq_some hs
       have hb := List.find?_some hs
       have hp : s.name = L.name := beq_iff_eq.1 hb
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
       rcases hm with rfl | rfl | rfl
       · rw [k13_slot_by_name L hL hp.symm]
         exact k13SLot_halves _ _ Zq G
       · rw [(k1_slots_by_name L hL).1 hp.symm]
         exact congrFun (congrFun (congrArg HLot.halves
           (K1.Sim.lotS_toHLot_base matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref
             openHonest)) Zq) G
       · rw [(k1_slots_by_name L hL).2 hp.symm]
         exact congrFun (congrFun (congrArg HLot.halves
           (K1.Sim.wS_toHLot_base matrixInput OnBytes.secondHashFunction openHonest)) Zq) G
     shared := []
     shared_named := fun _ hr => by cases hr
     shared_apart := by simp
     shared_fit := fun _ _ _ hr => by simp at hr
     second := []
     second_named := fun _ hr => by cases hr
     second_apart := by simp
     second_fit := fun _ _ _ hr => by simp at hr },
    List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self,
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩

/-! ## 2 The owner's field fresh at the kind's address, at the lists -/

/-- **At each list of the first chain at a place of the kind K1, at each side of it: the field fresh
of `Good` at the one address ⟨⟨1, none, 3, .K13⟩, 1⟩**, the kind's second part's, at the list's own
bound: over the sender's own coins, the blocks that this part spends are uniform and independent of
what the sender shows together with what is known at that address. A definition, meant as a
theorem's end. -/
def OwnerFreshAtK13 {W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Inst} {Bk : ProverCoinCounts}
    (G : Sides F Bk W₀ Rc Ky Tr X₀ X) : Prop :=
  ∀ L ∈ G.first, L.place.kind = .K1 → ∀ σ, L.side F.first.blocksInOrder G.falls₁ = some σ →
    FreshAtP .own σ Bk (orderOf F) L.bud ⟨⟨1, none, 3, .K13⟩, 1⟩

/-- **A list stands at the owner's place, the first segment's opening's, and has a side over the
description.** A definition, meant as a theorem's end. -/
def OwnerStands {W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Inst} {Bk : ProverCoinCounts}
    (G : Sides F Bk W₀ Rc Ky Tr X₀ X) : Prop :=
  ∃ L ∈ G.first, L.place = ⟨1, some 0, 1, .K1⟩ ∧ ∃ σ, L.side F.first.blocksInOrder G.falls₁ = some σ

/-- Of the base filling's thirteen lots each either bears the name of one of the kind K1's two lots
or lays no side at a place of that kind. No premise. -/
theorem otherLotsLayNoSideOfK1 (Zq : Pub) (G : Ground) :
    ∀ M ∈ (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref
      openHonest).lots,
      (∃ l ∈ [k1LotAtBase, wLotAtBase], l.name = M.name) ∨
        ∀ x ∈ M.halves Zq G, x.place.kind ≠ .K1 := by
  intro M hM
  by_cases hx : ∃ x ∈ M.halves Zq G, x.place.kind = .K1
  · obtain ⟨x, hx, hk⟩ := hx
    have hp := k1_pairs _ _ _ _ M (lot_of_kind _ _ _ _ Zq G M hM x hx hk)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact Or.inl ⟨_, List.mem_cons_self, rfl⟩
    · exact Or.inl ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
  · exact Or.inr fun x hx' hk => hx ⟨x, hx', hk⟩

section
variable {files : VerifierAndGoals.PublicFiles} (scope : VerifierAndGoals.InScope files = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (made : baseMaker files = .ok returned)
    (mine : List (SLot (Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit Inst))
    (named : ∀ s ∈ mine, (baseFilling files).lots.any (fun L => L.name == s.name) = true)
    (apart : (mine.map (·.name)).Nodup)
    (hm : ∀ L ∈ (baseFilling files).lots, ∀ s,
      (mine.find? fun s => s.name == L.name) = some s →
      (s.rows returned.Z returned.G).map (·.half) = L.halves returned.Z returned.G)
    (shared : List (Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins OnBytes.TableKey) Unit OnBytes.TableKey))
    (hs : shared.map (·.half) = (baseFilling files).shared returned.Z returned.G)
    (second : List (Unlettered (Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit Inst))
    (h₃ : second.map (·.half) = (baseFilling files).second returned.Z returned.G)
    {F₀ : FileDescription Inst} (same : returned.F = F₀)
    (Ls : Letters F₀ returned.B FullSizeMatrix IndexCommitterCoins OnBytes.TableKey Cells Unit Unit)
    (f₁ : List (Fall F₀.S₁)) (f₂ : List (Fall F₀.S₂)) (f₃ : List (Fall F₀.S₃))
    (laid₁ : k1LotAtBase ∈ mine) (laidW : wLotAtBase ∈ mine)
include scope live made same laid₁ laidW

/-- CONDITIONAL: in scope; live; the base maker's return; the kind K1's two lots are among the lots
laid over the filling's; the letters leave their rows as they are. **The owner's field fresh at the
kind's address, at the lists.** -/
theorem ownerFreshAtK13_at_the_sides
    (whole : ∀ u ∈ rowsOfLots returned.Z returned.G [k1LotAtBase, wLotAtBase],
      (Ls.first u).bare = u) :
    OwnerFreshAtK13 (theSides F₀ Ls
      (overlaySlots (baseFilling files) returned.Z returned.G mine named apart hm shared hs second
        h₃).rows f₁ f₂ f₃) := by
  subst same
  intro L hL hk σ hσ
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hL
  rw [(Ls.keeps₁ u).1] at hk
  obtain ⟨l, hl, hul⟩ := rows_of_overlay (ls := [k1LotAtBase, wLotAtBase]) apart
    (fun l hl => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact laid₁
      · exact laidW) hm (otherLotsLayNoSideOfK1 returned.Z returned.G) u hu hk
  have hur : u ∈ rowsOfLots returned.Z returned.G [k1LotAtBase, wLotAtBase] :=
    List.mem_flatMap.2 ⟨l, hl, hul⟩
  have eb : (Ls.first u).bud = u.bud := congrArg Unlettered.bud (whole u hur)
  rw [K1.Sim.rows_eq] at hur
  obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hur
  have seated : Side.seated returned.F.first.blocksInOrder
      (jobRow (V := Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Pb := Inst)
        (K1.Sim.witAt matrixInput id id returned.Z) J).place
      (jobRow (V := Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Pb := Inst)
        (K1.Sim.witAt matrixInput id id returned.Z) J).row f₁ = some σ := by
    rw [← (Ls.keeps₁ _).1, ← (Ls.keeps₁ _).2]
    exact hσ
  rw [eb]
  exact AtFullSide.K1.owner_fresh_at_return scope live matrixInput id id _ openHonest made .own f₁ _
    J hJ σ seated

omit laidW in
/-- CONDITIONAL: as above, without the premise on the second lot. Th: any family of threads over the
description; nothing is read of it. **A list stands at the owner's place, with a side.** -/
theorem ownerStands_at_the_sides
    (Th : Local FullSizeMatrix IndexCommitterCoins Inst Cells → Thread returned.B F₀.S₁ F₀.Cl (Local FullSizeMatrix IndexCommitterCoins Inst Cells)
      (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit Inst) :
    OwnerStands (theSides F₀ Ls
      (overlaySlots (baseFilling files) returned.Z returned.G mine named apart hm shared hs second
        h₃).rows f₁ f₂ f₃) := by
  subst same
  obtain ⟨J, hJ, hplace⟩ : ∃ J ∈ ProofFile.Honest.K1.lotJobs (X := Unit)
      (lotNo OnBytes.secondHashFunction returned.Z) (lotData OnBytes.HonestTrace.Sz.ref) returned.Z returned.G,
      (jobRow (V := Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Pb := Inst)
        (witAt matrixInput id id returned.Z) J).place = ⟨1, some 0, 1, .K1⟩ :=
    ⟨_, List.mem_cons_self, rfl⟩
  have block := (handIn_at_return (pre₀ := []) scope live matrixInput id id
    OnBytes.HonestTrace.Sz.ref openHonest made .own returned.B [] 0 0 Th (fun _ _ _ _ => True) f₁ J
    (List.mem_append_left _ hJ) _ rfl).1
  rw [hplace] at block
  have found : overlayLot mine (HLot.byPub matrixInput.weights
      (LongLots.plain (X := Unit) OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest).k1) =
      k1LotAtBase := by
    unfold overlayLot
    have f' : (mine.find? fun t => t.name == (HLot.byPub matrixInput.weights
        (LongLots.plain (X := Unit) OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref
          openHonest).k1).name) = some k1LotAtBase := find_name apart laid₁
    rw [f']
  have inLots : HLot.byPub matrixInput.weights
      (LongLots.plain (X := Unit) OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest).k1 ∈
      (baseFilling files).lots := by
    rw [fillPairs_lots]
    exact List.mem_map.2 ⟨(_, .K1), List.mem_append_left _ (List.Mem.head _), rfl⟩
  have inRows : jobRow (V := Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Pb := Inst)
      (witAt matrixInput id id returned.Z) J ∈ rowsOfLots returned.Z returned.G
        ((baseFilling files).lots.map (overlayLot mine)) :=
    List.mem_flatMap.2 ⟨_, List.mem_map.2 ⟨_, inLots, found⟩, List.mem_map_of_mem hJ⟩
  have some : (returned.F.first.blocksInOrder.find? fun b => b.place == ⟨1, some 0, 1, .K1⟩).isSome =
      true := by
    rw [List.find?_isSome]
    exact List.any_eq_true.1 block
  obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.1 some
  have atPlace := (Ls.keeps₁ (jobRow (V := Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Pb := Inst)
    (witAt matrixInput id id returned.Z) J)).1.trans hplace
  refine ⟨_, List.mem_map_of_mem inRows, atPlace, Option.isSome_iff_exists.1 ?_⟩
  show (Side.seated returned.F.first.blocksInOrder _ _ f₁).isSome = true
  unfold Side.seated
  rw [atPlace, hb']
  rfl

end

/-! ## 3 At the lists by their name -/

/-- CONDITIONAL: in scope; live; the base maker's return, with the head; the kind K1's two lots are
among the lots that the kinds lay. **The owner's field fresh at the kind's address, at
`theGOfReturn made h T K`.** No premise that the kind K1 pays. -/
theorem ownerFreshAtK13_at_theGOfReturn {Wt : Type} {files : VerifierAndGoals.PublicFiles}
    (scope : VerifierAndGoals.InScope files = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (made : baseMaker files = .ok returned)
    (h : HeadAtReturn files returned) (T : ThreadParts returned Wt)
    (K : KindRows (baseFilling files) returned.Z returned.G)
    (laid₁ : k1LotAtBase ∈ K.lots) (laidW : wLotAtBase ∈ K.lots) :
    OwnerFreshAtK13 (theGOfReturn made h T K) :=
  castSides_of (Q := fun _ G => OwnerFreshAtK13 G) (atPure_at_laid h.head.laid made).2
    (ownerFreshAtK13_at_the_sides scope live made K.lots K.named K.apart K.lots_fit _ _ _ _
      (atPure_at_laid h.head.laid made).2 (theLetters h T) _ _ _ laid₁ laidW fun _ _ => rfl)

/-- **A list stands at the owner's place in `theGOfReturn made h T K`, with a side.** -/
theorem ownerStands_at_theGOfReturn {Wt : Type} {files : VerifierAndGoals.PublicFiles}
    (scope : VerifierAndGoals.InScope files = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (made : baseMaker files = .ok returned)
    (h : HeadAtReturn files returned) (T : ThreadParts returned Wt)
    (K : KindRows (baseFilling files) returned.Z returned.G) (laid₁ : k1LotAtBase ∈ K.lots) :
    OwnerStands (theGOfReturn made h T K) :=
  castSides_of (Q := fun _ G => OwnerStands G) (atPure_at_laid h.head.laid made).2
    (ownerStands_at_the_sides scope live made K.lots K.named K.apart K.lots_fit _ _ _ _
      (atPure_at_laid h.head.laid made).2 (theLetters h T) _ _ _ laid₁ (firstThread h T.first))

/-- **With no premise on the kinds' rows**: in scope, live, at the base maker's return with the
head, there is a value K of the kinds' rows at which the kind's row stands with a side, the kind
pays, a list stands at the owner's place with a side, and the owner's field fresh holds at the
kind's address. -/
theorem k13_and_its_owner_at_some_rows {Wt : Type} {files : VerifierAndGoals.PublicFiles}
    (scope : VerifierAndGoals.InScope files = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (made : baseMaker files = .ok returned)
    (h : HeadAtReturn files returned) (T : ThreadParts returned Wt) :
    ∃ K : KindRows (baseFilling files) returned.Z returned.G,
      K13Stands (theGOfReturn made h T K)
        ((k13LotAtBase returned.Z).rows returned.Z returned.G) ∧
      VerifiableInference.Compilation.KindPays (theGOfReturn made h T K) .K13 ∧
      OwnerStands (theGOfReturn made h T K) ∧ OwnerFreshAtK13 (theGOfReturn made h T K) := by
  obtain ⟨K, laid, laid₁, laidW⟩ :=
    kindRowsWithK13sAndItsOwnersLotsExist files returned.Z returned.G
  exact ⟨K, k13Stands_at_theGOfReturn made h T K laid, k13KindPays_at_theGOfReturn made h T K laid,
    ownerStands_at_theGOfReturn scope live made h T K laid₁,
    ownerFreshAtK13_at_theGOfReturn scope live made h T K laid₁ laidW⟩

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_and_its_owner_at_some_rows
#print axioms ProofFile.Honest.K13.OwnerStands
#print axioms ProofFile.Honest.K13.ownerStands_at_the_sides
#print axioms ProofFile.Honest.K13.ownerStands_at_theGOfReturn
#print axioms ProofFile.Honest.K13.k1_slots_by_name
#print axioms ProofFile.Honest.K13.kindRowsWithK13sAndItsOwnersLotsExist
#print axioms ProofFile.Honest.K13.OwnerFreshAtK13
#print axioms ProofFile.Honest.K13.otherLotsLayNoSideOfK1
#print axioms ProofFile.Honest.K13.ownerFreshAtK13_at_the_sides
#print axioms ProofFile.Honest.K13.ownerFreshAtK13_at_theGOfReturn
