-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K13/Term/KindPaysAtTheG.lean: the members' batching (kind K13): what
the kind pays toward the statement on zero knowledge, at the lists of all kinds' rows by their name
(`theGAtBase`, `theGOfReturn`, E2E/TheG.lean), at a return of the maker at the base filling
(`baseMaker`, E2E/BaseMaker.lean) with the library's head (`HeadAtReturn`,
Johnson/Desc/ProofFile/Honest/Thread/TheFirstThread.lean). One definition; statements with their
proofs.

The rule that yields `Owed` from the kinds (Johnson/T3/OwedOfKinds.lean,
Johnson/Desc/ProofFile/Honest/Law/OwedAtRun.lean) asks three things of each kind, at one G:
  * `KindPays G κ`: at each list at a place of the kind: the list fits its block, each part has a
    simulator that is exact, each owner is fresh (the fields fits, exact and fresh of `Good`);
  * `KindBud G κ` (Johnson/M1/BudGather.lean): the kind's share of the clause on the bound `bud`;
  * `KindOnAtEveryRun Rel T κ` (Johnson/Desc/ProofFile/Honest/Law/UseByKind.lean): the kind's share
    of "On holds at every run".
Here all three at κ := K13, under one premise on the kinds' rows K: the kind's own lot with its
simulators is among the lots that K lays.

  `k13LotAtBase`   the kind's lot with its simulators (`k13SLot`, RowsLot.lean of the folder above),
     at the base filling's reader of the index and filler of the pile
  `otherLotsLayNoSideOfK13`   of the base filling's thirteen lots each either bears the name of the
     kind's lot or lays no side at a place of the kind. No premise
  `k13_on_at`   at a row of the lot `On` holds always
  `k13KindPays_at_the_sides`, `k13ListsBear_at_the_sides`   at the lists built from the filling's
     lots with any lots laid over them, at the head's description, at any falls; at letters that
     narrow `On` and `bud` at the kind's row (the first), that leave the row as it is (the second)
  `k13KindBud_of_bear`, `k13OnAtEveryRun_of_bear`   the two conditions of use, at any lists G whose
     lists of the kind are the lot's rows
  `k13KindPays_at_theGAtBase`, `k13KindPays_at_theGOfReturn`   **`KindPays G .K13`**
  `k13ListsBear_at_theGOfReturn`   each list of the kind at that G is the lot's one row, in the
     first chain alone
  `k13KindBud_at_theGOfReturn`   **`KindBud G .K13`**
  `k13OnAtEveryRun_at_theGOfReturn`   **`KindOnAtEveryRun Rel T .K13`**, at every relation, every
     prover beside the lists and every family of invariants
  `OwnerFreshK13`, `k13OwnerFresh_of_the_owners_kind`, `k13OwnerFresh_at_theGOfReturn`   **the coins
     that the kind's second part spends are fresh**, in the sense of the field fresh of `Good` at
     their owner: CONDITIONAL on `KindPays G .K1`: by the returned book every part of whose coins
     that part spends is the first segment's opening, which stands at a place of the kind K1

Limits.
  * h (the head at the return), the threads' parts T and the kinds' rows K are arguments: no value
    of them is given here. `laid` is a premise on K: whoever lays K owes it.
  * At the base filling's return, not at the return of the maker from which the honest prover for a
    request is made: that filling is this one read through, at another type of the table's coins.
  * `KindPays` leaves the fields plays and acc of `Good` unasked. Of fresh: the kind's two parts own
    no coin, so the field fresh at the kind's own list says next to nothing; the coins that the
    second part spends are entries of the index-mask message, and that these are fresh is the field
    fresh at their owner's list, a list of the kind K1: here it is drawn from `KindPays G .K1`,
    which is a premise.
  * `k13KindPays_at_the_sides` is general in the letters, under a premise that lets them narrow `On`
    and `bud`: at letters whose `On` or `bud` never holds the fields exact and fresh ask nothing,
    and the statement is met for nothing. At the lists by their name this does not bite: the
    threads' letters keep the row's `On` and `bud`.
  * All ends begin "at each list at a place of the kind": that such a list stands, with a side, is
    StandsAtTheG.lean's of this folder; that the premise `laid` can be met, too. Nothing shows that
    a run ever calls the kind's parts.
  * `OwnerFreshK13` is one projection of its premise, that the kind K1 pays: it pays nothing, and
    nothing takes it. Where the opening's job does not fit its place the owner shows the error
    value, and fresh speaks of coins alone; that it fits is `fits_at_return`
    (Johnson/Desc/ProofFile/Honest/K1/Sim/ShowsAtReturn.lean). The owner's field at the kind's
    address, without that premise, is OwnerAtTheG.lean's of this folder.
  * `On` and `bud` of the kind ask nothing (`k13On`, `k13Bud`): so the two conditions of use hold
    for that reason. It is lawful here because the kind's parts open no masked tree, and exact is
    shown at every state (Exact.lean, Fields.lean of the folder above).
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import E2E.TheG
import E2E.KindPaysOfALot
import Johnson.M1.BudGather
import Johnson.Desc.ProofFile.Honest.Law.UseByKind
import Johnson.Desc.ProofFile.Honest.Law.FillPairs
import AtFullSide.K13.AtBaseFilling
import AtFullSide.K13.EntryAtBook

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13
open VerifiableInference.Desc (Chain KindName FileDescription)
open VerifiableInference.Compilation (KindPays)
open ProofFile.Honest.Term (matrixInput theGAtBase baseMaker baseFilling)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open AtPublicFiles.TheSides (Letters theSides overlaySlots Narrows narrows_of_bare KindRows castSides
  castSides_of kindPays_of_rows rows_of_overlay block_of_seated)
open AtPublicFiles.TheG (ThreadParts theLetters theG theGOfReturn)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge

/-- **The kind's lot with its simulators, at the base filling's reader of the index and filler of
the pile.** Z: the public part at which the reader is taken. -/
noncomputable abbrev k13LotAtBase (Z : Pub) :
    SLot (Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit Inst :=
  k13SLot (matrixInput.weights Z) openHonest.pile

/-- **Of the base filling's thirteen lots, each either bears the name of the kind's lot or lays no
side at a place of the kind K13.** No premise. The proof has more in the first case: the lot is the
filling's lot of the kind itself. -/
theorem otherLotsLayNoSideOfK13 {W₀ : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (Zq : Pub) (G : Ground) :
    ∀ M ∈ (onlineProverPartsInUse I o S O).lots,
      M.name = "K13: the members' batching" ∨ ∀ x ∈ M.halves Zq G, x.place.kind ≠ .K13 := by
  intro M hM
  rcases lot_alone I o S O (pair_only I o S O (k13FillLot_pair I o S O) (by decide)) Zq G M hM with
    rfl | none
  · exact Or.inl rfl
  · exact Or.inr none

/-- At a row of the kind's lot `On` holds always. -/
theorem k13_on_at {W₀ Rc Tr X Pb : Type} (weights : W₀ → Weights)
    (pile : Pub → Ground → PileOf Inst) (Zq : Pub) (G : Ground) :
    ∀ r ∈ (k13SLot (Rc := Rc) (Tr := Tr) (X := X) (Pb := Pb) weights pile).rows Zq G,
      ∀ u ca m front, r.On u ca m front := by
  intro r hr
  obtain rfl := List.mem_singleton.1 hr
  exact fun _ _ _ _ => trivial

/-! ## 1 At the lists built from the filling's lots -/

section
variable {files : VerifierAndGoals.PublicFiles} {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (made : baseMaker files = .ok returned) (h : HeadAtReturn files returned)
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
    (Ls : Letters h.description returned.B FullSizeMatrix IndexCommitterCoins OnBytes.TableKey Cells Unit Unit)
    (f₁ : List (Fall h.description.S₁)) (f₂ : List (Fall h.description.S₂))
    (f₃ : List (Fall h.description.S₃))
    (laid : k13LotAtBase returned.Z ∈ mine)
include made laid

omit made in
/-- A row of the kind among the rows that the overlay lays is a row of the kind's lot. -/
theorem k13_row_of_overlay :
    ∀ u ∈ (overlaySlots (baseFilling files) returned.Z returned.G mine named apart hm shared hs
        second h₃).rows.first, u.place.kind = .K13 →
      u ∈ (k13LotAtBase returned.Z).rows returned.Z returned.G := by
  intro u hu hk
  obtain ⟨l, hl, hul⟩ := rows_of_overlay (ls := [k13LotAtBase returned.Z]) apart
    (fun l hl => by rw [List.mem_singleton.1 hl]; exact laid) hm
    (fun M hM => by
      rcases otherLotsLayNoSideOfK13 matrixInput _ _ _ returned.Z returned.G M hM with name | none
      · exact Or.inl ⟨_, List.mem_singleton.2 rfl, name.symm⟩
      · exact Or.inr none) u hu hk
  obtain rfl := List.mem_singleton.1 hl
  exact hul

/-- CONDITIONAL: the base maker's return, with the head; the kind's lot is among the lots laid over
the filling's; the letters narrow On and bud at the kind's row. **`KindPays G .K13`.** -/
theorem k13KindPays_at_the_sides
    (narrows : ∀ u ∈ (k13LotAtBase returned.Z).rows returned.Z returned.G, Narrows (Ls.first u) u) :
    KindPays (theSides h.description Ls
      (overlaySlots (baseFilling files) returned.Z returned.G mine named apart hm shared hs second
        h₃).rows f₁ f₂ f₃) .K13 := by
  refine kindPays_of_rows Ls _ f₁ f₂ f₃ .K13 (fun u hu hk σ hσ => ?_) (fun u _ hk σ hσ => ?_)
    (fun u _ hk σ hσ => ?_)
  · have hul := k13_row_of_overlay mine named apart hm shared hs second h₃ laid u hu hk
    exact ⟨narrows u hul, _, _,
      (k13_good_rows_atPure h.head made _ _ returned.G _ .own _ 0 0 f₁ u hul).2 σ hσ⟩
  · obtain ⟨b, hb, e⟩ := block_of_seated hσ
    exact absurd (by rw [e]; exact hk) ((k13_places_of_kind h.head).2.1 b hb)
  · obtain ⟨b, hb, e⟩ := block_of_seated hσ
    exact absurd (by rw [e]; exact hk) ((k13_places_of_kind h.head).2.2 b hb)

/-- CONDITIONAL: as above, and the letters leave the kind's row as it is. **The lists of the kind at
that G are the lot's rows, in the first chain alone.** -/
theorem k13ListsBear_at_the_sides
    (whole : ∀ u ∈ (k13LotAtBase returned.Z).rows returned.Z returned.G, (Ls.first u).bare = u) :
    ListsOfTheKindBear (theSides h.description Ls
      (overlaySlots (baseFilling files) returned.Z returned.G mine named apart hm shared hs second
        h₃).rows f₁ f₂ f₃) .K13 ((k13LotAtBase returned.Z).rows returned.Z returned.G) := by
  obtain ⟨-, -, -, -, -, -, -, -, e₂, e₃, -⟩ := atPure_ok made
  obtain ⟨n₂, n₃⟩ := k13_none_elsewhere h.head made
  refine ⟨?_, ?_, ?_⟩
  · intro L hL hk
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hL
    rw [(Ls.keeps₁ u).1] at hk
    have hul := k13_row_of_overlay mine named apart hm shared hs second h₃ laid u hu hk
    rw [whole u hul]
    exact hul
  · intro L hL hk
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hL
    rw [(Ls.keeps₂ u).1] at hk
    have side : u.half ∈ returned.H.shared := by
      rw [e₂, ← hs]
      exact List.mem_map_of_mem hu
    have : u.half ∈ returned.H.shared.filter atK13 :=
      List.mem_filter.2 ⟨side, by unfold atK13; exact beq_iff_eq.2 hk⟩
    rw [n₂] at this
    cases this
  · intro L hL hk
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hL
    rw [(Ls.keeps₃ u).1] at hk
    have side : u.half ∈ returned.H.second := by
      rw [e₃, ← h₃]
      exact List.mem_map_of_mem hu
    have : u.half ∈ returned.H.second.filter atK13 :=
      List.mem_filter.2 ⟨side, by unfold atK13; exact beq_iff_eq.2 hk⟩
    rw [n₃] at this
    cases this

end

/-! ## 2 The two conditions of use, at any lists that bear the lot's rows -/

section
variable {W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Inst} {Bk : ProverCoinCounts}
  {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {weights : W₀ → Weights} {pile : Pub → Ground → PileOf Inst}
  {Zq : Pub} {Gr : Ground}

/-- CONDITIONAL on the lists. **The kind's share of the clause on `bud`, in all three chains.** In
the shared and the second chain it holds for want of a list of the kind. -/
theorem k13KindBud_of_bear
    (bear : ListsOfTheKindBear G .K13 ((k13SLot weights pile).rows Zq Gr)) :
    Johnson.M1.KindBud G .K13 :=
  ⟨fun L hL hk =>
      Johnson.M1.budOwed_true F L (k13_bud_at weights pile Zq Gr L.bare (bear.first L hL hk)),
    fun L hL e => absurd e (bear.noneShared L hL), fun L hL e => absurd e (bear.noneSecond L hL)⟩

/-- CONDITIONAL on the lists. **The kind's share of "On at every run"**: at every relation, every
prover beside the lists and every family of invariants. -/
theorem k13OnAtEveryRun_of_bear
    (bear : ListsOfTheKindBear G .K13 ((k13SLot weights pile).rows Zq Gr))
    {H : Prover W₀ Rc Inst Ky Tr X₀ X} (Rel : W₀ → Rc → Inst → Prop)
    (T : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      ThreadsP F Bk (G.prover H) w₀ rc x k R) :
    KindOnAtEveryRun (G := G) (H := H) Rel T .K13 :=
  fun w₀ rc x hrel k R hR ρ r _ _ _ =>
    kindOnAtRun_of_rows bear (fun L hL => k13_on_at weights pile Zq Gr L.bare hL)
      (T w₀ rc x hrel k R hR) ρ r

end

/-! ## 3 At G by its name -/

section
variable {Wt : Type} {files : VerifierAndGoals.PublicFiles} {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (made : baseMaker files = .ok returned) (h : HeadAtReturn files returned)
    (T : ThreadParts returned Wt) (K : KindRows (baseFilling files) returned.Z returned.G)
    (laid : k13LotAtBase returned.Z ∈ K.lots)
include made laid

/-- CONDITIONAL: the base maker's return, with the head; the kind's lot is among the lots that the
kinds lay. **`KindPays (theGAtBase h T K) .K13`.** -/
theorem k13KindPays_at_theGAtBase : KindPays (theGAtBase h T K) .K13 :=
  k13KindPays_at_the_sides made h K.lots K.named K.apart K.lots_fit _ _ _ _ (theLetters h T) _ _ _
    laid fun _ _ => narrows_of_bare rfl

/-- **The same at the description that the return holds.** These are the lists, by type, that a
statement on zero knowledge from the base filling would take; this file states none; the statement
at the honest
prover's own return (Johnson/T3/OwedOfKinds.lean) takes lists at another type of the table's coins.
-/
theorem k13KindPays_at_theGOfReturn : KindPays (theGOfReturn made h T K) .K13 :=
  castSides_of (Q := fun _ G => KindPays G .K13) (atPure_at_laid h.head.laid made).2
    (k13KindPays_at_theGAtBase made h T K laid)

/-- **The lists of the kind at that G are the lot's rows, in the first chain alone.** -/
theorem k13ListsBear_at_theGOfReturn :
    ListsOfTheKindBear (theGOfReturn made h T K) .K13
      ((k13LotAtBase returned.Z).rows returned.Z returned.G) :=
  castSides_of (Q := fun _ G => ListsOfTheKindBear G .K13
      ((k13LotAtBase returned.Z).rows returned.Z returned.G))
    (atPure_at_laid h.head.laid made).2
    (k13ListsBear_at_the_sides made h K.lots K.named K.apart K.lots_fit _ _ _ _ (theLetters h T) _ _
      _ laid fun _ _ => rfl)

/-- **`KindBud (theGOfReturn made h T K) .K13`.** -/
theorem k13KindBud_at_theGOfReturn : Johnson.M1.KindBud (theGOfReturn made h T K) .K13 :=
  k13KindBud_of_bear (k13ListsBear_at_theGOfReturn made h T K laid)

/-- **The kind's share of "On at every run" at that G.** -/
theorem k13OnAtEveryRun_at_theGOfReturn
    {H : Prover FullSizeMatrix IndexCommitterCoins Inst OnBytes.TableKey Cells Unit Unit} (Rel : FullSizeMatrix → IndexCommitterCoins → Inst → Prop)
    (Th : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R,
      ready returned.F returned.B ((theGOfReturn made h T K).prover H) w₀ rc x k = .ok R →
      ThreadsP returned.F returned.B ((theGOfReturn made h T K).prover H) w₀ rc x k R) :
    KindOnAtEveryRun (G := theGOfReturn made h T K) (H := H) Rel Th .K13 :=
  k13OnAtEveryRun_of_bear (k13ListsBear_at_theGOfReturn made h T K laid) Rel Th

end

/-! ## 4 The owner's debt, from the owner's kind -/

/-- A list's side stands at the list's place. -/
theorem side_at_the_lists_place {Bk : ProverCoinCounts} {S Cl V W Y Pb : Type} {L : Lettered Bk S Cl V W Y Pb}
    {bs : List (VerifiableInference.Desc.Block S Cl)} {fs : List (Fall S)} {σ : Side S Cl V W Y Pb}
    (h : L.side bs fs = some σ) : σ.block.place = L.place := by
  unfold Lettered.side Side.seated at h
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h
  exact eq_of_beq (List.find?_some (p := fun b : VerifiableInference.Desc.Block S Cl =>
    b.place == L.place) hb)

/-- **The coins that the kind's second part spends are fresh at their owner**: at each list of the
first chain, each side of it and each member of whose coins the part at ⟨⟨1, none, 3, .K13⟩, 1⟩
spends any by the book: the field fresh of `Good` at that member, at the list's own bound. A
definition, meant as a theorem's end. The kind's first part spends no coin (`k13_entry_at_book`,
AtFullSide/K13/EntryAtBook.lean). -/
def OwnerFreshK13 {W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Inst} {Bk : ProverCoinCounts}
    (G : Sides F Bk W₀ Rc Ky Tr X₀ X) : Prop :=
  ∀ L ∈ G.first, ∀ σ, L.side F.first.blocksInOrder G.falls₁ = some σ → ∀ u ∈ σ.members,
    Bk.spentBy ⟨σ.block.place, u.number⟩ ⟨⟨1, none, 3, .K13⟩, 1⟩ ≠ [] →
    Small.FreshMember .own σ Bk (orderOf F) L.bud u

/-- CONDITIONAL: other: by the book, of no part's coins but the first segment's opening's does the
kind's second part spend any; THE OWNER's KIND PAYS. **`OwnerFreshK13 G`.** One projection. -/
theorem k13OwnerFresh_of_the_owners_kind {W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Inst} {Bk : ProverCoinCounts}
    {G : Sides F Bk W₀ Rc Ky Tr X₀ X}
    (other : ∀ o : Addr, o ≠ ⟨⟨1, some 0, 1, .K1⟩, 0⟩ →
      Bk.spentBy o ⟨⟨1, none, 3, .K13⟩, 1⟩ = [])
    (ownersKindPays : KindPays G .K1) : OwnerFreshK13 G := by
  intro L hL σ hσ u hu spends
  have owner : (⟨σ.block.place, u.number⟩ : Addr) = ⟨⟨1, some 0, 1, .K1⟩, 0⟩ := by
    by_contra hne
    exact spends (other _ hne)
  have place : σ.block.place = ⟨1, some 0, 1, .K1⟩ := congrArg Addr.place owner
  have kind : L.place.kind = .K1 := by
    rw [← side_at_the_lists_place hσ, place]
  obtain ⟨A', B', good⟩ := ownersKindPays.1 L hL kind σ hσ
  exact good.fresh u hu

/-- **The same at G by its name**, at the base maker's return with the head. -/
theorem k13OwnerFresh_at_theGOfReturn {Wt : Type} {files : VerifierAndGoals.PublicFiles}
    {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (made : baseMaker files = .ok returned)
    (h : HeadAtReturn files returned) (T : ThreadParts returned Wt)
    (K : KindRows (baseFilling files) returned.Z returned.G)
    (ownersKindPays : KindPays (theGOfReturn made h T K) .K1) :
    OwnerFreshK13 (theGOfReturn made h T K) :=
  k13OwnerFresh_of_the_owners_kind
    (fun _ ho => AtFullSide.K13.k13_spentBy_other h.head (K14.atPure_book_at_head h.head made) ho)
    ownersKindPays

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13LotAtBase
#print axioms ProofFile.Honest.K13.otherLotsLayNoSideOfK13
#print axioms ProofFile.Honest.K13.k13_on_at
#print axioms ProofFile.Honest.K13.k13_row_of_overlay
#print axioms ProofFile.Honest.K13.k13KindPays_at_the_sides
#print axioms ProofFile.Honest.K13.k13ListsBear_at_the_sides
#print axioms ProofFile.Honest.K13.k13KindBud_of_bear
#print axioms ProofFile.Honest.K13.k13OnAtEveryRun_of_bear
#print axioms ProofFile.Honest.K13.k13KindPays_at_theGAtBase
#print axioms ProofFile.Honest.K13.k13KindPays_at_theGOfReturn
#print axioms ProofFile.Honest.K13.k13ListsBear_at_theGOfReturn
#print axioms ProofFile.Honest.K13.k13KindBud_at_theGOfReturn
#print axioms ProofFile.Honest.K13.k13OnAtEveryRun_at_theGOfReturn
#print axioms ProofFile.Honest.K13.side_at_the_lists_place
#print axioms ProofFile.Honest.K13.OwnerFreshK13
#print axioms ProofFile.Honest.K13.k13OwnerFresh_of_the_owners_kind
#print axioms ProofFile.Honest.K13.k13OwnerFresh_at_theGOfReturn
