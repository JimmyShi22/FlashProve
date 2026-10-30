-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K11/KindPaysAtTheG.lean: what the kind K11 pays toward the statement on zero knowledge, at
the lists of all kinds' rows by their name (theGAtBase, theGOfReturn, E2E/TheG.lean), at a return of
the maker at the base filling with the library's head. Under one premise on the kinds' rows K: the
kind's lot with its simulator is among the lots that K lays.

  k11LotAtBase, otherLotsLayNoSideOfK11, k11_on_at, k11_bud_at
  k11_good_at_row                  Good at the kind's row, at any list in front and any order
  k11KindPays_at_the_sides, k11ListsBear_at_the_sides
  k11KindPays_at_theGOfReturn      KindPays G .K11
  k11ListsBear_at_theGOfReturn     each list of the kind at that G is the lot's one row
  k11KindBud_at_theGOfReturn       KindBud G .K11
  k11OnAtEveryRun_at_theGOfReturn  KindOnAtEveryRun Rel T .K11
  k11Share_at_theGOfReturn         the three in one record

Limits. The head, the threads' parts T and the kinds' rows K are arguments. All ends begin "at each
list at a place of the kind"; that such a list stands with a side is k11Stands_at_theGOfReturn. The
field fresh at the kind's own list says next to nothing: the kind's parts own no coin. The coins
that its second part spends are fresh at their owners' lists: OwnerFresh in ForTheRule.lean, paid by
the owners' kinds. On and bud of the kind ask nothing, so the two conditions of use hold for that
reason. At the base filling's return, not at the online prover's.
-/
import AtFullSide.K11.SlotAtTheG
import E2E.TheG
import E2E.KindPaysOfALot
import Johnson.M1.BudGather
import Johnson.Desc.ProofFile.Honest.Law.UseByKind
import Johnson.Desc.ProofFile.Honest.Law.FillPairs
import Johnson.Desc.ProofFile.Honest.Law.KindPaysOnlineForms
import Johnson.Desc.ProofFile.Honest.Law.RowDebtsByKind

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K11
open VerifiableInference.Desc (Chain KindName FileDescription)
open VerifiableInference.Compilation (KindPays)
open ProofFile (SecondHashFunctionArgument Pub Ground Inst)
open ProofFile.Honest
open ProofFile.Honest.K11
open ProofFile.Honest.Term (matrixInput theGAtBase baseFilling onlineBase online_second_kinds
  online_shared_kinds)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open AtPublicFiles.TheSides (Letters theSides overlaySlots Narrows narrows_of_bare KindRows castSides
  castSides_of kindPays_of_rows rows_of_overlay block_of_seated)
open AtPublicFiles.TheG (ThreadParts theLetters theG theGOfReturn)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open AtPublicFiles.AtFiles.HonestTerm.K11Term

/-- **The kind's lot with its simulator, at the base filling's reader of the index.** -/
noncomputable abbrev k11LotAtBase : SLot (Input FullSizeMatrix) (Input FullSizeMatrix) Unit Inst := k11SimLot matrixInput

/-- **Of the base filling's thirteen lots, each either bears the name of the kind's lot or lays no
side at a place of the kind.** -/
theorem otherLotsLayNoSideOfK11 {W₀ : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (Zq : Pub) (G : Ground) :
    ∀ M ∈ (onlineProverPartsInUse I o S O).lots,
      M.name = "the merge of the weights' claims" ∨ ∀ x ∈ M.halves Zq G, x.place.kind ≠ .K11 := by
  intro M hM
  rcases lot_alone I o S O (onlyK11 I o S O) Zq G M hM with rfl | none
  · exact Or.inl rfl
  · exact Or.inr none

/-- At a row of the kind's lot On holds always. -/
theorem k11_on_at {W₀ : Type} (I : WiderIn W₀) (Zq : Pub) (G : Ground) :
    ∀ r ∈ (k11SimLot I).rows Zq G, ∀ u ca m front, r.On u ca m front := by
  intro r hr
  obtain rfl := List.mem_singleton.1 hr
  exact fun _ _ _ _ => trivial

/-- At a row of the kind's lot bud holds always. -/
theorem k11_bud_at {W₀ : Type} (I : WiderIn W₀) (Zq : Pub) (G : Ground) :
    ∀ r ∈ (k11SimLot I).rows Zq G, ∀ n ds asks, r.bud n ds asks := by
  intro r hr
  obtain rfl := List.mem_singleton.1 hr
  exact fun _ _ _ => trivial

/-- **Good at the kind's row**, at any list in front, any order and any falls. -/
theorem k11_good_at_row {Z : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (made : ProofFile.Honest.Term.baseMaker Z = .ok A) (h : HeadAtReturn Z A)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (ord : List VerifiableInference.Desc.Place) (fs : List (Fall P5J.TS))
    {u : Unlettered (Input FullSizeMatrix) (Input FullSizeMatrix) Unit Inst}
    (hu : u ∈ k11LotAtBase.rows A.Z A.G)
    {σ : Side P5J.TS ProofFile.Cl (Input FullSizeMatrix) (Input FullSizeMatrix) Unit Inst}
    (hσ : Side.seated h.firstChain.blocksInOrder u.place u.row fs = some σ) :
    Good pre .own σ A.B ord 0 0 (fun _ _ _ _ => False) (fun _ _ _ _ => False) u.On u.bud := by
  obtain ⟨Bs, base, O⟩ := h.head.laid.opened
  have hB := O.made
  obtain ⟨-, eG⟩ := k11_ground h.head made hB
  rw [eG] at hu
  obtain rfl := List.mem_singleton.1 hu
  exact headMergeGoodAtFull _ _ ProofFile.Inst _ _ Z _ _ A.Z _ _ _ Bs fs σ .own A.B _ 0 0 _
    (headClaimsByPlace A.Z Bs.G₀) (matrixInput.weights A.Z) h.head (places_nodup h.head) hB hσ
    fun j q => k11_unspent_at h.head made (k11_place_is h.head hB) j q

/-- The base prover has no side of the kind at the shared chain. -/
theorem k11_none_shared {files : VerifierAndGoals.PublicFiles} {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (made : ProofFile.Honest.Term.baseMaker files = .ok returned) (h : HeadAtReturn files returned) :
    ∀ x ∈ returned.H.shared, x.place.kind ≠ KindName.K11 := by
  obtain ⟨-, -, -, -, -, -, -, -, e₂, -⟩ := atPure_ok made
  intro x hx hk
  rw [e₂] at hx
  rcases online_shared_kinds h.head returned.G x hx with e | e | e <;> rw [e] at hk <;> cases hk

/-- The base prover has no side of the kind at the last chain. -/
theorem k11_none_second {files : VerifierAndGoals.PublicFiles} {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (made : ProofFile.Honest.Term.baseMaker files = .ok returned) :
    ∀ x ∈ returned.H.second, x.place.kind ≠ KindName.K11 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, e₃, -⟩ := atPure_ok made
  intro x hx hk
  rw [e₃] at hx
  rw [online_second_kinds _ _ x hx] at hk
  cases hk

/-! ## 1 At the lists built from the filling's lots -/

section
variable {files : VerifierAndGoals.PublicFiles} {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (made : ProofFile.Honest.Term.baseMaker files = .ok returned) (h : HeadAtReturn files returned)
    (mine : List (SLot (Input FullSizeMatrix) (Input FullSizeMatrix) Unit Inst))
    (named : ∀ s ∈ mine, (baseFilling files).lots.any (fun L => L.name == s.name) = true)
    (apart : (mine.map (·.name)).Nodup)
    (hm : ∀ L ∈ (baseFilling files).lots, ∀ s,
      (mine.find? fun s => s.name == L.name) = some s →
      (s.rows returned.Z returned.G).map (·.half) = L.halves returned.Z returned.G)
    (shared : List (Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins OnBytes.TableKey) Unit OnBytes.TableKey))
    (hs : shared.map (·.half) = (baseFilling files).shared returned.Z returned.G)
    (second : List (Unlettered (Input FullSizeMatrix) (Input FullSizeMatrix) Unit Inst))
    (h₃ : second.map (·.half) = (baseFilling files).second returned.Z returned.G)
    (Ls : Letters h.description returned.B FullSizeMatrix IndexCommitterCoins OnBytes.TableKey Cells Unit Unit)
    (f₁ : List (Fall h.description.S₁)) (f₂ : List (Fall h.description.S₂))
    (f₃ : List (Fall h.description.S₃))
    (laid : k11LotAtBase ∈ mine)
include laid

/-- A row of the kind among the rows that the overlay lays is a row of the kind's lot. -/
theorem k11_row_of_overlay :
    ∀ u ∈ (overlaySlots (baseFilling files) returned.Z returned.G mine named apart hm shared hs
        second h₃).rows.first, u.place.kind = .K11 →
      u ∈ k11LotAtBase.rows returned.Z returned.G := by
  intro u hu hk
  obtain ⟨l, hl, hul⟩ := rows_of_overlay (ls := [k11LotAtBase]) apart
    (fun l hl => by rw [List.mem_singleton.1 hl]; exact laid) hm
    (fun M hM => by
      rcases otherLotsLayNoSideOfK11 matrixInput _ _ _ returned.Z returned.G M hM with name | none
      · exact Or.inl ⟨_, List.mem_singleton.2 rfl, name.symm⟩
      · exact Or.inr none) u hu hk
  obtain rfl := List.mem_singleton.1 hl
  exact hul

include made

/-- **KindPays at the lists built from the filling's lots.** -/
theorem k11KindPays_at_the_sides
    (narrows : ∀ u ∈ k11LotAtBase.rows returned.Z returned.G, Narrows (Ls.first u) u) :
    KindPays (theSides h.description Ls
      (overlaySlots (baseFilling files) returned.Z returned.G mine named apart hm shared hs second
        h₃).rows f₁ f₂ f₃) .K11 := by
  refine kindPays_of_rows Ls _ f₁ f₂ f₃ .K11 (fun u hu hk σ hσ => ?_) (fun u hu hk σ hσ => ?_)
    (fun u hu hk σ hσ => ?_)
  · have hul := k11_row_of_overlay mine named apart hm shared hs second h₃ laid u hu hk
    exact ⟨narrows u hul, _, _, k11_good_at_row made h _ _ f₁ hul hσ⟩
  · obtain ⟨-, -, -, -, -, -, -, -, e₂, -⟩ := atPure_ok made
    have side : u.half ∈ returned.H.shared := by
      rw [e₂, ← hs]
      exact List.mem_map_of_mem hu
    exact absurd hk (k11_none_shared made h _ side)
  · obtain ⟨-, -, -, -, -, -, -, -, -, e₃, -⟩ := atPure_ok made
    have side : u.half ∈ returned.H.second := by
      rw [e₃, ← h₃]
      exact List.mem_map_of_mem hu
    exact absurd hk (k11_none_second made _ side)

/-- **The lists of the kind are the lot's rows, in the first chain alone.** -/
theorem k11ListsBear_at_the_sides
    (whole : ∀ u ∈ k11LotAtBase.rows returned.Z returned.G, (Ls.first u).bare = u) :
    ListsOfTheKindBear (theSides h.description Ls
      (overlaySlots (baseFilling files) returned.Z returned.G mine named apart hm shared hs second
        h₃).rows f₁ f₂ f₃) .K11 (k11LotAtBase.rows returned.Z returned.G) := by
  obtain ⟨-, -, -, -, -, -, -, -, e₂, e₃, -⟩ := atPure_ok made
  refine ⟨?_, ?_, ?_⟩
  · intro L hL hk
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hL
    rw [(Ls.keeps₁ u).1] at hk
    have hul := k11_row_of_overlay mine named apart hm shared hs second h₃ laid u hu hk
    rw [whole u hul]
    exact hul
  · intro L hL hk
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hL
    rw [(Ls.keeps₂ u).1] at hk
    have side : u.half ∈ returned.H.shared := by
      rw [e₂, ← hs]
      exact List.mem_map_of_mem hu
    exact k11_none_shared made h _ side hk
  · intro L hL hk
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hL
    rw [(Ls.keeps₃ u).1] at hk
    have side : u.half ∈ returned.H.second := by
      rw [e₃, ← h₃]
      exact List.mem_map_of_mem hu
    exact k11_none_second made _ side hk

end

/-! ## 2 The two conditions of use, at any lists that bear the lot's rows -/

section
variable {W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Inst} {Bk : ProverCoinCounts}
  {G : Sides F Bk W₀ Rc Ky Tr X₀ X}

/-- **The kind's share of the clause on bud.** -/
theorem k11KindBud_of_bear {V₀ : Type} {I : WiderIn V₀}
    {rows : List (Unlettered (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst)}
    (always : ∀ r ∈ rows, ∀ n ds asks, r.bud n ds asks)
    (bear : ListsOfTheKindBear G .K11 rows) : Johnson.M1.KindBud G .K11 :=
  ⟨fun L hL hk => Johnson.M1.budOwed_true F L (always L.bare (bear.first L hL hk)),
    fun L hL e => absurd e (bear.noneShared L hL), fun L hL e => absurd e (bear.noneSecond L hL)⟩

/-- **The kind's share of "On at every run".** -/
theorem k11OnAtEveryRun_of_bear
    {rows : List (Unlettered (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst)}
    (always : ∀ r ∈ rows, ∀ u ca m front, r.On u ca m front)
    (bear : ListsOfTheKindBear G .K11 rows)
    {H : Prover W₀ Rc Inst Ky Tr X₀ X} (Rel : W₀ → Rc → Inst → Prop)
    (T : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      ThreadsP F Bk (G.prover H) w₀ rc x k R) :
    KindOnAtEveryRun (G := G) (H := H) Rel T .K11 :=
  fun w₀ rc x hrel k R hR ρ r _ _ _ =>
    kindOnAtRun_of_rows bear (fun L hL => always L.bare hL) (T w₀ rc x hrel k R hR) ρ r

end

/-! ## 3 At G by its name -/

section
variable {Wt : Type} {files : VerifierAndGoals.PublicFiles} {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (made : ProofFile.Honest.Term.baseMaker files = .ok returned) (h : HeadAtReturn files returned)
    (T : ThreadParts returned Wt) (K : KindRows (baseFilling files) returned.Z returned.G)
    (laid : k11LotAtBase ∈ K.lots)
include made laid

/-- **KindPays (theGAtBase h T K) .K11.** -/
theorem k11KindPays_at_theGAtBase : KindPays (theGAtBase h T K) .K11 :=
  k11KindPays_at_the_sides made h K.lots K.named K.apart K.lots_fit _ _ _ _ (theLetters h T) _ _ _
    laid fun _ _ => narrows_of_bare rfl

/-- **The same at the description that the return holds.** -/
theorem k11KindPays_at_theGOfReturn : KindPays (theGOfReturn made h T K) .K11 :=
  castSides_of (Q := fun _ G => KindPays G .K11) (atPure_at_laid h.head.laid made).2
    (k11KindPays_at_theGAtBase made h T K laid)

/-- **The lists of the kind at that G are the lot's rows, in the first chain alone.** -/
theorem k11ListsBear_at_theGOfReturn :
    ListsOfTheKindBear (theGOfReturn made h T K) .K11 (k11LotAtBase.rows returned.Z returned.G) :=
  castSides_of (Q := fun _ G => ListsOfTheKindBear G .K11 (k11LotAtBase.rows returned.Z returned.G))
    (atPure_at_laid h.head.laid made).2
    (k11ListsBear_at_the_sides made h K.lots K.named K.apart K.lots_fit _ _ _ _ (theLetters h T) _ _
      _ laid fun _ _ => rfl)

/-- **KindBud (theGOfReturn made h T K) .K11.** -/
theorem k11KindBud_at_theGOfReturn : Johnson.M1.KindBud (theGOfReturn made h T K) .K11 :=
  k11KindBud_of_bear (I := matrixInput) (k11_bud_at matrixInput _ _)
    (k11ListsBear_at_theGOfReturn made h T K laid)

/-- **The kind's share of "On at every run" at that G.** -/
theorem k11OnAtEveryRun_at_theGOfReturn
    {H : Prover FullSizeMatrix IndexCommitterCoins Inst OnBytes.TableKey Cells Unit Unit} (Rel : FullSizeMatrix → IndexCommitterCoins → Inst → Prop)
    (Th : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R,
      ready returned.F returned.B ((theGOfReturn made h T K).prover H) w₀ rc x k = .ok R →
      ThreadsP returned.F returned.B ((theGOfReturn made h T K).prover H) w₀ rc x k R) :
    KindOnAtEveryRun (G := theGOfReturn made h T K) (H := H) Rel Th .K11 :=
  k11OnAtEveryRun_of_bear (k11_on_at matrixInput _ _)
    (k11ListsBear_at_theGOfReturn made h T K laid) Rel Th

/-- **The kind's three shares in one record.** -/
theorem k11Share_at_theGOfReturn
    (H : Prover FullSizeMatrix IndexCommitterCoins Inst OnBytes.TableKey Cells Unit Unit) (Rel : FullSizeMatrix → IndexCommitterCoins → Inst → Prop)
    (Th : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R,
      ready returned.F returned.B ((theGOfReturn made h T K).prover H) w₀ rc x k = .ok R →
      ThreadsP returned.F returned.B ((theGOfReturn made h T K).prover H) w₀ rc x k R) :
    KindShare returned (theGOfReturn made h T K) H Rel Th .K11 :=
  ⟨k11KindPays_at_theGOfReturn made h T K laid, k11KindBud_at_theGOfReturn made h T K laid,
    k11OnAtEveryRun_at_theGOfReturn made h T K laid Rel Th⟩

end

end AtFullSide.K11

#print axioms AtFullSide.K11.k11Share_at_theGOfReturn
#print axioms AtFullSide.K11.k11KindPays_at_theGOfReturn
