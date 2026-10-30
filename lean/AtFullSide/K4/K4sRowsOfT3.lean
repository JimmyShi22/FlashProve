-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K4/K4sRowsOfT3.lean: what T3's one theorem (AtFullSide/T3/TheOneTheorem.lean) asks at the
kind K4, each in T3's own text, at `theGOfReturn made h T K` (E2E/TheG.lean), for all parts of the
threads T and every K with K4's slot.

  `k4_kinds_row`   `RowDebtsP.kinds` at .K4.
  `k4_bud_row`   the clause of `budDebts_of_kinds` at .K4, toward `RowDebtsP.hbud`.
  `k4_kind_share`   **K4's three shares of `RowDebtsP` as one end: `KindShare … .K4`** (pays, bud, on).
  `k4_lists_on_bud_row`, `k4_rows_seated_row`   plain, at the same G: On, bud; twelve rows, seated.
  `k4_named_base`, `k4_fit_at_name`   what a K of many kinds asks of K4's slot.
  `k4_beta_marked_at_member`   `betaMarked` at a member's own rounds.
  `k4_seated_row`   the clause of `Sides.seated` at the lists of the kind, toward `AtHonest.asks`.
  `k4_first_stretch`, `k4_later_stretch`   K4's stretch of `AtHonest.first`, `shared`, `second`.
  `k4_sends_no_root`   K4's share of `rootedAll`.

Limits. THE SPENDER's HALF; fresh TRUE AND EMPTY; NO JOINT LAW; A' := B' := False; On and bud are True
at K4's rows, so the On rows say nothing of a run. At a filling whose authors' three warnings are
being checked. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ExactFresh.BudAtTheG
import Johnson.Desc.ProofFile.Honest.K4.Law.ExactFresh.BetaMarkedAtMember
import Johnson.Desc.ProofFile.Honest.Law.RowDebtsByKind
import Johnson.T3.OwedOfKinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K4
open ProofFile.Honest ProofFile.Honest.K4 ProofFile.Honest.K4.ExactFresh
open ProofFile.Honest.Term (baseMaker baseFilling matrixInput theGAtBase)
open VerifiableInference.Desc (KindName FileDescription)
open VerifiableInference.Compilation (KindPays)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open AtPublicFiles.AtFiles
open AtPublicFiles.TheG (ThreadParts theGOfReturn)
open AtPublicFiles.TheSides (KindRows castSides_of)
open Johnson.M1 (KindBud)
open OnBytes.Desc.First.K4.Honest

variable {files : VerifierAndGoals.PublicFiles} {Wt : Type} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **`RowDebtsP.kinds` at the kind K4.** -/
theorem k4_kinds_row (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (T : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G)
    (hslot : k4BaseSlot ∈ K.lots) : KindPays (theGOfReturn made h T K) .K4 :=
  kindPays_K4_at_theGOfReturn made h T K hslot

/-- **The clause of `budDebts_of_kinds` at the kind K4.** -/
theorem k4_bud_row (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (T : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G)
    (hslot : k4BaseSlot ∈ K.lots) : KindBud (theGOfReturn made h T K) .K4 :=
  castSides_of (Q := fun _ G => KindBud G .K4) _ (kindBud_K4_at_theG made h T K hslot)

/-- At every list of the kind On holds at every argument. -/
theorem k4_lists_on (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (T : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G)
    (hslot : k4BaseSlot ∈ K.lots) :
    ∀ L ∈ (theGOfReturn made h T K).first, L.place.kind = .K4 → ∀ u ca m front, L.On u ca m front :=
  castSides_of (Q := fun _ G => ∀ L ∈ G.first, L.place.kind = .K4 → ∀ u ca m front,
      L.On u ca m front) _
    fun L hL hk => (k4_lists_on_bud_at_theG h T K hslot L hL hk).1

/-- No list of the shared chain is of the kind K4. -/
theorem k4_no_shared_list (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (T : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G) :
    ∀ L ∈ (theGOfReturn made h T K).shared, L.place.kind ≠ .K4 :=
  castSides_of (Q := fun _ G => ∀ L ∈ G.shared, L.place.kind ≠ .K4) _
    (k4_no_later_lists_at_theG made h T K).1

/-- No list of the second chain is of the kind K4. -/
theorem k4_no_second_list (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (T : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G) :
    ∀ L ∈ (theGOfReturn made h T K).second, L.place.kind ≠ .K4 :=
  castSides_of (Q := fun _ G => ∀ L ∈ G.second, L.place.kind ≠ .K4) _
    (k4_no_later_lists_at_theG made h T K).2

/-- **The lists of the kind bear K4's rows.** -/
theorem k4_lists_bear (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (T : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G)
    (hslot : k4BaseSlot ∈ K.lots) :
    ListsOfTheKindBear (theGOfReturn made h T K) .K4 (k4BaseSlot.rows A.Z A.G) :=
  ⟨castSides_of (Q := fun _ G => ∀ L ∈ G.first, L.place.kind = .K4 →
      L.bare ∈ k4BaseSlot.rows A.Z A.G) _ (k4_list_is_a_row h T K hslot),
    k4_no_shared_list made h T K, k4_no_second_list made h T K⟩

/-- **K4's THREE SHARES OF `RowDebtsP`, AS ONE END: THE SPENDER's HALF; fresh TRUE AND EMPTY; NO JOINT
LAW; A' := B' := False; On and bud True at K4's rows.** At every H, Rel and family of invariants T. -/
theorem k4_kind_share (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (T₀ : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G)
    (hslot : k4BaseSlot ∈ K.lots)
    (H : Prover FullSizeMatrix IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)
    (Rel : FullSizeMatrix → IndexCommitterCoins → ProofFile.Inst → Prop)
    (T : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R,
      ready A.F A.B ((theGOfReturn made h T₀ K).prover H) w₀ rc x k = .ok R →
      ThreadsP A.F A.B ((theGOfReturn made h T₀ K).prover H) w₀ rc x k R) :
    KindShare A (theGOfReturn made h T₀ K) H Rel T .K4 := by
  refine ⟨k4_kinds_row made h T₀ K hslot, k4_bud_row made h T₀ K hslot, ?_⟩
  intro w₀ rc x hrel k R hR ρ r _ _ _
  refine kindOnAtRun_of_rows (k4_lists_bear made h T₀ K hslot) (fun L hr u ca m front => ?_) _ ρ r
  have e₁ : L.bare.On = fun _ _ _ _ => True := k4_rows_on_true id _ _ _ _ hr
  show L.bare.On u ca m front
  rw [e₁]
  trivial

/-- **Plain: at every list of the kind at `theGOfReturn` On and bud hold at every argument.** -/
theorem k4_lists_on_bud_row (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (T : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G)
    (hslot : k4BaseSlot ∈ K.lots) :
    ∀ L ∈ (theGOfReturn made h T K).first, L.place.kind = .K4 →
      (∀ u ca m front, L.On u ca m front) ∧ ∀ n ds asks, L.bud n ds asks :=
  castSides_of (Q := fun _ G => ∀ L ∈ G.first, L.place.kind = .K4 →
      (∀ u ca m front, L.On u ca m front) ∧ ∀ n ds asks, L.bud n ds asks) _
    (k4_lists_on_bud_at_theG h T K hslot)

/-- **Twelve rows; each stands in the first list of `theGOfReturn`, seated at its falls.** -/
theorem k4_rows_seated_row (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (T : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G)
    (hslot : k4BaseSlot ∈ K.lots) :
    (k4BaseSlot.rows A.Z A.G).length = 12 ∧ ∀ row ∈ k4BaseSlot.rows A.Z A.G,
      ∃ L ∈ (theGOfReturn made h T K).first, L.bare = row ∧
        ∃ σ, L.side A.F.first.blocksInOrder (theGOfReturn made h T K).falls₁ = some σ :=
  castSides_of (Q := fun F₀ G => (k4BaseSlot.rows A.Z A.G).length = 12 ∧
      ∀ row ∈ k4BaseSlot.rows A.Z A.G, ∃ L ∈ G.first, L.bare = row ∧
        ∃ σ, L.side F₀.first.blocksInOrder G.falls₁ = some σ) _
    (k4_rows_seated_at_theG made h T K hslot)

/-- **K4's name stands among the filling's lots.** For whoever lays K4's slot into a K of many kinds. -/
theorem k4_named_base (files : VerifierAndGoals.PublicFiles) :
    (baseFilling files).lots.any (fun L => L.name == k4BaseSlot.name) = true :=
  List.any_eq_true.2 ⟨_, List.mem_of_getElem? (i := 6) rfl, by rfl⟩

/-- **The lot of K4's name has K4's slot's halves.** -/
theorem k4_fit_at_name (files : VerifierAndGoals.PublicFiles) (Zq : ProofFile.Pub) (Gr : ProofFile.Ground) :
    ∀ L ∈ (baseFilling files).lots, L.name = "K4" →
      (k4BaseSlot.rows Zq Gr).map (·.half) = L.halves Zq Gr := by
  intro L hL hn
  have at6 := entry_at_the_only_true _ _ (onlyTheSeventhLotBearsK4sName matrixInput OnBytes.secondHashFunction
    OnBytes.HonestTrace.Sz.ref openHonest) L hL (beq_iff_eq.2 hn)
  obtain rfl : (HLot.byPub matrixInput.weights fun wt => k4HLot id wt fun _ _ => k4LookAt) = L :=
    Option.some.inj at6
  exact k4_rows_halves id (matrixInput.weights Zq) _ Zq Gr

/-- **`betaMarked` at a member's own rounds**, at every masked sumcheck of a seated K4 row: at the
return, by the row's public data Q. -/
theorem k4_beta_marked_at_member (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    {row : Unlettered (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst}
    (hr : row ∈ k4BaseSlot.rows A.Z A.G) {fs : List (Fall P5J.TS)}
    {σ : Side P5J.TS ProofFile.Cl (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit
      ProofFile.Inst}
    (hσ : Side.seated h.firstChain.blocksInOrder row.place row.row fs = some σ) :
    ∃ Q : K4Pub, row.place = k4Place Q ∧ ∀ u ∈ σ.members, ∀ k,
      (k4KindsAll Q)[u.number]? = some (.ms k) → ProofFile.Honest.SumLaw.betaMarked k u.rounds = true := by
  have hG := atPure_ground_at_laid h.head.laid made
  obtain ⟨x, hx, e⟩ := List.mem_filterMap.1 hr
  obtain ⟨Q, hQ', rfl⟩ := Option.map_eq_some_iff.1 e
  obtain ⟨hQ, -⟩ := Option.filter_eq_some_iff.1 hQ'
  refine ⟨Q, rfl, fun u hu k hk => ?_⟩
  have hσ' : Side.seated h.firstChain.blocksInOrder (k4Place Q)
      (k4Sided Q id (matrixInput.weights A.Z) k4Tokens (k4LookAt Q)) fs = some σ := hσ
  have hm := seated_mem hσ'
  obtain ⟨hrow, hp⟩ := seated_is hσ'
  have h0 := k4_rounds_marked_at_member h.head.scope h.head.reads h.head.laid hG hx hQ hm hp
  obtain ⟨t, y, hy, rfl⟩ := membersOf_at σ.row 0 _ u hu
  simp only [Nat.zero_add] at hk ⊢
  have e2 := walk_member Q id (matrixInput.weights A.Z) k4Tokens (k4LookAt Q)
    ProofFile.Honest.SumLaw.betaMarked (k4KindsAll Q) σ.row
    (fun i x hi => hrow ▸ k4_kind_all (Rc := IndexCommitterCoins) (X := Unit) Q id (matrixInput.weights A.Z) k4Tokens
      (k4LookAt Q) hi) _ h0 hk hy
  exact (Bool.and_eq_true _ _ ▸ e2 : _ ∧ _).2

/-- **The clause of `Sides.seated` at the lists of the kind K4.** -/
theorem k4_seated_row (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (T : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G)
    (hslot : k4BaseSlot ∈ K.lots) :
    ∀ L ∈ (theGOfReturn made h T K).first, L.place.kind = .K4 →
      (L.side A.F.first.blocksInOrder).isSome = true := by
  have hin := k4SimulatorHandInAtMaker (W₁ := FullSizeMatrix) (Rc₁ := IndexCommitterCoins) (Tr₁ := Cells) (X₁ := Unit) h.head
    made id (matrixInput.weights A.Z) (fun _ _ => k4LookAt)
  refine castSides_of (Q := fun F₀ G => ∀ L ∈ G.first, L.place.kind = .K4 →
    (L.side F₀.first.blocksInOrder).isSome = true) _ ?_
  intro L hL hk
  obtain ⟨σ, hσ⟩ := (hin.atEveryRow _ (k4_list_is_a_row h T K hslot L hL hk)).seated []
  exact Option.isSome_iff_exists.2 ⟨σ, hσ⟩

/-- **K4's stretch of `AtHonest.first`**: the prover's halves of the kind are K4's rows', in order. The
whole equation is IOP's. -/
theorem k4_first_stretch (made : baseMaker files = .ok A) :
    A.H.first.filter (fun y => decide (y.place.kind = .K4)) =
      (k4BaseSlot.rows A.Z A.G).map (·.half) :=
  k4_halves_at_maker matrixInput OnBytes.secondHashFunction _ OnBytes.HonestTrace.Sz.ref openHonest made

/-- **K4's stretch of `AtHonest.shared` and `second`**: no half of the kind stands there. -/
theorem k4_later_stretch (made : baseMaker files = .ok A) (h : HeadAtReturn files A) :
    (∀ g ∈ A.H.shared, g.place.kind ≠ .K4) ∧ ∀ g ∈ A.H.second, g.place.kind ≠ .K4 := by
  have plan : A.F.planOk = true := by
    have eF : A.F = P5J.F0T OnBytes.secondHashFunction A.Z h.places h.firstChain :=
      Except.ok.inj ((atPure_ok made).2.2.1.symm.trans h.head.laid.value)
    rw [eF]
    exact h.head.laid.planOk
  exact k4_no_half_in_the_later_chains made plan

/-- **K4's share of `rootedAll`: a sub-protocol of the kind K4 sends no root.** -/
theorem k4_sends_no_root (made : baseMaker files = .ok A) (h : HeadAtReturn files A) :
    ∀ b ∈ h.firstChain.blocksInOrder, b.place.kind = .K4 →
      (b.rounds.all fun d => d.entry.roots == 0) = true := by
  intro b hb hk
  have hG := atPure_ground_at_laid h.head.laid made
  obtain ⟨row, hr, ep⟩ := k4_row_of_block (Rc := IndexCommitterCoins) (X' := Unit) h.head hG id
    (matrixInput.weights A.Z) (fun _ _ => k4LookAt) hb hk
  obtain ⟨x, hx, e⟩ := List.mem_filterMap.1 hr
  obtain ⟨Q, hQ', rfl⟩ := Option.map_eq_some_iff.1 e
  obtain ⟨hQ, -⟩ := Option.filter_eq_some_iff.1 hQ'
  obtain ⟨he, -⟩ := k4_member_of_lot h.head.scope h.head.reads h.head.laid hG hx hQ hb ep.symm
  refine List.all_eq_true.2 fun d hd => ?_
  have hm : d.entry ∈ b.rounds.map (·.entry) := List.mem_map_of_mem hd
  rw [he] at hm
  unfold OnBytes.Desc.First.K4.entries at hm
  obtain ⟨q, -, e2⟩ := List.mem_map.1 hm
  rw [← e2]
  rfl

end AtFullSide.K4

#print axioms AtFullSide.K4.k4_first_stretch
#print axioms AtFullSide.K4.k4_later_stretch
#print axioms AtFullSide.K4.k4_sends_no_root
#print axioms AtFullSide.K4.k4_kinds_row
#print axioms AtFullSide.K4.k4_bud_row
#print axioms AtFullSide.K4.k4_kind_share
#print axioms AtFullSide.K4.k4_lists_on_bud_row
#print axioms AtFullSide.K4.k4_rows_seated_row
#print axioms AtFullSide.K4.k4_named_base
#print axioms AtFullSide.K4.k4_fit_at_name
#print axioms AtFullSide.K4.k4_beta_marked_at_member
#print axioms AtFullSide.K4.k4_seated_row
