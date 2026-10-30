-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/ExactFresh/BudAtTheG.lean: K4's lists at `theGAtBase`, at every K
with K4's slot: in the plain form, what the rule's rows 2b and 2c ask at the kind, and the clause
`KindBud` of `budDebts_of_kinds` (Johnson/M1/BudGather.lean).

  `k4_list_is_a_row`   a list of the first chain of the kind K4 is, its letters forgotten, a K4 row.
  `k4_lists_on_bud_at_theG`   **at every such list On and bud hold at every argument.**
  `k4_no_later_lists_at_theG`   no list of the shared or second chain is of the kind K4.
  `kindBud_K4_at_theG`   **`KindBud (theGAtBase h T K) .K4`.**
  `k4_rows_seated_at_theG`   **twelve rows, each in the first list and seated at G's falls.**

Limits. On and bud are True by definition at K4's rows, and the guards `k4_rows_on_true`,
`k4_rows_bud_true` hold them there. K4's rounds send no root (`k4_sends_no_root`,
AtFullSide/K4/K4sRowsOfT3.lean): that speaks of roots SENT alone. The library's docstring on this form
(`budOwed_true`, Johnson/M1/BudShareCore.lean), whole: «A list whose bound always holds owes nothing. LAWFUL ONLY
WHERE NOTHING MASKED IS SHOWN: at a row with no slack `bud := True` makes `exact` false, so this is no way for a
row that opens masked trees.» bud is a premise of `Good.exact` and `Good.fresh` (Honest/Side.lean). This comment
does not say that nothing masked is shown: Honest/K4/Part.lean has «A round whose message holds n hidden scalars,
each plus its mask entry.» `exact` at these rows is had in `kindPays_K4_at_theGOfReturn` (KindPaysAtTheG.lean of
this folder): THE SPENDER's HALF; fresh TRUE AND EMPTY; NO JOINT LAW; A' := B' := False. At a filling whose authors'
three warnings are being checked. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ExactFresh.KindPaysAtTheG
import Johnson.M1.BudGather

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.ExactFresh
open ProofFile.Honest.Term (baseMaker baseFilling matrixInput theGAtBase)
open VerifiableInference.Desc (KindName)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open AtPublicFiles.AtFiles
open AtPublicFiles.TheG (ThreadParts)
open AtPublicFiles.TheSides (KindRows rows_of_overlay)
open Johnson.M1 (KindBud kindBud_always)

variable {files : VerifierAndGoals.PublicFiles} {Wt : Type} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **A list of the first chain of `theGAtBase` of the kind K4 is, its letters forgotten, a K4 row.** -/
theorem k4_list_is_a_row (h : HeadAtReturn files A) (T : ThreadParts A Wt)
    (K : KindRows (baseFilling files) A.Z A.G) (hslot : k4BaseSlot ∈ K.lots) :
    ∀ L ∈ (theGAtBase h T K).first, L.place.kind = .K4 → L.bare ∈ k4BaseSlot.rows A.Z A.G := by
  intro L hL hk
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hL
  obtain ⟨l, hl, hul⟩ := rows_of_overlay (ls := [k4BaseSlot]) K.apart
    (fun l hl => by rw [List.mem_singleton.1 hl]; exact hslot) K.lots_fit
    (k4_alone_at_base files A.Z A.G) u hu hk
  obtain rfl := List.mem_singleton.1 hl
  exact hul

/-- **At every list of the kind On and bud hold at every argument.** -/
theorem k4_lists_on_bud_at_theG (h : HeadAtReturn files A) (T : ThreadParts A Wt)
    (K : KindRows (baseFilling files) A.Z A.G) (hslot : k4BaseSlot ∈ K.lots) :
    ∀ L ∈ (theGAtBase h T K).first, L.place.kind = .K4 →
      (∀ u ca m front, L.On u ca m front) ∧ ∀ n ds asks, L.bud n ds asks := by
  intro L hL hk
  have hr := k4_list_is_a_row h T K hslot L hL hk
  have e₁ : L.bare.On = fun _ _ _ _ => True := k4_rows_on_true id _ _ _ _ hr
  have e₂ : L.bare.bud = fun _ _ _ => True := k4_rows_bud_true id _ _ _ _ hr
  refine ⟨fun u ca m front => ?_, fun n ds asks => ?_⟩
  · show L.bare.On u ca m front
    rw [e₁]
    trivial
  · show L.bare.bud n ds asks
    rw [e₂]
    trivial

/-- **No list of the shared or the second chain of `theGAtBase` is of the kind K4**, at `baseMaker`'s
return. -/
theorem k4_no_later_lists_at_theG (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (T : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G) :
    (∀ L ∈ (theGAtBase h T K).shared, L.place.kind ≠ .K4) ∧
      ∀ L ∈ (theGAtBase h T K).second, L.place.kind ≠ .K4 := by
  have plan : A.F.planOk = true := by
    have eF : A.F = P5J.F0T OnBytes.secondHashFunction A.Z h.places h.firstChain :=
      Except.ok.inj ((atPure_ok made).2.2.1.symm.trans h.head.laid.value)
    rw [eF]
    exact h.head.laid.planOk
  obtain ⟨n2, n3⟩ := k4_no_half_in_the_later_chains made plan
  obtain ⟨-, f2, f3⟩ := K.slots.fit made
  refine ⟨fun L hL => ?_, fun L hL => ?_⟩
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hL
    exact n2 u.half (f2 ▸ List.mem_map_of_mem hu)
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hL
    exact n3 u.half (f3 ▸ List.mem_map_of_mem hu)

/-- **The clause of `budDebts_of_kinds` at the kind K4.** -/
theorem kindBud_K4_at_theG (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (T : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G)
    (hslot : k4BaseSlot ∈ K.lots) : KindBud (theGAtBase h T K) .K4 := by
  obtain ⟨n2, n3⟩ := k4_no_later_lists_at_theG made h T K
  exact kindBud_always (fun L hL e => (k4_lists_on_bud_at_theG h T K hslot L hL e).2)
    (fun L hL e => absurd e (n2 L hL)) fun L hL e => absurd e (n3 L hL)

/-- **Twelve rows; each stands in the first list of `theGAtBase` and is seated at G's falls.** -/
theorem k4_rows_seated_at_theG (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (T : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G)
    (hslot : k4BaseSlot ∈ K.lots) :
    (k4BaseSlot.rows A.Z A.G).length = 12 ∧ ∀ row ∈ k4BaseSlot.rows A.Z A.G,
      ∃ L ∈ (theGAtBase h T K).first, L.bare = row ∧
        ∃ σ, L.side h.description.first.blocksInOrder (theGAtBase h T K).falls₁ = some σ := by
  have hin := k4SimulatorHandInAtMaker (W₁ := FullSizeMatrix) (Rc₁ := IndexCommitterCoins) (Tr₁ := Cells) (X₁ := Unit) h.head
    made id (matrixInput.weights A.Z) (fun _ _ => k4LookAt)
  refine ⟨hin.rowsAreTwelve, fun row hr => ?_⟩
  obtain ⟨L, hL, rfl⟩ := k4_rows_in_theG h T K hslot hr
  exact ⟨L, hL, rfl, (hin.atEveryRow _ hr).seated _⟩

end ProofFile.Honest.K4.ExactFresh

#print axioms ProofFile.Honest.K4.ExactFresh.k4_list_is_a_row
#print axioms ProofFile.Honest.K4.ExactFresh.k4_lists_on_bud_at_theG
#print axioms ProofFile.Honest.K4.ExactFresh.k4_no_later_lists_at_theG
#print axioms ProofFile.Honest.K4.ExactFresh.kindBud_K4_at_theG
#print axioms ProofFile.Honest.K4.ExactFresh.k4_rows_seated_at_theG
