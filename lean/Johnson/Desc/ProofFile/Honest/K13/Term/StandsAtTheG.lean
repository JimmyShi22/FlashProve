-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K13/Term/StandsAtTheG.lean: the members' batching (kind K13), beside
KindPaysAtTheG.lean of this folder: that the one premise of that file on the kinds' rows can be met,
that the kind's row stands among the lists with a side, and the kind's three shares gathered. At a
return of the maker at the base filling (`baseMaker`, E2E/BaseMaker.lean) with the library's head.
One definition; statements with their proofs.

KindPaysAtTheG.lean shows what the kind pays at the lists `theGOfReturn made h T K` (E2E/TheG.lean)
under the premise that the kind's lot with its simulators is among the lots that K lays. All its
ends begin "at each list at a place of the kind": they would hold for want of such a list.

  `k13_slot_by_name`   a lot of the base filling that bears the name of the kind's lot is the
     filling's lot of the kind. No premise
  `k13Lot_overlays_the_base`   with the simulators forgotten, the rows of the kind's lot are the
     sides of the filling's lot of that name
  `kindRowsWithK13sLotExist`   **a value K that lays the kind's lot exists**, at every public part
     and ground. No premise
  `K13Stands`, `k13Stands_at_the_sides`, `k13Stands_at_theGOfReturn`   **the kind's row stands**: a
     list that bears a row of the lot is among the first chain's lists, and has a side over the
     description, at its member number 355
  `k13Share_at_theGOfReturn`   the three shares in the form in which the rule's premise is gathered
     from all kinds (`KindShare`, `rowDebtsP_of_kinds`,
     Johnson/Desc/ProofFile/Honest/Law/RowDebtsByKind.lean)
  `k13_stands_and_pays_at_some_rows`   with no premise on K: there is a K at which the row stands
     and the kind pays

Limits.
  * The witness lays the kind's lot ALONE: the other twelve lots stand beside simulators that tell
    nothing. It shows that the premise on K can be met; not that a K with all kinds' simulators
    exists, nor that the K which is laid in the end holds this lot. For that K its layer needs the
    first two statements here, and that the names are apart.
  * "Stands" is a sentence on lists and places, not on a run: nothing here shows that a run ever
    calls the kind's parts. The fields plays and acc of `Good` are unasked.
  * What the kind pays is the borrower's half: fits and exact, one part at a time, for challenges
    that are drawn honestly. It is not shown that the kind's job is the protocol's summand.
  * The kind's `On` asks nothing, and its two conditions of use are free, because the sender never
    refuses: its job is total, and the masked sumcheck's part fills up or cuts a list that does not
    fit. That is lawful for zero knowledge, which speaks of the sender as written. Toward
    completeness nothing of it is spent.
  * At the base filling's return. These lists have the type that a statement on zero knowledge from
    the base would take. This file states none, and shows no crossing from the base to the honest
    prover's own return.
  * h and T are arguments: no value of them is given here.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.K13.Term.KindPaysAtTheG
import Johnson.Desc.ProofFile.Honest.Law.RowDebtsByKind

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13
open VerifiableInference.Desc (Chain KindName FileDescription)
open VerifiableInference.Compilation (KindPays)
open ProofFile.Honest.Term (matrixInput theGAtBase baseMaker baseFilling)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open AtPublicFiles.TheSides (Letters theSides overlaySlots overlayLot find_name KindRows castSides
  castSides_of)
open AtPublicFiles.TheG (ThreadParts theLetters theG theGOfReturn)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge

/-! ## 1 A value of the kinds' rows that lays the kind's lot -/

/-- **A lot of the base filling that bears the name of the kind's lot is the filling's lot of the
kind.** No premise: the thirteen names are told apart one by one. -/
theorem k13_slot_by_name :
    ∀ L ∈ (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref
      openHonest).lots, L.name = "K13: the members' batching" →
      L = k13FillLot matrixInput openHonest := by
  intro L hL hn
  rw [widerFillAtCPUOWM_lots, widerFillAt_lots] at hL
  simp only [widerPairs, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hL
  rcases hL with (((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl) | rfl) | rfl
  all_goals first | exact absurd hn (by decide) | rfl

/-- **The premise under which the kind's lot is laid over the base filling's own**, at the list that
holds this lot alone: with the simulators forgotten its rows are the sides of the filling's lot of
that name. -/
theorem k13Lot_overlays_the_base (files : VerifierAndGoals.PublicFiles) (Zq : Pub) (G : Ground) :
    ∀ L ∈ (baseFilling files).lots, ∀ s,
      ([k13LotAtBase Zq].find? fun s => s.name == L.name) = some s →
      (s.rows Zq G).map (·.half) = L.halves Zq G := by
  intro L hL s hs
  have hm := List.mem_of_find?_eq_some hs
  have hp := List.find?_some hs
  obtain rfl := List.mem_singleton.1 hm
  rw [k13_slot_by_name L hL (beq_iff_eq.1 hp).symm]
  exact k13SLot_halves _ _ Zq G

/-- **A value of the kinds' rows that lays the kind's lot exists**, at the base filling, at every
public part and ground. It lays that lot alone, and no row on the two other chains. -/
theorem kindRowsWithK13sLotExist (files : VerifierAndGoals.PublicFiles) (Zq : Pub) (G : Ground) :
    ∃ K : KindRows (baseFilling files) Zq G, k13LotAtBase Zq ∈ K.lots :=
  ⟨{ lots := [k13LotAtBase Zq]
     named := fun s hs => by
       rw [List.mem_singleton.1 hs]
       exact List.any_eq_true.2 ⟨_, k13FillLot_mem matrixInput _ _ openHonest, by rfl⟩
     apart := by simp
     lots_fit := k13Lot_overlays_the_base files Zq G
     shared := []
     shared_named := fun _ hr => by cases hr
     shared_apart := by simp
     shared_fit := fun _ _ _ hr => by simp at hr
     second := []
     second_named := fun _ hr => by cases hr
     second_apart := by simp
     second_fit := fun _ _ _ hr => by simp at hr }, List.mem_singleton.2 rfl⟩

/-! ## 2 The kind's row stands among the lists, with a side -/

/-- **A list that bears a row of the kind's lot stands in the first chain's lists, and has a side
over the description, at its member number 355.** rows: the lot's rows. A definition, meant as a
theorem's end. -/
def K13Stands {W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Inst} {Bk : ProverCoinCounts}
    (G : Sides F Bk W₀ Rc Ky Tr X₀ X)
    (rows : List (Unlettered (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst)) : Prop :=
  ∃ L ∈ G.first, L.bare ∈ rows ∧
    ∃ σ, L.side F.first.blocksInOrder G.falls₁ = some σ ∧ F.first.blocksInOrder[355]? = some σ.block

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

/-- CONDITIONAL: the base maker's return, with the head; the kind's lot is among the lots laid over
the filling's; the letters leave the kind's row as it is. **The kind's row stands, with a side.** -/
theorem k13Stands_at_the_sides
    (whole : ∀ u ∈ (k13LotAtBase returned.Z).rows returned.Z returned.G, (Ls.first u).bare = u) :
    K13Stands (theSides h.description Ls
      (overlaySlots (baseFilling files) returned.Z returned.G mine named apart hm shared hs second
        h₃).rows f₁ f₂ f₃) ((k13LotAtBase returned.Z).rows returned.Z returned.G) := by
  obtain ⟨r, hr⟩ : ∃ r, r ∈ (k13LotAtBase returned.Z).rows returned.Z returned.G :=
    ⟨_, List.mem_singleton.2 rfl⟩
  have found : overlayLot mine (k13FillLot matrixInput openHonest) = k13LotAtBase returned.Z := by
    unfold overlayLot
    have f' : (mine.find? fun t => t.name == (k13FillLot matrixInput openHonest).name) =
        some (k13LotAtBase returned.Z) := find_name apart laid
    rw [f']
  have inRows : r ∈ rowsOfLots returned.Z returned.G
      ((baseFilling files).lots.map (overlayLot mine)) :=
    List.mem_flatMap.2 ⟨_, List.mem_map.2 ⟨_, k13FillLot_mem matrixInput _ _ openHonest, found⟩, hr⟩
  obtain ⟨⟨σ, hσ, at355⟩, -⟩ :=
    k13_good_rows_atPure h.head made _ _ returned.G [] .own [] 0 0 f₁ r hr
  refine ⟨Ls.first r, List.mem_map_of_mem inRows, ?_, σ, ?_, at355⟩
  · rw [whole r hr]
    exact hr
  · show Side.seated _ (Ls.first r).place (Ls.first r).row f₁ = some σ
    rw [(Ls.keeps₁ r).1, (Ls.keeps₁ r).2]
    exact hσ

end

/-! ## 3 At the lists by their name -/

section
variable {Wt : Type} {files : VerifierAndGoals.PublicFiles} {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (made : baseMaker files = .ok returned) (h : HeadAtReturn files returned)
    (T : ThreadParts returned Wt) (K : KindRows (baseFilling files) returned.Z returned.G)
    (laid : k13LotAtBase returned.Z ∈ K.lots)
include laid

/-- **The kind's row stands in `theGOfReturn made h T K`, with a side at member 355.** -/
theorem k13Stands_at_theGOfReturn :
    K13Stands (theGOfReturn made h T K) ((k13LotAtBase returned.Z).rows returned.Z returned.G) :=
  castSides_of (Q := fun _ G => K13Stands G
      ((k13LotAtBase returned.Z).rows returned.Z returned.G))
    (atPure_at_laid h.head.laid made).2
    (k13Stands_at_the_sides made h K.lots K.named K.apart K.lots_fit _ _ _ _ (theLetters h T) _ _ _
      laid fun _ _ => rfl)

/-- **The kind's three shares of the rule's premise, gathered**, at every prover beside the lists,
every relation and every family of invariants. -/
theorem k13Share_at_theGOfReturn
    (H : Prover FullSizeMatrix IndexCommitterCoins Inst OnBytes.TableKey Cells Unit Unit) (Rel : FullSizeMatrix → IndexCommitterCoins → Inst → Prop)
    (Th : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R,
      ready returned.F returned.B ((theGOfReturn made h T K).prover H) w₀ rc x k = .ok R →
      ThreadsP returned.F returned.B ((theGOfReturn made h T K).prover H) w₀ rc x k R) :
    KindShare returned (theGOfReturn made h T K) H Rel Th .K13 :=
  ⟨k13KindPays_at_theGOfReturn made h T K laid, k13KindBud_at_theGOfReturn made h T K laid,
    k13OnAtEveryRun_at_theGOfReturn made h T K laid Rel Th⟩

end

/-- **With no premise on the kinds' rows**: at the base maker's return with the head there is a
value K of the kinds' rows at which the kind's row stands with a side and the kind pays. -/
theorem k13_stands_and_pays_at_some_rows {Wt : Type} {files : VerifierAndGoals.PublicFiles}
    {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (made : baseMaker files = .ok returned)
    (h : HeadAtReturn files returned) (T : ThreadParts returned Wt) :
    ∃ K : KindRows (baseFilling files) returned.Z returned.G,
      K13Stands (theGOfReturn made h T K)
        ((k13LotAtBase returned.Z).rows returned.Z returned.G) ∧
      KindPays (theGOfReturn made h T K) .K13 ∧
      Johnson.M1.KindBud (theGOfReturn made h T K) .K13 := by
  obtain ⟨K, laid⟩ := kindRowsWithK13sLotExist files returned.Z returned.G
  exact ⟨K, k13Stands_at_theGOfReturn made h T K laid, k13KindPays_at_theGOfReturn made h T K laid,
    k13KindBud_at_theGOfReturn made h T K laid⟩

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_slot_by_name
#print axioms ProofFile.Honest.K13.k13Lot_overlays_the_base
#print axioms ProofFile.Honest.K13.kindRowsWithK13sLotExist
#print axioms ProofFile.Honest.K13.K13Stands
#print axioms ProofFile.Honest.K13.k13Stands_at_the_sides
#print axioms ProofFile.Honest.K13.k13Stands_at_theGOfReturn
#print axioms ProofFile.Honest.K13.k13Share_at_theGOfReturn
#print axioms ProofFile.Honest.K13.k13_stands_and_pays_at_some_rows
