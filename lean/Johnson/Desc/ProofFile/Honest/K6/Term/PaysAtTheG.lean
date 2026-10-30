--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Term/PaysAtTheG.lean: THE KIND K6 ("the output head's own rounds") AT G, ALL AT
ONE G AND UNDER ONE SET OF LETTERS, AT THE BASE FILLING AND AT THE FILLING THAT THE ONLINE PROVER READS: at `theGOfReturn made h T K`
(E2E/TheG.lean): a list of the kind STANDS in G with a side; `KindPays G .K6` (Johnson/T3/OwedOfKinds.lean); K6's two
conditions of use; and so all three shares of `RowDebtsP` that a kind pays (`KindShare`,
Honest/Law/RowDebtsByKind.lean). One premise on K: K6's lot is among the lots that the kinds lay. From one statement
that is general in the filling.

WHY ALL AT ONE G. `KindPays` alone can be met at letters that narrow On or bud to "never", where the fields `exact`
and `fresh` ask nothing. What bites is "On at the run" and `BudDebts` AT THE SAME LETTERS. So here the letters leave
K6's row whole, and the three are stated together. At `theG` the letters are the threads', which do.

TURNED, AND WHY. `HeadPaysAt` had three fields: stands, pays, use. `HeadStandsAndPays` beside it has a sentence that the
two statements at G proved on their way and then dropped: each list of the kind in G is a row of K6's own lot, simulators,
On and bud included, and none stands in the other two chains (bear). Without it nobody could tell from the end alone that the
simulators at which the kind pays are K6's own. So `HeadPaysAt` now takes the lot's rows as a letter and has bear as a fourth
field, and the two statements at G end at the rows of `headSimulatorLot`. In the list of names below, one name that no
declaration of this file bears is struck. Nothing else is turned: the other three fields, the premises and the proofs' cores are
as they were.

WHAT IT IS NOT.
  * NOT zero knowledge and NOT hiding of anything. THE SPENDER's HALF: fits, exact and an empty fresh at simulators
    that read their own coins alone. That K6's 173 spent coins are fresh is the owner's kind's, K2's.
  * `plays` and `acc` of `Good` are unasked (`KindPays`' own form), and the rule ends at the muted lists. NOTHING SHOWS
    THAT A RUN EVER CALLS K6's PARTS: that this is not idle at K6 hangs on acceptance at the same G.
  * "A list of the kind stands in G" is a sentence on lists and places, not on a run.
  * The head at the return, the threads' parts and the kinds' rows are arguments: no value of them is given.
    THE WITNESSES lay K6's lot ALONE, the other twelve lots beside simulators that tell nothing: they show that the
    premise on K can be met, not that a K with thirteen simulators exists.
  * A family of invariants that is CHOSEN out of an "there is a T" shows nothing of itself: only a share at every T, as K6's is,
    or one from T's own fields, fits it.

  `HeadStandsAndPays`    the three sentences that are general in the description
  `headStandsAndPays_at_a_filling`   at any filling whose other lots lay no side of the kind
  `otherLotsLayNoSideOfTheKindAtTheTerm`   that premise at the online prover's filling
  `HeadPaysAt`   with the conditions of use, at the return's own description; rows: the lot's rows
  `headPays_at_theGOfReturn_at_the_base`, `…_at_the_term`   **AT G, at the two fillings**
  `HeadPaysAt.share`      the three shares of `RowDebtsP`
  `headAtReturn_exists`   the head at a return is there, in scope and live
  `kindRowsWithTheHeadsLotExist`, `…AtTheTerm`   a K that lays K6's lot exists. No premise
-/
import E2E.TheG
import Johnson.Desc.ProofFile.Honest.Law.RowDebtsByKind
import Johnson.Desc.ProofFile.Honest.K6.Term.KindPaysAtTheBase

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Chain KindName FileDescription)
open ProofFile.Honest.Term (matrixInput tableCoins onlineFilling onlineMaker OnlineReturn)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open AtPublicFiles.TheSides (Letters theSides overlaySlots overlayLot Narrows narrows_of_bare kindPays_of_lot
  rows_of_overlay block_of_seated find_name KindRows castSides castSides_of)
open AtPublicFiles.TheG (ThreadParts theLetters theG theGOfReturn)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge

/-- **A list of the kind stands, the kind pays, and its lists are the lot's rows**: three sentences on the lists
G that are general in the description. rows: the lot's rows. A definition that is meant to stand at the end of
a theorem. -/
structure HeadStandsAndPays {W₀ Rc X₀ X : Type} {F₀ : FileDescription Inst} {Bk : ProverCoinCounts}
    (G : Sides F₀ Bk W₀ Rc OnBytes.TableKey Cells X₀ X)
    (rows : List (Unlettered (Local W₀ Rc Inst Cells) (Local W₀ Rc Inst Cells) X Inst)) : Prop where
  /-- G's first chain holds a list at K6's place, and that list has a side over the description -/
  stands : ∃ L ∈ G.first, L.place = IM.k6Place ∧ ∃ σ, L.side F₀.first.blocksInOrder G.falls₁ = some σ
  /-- fits, exact and fresh of `Good` at every list of the kind -/
  pays : VerifiableInference.Compilation.KindPays G .K6
  /-- each list of the kind is a row of the lot, simulators, On and bud included; none in the other chains -/
  bear : ListsOfTheKindBear G .K6 rows

section
variable {Rc : Type} {files : VerifierAndGoals.PublicFiles} {P : OnlineProverParts FullSizeMatrix Rc Cells Unit Unit}
    {returned : OnlineProverWithDescription FullSizeMatrix Rc Cells Unit Unit}
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL P = .ok returned)
    {places : H2U.Places4} {firstChain : Chain P5J.TS ProofFile.Cl}
    {row : Unlettered (Local FullSizeMatrix Rc Inst Cells) (Local FullSizeMatrix Rc Inst Cells) Unit Inst}
    (s : SimulatorShareAtTheProver returned places firstChain row)
    (alone : ∀ M ∈ P.lots, M.name = "the output head's own rounds (K6)" ∨
      ∀ x ∈ M.halves returned.Z returned.G, x.place.kind ≠ .K6)
    (inFilling : (headSimulatorLot (Rc := Rc) (X := Unit) matrixInput.weights).toHLot ∈ P.lots)
    (mine : List (SLot (Local FullSizeMatrix Rc Inst Cells) (Local FullSizeMatrix Rc Inst Cells) Unit Inst))
    (named : ∀ s ∈ mine, P.lots.any (fun L => L.name == s.name) = true)
    (apart : (mine.map (·.name)).Nodup)
    (hm : ∀ L ∈ P.lots, ∀ s, (mine.find? fun s => s.name == L.name) = some s →
      (s.rows returned.Z returned.G).map (·.half) = L.halves returned.Z returned.G)
    (shared : List (Unlettered Empty (Common FullSizeMatrix Rc OnBytes.TableKey) Unit OnBytes.TableKey))
    (hs : shared.map (·.half) = P.shared returned.Z returned.G)
    (second : List (Unlettered (Local FullSizeMatrix Rc Inst Cells) (Local FullSizeMatrix Rc Inst Cells) Unit Inst))
    (h₃ : second.map (·.half) = P.second returned.Z returned.G)
    {F₀ : FileDescription Inst} (same : returned.F = F₀)
    (Ls : Letters F₀ returned.B FullSizeMatrix Rc OnBytes.TableKey Cells Unit Unit)
    (f₁ : List (Fall F₀.S₁)) (f₂ : List (Fall F₀.S₂)) (f₃ : List (Fall F₀.S₃))
    (laid : (headSimulatorLot (Rc := Rc) (X := Unit) matrixInput.weights) ∈ mine)
    (whole : ∀ u ∈ (headSimulatorLot (Rc := Rc) (X := Unit) matrixInput.weights).rows returned.Z
      returned.G, (Ls.first u).bare = u)
include made s alone inFilling same laid whole

/-- CONDITIONAL. **At any filling whose other lots lay no side of the kind**, at any description that equals the
return's, at letters that leave K6's row whole: a list of the kind stands, the kind pays, and its lists are
the lot's rows. -/
theorem headStandsAndPays_at_a_filling :
    HeadStandsAndPays (theSides F₀ Ls
      (overlaySlots P returned.Z returned.G mine named apart hm shared hs second h₃).rows f₁ f₂ f₃)
      ((headSimulatorLot (Rc := Rc) (X := Unit) matrixInput.weights).rows returned.Z returned.G) := by
  subst same
  have stands := s.sideAndBook.stands
  rw [← s.description] at stands
  obtain ⟨-, -, -, -, -, -, -, -, e₂, e₃, -⟩ := atPure_ok made
  have hls : ∀ l ∈ [(headSimulatorLot (Rc := Rc) (X := Unit) matrixInput.weights)], l ∈ mine :=
    fun l hl => by rw [List.mem_singleton.1 hl]; exact laid
  have hAlone : ∀ M ∈ P.lots, (∃ l ∈ [(headSimulatorLot (Rc := Rc) (X := Unit) matrixInput.weights)], l.name = M.name) ∨
      ∀ x ∈ M.halves returned.Z returned.G, x.place.kind ≠ .K6 := fun M hM => by
    rcases alone M hM with name | none
    · exact Or.inl ⟨_, List.mem_singleton.2 rfl, name.symm⟩
    · exact Or.inr none
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have isRow : row ∈ (headSimulatorLot (Rc := Rc) (X := Unit) matrixInput.weights).rows returned.Z returned.G := by
      rw [s.oneRow]
      exact List.mem_singleton.2 rfl
    have place : row.place = IM.k6Place := by
      have e := s.share.oneRow
      rw [s.oneRow] at e
      exact List.head_eq_of_cons_eq e
    have found : overlayLot mine
        (headSimulatorLot (Rc := Rc) (X := Unit) matrixInput.weights).toHLot =
        (headSimulatorLot (Rc := Rc) (X := Unit) matrixInput.weights) := by
      unfold overlayLot
      have f := find_name apart laid
      have f' : (mine.find? fun t => t.name ==
          (headSimulatorLot (Rc := Rc) (X := Unit) matrixInput.weights).toHLot.name) =
          some (headSimulatorLot (Rc := Rc) (X := Unit) matrixInput.weights) := f
      rw [f']
    have inRows : row ∈ rowsOfLots returned.Z returned.G (P.lots.map (overlayLot mine)) :=
      List.mem_flatMap.2 ⟨_, List.mem_map.2 ⟨_, inFilling, found⟩, isRow⟩
    have atPlace : (Ls.first row).place = IM.k6Place := (Ls.keeps₁ row).1.trans place
    obtain ⟨b, hb, hbp⟩ := List.any_eq_true.1 s.share.seated
    have some : (returned.F.first.blocksInOrder.find? fun b => b.place == IM.k6Place).isSome = true := by
      rw [List.find?_isSome]
      exact ⟨b, hb, hbp⟩
    obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.1 some
    refine ⟨Ls.first row, List.mem_map_of_mem inRows, atPlace, Option.isSome_iff_exists.1 ?_⟩
    show (Side.seated returned.F.first.blocksInOrder (Ls.first row).place (Ls.first row).row f₁).isSome = true
    unfold Side.seated
    rw [atPlace, hb']
    rfl
  · refine kindPays_of_lot mine named apart hm shared hs second h₃ Ls f₁ f₂ f₃ .K6 _ hls hAlone ?_ ?_ ?_
    · intro l hl u hu _ σ hσ
      obtain rfl := List.mem_singleton.1 hl
      exact ⟨narrows_of_bare (whole u hu), _, _, s.share.good u hu f₁ σ hσ _ fun _ _ _ _ => False⟩
    · intro u _ hk σ hσ
      obtain ⟨b, hb, e⟩ := block_of_seated hσ
      exact absurd (by rw [e]; exact hk) (stands.2.2.1 b hb)
    · intro u _ hk σ hσ
      obtain ⟨b, hb, e⟩ := block_of_seated hσ
      exact absurd (by rw [e]; exact hk) (stands.2.2.2 b hb)
  · intro L hL hk
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hL
    rw [(Ls.keeps₁ u).1] at hk
    obtain ⟨l, hl, hul⟩ := rows_of_overlay apart hls hm hAlone u hu hk
    obtain rfl := List.mem_singleton.1 hl
    rw [whole u hul]
    exact hul
  · intro L hL hk
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hL
    rw [(Ls.keeps₂ u).1] at hk
    have side : u.half ∈ returned.H.shared := by
      rw [e₂, ← hs]
      exact List.mem_map_of_mem hu
    exact s.sideAndBook.noneShared _ side hk
  · intro L hL hk
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hL
    rw [(Ls.keeps₃ u).1] at hk
    have side : u.half ∈ returned.H.second := by
      rw [e₃, ← h₃]
      exact List.mem_map_of_mem hu
    exact s.sideAndBook.noneLast _ side hk

end

/-- **Of the lots of the filling that the online prover reads, each either bears the name of the head's lot or
lays no side of the kind K6.** A lot read through keeps its name and its sides' places. No premise. -/
theorem otherLotsLayNoSideOfTheKindAtTheTerm (files : VerifierAndGoals.PublicFiles) (Zq : Pub) (G : Ground) :
    ∀ M ∈ (onlineFilling files).lots,
      M.name = "the output head's own rounds (K6)" ∨ ∀ x ∈ M.halves Zq G, x.place.kind ≠ .K6 := by
  intro M hM
  obtain ⟨M₀, h₀, rfl⟩ := List.mem_map.1 hM
  rcases otherLotsLayNoSideOfTheKind matrixInput _ _ _ Zq G M₀ h₀ with name | none
  · exact Or.inl name
  · right
    intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := List.mem_map.1 hx
    exact none x₀ hx₀

/-- **All that K6 pays at lists G at the return's own description**: a list of the kind stands; `KindPays`; the
two conditions of use; the kind's lists are the lot's rows. rows: the lot's rows. A definition that is meant to stand at the
end of a theorem. -/
structure HeadPaysAt {W₀ Rc X₀ X : Type} (returned : OnlineProverWithDescription W₀ Rc Cells X₀ X)
    (G : Sides returned.F returned.B W₀ Rc OnBytes.TableKey Cells X₀ X)
    (rows : List (Unlettered (Local W₀ Rc Inst Cells) (Local W₀ Rc Inst Cells) X Inst)) : Prop where
  stands : ∃ L ∈ G.first, L.place = IM.k6Place ∧
    ∃ σ, L.side returned.F.first.blocksInOrder G.falls₁ = some σ
  pays : VerifiableInference.Compilation.KindPays G .K6
  use : HeadConditionsOfUse returned G
  /-- each list of the kind is a row of the lot, simulators, On and bud included; none in the other chains -/
  bear : ListsOfTheKindBear G .K6 rows

/-- **K6's three shares of `RowDebtsP`**, at every prover beside the lists, every relation and EVERY family of
invariants. -/
theorem HeadPaysAt.share {W₀ Rc X₀ X : Type} {returned : OnlineProverWithDescription W₀ Rc Cells X₀ X}
    {G : Sides returned.F returned.B W₀ Rc OnBytes.TableKey Cells X₀ X}
    {rows : List (Unlettered (Local W₀ Rc Inst Cells) (Local W₀ Rc Inst Cells) X Inst)}
    (p : HeadPaysAt returned G rows)
    (H : Prover W₀ Rc Inst OnBytes.TableKey Cells X₀ X) (Rel : W₀ → Rc → Inst → Prop)
    (Th : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R,
      ready returned.F returned.B (G.prover H) w₀ rc x k = .ok R →
      ThreadsP returned.F returned.B (G.prover H) w₀ rc x k R) :
    KindShare returned G H Rel Th .K6 :=
  ⟨p.pays, p.use.kindBud, p.use.onAtEveryRun Rel Th⟩

section
variable {Wt : Type} (files : VerifierAndGoals.PublicFiles) (scope : VerifierAndGoals.InScope files = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
include scope live

/-- CONDITIONAL: in scope; live; the base maker's return; K6's lot is among the lots that the kinds lay.
**AT G, AT THE BASE FILLING.** -/
theorem headPays_at_theGOfReturn_at_the_base {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (made : ProofFile.Honest.Term.baseMaker files = .ok returned) (h : HeadAtReturn files returned)
    (T : ThreadParts returned Wt)
    (K : KindRows (ProofFile.Honest.Term.baseFilling files) returned.Z returned.G)
    (laid : headSimulatorLot (Rc := IndexCommitterCoins) (X := Unit) matrixInput.weights ∈ K.lots) :
    HeadPaysAt returned (theGOfReturn made h T K)
      ((headSimulatorLot (Rc := IndexCommitterCoins) (X := Unit) matrixInput.weights).rows returned.Z returned.G) := by
  obtain ⟨places, firstChain, row, s⟩ := simulatorShare_at_the_base_prover files scope live made
  have core : HeadStandsAndPays (theGOfReturn made h T K)
      ((headSimulatorLot (Rc := IndexCommitterCoins) (X := Unit) matrixInput.weights).rows returned.Z returned.G) :=
    castSides_of (Q := fun _ G => HeadStandsAndPays G
      ((headSimulatorLot (Rc := IndexCommitterCoins) (X := Unit) matrixInput.weights).rows returned.Z returned.G))
    (atPure_at_laid h.head.laid made).2
    (headStandsAndPays_at_a_filling made s
      (otherLotsLayNoSideOfTheKind matrixInput _ _ _ returned.Z returned.G)
      headSimulatorLot_in_baseFilling K.lots K.named K.apart K.lots_fit _ _ _ _
      (atPure_at_laid h.head.laid made).2 (theLetters h T) _ _ _ laid fun _ _ => rfl)
  exact ⟨core.stands, core.pays,
    headConditionsOfUse_at_the_base_prover files scope live made core.bear, core.bear⟩

/-- **AT G, AT THE FILLING THAT THE ONLINE PROVER READS**: at the honest prover's maker's return. -/
theorem headPays_at_theGOfReturn_at_the_term {returned : OnlineReturn files}
    (made : onlineMaker files = .ok returned) (h : HeadAtReturn files returned)
    (T : ThreadParts returned Wt) (K : KindRows (onlineFilling files) returned.Z returned.G)
    (laid : headSimulatorLot (Rc := (protocolAtFiles files).EncodingRandomness) (X := Unit) matrixInput.weights ∈ K.lots) :
    HeadPaysAt returned (theGOfReturn made h T K)
      ((headSimulatorLot (Rc := (protocolAtFiles files).EncodingRandomness) (X := Unit) matrixInput.weights).rows returned.Z
        returned.G) := by
  obtain ⟨places, firstChain, row, -, -, s⟩ :=
    simulatorShare_at_the_honest_prover files scope live made
  have core : HeadStandsAndPays (theGOfReturn made h T K)
      ((headSimulatorLot (Rc := (protocolAtFiles files).EncodingRandomness) (X := Unit) matrixInput.weights).rows returned.Z
        returned.G) :=
    castSides_of (Q := fun _ G => HeadStandsAndPays G
      ((headSimulatorLot (Rc := (protocolAtFiles files).EncodingRandomness) (X := Unit) matrixInput.weights).rows returned.Z
        returned.G))
    (atPure_at_laid h.head.laid made).2
    (headStandsAndPays_at_a_filling made s
      (otherLotsLayNoSideOfTheKindAtTheTerm files returned.Z returned.G)
      (headSimulatorLot_in_onlineFilling files) K.lots K.named K.apart K.lots_fit _ _ _ _
      (atPure_at_laid h.head.laid made).2 (theLetters h T) _ _ _ laid fun _ _ => rfl)
  exact ⟨core.stands, core.pays,
    headConditionsOfUse_at_the_honest_prover files scope live made core.bear, core.bear⟩

end

/-- **The head at a return of the maker is there**, in scope and live, at any filling: so the argument h of the
statements above can be met wherever the maker returns. -/
theorem headAtReturn_exists {W₀ Rc Tr X₀ X : Type} (files : VerifierAndGoals.PublicFiles)
    (scope : VerifierAndGoals.InScope files = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true) {P : OnlineProverParts W₀ Rc Tr X₀ X}
    {returned : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL P = .ok returned) :
    Nonempty (HeadAtReturn files returned) := by
  obtain ⟨Zp, Np, cF, x, h⟩ := head_of_the_two_tests files scope live
  obtain rfl := (atPure_at_laid h.laid made).1
  exact ⟨⟨⟨P, made⟩, Np, cF, x, h⟩⟩

/-- **A K that lays K6's lot exists**, at the base filling, at every public part and ground. It lays that lot
alone, and no row on the two other chains. -/
theorem kindRowsWithTheHeadsLotExist (files : VerifierAndGoals.PublicFiles) (Zq : Pub) (G : Ground) :
    ∃ K : KindRows (ProofFile.Honest.Term.baseFilling files) Zq G,
      headSimulatorLot (Rc := IndexCommitterCoins) (X := Unit) matrixInput.weights ∈ K.lots :=
  ⟨{ lots := [headSimulatorLot (Rc := IndexCommitterCoins) (X := Unit) matrixInput.weights]
     named := fun s hs => by
       rw [List.mem_singleton.1 hs]
       rfl
     apart := by simp
     lots_fit := fun L hL s hs => by
       rw [← headSimulatorLot_overlays_the_base L hL s hs]
       rfl
     shared := []
     shared_named := fun _ hr => by cases hr
     shared_apart := by simp
     shared_fit := fun _ _ _ hr => by simp at hr
     second := []
     second_named := fun _ hr => by cases hr
     second_apart := by simp
     second_fit := fun _ _ _ hr => by simp at hr }, List.mem_singleton.2 rfl⟩

/-- The same at the filling that the online prover reads. -/
theorem kindRowsWithTheHeadsLotExistAtTheTerm (files : VerifierAndGoals.PublicFiles) (Zq : Pub) (G : Ground) :
    ∃ K : KindRows (onlineFilling files) Zq G,
      headSimulatorLot (Rc := (protocolAtFiles files).EncodingRandomness) (X := Unit) matrixInput.weights ∈ K.lots :=
  ⟨{ lots := [headSimulatorLot (Rc := (protocolAtFiles files).EncodingRandomness) (X := Unit) matrixInput.weights]
     named := fun s hs => by
       rw [List.mem_singleton.1 hs]
       exact List.any_eq_true.2 ⟨_, headSimulatorLot_in_onlineFilling files, by simp [SLot.toHLot]⟩
     apart := by simp
     lots_fit := fun L hL s hs => by
       rw [← headSimulatorLot_overlays_the_online_filling files L hL s hs]
       rfl
     shared := []
     shared_named := fun _ hr => by cases hr
     shared_apart := by simp
     shared_fit := fun _ _ _ hr => by simp at hr
     second := []
     second_named := fun _ hr => by cases hr
     second_apart := by simp
     second_fit := fun _ _ _ hr => by simp at hr }, List.mem_singleton.2 rfl⟩

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.HeadStandsAndPays
#print axioms ProofFile.Honest.K6.headStandsAndPays_at_a_filling
#print axioms ProofFile.Honest.K6.otherLotsLayNoSideOfTheKindAtTheTerm
#print axioms ProofFile.Honest.K6.HeadPaysAt
#print axioms ProofFile.Honest.K6.HeadPaysAt.share
#print axioms ProofFile.Honest.K6.headPays_at_theGOfReturn_at_the_base
#print axioms ProofFile.Honest.K6.headPays_at_theGOfReturn_at_the_term
#print axioms ProofFile.Honest.K6.headAtReturn_exists
#print axioms ProofFile.Honest.K6.kindRowsWithTheHeadsLotExist
#print axioms ProofFile.Honest.K6.kindRowsWithTheHeadsLotExistAtTheTerm
