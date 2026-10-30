--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Term/ConditionsOfUse.lean: THE CONDITIONS UNDER WHICH THE SIMULATORS OF THE
KIND K6 ("the output head's own rounds") MAY BE USED AT A RUN: K6's share of `BudDebts`
(Honest/Law/OwedRule.lean) and of "On at the run, list by list" (`KindOnAtRun`,
Honest/Law/UseByKind.lean), which the rule that ends in `Owed` asks beside `Good`. At any return of the
honest prover's maker, general in the filling; at the one base maker; and at the two named sets of
public files. The share of `BudDebts` is stated in other authors' forms: `BudOwed`
(Johnson/M1/BudShareCore.lean) and `KindBud G .K6` (Johnson/M1/BudGather.lean), from which their
`budDebts_of_kinds` gathers `BudDebts`.

WHY THEY ARE LIGHT AT K6. On asks nothing (the field `exact` holds at every state), so it holds at every
run. bud says "no position of a table of the row's is read", and K6's rounds send no table.

WHAT IT IS NOT.
  * TWO OF THE CONDITIONS, NOT ALL: that the spent coins are fresh, that a family of invariants exists, and
    `Good` itself are others (Honest/K6/Term/KindPaysAtTheBase.lean has K6's `KindPays`).
  * ONE PREMISE ON THE LISTS G STAYS: `ListsOfTheKindBear G .K6 rows`: each list of G's first chain at a
    place of the kind is this lot's row, simulators, On and bud included, and no list of the kind stands in the
    other two chains. Whoever lays G owes it. AT A G WITHOUT A LIST OF THE KIND EVERYTHING HERE HOLDS EMPTILY.
  * It gives no family of invariants and no run: `KindOnAtRun` stands at every T, ρ and r that it is handed.
  * NOT zero knowledge and NOT hiding of anything: two of the premises of a rule whose end, `Owed`, is itself
    a hypothesis of the frame's theorem. That K6's 173 spent coins are fresh is owed with another kind.
  * The library's hypothesis at the full size and "the maker returns" are premises of the general form.

  `HeadSimulatorShare.onAtRun`   On at a run, at a list that bears a row of the lot
  `HeadSimulatorShare.budAtTheKind`, `.kindOnAtRun`   K6's two shares, from the share
  `HeadConditionsOfUse`, `.kindBud`, `.onAtEveryRun`, `headConditionsOfUse_at_maker`   both, gathered; the
        share of `BudDebts` in all three chains; that of On with the rule's own prefix; at any return of the maker
  `headConditionsOfUse_at_the_base_prover`, `…_at_the_honest_prover`   both at the one base maker's return, and
        at the honest prover's maker's, in scope and live
  `headConditionsOfUse_at_the_named_files`   both at either named set of public files
-/
import E2E.BaseMaker
import AtFullSide.K14.BudAtNamed
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstAnyAtCopy
import Johnson.M1.BudGather
import Johnson.Desc.ProofFile.Honest.Law.UseByKind
import Johnson.Desc.ProofFile.Honest.K6.Term.SimulatorAtTheHonestProver

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain KindName)
open ProofFile.Honest.Term (matrixInput)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge

variable {W₀ Rc X₀ X : Type}

section
variable {weights : Pub → W₀ → Weights} {returned : OnlineProverWithDescription W₀ Rc Cells X₀ X}
  {G : Sides returned.F returned.B W₀ Rc OnBytes.TableKey Cells X₀ X}
  {H : Prover W₀ Rc Inst OnBytes.TableKey Cells X₀ X}

/-- **On at a run**, at a list whose place, parts, simulators, On and bud are a row's of the lot: at every
family of invariants, every list of challenges and every run. -/
theorem HeadSimulatorShare.onAtRun (s : HeadSimulatorShare weights returned)
    (L : Lettered returned.B returned.F.S₁ returned.F.Cl (Local W₀ Rc Inst Cells)
      (Local W₀ Rc Inst Cells) X Inst)
    (hL : L.bare ∈ (headSimulatorLot (Rc := Rc) (X := X) weights).rows returned.Z returned.G)
    {w₀ : W₀} {rc : Rc} {x : Inst} {k : Coins returned.B}
    {R : Ready W₀ Rc Inst OnBytes.TableKey Cells X₀ X}
    (T : ThreadsP returned.F returned.B (G.prover H) w₀ rc x k R) (ρ : Draws) (r : RunC returned.F) :
    OnAtRun₁ (G := G) (H := H) T ρ r L :=
  onAtRun₁_of_always T ρ r (s.onDebt L hL)

/-- CONDITIONAL on the lists. **K6's share of `BudDebts`** at each list of the first chain at a place of the
kind, in the form `BudOwed`, which is the text of the clause bud₁; by `bear` the kind has no list in the
other two chains. -/
theorem HeadSimulatorShare.budAtTheKind (s : HeadSimulatorShare weights returned)
    (bear : ListsOfTheKindBear G .K6
      ((headSimulatorLot (Rc := Rc) (X := X) weights).rows returned.Z returned.G)) :
    ∀ L ∈ G.first, L.place.kind = .K6 → Johnson.M1.BudOwed returned.F L :=
  fun L hL hk => s.budDebt L (bear.first L hL hk)

/-- CONDITIONAL on the lists. **K6's share of "On at the run, list by list"**, at every family of
invariants, every list of challenges and every run. -/
theorem HeadSimulatorShare.kindOnAtRun (s : HeadSimulatorShare weights returned)
    (bear : ListsOfTheKindBear G .K6
      ((headSimulatorLot (Rc := Rc) (X := X) weights).rows returned.Z returned.G))
    {w₀ : W₀} {rc : Rc} {x : Inst} {k : Coins returned.B}
    {R : Ready W₀ Rc Inst OnBytes.TableKey Cells X₀ X}
    (T : ThreadsP returned.F returned.B (G.prover H) w₀ rc x k R) (ρ : Draws) (r : RunC returned.F) :
    KindOnAtRun (G := G) (H := H) T ρ r .K6 :=
  kindOnAtRun_of_rows bear (fun L hL => s.onDebt L hL) T ρ r

end

/-- **Both conditions of use, gathered.** G: the lists of all kinds' rows at the return. A definition that
is meant to stand at the end of a theorem. -/
structure HeadConditionsOfUse {W₀ Rc X₀ X : Type} (returned : OnlineProverWithDescription W₀ Rc Cells X₀ X)
    (G : Sides returned.F returned.B W₀ Rc OnBytes.TableKey Cells X₀ X) : Prop where
  /-- K6's share of `BudDebts`: the clause bud₁ at each list of the first chain at a place of the kind -/
  bud : ∀ L ∈ G.first, L.place.kind = .K6 → Johnson.M1.BudOwed returned.F L
  /-- the kind has no list in the other two chains -/
  noneElsewhere : (∀ L ∈ G.shared, L.place.kind ≠ .K6) ∧ ∀ L ∈ G.second, L.place.kind ≠ .K6
  /-- K6's share of "On at the run", at every prover H beside the lists, input, coins, return of
  `ready`, family of invariants, list of challenges and run -/
  on : ∀ (H : Prover W₀ Rc Inst OnBytes.TableKey Cells X₀ X) (w₀ : W₀) (rc : Rc) (x : Inst)
    (k : Coins returned.B) (R : Ready W₀ Rc Inst OnBytes.TableKey Cells X₀ X)
    (T : ThreadsP returned.F returned.B (G.prover H) w₀ rc x k R) (ρ : Draws) (r : RunC returned.F),
    KindOnAtRun (G := G) (H := H) T ρ r .K6

/-- **K6's share of `BudDebts` in all three chains**: other authors' `KindBud G .K6`. In the shared and the
second chain it holds for want of a list of the kind. -/
theorem HeadConditionsOfUse.kindBud {W₀ Rc X₀ X : Type} {returned : OnlineProverWithDescription W₀ Rc Cells X₀ X}
    {G : Sides returned.F returned.B W₀ Rc OnBytes.TableKey Cells X₀ X}
    (c : HeadConditionsOfUse returned G) : Johnson.M1.KindBud G .K6 :=
  ⟨c.bud, fun L hL e => absurd e (c.noneElsewhere.1 L hL),
    fun L hL e => absurd e (c.noneElsewhere.2 L hL)⟩

/-- **K6's share of the rule's premise on On, with its own prefix**: at every relation, every prover beside
the lists and EVERY family of invariants. -/
theorem HeadConditionsOfUse.onAtEveryRun {W₀ Rc X₀ X : Type} {returned : OnlineProverWithDescription W₀ Rc Cells X₀ X}
    {G : Sides returned.F returned.B W₀ Rc OnBytes.TableKey Cells X₀ X}
    (c : HeadConditionsOfUse returned G) {H : Prover W₀ Rc Inst OnBytes.TableKey Cells X₀ X}
    (Rel : W₀ → Rc → Inst → Prop)
    (T : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R,
      ready returned.F returned.B (G.prover H) w₀ rc x k = .ok R →
      ThreadsP returned.F returned.B (G.prover H) w₀ rc x k R) :
    KindOnAtEveryRun (G := G) (H := H) Rel T .K6 :=
  fun w₀ rc x hrel k R hR ρ r _ _ _ => c.on H w₀ rc x k R (T w₀ rc x hrel k R hR) ρ r

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: the library's hypothesis; the maker returns; the lists bear the lot's row. **K6's
conditions of use at any return of the maker.** General in the filling and in the reader of the index. -/
theorem headConditionsOfUse_at_maker (h : P5J.AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x₀)
    {P : OnlineProverParts W₀ Rc Cells X₀ X} {A : OnlineProverWithDescription W₀ Rc Cells X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (weights : Pub → W₀ → Weights)
    {G : Sides A.F A.B W₀ Rc OnBytes.TableKey Cells X₀ X}
    (bear : ListsOfTheKindBear G .K6
      ((headSimulatorLot (Rc := Rc) (X := X) weights).rows A.Z A.G)) : HeadConditionsOfUse A G :=
  have s := headSimulatorShare_at_maker h hA weights
  ⟨s.budAtTheKind bear, ⟨bear.noneShared, bear.noneSecond⟩,
    fun _ _ _ _ _ _ T ρ r => s.kindOnAtRun bear T ρ r⟩

/-- **At the one base maker's return**, where the public files are in scope and pass the library's test. -/
theorem headConditionsOfUse_at_the_base_prover (files : VerifierAndGoals.PublicFiles)
    (scope : VerifierAndGoals.InScope files = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (made : ProofFile.Honest.Term.baseMaker files = .ok returned)
    {G : Sides returned.F returned.B FullSizeMatrix IndexCommitterCoins OnBytes.TableKey Cells Unit Unit}
    (bear : ListsOfTheKindBear G .K6
      ((headSimulatorLot (Rc := IndexCommitterCoins) (X := Unit) matrixInput.weights).rows returned.Z returned.G)) :
    HeadConditionsOfUse returned G := by
  obtain ⟨Zp, Np, cF, x, h⟩ := head_of_the_two_tests files scope live
  exact headConditionsOfUse_at_maker h made _ bear

/-- **The same at the honest prover's maker's return.** -/
theorem headConditionsOfUse_at_the_honest_prover (files : VerifierAndGoals.PublicFiles)
    (scope : VerifierAndGoals.InScope files = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    {returned : ProofFile.Honest.Term.OnlineReturn files}
    (made : ProofFile.Honest.Term.onlineMaker files = .ok returned)
    {G : Sides returned.F returned.B FullSizeMatrix (protocolAtFiles files).EncodingRandomness OnBytes.TableKey Cells Unit Unit}
    (bear : ListsOfTheKindBear G .K6
      ((headSimulatorLot (Rc := (protocolAtFiles files).EncodingRandomness) (X := Unit) matrixInput.weights).rows returned.Z
        returned.G)) :
    HeadConditionsOfUse returned G := by
  obtain ⟨Zp, Np, cF, x, h⟩ := head_of_the_two_tests files scope live
  exact headConditionsOfUse_at_maker h made _ bear

/-- **At either named set of public files**: at whatever the one base maker returns there, at all lists
that bear the lot's row. -/
theorem headConditionsOfUse_at_the_named_files (files : VerifierAndGoals.PublicFiles)
    (named : VerifierAndGoals.NamedFiles files) {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (made : ProofFile.Honest.Term.baseMaker files = .ok returned)
    {G : Sides returned.F returned.B FullSizeMatrix IndexCommitterCoins OnBytes.TableKey Cells Unit Unit}
    (bear : ListsOfTheKindBear G .K6
      ((headSimulatorLot (Rc := IndexCommitterCoins) (X := Unit) matrixInput.weights).rows returned.Z returned.G)) :
    HeadConditionsOfUse returned G :=
  headConditionsOfUse_at_the_base_prover files (ProofFile.Honest.K12.Light.named_in_scope files named)
    (AtFullSide.K14.live_named files named) made bear

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.HeadSimulatorShare.onAtRun
#print axioms ProofFile.Honest.K6.HeadSimulatorShare.budAtTheKind
#print axioms ProofFile.Honest.K6.HeadSimulatorShare.kindOnAtRun
#print axioms ProofFile.Honest.K6.HeadConditionsOfUse
#print axioms ProofFile.Honest.K6.HeadConditionsOfUse.kindBud
#print axioms ProofFile.Honest.K6.HeadConditionsOfUse.onAtEveryRun
#print axioms ProofFile.Honest.K6.headConditionsOfUse_at_maker
#print axioms ProofFile.Honest.K6.headConditionsOfUse_at_the_base_prover
#print axioms ProofFile.Honest.K6.headConditionsOfUse_at_the_honest_prover
#print axioms ProofFile.Honest.K6.headConditionsOfUse_at_the_named_files
