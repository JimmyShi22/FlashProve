-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SeedOracle.lean: a probability over the oracle: for ONE stored table and ONE key, both
fixed before the oracle is drawn, the probability over a uniform oracle that, at the seed of the
key's table under the oracle, the record does not single one table out.

The seed under g is a function of g's answers at the strings of the blocks 1, .., b of the seeds'
round, at the start that g gives at the string of the table's name (`seedUnder_eq`,
OnBytes/Slice/SeedRow.lean). At each start these strings are pairwise different, and none is the
name's string (OnBytes/Slice/SeedStrings.lean). An algorithm that asks the name's string and then
these strings has, under lazily sampled oracles, uniform answers; and for an event that does not
name the oracle the probability over a uniform oracle is the probability under lazy sampling (the
library's `Pr_eq_law`, Rom/EagerLazy.lean).

Main definitions.
 `askFn b q`            asks the oracle at b strings and gives the b answers.
 `seedAlg name b`       asks the name's string, then the strings of the blocks 1, .., b at the
                        answered start; gives the b answers. IT IS NOT `askSeed`
                        (OnBytes/Slice/SeedAsked.lean), which asks the blocks 0, .., 2 `seedCalls` -
                        1 and gives nothing: the two are tied through g alone (`seedAlg_det`,
                        `seedAt_ask_eq`).
Main theorems.
 `askFn_det`, `askFn_noCoin`, `askFn_lazy`   under g it gives g's answers; no coin; THE ANSWERS OF A
                        LAZILY SAMPLED ORACLE AT b DIFFERENT STRINGS THAT WERE NOT ASKED BEFORE ARE
                        UNIFORM.
 `seedAlg_det`, `seedAlg_noCoin`, `seedAlg_law`, `prCoins_seedAlg`   under g it gives `blocksUnder g
                        name b`; its law is uniform, for b + 1 below 2^48.
 `pr_blocksUnder`, `measure_blocksUnder`   equations: the average over g of "P holds of `blocksUnder
                        g name b`", and the measure of the set of these g, are the probability of P
                        over uniform blocks; for every P and every name.
 `measurableSet_blocksUnder`, `measurableSet_seedUnder`   THE ORACLES UNDER WHICH THE SEED OF A
                        KEY'S TABLE HAS A PROPERTY ARE A MEASURABLE SET. With
                        `measurable_blocksUnder`, `seedUnder_iff`.
 `coll_pr_oracle`, `coll_measure_oracle`   the bound of `coll_pr` (OnBytes/Slice/SeedBias.lean) as
                        an average over g and as a measure of a set of oracles;
                        `coll_pr_oracle_full`, `coll_measure_oracle_full`: at the sizes of
                        OnBytes/Slice/RecordFull.lean.

WHAT IT IS, AND IS NOT. ONE TABLE f AND ONE KEY k, SO ONE NAME, FIXED BEFORE g IS DRAWN: f and k are
bound outside the average. NOTHING FOR A COMMITTER THAT PICKS ITS TABLE OR ITS NAME AFTER QUESTIONS
TO g: it can try many roots; it can ask strings of the round at starts of its choice before it asks
the name's string; the table under a root need not be settled when the name's string is asked. f and
k are not tied: that f is the table under k's root is asked by nobody here. lg and s are arguments
beside the key; the field is the second. No number is evaluated: the radius is an argument;
`listMax`, `err` and the number of seeds stand as expressions. Nothing on proof of work. It is laid
into no join. That `recZ` is the programs' sample map is a reading of their text. (Of the Lean port
one part is shown: the coefficients of its row of a record's answer are `recZ`'s matrix:
`coefAt_recRow`, OnBytes/Slice/BlkRecRow.lean. Of the C++ programs nothing is shown.) A random
oracle: nothing on any hash function.

-/
import OnBytes.Slice.SeedStrings
import Rom.EagerLazy
import Rom.StateFirstRel
import Prob.LawKit
import Prob.Linear
import Run.CodingBitsLaws

set_option autoImplicit false

namespace OnBytes.Slice
open Prob Cb Cb.Ood _root_.Iop _root_.Run Rom MeasureTheory
open scoped ENNReal
open OnBytes.Tie (IdKey)

/-! ## Asking at finitely many different strings -/

/-- Asks the oracle at b strings and gives the b answers. -/
def askFn : (b : ℕ) → (Fin b → List Bool) → OComp (rom 256) (Fin b → Dig 256)
  | 0, _ => .pure fun i => i.elim0
  | b + 1, q =>
    .query () (q 0) fun r => (askFn b fun i => q i.succ).bind fun v => .pure (Fin.cons r v)

/-- Under g it gives g's answers. -/
theorem askFn_det (g : Fam (rom 256)) : ∀ (b : ℕ) (q : Fin b → List Bool),
    (askFn b q).det g = fun i => g () (q i)
  | 0, _ => funext fun i => i.elim0
  | b + 1, q => by
    show (((askFn b fun i => q i.succ).bind fun v =>
      (OComp.pure (Fin.cons (g () (q 0)) v) : OComp (rom 256) (Fin (b + 1) → Dig 256))).det g) = _
    rw [OComp.det_bind, askFn_det g b]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- It tosses no coin. -/
theorem askFn_noCoin : ∀ (b : ℕ) (q : Fin b → List Bool), (askFn b q).NoCoin
  | 0, _ => trivial
  | b + 1, _ => fun _ => OComp.NoCoin.bind (askFn_noCoin b _) fun _ => trivial

/-- **The answers of a lazily sampled oracle at b different strings that were not asked before are
uniform.** The law of the answers; nothing on the table that is left behind. -/
theorem askFn_lazy : ∀ (b : ℕ) (q : Fin b → List Bool) (T : Table (rom 256)),
    Function.Injective q → (∀ i, T () (q i) = none) →
      ((askFn b q).runLazy T).map Prod.fst = unif (Fin b → Dig 256)
  | 0, _, _, _, _ => eq_unif_of_const _ fun x y => by rw [Subsingleton.elim x y]
  | b + 1, q, T, hq, hT => by
    have e0 : (askFn (b + 1) q).runLazy T =
        (unif (Dig 256)).bind fun r =>
          ((askFn b fun i => q i.succ).bind fun v =>
            (OComp.pure (Fin.cons r v) : OComp (rom 256) (Fin (b + 1) → Dig 256))).runLazy
              (T.set () (q 0) r) := by
      show OComp.runLazy (OComp.query () (q 0) fun r =>
        (askFn b fun i => q i.succ).bind fun v =>
          (OComp.pure (Fin.cons r v) : OComp (rom 256) (Fin (b + 1) → Dig 256))) T = _
      simp only [OComp.runLazy, hT 0]
      rfl
    have e1 : ∀ r : Dig 256,
        (((askFn b fun i => q i.succ).bind fun v =>
          (OComp.pure (Fin.cons r v) : OComp (rom 256) (Fin (b + 1) → Dig 256))).runLazy
            (T.set () (q 0) r)).map Prod.fst =
          (unif (Fin b → Dig 256)).map fun v => consE b (Dig 256) (r, v) := by
      intro r
      have ih := askFn_lazy b (fun i => q i.succ) (T.set () (q 0) r)
        (fun i j h => Fin.succ_injective _ (hq h)) (fun i => by
          have hne : q i.succ ≠ q 0 := fun h => Fin.succ_ne_zero i (hq h)
          exact (Table.set_ne_point T () hne r).trans (hT i.succ))
      rw [← ih, OComp.runLazy_bind, PMF.map_bind, PMF.map_comp, ← PMF.bind_pure_comp]
      refine congrArg _ (funext fun out => ?_)
      show (PMF.pure _).map _ = _
      rw [PMF.pure_map]
      rfl
    rw [e0, PMF.map_bind]
    simp only [e1]
    rw [← map_unif_prod fun x : Dig 256 × (Fin b → Dig 256) => consE b (Dig 256) x]
    exact map_unif_equiv (consE b (Dig 256))

/-! ## The blocks of the seeds' round under a uniform oracle -/

/-- **Asks for the blocks that the draw of a table's seeds reads**: the string of the table's name;
then the strings of the blocks 1, .., b of the seeds' round at the start that was answered. It gives
the b answers. -/
def seedAlg (name : ByteArray) (b : ℕ) : OComp (rom 256) (Fin b → Dig 256) :=
  .query () (bytesToBits (seedFirst name)) fun d =>
    askFn b fun i => bytesToBits (blockStr (digToBytes d) (i.val + 1))

/-- Under g it gives `blocksUnder g name b`. -/
theorem seedAlg_det (g : Fam (rom 256)) (name : ByteArray) (b : ℕ) :
    (seedAlg name b).det g = blocksUnder g name b :=
  askFn_det g b _

/-- It tosses no coin. -/
theorem seedAlg_noCoin (name : ByteArray) (b : ℕ) : (seedAlg name b).NoCoin :=
  fun _ => askFn_noCoin b _

/-- **Under lazily sampled oracles these blocks are uniform**, for b + 1 below 2^48: at each start
the strings are pairwise different, and none is the string of the name. -/
theorem seedAlg_law (name : ByteArray) (b : ℕ) (hb : b + 1 < 2 ^ 48) :
    (seedAlg name b).law = unif (Fin b → Dig 256) := by
  have e0 : (seedAlg name b).runLazy (Table.empty (rom 256)) =
      (unif (Dig 256)).bind fun d =>
        (askFn b fun i => bytesToBits (blockStr (digToBytes d) (i.val + 1))).runLazy
          ((Table.empty (rom 256)).set () (bytesToBits (seedFirst name)) d) := rfl
  unfold OComp.law
  rw [e0, PMF.map_bind]
  have e1 : ∀ d : Dig 256,
      ((askFn b fun i => bytesToBits (blockStr (digToBytes d) (i.val + 1))).runLazy
        ((Table.empty (rom 256)).set () (bytesToBits (seedFirst name)) d)).map Prod.fst =
        unif (Fin b → Dig 256) := fun d =>
    askFn_lazy b _ _
      (fun i j h => Fin.ext (Nat.succ.inj (blockStr_inj (digToBytes d) (size_digToBytes d) _ _
        (by have := i.isLt; omega) (by have := j.isLt; omega) (bytesToBits_inj h))))
      (fun i => by
        have hne : bytesToBits (blockStr (digToBytes d) (i.val + 1)) ≠
            bytesToBits (seedFirst name) :=
          fun h => seedFirst_ne_blockStr name _ _ (bytesToBits_inj h).symm
        exact Table.set_ne_point (Table.empty (rom 256)) () hne d)
  simp only [e1]
  exact PMF.bind_const _ _

/-- With the oracle fixed, the probability that the algorithm's value lies in a set is 1 or 0. -/
theorem prCoins_seedAlg (g : Fam (rom 256)) (name : ByteArray) (b : ℕ)
    (P : (Fin b → Dig 256) → Prop) [Decidable (P (blocksUnder g name b))] :
    PrCoins g (seedAlg name b) {u | P u} = if P (blocksUnder g name b) then 1 else 0 := by
  unfold PrCoins
  rw [(seedAlg_noCoin name b).runEager g, pr_pure, seedAlg_det]
  by_cases h : P (blocksUnder g name b)
  · rw [if_pos h, if_pos (show blocksUnder g name b ∈ {u | P u} from h)]
  · rw [if_neg h, if_neg (show blocksUnder g name b ∉ {u | P u} from h)]

open Classical in
/-- **THE BLOCKS THAT THE DRAW READS ARE UNIFORM UNDER A UNIFORM ORACLE, FOR ONE NAME FIXED
BEFOREHAND**: the average over g of "P holds of `blocksUnder g name b`" is the probability of P over
uniform blocks. -/
theorem pr_blocksUnder (name : ByteArray) (b : ℕ) (hb : b + 1 < 2 ^ 48)
    (P : (Fin b → Dig 256) → Prop) :
    ∫⁻ g, (if P (blocksUnder g name b) then 1 else 0) ∂(U (rom 256)) =
      pr (unif (Fin b → Dig 256)) {u | P u} := by
  rw [← seedAlg_law name b hb, ← Pr_eq_law]
  unfold Rom.Pr
  exact lintegral_congr fun g => (prCoins_seedAlg g name b P).symm

open Classical in
/-- "P holds of `blocksUnder g name b`", as a function of g with the values 1 and 0, is measurable.
-/
theorem measurable_blocksUnder (name : ByteArray) (b : ℕ) (P : (Fin b → Dig 256) → Prop) :
    Measurable fun g : Fam (rom 256) => (if P (blocksUnder g name b) then 1 else 0 : ℝ≥0∞) := by
  have h := measurable_PrCoins (seedAlg name b) {u | P u}
  have e : (fun g : Fam (rom 256) => PrCoins g (seedAlg name b) {u | P u}) =
      fun g => (if P (blocksUnder g name b) then 1 else 0 : ℝ≥0∞) :=
    funext fun g => prCoins_seedAlg g name b P
  rwa [e] at h

/-- **The oracles under which P holds of `blocksUnder g name b` are a measurable set.** -/
theorem measurableSet_blocksUnder (name : ByteArray) (b : ℕ) (P : (Fin b → Dig 256) → Prop) :
    MeasurableSet {g : Fam (rom 256) | P (blocksUnder g name b)} := by
  classical
  have h := measurable_blocksUnder name b P (measurableSet_singleton (1 : ℝ≥0∞))
  have e : (fun g : Fam (rom 256) => (if P (blocksUnder g name b) then 1 else 0 : ℝ≥0∞)) ⁻¹' {1} =
      {g | P (blocksUnder g name b)} := by
    ext g
    by_cases hp : P (blocksUnder g name b) <;> simp [hp]
  rwa [e] at h

/-- **The same as a measure of a set of oracles**: an equation. -/
theorem measure_blocksUnder (name : ByteArray) (b : ℕ) (hb : b + 1 < 2 ^ 48)
    (P : (Fin b → Dig 256) → Prop) :
    U (rom 256) {g | P (blocksUnder g name b)} = pr (unif (Fin b → Dig 256)) {u | P u} := by
  classical
  rw [← pr_blocksUnder name b hb P, ← lintegral_indicator_one (measurableSet_blocksUnder name b P)]
  refine lintegral_congr fun g => ?_
  by_cases hp : P (blocksUnder g name b)
  · rw [if_pos hp, Set.indicator_of_mem (show g ∈ {g | P (blocksUnder g name b)} from hp)]
    rfl
  · rw [if_neg hp, Set.indicator_of_notMem (show g ∉ {g | P (blocksUnder g name b)} from hp)]

/-- What is said of the seed under g is said of `blocksUnder g`. -/
theorem seedUnder_iff (lg s : ℕ) (k : IdKey) (g : Fam (rom 256))
    (Q : (Fin s → (Fin lg → GE) × NZ) → Prop) :
    (∃ ρ, seedUnder lg s k g = some ρ ∧ Q ρ) ↔
      Q (toSeed lg s ((seedBS lg s).φ
        (blocksUnder g (Key.nameOf k.1 k.2.1 k.2.2) (seedBS lg s).b))) := by
  rw [seedUnder_eq]
  constructor
  · rintro ⟨ρ, h1, h2⟩
    rw [Option.some.inj h1]
    exact h2
  · exact fun h => ⟨_, rfl, h⟩

/-- **The oracles under which the seed of k's table has a property are a measurable set.** -/
theorem measurableSet_seedUnder (lg s : ℕ) (k : IdKey)
    (Q : (Fin s → (Fin lg → GE) × NZ) → Prop) :
    MeasurableSet {g : Fam (rom 256) | ∃ ρ, seedUnder lg s k g = some ρ ∧ Q ρ} := by
  have e : {g : Fam (rom 256) | ∃ ρ, seedUnder lg s k g = some ρ ∧ Q ρ} =
      {g | Q (toSeed lg s ((seedBS lg s).φ
        (blocksUnder g (Key.nameOf k.1 k.2.1 k.2.2) (seedBS lg s).b)))} :=
    Set.ext fun g => seedUnder_iff lg s k g Q
  rw [e]
  exact measurableSet_blocksUnder _ _ fun u => Q (toSeed lg s ((seedBS lg s).φ u))

open Classical in
/-- **A PROBABILITY OVER THE ORACLE: ONE TABLE f AND ONE KEY k, FIXED BEFORE g IS DRAWN.** Within
the Johnson bound: the average over a uniform g of "at the seed of k's table under g the record does
not single one table out of f's list" (`DecR.coll`: two members with different message parts have
the same answers) is at most the bound of `coll_pr`. f and k are not tied: that f is the table under
k's root is not asked. lg and s are arguments beside the key. -/
theorem coll_pr_oracle (T : Fmt.M1.Code) (v eM lg s : ℕ) (ha : T.a ≤ 32)
    (hk : T.r + T.l ≤ 2 ^ T.a) (he : eM < 2 ^ T.a - (T.r + T.l) + 1)
    (hJ : InJohnson (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM) (h3 : 3 * s ≤ T.l)
    (hl : T.l - 3 * s ≤ 2 ^ lg) (hb : (seedBS lg s).b + 1 < 2 ^ 48)
    (f : Fin (2 ^ T.a) → Run.PQ.SgX) (k : IdKey) :
    ∫⁻ g, (if ∃ ρ, seedUnder lg s k g = some ρ ∧ (decRec T v eM lg s).coll f ρ then 1 else 0)
        ∂(U (rom 256)) ≤
      kapSl 128 ^ (seedBS lg s).b *
        ((((listMax (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM).choose 2 * (recZ T.l lg s).err : ℕ) :
          ℝ≥0∞) / Fintype.card (recZ T.l lg s).D) := by
  refine le_trans (le_of_eq ?_) (coll_pr_toSeed T v eM lg s ha hk he hJ h3 hl f)
  rw [← pr_blocksUnder (Key.nameOf k.1 k.2.1 k.2.2) (seedBS lg s).b hb fun u =>
    (decRec T v eM lg s).coll f (toSeed lg s ((seedBS lg s).φ u))]
  refine lintegral_congr fun g => ?_
  have hiff : (∃ ρ, seedUnder lg s k g = some ρ ∧ (decRec T v eM lg s).coll f ρ) ↔
      (decRec T v eM lg s).coll f (toSeed lg s ((seedBS lg s).φ
        (blocksUnder g (Key.nameOf k.1 k.2.1 k.2.2) (seedBS lg s).b))) := by
    rw [seedUnder_eq]
    constructor
    · rintro ⟨ρ, h1, h2⟩
      rw [Option.some.inj h1]
      exact h2
    · exact fun h => ⟨_, rfl, h⟩
  simp only [hiff]

/-- **The same as a measure of a set of oracles** (the set is measurable:
`measurableSet_seedUnder`). -/
theorem coll_measure_oracle (T : Fmt.M1.Code) (v eM lg s : ℕ) (ha : T.a ≤ 32)
    (hk : T.r + T.l ≤ 2 ^ T.a) (he : eM < 2 ^ T.a - (T.r + T.l) + 1)
    (hJ : InJohnson (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM) (h3 : 3 * s ≤ T.l)
    (hl : T.l - 3 * s ≤ 2 ^ lg) (hb : (seedBS lg s).b + 1 < 2 ^ 48)
    (f : Fin (2 ^ T.a) → Run.PQ.SgX) (k : IdKey) :
    U (rom 256) {g | ∃ ρ, seedUnder lg s k g = some ρ ∧ (decRec T v eM lg s).coll f ρ} ≤
      kapSl 128 ^ (seedBS lg s).b *
        ((((listMax (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM).choose 2 * (recZ T.l lg s).err : ℕ) :
          ℝ≥0∞) / Fintype.card (recZ T.l lg s).D) := by
  have e : {g : Fam (rom 256) | ∃ ρ, seedUnder lg s k g = some ρ ∧
      (decRec T v eM lg s).coll f ρ} =
      {g | (decRec T v eM lg s).coll f (toSeed lg s ((seedBS lg s).φ
        (blocksUnder g (Key.nameOf k.1 k.2.1 k.2.2) (seedBS lg s).b)))} :=
    Set.ext fun g => seedUnder_iff lg s k g _
  rw [e, measure_blocksUnder _ _ hb fun u =>
    (decRec T v eM lg s).coll f (toSeed lg s ((seedBS lg s).φ u))]
  exact coll_pr_toSeed T v eM lg s ha hk he hJ h3 hl f

open Classical in
/-- **At the sizes of OnBytes/Slice/RecordFull.lean**; the radius eM is an argument, within the
Johnson bound. ONE table f and ONE key k, fixed before g is drawn. f and k are not tied; k is any
key, whatever shape it holds. No number on the right is evaluated. -/
theorem coll_pr_oracle_full (eM : ℕ) (he : eM < 3848273922)
    (hJ : InJohnson (2 ^ 32) 3848273922 eM) (f : Fin (2 ^ recT.a) → Run.PQ.SgX) (k : IdKey) :
    ∫⁻ g, (if ∃ ρ, seedUnder recLg recS k g = some ρ ∧ (decRecFull eM).coll f ρ then 1 else 0)
        ∂(U (rom 256)) ≤
      kapSl 128 ^ 140 *
        ((((listMax (2 ^ 32) 3848273922 eM).choose 2 * (recZ recT.l recLg recS).err : ℕ) : ℝ≥0∞) /
          Fintype.card (recZ recT.l recLg recS).D) := by
  have h := coll_pr_oracle recT recV eM recLg recS (by decide) (by decide) he hJ recT_room.1
    recT_room.2 (by rw [seedBS_b_full]; decide) f k
  have e : kapSl 128 ^ (seedBS recLg recS).b = kapSl 128 ^ 140 := by rw [seedBS_b_full]
  rwa [e] at h

/-- **The same as a measure of a set of oracles**, at these sizes (the set is measurable:
`measurableSet_seedUnder`). f and k are not tied; k is any key, whatever shape it holds. -/
theorem coll_measure_oracle_full (eM : ℕ) (he : eM < 3848273922)
    (hJ : InJohnson (2 ^ 32) 3848273922 eM) (f : Fin (2 ^ recT.a) → Run.PQ.SgX) (k : IdKey) :
    U (rom 256) {g | ∃ ρ, seedUnder recLg recS k g = some ρ ∧ (decRecFull eM).coll f ρ} ≤
      kapSl 128 ^ 140 *
        ((((listMax (2 ^ 32) 3848273922 eM).choose 2 * (recZ recT.l recLg recS).err : ℕ) : ℝ≥0∞) /
          Fintype.card (recZ recT.l recLg recS).D) := by
  have h := coll_measure_oracle recT recV eM recLg recS (by decide) (by decide) he hJ recT_room.1
    recT_room.2 (by rw [seedBS_b_full]; decide) f k
  have e : kapSl 128 ^ (seedBS recLg recS).b = kapSl 128 ^ 140 := by rw [seedBS_b_full]
  rwa [e] at h

end OnBytes.Slice

#print axioms OnBytes.Slice.askFn_det
#print axioms OnBytes.Slice.askFn_noCoin
#print axioms OnBytes.Slice.askFn_lazy
#print axioms OnBytes.Slice.seedAlg_det
#print axioms OnBytes.Slice.seedAlg_noCoin
#print axioms OnBytes.Slice.seedAlg_law
#print axioms OnBytes.Slice.prCoins_seedAlg
#print axioms OnBytes.Slice.pr_blocksUnder
#print axioms OnBytes.Slice.measurable_blocksUnder
#print axioms OnBytes.Slice.measurableSet_blocksUnder
#print axioms OnBytes.Slice.measure_blocksUnder
#print axioms OnBytes.Slice.seedUnder_iff
#print axioms OnBytes.Slice.measurableSet_seedUnder
#print axioms OnBytes.Slice.coll_pr_oracle
#print axioms OnBytes.Slice.coll_measure_oracle
#print axioms OnBytes.Slice.coll_pr_oracle_full
#print axioms OnBytes.Slice.coll_measure_oracle_full
