-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/FitsLen.lean: for each chain of a whole file as many roots were read as the chain's
rounds have trees, at the makers' wire record and the makers' typing: three of the eight fields of
`Fits` (OnBytes/TypedOracleCompiler/Joined/K/RunsAt.lean).

`Fits F k₁ k₂ k₃` is asked before the three chains of a file can be shown to have values under fixed
oracle functions. Its fields `len₁`, `len₂`, `len₃` compare the number of roots in what was read for
a chain with the number of trees in the wire records of the chain's rounds. Here the wire record is
`wqWhole` (OnBytes/Maker/Wire.lean) and what was read is `strAt₁`, `strAt₂`, `strAt₃`
(OnBytes/Maker/TypingParts.lean), at the data that are made of three lists of rounds
(`Three.Whole.of`, OnBytes/Three/Data.lean). Nothing names a key file or a proof file: the letters
serve both.

Main names:
  `sumJ_wiresLo`, `sum0_wiresSh`: a stretch's wire records have as many trees as its data hold.
  `sumJ_whole₁`, `sum_whole₂`, `sumJ_whole₃`: the same at the three chains of `wqWhole`: a silent
    round has no tree.
  `trees_ds₃`: the third stretch's data hold as many trees as the third list of rounds has items
    "root". `trees_ds₁₂`: the first two stretches', where the makers' tests pass (`countsFit`).
  `len₁_whole`, `len₂_whole`, `len₃_whole`: THE THREE FIELDS.

What is asked: that the makers' tests pass at the three lists of rounds (`okAt`; for the first two
fields alone); for each chain, that the reading holds as many roots as the chain's list of rounds
has items "root".

Limits: the three counts on the reading are premises (OnBytes/Maker/ReadSpecs.lean,
`readChain_roots`, and OnBytes/Maker/RootsCount.lean, `third_roots`, give them from the program's
own reading). The other five fields of `Fits` are not here. Nothing on what the chains' values are;
nothing on soundness.

Terms: lean/GLOSSARY.md.


-/
import OnBytes.Maker.LineAt
import OnBytes.Maker.TypingParts
import OnBytes.Maker.RootsOfTrees
import OnBytes.Maker.ReadData
import OnBytes.Maker.Files
import OnBytes.TypedOracleCompiler.Joined.K.RunsAt

set_option autoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined _root_.Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

section Wire
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- A stretch of local rounds has, over the slot's components, as many trees as its data hold. -/
theorem sumJ_wiresLo : ∀ ds : List RDT,
    sumJ (uLT C ds) (RoundSplits.allLocal (uLT C ds)) (wiresLo C K chal ds) =
      (ds.map (·.trees.length)).sum
  | [] => rfl
  | d :: ds => by
    show (d.trees.map (·.a)).length + sumJ (uLT C ds) _ (wiresLo C K chal ds) = _
    rw [sumJ_wiresLo ds, List.length_map, List.map_cons, List.sum_cons]

/-- A stretch of shared rounds has, over the shared components, as many trees as its data hold. -/
theorem sum0_wiresSh : ∀ ds : List RDT,
    sum0 (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) (wiresSh C K chal ds) =
      (ds.map (·.trees.length)).sum
  | [] => rfl
  | d :: ds => by
    show (d.trees.map (·.a)).length + sum0 (uLT C ds) _ (wiresSh C K chal ds) = _
    rw [sum0_wiresSh ds, List.length_map, List.map_cons, List.sum_cons]

variable (D : WholeD) {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3)
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- The first chain's rounds have as many trees as the first stretch's data hold. -/
theorem sumJ_whole₁ :
    sumJ (chainsOf C D tF tJ t3).c₁ (chainsOf C D tF tJ t3).A₁
      (wire₁ (wqWhole C K chal D tF tJ t3 silent run)) = (D.ds₁.map (·.trees.length)).sum := by
  rw [wire₁_whole]
  show 0 + sumJ (uLT C D.ds₁) _ (wiresLo C K chal D.ds₁) = _
  rw [sumJ_wiresLo, Nat.zero_add]

/-- The second chain's: the joining round has none. -/
theorem sum_whole₂ :
    (wire₂ (wqWhole C K chal D tF tJ t3 silent run)).1.depthJ.length +
      ((wire₂ (wqWhole C K chal D tF tJ t3 silent run)).1.depth0.length +
        sum0 (chainsOf C D tF tJ t3).s₂
          (RoundSplits.const (RAnn.ofShared .sh) (chainsOf C D tF tJ t3).s₂)
          (wire₂ (wqWhole C K chal D tF tJ t3 silent run)).2) =
      (D.ds₂.map (·.trees.length)).sum := by
  rw [wire₂_whole]
  show 0 + (0 + sum0 (uLT C D.ds₂) _ (wiresSh C K chal D.ds₂)) = _
  rw [sum0_wiresSh, Nat.zero_add, Nat.zero_add]

/-- The third chain's. -/
theorem sumJ_whole₃ :
    sumJ (chainsOf C D tF tJ t3).c₃ (chainsOf C D tF tJ t3).A₃
      (wire₃ (wqWhole C K chal D tF tJ t3 silent run)) = (D.ds₃.map (·.trees.length)).sum := by
  rw [wire₃_whole]
  show 0 + sumJ (uLT C D.ds₃) _ (wiresLo C K chal D.ds₃) = _
  rw [sumJ_wiresLo, Nat.zero_add]

end Wire

section Data
variable (a : ℕ) (R₁ R₂ R₃ : Params.Rounds)

/-- The third stretch's data hold as many trees as the third list of rounds has items "root". -/
theorem trees_ds₃ :
    ((WholeD.of a (Three.Whole.of R₁ R₂ R₃)).ds₃.map (·.trees.length)).sum = Three.rootsIn R₃ := by
  show (((Three.Whole.of R₁ R₂ R₃).ds₃.map rdtOf).map (·.trees.length)).sum = _
  rw [List.map_map]
  exact congrArg List.sum (rdsFromL_map _ _ _ _ _ _ _
    (fun r => r.1.items.countP (· == .root))
    (fun r n => by
      show ((List.range (r.1.items.countP (· == .root))).map _).length = _
      rw [List.length_map, List.length_range]) R₃)

/-- The first two stretches', where the makers' tests pass. -/
theorem trees_ds₁₂ (hok : okAt a (some (R₁, R₂, R₃)) = true) :
    ((WholeD.of a (Three.Whole.of R₁ R₂ R₃)).ds₁.map (·.trees.length)).sum = Three.rootsIn R₁ ∧
      ((WholeD.of a (Three.Whole.of R₁ R₂ R₃)).ds₂.map (·.trees.length)).sum =
        Three.rootsIn R₂ := by
  have h := (okAt_parts hok).counts
  unfold countsFit at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h

end Data

section Len
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (a : ℕ)
  (R₁ R₂ R₃ : Params.Rounds) {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3)
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool) (sb : ℕ)
  (r : Proof.TailRead)

/-- **The field `len₁` of `Fits`** (OnBytes/TypedOracleCompiler/Joined/K/RunsAt.lean). -/
theorem len₁_whole (hok : okAt a (some (R₁, R₂, R₃)) = true)
    (n₁ : Three.rootsIn R₁ = r.first.roots.length) (pF : TF) :
    (strAt₁ C a (Three.Whole.of R₁ R₂ R₃) tF tJ t3 sb pF r).roots.length =
      sumJ (chainsOf C (WholeD.of a (Three.Whole.of R₁ R₂ R₃)) tF tJ t3).c₁
        (chainsOf C (WholeD.of a (Three.Whole.of R₁ R₂ R₃)) tF tJ t3).A₁
        (wire₁ (wqWhole C K chal (WholeD.of a (Three.Whole.of R₁ R₂ R₃)) tF tJ t3 silent run)) := by
  rw [sumJ_whole₁, (trees_ds₁₂ a R₁ R₂ R₃ hok).1, n₁]
  show (rootsT r.first.out.rounds.toList).length = _
  rw [rootsT_eq_roots, List.length_map]

/-- **The field `len₂`.** -/
theorem len₂_whole (hok : okAt a (some (R₁, R₂, R₃)) = true)
    (n₂ : Three.rootsIn R₂ = r.shared.roots.length) (pJ : TJ) :
    (strAt₂ C a (Three.Whole.of R₁ R₂ R₃) tF tJ t3 sb pJ r).roots.length =
      (wire₂ (wqWhole C K chal (WholeD.of a (Three.Whole.of R₁ R₂ R₃)) tF tJ t3 silent
          run)).1.depthJ.length +
        ((wire₂ (wqWhole C K chal (WholeD.of a (Three.Whole.of R₁ R₂ R₃)) tF tJ t3 silent
            run)).1.depth0.length +
          sum0 (chainsOf C (WholeD.of a (Three.Whole.of R₁ R₂ R₃)) tF tJ t3).s₂
            (RoundSplits.const (RAnn.ofShared .sh)
              (chainsOf C (WholeD.of a (Three.Whole.of R₁ R₂ R₃)) tF tJ t3).s₂)
            (wire₂ (wqWhole C K chal (WholeD.of a (Three.Whole.of R₁ R₂ R₃)) tF tJ t3 silent
              run)).2) := by
  rw [sum_whole₂, (trees_ds₁₂ a R₁ R₂ R₃ hok).2, n₂]
  show (rootsT r.shared.out.rounds.toList).length = _
  rw [rootsT_eq_roots, List.length_map]

/-- **The field `len₃`.** -/
theorem len₃_whole (n₃ : Three.rootsIn R₃ = r.second.roots.length) (p3 : T3) :
    (strAt₃ C a (Three.Whole.of R₁ R₂ R₃) tF tJ t3 sb p3 r).roots.length =
      sumJ (chainsOf C (WholeD.of a (Three.Whole.of R₁ R₂ R₃)) tF tJ t3).c₃
        (chainsOf C (WholeD.of a (Three.Whole.of R₁ R₂ R₃)) tF tJ t3).A₃
        (wire₃ (wqWhole C K chal (WholeD.of a (Three.Whole.of R₁ R₂ R₃)) tF tJ t3 silent run)) := by
  rw [sumJ_whole₃, trees_ds₃, n₃]
  show (rootsT r.second.out.rounds.toList).length = _
  rw [rootsT_eq_roots, List.length_map]

end Len

end OnBytes.Maker
