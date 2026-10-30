-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/DataRounds.lean: THE DATA OF A FILE's ROUNDS, ROUND BY ROUND, OFF THE
DESCRIPTION's DECLARED ROUNDS: entry, kind, items, THE NUMBER OF TREES SENT, stored tables; and THE
SHAPES OF ALL THE FILE's TREES IN A ROW, against the declared openings. Definitions, statements and
proofs.

Beside Johnson/Desc/BlockSlotOpens.lean (`opensOfData`: the stored tables and the openings by
number), after its proof and over the same laws of Johnson/Desc/BlockSlotProofs.lean.

  `RoundAsG d r`: the data d have the declared round r's entry; the kind of its name; its cut into
    items; as many trees as its entry has roots; its stored tables.
  `RoundsAre F D`, `roundsOfData`: **at a description F with F.data file = .ok D**: chain by chain,
    round by round (the first chain's declared rounds without their last, the sealing round).
  `allTrees W`: the shapes of all trees that the three chains send, in the file's order.
    `treeIs_iff`: the makers' table has the shape s at number j just if `allTrees` has.
  `allT D`: the same off the data D. `OpensShaped`, `opensShaped`: **every declared opening o of
    chain c finds its own shape at `allT D`'s number numAt t₁ t₂ c o.2**; and D.t₁ = F.t₁,
    D.t₂ = F.t₂.
  `chainTrees`, `cutTrees`: where each chain's trees lie in `allT D` (from 0, from t₁, from
    t₁ + t₂), and a cut's trees in its chain's.
Limits: nothing on soundness. The first chain's sealing round's data are not in D.ds₁: by the
makers' test on the counts it sends no tree.
A tool.
-/
import Johnson.Desc.BlockSlotOpens
import OnBytes.Maker.OkOfLeft
import OnBytes.Maker.TableChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc
open OnBytes OnBytes.Maker
open OnBytes.Three (wholeNo opensOf rdOf rdsFromL tagRoot tagRun rootsIn treesOfChain sentBefore)

/-- A round's data against its declared round. -/
def RoundAsG (d : RDT) (r : Fmt.DeclaredRound) : Prop :=
  d.entry = r.entry ∧ Fmt.kindOf r.entry.name = some d.kind ∧ d.items = r.items ∧
    d.trees.length = r.entry.roots ∧ d.stored = r.stored

theorem round_kind {e : List (List ByteArray × ByteArray)} {r : Fmt.DeclaredRound} {y : Fmt.Round}
    (h : r.round e = some y) : Fmt.kindOf r.entry.name = some y.kind := by
  unfold Fmt.DeclaredRound.round at h
  cases hk : Fmt.kindOf r.entry.name with
  | none => rw [hk] at h; cases h
  | some k =>
    rw [hk] at h
    obtain ⟨os, _, rfl⟩ := Option.map_eq_some_iff.1 h
    rfl

theorem zip_as (all : List (ℕ × Fmt.Shape × ℕ × ℕ)) (t₁ t₂ here base first : ℕ)
    {e : List (List ByteArray × ByteArray)} {l : List Fmt.DeclaredRound} {R : Params.Rounds}
    (hw : List.Forall₂ (Written e) l R) :
    (∀ x ∈ R, x.1.items.countP (· == .root) = x.1.entry.roots) →
    ∀ L : List ℕ, L.length = R.length →
      List.Forall₂ RoundAsG ((List.zipWith (rdOf all t₁ t₂ here base first) R L).map rdtOf) l := by
  induction hw with
  | nil => intro _ L _; rw [List.zipWith_nil_left]; exact .nil
  | @cons r x l R hd _ ih =>
    intro hf L hL
    cases L with
    | nil => cases hL
    | cons n L =>
      obtain ⟨y, hy, rfl⟩ := hd
      obtain ⟨a1, a2, _⟩ := round_ok hy
      rw [List.zipWith_cons_cons, List.map_cons]
      refine .cons ⟨a1, round_kind hy, a2, ?_, rfl⟩
        (ih (fun x' hx' => hf x' (List.mem_cons_of_mem _ hx')) L (Nat.succ.inj hL))
      show ((List.range _).map _).length = _
      rw [List.length_map, List.length_range, hf _ List.mem_cons_self, a1]

theorem chain_as (all : List (ℕ × Fmt.Shape × ℕ × ℕ)) (t₁ t₂ here base first : ℕ)
    {e : List (List ByteArray × ByteArray)} {l : List Fmt.DeclaredRound} {R : Params.Rounds}
    (hw : List.Forall₂ (Written e) l R)
    (hf : ∀ x ∈ R, x.1.items.countP (· == .root) = x.1.entry.roots) :
    List.Forall₂ RoundAsG ((rdsFromL all t₁ t₂ here base first R).map rdtOf) l :=
  zip_as all t₁ t₂ here base first hw hf _ (sentBefore_length R)

/-- The statement: round by round, chain by chain. -/
def RoundsAre {Xi : Type} (F : FileDescription Xi) (D : WholeD) : Prop :=
  List.Forall₂ RoundAsG D.ds₁ F.roundsDeclaredByBlocks.1.dropLast ∧ List.Forall₂ RoundAsG D.ds₂ F.roundsDeclaredByBlocks.2.1 ∧
    List.Forall₂ RoundAsG D.ds₃ F.roundsDeclaredByBlocks.2.2

/-- **The data of a file's rounds are the declared rounds', round by round.** -/
theorem roundsOfData {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D) : RoundsAre F D := by
  obtain ⟨⟨R₁, R₂, R₃⟩, hR, hk, rfl⟩ := data_ok h
  obtain ⟨w₁, w₂, w₃⟩ := writtenOf_ok hR
  have hf : Three.Whole.fits R₁ R₂ R₃ 2 = true := (okAt_parts hk).fits
  refine ⟨?_, chain_as _ _ _ _ _ _ w₂ (fits_roots hf (1, R₂) (by simp)),
    chain_as _ _ _ _ _ _ w₃ (fits_roots hf (2, R₃) (by simp))⟩
  have c₁ := chain_as (Three.Whole.of R₁ R₂ R₃).opens (rootsIn R₁) (rootsIn R₂) 0 0 0 w₁
    (fits_roots hf (0, R₁) (by simp))
  have c₁' := forall₂_dropLast c₁
  rw [← List.map_dropLast] at c₁'
  exact c₁'

/-- The shapes of all trees that the three chains send, in the file's order. -/
def allTrees (W : Three.Whole) : List Fmt.Shape :=
  W.ds₁.flatMap (·.trees) ++ (W.ds₂.flatMap (·.trees) ++ W.ds₃.flatMap (·.trees))

theorem table_shapes (R₁ R₂ R₃ : Params.Rounds) :
    (Three.Whole.of R₁ R₂ R₃).table.map (·.shape) = allTrees (Three.Whole.of R₁ R₂ R₃) := by
  show (treesOfChain _ 0 0 _ ++ (treesOfChain _ 1 _ _ ++ treesOfChain _ 2 _ _)).map (·.shape) = _
  rw [List.map_append, List.map_append, treesOfChain_shapes, treesOfChain_shapes,
    treesOfChain_shapes]
  rfl

theorem treeIs_iff (R₁ R₂ R₃ : Params.Rounds) (s : Fmt.Shape) (j : ℕ) :
    TreeIs (Three.Whole.of R₁ R₂ R₃) s j ↔ (allTrees (Three.Whole.of R₁ R₂ R₃))[j]? = some s := by
  rw [← table_shapes, List.getElem?_map]
  unfold TreeIs
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [ht]
    rfl
  · intro h
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨t, ht, rfl⟩

/-! ## At the data D -/

/-- The shapes of all trees that the data's three lists of rounds send, in the file's order. -/
def allT (D : WholeD) : List Fmt.Shape :=
  D.ds₁.flatMap (·.trees) ++ (D.ds₂.flatMap (·.trees) ++ D.ds₃.flatMap (·.trees))

theorem flat_len (ds : List RDT) :
    (ds.flatMap (·.trees)).length = (ds.map (·.trees.length)).sum := by
  induction ds with
  | nil => rfl
  | cons d ds ih => rw [List.flatMap_cons, List.length_append, ih, List.map_cons, List.sum_cons]

theorem flat_rdt (ds : List Three.RDL) :
    (ds.map rdtOf).flatMap (·.trees) = ds.flatMap (·.trees) := by
  rw [List.flatMap_map]
  rfl

/-- Where the sealing round sends no tree, the data's trees are the whole's. -/
theorem allT_of (a : ℕ) (W : Three.Whole)
    (h : (W.ds₁.dropLast.flatMap (·.trees)).length = (W.ds₁.flatMap (·.trees)).length) :
    allT (WholeD.of a W) = allTrees W := by
  have e : W.ds₁.dropLast.flatMap (·.trees) = W.ds₁.flatMap (·.trees) := by
    rcases List.eq_nil_or_concat W.ds₁ with h0 | ⟨L, b, hb⟩
    · rw [h0]
      rfl
    · rw [hb, List.concat_eq_append, List.dropLast_concat] at h ⊢
      rw [List.flatMap_append, List.length_append] at h
      rw [List.flatMap_append]
      have hb0 : [b].flatMap (·.trees) = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [hb0, List.append_nil]
  show (W.stretch₁.map rdtOf).flatMap (·.trees) ++
    ((W.ds₂.map rdtOf).flatMap (·.trees) ++ (W.ds₃.map rdtOf).flatMap (·.trees)) = _
  rw [flat_rdt, flat_rdt, flat_rdt]
  show W.ds₁.dropLast.flatMap (·.trees) ++ _ = _
  rw [e]
  rfl

/-- The statement: every declared opening finds its own shape among all the file's trees, at its
number over the file. -/
def OpensShaped {Xi : Type} (F : FileDescription Xi) (D : WholeD) : Prop :=
  (∀ r ∈ F.roundsDeclaredByBlocks.1, ∀ o ∈ r.opens, (allT D)[numAt F.t₁ F.t₂ 0 o.2]? = some o.1) ∧
    (∀ r ∈ F.roundsDeclaredByBlocks.2.1, ∀ o ∈ r.opens, (allT D)[numAt F.t₁ F.t₂ 1 o.2]? = some o.1) ∧
    ∀ r ∈ F.roundsDeclaredByBlocks.2.2, ∀ o ∈ r.opens, (allT D)[numAt F.t₁ F.t₂ 2 o.2]? = some o.1

theorem shaped_of_is (R₁ R₂ R₃ : Params.Rounds) (num : Fmt.TreeSource → ℕ) {ds : List Three.RDL}
    {l : List Fmt.DeclaredRound}
    (h : List.Forall₂ (RoundIs (Three.Whole.of R₁ R₂ R₃) num) ds l) :
    ∀ r ∈ l, ∀ o ∈ r.opens, (allTrees (Three.Whole.of R₁ R₂ R₃))[num o.2]? = some o.1 := by
  intro r hr o ho
  obtain ⟨d, hd⟩ := forall₂_right h r hr
  exact (treeIs_iff R₁ R₂ R₃ o.1 (num o.2)).1 (hd.2.2 o ho)

/-- **Every declared opening finds its own shape at its number over the file**; and the numbers of
trees that the first two chains send are the declared roots'. -/
theorem opensShaped {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D) : OpensShaped F D ∧ D.t₁ = F.t₁ ∧ D.t₂ = F.t₂ := by
  obtain ⟨⟨R₁, R₂, R₃⟩, hR, hk, rfl⟩ := data_ok h
  obtain ⟨w₁, w₂, w₃⟩ := writtenOf_ok hR
  have parts := okAt_parts hk
  have hf : Three.Whole.fits R₁ R₂ R₃ 2 = true := parts.fits
  have e₁ : rootsIn R₁ = F.t₁ := rootsIn_eq w₁ (fits_roots hf (0, R₁) (by simp))
  have e₂ : rootsIn R₂ = F.t₂ := rootsIn_eq w₂ (fits_roots hf (1, R₂) (by simp))
  have hst : standIns F.roundsDeclaredByBlocks =
      [((List.range (rootsIn R₁)).map tagRoot, tagRun 1),
       ((List.range (rootsIn R₂)).map tagRoot, tagRun 2)] := by
    rw [e₁, e₂]; rfl
  rw [hst] at w₃
  have c₁ : List.Forall₂ (RoundIs (Three.Whole.of R₁ R₂ R₃) (numAt F.t₁ F.t₂ 0))
      (Three.Whole.of R₁ R₂ R₃).ds₁ F.roundsDeclaredByBlocks.1 := by
    rw [← e₁, ← e₂]
    exact chain_is _ _ 0 0 (namesGo₀ _ _) w₁
      fun z hz => fits_trees hf z (List.mem_append_left _ hz)
  have c₂ : List.Forall₂ (RoundIs (Three.Whole.of R₁ R₂ R₃) (numAt F.t₁ F.t₂ 1))
      (Three.Whole.of R₁ R₂ R₃).ds₂ F.roundsDeclaredByBlocks.2.1 := by
    rw [← e₁, ← e₂]
    exact chain_is _ _ _ 0 (namesGo₁ _ _) w₂
      fun z hz => fits_trees hf z (List.mem_append_right _ (List.mem_append_left _ hz))
  have c₃ : List.Forall₂ (RoundIs (Three.Whole.of R₁ R₂ R₃) (numAt F.t₁ F.t₂ 2))
      (Three.Whole.of R₁ R₂ R₃).ds₃ F.roundsDeclaredByBlocks.2.2 := by
    rw [← e₁, ← e₂]
    exact chain_is _ _ _ _ (namesGo₂ _ _) w₃
      fun z hz => fits_trees hf z (List.mem_append_right _ (List.mem_append_right _ hz))
  have hcnt : countsFit F.tableDepth (Three.Whole.of R₁ R₂ R₃) = true := parts.counts
  unfold countsFit at hcnt
  rw [Bool.and_eq_true] at hcnt
  have k₁ : (WholeD.of F.tableDepth (Three.Whole.of R₁ R₂ R₃)).t₁ = rootsIn R₁ :=
    eq_of_beq hcnt.1
  have k₂ : (WholeD.of F.tableDepth (Three.Whole.of R₁ R₂ R₃)).t₂ = rootsIn R₂ :=
    eq_of_beq hcnt.2
  have hall : allT (WholeD.of F.tableDepth (Three.Whole.of R₁ R₂ R₃)) =
      allTrees (Three.Whole.of R₁ R₂ R₃) := by
    refine allT_of _ _ ?_
    have a1 : ((Three.Whole.of R₁ R₂ R₃).ds₁.dropLast.flatMap (·.trees)).length = rootsIn R₁ := by
      rw [← k₁, ← flat_rdt, flat_len]
      rfl
    have a2 : ((Three.Whole.of R₁ R₂ R₃).ds₁.flatMap (·.trees)).length = rootsIn R₁ := by
      rw [← treesOfChain_shapes (Three.Whole.of R₁ R₂ R₃).opens 0 0, List.length_map]
      exact trees_count _ _ _ _ _ _ _ _ R₁
    rw [a1, a2]
  change (OpensShaped F (WholeD.of F.tableDepth (Three.Whole.of R₁ R₂ R₃))) ∧ _
  unfold OpensShaped
  rw [hall]
  exact ⟨⟨shaped_of_is R₁ R₂ R₃ _ c₁, shaped_of_is R₁ R₂ R₃ _ c₂, shaped_of_is R₁ R₂ R₃ _ c₃⟩,
    k₁.trans e₁, k₂.trans e₂⟩

/-- Where each chain's trees lie among all. -/
theorem chainTrees (D : WholeD) (n : ℕ) (x : Fmt.Shape) :
    ((D.ds₁.flatMap (·.trees))[n]? = some x → (allT D)[n]? = some x) ∧
    ((D.ds₂.flatMap (·.trees))[n]? = some x → (allT D)[D.t₁ + n]? = some x) ∧
    ((D.ds₃.flatMap (·.trees))[n]? = some x → (allT D)[D.t₁ + D.t₂ + n]? = some x) := by
  have l₁ : (D.ds₁.flatMap (·.trees)).length = D.t₁ := flat_len D.ds₁
  have l₂ : (D.ds₂.flatMap (·.trees)).length = D.t₂ := flat_len D.ds₂
  unfold allT
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
    exact h
  · rw [List.getElem?_append_right (by omega), l₁, Nat.add_sub_cancel_left,
      List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
    exact h
  · rw [List.getElem?_append_right (by omega), l₁, List.getElem?_append_right (by omega), l₂,
      show D.t₁ + D.t₂ + n - D.t₁ - D.t₂ = n by omega]
    exact h

/-- The trees of a cut of a chain's data, among the chain's. -/
theorem cutTrees (ds : List RDT) (a b n : ℕ) (x : Fmt.Shape)
    (h : (((ds.drop a).take b).flatMap (·.trees))[n]? = some x) :
    (ds.flatMap (·.trees))[((ds.take a).map (·.trees.length)).sum + n]? = some x := by
  have key : ds.flatMap (·.trees) = (ds.take a).flatMap (·.trees) ++
      (((ds.drop a).take b).flatMap (·.trees) ++ ((ds.drop a).drop b).flatMap (·.trees)) := by
    rw [← List.flatMap_append, ← List.flatMap_append, List.take_append_drop,
      List.take_append_drop]
  rw [key, List.getElem?_append_right (by rw [flat_len]; omega), flat_len,
    Nat.add_sub_cancel_left,
    List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
  exact h

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.roundsOfData
#print axioms VerifiableInference.Desc.treeIs_iff
#print axioms VerifiableInference.Desc.opensShaped
#print axioms VerifiableInference.Desc.chainTrees
#print axioms VerifiableInference.Desc.cutTrees
