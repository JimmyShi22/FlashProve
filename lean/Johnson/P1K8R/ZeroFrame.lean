-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/ZeroFrame.lean: "EVERY VIRTUAL ROW OF EVERY ARRAY OF AN OPEN LEDGER BEGINS AT COLUMN
0" (the field L0 of HRow, OnBytes/Model/Hide.lean) AS A SENTENCE ON THE FIRST CHAIN's STATE, AND THE
FEW STEPS BY WHICH IT PASSES FROM A STATE TO THE NEXT. Definitions and lemmas; none of the library's
goals. No prover stands in them; nothing on completeness, soundness or hiding.

  `l0s X`   the first columns of an array's virtual rows; `AllZero`
      (Johnson/P1K8R/AllZeroAtPlans.lean) reads a ledger through these alone: `l0At_map`
  **`allZero_map`**   two ledgers with the same first columns: `AllZero` passes. Its feeders:
      `allZero_trees` (the same arrays), `l0s_of_frame`, `allZero_frame` (the same treesFrame,
      OnBytes/Model/HideLaws.lean; `frameL0s`, `l0s_frame`), `l0s_of_sums` (the same K9L.sums,
      Johnson/Desc/First/Batch/Law/Measure.lean)
  `l0s_rows_map`, `l0s_rows_modify`   a writing of rows that leaves each row's first column
  `allZero_laid`, `allZero_start`   the ledger from which a sub-proof starts (startFork,
      Johnson/Desc/First/Walk/FirstQuiet.lean), off a plan that has it
  `fold_l0s`, `fill_l0s`, `allZero_fill`   the filling of the weights (t2FillL,
      OnBytes/Model/Trees.lean)
  **`allZero_rests`**   the five closure rules for a property of a ledger (ForkRests,
      Johnson/Desc/First/Link/Law/SizedRides.lean)
  `ZeroInv s`, `KeepsZero s s'`   the sentence on a state: whatever ledger is open has `AllZero`; it
      passes from s to s'. `kz_refl`, `kz_trans`; **`kz_of_cases`**: the ledger behind has it
      outright, or there was a ledger in front with the same first columns; `kz_same`, `kz_none`,
      `zeroInv_none`, `kz_trees`
By: the frame of the library's walk for the arrays' looks
(Johnson/Desc/First/Link/Law/LooksWalk.lean, LooksAre.lean; Johnson/Desc/First/Batch/Law/Look.lean,
FitsAtS.lean), lemma for lemma, with the first columns in the looks' place · hideRun_core,
paid_core, eq_side: the arrays are the same · K9L.core_coefBody
(Johnson/Desc/First/Batch/Law/Coef.lean) for the fifth rule, where the looks' own road
(coefBody_inv) asks a property to pass every writing of a row, which `AllZero` does not ·
Model.map_modify_same.
Limits. NOTHING ON ANY SUB-PROTOCOL AND NOTHING ON ANY REACHED STATE: that the first chain's
sub-protocols step in `KeepsZero` is not shown.

-/
import Johnson.P1K8R.AllZeroAtPlans
import Johnson.Desc.First.Link.Law.LooksWalk
import Johnson.Desc.First.Link.Law.TreesRide
import Johnson.Desc.First.Batch.Law.Coef
import Johnson.Desc.First.Batch.Law.FitsAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (hideRun_core paid_core)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims.Law (eq_side)
open VerifiableInference.Desc.LinkJoin (ForkRests KeepsTrees)
open Johnson.Desc.First.Walk (LinkPub startFork emptySlots weightsAtZero)

/-- The first columns of an array's virtual rows. -/
def l0s (X : HTree) : Array Nat := X.rows.map (·.L0)

/-- A ledger's first columns, read through `l0s`. -/
theorem l0At_map (F : Fork) (t e : Nat) :
    l0At F t e = ((F.trees.map l0s).getD t #[]).getD e 0 := by
  unfold l0At l0s
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases F.trees[t]? with
  | none => simp
  | some X =>
    simp only [Option.map_some, Option.getD_some, Array.getElem?_map]
    cases X.rows[e]? with
    | none => rfl
    | some r => rfl

/-- **The same first columns.** -/
theorem allZero_map {F G : Fork} (h : G.trees.map l0s = F.trees.map l0s) (hF : AllZero F) :
    AllZero G := fun t e => by
  rw [l0At_map, h, ← l0At_map]
  exact hF t e

theorem allZero_trees {F G : Fork} (h : G.trees = F.trees) (hF : AllZero F) : AllZero G :=
  allZero_map (by rw [h]) hF

/-- The first columns, off an array's frame. -/
def frameL0s (x : HTree × Array (HRow × Nat)) : Array Nat := x.2.map (·.1.L0)

theorem l0s_frame (X : HTree) : frameL0s X.frame = l0s X := by
  simp [frameL0s, HTree.frame, HRow.frame, l0s, Array.map_map, Function.comp_def]

/-- Whatever keeps the arrays' frame keeps their first columns. -/
theorem l0s_of_frame (A B : Array HTree) (h : treesFrame A = treesFrame B) :
    A.map l0s = B.map l0s := by
  have e : ∀ tr : Array HTree, tr.map l0s = (treesFrame tr).map frameL0s := by
    intro tr
    unfold treesFrame
    rw [Array.map_map]
    congr 1
    funext X
    exact (l0s_frame X).symm
  rw [e A, e B, h]

theorem allZero_frame {F G : Fork} (h : treesFrame G.trees = treesFrame F.trees)
    (hF : AllZero F) : AllZero G := allZero_map (l0s_of_frame _ _ h) hF

/-- Whatever keeps the ledger's sums keeps the first columns. -/
theorem l0s_of_sums {F G : Fork} (h : K9L.sums G = K9L.sums F) :
    G.trees.map l0s = F.trees.map l0s := by
  have e : ∀ H : Fork, H.trees.map l0s = (K9L.sums H).1.map fun a => a.map (·.2) := by
    intro H
    simp [K9L.sums, l0s, Array.map_map, Function.comp_def]
  rw [e G, e F, h]

theorem l0s_rows_map (X : HTree) (f : HRow → HRow) (hf : ∀ r, (f r).L0 = r.L0) :
    l0s { X with rows := X.rows.map f } = l0s X := by
  show (X.rows.map f).map (·.L0) = X.rows.map (·.L0)
  rw [Array.map_map]
  congr 1
  funext r
  exact hf r

theorem l0s_rows_modify (X : HTree) (i : Nat) (f : HRow → HRow) (hf : ∀ r, (f r).L0 = r.L0) :
    l0s { X with rows := X.rows.modify i f } = l0s X := by
  show (X.rows.modify i f).map (fun r : HRow => r.L0) = X.rows.map fun r : HRow => r.L0
  exact map_modify_same (fun r : HRow => r.L0) f hf X.rows i

/-- The ledger that is laid off a list of arrays. -/
theorem allZero_laid {F : Fork} (ns : Nat) (h : AllZero F) :
    AllZero (emptySlots (weightsAtZero F) ns) := by
  refine allZero_map (F := F) ?_ h
  show (F.trees.map fun X => { X with rows := X.rows.map fun r =>
    { r with L := Array.replicate X.K zeroE } }).map l0s = F.trees.map l0s
  rw [Array.map_map]
  congr 1
  funext X
  exact l0s_rows_map X _ fun _ => rfl

/-- The ledger from which a sub-proof starts. -/
theorem allZero_start (X : LinkPub) (ns : Nat) (h : AllZero X.Fp) : AllZero (startFork X ns) :=
  allZero_laid ns h

theorem fold_l0s : ∀ (l : List Nat) (tr : Array HTree),
    (l.foldl (fun trees ti => trees.modify ti K9L.fillOne) tr).map l0s = tr.map l0s
  | [], _ => rfl
  | ti :: l, tr => by
    rw [List.foldl_cons, fold_l0s l]
    exact map_modify_same l0s K9L.fillOne
      (fun X => l0s_rows_map X _ fun r => by split <;> rfl) tr ti

/-- The filling of the weights keeps the first columns. -/
theorem fill_l0s (F : Fork) (T : Tail2) : (t2FillL F T).trees.map l0s = F.trees.map l0s :=
  fold_l0s _ _

theorem allZero_fill {F : Fork} (T : Tail2) (h : AllZero F) : AllZero (t2FillL F T) :=
  allZero_map (fill_l0s F T) h

/-- **The five closure rules.** -/
theorem allZero_rests : ForkRests AllZero where
  later _ _ hc _ := allZero_trees hc.trees
  hide _ _ _ _ _ h := allZero_trees (hideRun_core h).trees
  paid F i := allZero_trees (paid_core F i).trees
  eq _ _ _ _ _ _ _ he := allZero_trees (eq_side he).trees
  coef tl g F h := allZero_map (l0s_of_sums (congrArg (·.1) (K9L.core_coefBody tl g F))) h

/-- **Whatever ledger is open has it.** -/
def ZeroInv (s : S) : Prop := ∀ G, s.fork? = some G → AllZero G

/-- It passes from s to s'. -/
def KeepsZero (s s' : S) : Prop := ZeroInv s → ZeroInv s'

theorem kz_refl (s : S) : KeepsZero s s := id

theorem kz_trans (a b c : S) (h : KeepsZero a b) (k : KeepsZero b c) : KeepsZero a c :=
  fun x => k (h x)

/-- **The tool**: a maker, or a keeper. -/
theorem kz_of_cases {s s' : S}
    (h : ∀ G', s'.fork? = some G' → AllZero G' ∨
      ∃ G, s.fork? = some G ∧ G'.trees.map l0s = G.trees.map l0s) : KeepsZero s s' := by
  intro hs G' hG
  rcases h G' hG with h1 | ⟨G, e1, e2⟩
  · exact h1
  · exact allZero_map e2 (hs G e1)

/-- The ledger is left. -/
theorem kz_same {s s' : S} (hf : s'.fork? = s.fork?) : KeepsZero s s' :=
  kz_of_cases fun G' hG => Or.inr ⟨G', hf ▸ hG, rfl⟩

/-- No ledger is open behind. -/
theorem kz_none {s s' : S} (hf : s'.fork? = none) : KeepsZero s s' := by
  intro _ G' hG
  rw [hf] at hG
  exact nomatch hG

theorem zeroInv_none {s : S} (h : s.fork? = none) : ZeroInv s := by
  intro G hG
  rw [h] at hG
  exact nomatch hG

/-- The arrays are left, where no ledger is opened. -/
theorem kz_trees {s s' : S} (h : KeepsTrees s s') (ho : s'.fork?.isSome → s.fork?.isSome) :
    KeepsZero s s' := by
  refine kz_of_cases fun G' hG => Or.inr ?_
  obtain ⟨G, e⟩ := Option.isSome_iff_exists.1 (ho (by rw [hG]; rfl))
  obtain ⟨G'', e1, e2⟩ := h G e
  obtain rfl : G'' = G' := Option.some.inj (e1.symm.trans hG)
  exact ⟨G, e, by rw [e2]⟩

end P1K8

#print axioms P1K8.l0At_map
#print axioms P1K8.allZero_map
#print axioms P1K8.allZero_trees
#print axioms P1K8.l0s_frame
#print axioms P1K8.l0s_of_frame
#print axioms P1K8.allZero_frame
#print axioms P1K8.l0s_of_sums
#print axioms P1K8.l0s_rows_map
#print axioms P1K8.l0s_rows_modify
#print axioms P1K8.allZero_laid
#print axioms P1K8.allZero_start
#print axioms P1K8.fold_l0s
#print axioms P1K8.fill_l0s
#print axioms P1K8.allZero_fill
#print axioms P1K8.allZero_rests
#print axioms P1K8.kz_refl
#print axioms P1K8.kz_trans
#print axioms P1K8.kz_of_cases
#print axioms P1K8.kz_same
#print axioms P1K8.kz_none
#print axioms P1K8.zeroInv_none
#print axioms P1K8.kz_trees
