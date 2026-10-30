-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/MergeStage.lean: the merges of claims as stages.

Blocks/MergeBlock.lean proves soundness, completeness and masked form of the two merges' blocks
(exactly: under hypotheses, of `mergeC`, `merge` and `rename`; of `tensorMerge` soundness only).
Here they are combined in stages (Blocks/Stage.lean), each beside its protocol (`Core`), in the
namespace `MG`.
 * `coMergeC`, `stMergeC`: coefficients, then a masked sumcheck of degree 2 with plain weights;
   column claims become one index claim.
 * `coRename`, `stRename`: a masked scalar for the end form; the claim now has the form of this
   scalar, and LIN(old form − scalar) is deferred (this form has the value 0).
 * `coTensorMerge`, `stTensorMerge`: steps (2) to (4) of the merge of tensor claims (coefficients,
   sumcheck, renaming); step (1) sends their masked scalars.
 * `coMerge`, `stMerge`: the merge of index claims. `coPadsMerge`, `stPadsMerge`: the same with its
   pad vector η⁽¹⁾ as one stage.
J indexes the claims and is any finite type, so that one theorem serves the 32 or 33 tensor claims
of a segment, the index claims of all segments, and two claims.
 * The relations between stages: `cutC`, `cutIs`, `cutI`, `cutIL`. Q is the set of indices of pads
   that the implicit part is known to hold; V is any condition on the honest state's matrix.
 * The `props_` theorems: `Stage.Props`, under the hypotheses of Blocks/MergeBlock.lean's theorems;
   besides, for `props_tensorMerge` that p is none of the sumcheck's pads, and for `props_padsMerge`
   three on the relations c₀ before it.
 * Nothing is withheld (`Quiet`; `Hon.withheld`, Blocks/BlockHon.lean): pBad = pWin = 0. Only
   `stPadsMerge` sends a vector.
 * rounds_..: one round for each entry of the list l, and 1 (stMergeC, stMerge), 2 (stPadsMerge)
   more; below_..: every error, as a probability, is at most 2 / |E|, if there is a claim at all.

Notation:
 * `M`: `MG E Y P Rw ι`: the data of a merge; P indexes the pads; l: a list of the sumcheck's
   variables ι (Blocks/MergeBlock.lean).
 * `Stage` P E a b: a `Core` (a block and its honest prover) with ε: `Err B.shape`: the errors,
   round by round, as counts; `S.U`, `S.D`: sets of pads (`Set P`); see the fields' doc comment;
   `Sim`; `pBad`, `pWin`: `ℝ≥0∞` (Blocks/Stage.lean).
 * `Cut` P E a: the relations between two stages: R: the relation for soundness; Hn: the relation of
   the honest run; V: validity of the honest state (Blocks/Stage.lean).
 * `Forms.OK`: a proposition: the constant form 1 has the value 1 (Blocks/RelForm.lean);
   `SC.PlacesOnce`: a proposition: every pad is used for one masked scalar only
   (Blocks/SumCheckBlock.lean).
 * `Q'` C rows mrow role q: a property of a vector's code, number of rows, number of row variables,
   role and number of positions read (`EncData.All`, Blocks/StageSide.lean).
 * end point ψ, end form: of the index claim that `MG.mergeC` puts out (the head of
   Blocks/MergeBlock.lean).
 * LIN(f): the affine form f has the value 0: a deferred claim (`Ledger`, Blocks/Form.lean; the head
   of Blocks/LookupStage.lean).

Limits. Left to the segment: how its statement holds the tensor claims and its honest state the
matrix (a lens, that is a getter and a setter: `Stage.on`); that the deferred form is added to its
linear claims. Not here: step (1), and so the merge of tensor claims as one stage. The completeness
theorems ask 2 ≠ 0 in E (NeZero (2 : E)), as those of Blocks/MergeBlock.lean (`accOn_mergeC`,
`accOn_merge`; not `accOn_rename`). Here all `props_` theorems but `props_rename` ask it.

Terms: lean/GLOSSARY.md.
-/
import Blocks.MergeBlock
import Blocks.SumCheckStage
import Blocks.StageSide
import Blocks.StageNums
import Blocks.StageCount
import Blocks.Allot
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks
namespace MG

open Iop Prob Alg
open scoped ENNReal

/-! ## 0. Honest provers that withhold nothing; masked form for fewer states -/

section Kit

variable {P E : Type}

/-- The honest prover withholds nothing: the public part and the rest of its withheld set are
empty. -/
structure Quiet {Xi Yi Xo Yo Ii Io : Type} {B : Block Xi Yi Xo Yo} (H : Hon B P E Ii Io) :
    Prop where
  bad : H.Bad = ∅
  win : ∀ s, H.Win s = ∅

theorem Quiet.seq {X₁ Y₁ X₂ Y₂ X₃ Y₃ I₁ I₂ I₃ : Type} {B₁ : Block X₁ Y₁ X₂ Y₂}
    {B₂ : Block X₂ Y₂ X₃ Y₃} {H₁ : Hon B₁ P E I₁ I₂} {H₂ : Hon B₂ P E I₂ I₃}
    (h₁ : Quiet H₁) (h₂ : Quiet H₂) : Quiet (H₁.seq H₂) where
  bad := Set.eq_empty_of_forall_notMem fun ρ hρ => by
    rcases hρ with h | h
    · have h' : Rho.fst ρ ∈ H₁.Bad := h
      rw [h₁.bad] at h'
      exact h'
    · have h' : Rho.snd (s := B₁.shape) ρ ∈ H₂.Bad := h
      rw [h₂.bad] at h'
      exact h'
  win := fun s => Set.eq_empty_of_forall_notMem fun ρ hρ => by
    rcases hρ with h | h
    · have h' : Rho.fst ρ ∈ H₁.Win s := h
      rw [h₁.win] at h'
      exact h'
    · have h' : Rho.snd (s := B₁.shape) ρ ∈ H₂.Win (H₁.next s (Rho.fst ρ)) := h
      rw [h₂.win] at h'
      exact h'

theorem quiet_pure {Xi Yi Xo Yo Ii Io : Type} (f : Xi → Option Xo) (g : Yi → Yo) (nx : Ii → Io) :
    Quiet (Hon.pure (P := P) (E := E) f g nx) :=
  ⟨rfl, fun _ => rfl⟩

/-- Masked form for all states is masked form for the valid ones. -/
theorem masked_of_true [Fintype P] [DecidableEq P] [AddCommGroup E] [Fintype E]
    {Xi Yi Xo Yo Ii Io : Type} {B : Block Xi Yi Xo Yo} {H : Hon B P E Ii Io}
    {U D : Set P} {Sim : Rho B.shape → PMF (Plains B.shape)}
    (h : H.Masked (fun _ => True) U D Sim) (V : Ii → Prop) : H.Masked V U D Sim :=
  ⟨fun s ρ π π' _ => h.reads s ρ π π' trivial, fun s ρ σ _ => h.law s ρ σ trivial⟩

end Kit

variable {E Y P Rw ι : Type} [Field E] [Fintype E] [DecidableEq E] [Fintype Rw] [Fintype ι]
  [DecidableEq ι] (M : MG E Y P Rw ι) (J : Type) [Fintype J] [DecidableEq J]

/-! ## 1. The relations -/

/-- All column claims hold. -/
def cutC (Q : Set P) (V : Mat E Rw ι → Prop) : Cut P E ⟨J → M.CClaim, Y, St0 E Rw ι J⟩ where
  R := fun x y => ∀ j, (x j).Holds y
  Hn := M.HiC J Q
  V := fun s => V s.2

/-- All index claims hold. -/
def cutIs (Q : Set P) (V : Mat E Rw ι → Prop) : Cut P E ⟨J → M.Idx, Y, StI E Rw ι J⟩ where
  R := fun x y => ∀ j, (x j).Holds y
  Hn := M.HiI J Q
  V := fun s => V s.2

/-- The one index claim holds. -/
def cutI (Q : Set P) (V : Mat E Rw ι → Prop) : Cut P E ⟨M.Idx, Y, St2 E Rw ι⟩ where
  R := fun a y => a.Holds y
  Hn := M.HoI Q
  V := fun s => V s.2

/-- The index claim holds, and the deferred form has the value 0. -/
def cutIL (Q : Set P) (V : Mat E Rw ι → Prop) : Cut P E ⟨M.Idx × M.forms.Fm, Y, St2 E Rw ι⟩ where
  R := fun o y => o.1.Holds y ∧ M.forms.val y o.2 = 0
  Hn := fun b π o y => M.HoI Q b π o.1 y ∧ M.forms.val y o.2 = 0
  V := fun s => V s.2

/-! ## 2. The protocols -/

/-- The merge of column claims: coefficients, then the sumcheck. -/
def coMergeC (l : List ι) :
    Core P E ⟨J → M.CClaim, Y, St0 E Rw ι J⟩ ⟨M.Idx, Y, St2 E Rw ι⟩ :=
  ⟨M.mergeC J l, M.honMergeC J l⟩

/-- Renaming: one masked scalar. -/
def coRename (p : P) :
    Core P E ⟨M.Idx, Y, St2 E Rw ι⟩ ⟨M.Idx × M.forms.Fm, Y, St2 E Rw ι⟩ :=
  ⟨M.rename p, M.honRename p⟩

/-- The merge of index claims. -/
def coMerge (l : List ι) :
    Core P E ⟨J → M.Idx, Y, StI E Rw ι J⟩ ⟨M.Idx, Y, St2 E Rw ι⟩ :=
  ⟨M.merge J l, M.honMerge J l⟩

theorem quiet_mergeC (l : List ι) : Quiet (M.honMergeC J l) :=
  Quiet.seq ⟨Set.eq_empty_of_forall_notMem fun _ h => (by cases h), fun _ => rfl⟩
    (Quiet.seq (quiet_pure _ _ _)
      (Quiet.seq ⟨(M.prover J).bad_sc (fun _ => rfl) l [], (M.prover J).win_sc l []⟩
        (quiet_pure _ _ _)))

theorem quiet_rename (p : P) : Quiet (M.honRename p) := ⟨rfl, fun _ => rfl⟩

theorem quiet_merge (l : List ι) : Quiet (M.honMerge J l) :=
  (quiet_pure _ _ _).seq (M.quiet_mergeC J l)

/-- The matrix in the honest state does not change. -/
theorem next_mergeC (l : List ι) (s : St0 E Rw ι J) (ρ : Rho (M.mergeC J l).shape) :
    ((M.honMergeC J l).next s ρ).2 = s.2 := by
  show (((M.prover J).sc l []).next _ _).1.2.1 = s.2
  rw [SC.Prover.next_fst]

theorem next_merge (l : List ι) (s : StI E Rw ι J) (ρ : Rho (M.merge J l).shape) :
    ((M.honMerge J l).next s ρ).2 = s.2 :=
  M.next_mergeC J l _ _

/-! ## 3. The stages -/

variable [Fintype P] [DecidableEq P]

/-- The merge of column claims into one index claim, as a stage. -/
def stMergeC (l : List ι) :
    Stage P E ⟨J → M.CClaim, Y, St0 E Rw ι J⟩ ⟨M.Idx, Y, St2 E Rw ι⟩ where
  toCore := M.coMergeC J l
  ε := M.mergeErr J l
  U := (M.sc J).padsOf l
  D := (M.sc J).padsOf l
  Sim := M.simMergeC J l
  pBad := 0
  pWin := 0

/-- Renaming, as a stage. -/
def stRename (p : P) :
    Stage P E ⟨M.Idx, Y, St2 E Rw ι⟩ ⟨M.Idx × M.forms.Fm, Y, St2 E Rw ι⟩ where
  toCore := M.coRename p
  ε := (0, ())
  U := {p}
  D := {p}
  Sim := Hon.simOne (r := sRound E) (K := Unit) E id
  pBad := 0
  pWin := 0

/-- The merge of index claims, as a stage. -/
def stMerge (l : List ι) :
    Stage P E ⟨J → M.Idx, Y, StI E Rw ι J⟩ ⟨M.Idx, Y, St2 E Rw ι⟩ where
  toCore := M.coMerge J l
  ε := Err.app (s := (M.asC J).shape) () (M.mergeErr J l)
  U := (M.sc J).padsOf l
  D := (M.sc J).padsOf l
  Sim := Hon.simSeq (s := (M.asC J).shape) (fun _ => PMF.pure ()) (M.simMergeC J l)
  pBad := 0
  pWin := 0

variable {J}

theorem props_rename (h : M.forms.OK) {p : P} {Q : Set P} (hpQ : p ∈ Q) (V : Mat E Rw ι → Prop) :
    (M.stRename p).Props (M.cutI Q V) (M.cutIL Q V) :=
  Stage.Props.of_empty (S := M.stRename p) (M.clean_rename p)
    (M.accOn_rename h hpQ) (masked_of_true (M.masked_rename p) _)
    (fun _ _ hs => hs) (M.quiet_rename p).bad (M.quiet_rename p).win

variable (J)

variable [NeZero (2 : E)]

/-- `Stage.Props` of `stMergeC`, under the hypotheses below and 2 ≠ 0 in E (`NeZero (2 : E)`). -/
theorem props_mergeC (h : M.forms.OK) {l : List ι} (hl : l.Nodup) (hall : ∀ v, v ∈ l)
    (hp : (M.sc J).PlacesOnce) {Q : Set P} (hQ : (M.sc J).padsOf l ⊆ Q) (V : Mat E Rw ι → Prop) :
    (M.stMergeC J l).Props (M.cutC J Q V) (M.cutI Q V) :=
  Stage.Props.of_empty (S := M.stMergeC J l) (M.clean_mergeC J h hl hall)
    (M.accOn_mergeC J h hl hall hQ) (masked_of_true (M.masked_mergeC J hp hl) _)
    (fun s ρ hs => by
      show V ((M.honMergeC J l).next s ρ).2
      rw [M.next_mergeC]
      exact hs)
    (M.quiet_mergeC J l).bad (M.quiet_mergeC J l).win

/-- `Stage.Props` of `stMerge`, under the hypotheses below and 2 ≠ 0 in E (`NeZero (2 : E)`). -/
theorem props_merge (h : M.forms.OK) {l : List ι} (hl : l.Nodup) (hall : ∀ v, v ∈ l)
    (hp : (M.sc J).PlacesOnce) {Q : Set P} (hQ : (M.sc J).padsOf l ⊆ Q) (V : Mat E Rw ι → Prop) :
    (M.stMerge J l).Props (M.cutIs J Q V) (M.cutI Q V) :=
  Stage.Props.of_empty (S := M.stMerge J l) (M.clean_merge J h hl hall)
    (M.accOn_merge J h hl hall hQ) (masked_of_true (M.masked_merge J hp hl) _)
    (fun s ρ hs => by
      show V ((M.honMerge J l).next s ρ).2
      rw [M.next_merge]
      exact hs)
    (M.quiet_merge J l).bad (M.quiet_merge J l).win

/-! ## 4. The merge of the tensor claims of a segment -/

omit [Fintype P] [DecidableEq P] [NeZero (2 : E)] in
theorem imp_mergeC (l : List ι) (y : Y) (τ : Tr (M.mergeC J l).shape) :
    (M.mergeC J l).imp y τ = y := by
  show ((M.sc J).sc l).imp y _ = y
  rw [SC.imp_sc]

omit [Fintype P] [DecidableEq P] [NeZero (2 : E)] in
theorem imp_tensorMerge (l : List ι) (p : P) (y : Y) (τ : Tr (M.tensorMerge J l p).shape) :
    (M.tensorMerge J l p).imp y τ = y :=
  M.imp_mergeC J l y _

omit [Fintype P] [DecidableEq P] [NeZero (2 : E)] in
/-- Steps (2) to (4): coefficients, sumcheck, renaming. -/
def coTensorMerge (l : List ι) (p : P) :
    Core P E ⟨J → M.CClaim, Y, St0 E Rw ι J⟩ ⟨M.Idx × M.forms.Fm, Y, St2 E Rw ι⟩ :=
  (M.coMergeC J l).seq (M.coRename p)

omit [NeZero (2 : E)] in
/-- Steps (2) to (4), as a stage. -/
def stTensorMerge (l : List ι) (p : P) :
    Stage P E ⟨J → M.CClaim, Y, St0 E Rw ι J⟩ ⟨M.Idx × M.forms.Fm, Y, St2 E Rw ι⟩ :=
  (M.stMergeC J l).seq (M.stRename p)

omit [NeZero (2 : E)] in
theorem toCore_tensorMerge (l : List ι) (p : P) :
    (M.stTensorMerge J l p).toCore = M.coTensorMerge J l p := rfl

theorem props_tensorMerge (h : M.forms.OK) {l : List ι} (hl : l.Nodup) (hall : ∀ v, v ∈ l)
    (hp : (M.sc J).PlacesOnce) {p : P} (hpl : p ∉ (M.sc J).padsOf l) {Q : Set P}
    (hQ : (M.sc J).padsOf l ⊆ Q) (hpQ : p ∈ Q) (V : Mat E Rw ι → Prop) :
    (M.stTensorMerge J l p).Props (M.cutC J Q V) (M.cutIL Q V) :=
  (M.props_mergeC J h hl hall hp hQ V).seq (M.props_rename h hpQ V)
    (Set.disjoint_singleton_right.2 hpl) (Set.disjoint_singleton_right.2 hpl)






/-! ## 5. The encoding data of the rounds: no vector -/

section Tracks

variable {F : Type} [Field F] [Algebra F E]

omit [Fintype P] [DecidableEq P] [NeZero (2 : E)] in
/-- The rounds of the merge of column claims have no vectors. -/
def encMergeC (F : Type) [Field F] [Algebra F E] (l : List ι) :
    EncData F E (M.mergeC J l).shape :=
  EncData.app (s := (Block.sample (J → M.CClaim) Y E (J → E) fun _ => true).shape)
    (REnc.none E F Empty (J → E), PUnit.unit)
    (EncData.app (s := (M.start J).shape) PUnit.unit
      (EncData.app (s := ((M.sc J).sc l).shape) (t := (M.finish J).shape)
        (SC.encSc (M.sc J) F l) PUnit.unit))

omit [NeZero (2 : E)] in
theorem all_encMergeC {Q : Code.Enc F → ℕ → ℕ → Role → ℕ → Prop} (l : List ι) :
    EncData.All Q _ (M.encMergeC J F l) :=
  EncData.All.app (s := (Block.sample (J → M.CClaim) Y E (J → E) fun _ => true).shape)
    (d := (REnc.none E F Empty (J → E), PUnit.unit)) ⟨fun e => e.elim, trivial⟩
    (EncData.All.app (s := (M.start J).shape) (d := PUnit.unit) trivial
      (EncData.All.app (s := ((M.sc J).sc l).shape) (t := (M.finish J).shape) (d' := PUnit.unit)
        (SC.all_encSc (M.sc J) l) trivial))

omit [NeZero (2 : E)] in
theorem sum_encMergeC (f : Code.Enc F → ℕ → ℕ → Role → ℕ → ℕ) (l : List ι) :
    EncData.sum f _ (M.encMergeC J F l) = 0 := by
  unfold encMergeC
  rw [EncData.sum_app, EncData.sum_app, EncData.sum_app, SC.sum_encSc]
  rfl

omit [Fintype P] [DecidableEq P] [NeZero (2 : E)] in
/-- Each stage of this section exposes its input's entries (`Reads`, Blocks/StageTrack.lean). -/
def trackMergeC (l : List ι) (ra : Reads F E ⟨J → M.CClaim, Y, St0 E Rw ι J⟩) :
    (M.coMergeC J l).Track ra (Stage.readsX M.Idx (St2 E Rw ι) ra) where
  d := M.encMergeC J F l
  src := fun n => .inl n

omit [Fintype P] [DecidableEq P] [NeZero (2 : E)] in
theorem trackMergeC_ok (l : List ι) (ra : Reads F E ⟨J → M.CClaim, Y, St0 E Rw ι J⟩) :
    (M.trackMergeC J l ra).OK :=
  ⟨fun y τ n => by
      show ra.rd ((M.mergeC J l).imp y τ) n = ra.rd y n
      rw [M.imp_mergeC],
    fun y τ => by
      show ra.mat ((M.mergeC J l).imp y τ) = ra.mat y
      rw [M.imp_mergeC]⟩

omit [Fintype P] [DecidableEq P] [NeZero (2 : E)] [Fintype J] [DecidableEq J] in
def trackRename (p : P) (ra : Reads F E ⟨M.Idx, Y, St2 E Rw ι⟩) :
    (M.coRename p).Track ra (Stage.readsX (M.Idx × M.forms.Fm) (St2 E Rw ι) ra) where
  d := (REnc.none E F Unit Unit, PUnit.unit)
  src := fun n => .inl n

omit [Fintype P] [DecidableEq P] [NeZero (2 : E)] [Fintype J] [DecidableEq J] in
theorem trackRename_ok (p : P) (ra : Reads F E ⟨M.Idx, Y, St2 E Rw ι⟩) : (M.trackRename p ra).OK :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩


omit [Fintype P] [DecidableEq P] [NeZero (2 : E)] in
def trackMerge (l : List ι) (ra : Reads F E ⟨J → M.Idx, Y, StI E Rw ι J⟩) :
    (M.coMerge J l).Track ra (Stage.readsX M.Idx (St2 E Rw ι) ra) where
  d := EncData.app (s := (M.asC J).shape) PUnit.unit (M.encMergeC J F l)
  src := fun n => .inl n

omit [Fintype P] [DecidableEq P] [NeZero (2 : E)] in
theorem trackMerge_ok (l : List ι) (ra : Reads F E ⟨J → M.Idx, Y, StI E Rw ι J⟩) :
    (M.trackMerge J l ra).OK :=
  ⟨fun y τ n => by
      show ra.rd ((M.mergeC J l).imp y _) n = ra.rd y n
      rw [M.imp_mergeC],
    fun y τ => by
      show ra.mat ((M.mergeC J l).imp y _) = ra.mat y
      rw [M.imp_mergeC]⟩


variable {Q' : Code.Enc F → ℕ → ℕ → Role → ℕ → Prop} (f : Code.Enc F → ℕ → ℕ → Role → ℕ → ℕ)

omit [NeZero (2 : E)] in
/-- No vector is sent, so every condition on the vectors that are sent holds, and every sum over
them is 0. -/
theorem all_trackMergeC (l : List ι) (ra : Reads F E ⟨J → M.CClaim, Y, St0 E Rw ι J⟩) :
    (M.trackMergeC J l ra).All Q' :=
  M.all_encMergeC J l

omit [NeZero (2 : E)] in
theorem sum_trackMergeC (l : List ι) (ra : Reads F E ⟨J → M.CClaim, Y, St0 E Rw ι J⟩) :
    (M.trackMergeC J l ra).sum f = 0 :=
  M.sum_encMergeC J f l

omit [NeZero (2 : E)] in
theorem all_trackMerge (l : List ι) (ra : Reads F E ⟨J → M.Idx, Y, StI E Rw ι J⟩) :
    (M.trackMerge J l ra).All Q' :=
  EncData.All.app (s := (M.asC J).shape) (d := PUnit.unit) trivial (M.all_encMergeC J l)

omit [NeZero (2 : E)] in
theorem sum_trackMerge (l : List ι) (ra : Reads F E ⟨J → M.Idx, Y, StI E Rw ι J⟩) :
    (M.trackMerge J l ra).sum f = 0 := by
  show EncData.sum f _ (EncData.app (s := (M.asC J).shape) PUnit.unit (M.encMergeC J F l)) = 0
  rw [EncData.sum_app, M.sum_encMergeC]
  rfl


end Tracks

/-! ## 6. Counts -/

omit [NeZero (2 : E)] in
/-- One round for the coefficients and one for each variable. -/
theorem rounds_mergeC (l : List ι) : (M.stMergeC J l).rounds = l.length + 1 := by
  show ((Block.sample (J → M.CClaim) Y E (J → E) fun _ => true).shape ++
      ((M.start J).shape ++ (((M.sc J).sc l).shape ++ (M.finish J).shape))).length = _
  rw [List.length_append, List.length_append, List.length_append, SC.length_shape_sc]
  show 1 + (0 + (l.length + 0)) = _
  omega

omit [NeZero (2 : E)] in
theorem rounds_merge (l : List ι) : (M.stMerge J l).rounds = l.length + 1 := M.rounds_mergeC J l


omit [DecidableEq E] [NeZero (2 : E)] in
/-- |E|^(n − 1) of the |E|^n tuples of coefficients (n = |J| ≥ 1) are, as a fraction, at most κ, if
1 / |E| ≤ κ (h). -/
theorem coeff_le [Nonempty J] {κ : ℝ≥0∞} (h : (1 : ℝ≥0∞) / Fintype.card E ≤ κ) :
    ((Fintype.card E ^ (Fintype.card J - 1) : ℕ) : ℝ≥0∞) ≤ κ * Fintype.card (J → E) := by
  have hq0 : (Fintype.card E : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hqt : (Fintype.card E : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hJ : 0 < Fintype.card J := Fintype.card_pos
  rw [Fintype.card_fun]
  have h1 : Fintype.card E ^ Fintype.card J =
      Fintype.card E ^ (Fintype.card J - 1) * Fintype.card E := by
    rw [← pow_succ, Nat.sub_add_cancel hJ]
  rw [h1]
  push_cast
  calc
    (Fintype.card E : ℝ≥0∞) ^ (Fintype.card J - 1) =
        ((1 : ℝ≥0∞) / Fintype.card E) *
          ((Fintype.card E : ℝ≥0∞) ^ (Fintype.card J - 1) * Fintype.card E) := by
        rw [mul_comm ((Fintype.card E : ℝ≥0∞) ^ (Fintype.card J - 1)), ← mul_assoc,
          ENNReal.div_mul_cancel hq0 hqt, one_mul]
    _ ≤ κ * ((Fintype.card E : ℝ≥0∞) ^ (Fintype.card J - 1) * Fintype.card E) := by gcongr

omit [NeZero (2 : E)] in
/-- The errors of `stMergeC`, as probabilities (1 / |E| at the coefficients, 2 / |E| in each round),
are at most κ, under `h2` and for non-empty J. -/
theorem below_mergeC [Nonempty J] {κ : ℝ≥0∞} (h2 : (2 : ℝ≥0∞) / Fintype.card E ≤ κ) (l : List ι) :
    (M.stMergeC J l).Below κ := by
  have hq0 : (Fintype.card E : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hqt : (Fintype.card E : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have h1 : (1 : ℝ≥0∞) / Fintype.card E ≤ κ :=
    le_trans (ENNReal.div_le_div_right (by norm_num) _) h2
  have h2' : ∀ i : ι, (((M.sc J).e i + 1 : ℕ) : ℝ≥0∞) ≤ κ * Fintype.card E := fun _ => by
    show (((1 + 1 : ℕ) : ℕ) : ℝ≥0∞) ≤ _
    have := (ENNReal.div_le_iff hq0 hqt).1 h2
    exact_mod_cast this
  exact Err.Below.app (s := (Block.sample (J → M.CClaim) Y E (J → E) fun _ => true).shape)
    (ε := (Fintype.card E ^ (Fintype.card J - 1), ())) ⟨coeff_le J h1, trivial⟩
    (Err.Below.app (s := (M.start J).shape) (ε := ()) trivial
      (Err.Below.app (s := ((M.sc J).sc l).shape) (t := (M.finish J).shape) (ε' := ())
        (SC.below_scErr (M.sc J) h2' l) trivial))

omit [NeZero (2 : E)] in
theorem below_merge [Nonempty J] {κ : ℝ≥0∞} (h2 : (2 : ℝ≥0∞) / Fintype.card E ≤ κ) (l : List ι) :
    (M.stMerge J l).Below κ :=
  Err.Below.app (s := (M.asC J).shape) (ε := ()) trivial (M.below_mergeC J h2 l)

omit [NeZero (2 : E)] [Fintype J] [DecidableEq J] in
theorem below_rename (κ : ℝ≥0∞) (p : P) : (M.stRename p).Below κ := ⟨by simp, trivial⟩


/-! ## 7. `merge` with its pad vector -/

end MG

namespace MG

open Iop Prob Alg
open scoped ENNReal

section Pads

variable {E Y₀ P Rw ι : Type} [Field E] [Fintype E] [DecidableEq E] [Fintype Rw]
  [Fintype ι] [DecidableEq ι] {n : ℕ} (M : MG E (Y₀ × (Fin n → E)) P Rw ι) (J : Type)
  [Fintype J] [DecidableEq J]

/-- `merge` with its pad vector: the prover first sends the pad vector η⁽¹⁾, which is added to the
implicit part. -/
def coPadsMerge (pl : Fin n → P) (l : List ι) :
    Core P E ⟨J → M.Idx, Y₀, StI E Rw ι J⟩ ⟨M.Idx, Y₀ × (Fin n → E), St2 E Rw ι⟩ :=
  (Core.pads (E := E) ⟨J → M.Idx, Y₀, StI E Rw ι J⟩ pl).seq (M.coMerge J l)

variable [Fintype P] [DecidableEq P]

@[inherit_doc coPadsMerge]
def stPadsMerge (pl : Fin n → P) (l : List ι) :
    Stage P E ⟨J → M.Idx, Y₀, StI E Rw ι J⟩ ⟨M.Idx, Y₀ × (Fin n → E), St2 E Rw ι⟩ :=
  (Stage.pads (E := E) ⟨J → M.Idx, Y₀, StI E Rw ι J⟩ pl).seq (M.stMerge J l)

theorem toCore_padsMerge (pl : Fin n → P) (l : List ι) :
    (M.stPadsMerge J pl l).toCore = M.coPadsMerge J pl l := rfl

theorem U_padsMerge (pl : Fin n → P) (l : List ι) : (M.stPadsMerge J pl l).U = (M.sc J).padsOf l :=
  Set.empty_union _

theorem D_padsMerge (pl : Fin n → P) (l : List ι) : (M.stPadsMerge J pl l).D = (M.sc J).padsOf l :=
  Set.empty_union _

/-- All properties of `stPadsMerge`, from relations c₀ on the implicit part before the pad vector.
Among the hypotheses:
 * hR: if all index claims hold with some pad vector η, the relation for soundness of c₀ holds;
 * hH: in the honest run, with the pad vector as the honest prover sends it, the claims match the
   honest state and are true. -/
theorem props_padsMerge [NeZero (2 : E)] (h : M.forms.OK) {l : List ι} (hl : l.Nodup)
    (hall : ∀ v, v ∈ l) (hp : (M.sc J).PlacesOnce) (pl : Fin n → P) {Q : Set P}
    (hQ : (M.sc J).padsOf l ⊆ Q) (V : Mat E Rw ι → Prop)
    (c₀ : Cut P E ⟨J → M.Idx, Y₀, StI E Rw ι J⟩)
    (hR : ∀ x y₀ η, (∀ j, (x j).Holds (y₀, η)) → c₀.R x y₀)
    (hH : ∀ a π x y₀ η, c₀.Hn a π x y₀ → (∀ j, η j = π (pl j)) → M.HiI J Q a π x (y₀, η))
    (hV : ∀ s, c₀.V s → V s.2) :
    (M.stPadsMerge J pl l).Props c₀ (M.cutI Q V) :=
  (Stage.props_pads pl c₀).seq
    ((M.props_merge J h hl hall hp hQ V).conseq (ca' := Stage.cutPads pl c₀) (cb' := M.cutI Q V)
      (fun x y hx => hR x y.1 y.2 hx) (fun _ _ hx => hx)
      (fun a π x y hx => hH a π x y.1 y.2 hx.1 hx.2) (fun _ _ _ _ hx => hx) hV fun _ hs => hs)
    (Set.empty_disjoint _) (Set.empty_disjoint _)

theorem rounds_padsMerge (pl : Fin n → P) (l : List ι) :
    (M.stPadsMerge J pl l).rounds = l.length + 2 := by
  rw [stPadsMerge, Stage.rounds_seq, M.rounds_merge]
  show 1 + (l.length + 1) = _
  omega

theorem below_padsMerge [Nonempty J] {κ : ℝ≥0∞} (h2 : (2 : ℝ≥0∞) / Fintype.card E ≤ κ)
    (pl : Fin n → P) (l : List ι) :
    (M.stPadsMerge J pl l).Below κ :=
  Stage.Below.seq (S₁ := Stage.pads (E := E) ⟨J → M.Idx, Y₀, StI E Rw ι J⟩ pl)
    ⟨by simp, trivial⟩ (M.below_merge J h2 l)

theorem pBad_padsMerge (pl : Fin n → P) (l : List ι) : (M.stPadsMerge J pl l).pBad = 0 := add_zero _

theorem pWin_padsMerge (pl : Fin n → P) (l : List ι) : (M.stPadsMerge J pl l).pWin = 0 := add_zero _

end Pads

section PadsTrack

variable {F E Y₀ P Rw ι : Type} [Field F] [Field E] [Fintype E] [DecidableEq E] [Algebra F E]
  [Fintype Rw] [Fintype ι] [DecidableEq ι] (C : Code.Enc F) [Nonempty (Fin C.n)]
  (M : MG E (Y₀ × (Fin C.msg → E)) P Rw ι) (J : Type) [Fintype J] [DecidableEq J]

/-- The pad vector is sent under the code C and read at q positions; its entries are exposed
(`Reads`, Blocks/StageTrack.lean). -/
def trackPadsMerge
    (q : ℕ) (pl : Fin C.msg → P) (l : List ι) (ra : Reads F E ⟨J → M.Idx, Y₀, StI E Rw ι J⟩) :
    (M.coPadsMerge J pl l).Track ra (Stage.readsX M.Idx (St2 E Rw ι) (Stage.readsPads C.msg ra)) :=
  (Core.trackPads C q pl ra).seq (M.trackMerge J l (Stage.readsPads C.msg ra))

variable [Fintype P] [DecidableEq P]

theorem trackPadsMerge_ok (q : ℕ) (pl : Fin C.msg → P) (l : List ι)
    (ra : Reads F E ⟨J → M.Idx, Y₀, StI E Rw ι J⟩) :
    (M.trackPadsMerge C J q pl l ra).OK :=
  (Stage.trackPads_ok C q pl ra).seq (M.trackMerge_ok J l _)

/-- One vector is sent: the pad vector; so every vector sent has Q', under `h` (Q' of the pad
vector) and for C.n > 0. -/
theorem all_trackPadsMerge {Q' : Code.Enc F → ℕ → ℕ → Role → ℕ → Prop} (q : ℕ) (pl : Fin C.msg → P)
    (l : List ι) (ra : Reads F E ⟨J → M.Idx, Y₀, StI E Rw ι J⟩) (h : Q' C 1 0 Role.pad q) :
    (M.trackPadsMerge C J q pl l ra).All Q' :=
  Core.Track.All.seq (t₁ := Core.trackPads C q pl ra) ⟨fun _ => h, trivial⟩ (M.all_trackMerge J l _)

theorem sum_trackPadsMerge (f : Code.Enc F → ℕ → ℕ → Role → ℕ → ℕ) (q : ℕ) (pl : Fin C.msg → P)
    (l : List ι) (ra : Reads F E ⟨J → M.Idx, Y₀, StI E Rw ι J⟩) :
    (M.trackPadsMerge C J q pl l ra).sum f = f C 1 0 Role.pad q := by
  refine (Core.Track.sum_seq
    f (Core.trackPads C q pl ra) (M.trackMerge J l (Stage.readsPads C.msg ra))).trans ?_
  rw [M.sum_trackMerge, Nat.add_zero]
  show (∑ _v : Unit, f C 1 0 Role.pad q) + 0 = _
  simp

end PadsTrack

end MG
end Blocks
