-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/E/KObj/PFile.lean: a written proof file, and its hypotheses place by place and by family.

Definitions, statements and proofs.

Main names:
  `KObj.PFile`: the first proof chain as a head step, a row of blocks each with the step behind it
    (Johnson/E/KObj/RowS.lean) and a tail step; the shared and the second chain as a typed list of
    batch blocks; the other two files as data of which nothing is asked.
  `KObj.PFile.Fields`, `KObj.PFile.proofBlocks`: the hypotheses place by place; they give
    `ObjB.ProofBlocks` (Johnson/E/KObj/ProofFile.lean).
  `KObj.KFam`, `KObj.KFam.Good`: a kind of block (an index type, which indices count, the joints,
    the block); every block of the kind has its property.
  `KObj.BK.Same`, `KObj.BK.IsOf`, `KObj.BK.good_of_isOf`: a block is a value of a kind (equality of
    joints and block); then it has its property if the kind has.
  `KObj.PFile.blocks_by_family`, `KObj.PFile.seams_by_family`: the hypotheses by a labelling of the
    places.
Limits: no proof file is written here. Nothing is said of any kind.
-/
import Johnson.E.KObj.ProofFile
import Johnson.E.KObj.RowS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj
open Iop Prob Hiop IOR Cb

universe u

/-! ### handing on, along app | snoc | fam -/

theorem LK.handsL_one {T U : Type} {A B : JK} (b : BK A B) (ρ : Rd T U A) (θ : Rd T U B) :
    (LK.one b).HandsL ρ θ ↔ b.Hands ρ θ := by rw [LK.HandsL]
theorem LK.handsL_snoc {T U : Type} {A B C : JK} (l : LK A B) (b : BK B C) (ρ : Rd T U A) (θ : Rd T
    U C) :
    (l.snoc b).HandsL ρ θ ↔ ∃ σ, l.HandsL ρ σ ∧ b.Hands σ θ := by rw [LK.HandsL]

theorem LK.handsL_app {T U : Type} {A B C : JK} (l : LK A B) (m : LK B C) (ρ : Rd T U A) (σ : Rd T U
    B) :
    ∀ θ : Rd T U C, l.HandsL ρ σ → m.HandsL σ θ → (l.app m).HandsL ρ θ := by
  induction m with
  | one b =>
    intro θ h1 h2
    rw [LK.app_one, LK.handsL_snoc]
    exact ⟨σ, h1, (LK.handsL_one b σ θ).1 h2⟩
  | snoc m b ih =>
    intro θ h1 h2
    obtain ⟨τ, h3, h4⟩ := (LK.handsL_snoc m b σ θ).1 h2
    rw [LK.app_snoc, LK.handsL_snoc]
    exact ⟨τ, ih τ h1 h3, h4⟩

theorem LK.handsL_fam {T U : Type} (J : ℕ → JK) (b : ∀ i, BK (J i) (J (i + 1))) (ρ : ∀ i, Rd T U (J
    i))
    (n : ℕ) (h : ∀ i ≤ n, (b i).Hands (ρ i) (ρ (i + 1))) : (LK.fam J b n).HandsL (ρ 0) (ρ (n + 1))
        := by
  induction n with
  | zero =>
    rw [LK.fam, LK.handsL_one]
    exact h 0 le_rfl
  | succ n ih =>
    rw [LK.fam, LK.handsL_snoc]
    exact ⟨ρ (n + 1), ih fun i hi => h i (Nat.le_succ_of_le hi), h (n + 1) le_rfl⟩

/-! ### a written proof file -/

structure PFile : Type 1 where
  C      : ConfigurationWithOutOfDomainSample
  on     : C.Left
  N      : ℕ
  dOn    : on.AMsg
  /-- the first proof chain -/
  row    : RowS
  n      : ℕ
  head   : BK (jReq C) (row.In 0)
  tail   : BK (row.In (n + 1)) (jLin C on)
  /-- how the record and the encoded index are read at each joint -/
  rd     : ∀ i, Rd C.Rec C.E0.Str (row.In i)
  /-- the shared and the second proof chain -/
  linOn  : LB (jbLin (N := N) C on) jbEnd
  /-- the other two files: nothing is asked of these -/
  off    : C.Left
  wf     : LK (jWf C) (jLin C off)
  linOff : LK (jLin C off) jEnd
  link   : LK (jLink C) jEnd
  dOff   : off.AMsg

namespace PFile
variable (W : PFile)

/-- the first proof chain's typed list -/
noncomputable def req : LK (jReq W.C) (jLin W.C W.on) := ((LK.one W.head).app (W.row.list W.n)).snoc
    W.tail

@[reducible] noncomputable def objB : ObjB :=
  ⟨W.C, W.off, W.on, W.N, W.wf, W.linOff, W.link, W.req, W.linOn, W.dOff, W.dOn⟩

/-- the named hypotheses, place by place -/
structure Fields : Prop where
  head   : W.head.Good
  headH  : W.head.Hands ⟨Prod.snd, id⟩ (W.rd 0)
  blocks : ∀ i ≤ W.n, (W.row.blk i).Good
  seams  : ∀ i ≤ W.n, W.row.SeamAt i
  hands  : ∀ i ≤ W.n, (W.row.seated i).Hands (W.rd i) (W.rd (i + 1))
  tail   : W.tail.Good
  tailH  : W.tail.Hands (W.rd (W.n + 1)) ⟨Prod.snd, Prod.fst⟩
  linOn  : W.linOn.Each

/-- (W1) -/
theorem proofBlocks (h : W.Fields) : W.objB.ProofBlocks where
  req := (LK.each_snoc _ _ _).2
    ⟨(LK.each_app _ _ _).2 ⟨(LK.each_one _ _).2 h.head, W.row.each W.n h.blocks h.seams⟩, h.tail⟩
  hands := (LK.handsL_snoc _ _ _ _).2 ⟨W.rd (W.n + 1),
    LK.handsL_app _ _ _ (W.rd 0) _ ((LK.handsL_one _ _ _).2 h.headH)
      (LK.handsL_fam W.row.In W.row.seated W.rd W.n h.hands), h.tailH⟩
  linOn := h.linOn

end PFile

/-! ### (W2) by family -/

/-- two blocks are one: joints and block -/
def BK.Same {A B A' B' : JK} (b : BK A B) (b' : BK A' B') : Prop :=
  (⟨A, B, b⟩ : Σ A B : JK, BK A B) = ⟨A', B', b'⟩

theorem BK.good_of_same {A B A' B' : JK} (b : BK A B) (b' : BK A' B') (h : b.Same b') (g : b'.Good)
    :
    b.Good := by
  cases h
  exact g

/-- a kind of block: an index type, which indices count, the joints, the block -/
structure KFam : Type (max 1 (u + 1)) where
  ι   : Type u
  mem : ι → Prop
  src : ι → JK
  dst : ι → JK
  blk : ∀ s, BK (src s) (dst s)

/-- every block of the kind has its property: one named proposition a kind -/
def KFam.Good (κ : KFam.{u}) : Prop := ∀ s, κ.mem s → (κ.blk s).Good

/-- b is a value of the kind -/
def BK.IsOf {A B : JK} (b : BK A B) (κ : KFam.{u}) : Prop := ∃ s, κ.mem s ∧ b.Same (κ.blk s)

theorem BK.good_of_isOf {A B : JK} (b : BK A B) (κ : KFam.{u}) (h : b.IsOf κ) (g : κ.Good) : b.Good
    :=
  h.elim fun s hs => b.good_of_same _ hs.2 (g s hs.1)

/-- the blocks' hypotheses by family -/
theorem PFile.blocks_by_family (W : PFile) {F : Type} (fam : ℕ → F) (K : F → KFam.{u})
    (isOf : ∀ i ≤ W.n, (W.row.blk i).IsOf (K (fam i))) (good : ∀ f, (K f).Good) :
    ∀ i ≤ W.n, (W.row.blk i).Good :=
  fun i hi => (W.row.blk i).good_of_isOf _ (isOf i hi) (good (fam i))

/-- the seams' hypotheses by family -/
theorem PFile.seams_by_family (W : PFile) {G : Type} (sfam : ℕ → G)
    (h : ∀ g : G, ∀ i ≤ W.n, sfam i = g → W.row.SeamAt i) : ∀ i ≤ W.n, W.row.SeamAt i :=
  (by_family sfam W.n _).2 h

#print axioms KObj.PFile.proofBlocks
#print axioms KObj.BK.good_of_isOf
#print axioms KObj.PFile.blocks_by_family

end KObj
