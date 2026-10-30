-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/E/KObj/RowS.lean: a row of blocks in which each block is followed by a step without rounds.

Definitions, statements and proofs. In a typed list two blocks stand in a row only if the joint
between them is one term. Here a block ends at a joint `Out i` of its own, of any types, and the
seam behind it is a step without rounds inside the place.

Main names:
  `KObj.StepD`, `KObj.StepD.OK`: the data of a step (a map of the explicit part, a map of the
    oracles, a map of witnesses backwards) and what a seam owes: the map of oracles is local; the
    condition is carried; `back` turns a witness behind the step into one before it.
  `KObj.BK.post`, `KObj.BK.good_post`, `KObj.BK.hands_post`: a block, then a step (`IOR.post`,
    Ior/Frame.lean): the same shape and the same errors; the block's property is kept under
    `StepD.OK`.
  `KObj.RowS`, `KObj.RowS.SeamAt`, `KObj.RowS.seated`, `KObj.RowS.list`: the row, its seams, its
    typed list.
  `KObj.RowS.seated_shape`: a place has the rounds of its block and no more.
  `KObj.RowS.good`: if every block has its property and every seam holds, the whole row is one
    block with its property.
Limits: a step's first map may refuse: then the place's verifier refuses. Two of the three clauses
of `StepD.OK` speak only of statements at which that map answers: a step that refuses every
statement meets them emptily, and a row with such a step is sound as a verifier that rejects
everything is. That a row's verifier accepts where the programs' verifier does is not a matter of
this file. Nothing is said of any value.
-/
import Johnson.E.KObj.Arrows
import Ior.FrameProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj
open Iop Prob IOR

/-- a step without rounds from B to C: the data -/
structure StepD (B C : JK) where
  f    : B.X → Option C.X
  g    : ExtMap B.E C.E
  back : B.X × B.E.Str → C.W → B.W

/-- what a seam owes -/
structure StepD.OK {B C : JK} (s : StepD B C) : Prop where
  isLocal : s.g.IsLocal
  onOut   : ∀ b x', B.on b → s.f b.1 = some x' → C.on (x', s.g.map b.2)
  know    : ∀ b x' w, B.on b → s.f b.1 = some x' → C.relR (x', s.g.map b.2) w → B.relR b (s.back b
      w)

/-- (R1) a block, then a step: the same shape, the same errors; d: the extractor's value where the
block's verifier rejects -/
noncomputable def BK.post {A B C : JK} (b : BK A B) (s : StepD B C) (d : A.W) : BK A C where
  R := b.R.post s.f s.g
  ext := fun a τ w => match b.R.red.out a τ with
    | some x => b.ext a τ (s.back x w)
    | none => d
  err := b.err

theorem BK.good_post {A B C : JK} (b : BK A B) (s : StepD B C) (d : A.W) (h : b.Good) (hs : s.OK) :
    (b.post s d).Good where
  point := h.point
  isLocal := h.isLocal.post s.f s.g hs.isLocal
  know := by
    intro a ha
    refine Doomed.mono _ _ ?_ (h.know a ha)
    intro τ hτ c w hc hw
    -- the block's own output
    have hc' : ((b.R.out a.1 a.2 τ).bind s.f).map (fun xo => (xo, s.g.map (b.R.imp a.2 τ))) = some c
        := hc
    obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.1 hc'
    obtain ⟨x, hx, hf⟩ := Option.bind_eq_some_iff.1 hx'
    have hb : b.R.red.out a τ = some (x, b.R.imp a.2 τ) := by
      show (b.R.out a.1 a.2 τ).map _ = _
      rw [hx]
      rfl
    show A.relR a (match b.R.red.out a τ with
      | some x => b.ext a τ (s.back x w)
      | none => d)
    rw [hb]
    refine hτ _ _ hb ?_
    by_cases hon : B.on (x, b.R.imp a.2 τ)
    · refine Or.inl (hs.know _ x' w hon hf ?_)
      exact hw.elim id fun n => absurd (hs.onOut _ x' hon hf) n
    · exact Or.inr hon

theorem BK.hands_post {T U : Type} {A B C : JK} (b : BK A B) (s : StepD B C) (d : A.W) (ρ : Rd T U
    A)
    (σ : Rd T U B) (θ : Rd T U C) (hb : b.Hands ρ σ) (h1 : ∀ x x', s.f x = some x' → θ.rc x' = σ.rc
        x)
    (h2 : ∀ y, θ.ix (s.g.map y) = σ.ix y) : (b.post s d).Hands ρ θ where
  passes := by
    intro x y τ x' h
    obtain ⟨x₁, hx, hf⟩ := Option.bind_eq_some_iff.1 (show (b.R.out x y τ).bind s.f = some x' from
        h)
    exact (h1 _ _ hf).trans (hb.passes _ _ _ _ hx)
  copy := fun y τ => (h2 _).trans (hb.copy y τ)

/-- (R2) a row of blocks, each with the step behind it -/
structure RowS : Type 1 where
  In  : ℕ → JK
  Out : ℕ → JK
  blk : ∀ i, BK (In i) (Out i)
  stp : ∀ i, StepD (Out i) (In (i + 1))
  d   : ∀ i, (In i).W

namespace RowS
variable (r : RowS)

/-- the seam behind block i -/
def SeamAt (i : ℕ) : Prop := (r.stp i).OK

noncomputable def seated (i : ℕ) : BK (r.In i) (r.In (i + 1)) := (r.blk i).post (r.stp i) (r.d i)

theorem seated_good (i : ℕ) (h : (r.blk i).Good) (s : r.SeamAt i) : (r.seated i).Good :=
  (r.blk i).good_post _ _ h s

/-- a place has the rounds of its block: no more -/
theorem seated_shape (i : ℕ) : (r.seated i).R.shape = (r.blk i).R.shape := rfl

noncomputable def list (n : ℕ) : LK (r.In 0) (r.In (n + 1)) := LK.fam r.In r.seated n

theorem each (n : ℕ) (hb : ∀ i ≤ n, (r.blk i).Good) (hs : ∀ i ≤ n, r.SeamAt i) : (r.list n).Each PG
    :=
  (LK.each_fam PG r.In r.seated n).2 fun i hi => r.seated_good i (hb i hi) (hs i hi)

theorem good (n : ℕ) (hb : ∀ i ≤ n, (r.blk i).Good) (hs : ∀ i ≤ n, r.SeamAt i) :
    ((r.list n).blk (r.d 0)).Good :=
  (r.list n).good _ (r.each n hb hs)

end RowS

#print axioms KObj.BK.good_post
#print axioms KObj.BK.hands_post
#print axioms KObj.RowS.good

end KObj
