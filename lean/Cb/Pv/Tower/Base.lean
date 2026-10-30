-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Tower/Base.lean: the last step of a proximity test (the rounds "BASE lambda" and "BASE" of a
plan) in the form in which the masking word went out earlier, inside an earlier prover message: a
typed reduction of two rounds without an oracle of its own; the statement that it is round-by-round
knowledge sound, proved under conditions on codes and numbers that no file here shows of any
setting.

The library's base case (`ldBaseIOR`, Cb/Ld/LdBase.lean) sends the masking word g as the oracle of
its first round. Here g stands in the input: the implicit part of the statement is the pair (input
word f, masking word g), and the joint is the library's joint of f read on the first component
(`IOR.Rels.keepE`, Ior/Frame.lean): it asks nothing of g. The verifier is the library's own, on the
transcript completed by g (`ldBaseUpR`, Cb/Ent/FoldRide.lean). The rounds are `ldBaseShapeN` (same
file): first a scalar u, answered by μ in E; then (message, randomness) in the clear, answered by t
long positions.

Main names (a : `LdJoint E`, Cb/Ld/LdTower.lean: code, linear form and radius are letters):
  `baseRide a t cov`: the reduction, from statements (target, state; f, g) to the trivial statement.
  `baseIn a`: its input joint, `a.rels.keepE a.C.nat`. `baseExt a t d`, `baseErr a t bad L2`: the
    library's extractor on the completed transcript; the library's two error counts.
  `BaseKnow a t cov d bad L2`: round-by-round knowledge soundness of `baseRide`, and nothing else.
  `base_know`: it holds under `a.BaseHypK d bad L2` (Cb/Ent/TowerKnow.lean: the code's laws, radius
    below d, mutual correlated agreement at the radius with the count bad, lists of two interleaved
    rows at most L2).
  `base_point`, `base_isLocal` (under the code's laws), `base_onOut`, `base_errList`.
  `base_out`: the verifier in closed form: it accepts if the library's test `LdwAccept` holds of the
    two words, and else rejects. `base_rounds`, `base_vals`: two rounds; the numbers of values of
    the verifier's messages.
  `baseRide_cov`: cov is idle in `baseRide`; it is an argument because the library's block has it.
  `BaseSize E`, `s.H`, `s.H₁`, `s.OK`, `s.h`, `s.h₁`: what is public of a last step as one record;
    the two statements at a size; the conditions; the statements hold under them.
  `BaseKnow₁`, `base_know₁`: the same clause for the library's own block, whose first round sends g.
  How the input joint meets the code switch's output joint: `cs_base_seam` (Cb/Pv/Tower/Cs.lean).

Why knowledge soundness passes: "the prover has lost" at the first round is a bound for every first
message (g, u) of the library's block; the block here, at the statement with g, is the instance at
that g.

Limits: knowledge soundness and the verifier's format alone: nothing on an honest prover. Nothing
says that bad and L2 are small. Who has the count of agreement beyond a third of the distance is an
instance's matter; the theorem on codes that is taken as given elsewhere (`Cb.BCHKS46At`,
Cb/Gen/CodeListRSAt.lean) does not occur in this file. The errors are bare counts for one instance:
nothing on proof of work, nothing on several instances. That the masking word among the input's
oracles is what an earlier block sent is that block's output joint's matter.

-/
import Cb.Ent.FoldRide
import Cb.Ent.TowerKnow
import Cb.Ld.LdBaseProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Cb.Pv.Tower
open Iop Prob IOR Blocks

variable {E : Type} [Field E] [Fintype E] (a : LdJoint E) (t : ℕ) (cov : a.C.NP → a.P)

open Classical in
/-- The last step, the masking word in the input. -/
def baseRide : IOR a.X (a.C.ext.prod a.C.nat) Unit extNone where
  shape := ldBaseShapeN a.C t
  blinded _ := true
  extReads ρ := (Finset.univ.image ρ.2.1).image Sum.inl ∪
    ((Finset.univ.image ρ.2.1).biUnion a.C.src).image Sum.inr
  reads _ := ∅
  out x y τ := (ldBaseIOR a.C a.sl t cov).out x y.1 (ldBaseUpR a.C t y.2 τ)
  imp _ _ := ()
  srcE _ _ := ∅
  srcO _ _ := ∅
  tie _ _ := ∅

/-- The input joint: the joint a, read on the input word; nothing is asked of the masking word. -/
def baseIn : IOR.Rels Unit a.X (a.C.ext.prod a.C.nat) a.W := a.rels.keepE a.C.nat

/-- The library's extractor, on the completed transcript. -/
def baseExt (d : ℕ) :
    a.X × (a.C.ext.prod a.C.nat).Str → Tr (ldBaseShapeN a.C t) → Unit → a.W :=
  fun s τ u => ldBaseExt a.C t d (s.1, s.2.1) (ldBaseUpR a.C t s.2.2 τ) u

/-- The library's two error counts. -/
def baseErr (bad L2 : ℕ) : Err (ldBaseShapeN a.C t) :=
  (bad + L2, ((Fintype.card a.P - a.e - 1) ^ t, ()))

/-- Round-by-round knowledge soundness of the last step, the masking word in the input. -/
def BaseKnow (d bad L2 : ℕ) : Prop :=
  (baseRide a t cov).red.Know (baseIn a).on (baseIn a).relR trivRels.relR (baseExt a t d)
    (baseErr a t bad L2)

/-- The same clause for the library's own block, whose first round sends the masking word. -/
def BaseKnow₁ (d bad L2 : ℕ) : Prop := (ldBaseEnd a t cov d bad L2).KnowT

theorem base_know (d bad L2 : ℕ) (h : a.BaseHypK d bad L2) : BaseKnow a t cov d bad L2 :=
  fun s _ m =>
    ldBase_know a.C a.sl t cov h.laws h.lt h.mca h.list (s.1, s.2.1) trivial (s.2.2, m.2)

theorem base_know₁ (d bad L2 : ℕ) (h : a.BaseHypK d bad L2) : BaseKnow₁ a t cov d bad L2 :=
  ldBase_know a.C a.sl t cov h.laws h.lt h.mca h.list

theorem base_point : Nonempty (baseRide a t cov).shape.IsPoint :=
  ⟨(plainPoint _ _ _, plainPoint _ _ _, ())⟩

theorem base_onOut : ∀ s τ b, (baseIn a).on s → (baseRide a t cov).red.out s τ = some b →
    trivRels.on b := fun _ _ _ _ _ => trivial

theorem base_isLocal (hC : a.C.Laws) : (baseRide a t cov).IsLocal where
  out := by
    classical
    intro x y y' τ τ' hρ hpl hy _
    refine (ldBase_isLocal (sl := a.sl) (t := t) (cov := cov) hC).out x y.1 y'.1
      (ldBaseUpR a.C t y.2 τ) (ldBaseUpR a.C t y'.2 τ') hρ hpl ?_ ?_
    · intro p hp
      exact Sum.inl.inj (hy (Sum.inl p) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)))
    · intro p hp
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hp
      have h := Sum.inr.inj
        (hy (Sum.inr n) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hn)))
      exact eq_of_heq (Sigma.mk.inj h).2
  imp := fun _ _ _ _ q => q.elim

theorem base_errList (bad L2 : ℕ) :
    (baseErr a t bad L2).toList = [bad + L2, (Fintype.card a.P - a.e - 1) ^ t] := rfl

open Classical in
/-- The verifier in closed form: the library's test, on the input word and the masking word. -/
theorem base_out (x : a.X) (y : (a.C.ext.prod a.C.nat).Str) (τ : Tr (ldBaseShapeN a.C t)) :
    (baseRide a t cov).out x y τ =
      if LdwAccept (ldCw a.C) (ldForm a.sl x) x.1 (a.C.T y.1) (a.C.T y.2) τ.1.2 τ.2.1 τ.2.2.1.2
          τ.2.2.2.1 then some ()
      else none := rfl

/-- cov is idle. -/
theorem baseRide_cov (cov' : a.C.NP → a.P) : baseRide a t cov = baseRide a t cov' := rfl

theorem base_rounds : (baseRide a t cov).shape.length = 2 := rfl

theorem base_vals :
    (baseRide a t cov).shape.chalList = [Fintype.card E, Fintype.card (Fin t → a.P)] := rfl

/-! ### the statement at a size -/

/-- What is public of a last step: the joint (code, form, radius), the number t of positions, and
the numbers of the statement: the corrector's threshold d, the count bad, the list size L2. cov is
an argument of the library's block; `s.H` does not hang on it (`baseRide_cov`). -/
structure BaseSize (E : Type) where
  a : LdJoint E
  t : ℕ
  cov : a.C.NP → a.P
  d : ℕ
  bad : ℕ
  L2 : ℕ

variable (s : BaseSize E)

/-- The statement that BASE whose masking word was sent earlier, at the size s, is knowledge
sound. -/
def BaseSize.H : Prop := BaseKnow s.a s.t s.cov s.d s.bad s.L2

/-- The statement that BASE that sends its masking word, at the size s, is knowledge sound. -/
def BaseSize.H₁ : Prop := BaseKnow₁ s.a s.t s.cov s.d s.bad s.L2

/-- Conditions, as in the library's theorem on the base case, on public data alone. -/
def BaseSize.OK : Prop := s.a.BaseHypK s.d s.bad s.L2

theorem BaseSize.h (h : s.OK) : s.H := base_know s.a s.t s.cov s.d s.bad s.L2 h

theorem BaseSize.h₁ (h : s.OK) : s.H₁ := base_know₁ s.a s.t s.cov s.d s.bad s.L2 h

#print axioms BaseSize.h
#print axioms BaseSize.h₁
#print axioms base_isLocal

end Cb.Pv.Tower
