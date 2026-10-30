--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/SpRow.lean: the tree beneath which the split's mask message o_sp lies, and
the one row in it: ON THE PLAN. A test with code, what its acceptance gives, and kernel evaluations
at two written values of the library.

Why. A count of the positions that declared rounds sample for a tree is held against the random tail
of each row beneath that tree. Which rows lie beneath which tree, and under which code, has to be
read off the verifier's own text. Here that is begun for one tree.

The two written values: realSized (Johnson/Desc/K1/Law/CondReal.lean: sizes over a proof file's own
codes, into which the numbers 101, 51 and 152 are written by hand) and keyFull
(Johnson/Goal/PlanValues/KeySizedReturns.lean: the sizes of a key of full size).

  spCode      the code under which o_sp's mask row stands: the shared groups' mask code
  spRowB      THE TEST, on codes, shape and what goes out with o_u: the trees of "send o_u" are one;
              those of "send o_omega" are two; o_sp's notice gets the second, as its first part;
              that tree has no main symbol, three mask words, and the length of spCode; o_sp has no
              main row, ONE mask row, the shared groups' mask code, and one out-of-domain answer
  SpRow, spRow_of   what its acceptance gives, as a structure of equations, for all codes and shapes
  spTailB     a test on sizes: the numbers of positions of the two proximity tests' first lists,
              added up, are the tail of spCode
  spRow_real, spRow_key     both tests accept at the two written values (decide +kernel)
  spCode_real, spCode_key   the code there: (2 ^ 13, 64, 152), and (2 ^ 13, 64, 146)
  spTail_fails   one position more in either list, or a tail shorter by one, and spTailB rejects
  spRow_fails    o_sp in o_omega's leaf class, a second mask row, or another mask code: spRowB
              rejects

What is not claimed. That any round opens that tree, or how often: no round occurs here. That a
planner sizes the tail as the sum of the two numbers: that rule (OnBytes/Params/DeriveLin.lean) is
no theorem, here or in the library. That the planner's sizes of a proof at the release's files are
realSized. Nothing on a verifier's decision (the state behind the two sendings:
Johnson/Desc/K14/Honest/SpTree.lean), on soundness or on hiding.

-/
import Johnson.Goal.Numbers.K14CondAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params
open VerifiableInference.Desc.K1 (realSized)
open Lk6.AtPlan (keyFull)

/-- The code under which o_sp's mask row stands. -/
def spCode (codes : Codes) (S : LinShape) : Code := codes.mask.getD S.sharedMaskCode default

/-- The shape of a tree that holds one mask row under the code z, and nothing else. -/
def oneMaskRow (z : Code) : TreeShape :=
  { logN := z.logN, logNzk := z.logN, mainSymbols := #[0], maskSymbols := #[3] }

/-- **The test on the plan.** -/
def spRowB (codes : Codes) (S : LinShape) (sentU : Array OracleNotice) : Bool :=
  (layTrees codes sentU).any (fun l => l.shapes.size == 1) &&
  (layTrees codes (withOmega S)).any (fun l =>
    l.shapes.size == 2 && l.tree.getD 0 0 == 0 && l.tree.getD 1 0 == 1 && l.part.getD 1 0 == 0 &&
      l.shapes.getD 1 {} == oneMaskRow (spCode codes S)) &&
  S.sharedSplit.mainRows == 0 && S.sharedSplit.maskRows == 1 &&
  S.sharedSplit.maskCode == S.sharedMaskCode && S.sharedSplit.answers == 1

/-- What the test's acceptance gives. layU, layO: how the trees of the two sendings are laid. -/
structure SpRow (codes : Codes) (S : LinShape) (layU layO : TreeLay) : Prop where
  oneTree : layU.shapes.size = 1
  twoTrees : layO.shapes.size = 2
  omegaFirst : layO.tree.getD 0 0 = 0
  spSecond : layO.tree.getD 1 0 = 1
  spPart : layO.part.getD 1 0 = 0
  shape : layO.shapes.getD 1 {} = oneMaskRow (spCode codes S)
  noMain : S.sharedSplit.mainRows = 0
  oneRow : S.sharedSplit.maskRows = 1
  code : S.sharedSplit.maskCode = S.sharedMaskCode
  oneAnswer : S.sharedSplit.answers = 1

theorem spRow_of {codes : Codes} {S : LinShape} {sentU : Array OracleNotice} {layU layO : TreeLay}
    (h : spRowB codes S sentU = true) (hU : layTrees codes sentU = some layU)
    (hO : layTrees codes (withOmega S) = some layO) : SpRow codes S layU layO := by
  unfold spRowB at h
  rw [hU, hO] at h
  simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩⟩, f⟩, g⟩, i⟩, j⟩ := h
  exact ⟨h1, a, b, c, d, e, f, g, i, j⟩

/-- **A test on sizes**: the two first lists' numbers of positions, added up, are the tail of o_sp's
code. -/
def spTailB (x : LinSized) (codes : Codes) : Bool :=
  x.folded.t + x.omega.t == (spCode codes x.shape).r

/-! ## At the two written values -/

theorem spRow_real : (realSized.any fun p =>
    (withU p.1.shape).any (spRowB p.2 p.1.shape) && spTailB p.1 p.2) = true := by
  decide +kernel

theorem spRow_key :
    ((withU keyFull.once.shape).any (spRowB keyFull.codes keyFull.once.shape) &&
      spTailB keyFull.once keyFull.codes) = true := by
  decide +kernel

theorem spCode_real : (realSized.any fun p =>
    decide (((spCode p.2 p.1.shape).logN, (spCode p.2 p.1.shape).ell, (spCode p.2 p.1.shape).r,
      p.1.folded.t, p.1.omega.t) = (13, 64, 152, 101, 51))) = true := by
  decide +kernel

theorem spCode_key :
    ((spCode keyFull.codes keyFull.once.shape).logN, (spCode keyFull.codes keyFull.once.shape).ell,
      (spCode keyFull.codes keyFull.once.shape).r, keyFull.once.folded.t, keyFull.once.omega.t) =
      (13, 64, 146, 97, 49) := by
  decide +kernel

/-- **It can fail**: one position more in either list, or a tail shorter by one, and the test
rejects. -/
theorem spTail_fails : (realSized.any fun p =>
    !spTailB { p.1 with folded := { p.1.folded with t := p.1.folded.t + 1 } } p.2 &&
      !spTailB { p.1 with omega := { p.1.omega with t := p.1.omega.t + 1 } } p.2 &&
      !spTailB p.1 { p.2 with mask := p.2.mask.modify p.1.shape.sharedMaskCode fun z =>
        { z with r := z.r - 1 } }) = true := by
  decide +kernel

/-- **The test on the plan can fail**: with o_sp in o_omega's leaf class it would share that tree;
with a second mask row, or under another mask code, the row is not the one: each time spRowB
rejects. -/
theorem spRow_fails : (realSized.any fun p =>
    (withU p.1.shape).any fun u =>
      !spRowB p.2 { p.1.shape with sharedSplitLeafClass := p.1.shape.omegaLeafClass } u &&
      !spRowB p.2 { p.1.shape with
        sharedSplit := { p.1.shape.sharedSplit with maskRows := 2 } } u &&
      !spRowB p.2 { p.1.shape with
        sharedSplit := { p.1.shape.sharedSplit with maskCode := p.1.shape.ownMaskCode } } u) =
    true := by
  decide +kernel

end Desc.K14.Honest

#print axioms Desc.K14.Honest.spRow_fails
#print axioms Desc.K14.Honest.spRow_of
#print axioms Desc.K14.Honest.spRow_real
#print axioms Desc.K14.Honest.spRow_key
#print axioms Desc.K14.Honest.spCode_real
#print axioms Desc.K14.Honest.spCode_key
#print axioms Desc.K14.Honest.spTail_fails
