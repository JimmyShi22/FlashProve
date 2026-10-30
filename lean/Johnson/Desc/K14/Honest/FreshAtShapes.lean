--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/FreshAtShapes.lean: six PUBLIC premises of fresh_sent
(Johnson/Desc/K14/Honest/FreshAt.lean), those on the codes and the shape alone, hold at the
library's two typed shapes. Kernel evaluations.

  FreshPublic     six premises of fresh_sent as one proposition: o_sp's mask code has n + 1 message
                  entries, a power of two, and at most 2 ^ 32 positions; o_sp has no main row, one
                  mask row and one out-of-domain answer. A seventh field is no premise: it names the
                  number r of the tail's entries
  fresh_public_key   it holds at keyFull.once.shape (Lk6.AtPlan.keyFull), with n = 63, r = 146
  fresh_public_real, fresh_public_full   at what realSized returns
                  (Johnson/Desc/K1/Law/CondReal.lean), with n = 63, r = 152: the first as a test
                  with code under Option.any, the second as the proposition at a named member
  FreshPublic.shape, fresh_sent_public   fresh_sent, CALLED from FreshPublic and a set of at most r
                  positions, through SpShape and fresh_sent_shape
                  (Johnson/Desc/K14/Honest/FreshAtChain.lean)
  splits_key, splits_full   both shapes split: the premise of fresh_chain on the shape
  spSymCode_eq    o_sp's own mask code is the shared groups' mask code
                  (spCode, Johnson/Desc/K14/Honest/SpRow.lean), where that file's test accepts

The two shapes are not of one grade. keyFull is what the planner's sizing of a key returns
(keySized_returns, Johnson/Goal/PlanValues/KeySizedReturns.lean). Into realSized the code's numbers
64 and 152 are written by hand: there these theorems read back what was typed in.

What is not claimed. That the sizes of a proof at the release's files are the typed ones. Nothing on
the other premises of fresh_sent: the set of positions, the statement, the sending's parameters, the
seed. Nothing on any property.

-/
import Johnson.Desc.K14.Honest.FreshAtChain
import Johnson.Desc.K14.Honest.SpRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open VerifiableInference.Desc.K1 (realSized)
open Johnson.G (codesFull2)
open Lk6.AtPlan (keyFull)

/-- The public premises of fresh_sent, with code. -/
def freshPublicB (codes : Codes) (Sh : LinShape) (n r : ℕ) : Bool :=
  (spSymCode codes Sh).l == n + 1 &&
  2 ^ (codes.mask.getD Sh.sharedSplit.maskCode default).logEll == (spSymCode codes Sh).l &&
  decide ((spSymCode codes Sh).a ≤ 32) && Sh.sharedSplit.mainRows == 0 &&
  Sh.sharedSplit.maskRows == 1 && Sh.sharedSplit.answers == 1 && (spSymCode codes Sh).r == r

/-- **The public premises of fresh_sent.** -/
structure FreshPublic (codes : Codes) (Sh : LinShape) (n r : ℕ) : Prop where
  length : (spSymCode codes Sh).l = n + 1
  power : 2 ^ (codes.mask.getD Sh.sharedSplit.maskCode default).logEll = (spSymCode codes Sh).l
  positions : (spSymCode codes Sh).a ≤ 32
  noMain : Sh.sharedSplit.mainRows = 0
  oneRow : Sh.sharedSplit.maskRows = 1
  oneAnswer : Sh.sharedSplit.answers = 1
  tail : (spSymCode codes Sh).r = r

theorem freshPublic_of {codes : Codes} {Sh : LinShape} {n r : ℕ}
    (h : freshPublicB codes Sh n r = true) : FreshPublic codes Sh n r := by
  unfold freshPublicB at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩ := h
  exact ⟨a, b, c, d, e, f, g⟩

/-- At the key's one-time test. -/
theorem fresh_public_key : FreshPublic keyFull.codes keyFull.once.shape 63 146 :=
  freshPublic_of (by decide +kernel)

/-- At the stored full size. -/
theorem fresh_public_real :
    (realSized.any fun p => freshPublicB p.2 p.1.shape 63 152) = true := by
  decide +kernel

/-- o_sp's own mask code is the shared groups' mask code. -/
theorem spSymCode_eq {codes : Codes} {Sh : LinShape} {layU layO : TreeLay}
    (R : SpRow codes Sh layU layO) :
    spSymCode codes Sh =
      ⟨(spCode codes Sh).logN, (spCode codes Sh).ell, (spCode codes Sh).r⟩ := by
  unfold spSymCode spCode
  rw [R.code]
  rfl

/-- At the stored full size, as a proposition at a named member: what realSized returns has the
written codes, and the public premises hold there. -/
theorem fresh_public_full : ∃ x : LinSized,
    realSized = some (x, codesFull2) ∧ FreshPublic codesFull2 x.shape 63 152 := by
  obtain ⟨x, _, _, hx, _⟩ := VerifiableInference.Desc.K1.real_members
  refine ⟨x, hx, freshPublic_of ?_⟩
  have h := fresh_public_real
  rw [hx] at h
  exact h

/-- FreshPublic gives the six premises in the form from which fresh_sent is called. -/
theorem FreshPublic.shape {codes : Codes} {Sh : LinShape} {n r : ℕ} (H : FreshPublic codes Sh n r) :
    SpShape codes Sh n :=
  ⟨H.length, H.power, H.positions, H.noMain, H.oneRow, H.oneAnswer⟩

/-- **fresh_sent, CALLED from FreshPublic and a set of at most r positions** (through
fresh_sent_shape): so this file stops compiling if the premises of fresh_sent change. -/
theorem fresh_sent_public (codes : Codes) (Sh : LinShape) (n r : ℕ) (H : FreshPublic codes Sh n r)
    (Q : VerifiableInference.Desc.K1.Par) (first : ℕ) (w₀ : OnBytes.Means.Words Cb.Gl.E)
    (psiLo zfd : List Cb.Gl.E) (u : ℕ → Cb.Gl.E) (cOmega : MsgCoins)
    (S : Finset (Fin (2 ^ (spSymCode codes Sh).a))) (hS : S.card ≤ r) (T : Statement)
    (X : OnBytes.Oracle) (hX : T.oracles[first + 1]? = some X) (hXs : X.shape = Sh.sharedSplit)
    (hT : T.codes = codes) (h2 : 1 < Q.sent.size)
    (hQ : Johnson.Prover.Send.shapeAt Q 1 = Sh.sharedSplit) (z : List E) (β y : E)
    (hz : (VerifiableInference.Desc.K1.Msg.of codes Sh.sharedSplit).v ≤ z.length)
    (hβ : OnBytes.Slice.readE β ≠ 0) (kappa : Fin n) :
    FreshLaw (spSymCode codes Sh).r n S
      (spTriple codes Sh Q first w₀ psiLo zfd u cOmega n S T z β y kappa) :=
  fresh_sent_shape codes Sh n H.shape Q first w₀ psiLo zfd u cOmega S (by rw [H.tail]; exact hS) T X
    hX hXs hT h2 hQ z β y hz hβ kappa

/-- Both typed shapes split: so fresh_chain's premise on the shape holds there. -/
theorem splits_key : keyFull.once.shape.sharedSplitNeeded = true := by decide +kernel

@[inherit_doc splits_key]
theorem splits_full : ∃ x : LinSized,
    realSized = some (x, codesFull2) ∧ x.shape.sharedSplitNeeded = true := by
  obtain ⟨x, _, _, hx, _⟩ := VerifiableInference.Desc.K1.real_members
  refine ⟨x, hx, ?_⟩
  have h : (realSized.any fun p => p.1.shape.sharedSplitNeeded) = true := by decide +kernel
  rw [hx] at h
  exact h

end Desc.K14.Honest

#print axioms Desc.K14.Honest.freshPublic_of
#print axioms Desc.K14.Honest.fresh_public_key
#print axioms Desc.K14.Honest.fresh_public_real
#print axioms Desc.K14.Honest.spSymCode_eq
#print axioms Desc.K14.Honest.fresh_public_full
#print axioms Desc.K14.Honest.FreshPublic.shape
#print axioms Desc.K14.Honest.fresh_sent_public
#print axioms Desc.K14.Honest.splits_key
#print axioms Desc.K14.Honest.splits_full
