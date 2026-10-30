-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/MidRoots.lean: AT ALL 25 LINKS OF THE PROOF FILE's SEAT, IN THE
GOALS' SCOPE: BETWEEN THE RECORD BEHIND A LINK's FIRST SENDING (the cut iM + 1) AND THE RECORD IN
FRONT OF THE READS' SENDING (the cut iR) THE FOLD GOES THROUGH TWO QUIET BLOCKS: BOTH RECORDS PINNED
TO THE FOLD IN THE STATEMENT.
  mid_quiet (l < 24: cuts 14 l + 3 and 14 l + 5), mid_quiet24 (cuts 340 and 342): Quiet t₁ t₃.
  mid_roots, mid_roots24: so the count of roots is the same.
Johnson/IMR/ListsAtDraw.lean's mid_stretch and Johnson/IMR/ListsEnds.lean's lists_at_draw24 go the
same way inside
their proofs, with the middle record under "there is": they were to call these later, and do not.
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USER: whoever shows the row on the book's
names.
No soundness.
-/
import Johnson.IMR.ListsEnds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Pub Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **At a layers' or an attention link.** -/
theorem mid_quiet (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ l, l < 24 → ∀ (p : ProofFile.InstPub) (R : List Fmt.RoundView)
      (C : List VerifiableInference.Desc.OpenedColumn) (t₁ t₃ : S) (R₁ R₃ : List Fmt.RoundView)
      (C₁ C₃ : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 3)) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁) →
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 5)) (ProofFile.startS Z p) R C = .ok (t₃, R₃, C₃) →
      Quiet t₁ t₃ := by
  intro l h24 p R C t₁ t₃ R₁ R₃ C₁ C₃ f₁ f₃
  have hl : l ≤ 24 := by omega
  obtain ⟨Lk, b1, b1', eL, e1, k3, la1⟩ := IM.k3_of hS hR O l (by omega) false
  have ix1 : IM.k3Ix l false = 1 := by
    show (if false = true then 6 else 1) + (if l = 24 then 1 else 0) = 1
    rw [if_neg (by omega : ¬ l = 24)]
    rfl
  rw [ix1] at e1
  have q1 : Decides Quiet b1 := fun s rs gs t h =>
    (theStated_quiet _ _ _ _ _ _ k3).1 s rs gs t
      ((IM.yes_alone la1 (by intro k; cases k) s t rs gs).1 h).1
  obtain ⟨b2, e2, q2⟩ : ∃ b2, Lk.hear[2]? = some b2 ∧ Decides Quiet b2 := by
    rcases Nat.even_or_odd' l with ⟨g, rfl | rfl⟩
    · obtain ⟨Lk', b, y, eL', e, -, la, -⟩ := IM.k4_of hS hR O g (by omega)
      obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
      exact ⟨b, e, fun s rs gs t h => (blockAtC_quiet _).1 s rs gs t
        ((IM.yes_alone la (by intro k; cases k) s t rs gs).1 h).1⟩
    · obtain ⟨Lk', b, b', a, eL', e, k5, la, -⟩ := IM.k5_of hS hR O g (by omega)
      obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
      exact ⟨b, e, fun s rs gs t h => (k5AtN_quiet _ _ _ _ k5).1 s rs gs t
        ((IM.yes_alone la (by intro k; cases k) s t rs gs).1 h).1⟩
  have i1 : c.blocksInOrder[14 * l + 3]? = some b1 := by
    have k := IM.hear_at_flat eL e1
    rwa [(IM.flatIx_scope hS hR O hl 1).trans (by omega : 14 * l + 1 + 2 = 14 * l + 3)] at k
  have i2 : c.blocksInOrder[14 * l + 4]? = some b2 := by
    have k := IM.hear_at_flat eL e2
    rwa [(IM.flatIx_scope hS hR O hl 2).trans (by omega : 14 * l + 2 + 2 = 14 * l + 4)] at k
  obtain ⟨t₂, R₂, C₂, f₂⟩ := fold_back (k := 14 * l + 4) f₃
  obtain ⟨rs1, gs1, d1⟩ := fold_next i1 f₁ f₂
  obtain ⟨rs2, gs2, d2⟩ := fold_next i2 f₂ f₃
  exact quiet_trans _ _ _ (q1 _ _ _ _ d1) (q2 _ _ _ _ d2)

/-- **At the head's link.** -/
theorem mid_quiet24 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ (p : ProofFile.InstPub) (R : List Fmt.RoundView)
      (C : List VerifiableInference.Desc.OpenedColumn) (t₁ t₃ : S) (R₁ R₃ : List Fmt.RoundView)
      (C₁ C₃ : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take 340) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁) →
      foldBlocks 0 (c.blocksInOrder.take 342) (ProofFile.startS Z p) R C = .ok (t₃, R₃, C₃) →
      Quiet t₁ t₃ := by
  intro p R C t₁ t₃ R₁ R₃ C₁ C₃ f₁ f₃
  have ix : ∀ i, IM.flatIx c 24 i = 338 + i := fun i =>
    (IM.flatIx_scope hS hR O (by decide) i).trans (by omega)
  obtain ⟨Lk, b2, b2', eL, e2, k3, la2⟩ := IM.k3_of hS hR O 24 (by decide) false
  have e2' : Lk.hear[2]? = some b2 := e2
  obtain ⟨Lk3, b3, b3', ms, eL3, e3, -, k6, la3, -⟩ := IM.k6_of hS hR O
  obtain rfl : Lk = Lk3 := Option.some.inj (eL.symm.trans eL3)
  have q2 : Decides Quiet b2 := fun s rs gs t h =>
    (theStated_quiet _ _ _ _ _ _ k3).1 s rs gs t
      ((IM.yes_alone la2 (by intro k; cases k) s t rs gs).1 h).1
  have q3 : Decides Quiet b3 := fun s rs gs t h =>
    (seatedClaims_quiet k6).1 s rs gs t
      ((IM.yes_alone la3 (by intro k; cases k) s t rs gs).1 h).1
  have i2 : c.blocksInOrder[340]? = some b2 := by
    have k := IM.hear_at_flat eL e2'
    rwa [ix 2] at k
  have i3 : c.blocksInOrder[341]? = some b3 := by
    have k := IM.hear_at_flat eL e3
    rwa [ix 3] at k
  obtain ⟨t₂, R₂, C₂, f₂⟩ := fold_back (k := 341) f₃
  obtain ⟨rs2, gs2, d2⟩ := fold_next i2 f₁ f₂
  obtain ⟨rs3, gs3, d3⟩ := fold_next i3 f₂ f₃
  exact quiet_trans _ _ _ (q2 _ _ _ _ d2) (q3 _ _ _ _ d3)

/-- **THE COUNT OF ROOTS IS THE SAME AT THE CUTS iM + 1 AND iR**, (iM, iR) = (14 l + 2, 14 l + 5),
l < 24. -/
theorem mid_roots (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h24 : l < 24)
    {p : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn}
    {r₁ r₃ : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn}
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2 + 1)) (ProofFile.startS Z p) R C = .ok r₁)
    (f₃ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 5)) (ProofFile.startS Z p) R C = .ok r₃) :
    r₃.1.roots = r₁.1.roots :=
  (mid_quiet hS hR O l h24 p R C r₁.1 r₃.1 r₁.2.1 r₃.2.1 r₁.2.2 r₃.2.2 f₁ f₃).1.2.2.2

/-- The same at the head's link: (iM, iR) = (339, 342). -/
theorem mid_roots24 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn}
    {r₁ r₃ : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn}
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (339 + 1)) (ProofFile.startS Z p) R C = .ok r₁)
    (f₃ : foldBlocks 0 (c.blocksInOrder.take 342) (ProofFile.startS Z p) R C = .ok r₃) :
    r₃.1.roots = r₁.1.roots :=
  (mid_quiet24 hS hR O p R C r₁.1 r₃.1 r₁.2.1 r₃.2.1 r₁.2.2 r₃.2.2 f₁ f₃).1.2.2.2

#print axioms mid_quiet
#print axioms mid_quiet24
#print axioms mid_roots
#print axioms mid_roots24

end Meaning.K2
