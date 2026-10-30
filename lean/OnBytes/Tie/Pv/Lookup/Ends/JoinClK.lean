-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/JoinClK.lean: the claim on the keys of the library's assembled lookup
(LkAsm2.clK), when the keys are the joint key vector, as an equation on joinRhs, the right side of
join_identity.

Statements and proofs. A claim is of the library's type Cb.LdLkp.MCl (Cb/Ld/LdLkpTree.lean): a point
pt, a linear form mf on further entries and a target tg. c.Holds k f μ says that the extension of f
(k variables) at pt plus the form at μ is tg. joinRhs and Prem are those of
OnBytes/Tie/Pv/Lookup/Ends/Join.lean.
Main names:
  `mcl_join`: for any claim c, any entries μ and any α: c holds of the joint key vector iff joinRhs
    at c's point equals α - c.tg + the form mf at μ.
  `topCl_join`: for any data of a lookup, I : LkInst E (Cb/Ld/LdLkpInst.lean): the claim I.topCl x
    at the top of the keys' tree holds iff joinRhs at that claim's point, with I.lam at x's state
    for α, equals x.1 less the incoming form at the entries m.
  `sum_join`: the same of the tree's own sum claim at its top (SumHolds), through the library's
    ldLkpInst_topK (Cb/Ld/LdLkpInstProofs.lean).
  `clK_join`: the same of A.clK x for an assembled lookup A : LkAsm2 E (Cb/Ld/LdLkpAsm2.lean).
Under, in all four: Prem h; the number of the keys' bits is the shape's v (k = h.v; I.v = h.v;
A.v' + 1 = h.v); the keys are the joint key vector (f = jointKey h kv θ; in the last three: the keys
at x's state and at the entries m are jointKey h kv θ). E is any field in mcl_join, where the type
N of the further entries is finite, and a finite field in the other three.
Does not say: that the point is the port's (the port: the Lean verifier under OnBytes/); which
entries the form reads; anything on the places of masks, on a round or on a message.

-/
import Cb.Ld.LdLkpAsm2
import OnBytes.Tie.Pv.Lookup.Ends.Join

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Ends

open Finset Blocks OnBytes.Model Cb Cb.LdLkp

section
variable {E : Type} [Field E]

/-- A claim (MCl) on the joint key vector, as an equation on joinRhs. -/
theorem mcl_join {N : Type} [Fintype N] {h : Forest.Shape} (hp : Prem h) (kv : ℕ → ℕ → E)
    (θ α : E) (c : MCl E N) (μ : N → E) {k : ℕ} (hk : k = h.v) {f : ℕ → E}
    (hf : f = jointKey h kv θ) :
    c.Holds k f μ ↔ joinRhs h kv θ α c.pt = α - c.tg + ∑ i, c.mf i * μ i := by
  subst hk hf
  unfold MCl.Holds
  rw [← join_identity hp kv θ α c.pt]
  constructor
  · intro e
    linear_combination (-1 : E) * e
  · intro e
    linear_combination (-1 : E) * e

end

section
variable {E : Type} [Field E] [Fintype E]

/-- The same at the data of the keys' tree: the right side is written in topCl's own fields. -/
theorem topCl_join (I : LkInst E) {h : Forest.Shape} (hp : Prem h) (hv : I.v = h.v)
    (kv : ℕ → ℕ → E) (θ : E) (x : E × (I.DK.lv I.v).T.St) (m : I.J → E)
    (hk : I.key (I.st ((I.DK.lv I.v).base x.2)) m = jointKey h kv θ) :
    (I.topCl x).Holds I.v (I.key (I.st ((I.DK.lv I.v).base x.2)) m) m ↔
      joinRhs h kv θ (I.lam ((I.DK.lv I.v).base x.2)) (I.topCl x).pt =
        x.1 - ∑ j, pushJ (I.DK.lv I.v).toJ ((I.DK.lv I.v).T.slS x.2) j * m j := by
  refine (mcl_join hp kv θ (I.lam ((I.DK.lv I.v).base x.2)) (I.topCl x) m hv hk).trans ?_
  have e : I.lam ((I.DK.lv I.v).base x.2) - (I.topCl x).tg + ∑ j, (I.topCl x).mf j * m j =
      x.1 - ∑ j, pushJ (I.DK.lv I.v).toJ ((I.DK.lv I.v).T.slS x.2) j * m j := by
    show I.lam ((I.DK.lv I.v).base x.2) - (I.lam ((I.DK.lv I.v).base x.2) - x.1) +
        ∑ j, (- pushJ (I.DK.lv I.v).toJ ((I.DK.lv I.v).T.slS x.2) j) * m j = _
    simp only [neg_mul, sum_neg_distrib]
    ring
  rw [e]

/-- The tree's own sum claim at its top, as the join: with the library's `ldLkpInst_topK`. -/
theorem sum_join (I : LkInst E) {h : Forest.Shape} (hp : Prem h) (hv : I.v = h.v)
    (kv : ℕ → ℕ → E) (θ : E) (x : E × (I.DK.lv I.v).T.St) (m : I.J → E)
    (hk : I.key (I.st ((I.DK.lv I.v).base x.2)) m = jointKey h kv θ) :
    (I.DK.lv I.v).T.SumHolds x (fun j => m ((I.DK.lv I.v).toJ j)) ↔
      joinRhs h kv θ (I.lam ((I.DK.lv I.v).base x.2)) (I.topCl x).pt =
        x.1 - ∑ j, pushJ (I.DK.lv I.v).toJ ((I.DK.lv I.v).T.slS x.2) j * m j :=
  (ldLkpInst_topK E I x m).trans (topCl_join I hp hv kv θ x m hk)

/-- The same for the assembled lookup: every A whose keys at the state are the joint key vector. The
state and λ are those that A's own data of the keys' side read off x. -/
theorem clK_join (A : LkAsm2 E) {h : Forest.Shape} (hp : Prem h) (hv : A.v' + 1 = h.v)
    (kv : ℕ → ℕ → E) (θ : E) (x : A.X4) (m : A.J → E)
    (hk : A.key ((A.IK.setV (A.v' + 1)).st
      (((A.IK.setV (A.v' + 1)).DK.lv (A.v' + 1)).base x.2)) m = jointKey h kv θ) :
    (A.clK x).Holds (A.v' + 1) (A.key ((A.IK.setV (A.v' + 1)).st
        (((A.IK.setV (A.v' + 1)).DK.lv (A.v' + 1)).base x.2)) m) m ↔
      joinRhs h kv θ ((A.IK.setV (A.v' + 1)).lam
          (((A.IK.setV (A.v' + 1)).DK.lv (A.v' + 1)).base x.2)) (A.clK x).pt =
        x.1 - ∑ j, pushJ ((A.IK.setV (A.v' + 1)).DK.lv (A.v' + 1)).toJ
          (((A.IK.setV (A.v' + 1)).DK.lv (A.v' + 1)).T.slS x.2) j * m j :=
  topCl_join (A.IK.setV (A.v' + 1)) hp hv kv θ x m hk

end

end OnBytes.Ends

#print axioms OnBytes.Ends.mcl_join
#print axioms OnBytes.Ends.topCl_join
#print axioms OnBytes.Ends.sum_join
#print axioms OnBytes.Ends.clK_join
