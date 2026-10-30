-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoLkOut.lean.
The lookup of a sub-proof: what its output claim says, with the masked claim on the joint key vector
written out by the join.

The typed lookup's output claim at an out-statement x = ((st, θ), cl, rows) and a reading μ has
three clauses: the masked claim cl holds of the lookup's key vector; the rows hold; and a third that
is empty. The key vector is the joint key vector of the calls' key vectors (Fo.forA_key), and a
masked claim on that vector is an equation on the calls' own extensions (OnBytes.Ends.mcl_join).
This file puts the three steps into one statement.

States:
  lkOut_iff: for every α: the lookup's output claim holds of x and μ if and only if
      joinRhs h (forK L st μ) θ α cl.pt = α - cl.tg + the sum over all entries i of cl.mf i * μ i
    and the rows hold of μ.
    joinRhs (OnBytes.Ends.joinRhs) is: the sum over the calls c of eC h pt c times
    (α - c θ - the extension of call c's key vector at zkC h pt c), and the sum over the padding
    trees y of the equality weight of y times (α - the padding key).
  lkOut_unfold: the three clauses, as they stand.
Premise: FoNums.ok h = true. None on x, μ or α. E is a finite field, and the entries J₀ are finite.
Does not say: that forA E h L is the lookup that the sub-proofs' verifier runs
(OnBytes/Tie/Pv/Lookup/Forest/FoA.lean says what forA is and where it is tied); that a run reaches
x; that cl.pt is the verifier's point; which entries cl.mf reads.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoJoinAt

set_option autoImplicit false

namespace Fo
open Iop IOR Cb Cb.Tw Cb.LdLkp Cb.Lkp TwV Tw3 Tw Cb.Fo Finset OnBytes.Ends

section
variable {E : Type} [Field E] [Fintype E] {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀]

/-- The three clauses of the lookup's output claim, as they stand. -/
theorem lkOut_unfold (h : FoNums.Sh) (L : Lay E St₀ J₀) (x : TX (St₀ × E) E (Option J₀))
    (μ : Option J₀ → E) :
    (forA E h L).lk.out id id x μ ↔
      x.2.1.Holds (FoNums.v' h + 1) ((forA E h L).key x.1 μ) μ ∧ RowsHold x.2.2 μ ∧ True :=
  Iff.rfl

/-- **What the lookup's output claim says, by the join.** -/
theorem lkOut_iff (h : FoNums.Sh) (H : FoNums.ok h = true) (L : Lay E St₀ J₀) (α : E)
    (x : TX (St₀ × E) E (Option J₀)) (μ : Option J₀ → E) :
    (forA E h L).lk.out id id x μ ↔
      (joinRhs h (forK E L x.1.1 μ) x.1.2 α x.2.1.pt =
        α - x.2.1.tg + ∑ i, x.2.1.mf i * μ i) ∧ RowsHold x.2.2 μ := by
  rw [lkOut_unfold,
    mcl_join (ok_prem H) (forK E L x.1.1 μ) x.1.2 α x.2.1 μ (ok_v H).symm
      (forA_key E h L H x.1.1 x.1.2 μ)]
  exact ⟨fun ⟨a, b, _⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b, trivial⟩⟩

end
end Fo
