-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/OCompCostP.lean: the monad of trees of queries: "tosses no coin, asks at most t, and whatever
it puts out has P" as a count with a condition on what comes out.

One definition: the instance, at ZKCP/Defs.lean's `OComp lam` (oracle computations), of
Run/CostP.lean's notion; what it says, by definition; the hash.

Main names:
  `qp lam`: `CostP (OComp lam)`: le x t P := x.NoCoin ∧ x.QueryBound t ∧ x.All P (`QueryBound`:
    ZKCP/Defs.lean; `NoCoin`: Run/OCompM.lean; `All`: Run/OCompAll.lean; bind: what follows is
    judged only at outputs with P).
  `qp_HM`: the hash over the tree monad: no coin, at most two queries (no condition on the answer).

Limits: this file says nothing on any rule of the format but the hash (`qp_HM`): the counts at the
format's functions are in Run/CostFmt.lean.

Terms: lean/GLOSSARY.md.
-/
import Run.CostP
import Run.OCompAll

set_option autoImplicit false

namespace Run
open ZKCP

/-- No coin, at most t queries, every output has P. -/
def qp (lam : ℕ) : CostP (OComp lam) where
  le := fun x t P => x.NoCoin ∧ x.QueryBound t ∧ x.All P
  le_pure := fun _ _ h => ⟨trivial, trivial, h⟩
  le_bind := fun x _ s _ _ _ hx hg =>
    ⟨OComp.NoCoin.bindP (fun a ha => (hg a ha).1) hx.2.2 hx.1,
      OComp.QueryBound.bindP (fun a ha => (hg a ha).2.1) x s hx.2.2 hx.2.1,
      OComp.All.bind (fun a ha => (hg a ha).2.2) hx.2.2⟩
  le_mono := fun x s t _ _ hx hst hPQ =>
    ⟨hx.1, OComp.QueryBound.mono x s t hst hx.2.1, OComp.All.mono hPQ hx.2.2⟩

theorem qp_le {lam : ℕ} {α : Type} (x : OComp lam α) (t : ℕ) (P : α → Prop) :
    (qp lam).le x t P ↔ x.NoCoin ∧ x.QueryBound t ∧ x.All P := Iff.rfl

theorem qp_HM (number tree index : Nat) (start bytes : ByteArray) :
    (qp 256).le (_root_.Fmt.HM askB number tree index start bytes) 2 fun _ => True :=
  ⟨noCoin_HM number tree index start bytes, asks_HM number tree index start bytes, OComp.all_true _⟩

end Run
