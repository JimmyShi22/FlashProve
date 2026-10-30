-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/BatchRide.lean: the draw that batches a ledger of claims into one form (`batch_knowAt`,
Cb/G6/Led.lean), beside a joint that rides along.

Definitions, one statement and its proof. In Cb/G6/Led.lean the joints before and behind the
batching draw speak of the ledger alone. Here a joint A0 on the statement's other part stands
unchanged on both sides: so a claim that leaves a sub-proof can pass the draw.

Main names:
  `ledInA A0 n msg`: A0, and every claim of the ledger holds; on the statements with A0's condition
    whose ledger has at most n claims.
  `ledOutA A0 msg`: A0, and the one form holds.
  `batchA_knowAt`: the draw as a block with `KnowAt` between the two, with the error n - 1.

Limits: nothing on an honest prover or on zero knowledge. The draw tests nothing of A0. The ledger
stands in the statement before the draw: each claim's coefficients and target are fixed before θ. A
claim whose form itself hangs on θ is no member of such a ledger: it must first be written as claims
that do not (one for each power of θ that it holds), and n counts these.

-/
import Cb.G6.Led

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att
open Iop Prob Cb IOR TWhole

variable {E J : Type} [Field E] [Fintype E] [Fintype J] {K M Wp P : Type} {Ex : ExtSpec}

/-- A0, and every claim of the ledger holds. -/
def ledInA (A0 : Rels K P Ex (M × Wp)) (n : ℕ) (msg : M → J → E) :
    Rels K (P × Ledger E J) Ex (M × Wp) :=
  ⟨fun x y w => A0.rel x.1 y w ∧ x.2.Holds (msg w.1),
    fun a w => A0.relR (a.1.1, a.2) w ∧ a.1.2.Holds (msg w.1),
    fun a => A0.on (a.1.1, a.2) ∧ a.1.2.length ≤ n, A0.core⟩

/-- A0, and the one form holds. -/
def ledOutA (A0 : Rels K P Ex (M × Wp)) (msg : M → J → E) :
    Rels K ((P × E) × Form E J) Ex (M × Wp) :=
  ⟨fun x y w => A0.rel x.1.1 y w ∧ x.2.Holds (msg w.1),
    fun a w => A0.relR (a.1.1.1, a.2) w ∧ a.1.2.Holds (msg w.1),
    fun a => A0.on (a.1.1.1, a.2), A0.core⟩

/-- The draw that batches a ledger, beside a joint that rides along. -/
theorem batchA_knowAt (A0 : Rels K P Ex (M × Wp)) (n : ℕ) (msg : M → J → E) :
    KnowAt (IOR.draw E (ledNx (J := J) (P := P)) Ex) (ledInA A0 n msg) (ledOutA A0 msg)
      (fun _ _ _ wp => wp) (Nums.draw K E (ledNx (J := J) (P := P)) Ex (n - 1)).err :=
  knowAt_draw _ _ _ (n - 1) (fun _ _ _ h => h.1) fun x _ m hx => by
    by_cases h : x.2.Holds (msg m)
    · rw [cnt_false fun θ hθ => by
        obtain ⟨_, h1, h2⟩ := hθ
        exact h2 ⟨h1.1, h⟩]
      exact Nat.zero_le _
    · refine le_trans (cnt_mono fun θ hθ => ?_)
        (le_trans (x.2.cnt_batch (msg m) h) (Nat.sub_le_sub_right hx.2 1))
      obtain ⟨_, h1, _⟩ := hθ
      exact h1.2

end Cb.Pv.Att
