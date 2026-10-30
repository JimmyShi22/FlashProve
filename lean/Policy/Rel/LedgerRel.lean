-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Rel/LedgerRel.lean

The relation pair of the integer model whose head carries the cost ledger, with the prime as a
variable: the conditions are formed modulo p.

`Ryes p pp` is the strict relation, `Rno p pp` the relaxed one (a larger bound on the witness's
cells); the table pp of scales and policy is a parameter. The layers' conditions, the output matrix
modulo p and the place of the request's form are those of Cm/TargetPRel.lean (the pair with the
plain head); the bound on cells and the honest trace are those of Cm/Rel.lean; the head's keys and
tables are those of Policy/Rel/LedgerHead.lean.

Limits:
* Definitions only: nothing on what the conditions force or admit, on segments as polynomial maps,
  or on protocols.
* That no condition has a prime inside is a reading; the theorem behind it is `ledger_lang`
  (Policy/Rel/LedgerRelLaws.lean), for every prime p with 2^61 - 1 ≤ p and every table with
  `TableOK`.
* The policy's three numbers stand in the conditions: the pair is that of one policy, `pp.pol`.
* What the heads of Cm/Rel.lean, Cm/RelBase.lean and Cm/TargetPRel.lean list as not said is not said
  here either (a lawful table need not be sensible; no weights are in sight; names of cells that no
  segment reads are free).
-/
import Cm.Rel
import Cm.TargetPRel
import Policy.Rel.True
import Policy.Rel.LedgerHead

set_option autoImplicit false

/- The next line removes the default table of scales (the instance `Scl.ref`) in this file.
Whatever reads a table here says which table. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Policy.LedgerRel

open Inst.Model Inst.Model.All

/-- What the statements on the pair ask of a table: its scales, taken without the policy, are lawful
(`Cm.Scales.Lawful`), and its policy has C, θ < 2^40, cap < 2^16. -/
structure TableOK (pp : ScalesAndPolicy) : Prop where
  scales : (⟨pp.w, pp.nf⟩ : Cm.Scales).Lawful
  pol : pp.pol.OK

variable (p : ℕ)

/-- The conditions, formed modulo p: in each of the 25 segments every key is an entry of its table
and every identity is 0; in the head besides the four clauses of the cost ledger; and y = 0 if
e < `ppref.T`. -/
structure Cond (pp : ScalesAndPolicy) (W : Mat) (x : Instance ppref) (T : Trace) :
    Prop extends Cm.TP.CondL p pp.kap pp.nf W (tokOf x.prompt) T where
  headKey : ∀ f a i, a < Head.len f → i < Head.nT →
    Head.InLut (LedgerHead.tableOf f)
      (LedgerHead.key pp.nf (T.vHead.cast (ZMod p)) (Cm.TP.castH p W) (Head.Req.of pp.pol x) f a i)
  headIdn : ∀ i < Head.nT, ∀ k < 17, Head.N.idn pp.nf (T.vHead.cast (ZMod p)) i k = 0
  headJc : ∀ i < Head.nT,
    Head.dB4 (T.vHead.cast (ZMod p)) (Head.Req.of pp.pol x) i = 0 ∧
    Head.dZ (T.vHead.cast (ZMod p)) (Head.Req.of pp.pol x) i = 0
  headSums : Head.sB2 (T.vHead.cast (ZMod p)) (Head.Req.of pp.pol x) = 0 ∧
    Head.sB3 (T.vHead.cast (ZMod p)) (Head.Req.of pp.pol x) = 0
  yZero : x.e < ppref.T → ((x.y.val : ℕ) : ZMod p) = 0

/-- The relation: r < e, every cell that some segment reads below 129 in absolute value
(`Cm.Below`), the conditions modulo p. -/
def Ryes (pp : ScalesAndPolicy) (i : Cm.Idx) (x : Instance ppref) (T : Trace) : Prop :=
  x.r < x.e ∧ Cm.Below 129 T ∧ Cond p pp i.mat x T

/-- Its relaxation: the same with the bound 2^18. -/
def Rno (pp : ScalesAndPolicy) (i : Cm.Idx) (x : Instance ppref) (T : Trace) : Prop :=
  x.r < x.e ∧ Cm.Below (2 ^ 18) T ∧ Cond p pp i.mat x T

end Policy.LedgerRel
