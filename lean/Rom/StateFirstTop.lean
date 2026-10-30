-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/StateFirstTop.lean: the step that expands a long answer of a random oracle from a state
(Rom/StateFirst.lean): proves `Spec.stateFirst` (stated there). No `Spec` statement is assumed.

After the step a chain oracle returns only a state: the chaining value and the last block, hid, of
its old answer; the other hash blocks are answers of an added oracle dr to expansion queries (state,
counter). (`Link`, `stSpec`: Rom/StateFirst.lean.)

  `stateFirst`
              Completeness, index binding and index privacy carry over from a scheme A over a family
              S of typed oracles to `stateFirstArg C A` over the second family `stSpec S lam C`,
              with the extractor `extSt C E`, the simulator `simSt C Sim` and the hypotheses and
              prices of the statement.

From `completeness_stateFirst`, `binding_stateFirst` (Rom/StateFirstCB.lean); `privacy_stateFirst`
(Rom/StateFirstPriv.lean) at `mixClose` (Rom/StateFirstClose.lean).

Notation:
  `lam`: a natural number: a hash block has `lam` bits (`Dg lam`, Rom/NeedA.lean)
  `C`: for each oracle o of S, a `Link lam (S.Rng o)` (Rom/StateFirst.lean): how an oracle with
      answers in R is treated (`plain` or `chain K e`)
  chain oracle: an oracle o with `C o` of the form `Link.chain K e` (Rom/StateFirst.lean); the other
      oracles are unchanged (`Link.plain`)
  B, α, ε, ζ: in `IsZKCPArgWith R A B E Sim α ε ζ` (ZKCP/Gen.lean): a natural number B, a number α
      and two functions ε, ζ of two natural numbers; its fields: `HasCompletenessError R A B α`,
      `HasIndexBindingWith R A E ε`, `HasIndexPrivacyWith R A B Sim ζ`
  nC, nP, nV: natural numbers; in `Spec.stateFirst` (Rom/StateFirst.lean) with `CostBoundAt (wCh C)`
      (Rom/OverOneN.lean): on every path, whatever the answers and the coins, the weights w o q of
      the queries add up to at most t; `wCh`: the weight of a query: 1 at a chain oracle, 0 at an
      unchanged one
  `mixClose`: the theorem `mixClose : Spec.mixClose` (Rom/StateFirstClose.lean; stated in
      Rom/StateFirstMix.lean)

What is not said. The limits in the head of Rom/StateFirst.lean, among them: nothing on one oracle f
(there: (1)); nothing on "only the blocks that a round needs" (there: (2)); the prices are coarse
(there: (4)). That a given scheme meets the hypotheses (the bounds at chain oracles, PlainOnly,
HidFree) is not shown here.
-/
import Rom.StateFirstClose
import Rom.StateFirstCB
import Rom.StateFirstPriv

set_option autoImplicit false

namespace Rom
open ZKCP

/-- `Spec.stateFirst`. -/
theorem stateFirst :
    Spec.stateFirst := fun _ _ _ _ _ _ _ _ _ _ R A B E Sim α ε ζ nC nP nV hC hP hV hE hH h =>
  ⟨completeness_stateFirst R A B α nC nP nV hC hP hV h.completeness,
    binding_stateFirst R A E ε nV hV hE h.indexBinding,
    privacy_stateFirst mixClose R A B Sim ζ nC nP hC hP hH h.indexPrivacy⟩

end Rom
