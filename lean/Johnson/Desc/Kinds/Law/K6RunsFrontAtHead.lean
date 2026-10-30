-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6RunsFrontAtHead.lean: AT THE HEAD's LINK OF THE FIRST CHAIN, UNDER THE ONE
HYPOTHESIS h, FOUR OF THE SEVEN RUNS OF CLAIMS THAT ARE NOT THE OUTPUT HEAD's OWN LEAVE WHAT THE
HEAD HAS HEARD AS IT WAS, AND, WHERE THE LEDGER HAS ITS SIZES, HAND ON A LATER ONE. One theorem ON
THE VERIFIER's TEXT, over the library and Law/K6RunsFront.lean; no prover is in this file, and no
goal is stated.

  `four_runs_at_head`   **`four_runs_frontLater` (Law/K6RunsFront.lean) with its premise paid**: the
                    runs that stand at (8, "the merge"), (5, "K8.equations"), (2, "guests") and (7,
                    "guests") of link 24 give `FrontLater`
                    (Johnson/Desc/First/Link/Law/K6HeardAtBatch.lean)

Who pays the premise. `HeadTies` at a seated link of the sort "head": the library's
`LPFK9.head_ties_at` (Johnson/LPFK9R/TiesWholeAt.lean), called as the library's own
`LPFK9.ties_head_mg` (SortTiesAtMg.lean there) calls it: the sort by `IM.subs_scope`
(Johnson/IMR/LinkSeat.lean), the number of the array of the head's reads by `P4.k6States_at_seat`
(Johnson/P4SR/K6StatesAtChain.lean). That lemma stands at the link that the closed constant's data
name; this one at the chain's own link 24, which is what a caller on the honest side has in hand.

Limits. CONDITIONAL on h : `P5J.AtMgA`: THE FULL SIZE AND THE FORMAT's EARLIER HASH ALONE. (The
library has a member of that hypothesis under four premises on the three public files:
`P5J.head_exists_at_name`, Johnson/P5J/HeadExistsAtName.lean; nothing here calls that.) IMPLICATIONS
FROM A RUN's RETURN. NOTHING ON THE LOOKUPS' THREE RUNS, (2, "objects"), (2, "planes") and (7,
"objects"). Nothing on the output head's own four runs. Nothing on what a run claims. (Where the
order's eleven entries stand: Law/K6RunsFront.lean's head.)
Nothing on any property.

-/
import Johnson.Desc.Kinds.Law.K6RunsFront
import Johnson.LPFK9R.TiesWholeAt
import Johnson.P4SR.K6StatesAtChain
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.Five
open VerifiableInference.Desc (Chain Claim Link)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.LinkJoin (At FrontLater)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE FOUR RUNS AT LINK 24 OF THE FIRST CHAIN, UNDER h.** -/
theorem four_runs_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Lk : Link S Claim}
    (hlk : cF.links[24]? = some Lk) :
    ∀ o ∈ [(8, "the merge"), (5, "K8.equations"), (2, "guests"), (7, "guests")],
      ∀ run, At Lk o run → ∀ m t z, run m t = .ok z → FrontLater t z.2 := by
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  have hl := IM.subs_scope h.scope h.reads O 24 (by omega)
  have hs : IM.subAt 24 = .head := rfl
  rw [hs] at hl
  obtain ⟨-, iU3, -, hU, -, -⟩ := P4.k6States_at_seat h.scope h.reads O
  obtain ⟨Lk', X, e, -, T⟩ := LPFK9.head_ties_at O.made O.places O.chain 24 hl iU3 hU
  obtain rfl : Lk' = Lk := Option.some.inj (e.symm.trans hlk)
  exact four_runs_frontLater T

end VerifiableInference.Desc.Kinds.Head.Law.Five

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Five.four_runs_at_head
