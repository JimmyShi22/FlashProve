-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/H2K5R/JoinAtOpen.lean: KIND K5: WHAT find? FINDS UNDER "join" AT THE
SEATED ATTENTION LINK's HEARING BLOCK 2: the lookup's own run joinRun, at the seat of the calls whose
claims K3Lot.ofForm makes, at the kind's keys: THE RUN ITSELF, no guard around it. A join of
theorems that lie.

Why. The lookup argument's files' law on the run "join" has a premise "hfind": find? by that name,
at what the link's block states, gives (nm, joinRun seat keys) at a plain maker of claims. The run
is stated by K5's sub-protocol, so the payers are K5's files.

How. K05_states_of_open (Johnson/H2K5R/SeatedStates.lean): block 2 states the kind's four runs, each
behind the seat's guard · find_guarded (Johnson/Desc/First/Look/K03States.lean): find? goes
through the guard · find_join (Johnson/Desc/First/Att/K05JoinThereAt.lean) · join_runN_eq
(Johnson/Desc/First/Att/K05JoinRunN.lean): made of forms and then typed, the run is the lookup's own
· guardRun_eq, pass_of_puts (Johnson/Desc/First/Look/K03StatesRaw.lean) with join_puts
(Johnson/Top/H/Keep/RunsPutFork.lean) and k03_atS2_calls: the guard is idle on it.

Main name:
  `K05_join_of_open`: **from an opening, at every o, where the proof covers attention, for g below
    the number of groups with plan a.**
PREMISES: the opening O · h4 · hg · ha. IDLE below profile 4 and wherever onlineDescription o refuses.
NO LETTER IS LOOSE: Lk is given with its equation.
No soundness of the protocol is claimed.
Nothing is claimed on completeness or hiding.

-/
import Johnson.H2K5R.SeatedStates
import Johnson.Desc.First.Look.K03StatesRaw
import Johnson.Desc.First.Att.K05JoinThereAt
import Johnson.Desc.First.Att.K05JoinRunN

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Claim Block Chain Link FileDescription)
open VerifiableInference.Desc.K9 (statesOfLink)
open VerifiableInference.OnPublicFiles (find_guarded guardRun_eq pass_of_puts join_puts k03_atS2_calls)

/-- **"join" AT THE SEATED LINK, FROM AN OPENING: THE RUN ITSELF.** -/
theorem K05_join_of_open {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block First.S Claim)}
    {c : Chain First.S Claim} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (O : IM.Open o pol lay KL F Z Bs base c A B) (h4 : Bs.G₀.W.p4 = true) {g : ℕ}
    (hg : g < Bs.G₀.W.NGr) {a : Attention.Plan} (ha : Bs.G₀.W.A[g]? = some a) :
    ∃ Lk : Link First.S Claim, c.links[2 * g + 1]? = some Lk ∧
      (statesOfLink Lk 2).find? (fun r => r.1 == "join") =
        some ("join", K3.joinRun (K3.seatCalls K3Lot.ofForm) (keysOfO a)) := by
  obtain ⟨Lk, -, e1, -, hL⟩ := K05_states_of_open O h4 hg ha
  refine ⟨Lk, e1, ?_⟩
  rw [hL, find_guarded, find_join, join_runN_eq]
  show some ("join", IM.guardRun ProofFile.sameReply
    (K3.joinRun (K3.seatCalls K3Lot.ofForm) (keysOfO a))) = _
  rw [guardRun_eq _ _ (pass_of_puts (join_puts _ k03_atS2_calls _))]

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_join_of_open
