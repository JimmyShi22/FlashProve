-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6LookRunsFront.lean: THE LOOKUPS' THREE RUNS OF CLAIMS OF THE HEAD's SEGMENT
LEAVE WHAT THE HEAD HAS HEARD AS IT WAS, AND HAND ON A LATER LEDGER. Lemmas ON THE VERIFIER's TEXT,
over the library alone, by calls; no prover is in this file, and no goal is stated.

  `frontLater_of_puts`   a state that is the state in front with another ledger put, that ledger a
                    later one: `FrontLater` (Johnson/Desc/First/Link/Law/K6HeardAtBatch.lean)
  `objects_frontLater`, `planes_frontLater`   the kind's runs "objects" (at either seat) and
                    "planes" (at the calls' seat) give it, from the state at which the run is called
                    to the state that it hands back
  `look_runs_at_head`   **so do the runs that stand at (2, "objects"), (2, "planes") and (7,
                    "objects") of link 24 of the first chain, under the one hypothesis h**

Who pays what: ALL OF IT IS THE LIBRARY's: every proof here is calls. That a return of each run is
the state with another ledger put: `objects_puts`, `planes_puts`
(Johnson/Top/H/Keep/RunsPutFork.lean). That this ledger is a later one: `objects_later`
(Johnson/Top/H/K3LedgerKeeps.lean) and `planes_frame` (K3Steps.lean there), at `fits_at`
(Johnson/Desc/First/Link/Law/SortK3Objects.lean). Which run stands at each entry: `at_objects_is`
(SortK3Objects.lean), `at_planes_is` (SortK3Planes.lean there); the calling kind's readers at the
head's link: `readersAt_head` (SortK3PlanesRun.lean there), `P4.head_24`
(Johnson/P4SR/PlanesAtSeat.lean), `P4.k6States_at_seat` (K6StatesAtChain.lean there). That putting a
ledger leaves the rest: `putFork_front` (Link/Law/FrontStays.lean).

Limits. IMPLICATIONS FROM A RUN's RETURN: nothing on what a run claims. The last lemma is
CONDITIONAL on h : `P5J.AtMgA`: THE FULL SIZE AND THE FORMAT's EARLIER HASH ALONE. (The library has
a member of that hypothesis under four premises on the three public files:
`P5J.head_exists_at_name`, Johnson/P5J/HeadExistsAtName.lean; nothing here calls that.) Nothing on
the segment's eight other runs (four of these: Law/K6RunsFront.lean, Law/K6RunsFrontAtHead.lean).
Nothing on the batching's own sample.
Nothing on any property.

-/
import Johnson.Desc.First.Link.Law.K6HeardAtBatch
import Johnson.Desc.First.Link.Law.SortK3PlanesRun
import Johnson.Top.H.K3Steps
import Johnson.Top.H.Keep.RunsPutFork
import Johnson.P4SR.PlanesAtSeat
import Johnson.P4SR.K6StatesAtChain
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.Five
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Chain Claim Link)
open VerifiableInference.Desc.First (S LaterS)
open VerifiableInference.Desc.K3 (Readers planesRun seatCalls)
open VerifiableInference.Desc.LinkJoin (At FrontLater putFork_front laterZ_of_laterS)
open VerifiableInference.OnPublicFiles (objectsRun seatOf objects_puts planes_puts objects_later
        planes_frame fits_at atS2_seatOf k03_atS2_calls at_objects_is at_planes_is readersAt_head)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

/-- A state that is the state in front with another ledger put, that ledger a later one. -/
theorem frontLater_of_puts {s s' : S} (hp : ∃ G : Fork, s' = s.putFork G) (hL : LaterS s s') :
    FrontLater s s' := by
  obtain ⟨G, rfl⟩ := hp
  exact ⟨putFork_front s G, laterZ_of_laterS hL⟩

/-- The run "objects", at the calls' seat (d = false) or the digits' (d = true). -/
theorem objects_frontLater (d : Bool) (n : Nat) (s : S) (cl : List Claim) (s' : S)
    (hrun : objectsRun (seatOf K3Lot.ofForm d) n s = .ok (cl, s')) : FrontLater s s' := by
  refine frontLater_of_puts (objects_puts _ (atS2_seatOf d) n s cl s' hrun) fun F hF => ?_
  obtain ⟨G, hG, -, hL⟩ := objects_later _ _ (fits_at d)
    (((atS2_seatOf d).fork s).trans hF) hrun
  exact ⟨G, ((atS2_seatOf d).fork s').symm.trans hG, hL⟩

/-- The run "planes", at the calls' seat. -/
theorem planes_frontLater (lm : Nat) (r : Readers S) (n : Nat) (s : S) (cl : List Claim) (s' : S)
    (hrun : planesRun (seatCalls K3Lot.ofForm) lm r n s = .ok (cl, s')) : FrontLater s s' := by
  refine frontLater_of_puts (planes_puts _ k03_atS2_calls lm r n s cl s' hrun) fun F hF => ?_
  obtain ⟨G, hG, hL⟩ := (planes_frame (seatCalls K3Lot.ofForm) (fits_at false).markFork
    (fun _ => (none : Option Unit)) (fun _ _ _ _ => rfl) lm r n s s' cl hrun).2 F
    ((k03_atS2_calls.fork s).trans hF)
  exact ⟨G, (k03_atS2_calls.fork s').symm.trans hG, hL⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE LOOKUPS' THREE RUNS AT LINK 24 OF THE FIRST CHAIN, UNDER h.** -/
theorem look_runs_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Lk : Link S Claim}
    (hlk : cF.links[24]? = some Lk) :
    ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")],
      ∀ run, At Lk o run → ∀ m t z, run m t = .ok z → FrontLater t z.2 := by
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  have hm : 24 < 25 := by omega
  obtain ⟨-, iU3, -, hU, -, -⟩ := P4.k6States_at_seat h.scope h.reads O
  have hr := readersAt_head (P4.head_24 h.scope h.reads O) hU
  intro o ho run hrn m t z hz
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · rw [at_objects_is h.scope h.reads O hm false hlk hrn] at hz
    exact objects_frontLater false m t z.1 z.2 hz
  · obtain ⟨p, -, e⟩ := at_planes_is h.scope h.reads O hm hlk hr hrn
    rw [e] at hz
    exact planes_frontLater p.lm _ m t z.1 z.2 hz
  · rw [at_objects_is h.scope h.reads O hm true hlk hrn] at hz
    exact objects_frontLater true m t z.1 z.2 hz

end VerifiableInference.Desc.Kinds.Head.Law.Five

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Five.frontLater_of_puts
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Five.objects_frontLater
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Five.planes_frontLater
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Five.look_runs_at_head
