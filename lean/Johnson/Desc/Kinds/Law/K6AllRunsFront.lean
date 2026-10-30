-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6AllRunsFront.lean: EVERY RUN OF CLAIMS THAT THE ORDER OF THE HEAD's LINK
NAMES LEAVES WHAT THE HEAD HAS HEARD AS IT WAS, AND, WHERE THE LEDGER HAS ITS SIZES, HANDS ON A
LATER ONE. Lemmas ON THE VERIFIER's TEXT, over the library and three files beside this one; no
prover is in this file, and no goal is stated.

  `ties_at_head`   link 24 of the first chain has the library's ties `HeadTies`, at the letters of
                    the public part `P5J.At.X Zp`: its shape, `readsOf`, `workOf`
  `own_runs_frontLater`   at a link with these ties the output head's own four runs, (3, "norm"),
                    (3, "join"), (3, "policy"), (3, "logits"), give `FrontLater`
                    (Johnson/Desc/First/Link/Law/K6HeardAtBatch.lean)
  `all_runs_at_head`   **so does every run that the order of link 24 names, under the one
                    hypothesis h**

Who pays what. The own three leave the state as it is: `k6_same`; "join" puts the ledger with one
owed claim marked: `k6_join` (both Law/HeadRunsCarry.lean), `OnBytes.PscRun.paid_later`
(OnBytes/Tie/Pv/Psc/PscLater.lean), `frontLater_of_puts` (Law/K6LookRunsFront.lean). Which run
stands at these four entries: the ties' fields tK6 and tJoin
(Johnson/Desc/First/Link/Law/PayHead.lean). The ties: `LPFK9.head_ties_at`
(Johnson/LPFK9R/TiesWholeAt.lean), which hands them at the opening's own letters (so does
`LPFK9.ties_head_mg`, SortTiesAtMg.lean there: the library's two theorems that end in `HeadTies`);
that these are the public part's: the library's `IM.Open.W` (Johnson/IMR/SeatOpen.lean), `readsOf`
by its text, `workOf` by unfolding (`work_is`, Law/K6StateAtHead.lean). The seven other entries:
`four_runs_at_head` (Law/K6RunsFrontAtHead.lean), `look_runs_at_head` (Law/K6LookRunsFront.lean).
That the link's order is the head's eleven entries: `LPFK9.k09_sits` (Johnson/LPFK9R/Sits.lean),
`order_head` (Link/Law/LinkJoinPay.lean). The proof of `ties_at_head` repeats seven lines of
`four_runs_at_head`'s, five of which follow the library's `LPFK9.ties_head_mg`
(Johnson/LPFK9R/SortTiesAtMg.lean).

Limits. IMPLICATIONS FROM A RUN's RETURN: nothing on what a run claims. RUN BY RUN: no lemma here
walks a gatherer through the order. CONDITIONAL on h : `P5J.AtMgA`: THE FULL SIZE AND THE FORMAT's
EARLIER HASH ALONE. (The library has a member of that hypothesis under four premises on the three
public files: `P5J.head_exists_at_name`, Johnson/P5J/HeadExistsAtName.lean; nothing here calls
that.) Nothing on the batching's own sample.
Nothing on any property.

-/
import Johnson.Desc.Kinds.Law.K6RunsFrontAtHead
import Johnson.Desc.Kinds.Law.K6LookRunsFront
import Johnson.Desc.Kinds.Law.HeadRunsCarry
import Johnson.Desc.Kinds.Law.K6StateAtHead
import Johnson.LPFK9R.Sits
import Johnson.Desc.First.Link.Law.LinkJoinPay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.Five
open VerifiableInference.Desc (Chain Claim Link)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.LinkJoin (At FrontLater HeadTies laterZ_refl order_head)
open VerifiableInference.Desc.Kinds.Head (parOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

/-- At a link with the library's ties the output head's own four runs give `FrontLater`. -/
theorem own_runs_frontLater {L : Link S Claim} {h : OnBytes.Model.Head.Shape} {iU3 l piece : Nat}
    {p : Par} {nU : Array Nat} (T : HeadTies L h iU3 l piece p nU) :
    ∀ o ∈ [(3, "norm"), (3, "join"), (3, "policy"), (3, "logits")],
      ∀ run, At L o run → ∀ m t z, run m t = .ok z → FrontLater t z.2 := by
  have three : ∀ name ∈ ["norm", "policy", "logits"], ∀ run, At L (3, name) run →
      ∀ m t z, run m t = .ok z → FrontLater t z.2 := by
    intro name hn run hr m t z hz
    obtain ⟨r0, hr0, U⟩ := T.tK6 name hn run hr
    have e : z.2 = t := k6_same h iU3 l piece p (name, r0) (lookup_mem _ _ _ hr0) m t (z.1, z.2)
      (U m t z.1 z.2 hz)
    rw [e]
    exact ⟨rfl, laterZ_refl t⟩
  intro o ho run hr m t z hz
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl
  · exact three "norm" (by simp) run hr m t z hz
  · obtain ⟨F, g, hF, -, e⟩ := k6_join _ m t (z.1, z.2) (T.tJoin run hr m t z.1 z.2 hz)
    have e' : z.2 = t.putFork (F.paid g.owedJoin) := e
    refine frontLater_of_puts ⟨_, e'⟩ fun F' hF' => ?_
    obtain rfl : F = F' := Option.some.inj (hF.symm.trans hF')
    exact ⟨_, by rw [e']; exact S.fork_putFork t F _ hF, OnBytes.PscRun.paid_later F _⟩
  · exact three "policy" (by simp) run hr m t z hz
  · exact three "logits" (by simp) run hr m t z hz

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Link 24 of the first chain has the library's ties, AT THE LETTERS OF THE PUBLIC PART
`P5J.At.X Zp`**: its shape, `readsOf`, `workOf`. -/
theorem ties_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Lk : Link S Claim}
    (hlk : cF.links[24]? = some Lk) :
    ∃ (l : Nat) (nU : Array Nat),
      HeadTies Lk (P5J.At.X Zp).hS (readsOf (P5J.At.X Zp)) l 4
        (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) nU := by
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  have hl := IM.subs_scope h.scope h.reads O 24 (by omega)
  have hs : IM.subAt 24 = .head := rfl
  rw [hs] at hl
  obtain ⟨-, iU3, -, hU, -, -⟩ := P4.k6States_at_seat h.scope h.reads O
  obtain ⟨Lk', X, e, -, T⟩ := LPFK9.head_ties_at O.made O.places O.chain 24 hl iU3 hU
  obtain rfl : Lk' = Lk := Option.some.inj (e.symm.trans hlk)
  have eU : readsOf Bs.G₀.W = iU3 := by
    unfold readsOf
    rw [hU]
    rfl
  have eW : Bs.G₀.W = P5J.At.X Zp := O.W
  rw [← eU, eW] at T
  exact ⟨_, _, T⟩

/-- **EVERY RUN THAT THE ORDER OF LINK 24 NAMES, UNDER h.** -/
theorem all_runs_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Lk : Link S Claim}
    (hlk : cF.links[24]? = some Lk) :
    ∀ o ∈ Lk.order, ∀ run, At Lk o run → ∀ m t z, run m t = .ok z → FrontLater t z.2 := by
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  obtain ⟨L, p, Q, -, -, hs⟩ := LPFK9.k09_sits h.scope h.reads O 24 (by omega)
  obtain rfl : Lk = L := Option.some.inj (hlk.symm.trans hs.link)
  have ord : Lk.order = VerifiableInference.Desc.First.orderOf .head := hs.order
  obtain ⟨_, _, T⟩ := ties_at_head h hlk
  have A := own_runs_frontLater T
  have B := four_runs_at_head h hlk
  have C := look_runs_at_head h hlk
  rw [ord, order_head]
  exact ⟨C _ (by simp), B _ (by simp), A _ (by simp), A _ (by simp), A _ (by simp), C _ (by simp),
    C _ (by simp), B _ (by simp), B _ (by simp), A _ (by simp), B _ (by simp)⟩

end VerifiableInference.Desc.Kinds.Head.Law.Five

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Five.own_runs_frontLater
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Five.ties_at_head
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Five.all_runs_at_head
