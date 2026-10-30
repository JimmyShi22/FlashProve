-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/GoodLaw/Rides/OwnShares.lean: WHAT THE OUTPUT HEAD's OWN FOUR RUNS
OF CLAIMS GIVE AT THE HEAD's LINK, AT A STATE WITH THE INVARIANT `K6GoodAt`
(Honest/K6/GoodLaw/Runs.lean): EVERY SLOT OF THE WINDOW BUT THE LAST IS LIVE IN ONE OF THEM; EVERY
CLAIM OF THEIRS TAKES ITS OWN NUMBER; FROM THE SLOT BEHIND THE WINDOW ON THEY NAME NO SLOT. Lemmas
at link 24 of the first chain, under the one hypothesis h. None of the library's goals.

  `order_at_head`   the order of link 24 is the head's eleven entries
  `own_live_at_head`   **live**: for b ≤ j and j + 1 < e there is an entry of the link's order,
                    (3, "norm") or (3, "logits"), whose run, called at a state with the invariant,
                    returns claims in which slot j is live
  `own_plain_at_head`   **plain**: at the four entries, at every slot; no invariant is asked
  `own_unnamed_at_head`   **unnamed**: at the four entries, at every slot j with e ≤ j

What for. These are the shares of the sub-protocol "the output head's own rounds" in three clauses
that a gatherer's law on the head's segment asks of a joint invariant: "live" at the slots of our
window, "plain" at our four entries, "unnamed" at the merge's slot at our four entries, where that
slot lies behind the window (e ≤ j: a premise here). The fourth, "handed on": Rides/AllRuns.lean.
`liveAt`, `plainAt`, `unnamedAt` are the library's (Johnson/Desc/K9/Honest/SlotsLive.lean).

Who pays what. At the kind's bare runs: `run_live`, `run_plain`, `run_unnamed`, `join_plain`,
`join_unnamed` (Runs.lean). That the link's own runs at number 3 only reject more than these: the
library's ties, fields tK6 and tJoin of `HeadTies` (Johnson/Desc/First/Link/Law/PayHead.lean), at
the invariant's letters by `ties_at_head` (Johnson/Desc/Kinds/Law/K6AllRunsFront.lean). (Our
`runs_under_at_head`, GoodLaw/RunsUnder.lean, says the like, at every name; it is not called: so
this file stands over neither that file nor Honest/K9/GatherYes.lean beneath it. It still stands
over Runs.lean, and through it over Honest/K9/GatherFold.lean, among other files that are not in the
library.) The order: the library's `LPFK9.k09_sits` (Johnson/LPFK9R/Sits.lean). A neighbour: these
are the shares at number 3 of the last three clauses of `clauses_four` (Runs.lean), freed of its
premises on the other entries, which nobody pays here; the proofs follow its lines.

Limits. IMPLICATIONS: THAT THE INVARIANT STANDS AT ANY STATE IS NOT SHOWN HERE. OUR WINDOW AND OUR
FOUR ENTRIES ALONE: "live" at the other slots and "unnamed" at the other entries are the other
sub-protocols'. THE WINDOW's LAST SLOT, e - 1, IS NOT SHOWN LIVE HERE: it is the slot of the value
that the merge takes (`sV_of_good`, GoodLaw/Window.lean). THAT THE MERGE's SLOT LIES BEHIND THE
WINDOW IS A PREMISE. THE FULL SIZE AND THE FORMAT's EARLIER HASH ALONE, as h : `P5J.AtMgA`. b and e,
the window's two ends, are letters.
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K6.GoodLaw.Runs
import Johnson.Desc.Kinds.Law.K6AllRunsFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6.GoodLaw
open VerifiableInference.Desc (Chain Claim Link)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head (parOf)
open VerifiableInference.Desc.Kinds.Head.Law (workOf)
open VerifiableInference.Desc.Kinds.Head.Law.Five (ties_at_head)
open VerifiableInference.Desc.K9H (liveAt plainAt unnamedAt)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The order of link 24 is the head's eleven entries. -/
theorem order_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Lk : Link S Claim}
    (hlk : cF.links[24]? = some Lk) :
    Lk.order = VerifiableInference.Desc.First.orderOf .head := by
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  obtain ⟨L, p, Q, -, -, hs⟩ := LPFK9.k09_sits h.scope h.reads O 24 (by omega)
  obtain rfl : Lk = L := Option.some.inj (hlk.symm.trans hs.link)
  exact hs.order

/-- **LIVE, IN OUR WINDOW.** b and e are letters. -/
theorem own_live_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Lk : Link S Claim}
    (hlk : cF.links[24]? = some Lk) (b e j : Nat) (h1 : b ≤ j) (h2 : j + 1 < e) :
    ∃ o ∈ Lk.order, ∀ run, VerifiableInference.Desc.LinkJoin.At Lk o run → ∀ m t z,
      K6GoodAt (P5J.At.X Zp).hS (Head.Law.readsOf (P5J.At.X Zp))
        (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) b e t →
      run m t = .ok z → liveAt z.1 j = true := by
  have ord := order_at_head h hlk
  obtain ⟨l, nU, T⟩ := ties_at_head h hlk
  by_cases hl : j < b + headBeforeLogits (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp)))
  · refine ⟨(3, "norm"), ?_, fun run hr m t z k hz => ?_⟩
    · rw [ord]
      simp [VerifiableInference.Desc.First.orderOf, VerifiableInference.Desc.First.orderCuts]
    · obtain ⟨r0, hr0, U⟩ := T.tK6 "norm" (by simp) run hr
      exact run_live _ _ _ l 4 b e "norm" r0 hr0 j (Or.inl ⟨rfl, h1, hl⟩) m t (z.1, z.2) k
        (U m t z.1 z.2 hz)
  · refine ⟨(3, "logits"), ?_, fun run hr m t z k hz => ?_⟩
    · rw [ord]
      simp [VerifiableInference.Desc.First.orderOf, VerifiableInference.Desc.First.orderCuts]
    · obtain ⟨r0, hr0, U⟩ := T.tK6 "logits" (by simp) run hr
      exact run_live _ _ _ l 4 b e "logits" r0 hr0 j (Or.inr ⟨rfl, by omega, h2⟩) m t (z.1, z.2) k
        (U m t z.1 z.2 hz)

/-- **PLAIN, AT OUR FOUR ENTRIES.** No invariant is asked. -/
theorem own_plain_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Lk : Link S Claim}
    (hlk : cF.links[24]? = some Lk) :
    ∀ o ∈ [(3, "norm"), (3, "join"), (3, "policy"), (3, "logits")],
      ∀ run, VerifiableInference.Desc.LinkJoin.At Lk o run → ∀ m t z,
        run m t = .ok z → ∀ j, plainAt z.1 j = true := by
  obtain ⟨l, nU, T⟩ := ties_at_head h hlk
  have three : ∀ name ∈ ["norm", "policy", "logits"], ∀ run,
      VerifiableInference.Desc.LinkJoin.At Lk (3, name) run → ∀ m t z,
        run m t = .ok z → ∀ j, plainAt z.1 j = true := by
    intro name hn run hr m t z hz j
    obtain ⟨r0, hr0, U⟩ := T.tK6 name hn run hr
    exact run_plain _ _ _ l 4 name r0 hr0 j m t (z.1, z.2) (U m t z.1 z.2 hz)
  intro o ho run hr m t z hz j
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl
  · exact three "norm" (by simp) run hr m t z hz j
  · exact join_plain _ j m t (z.1, z.2) (T.tJoin run hr m t z.1 z.2 hz)
  · exact three "policy" (by simp) run hr m t z hz j
  · exact three "logits" (by simp) run hr m t z hz j

/-- **UNNAMED, AT OUR FOUR ENTRIES**, from the slot behind the window on. -/
theorem own_unnamed_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Lk : Link S Claim}
    (hlk : cF.links[24]? = some Lk) (b e j : Nat) (hj : e ≤ j) :
    ∀ o ∈ [(3, "norm"), (3, "join"), (3, "policy"), (3, "logits")],
      ∀ run, VerifiableInference.Desc.LinkJoin.At Lk o run → ∀ m t z,
        K6GoodAt (P5J.At.X Zp).hS (Head.Law.readsOf (P5J.At.X Zp))
          (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) b e t →
        run m t = .ok z → unnamedAt z.1 j = true := by
  obtain ⟨l, nU, T⟩ := ties_at_head h hlk
  have three : ∀ name ∈ ["norm", "policy", "logits"], ∀ run,
      VerifiableInference.Desc.LinkJoin.At Lk (3, name) run → ∀ m t z,
        K6GoodAt (P5J.At.X Zp).hS (Head.Law.readsOf (P5J.At.X Zp))
          (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) b e t →
        run m t = .ok z → unnamedAt z.1 j = true := by
    intro name hn run hr m t z k hz
    obtain ⟨r0, hr0, U⟩ := T.tK6 name hn run hr
    exact run_unnamed _ _ _ l 4 b e name r0 hr0 j (Or.inr hj) m t (z.1, z.2) k (U m t z.1 z.2 hz)
  intro o ho run hr m t z k hz
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl
  · exact three "norm" (by simp) run hr m t z k hz
  · exact join_unnamed _ _ _ b e j hj m t (z.1, z.2) k (T.tJoin run hr m t z.1 z.2 hz)
  · exact three "policy" (by simp) run hr m t z k hz
  · exact three "logits" (by simp) run hr m t z k hz

#print axioms order_at_head
#print axioms own_live_at_head
#print axioms own_plain_at_head
#print axioms own_unnamed_at_head

end ProofFile.Honest.K6.GoodLaw
