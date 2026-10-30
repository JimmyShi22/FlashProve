-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/LookRest.lean: the honest side of the kind "lookup"
(K3): two facts on what the lookup has heard that the layers' own kind asks and that the lookup's
promise behind does not include, from the member's accepting step alone: nothing is asked of the
state in front. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: zx, zk and e are fields of the heard structure: the
lookup's point, the calls' key points and the weights of the calls. `toHeard`
(Johnson/Desc/First/Look/K3LookupGeneral.lean) makes the heard structure. "The step says yes" is the
library's `StepYes` (Johnson/Top/H0/Walk/Reach.lean).

What is shown.
  `e_size`: there are as many weights of calls as the heard shape has calls.
  `merged_of_last`: wherever the last k coordinates of zx can be read, those of every call's key
    point can, and all are the same. There is no hypothesis on k (helper: `size_of_last`).
  `look_rest_at`: both, at the state behind an accepting step of the description's own member at a
    lookup on the calls, the step in the form `StepYes`.

Hypotheses that remain.
  In `e_size` and `merged_of_last`: `hg` alone: `toHeard` returns. In `size_of_last`: `h`: `lastOf`
    returns.
  In `look_rest_at`:
  `O`: the description returns (`IM.Open`, Johnson/IMR/SeatOpen.lean).
  `hs`, `hd`: s is a site of the public part (`lookSites Z`); it is on the calls.
  `hb`, `hbs`: lot is one of the lookups' own sub-protocols (`(K3Lot.lot Z).blocks`); it stands at
    the site's place.
  Inside the statement, without letters: the member blk is in the first chain's flat list; it stands
    at that place; it passes its own test on the plan (planOk), a test on public data; its step says
    yes (`StepYes`).

Users. `look_rest_link` (Honest/K3/Law/Thread/AtLink.lean) calls `look_rest_at`.

Limits. Conditional on the hypotheses above. That the heard shape's number of calls is the number of
calls in the layout's list is a fact on the layout, which is not stated here. At a link that is no
layers' link `look_rest_at` says nothing. No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.MergedPoint
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes (E)
open OnBytes.Model (Fork lastOf cutLast)
open OnBytes.Model.Forest (Shape)
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn)
open VerifiableInference.Desc.K3 (HeardG toHeard)
open Johnson.Desc.First.Walk.Tied (StepYes)

local notation "FS" => VerifiableInference.Desc.First.S

/-- **There are as many weights of calls as the heard shape has calls.** Conditional on the return
of `toHeard`. -/
theorem e_size {h : Shape} {g : HeardG} {H : OnBytes.Model.Forest.Heard}
    (hg : toHeard h g = some H) : H.e.size = H.shape.NC := by
  unfold toHeard at hg
  split at hg
  · simp only at hg
    split at hg
    · cases hg
      simp
    · cases hg
  · cases hg

/-- Where the last k coordinates of a point can be read, the point has k. -/
theorem size_of_last {z Zp : Array E} {k : Nat} (h : (lastOf z k).toOption = some Zp) :
    k ≤ z.size := by
  by_cases hk : k > z.size
  · unfold lastOf cutLast at h
    rw [if_pos hk] at h
    exact nomatch h
  · omega

/-- **Wherever the last k coordinates of zx can be read, those of every call's key point can, and
all are the same.** Conditional on the return of `toHeard`. -/
theorem merged_of_last {h : Shape} {g : HeardG} {H : OnBytes.Model.Forest.Heard}
    (hg : toHeard h g = some H) (k : Nat) :
    ∀ Zp, (lastOf H.zx k).toOption = some Zp →
      ∃ ends, (H.zk.mapM fun zk => (lastOf zk k).toOption) = some ends ∧
        ends.all (· == Zp) = true := by
  intro Zp hZ
  obtain ⟨Z', ends, h1, h2, h3⟩ := merged_point hg k (size_of_last hZ)
  obtain rfl : Z' = Zp := Option.some.inj (h1.symm.trans hZ)
  exact ⟨ends, h2, h3⟩

/-- **Both, behind an accepting step of the description's own member at a lookup on the calls.**
Conditional on the hypotheses that the head of this file lists; nothing is asked of the state in
front. No instance of these hypotheses is exhibited in this file. -/
theorem look_rest_at (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
    (hs : s ∈ lookSites Z) (hd : s.digits = false) (lot : Block FS ProofFile.Cl)
    (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : lot.place = s.at_.place) :
    ∀ blk ∈ ch.blocksInOrder, blk.place = lot.place → blk.planOk = true →
      ∀ (ft : Nat) (s₀ s' : FS), StepYes ft blk s₀ s' →
        ∀ a fo, s'.here = .lay a → a.fo = some fo →
          (∀ k Zp, (lastOf fo.zx k).toOption = some Zp →
            ∃ ends, (fo.zk.mapM fun zk => (lastOf zk k).toOption) = some ends ∧
              ends.all (· == Zp) = true) ∧
          fo.e.size = fo.shape.NC := by
  intro blk hm hmp hpk ft s₀ s' ⟨R, c, _, hstep⟩ a fo ha hfo
  obtain ⟨F, H, G, _, hv, hput⟩ := member_back_fo o pol lay KL Fd Z Bs base ch A B O s hs hd lot
    blk hb hbs hm hmp hpk ft s₀ s' _ R c hstep
  obtain rfl : H = fo := Option.some.inj ((hput a ha).1.symm.trans hfo)
  have hs' := hs
  unfold lookSites at hs'
  obtain ⟨x, _, hsx⟩ := List.mem_filterMap.1 hs'
  obtain ⟨_, f2, _⟩ := site_facts _ _ x s hsx
  obtain ⟨g, _, hH⟩ := hearVia_back f2 hv
  exact ⟨fun k Zp hZ => merged_of_last hH k Zp hZ, e_size hH⟩

#print axioms ProofFile.Honest.K3.Law.AtThr.e_size
#print axioms ProofFile.Honest.K3.Law.AtThr.size_of_last
#print axioms ProofFile.Honest.K3.Law.AtThr.merged_of_last
#print axioms ProofFile.Honest.K3.Law.AtThr.look_rest_at

end ProofFile.Honest.K3.Law.AtThr
