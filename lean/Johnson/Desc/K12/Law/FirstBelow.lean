-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.MasksFixed
import Johnson.Desc.K12.Law.AloneOk
import Johnson.Desc.K12.Law.FirstNe
import Fmt.Rules6Laws
/-
Johnson/Desc/K12/Law/FirstBelow.lean: THE ROW masks_fixed_word, THE OWN ARM: the members' trees stand in front of the test, UNDER A TEST ON THE PLAN in the place of MasksFixed.membersBelow's premise inj. Statements and proofs. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
Why. membersBelow (MasksFixed.lean) takes «no z = no D.fresh.t → z = D.fresh.t on D.ts». That premise is a clause on the plan in disguise: the field front leaves one door, a member of nums.first with the source «own», number free. Shut it on the plan and the premise falls.
Main names:
  firstNe p (FirstNe.lean): the test, with code: no tree of p.nums.first has the source «own», number free.
  MasksFixed.othersBelow: under firstNe, the two pins n2 | n3, the first clause of FirstOpensOwn and «the last of D.ts is D.fresh.t»: every place of D.ts but D.fresh.t has no z < base. It goes by the place's NUMBER in the list: a place that is not the last one's stands at an index below the last, and there the declared opening is one of nums.first. No premise that D.ts rises, or that no is one-to-one.
  MasksFixed.membersBelowOwn: THE SECOND CLAUSE OF FirstOpensOwn IN PLAIN LETTERS (∀ i, no (D.mems.get i).t < base), with Made.ts for «a member's place is in D.ts» and aloneOk for «it is not the mask's».
Limits: firstNe IS ASKED BY NO RUNNING TEXT. It has said true at the five proximity tests of both stored proofs, its control false at each (runs' words); at the test O of both it is a theorem by the kernel (MemberOMore.lean: the smaller). [By reading, untyped: where a file's description passes BookPlan's test that the places of the trees which a round opens rise strictly, the first switch's second round, which opens nums.first and then the own mask's tree, cannot name that tree twice: so firstNe should follow from the file's test on the plan.] The pins n2, n3 and the first clause (h1) are premises, as in MasksFixed.lean.
-/
set_option autoImplicit false
namespace H2K.Made
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.First

namespace MasksFixed
variable {p : P12}

/-- Every place of D.ts but the mask's has a number below the stretch's first. -/
theorem othersBelow (h : MasksFixed p) (ho : p.nums.ownMask = true) (hne : firstNe p = true)
    (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hs : p.nums.stages = a :: rest)
    (num : Fmt.TreeSource → Nat) (base : Nat) (n2 : ∀ n, n < p.nums.free → num (.own n) < base)
    (n3 : ∀ c n, (c + 1, n) ∈ p.before → num (.taken c n) < base) (D : Plain) (no : Nat → Nat)
    (hD : D.opens = opensOf p a.k) (h1 : D.opens.map (fun o => num o.2) = D.ts.map no)
    (hlast : D.ts.getLast? = some D.fresh.t) : ∀ z ∈ D.ts, z ≠ D.fresh.t → no z < base := by
  intro z hz hzne
  obtain ⟨a', b, rest', _, _, hs', _, _, hop⟩ := h.made
  obtain ⟨rfl, _⟩ := List.cons.inj (hs.symm.trans hs')
  obtain ⟨x, W, hx⟩ := h.own ho
  rw [hD, hop, hx] at h1
  have hlen : p.nums.first.length + 1 = D.ts.length := by
    simpa using congrArg List.length h1
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hz
  have hil : i < D.ts.length := (List.getElem?_eq_some_iff.1 hi).1
  have hnl : i ≠ D.ts.length - 1 := by
    intro e
    rw [List.getLast?_eq_getElem?, ← e, hi] at hlast
    exact hzne (Option.some.inj hlast)
  have hif : i < p.nums.first.length := by omega
  have e := congrArg (·[i]?) h1
  simp only [List.getElem?_map, hi, Option.map_some, List.getElem?_append_left hif,
    List.getElem?_eq_getElem hif] at e
  have e' : num (p.nums.first[i]).2 = no z := Option.some.inj e
  have hm : p.nums.first[i] ∈ p.nums.first := List.getElem_mem hif
  rw [← e']
  rcases h.front _ hm with hf | ⟨_, h2⟩
  · exact inFront_below num base n2 n3 _ hf
  · have := List.all_eq_true.1 hne _ hm
    exact absurd h2 (of_decide_eq_true this)

/-- The second clause of FirstOpensOwn, in plain letters. -/
theorem membersBelowOwn (h : MasksFixed p) (ho : p.nums.ownMask = true) (hne : firstNe p = true)
    (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hs : p.nums.stages = a :: rest)
    (num : Fmt.TreeSource → Nat) (base : Nat) (n2 : ∀ n, n < p.nums.free → num (.own n) < base)
    (n3 : ∀ c n, (c + 1, n) ∈ p.before → num (.taken c n) < base) (D : Plain) (no : Nat → Nat)
    (hD : D.opens = opensOf p a.k) (h1 : D.opens.map (fun o => num o.2) = D.ts.map no)
    (hlast : D.ts.getLast? = some D.fresh.t)
    (hts : D.ts = Fmt.listOf ((D.mems.map (·.t)) ++ [D.fresh.t])) (hal : aloneOk D = true) :
    ∀ i, no (D.mems.get i).t < base := by
  intro i
  have hm : D.mems.get i ∈ D.mems := List.get_mem _ _
  refine h.othersBelow ho hne a rest hs num base n2 n3 D no hD h1 hlast _ ?_ ?_
  · rw [hts, Fmt.listOf_mem]
    exact List.mem_append_left _ (List.mem_map.2 ⟨_, hm, rfl⟩)
  · have := List.all_eq_true.1 hal _ hm
    simpa using this

end MasksFixed

end H2K.Made

#print axioms H2K.Made.MasksFixed.othersBelow
#print axioms H2K.Made.MasksFixed.membersBelowOwn
