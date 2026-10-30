-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/KeptCountOf.lean: «THE KEPT MEMBERS' MAIN ROWS ADD UP TO rows.keptRows»
(the fourth of the four facts on the front that `hF_of_door` asks: hFr, HFOfDoor.lean; `keptCount`,
FrontAnswers.lean) FROM THE CLOSING's FILES' OWN FACT ON THE ROWS THAT A CLOSING LAYS
(`CarriedOk.keptRows`, Johnson/Desc/First/Close/Law/CarriedRows.lean). Theorems. No other file
turns.

  `keptCount_filter`: keptCount counts the main symbols at the places with the flag «kept».
  `keptCount_of`: rows.keptRows is the sum of f over the switch's list of kept members · nM w = f
    ‹the layout's member number w› at the kept places ⊢ keptCount rows.layout nM ‹all places› =
    rows.keptRows. By `switchKept_list` (Johnson/Top/H0/K2Hears/KeptNos.lean).
  `keptCount_link`: **at a switch that stands at a link: the closing's fact at the border's state's
    statement and rows · the kept members' numbers are below that statement's messages ⊢ hFr's
    fourth fact.** By `skel_old_link` (FrontSt.lean).
Limits. At a link alone. The closing's fact is a premise here (`closing_carried` has it at a yes of
the closing). Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.FrontSt
import Johnson.Desc.First.Link.Law.FrontAnswers
import Johnson.Top.H0.K2Hears.KeptNos

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice
open VerifiableInference.Desc.Own (keptNos switchKept_list)
open VerifiableInference.Desc.First.K2Caller (doorZ)

theorem keptCount_filter (L : GroupLayout) (nM : ℕ → ℕ) :
    ∀ ws : List ℕ, keptCount L nM ws = ((ws.filter fun w => L.kept.getD w false).map nM).sum
  | [] => rfl
  | w :: ws => by
    show (if L.kept.getD w false then nM w else 0) + keptCount L nM ws = _
    rw [keptCount_filter L nM ws]
    by_cases hk : L.kept.getD w false = true
    · rw [if_pos hk, List.filter_cons_of_pos (p := fun w => L.kept.getD w false) hk,
        List.map_cons, List.sum_cons]
    · rw [if_neg hk, List.filter_cons_of_neg (p := fun w => L.kept.getD w false) hk,
        Nat.zero_add]

theorem keptCount_of (rows : SingleRows) (nM f : ℕ → ℕ)
    (hc : rows.keptRows = ((switchKept rows).toList.map f).sum)
    (hf : ∀ w ∈ keptNos rows.layout, nM w = f (rows.layout.members.getD w 0)) :
    keptCount rows.layout nM (List.range rows.layout.members.size) = rows.keptRows := by
  rw [keptCount_filter, hc, switchKept_list, List.map_map]
  exact congrArg List.sum (List.map_congr_left hf)

/-- **hFr's FOURTH FACT, AT A LINK.** -/
theorem keptCount_link {Z : ProofFile.Pub} {m : ℕ} (hp : (ProofFile.pAtK2 Z m).stands = .link)
    {s' t : First.S} (hd : doorZ Z m s' = some t) {fx : _root_.Tw.K2.Front}
    (hf : First.K2.frontAt (ProofFile.pAtK2 Z m) t = some fx)
    (hc : s'.live.frame.rows.keptRows = ((switchKept s'.live.frame.rows).toList.map fun o =>
      ((s'.st.oracles[o]?).map (·.shape.mainRows)).getD 0).sum)
    (hlt : ∀ w ∈ keptNos s'.live.frame.rows.layout,
      s'.live.frame.rows.layout.members.getD w 0 < s'.st.oracles.size) :
    keptCount s'.live.frame.rows.layout
      (fun w => ((First.K2.skelOf fx).oracles.getD
        (s'.live.frame.rows.layout.members.getD w 0) default).shape.mainRows)
      (List.range s'.live.frame.rows.layout.members.size) = s'.live.frame.rows.keptRows := by
  refine keptCount_of _ _ _ hc fun w hw => ?_
  have h1 := hlt w hw
  show ((First.K2.skelOf fx).oracles.getD _ default).shape.mainRows = _
  rw [Array.getD_eq_getD_getElem?, skel_old_link hp hd hf h1, Array.getElem?_eq_getElem h1]
  rfl

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.keptCount_filter
#print axioms VerifiableInference.Desc.LinkJoin.keptCount_of
#print axioms VerifiableInference.Desc.LinkJoin.keptCount_link
