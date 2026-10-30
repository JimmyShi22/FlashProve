-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FrontStEnds.lean: FrontSt.lean's AND KeptCountOf.lean's THEOREMS
WHEREVER THE CODE SWITCH STANDS: at a link, at the head, at the finish. The front's statement
(`K2.skelOf fx`) has, at every number below the border's state's statement's oracle messages, that
statement's own message: so three of the four facts on the front that `hF_of_door` asks (hFr,
HFOfDoor.lean) come from the border's state at all three sorts of place. By calls. Theorems. No
other file turns.

  `front_st_head`, `front_st_finish`: the front that the text makes of a state t at the head | at
    the finish has t's own statement (by the text of `K2.frontAt`,
    Johnson/Top/H0/K2Hears/Long.lean).
  `skel_old_head`, `skel_old_finish`: as `skel_old_link`: the way in pushes a fresh group and no
    message (`headFrontQ_st`, Tw/K2C/FrontGroup.lean; `finishFrontQ_st`,
    Tw/K2C/FinFront.lean; `doorZ_head`, `doorZ_finish`, Walk/FrameCarryEnds.lean).
  `skel_old_door`: **WHEREVER THE SWITCH STANDS.** At the head: where the border's state does not
    stand at the head's link already.
  `doorReads_door`: `doorReads_link` | `_head` | `_finish`
    (Walk/FrameCarryFenceEnds.lean) as one: `hF_of_door`'s premise hD.
  `front_shapes_door`, `keptCount_door`: `front_shapes_link` and `keptCount_link` so.
Limits. At the head: the state in front must not stand at the head's link (the premise of
`doorReads_head` too). The book behind the sending (hFr's first) is not treated here
(`bookAt_of`, BookThere.lean, names no place). Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.KeptCountOf
import Johnson.Top.H0.Tw.K2C.FinFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice Johnson.G
open VerifiableInference.Desc.Own (keptNos)
open VerifiableInference.Desc.First.K2Caller (doorZ rest)
open _root_.Johnson.Desc.First.Walk.Tied (toOption_some doorZ_head doorZ_finish)

theorem front_st_head {p : First.K2.P2} (hp : p.stands = .head) {t : First.S}
    {fx : _root_.Tw.K2.Front} (h : First.K2.frontAt p t = some fx) : fx.st = t.st := by
  unfold First.K2.frontAt at h
  rw [hp] at h
  cases hh : t.here with
  | head a =>
    rw [hh] at h
    obtain ⟨G, _, rfl⟩ := Option.map_eq_some_iff.1 h
    rfl
  | _ => rw [hh] at h; cases h

theorem front_st_finish {p : First.K2.P2} (hp : p.stands = .finish) {t : First.S}
    {fx : _root_.Tw.K2.Front} (h : First.K2.frontAt p t = some fx) : fx.st = t.st := by
  unfold First.K2.frontAt at h
  rw [hp] at h
  cases hh : t.here with
  | fin a =>
    rw [hh] at h
    obtain ⟨G, _, rfl⟩ := Option.map_eq_some_iff.1 h
    rfl
  | _ => rw [hh] at h; cases h

theorem skel_old_head {Z : ProofFile.Pub} {m : ℕ} (hp : (ProofFile.pAtK2 Z m).stands = .head)
    {s' t : First.S} (hs : ∀ a, s'.here ≠ .head a) (hd : doorZ Z m s' = some t)
    {fx : _root_.Tw.K2.Front} (hf : First.K2.frontAt (ProofFile.pAtK2 Z m) t = some fx) {o : ℕ}
    (ho : o < s'.st.oracles.size) :
    (First.K2.skelOf fx).oracles[o]? = s'.st.oracles[o]? := by
  rw [doorZ_head hp hs] at hd
  have e1 := First.K2.headFrontQ_st (toOption_some hd)
  have e2 : fx.st.oracles = s'.st.oracles := by
    rw [front_st_head hp hf, e1, rest_st]
    rfl
  unfold First.K2.skelOf
  rw [stSent_old _ _ o (by rw [e2]; exact ho), e2]

theorem skel_old_finish {Z : ProofFile.Pub} {m : ℕ} (hp : (ProofFile.pAtK2 Z m).stands = .finish)
    {s' t : First.S} (hd : doorZ Z m s' = some t) {fx : _root_.Tw.K2.Front}
    (hf : First.K2.frontAt (ProofFile.pAtK2 Z m) t = some fx) {o : ℕ} (ho : o < s'.st.oracles.size) :
    (First.K2.skelOf fx).oracles[o]? = s'.st.oracles[o]? := by
  rw [doorZ_finish hp] at hd
  have e1 := First.K2.finishFrontQ_st (toOption_some hd)
  have e2 : fx.st.oracles = s'.st.oracles := by
    rw [front_st_finish hp hf, e1, rest_st]
    rfl
  unfold First.K2.skelOf
  rw [stSent_old _ _ o (by rw [e2]; exact ho), e2]

/-- **THE FRONT's STATEMENT HAS THE STATE's OWN MESSAGES, WHEREVER THE SWITCH STANDS.** -/
theorem skel_old_door {Z : ProofFile.Pub} {m : ℕ} {s' t : First.S}
    (hH : (ProofFile.pAtK2 Z m).stands = .head → ∀ a, s'.here ≠ .head a)
    (hd : doorZ Z m s' = some t) {fx : _root_.Tw.K2.Front}
    (hf : First.K2.frontAt (ProofFile.pAtK2 Z m) t = some fx) {o : ℕ} (ho : o < s'.st.oracles.size) :
    (First.K2.skelOf fx).oracles[o]? = s'.st.oracles[o]? := by
  cases hp : (ProofFile.pAtK2 Z m).stands with
  | link => exact skel_old_link hp hd hf ho
  | head => exact skel_old_head hp (hH hp) hd hf ho
  | finish => exact skel_old_finish hp hd hf ho

/-- The three `doorReads_*` laws on what the way in's answer reads, as one: `hF_of_door`'s hD. -/
theorem doorReads_door {Z : ProofFile.Pub} {m : ℕ} {s' : First.S}
    (hH : (ProofFile.pAtK2 Z m).stands = .head → ∀ a, s'.here ≠ .head a) (t : First.S)
    (hd : doorZ Z m s' = some t) :
    _root_.Johnson.Desc.First.Walk.Tied.DoorReads (ProofFile.pAtK2 Z m) s' t := by
  cases hp : (ProofFile.pAtK2 Z m).stands with
  | link => exact _root_.Johnson.Desc.First.Walk.Tied.doorReads_link hp hd
  | head => exact _root_.Johnson.Desc.First.Walk.Tied.doorReads_head hp (hH hp) hd
  | finish => exact _root_.Johnson.Desc.First.Walk.Tied.doorReads_finish hp hd

/-- **TWO OF hFr's FOUR FACTS, WHEREVER THE SWITCH STANDS.** -/
theorem front_shapes_door {Z : ProofFile.Pub} {m : ℕ} {s' t : First.S}
    (hH : (ProofFile.pAtK2 Z m).stands = .head → ∀ a, s'.here ≠ .head a)
    (hd : doorZ Z m s' = some t) {fx : _root_.Tw.K2.Front}
    (hf : First.K2.frontAt (ProofFile.pAtK2 Z m) t = some fx) (lo : List (OracleShape × ℕ))
    (no : Fin lo.length → ℕ) (h fresh : ℕ)
    (hs : ∀ b : {i // memMain lo i}, ∃ xo, s'.st.oracles[no b.1]? = some xo ∧
      xo.shape = (lo.get b.1).1)
    (hm : ∃ xoF, s'.st.oracles[fresh]? = some xoF ∧ xoF.shape.maskRows = 2 ^ h) :
    (∀ b : {i // memMain lo i}, ∃ xo, (First.K2.skelOf fx).oracles[no b.1]? = some xo ∧
        xo.shape = (lo.get b.1).1) ∧
      ∃ xoF, (First.K2.skelOf fx).oracles[fresh]? = some xoF ∧ xoF.shape.maskRows = 2 ^ h := by
  refine ⟨fun b => ?_, ?_⟩
  · obtain ⟨xo, x1, x2⟩ := hs b
    exact ⟨xo, by rw [skel_old_door hH hd hf (Array.getElem?_eq_some_iff.1 x1).1]; exact x1, x2⟩
  · obtain ⟨xo, x1, x2⟩ := hm
    exact ⟨xo, by rw [skel_old_door hH hd hf (Array.getElem?_eq_some_iff.1 x1).1]; exact x1, x2⟩

/-- **hFr's FOURTH FACT, WHEREVER THE SWITCH STANDS.** -/
theorem keptCount_door {Z : ProofFile.Pub} {m : ℕ} {s' t : First.S}
    (hH : (ProofFile.pAtK2 Z m).stands = .head → ∀ a, s'.here ≠ .head a)
    (hd : doorZ Z m s' = some t) {fx : _root_.Tw.K2.Front}
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
  rw [Array.getD_eq_getD_getElem?, skel_old_door hH hd hf h1, Array.getElem?_eq_getElem h1]
  rfl

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.front_st_head
#print axioms VerifiableInference.Desc.LinkJoin.front_st_finish
#print axioms VerifiableInference.Desc.LinkJoin.skel_old_head
#print axioms VerifiableInference.Desc.LinkJoin.skel_old_finish
#print axioms VerifiableInference.Desc.LinkJoin.skel_old_door
#print axioms VerifiableInference.Desc.LinkJoin.doorReads_door
#print axioms VerifiableInference.Desc.LinkJoin.front_shapes_door
#print axioms VerifiableInference.Desc.LinkJoin.keptCount_door
