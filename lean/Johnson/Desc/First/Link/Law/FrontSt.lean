-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FrontSt.lean: AT A CODE SWITCH THAT STANDS AT A LINK: THE FRONT's
STATEMENT (`K2.skelOf fx`) HAS, AT EVERY NUMBER BELOW THE BORDER's STATE's STATEMENT's ORACLE
MESSAGES, THAT STATEMENT's OWN MESSAGE: so two of the four facts on the front that `hF_of_door` asks
(hFr, HFOfDoor.lean: the written shape at each member's number; 2 ^ h mask rows at the fresh mask)
come from the border's state's statement. By calls. Theorems. No text already in the library turns.

  `rest_st`: what the way in lets in at a link has the state's statement.
  `skel_old_link`: **p stands at a link · the way in lets t in of s' · the text makes the front fx
    of t · o is below s'.st's oracle messages ⊢ (K2.skelOf fx).oracles[o]? = s'.st.oracles[o]?**:
    the front's maker pushes a fresh group and no message (`firstFront_st`,
    Johnson/Top/H0/Tw/K2C/FrontGroup.lean); the sending's notices come behind
    (`stSent_old`, OnBytes/Slice/BlkStLaws.lean).
  `front_shapes_link`: so the two facts, from: s'.st has the written shape at each member's number,
    and a message with 2 ^ h mask rows at the fresh mask's.
Limits. AT A LINK ALONE: the switches that stand at the head and at the finish are not treated. The
book behind the sending and the kept rows' count (hFr's other two) are not treated. Nothing on
soundness.
-/
import Johnson.Top.H0.Walk.FrameCarryFenceEnds
import Johnson.Top.H0.Tw.K2C.FrontGroup
import Johnson.G.SwitchKeptLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice Johnson.G
open VerifiableInference.Desc.First.K2Caller (doorZ rest)
open _root_.Johnson.Desc.First.Walk.Tied (toOption_some)

theorem rest_st (s : First.S) : (rest s).st = s.st := by
  unfold rest
  split <;> rfl

/-- **THE FRONT's STATEMENT HAS THE STATE's OWN MESSAGES.** -/
theorem skel_old_link {Z : ProofFile.Pub} {m : ℕ} (hp : (ProofFile.pAtK2 Z m).stands = .link)
    {s' t : First.S} (hd : doorZ Z m s' = some t) {fx : _root_.Tw.K2.Front}
    (hf : First.K2.frontAt (ProofFile.pAtK2 Z m) t = some fx) {o : ℕ} (ho : o < s'.st.oracles.size) :
    (First.K2.skelOf fx).oracles[o]? = s'.st.oracles[o]? := by
  unfold doorZ at hd
  rw [hp] at hd
  obtain rfl : rest s' = t := Option.some.inj hd
  unfold First.K2.frontAt at hf
  rw [hp] at hf
  dsimp only at hf
  obtain ⟨e1, _⟩ := First.K2.firstFront_st (toOption_some hf)
  have e2 : fx.st.oracles = s'.st.oracles := by
    rw [e1, rest_st]
    rfl
  unfold First.K2.skelOf
  rw [stSent_old _ _ o (by rw [e2]; exact ho), e2]

/-- **TWO OF hFr's FOUR FACTS, AT A LINK.** -/
theorem front_shapes_link {Z : ProofFile.Pub} {m : ℕ} (hp : (ProofFile.pAtK2 Z m).stands = .link)
    {s' t : First.S} (hd : doorZ Z m s' = some t) {fx : _root_.Tw.K2.Front}
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
    exact ⟨xo, by rw [skel_old_link hp hd hf (Array.getElem?_eq_some_iff.1 x1).1]; exact x1, x2⟩
  · obtain ⟨xo, x1, x2⟩ := hm
    exact ⟨xo, by rw [skel_old_link hp hd hf (Array.getElem?_eq_some_iff.1 x1).1]; exact x1, x2⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.rest_st
#print axioms VerifiableInference.Desc.LinkJoin.skel_old_link
#print axioms VerifiableInference.Desc.LinkJoin.front_shapes_link
