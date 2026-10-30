-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/MsgsOfFrame.lean: THE SMALLNESS TEST: EVERY ORACLE MESSAGE IN WHICH ONE OF ITS
ARRAYS LIES IS, BY THE TEXT ALONE, AN ENTRY OF THE OPEN LINK'S FRAME'S OWN LIST OR OF ITS LIST OF
KEPT COPIES. Statements with their proofs; one definition. The first step on the two premises
hmem and hG.

Main names (namespace `VerifiableInference.Desc.First.K8`).
  **`msgs_own_or_kept`**: o ∈ `Named.msgs tl L` → o ∈ `L.check.frame.own.toList` ∨ o ∈
    `L.check.frame.keptBefore.toList`. By `Order.namedNow`'s two arms:
    `Named.namedNow_own` and `Named.namedNow_kept` (Johnson/Desc/First/K8/LawNamed.lean,
    LawBookNames.lean), through `Named.mem_msgs`.
  `hmem_of_lists`: so, where every entry of these two lists is a member of a group G, every message
    of `Named.msgs tl L` is: the premise hmem of `sent_of_members`
    (Johnson/Desc/First/K8/SentPromise.lean).
  **`sent_of_lists`**: `sent_of_onQ` with hmem exchanged for the two premises on the frame's lists.
  **`FrameJoined St f`**: ONE SENTENCE ON A STATEMENT AND A COPY OF THE FRAME: every entry of
    `f.own` and of `f.keptBefore` is a member of the group number `f.group`, which is made.
    **`sent_of_joined`**: `sent_of_onQ` under that sentence at the open link's copy, and
    `L.check.frame.group = N.groupAt l`: "the group is made" (hG) IS NO PREMISE.

Every "there is": as in SentPromise.lean.
WHAT IS NOT PAID HERE: `FrameJoined` at the state in front of the draw, and which group the copy
names: facts on the verifier's state.
Limits. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.K8.SentPromise
import Johnson.Desc.First.K8.LawBookNames

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8
open OnBytes OnBytes.Model
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers flatPlacesOf)

/-- **BY THE TEXT ALONE.** -/
theorem msgs_own_or_kept (tl : HTailF2) (L : LinkCtx) (o : ℕ) (ho : o ∈ Named.msgs tl L) :
    o ∈ L.check.frame.own.toList ∨ o ∈ L.check.frame.keptBefore.toList := by
  obtain ⟨t, -, hto⟩ := Named.mem_msgs.1 ho
  unfold Named.msgNow at hto
  cases hw : Order.liesAt L t with
  | none => simp [hw] at hto
  | some w =>
    rw [hw] at hto
    have hn : Order.namedNow L.check.frame w = some o := hto
    by_cases hb : w.born = L.check.frame.link
    · left
      rw [Named.namedNow_own L w hb] at hn
      unfold Named.ownNow at hn
      split at hn
      · exact Array.mem_toList_iff.2 (Array.mem_of_getElem? hn)
      · exact nomatch hn
    · exact Or.inr (Named.namedNow_kept hn hb)

/-- The premise hmem, from the frame's two lists. -/
theorem hmem_of_lists (tl : HTailF2) (L : LinkCtx) (G : Group)
    (hown : ∀ o ∈ L.check.frame.own.toList, o ∈ G.members.toList)
    (hkept : ∀ o ∈ L.check.frame.keptBefore.toList, o ∈ G.members.toList) :
    ∀ o ∈ Named.msgs tl L, o ∈ G.members.toList := fun o ho =>
  (msgs_own_or_kept tl L o ho).elim (hown o) (hkept o)

/-- **OUT OF THE PROMISE, AT THE FULL SIZE, IN FRONT OF THE DRAW OF SEGMENT l**: under the two
premises on the open link's frame's lists. -/
theorem sent_of_lists {A P W : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
    (get : A → P × First.S) (l : ℕ) (hl : l ≤ 24) (a : A × Fr.E.Str)
    (h : onQ N Mg linksFull (flatPlacesOf linksFull true) get (drawAt l) a)
    (hm : (get a.1).2.failed = none) (rad : OracleShape → ℕ) (tl : HTailF2) (L : LinkCtx)
    (G : Group) (hG : (get a.1).2.st.groups[N.groupAt l]? = some G)
    (hown : ∀ o ∈ L.check.frame.own.toList, o ∈ G.members.toList)
    (hkept : ∀ o ∈ L.check.frame.keptBefore.toList, o ∈ G.members.toList) :
    ∀ i, ∃ t ∈ [0, 1],
      Named.seatFn rad (get a.1).2.st (get a.1).2.book tl L i ∈ N.sent l t :=
  sent_of_onQ N Mg get l hl a h hm rad tl L G hG (hmem_of_lists tl L G hown hkept)

/-- **One sentence on a statement and a copy of the frame**: every entry of the frame's own list and
of its list of kept copies is a member of the group that the frame names, and that group is made. At
a frame with both lists empty nothing is asked. -/
def FrameJoined (St : Statement) (f : ReqFrame) : Prop :=
  ∀ o, o ∈ f.own.toList ∨ o ∈ f.keptBefore.toList →
    ∃ G, St.groups[f.group]? = some G ∧ o ∈ G.members.toList

/-- **OUT OF THE PROMISE, UNDER THAT ONE SENTENCE** at the open link's copy of the frame, and that
this copy names the segment's listed group. "The group is made" is no premise: where the
list has a seat at all, it has a message, and the sentence makes the group. -/
theorem sent_of_joined {A P W : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
    (get : A → P × First.S) (l : ℕ) (hl : l ≤ 24) (a : A × Fr.E.Str)
    (h : onQ N Mg linksFull (flatPlacesOf linksFull true) get (drawAt l) a)
    (hm : (get a.1).2.failed = none) (rad : OracleShape → ℕ) (tl : HTailF2) (L : LinkCtx)
    (hJ : FrameJoined (get a.1).2.st L.check.frame) (hg : L.check.frame.group = N.groupAt l) :
    ∀ i, ∃ t ∈ [0, 1],
      Named.seatFn rad (get a.1).2.st (get a.1).2.book tl L i ∈ N.sent l t := by
  intro i
  obtain ⟨o, ho, -⟩ := seat_placed rad (get a.1).2.st (get a.1).2.book tl L i
  obtain ⟨G, hG, -⟩ := hJ o (msgs_own_or_kept tl L o ho)
  rw [hg] at hG
  refine sent_of_onQ N Mg get l hl a h hm rad tl L G hG (fun o' ho' => ?_) i
  obtain ⟨G', hG', hm'⟩ := hJ o' (msgs_own_or_kept tl L o' ho')
  rw [hg, hG] at hG'
  rw [Option.some.inj hG']
  exact hm'

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.sent_of_joined
#print axioms VerifiableInference.Desc.First.K8.msgs_own_or_kept
#print axioms VerifiableInference.Desc.First.K8.hmem_of_lists
#print axioms VerifiableInference.Desc.First.K8.sent_of_lists
