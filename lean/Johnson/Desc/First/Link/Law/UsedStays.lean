-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/UsedStays.lean: K9's LAW OF A LINK, THE FIELD "a part is there behind
the batching" AT THE HEAD's LINK: "THE NUMBER OF SLOTS TAKEN IS THERE" (K9.usedOf answers) STAYS
OVER A YES OF THE BATCHING's SUB-PROTOCOL AND OF THE FRAME's BEHIND IT. At the head's link that
number is there only behind the merge: so kind K9's lens finds a part behind the batching just
because it found one in front. Theorems. A law file; no running text imports it.
  `usedSome s`        K9.usedOf s answers: as a Bool. (The number itself does not rest: at an
                    attention link it is the ledger's next free slot, which a writing of the ledger
                    moves.)
  `rests_usedSome`    it rests under the four writings (FieldRests, KeepsAny.lean beside this file).
  `usedSome_set`      and under the lens's own writing.
  `used_behind_batch` a yes of L.batchB from s to s', where the sub-protocol is "a draw, then the
                    adding of the link's claims" and every run of the link stands in every relation
                    that holds of the six writings (the premises hb₁ and H of two_blocks,
                    LinkAtSort.lean): usedSome s' = usedSome s.
  `used_behind_frame` the same over a yes of L.behindB.
  `part_of_used`      at a state that stands in the head's link: usedSome gives the part
                    (part_of_head, PartOfPromise.lean).

Limits. General in the link. hb₁ and H are premises: their payers are the sorts' laws. Nothing on
soundness or on hiding.
-/
import Johnson.Desc.First.Link.Law.LinkAtSort
import Johnson.Desc.First.Link.Law.PartOfPromise

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Link Claim)
open VerifiableInference.Desc.K9 (atS usedOf Where)
open VerifiableInference.Desc.K9L (DrawMoves MoveKeeps drawMoves_keep isMoves_keep)
open VerifiableInference.Desc.First (S standOf ModelPart)
open VerifiableInference.Desc.JoinAtBlocks (behind_isMoves)

/-- The number of slots taken is there. -/
def usedSome (s : S) : Bool := (usedOf s).isSome

/-- It rests under the four writings. -/
theorem rests_usedSome : FieldRests usedSome where
  tl s tl := by
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
    cases here with
    | head x => by_cases ho : x.opened = true <;> simp [usedSome, usedOf, S.putTl, ho]
    | _ => rfl
  fork s G := by
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
    cases here with
    | head x => by_cases ho : x.opened = true <;> simp [usedSome, usedOf, S.putFork, ho]
    | _ => rfl
  wrote e _ _ _ hw := by
    obtain ⟨h1, rfl⟩ := hw
    simp [usedSome, usedOf, h1]
  head s a G h := by simp [usedSome, usedOf, h]

/-- And under a writing of the link's context. -/
theorem usedSome_putLink (s : S) (L : LinkCtx) : usedSome (s.putLink L) = usedSome s := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x => by_cases ho : x.opened = true <;> simp [usedSome, usedOf, S.putLink, ho]
  | _ => rfl

/-- And under the lens's own writing. -/
theorem usedSome_set (s : S) (a : K9.Part) : usedSome (atS.set s a) = usedSome s := by
  have h : usedSome (atS.set s a) = usedSome ((s.putLink a.L).putFork a.F) := rfl
  rw [h, rests_usedSome.fork, usedSome_putLink]

/-- **Over a yes of the batching's sub-protocol.** -/
theorem used_behind_batch (L : Link S Claim) (pp : Where)
    (hb₁ : DrawMoves atS pp [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (H : ∀ B : S → S → Prop, RelRests B → (∀ s G, B s (s.putFork G)) → RunsStand L B)
    (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : L.batchB.step ft s rs cols = .ok (s', k)) : usedSome s' = usedSome s := by
  have hU := H _ (relRests_of_field rests_usedSome) rests_usedSome.fork
  refine drawMoves_keep usedSome usedSome_set pp _ L.batchB hb₁ (fun m hm => ?_) ft s rs cols s' k h
  obtain rfl := List.mem_singleton.1 hm
  refine claimsInBy_keep usedSome L.each L.hear L.order fun r' hr' => ?_
  obtain ⟨o', ho', e'⟩ := List.mem_filterMap.1 hr'
  obtain ⟨run, hrun, rfl⟩ := Option.map_eq_some_iff.1 e'
  exact hU.1 o' ho' run hrun

/-- Over a yes of the frame's sub-protocol behind the batching. -/
theorem used_behind_frame (L : Link S Claim)
    (H : ∀ B : S → S → Prop, RelRests B → (∀ s G, B s (s.putFork G)) → RunsStand L B)
    (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : L.behindB.step ft s rs cols = .ok (s', k)) : usedSome s' = usedSome s := by
  have hU := H _ (relRests_of_field rests_usedSome) rests_usedSome.fork
  refine isMoves_keep usedSome usedSome_set _ L.behindB (behind_isMoves atS L) (fun m hm => ?_)
    ft s rs cols s' k h
  obtain rfl := List.mem_singleton.1 hm
  exact runBehind_keep usedSome L hU.2

/-- At a state that stands in the head's link. -/
theorem part_of_used {s : S} (h : standOf s = .link .head) (hu : usedSome s = true) :
    (atS.get? s).isSome = true := part_of_head h hu

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.rests_usedSome
#print axioms VerifiableInference.Desc.LinkJoin.usedSome_set
#print axioms VerifiableInference.Desc.LinkJoin.used_behind_batch
#print axioms VerifiableInference.Desc.LinkJoin.used_behind_frame
#print axioms VerifiableInference.Desc.LinkJoin.part_of_used
