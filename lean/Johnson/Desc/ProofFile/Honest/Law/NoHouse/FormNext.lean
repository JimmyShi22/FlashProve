-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/FormNext.lean: THE FIRST CHAIN's CLAUSE (P) RIDES PAST A
STEP AT A QUIET ROW THAT PLAYS NOTHING. The first chain's thread (Honest/Thread/First.lean) has as
its clause (P): no mark, and the library's own promise `onAt` (Johnson/Desc/First/Borders.lean) at
the honest letters, at the table's own open sets. Here: at a place whose row of the table closes and
opens no class of rows and no pin (`quietRow`), from (P) at the border in front, at a state s'
behind that has the mark, the statement's groups and the book's places of the state s in front: (P)
at the next border, under six sentences on the public book-keeping behind. It serves the field
`behind` of `NoHouse` (Honest/Law/NoHouse/Bare.lean) at a member without a round.

WHAT THIS IS. Conditional lemmas on a definition of ours: one call of the library's
`onAt_step_quiet` (Johnson/Desc/First/PromiseRides.lean), as the library's own `onQ_step_quiet`
(Johnson/Desc/Sound/PromiseRidesQ.lean) calls it. At the honest letters three of that rule's
premises are true by the letters' text (decodes, shown, no collision). None of the library's goals.

  `form_next_quiet`, `form_next_letters`

THE LIBRARY's KIN. `onT_rides` (Johnson/Desc/First/Link/Law/QuietRides.lean) says the like of the
table's own promise over a frame's oracles' strings, from two records of premises: `RecRides` (the
mark, the statement, the book as they were; the shape behind; the plan's counts) and `MgRides`, of
which `form_next_quiet`'s four premises on the public letters are four fields to the letter.
`LettersRide` (Johnson/Top/H0/Walk/FrameTied.lean) asks the like over a relation on states WITH THE
WHOLE PROMISE IN FRONT IN HAND, and at a state without a mark alone: the weaker ask:
`form_next_letters` takes it as ONE premise, so that whoever pays it at a filling pays the library's
own form. Of its eight fields four are spent here (in order; the public items' Bools; what they say
beside; held).

Limits. A RULE OVER LETTERS: IT PAYS NOTHING BY ITSELF. The six premises (the shape behind; where
the book stands; in order; the public items' Bools; what they say beside; held) can be paid only at
a filling of the letters. The three equations hold behind «behind the batching» by the library's
`Rb` (Johnson/Desc/First/Link/Law/RbDef.lean); OF THE OTHER MEMBERS WITHOUT A ROUND NOTHING IS
SHOWN. Where the prover's run stands does not turn: a member with a round wants another lemma.
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.Thread.First
import Johnson.Desc.First.PromiseRides
import Johnson.Desc.First.BordersSucc
import Johnson.Top.H0.Walk.FrameTied

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Block Place Strs Wit)
open VerifiableInference.Desc.First (S ModelPart Item Pub Numbers Meaning onAt openSets pubSets start
  rowOf pubRowM pubStep stepOpen quietRow shapeAt pubHeld sampledIn bookAt)
open Johnson.Desc.First.Walk.Tied (LettersRide FrontAt)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok M : Type}

/-- **(P) at the next border.** p: the place at the border b. s, s': the verifier's state in front
and behind. O, Q in the premises: the table's open items and open public items at b. -/
theorem form_next_quiet (L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M) {b : Nat} {p : Place}
    (hp : L.ps[b]? = some p) (hq : quietRow (rowOf L.links p) = true) {k : Coins Bk} {s s' : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} (hF : L.thread.Form b k s m) (hf : s'.failed = s.failed)
    (hG : s'.st.groups = s.st.groups) (hB : s'.book.place = s.book.place)
    (hShape : shapeAt L.links L.ps[b + 1]? s' = true)
    (hBook : bookAt L.N L.ps[b]? s = true → bookAt L.N L.ps[b + 1]? s' = true)
    (hIn : L.mgP.inOrder (L.pubOf m.st.input.x, s) = true →
      L.mgP.inOrder (L.pubOf m.st.input.x, s') = true)
    (hPub : pubHeld L.mgP ((openSets L.links L.ps (start L.links))[b]?.getD [])
        ((pubSets L.mgP.more L.links L.ps)[b]?.getD []) (L.pubOf m.st.input.x, s) = true →
      pubHeld L.mgP
        (stepOpen ((openSets L.links L.ps (start L.links))[b]?.getD []) (rowOf L.links p))
        (pubStep ((pubSets L.mgP.more L.links L.ps)[b]?.getD []) (pubRowM L.mgP.more L.links p))
        (L.pubOf m.st.input.x, s') = true)
    (hPP : (∀ q ∈ (pubSets L.mgP.more L.links L.ps)[b]?.getD [],
        L.mgP.pubP q (L.pubOf m.st.input.x, s)) →
      ∀ q ∈ pubStep ((pubSets L.mgP.more L.links L.ps)[b]?.getD [])
        (pubRowM L.mgP.more L.links p), L.mgP.pubP q (L.pubOf m.st.input.x, s'))
    (hHeld : ∀ x ∈ sampledIn L.N ((openSets L.links L.ps (start L.links))[b]?.getD []),
      L.mgP.held x.1 x.2 (L.pubOf m.st.input.x, s) = true →
      L.mgP.held x.1 x.2 (L.pubOf m.st.input.x, s') = true) :
    L.thread.Form (b + 1) k s' m := by
  obtain ⟨h1, h2⟩ := hF
  have h1' : s.failed.isNone = true := h1
  have h2' : onAt L.N L.mgP L.links L.ps[b]?
      ((openSets L.links L.ps (start L.links))[b]?.getD [])
      ((pubSets L.mgP.more L.links L.ps)[b]?.getD []) (L.pubOf m.st.input.x, s) noStrs := h2
  refine ⟨?_, ?_⟩
  · show s'.failed.isNone = true
    rw [hf]
    exact h1'
  · show onAt L.N L.mgP L.links L.ps[b + 1]?
      ((openSets L.links L.ps (start L.links))[b + 1]?.getD [])
      ((pubSets L.mgP.more L.links L.ps)[b + 1]?.getD []) (L.pubOf m.st.input.x, s') noStrs
    rw [VerifiableInference.Desc.First.openSets_succ L.links L.ps (start L.links) b p hp,
      VerifiableInference.Desc.First.pubSets_succ L.mgP.more L.links L.ps b p hp]
    exact VerifiableInference.Desc.First.onAt_step_quiet L.N L.mgP L.links L.ps[b]? L.ps[b + 1]? _
      _ _ (rowOf L.links p) (L.pubOf m.st.input.x, s) (L.pubOf m.st.input.x, s') noStrs noStrs hq
      h2' (fun h => by
        show s'.failed ≠ none
        rw [hf]
        exact h) (fun _ => trivial) (fun _ => hShape) hG hB hIn (fun _ => hPub) (fun _ => hBook)
      (fun _ => hPP) hHeld (fun _ _ _ => trivial) (fun _ _ _ => trivial)

/-- **The same, from the library's own `LettersRide`**, at a relation rel in which s and s' stand.
-/
theorem form_next_letters (L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M) {b : Nat} {p : Place}
    (hp : L.ps[b]? = some p) (hq : quietRow (rowOf L.links p) = true) {k : Coins Bk} {s s' : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} (hF : L.thread.Form b k s m) (hf : s'.failed = s.failed)
    (hG : s'.st.groups = s.st.groups) (hB : s'.book.place = s.book.place)
    (hShape : shapeAt L.links L.ps[b + 1]? s' = true)
    (hBook : bookAt L.N L.ps[b]? s = true → bookAt L.N L.ps[b + 1]? s' = true)
    {rel : S → S → Prop} {base : Nat} {Op : Item → Prop}
    (hL : LettersRide L.N L.mgP rel base (FrontAt L.N L.mgP L.links L.ps b)
      ((openSets L.links L.ps (start L.links))[b + 1]?.getD [])
      ((pubSets L.mgP.more L.links L.ps)[b + 1]?.getD []) Op) (hrel : rel s s') :
    L.thread.Form (b + 1) k s' m := by
  have h0 : s.failed = none := Option.isNone_iff_eq_none.1 hF.1
  have hFr : FrontAt L.N L.mgP L.links L.ps b (L.pubOf m.st.input.x, s) noStrs := hF.2
  have eO := VerifiableInference.Desc.First.openSets_succ L.links L.ps (start L.links) b p hp
  have eQ := VerifiableInference.Desc.First.pubSets_succ L.mgP.more L.links L.ps b p hp
  refine form_next_quiet L hp hq hF hf hG hB hShape hBook
    (fun _ => hL.inOrder _ s s' noStrs hrel h0 hFr) (fun _ => ?_) (fun _ q hq' => ?_)
    (fun x hx _ => ?_)
  · rw [← eO, ← eQ]
    unfold pubHeld
    exact List.all_eq_true.2 fun q hq' => hL.pub _ s s' noStrs q hrel h0 hFr hq'
  · rw [← eQ] at hq'
    exact hL.pubP _ s s' noStrs q hrel h0 hFr hq'
  · refine hL.held _ s s' noStrs x hrel h0 hFr ?_
    rw [eO, VerifiableInference.Desc.First.sampledIn_step L.N _ _ hq]
    exact hx

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.form_next_quiet
#print axioms ProofFile.Honest.FirstThread.form_next_letters
