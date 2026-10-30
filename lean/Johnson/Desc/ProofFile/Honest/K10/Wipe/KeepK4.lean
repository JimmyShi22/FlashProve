-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Wipe/KeepK4.lean: the closing of a segment (K10): a layers' link's own block (kind K4,
Johnson/Desc/First/K4/AtC.lean: blockAtC) does alike at two states of the first chain that are one once wiped. One
structure of type Prop; the rest are theorems.

Words. wipeS sets to zero the targets of the rows that a state of the first chain holds (Honest/K10/WipeS.lean says
which). Two states are one under w where w s = w s'. A reader does not see w where it returns at w s what it returns
at s. A writer goes through w where it returns at w s the image under w of what it returns at s. Two outcomes are
alike where both refuse with the same word, or both return and the values are one under w (AlikeE, Wipe/Alike.lean). A
block does alike (Whole2 w) where its decide, each of its runs of claims and each of its runs behind the batching have
like outcomes at two states that are one under w; the claims of a run are then equal.

What is proved.
  K4Blind w L     what is asked of K4's seat L: its five readers do not see w; its three layings go through w
  hearAt2, runOf2, freeSlot2, block4_whole2   K4Blind w L ⊢ the kind's decide, a named run of its claims, its run
                  behind the batching, and so its block, do alike, at any type of state
  seatOwn_blind   K4Blind wipeK4 seatOwn: the seat at K4's part of the state, under that part's wiping
                  (Wipe/WipeLenses.lean)
  **k4_keeps**      Whole2 wipeS (blockAtC p): the field k4 of SeatKeeps2 (Wipe/Lots2.lean)

By what. At any type of state: what the seat's readers return at s is rewritten to what they return at s'; then the
two texts make the same calls, one after the other (AlikeE.head'); the decide ends in a branching on what the hearing
returns, which is one value in both. The hearing (hearFl) and the makers of the forms are handed public records, the
tokens, what the lookup returned and the ledger, never the state: they are not opened. From the part to the state:
Wipe/Wrap2.lean's liftPart_whole2 and atClaims_whole2, over Wipe/WipeLenses.lean's k4Part_wipe and k4Set_wipe.

Limits. K4's part holds the link's context, which wipeK4 wipes; that the kind's text reads nothing of it is what
seatOwn_blind says. Nothing is said of what the hearing or the forms' makers compute. No property of the protocol is
claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Wipe.KeepBase
import Johnson.Desc.ProofFile.Honest.K10.Wipe.Wrap2
import Johnson.Desc.ProofFile.Honest.K10.Wipe.WipeLenses
import Johnson.Desc.First.K4.AtC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)

/-! ## 1 The kind at any type of state -/

section letter
variable {T : Type} {w : T → T} {L : OnBytes.Desc.First.K4.Seat T}

/-- What is asked of K4's seat: the readers do not see w; the layings go through w. -/
structure K4Blind (w : T → T) (L : OnBytes.Desc.First.K4.Seat T) : Prop where
  fork : ∀ s, L.fork (w s) = L.fork s
  look : ∀ s, L.look (w s) = L.look s
  own : ∀ s, L.own (w s) = L.own s
  owed : ∀ s, L.owed (w s) = L.owed s
  tokv : ∀ s, L.tokv (w s) = L.tokv s
  setFork : ∀ s F, L.setFork (w s) F = w (L.setFork s F)
  setOwn : ∀ s o, L.setOwn (w s) o = w (L.setOwn s o)
  setOwed : ∀ s d, L.setOwed (w s) d = w (L.setOwed s d)

/-- K4's decide has like outcomes at two states that are one under w. -/
theorem hearAt2 (h : K4Blind w L) (p : OnBytes.Desc.First.K4.Par) {s s' : T} (hs : w s = w s')
    (rs : List Fmt.RoundView) : AlikeE w (OnBytes.Desc.First.K4.hearAt L p s rs) (OnBytes.Desc.First.K4.hearAt L p s' rs) := by
  unfold OnBytes.Desc.First.K4.hearAt
  rw [blind2 (f := L.owed) h.owed hs, blind2 (f := L.look) h.look hs, blind2 (f := L.tokv) h.tokv hs,
    blind2 (f := L.fork) h.fork hs]
  refine AlikeE.head' fun _ => ?_
  refine AlikeE.head' fun _ => ?_
  refine AlikeE.head' fun _ => ?_
  refine AlikeE.head' fun fo => ?_
  split
  · exact AlikeE.ok (put2 (f := L.setOwed) h.setOwed
      (put2 (f := L.setOwn) h.setOwn (put2 (f := L.setFork) h.setFork hs _) _) _)
  · exact AlikeE.error _
  · exact AlikeE.error _

/-- A named run of K4's claims returns equal forms and like states at two states that are one under w. f, whose type is
left to Lean: Own → Fork → Option (Array Aff × Fork), as the library's `runOf` has it. -/
theorem runOf2 (h : K4Blind w L) (name : String) (f : _) : FnCl2 w (OnBytes.Desc.First.K4.runOf L name f) := by
  intro s s' hs
  unfold OnBytes.Desc.First.K4.runOf
  rw [blind2 (f := L.own) h.own hs, blind2 (f := L.fork) h.fork hs]
  refine AlikeE.head' fun o => ?_
  refine AlikeE.head' fun x => ?_
  exact AlikeE.ok (wCl_eq (put2 (f := L.setFork) h.setFork hs _))

/-- K4's run behind the batching has like outcomes at two states that are one under w. hp, whose type is left to Lean:
the layers' plan HPlan2, as the library's `freeSlot` has it. -/
theorem freeSlot2 (h : K4Blind w L) (hp : _) : Fn2 w (OnBytes.Desc.First.K4.freeSlot L hp) := by
  intro s s' hs
  unfold OnBytes.Desc.First.K4.freeSlot
  rw [blind2 (f := L.own) h.own hs, blind2 (f := L.fork) h.fork hs]
  refine AlikeE.head' fun o => ?_
  refine AlikeE.head' fun _ => ?_
  exact AlikeE.ok hs

/-- **K4's block does alike at a seat whose readers do not see w and whose layings go through w.** -/
theorem block4_whole2 (h : K4Blind w L) (p : OnBytes.Desc.First.K4.Par) :
    Whole2 w (OnBytes.Desc.First.K4.block L p) := by
  refine ⟨fun _ _ rs _ _ hs _ => hearAt2 h p hs rs, fun c hc n => ?_, fun c hc => ?_⟩
  · rcases List.mem_cons.1 hc with rfl | hc
    · exact runOf2 h _ _
    · rcases List.mem_cons.1 hc with rfl | hc
      · exact runOf2 h _ _
      · cases hc
  · rcases List.mem_cons.1 hc with rfl | hc
    · exact freeSlot2 h _
    · cases hc

end letter

/-! ## 2 At K4's part of the first chain's state, and at the state -/

/-- K4's seat at its part of the state: its readers do not see that part's wiping; its layings go through it. -/
theorem seatOwn_blind : K4Blind wipeK4 OnBytes.Desc.First.K4.seatOwn where
  fork _ := rfl
  look _ := rfl
  own _ := rfl
  owed _ := rfl
  tokv _ := rfl
  setFork _ _ := rfl
  setOwn _ _ := rfl
  setOwed _ _ := rfl

/-- **Kind K4's block does alike at two states that are one once wiped.** -/
theorem k4_keeps (p : OnBytes.Desc.First.K4.Par) : Whole2 wipeS (OnBytes.Desc.First.K4.blockAtC p) :=
  atClaims_whole2 (liftPart_whole2 (v := wipeK4) OnBytes.Desc.First.K4.part? OnBytes.Desc.First.K4.setPart
    (fun s s' h => by rw [← k4Part_wipe, ← k4Part_wipe, h])
    (fun s s' e e' h he => by rw [k4Set_wipe, k4Set_wipe, h, he])
    (block4_whole2 seatOwn_blind p))

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.K4Blind
#print axioms ProofFile.Honest.K10.hearAt2
#print axioms ProofFile.Honest.K10.runOf2
#print axioms ProofFile.Honest.K10.freeSlot2
#print axioms ProofFile.Honest.K10.block4_whole2
#print axioms ProofFile.Honest.K10.seatOwn_blind
#print axioms ProofFile.Honest.K10.k4_keeps
