-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/HandsAtLater.lean: WHAT
ONE BLOCK OWES (`IM.Hands`: six fields: mark, shape, rows, members, book, more) AT
KIND K1's FIFTY LATER SENDINGS of a proof file's first chain: at every link l < 25 its reads' place
and its digits' place. Two theorems: calls alone.
On words: "the state" is the value of type S that the description's fold carries from block to
block.
  hands_block   GENERAL in the table's letters, the place's parameters P and the block: at any block
                c under a lot's block B (`c.UnderR B.retype`) with two declared rounds, whose yes
                leaves the mark and is a step of a later sending (`StepL`, KeepAtLater.lean): mark
                by hmark · shape by `shapeAt_stepL` · rows by `rowsHeld_joins`, `rowsHeld_open` ·
                members by `membersHeld_joins` · book by `bookAt_stepL`: the steps of
                `keep_later`'s own proof, CALLED.
  hands_later   **AT THE FIFTY**: at (l, d), at any block under `blkL Z G l d X arrs`: the table's
                row by `rowL_digits_full` | `rowL_reads_full` (by the kernel at the written list);
                the mark by `commit_mark` | `reads_mark`; the step by `stepL_commitAtS` |
                `stepL_k1Reads`.
WHAT STAYS AS PREMISES, BY NAME (the first four are the top `k01_law`'s own binders):
  hinj · trees · msgs · hP   on the plan's numbers.
  hg     inside X at border k the state's open link's frame has the plan's group of l. NO CONJUNCT
         OF `IM.BK` SAYS SO: it has to come out of the letter E, or of a Bool more.
  more   the field `more` itself: E is a letter here.
What is not claimed. That any premise holds at the numbers and the letter E that are meant. Nothing
on soundness.

-/
import Johnson.Desc.K1.Law.LaterOne
import Johnson.IMR.HandsDef

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S ModelPart Item Pub Numbers More flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.K13.Law (openAt)
open OnBytes.Model.Stages (LinkH)
open IM (k1Ix k1Reads)

/-- **What one block owes, at a block under a later sending's.** -/
theorem hands_block (N : Numbers) (links : List ModelPart) (ps : List Place) (E : ℕ → S → Bool)
    (ft k m t : ℕ) (P : Par) (B : Block S Unit) (c : Block S ProofFile.Cl)
    (hc : c.UnderR (B.retype : Block S ProofFile.Cl)) (hl : B.rounds.length = 2)
    (hmark : ∀ s s' r₁ r₂ gs, B.decide s [r₁, r₂] gs = .ok s' → s'.failed = s.failed)
    (hstep : ∀ s s' r₁ r₂ gs, B.decide s [r₁, r₂] gs = .ok s' → ∀ g,
      (∀ L, s.link? = some L → L.check.frame.group = g) → StepL P g ((), s) ((), s'))
    (M : More) (T : List Pub)
    (hT : RowL N M links ps k m t (layOf P).shapes.size P.sent.size T)
    (hP : laterSeatsB N P m t (N.treesAt ps[k]?) = true)
    (hg : ∀ s : S, s.failed = none → IM.XK N links ps E k s = true →
      ∀ L, s.link? = some L → L.check.frame.group = N.groupAt m)
    (more : ∀ s s', IM.Yes ft c s s' → s.failed = none → s'.failed = none →
      IM.XK N links ps E k s = true → E (k + 1) s' = true) :
    IM.Hands N links ps E ft k c := by
  have hdec : ∀ s s', IM.Yes ft c s s' → ∃ r₁ r₂ gs, B.decide s [r₁, r₂] gs = .ok s' := by
    rintro s s' ⟨rs, cols, n, hst⟩
    obtain ⟨r₁, r₂, gs, hd⟩ := yes_of_step c (by rw [hc.1]; exact hl) ft s s' rs cols n hst
    exact ⟨r₁, r₂, gs, hc.2 _ _ _ _ hd⟩
  have hst : ∀ s s', IM.Yes ft c s s' → s.failed = none → IM.XK N links ps E k s = true →
      StepL P (N.groupAt m) ((), s) ((), s') := by
    intro s s' hy h0 hx
    obtain ⟨r₁, r₂, gs, hd⟩ := hdec s s' hy
    exact hstep s s' r₁ r₂ gs hd _ (hg s h0 hx)
  refine ⟨fun s s' hy h => ?_, fun s s' hy h0 _ hx => ?_, fun s s' hy h0 _ hx => ?_,
    fun s s' hy h0 _ hx => ?_, fun s s' hy h0 _ hx => ?_, more⟩
  · obtain ⟨r₁, r₂, gs, hd⟩ := hdec s s' hy
    rw [hmark s s' r₁ r₂ gs hd]
    exact h
  · obtain ⟨p, p', hp, hp', hs, hk⟩ := hT.next
    have c1 := (IM.xk_parts hx).1
    rw [hp] at c1
    rw [hp']
    exact shapeAt_stepL (hst s s' hy h0 hx) links p p' hs hk c1
  · have c2 : First.rowsHeld N (openAt links ps k) s = true := (IM.xk_parts hx).2.1
    show First.rowsHeld N (openAt links ps (k + 1)) s' = true
    exact rowsHeld_open N _ _ _ hT.seg hT.due hT.inl
      (rowsHeld_joins N _ s s' (hst s s' hy h0 hx).joins c2)
  · have c3 : First.membersHeld N (openAt links ps k) s = true := (IM.xk_parts hx).2.2.1
    have c6 := (IM.xk_parts hx).2.2.2.1
    unfold First.bookAt at c6
    simp only [Bool.and_eq_true, beq_iff_eq] at c6
    obtain ⟨⟨b1, b2⟩, _⟩ := c6
    show First.membersHeld N (openAt links ps (k + 1)) s' = true
    exact membersHeld_joins P s s' N _ _ m t (hst s s' hy h0 hx).joins (hst s s' hy h0 hx).booked
      hT.seg hT.inj b2 hT.other hT.here (by rw [b1]; exact hP) c3
  · exact bookAt_stepL (hst s s' hy h0 hx) N _ _ hT.trees hT.msgs (IM.xk_parts hx).2.2.2.1

/-- **AT THE FIFTY.** -/
theorem hands_later (N : Numbers) (E : ℕ → S → Bool) (ft : ℕ) (Z : ProofFile.Pub) (G : ProofFile.Ground)
    (l : ℕ) (hl : l < 25) (d : Bool) (X : LinkH) (arrs : Option (List ℕ)) (c : Block S ProofFile.Cl)
    (hu : c.UnderR ((blkL Z G l d X arrs).retype : Block S ProofFile.Cl))
    (hinj : ∀ m' ∈ First.rowSegs (openAt linksFull (flatPlacesOf linksFull true) (noL l d + 1)),
      N.groupAt m' = N.groupAt l → m' = l)
    (trees : N.treesAt (flatPlacesOf linksFull true)[noL l d + 1]? =
      N.treesAt (flatPlacesOf linksFull true)[noL l d]? + (layOf (parL Z G l d)).shapes.size)
    (msgs : N.msgsAt (flatPlacesOf linksFull true)[noL l d + 1]? =
      N.msgsAt (flatPlacesOf linksFull true)[noL l d]? + (parL Z G l d).sent.size)
    (hP : laterSeatsB N (parL Z G l d) l (momL d)
      (N.treesAt (flatPlacesOf linksFull true)[noL l d]?) = true)
    (hg : ∀ s : S, s.failed = none →
      IM.XK N linksFull (flatPlacesOf linksFull true) E (noL l d) s = true →
      ∀ L, s.link? = some L → L.check.frame.group = N.groupAt l)
    (more : ∀ s s', IM.Yes ft c s s' → s.failed = none → s'.failed = none →
      IM.XK N linksFull (flatPlacesOf linksFull true) E (noL l d) s = true →
      E (noL l d + 1) s' = true) :
    IM.Hands N linksFull (flatPlacesOf linksFull true) E ft (noL l d) c := by
  cases d with
  | true =>
    exact hands_block N linksFull (flatPlacesOf linksFull true) E ft (noD l) l 2
      (parD G.first (gpOf Z) l)
      (laterAt G.first (gpOf Z) l (k1Ix l true + 1) 2 arrs : Block S Unit) c hu rfl
      (commit_mark _ _ _ _)
      (fun s s' r₁ r₂ gs h g hg' => stepL_commitAtS _ _ _ _ s s' r₁ r₂ gs h g hg' ())
      {} _ (rowL_digits_full N {} l hl _ _ hinj trees msgs) hP hg more
  | false =>
    exact hands_block N linksFull (flatPlacesOf linksFull true) E ft (noR l) l 1 (parR Z G l)
      (k1Reads Z G l X (k1Ix l false + 1) arrs) c hu (rounds_k1Reads _ _ _ _ _ _)
      (reads_mark _ _ _ _ _ _)
      (fun s s' r₁ r₂ gs h g hg' => stepL_k1Reads _ _ _ _ _ _ s s' r₁ r₂ gs h g hg' ())
      {} _ (rowL_reads_full N {} l hl _ _ hinj trees msgs) hP hg more

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.hands_block
#print axioms VerifiableInference.Desc.K1.hands_later
