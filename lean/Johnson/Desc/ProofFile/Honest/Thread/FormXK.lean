-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/FormXK.lean: WHAT THE FIRST CHAIN's FORM AT A BORDER IS: ONE
LEMMA, WITH NO FENCE, NO YES AND NO FORM IN FRONT. The thread's clause `Form` at the first chain's
letters is "no mark" and the library's promise at the honest letters and no strings. At these
letters "decodes", "shown" and "no collision" are true by the letters' text. What is left: no mark
· the promise's six Bools at the border (the library's `IM.XK` at `P1K2.EQ`: where the chain stands
· the open rows' lists · the groups' members · where the book stands · "in order" · every open
public item's Bool) · `samplesHeld` · what the open public items say beside their Bools (`pubP`). A
reader's mark: that this be the page's ground, with the ways to the six Bools as payers of ONE
`XK`. General in the first chain's letters (at the proof file's type of claims). No definition.
Four conditional lemmas.

  `form_of_xk`          no mark · XK · samplesHeld · pubP at a border give the form there
  `xk_of_form`          the form gives XK: so the six Bools in front are in hand at the thread
  `form_behind_of_xk`   the same behind a member's step, at where the prover's run then stands: the
                        join that an author's `BehindS` wants (the input is as it was: `play_mid`)
  `xk_next_hands`       one payer of XK behind: the library's `IM.HandsR` with its fence

Limits. It pays nothing: it says what is to be paid. `XK` behind a member is that member's authors',
by whichever road: `IM.HandsR` (not lighter: the same six Bools, at every state that a yes reaches
from a fenced one; sealed under the head at the code switch's 25 places alone, by one author's sort)
· a pointwise law at a quiet row · an own evaluation of the six. `samplesHeld` behind has no payer
with us yet. It says nothing of `rides` or `keeps`. None is one of the library's goals. This file
proves nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.First
import Johnson.Desc.ProofFile.Honest.Thread.Riders
import Johnson.P1K2R.TieTwo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S onAt samplesHeld)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X P Cells Tok M : Type}

/-- **WHAT THE FORM AT A BORDER IS.** -/
theorem form_of_xk (L : Letters Bk ProofFile.Cl W₀ Rc Xi Tr X P Cells Tok M) {b : Nat} {k : Coins Bk}
    {s : S} {m : Mid (Local W₀ Rc Xi Tr) X} (h0 : s.failed = none)
    (hx : IM.XK L.N L.links L.ps (P1K2.EQ L.mgP L.links L.ps (L.pubOf m.st.input.x)) b s = true)
    (hHeld : samplesHeld L.N L.mgP (IM.openAt L.links L.ps b) (L.pubOf m.st.input.x, s) = true)
    (hPP : ∀ q ∈ P1K2.pubAt L.mgP L.links L.ps b, L.mgP.pubP q (L.pubOf m.st.input.x, s)) :
    L.thread.Form b k s m := by
  refine ⟨?_, ?_⟩
  · show s.failed.isNone = true
    rw [h0]
    rfl
  · show onAt L.N L.mgP L.links L.ps[b]? (IM.openAt L.links L.ps b)
      (P1K2.pubAt L.mgP L.links L.ps b) (L.pubOf m.st.input.x, s) noStrs
    refine ⟨trivial, Or.inr ?_⟩
    obtain ⟨c1, c2, c3, c4, c5⟩ := IM.xk_parts hx
    unfold P1K2.EQ at c5
    rw [Bool.and_eq_true] at c5
    refine ⟨?_, hHeld, fun _ _ => ⟨trivial, trivial⟩, hPP⟩
    rw [c1, c2, c3, c5.1, c5.2, c4]
    rfl

/-- The form gives the six Bools. -/
theorem xk_of_form (L : Letters Bk ProofFile.Cl W₀ Rc Xi Tr X P Cells Tok M) {b : Nat} {k : Coins Bk}
    {s : S} {m : Mid (Local W₀ Rc Xi Tr) X} (hF : L.thread.Form b k s m) :
    IM.XK L.N L.links L.ps (P1K2.EQ L.mgP L.links L.ps (L.pubOf m.st.input.x)) b s = true := by
  have h0 : s.failed = none := Option.isNone_iff_eq_none.1 hF.1
  have ha : onAt L.N L.mgP L.links L.ps[b]? (IM.openAt L.links L.ps b)
      (P1K2.pubAt L.mgP L.links L.ps b) (L.pubOf m.st.input.x, s) noStrs := hF.2
  exact P1K2.xk_of_on ha h0

/-- **THE FORM BEHIND A MEMBER's STEP**, at where the prover's run then stands: all four premises at
the input in front. -/
theorem form_behind_of_xk (L : Letters Bk ProofFile.Cl W₀ Rc Xi Tr X P Cells Tok M) {b : Nat}
    {blk : Block S ProofFile.Cl} {k : Coins Bk} {s s' : S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hS : L.thread.Stepped blk k s m E ds y cols s') (h' : s'.failed = none)
    (hx : IM.XK L.N L.links L.ps (P1K2.EQ L.mgP L.links L.ps (L.pubOf m.st.input.x)) (b + 1) s' =
      true)
    (hHeld : samplesHeld L.N L.mgP (IM.openAt L.links L.ps (b + 1))
      (L.pubOf m.st.input.x, s') = true)
    (hPP : ∀ q ∈ P1K2.pubAt L.mgP L.links L.ps (b + 1),
      L.mgP.pubP q (L.pubOf m.st.input.x, s')) : L.thread.Form (b + 1) k s' y.2 := by
  have hS' := hS
  unfold Thread.Stepped Thread.Moved at hS'
  obtain ⟨⟨⟨l, -, hy⟩, -⟩, -⟩ := hS'
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  exact form_of_xk L h' (by rw [ei]; exact hx) (by rw [ei]; exact hHeld) (by rw [ei]; exact hPP)

/-- **ONE PAYER OF THE SIX BOOLS BEHIND**: the library's `IM.HandsR`, at a fence that the state in
front meets. -/
theorem xk_next_hands (L : Letters Bk ProofFile.Cl W₀ Rc Xi Tr X P Cells Tok M) {Fk : Nat → S → Prop}
    {ft b : Nat} {blk : Block S ProofFile.Cl} {k : Coins Bk} {s s' : S}
    {m : Mid (Local W₀ Rc Xi Tr) X}
    (Hd : IM.HandsR Fk L.N L.links L.ps (P1K2.EQ L.mgP L.links L.ps (L.pubOf m.st.input.x)) ft b
      blk)
    (hf : Fk b s) (hy : IM.Yes ft blk s s') (h' : s'.failed = none)
    (hF : L.thread.Form b k s m) :
    IM.XK L.N L.links L.ps (P1K2.EQ L.mgP L.links L.ps (L.pubOf m.st.input.x)) (b + 1) s' =
      true :=
  Hd.step hf hy (Option.isNone_iff_eq_none.1 hF.1) h' (xk_of_form L hF)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.form_of_xk
#print axioms ProofFile.Honest.FirstThread.xk_of_form
#print axioms ProofFile.Honest.FirstThread.form_behind_of_xk
#print axioms ProofFile.Honest.FirstThread.xk_next_hands
