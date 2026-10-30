-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/ShownNew.lean: WHAT A SENDING GIVES AT A NEW TENANT: "SHOWN". Behind a yes of
the piece whose own stretch sends a tree, the table's letter "shown" as another file fills it
(`shownJT`, Johnson/Desc/Sound/MeaningSig.lean) holds at every seat in that tree at which a member
sits. KIND-FREE: general in the piece. A statement as a definition of a Prop, and its proof.
Main names:
  `OwedShownNew`, `shown_new`: p: any piece; new: members; each of their trees is one that p's own
    stretch sends (`SentBy`, Johnson/Desc/Sound/WordsLaw.lean); p shows what it sends at each of
    their lists (`Piece.ShownAll`, Johnson/Desc/Sound/ShownOfData.lean: had at no price at every
    piece that the maker cuts: `cutShown`, `shownOfData`, under `SeatFits`); at the seat (j, t) a
    member of ms sits, and every member of ms that sits there is among new: then behind a yes:
    `shownJT cs G ms j t (strsOf Fr b.2)`.
By `out_behind` (Johnson/Desc/Sound/SendLaw.lean).
What is not claimed. `SentBy`, `ShownAll`, or that a member sits at a seat: tests on the plan and
the maker's cuts. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.MeaningSig
import Johnson.Desc.Sound.SendLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Maker
open _root_.Run.PQ (CK)
open VerifiableInference.Desc.Sound (Frame Piece Mem SitsAt shownJT SentBy strsOf out_behind)

/-- **OWED.** Behind the piece that sends their trees the new members' seats are shown. -/
def OwedShownNew : Prop :=
  ∀ {Xi A Cl W : Type} {C : CK} {Fr : Frame} (cs : Codes) (G : FileDescription Xi) (ms new : List Mem)
    (p : Piece C Fr A Cl W), SentBy p new → (∀ x ∈ new, p.ShownAll G cs x.1.l x.1.seat) →
    ∀ (j t : ℕ), (∃ x ∈ ms, SitsAt x j t) → (∀ x ∈ ms, SitsAt x j t → x ∈ new) →
    ∀ a τ b, p.ior.red.out a τ = some b → shownJT cs G ms j t (strsOf Fr b.2)

theorem shown_new : OwedShownNew := by
  intro Xi A Cl W C Fr cs G ms new p hB hSh j t hex hin a τ b hb
  refine ⟨hex, fun x hx hs => ?_⟩
  obtain ⟨n, sh, hj, hsh⟩ := hB x (hin x hx hs)
  rw [out_behind p a b τ hb]
  exact hSh x (hin x hx hs) a.2 τ x.2 n sh hj hsh

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.shown_new
