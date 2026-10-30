-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/LinkLaw5.lean: the premises `Piece.Reads` (Johnson/Desc/LinkLaw3.lean) and
`Piece.ReadsAll` (Johnson/Desc/LinkLaw4.lean), paid at the written rounds of the file format, from
the law of the reading of a round (Johnson/Flat/ReadingBad.lean).

The two premises ask: a set of field elements pulls back to a family of bad raw challenges within a
piece's errors, such that on a clean transcript on which the proofs of work pass no drawn element
lies in its set. ReadingBad.lean has such families at the format's own kit of challenges
(`ckP .two`): `badElems` for one set, `badAll` for a set that hangs on what stands before
the element; they hold the raw challenges that pass the work and whose drawn elements hit.

What is said.
  `within_mono`: a family within a list of errors is within every larger list.
  `reads_of_counts`: `Piece.Reads`, if positions have at most 64 bits, the rounds that are put
    behind the stretch's own draw no element, and the piece's errors bear the counts `badErr` of
    every set of at most d elements.
  `readsAll_of_counts`: `Piece.ReadsAll`, the like, with `CountsAll`.

`hback` is owed by whoever lays a chain's pieces. It is meant to be met so: the only round that the
format's decision puts behind a view's own rounds is `withEmptySealRound`'s (Johnson/Desc/Block.lean), at the
first chain: a round without an item and without a draw; and `Piece.back` (ChainRule.lean) is meant
for that round alone. That a chain's pieces are laid so is shown nowhere yet. At a piece of several
rounds `badErr` counts at every round that draws elements, also at rounds of which the law that
calls `Reads` does not speak: harmless at the batching's one round.

What is left: the counts themselves: how many typed values of a round's draws hit a set of at most d
(or, element by element, of at most deg) field elements, times the sampler's bound. That is a count
on the format's draws, owed by the law of the reading of a round.

-/
import Johnson.Desc.LinkLaw4
import Johnson.Flat.ReadingBad

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run (ckP)
open _root_.Iop (Err Shape BadFam)

/-- A family of bad challenges within a list of errors is within every larger list. -/
theorem within_mono : ∀ {s : Shape} (fam : BadFam s) {ε ε' : Err s}, Err.le ε ε' →
    fam.Within ε → fam.Within ε'
  | [], _, _, _, _, _ => trivial
  | _ :: _, (_, k), (_, _), (_, _), h, hw =>
    ⟨fun m => (hw.1 m).trans h.1, fun m c => within_mono (k m c) h.2 (hw.2 m c)⟩

variable {S Cl W K : Type} {F : Frame}

/-- What a piece's verifier is shown: the stretch's own rounds, then those put behind. -/
theorem shown_rounds (p : Piece (ckP .two) F S Cl W) (y : F.E.Str)
    (τ : Iop.Tr (uLT (ckP .two) p.ds)) :
    (p.shown y τ).rounds = rvT (ckP .two) p.ds τ ++ p.back := rfl

/-- **`Piece.Reads` at the written rounds.** -/
theorem reads_of_counts (p : Piece (ckP .two) F S Cl W) (rd : Fmt.Ext → K) (d : ℕ)
    (hlog : ∀ r ∈ p.ds, r.entry.logN ≤ 64) (hback : ∀ r ∈ p.back, r.drawn.elems = [])
    (hcount : ∀ B : Finset K, B.card ≤ d → Err.le (badErr rd (↑B : Set K) p.ds) p.err) :
    p.Reads rd d := by
  intro B hB y
  refine ⟨badElems rd (↑B : Set K) p.ds,
    within_mono _ (hcount B hB) (badElems_within rd _ p.ds hlog), ?_⟩
  intro τ hclean hpass x hx
  rw [shown_rounds, List.flatMap_append] at hx
  have hb : p.back.flatMap (·.drawn.elems) = [] := by
    rw [List.flatMap_eq_nil_iff]
    exact hback
  rw [hb, List.append_nil] at hx
  have hm : x ∈ (rvT (ckP .two) p.ds τ).flatMap (·.drawn.elems) := by
    rw [hx]; exact List.mem_singleton.2 rfl
  exact fun h => badElems_clean rd _ p.ds τ hclean hpass x hm (Finset.mem_coe.2 h)

/-- **`Piece.ReadsAll` at the written rounds.** -/
theorem readsAll_of_counts (p : Piece (ckP .two) F S Cl W) (rd : Fmt.Ext → K) (deg : ℕ → ℕ → ℕ)
    (hlog : ∀ r ∈ p.ds, r.entry.logN ≤ 64) (hback : ∀ r ∈ p.back, r.drawn.elems = [])
    (hcount : ∀ B : List Fmt.RoundView → List Fmt.ItemValue → List Fmt.Ext → Finset K,
      (∀ pre vals xs, (B pre vals xs).card ≤ deg pre.length xs.length) →
      CountsAll rd (fun pre vals xs => (↑(B pre vals xs) : Set K)) p.ds p.err) :
    p.ReadsAll rd deg := by
  intro B hB y
  refine ⟨badAll rd (fun pre vals xs => (↑(B pre vals xs) : Set K)) p.ds [],
    badAll_within rd _ p.ds [] p.err hlog (hcount B hB), ?_⟩
  intro τ hclean hpass pre r post hpr xs x ys hx
  rw [shown_rounds] at hpr
  have hnb : r ∉ p.back := fun hr => by
    rw [hback r hr] at hx
    exact absurd hx (by simp)
  rcases List.append_eq_append_iff.1 hpr with ⟨a', _, h2⟩ | ⟨c', h1, h2⟩
  · exact absurd (by rw [h2]; simp) hnb
  · cases c' with
    | nil => exact absurd (by rw [← (show r :: post = p.back from h2)]; simp) hnb
    | cons c c' =>
      obtain ⟨rfl, _⟩ := List.cons.inj h2
      have := badAll_clean rd _ p.ds [] τ hclean hpass pre r c' h1 xs x ys hx
      exact fun h => this (Finset.mem_coe.2 h)

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.within_mono
#print axioms VerifiableInference.Desc.Sound.shown_rounds
#print axioms VerifiableInference.Desc.Sound.reads_of_counts
#print axioms VerifiableInference.Desc.Sound.readsAll_of_counts
