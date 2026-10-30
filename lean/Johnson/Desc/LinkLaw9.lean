-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/LinkLaw9.lean: the premises `Piece.Reads` (Johnson/Desc/LinkLaw3.lean) and
`Piece.ReadsAll` (Johnson/Desc/LinkLaw4.lean) at the written rounds of the file format, FROM THE
DEGREES ALONE: no count is left as a premise.

Johnson/Desc/LinkLaw5.lean paid the two premises down to counts of typed values. The counts are in
Johnson/Flat/ReadingCount.lean and ReadingCountAll.lean: `allErr deg i ds` is, round by round, a
bound on the typed values of which some drawn element hits its set of at most deg values, times the
bound on the written messages that give one typed value; `allErr_below_ex` there says which share
of a round's written messages that is, with the sampler's bias and the proof of work counted.

What is said.
  `readsAll_of_countsAt`: LinkLaw5's `readsAll_of_counts` from the weaker `CountsAt`: the bound of a
    round is asked at its own place in the stretch alone.
  `readsAll_allErr`: **`Piece.ReadsAll rd deg`, if the reading is one to one on typed elements and
    the piece's errors are at least `allErr deg 0 p.ds`.**
  `reads_of_readsAll`: `Piece.Reads rd d` follows from `Piece.ReadsAll` at the constant degree d.
  `reads_allErr`: so **`Piece.Reads rd d`, if the piece's errors are at least
    `allErr (fun _ _ => d) 0 p.ds`.**
So a kind that goes by these laws owes, for the carriage to raw challenges, its degrees and one
comparison of numbers for each round.

Left as premises: positions have at most 64 bits; the rounds that are put behind the stretch's own
draw no element (LinkLaw5.lean's head says who owes that); the reading is one to one on typed
elements.

Limits. With two or more elements in a round the bound in `allErr` is a union bound. At a piece of
several rounds `reads_allErr` pays d at every drawn element of every round. No piece of the protocol
is laid here.

-/
import Johnson.Desc.LinkLaw5
import Johnson.Flat.ReadingCountAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run (ckP EV toU3)
open _root_.Iop (Err Shape BadFam)

variable {S Cl W K : Type} {F : Frame}

/-- `Piece.ReadsAll` at the written rounds, the bound of a round asked at its own place alone. -/
theorem readsAll_of_countsAt (p : Piece (ckP .two) F S Cl W) (rd : Fmt.Ext → K) (deg : ℕ → ℕ → ℕ)
    (hlog : ∀ r ∈ p.ds, r.entry.logN ≤ 64) (hback : ∀ r ∈ p.back, r.drawn.elems = [])
    (hcount : ∀ B : List Fmt.RoundView → List Fmt.ItemValue → List Fmt.Ext → Finset K,
      (∀ pre vals xs, (B pre vals xs).card ≤ deg pre.length xs.length) →
      CountsAt rd (fun pre vals xs => (↑(B pre vals xs) : Set K)) 0 p.ds p.err) :
    p.ReadsAll rd deg := by
  intro B hB y
  refine ⟨badAll rd (fun pre vals xs => (↑(B pre vals xs) : Set K)) p.ds [],
    badAll_within_at rd _ p.ds [] p.err hlog (hcount B hB), ?_⟩
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

/-- `CountsAt` bears larger errors. -/
theorem countsAt_mono (rd : Fmt.Ext → K) (A : List Fmt.RoundView → List Fmt.ItemValue → List Fmt.Ext → Set K) :
    ∀ (i : ℕ) (ds : List RDT) {ε ε' : Err (uLT (ckP .two) ds)}, Err.le ε ε' →
      CountsAt rd A i ds ε → CountsAt rd A i ds ε'
  | _, [], _, _, _, _ => trivial
  | i, _ :: ds, (_, _), (_, _), h, hc =>
    ⟨fun pre vals hp => (hc.1 pre vals hp).trans h.1, countsAt_mono rd A (i + 1) ds h.2 hc.2⟩

/-- **`Piece.ReadsAll` from the degrees.** -/
theorem readsAll_allErr (p : Piece (ckP .two) F S Cl W) (rd : Fmt.Ext → K) (deg : ℕ → ℕ → ℕ)
    (hlog : ∀ r ∈ p.ds, r.entry.logN ≤ 64) (hback : ∀ r ∈ p.back, r.drawn.elems = [])
    (hinj : Function.Injective fun a : EV .two => rd (toU3 a))
    (herr : Err.le (allErr deg 0 p.ds) p.err) : p.ReadsAll rd deg :=
  readsAll_of_countsAt p rd deg hlog hback fun _ hB =>
    countsAt_mono rd _ 0 p.ds herr
      (countsAt_allErr rd _ deg (fun pre vals xs => (cnt_mem_le rd hinj _).trans (hB pre vals xs))
        0 p.ds)

/-- `Piece.Reads` from `Piece.ReadsAll` at a constant degree. -/
theorem reads_of_readsAll {C : _root_.Run.PQ.CK} (p : Piece C F S Cl W) (rd : Fmt.Ext → K) (d : ℕ)
    (h : p.ReadsAll rd fun _ _ => d) : p.Reads rd d := by
  intro B hB y
  obtain ⟨fam, hw, hc⟩ := h (fun _ _ _ => B) (fun _ _ _ => hB) y
  refine ⟨fam, hw, fun τ hclean hpass x hx => ?_⟩
  have hm : x ∈ (p.shown y τ).rounds.flatMap (·.drawn.elems) := by
    rw [hx]; exact List.mem_singleton.2 rfl
  obtain ⟨r, hr, hxr⟩ := List.mem_flatMap.1 hm
  obtain ⟨pre, post, hpr⟩ := List.append_of_mem hr
  obtain ⟨xs, ys, hxs⟩ := List.append_of_mem hxr
  exact hc τ hclean hpass pre r post hpr xs x ys hxs

/-- **`Piece.Reads` from the degree.** -/
theorem reads_allErr (p : Piece (ckP .two) F S Cl W) (rd : Fmt.Ext → K) (d : ℕ)
    (hlog : ∀ r ∈ p.ds, r.entry.logN ≤ 64) (hback : ∀ r ∈ p.back, r.drawn.elems = [])
    (hinj : Function.Injective fun a : EV .two => rd (toU3 a))
    (herr : Err.le (allErr (fun _ _ => d) 0 p.ds) p.err) : p.Reads rd d :=
  reads_of_readsAll p rd d (readsAll_allErr p rd _ hlog hback hinj herr)

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.readsAll_of_countsAt
#print axioms VerifiableInference.Desc.Sound.countsAt_mono
#print axioms VerifiableInference.Desc.Sound.readsAll_allErr
#print axioms VerifiableInference.Desc.Sound.reads_of_readsAll
#print axioms VerifiableInference.Desc.Sound.reads_allErr
