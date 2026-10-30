-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/LookOfLeft.lean: WHAT THE LOOKUP's RECORD OF WHAT IT LEFT GIVES TO THE PROMISE IN
FRONT OF K4's BLOCK. Statements and proofs: read off the lookups' record `K3Left` and its
two promises `K3LeftAt`, `K3LeftOn` (Johnson/Top/H/K3LeftStatement.lean) and `PadLeft`
(OnBytes/Tie/Pv/Lookup/Port/FoHeard.lean). No new argument.

  `look_of_left`: from `K3Left ρ h lm F F' g rs`, the plan's own shape of the lookup being h
    (Pp.y.fo = h), h being s0 but for its field pub, a ledger G later than F' and the public test
    `FoNums.ok h`: the five lines `LookLines Pp g s0` (Johnson/Road/K4/PubAt.lean); every slot that
    the form g.cEnd names is there and filled in G; that form names no entry; the heard shape
    passes the test.
  `next_of_leftAt`: UNDER THE SHARP PROMISE `K3LeftAt` (the ledger in hand IS the one that the
    lookup left) THE LEDGER's NEXT FREE SLOT IS first + Forest.elems h: one number, of the letters
    first and h alone; and the ledger has arrays of the right sizes.
  `next_le_of_leftOn`: under the promise that stands at every later record, `K3LeftOn`, only
    first + Forest.elems h ≤ next.
  **`front_of_leftAt`**: these at a seat L of K4's block (OnBytes/Desc/First/K4/Steps.lean), the
    sharp promise read through `L.fork` and `L.look`.

On s0 and h. `LookLines`' s0 is meant as what `Forest.shape` returns at the plan's calls, whose
field pub is empty; the lookups' h (`Look.P.shape`, Johnson/Desc/First/Look/LookKind.lean) and the
plan's `Lay.fo` (OnBytes/Model/LayerLayout.lean) are such a return with the field pub laid.
`LookLines` reads of s0 the fields NC and calls alone.

Limits. `K3Left`, `K3LeftAt`, `K3LeftOn` ARE PREMISES: that a yes of the lookup's block leaves them
is K3's files' to show. That K4's block stands directly behind the lookup's, so that the sharp
promise is the one in front of it, is the description's order: not said here. `first` IS A LETTER:
that it is the plan's number is not said here. hh, hs, hok are premises on public numbers. One
direction. Nothing on soundness.
-/
import Johnson.Top.H.K3LeftStatement
import Johnson.Road.K4.PubAt
import OnBytes.Desc.First.K4.Steps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Pub)
open OnBytes.Desc.First.K4 (Seat)
open VerifiableInference.OnPublicFiles (K3Left K3LeftAt K3LeftOn)

/-- "Every slot that the form names is there and filled" passes to a later ledger. -/
theorem filledA_later {F G : Fork} {a : Aff} (h : _root_.Fo.Later F G)
    (ha : _root_.Fo.FilledA F a) : _root_.Fo.FilledA G a := fun x hx =>
  ⟨by rw [h.ns]; exact (ha x hx).1, (h.keep x.1 (ha x hx).2).1⟩

/-- **What the lookup left, in the letters of the promise in front of K4's block.** -/
theorem look_of_left {K : Type} [CommRing K] {ρ : Reading K} {h s0 : Forest.Shape} {lm : ℕ}
    {F F' G : Fork} {g : Forest.Heard} {rs : _} (L : K3Left ρ h lm F F' g rs) {Pp : Pub}
    (hh : Pp.y.fo = h) (hs : ∃ pb, h = { s0 with pub := pb }) (hG : _root_.Fo.Later F' G)
    (hok : FoNums.ok h = true) :
    LookLines Pp g s0 ∧ _root_.Fo.FilledA G g.cEnd ∧ g.cEnd.ents = #[] ∧
      FoNums.ok g.shape = true := by
  have hN : s0.NC = h.NC := by
    obtain ⟨pb, rfl⟩ := hs
    rfl
  have hc : s0.calls = h.calls := by
    obtain ⟨pb, rfl⟩ := hs
    rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, filledA_later hG L.cEndFilled, L.cEndEnts, ?_⟩
  · rw [hh]
    exact L.zx
  · rw [hh]
    exact L.zy
  · rw [hh]
    apply Array.ext
    · simp [L.zkSize]
    · intro i h1 h2
      have hi : i < h.NC := by
        rw [← L.zkSize]
        exact h1
      have e := (L.zkRaw i hi).2
      have e' : g.zk.getD i #[] = g.zk[i] := by simp [Array.getD, h1]
      rw [e'] at e
      simp only [Array.getElem_map, Array.getElem_range]
      exact e
  · rw [hh]
    exact L.eRaw
  · rw [List.all_eq_true]
    intro q hq
    rw [beq_iff_eq, hc]
    exact L.zkLen q (by rw [← hN]; exact List.mem_range.mp hq)
  · rw [L.shape]
    exact hok

/-- **Under the sharp promise the next free slot is one number.** -/
theorem next_of_leftAt {S : Type} {fork : S → Option Fork} {heard : S → Option Forest.Heard}
    {h : Forest.Shape} {lm first : ℕ} {Q : Fork → Prop} {s : S}
    (H : K3LeftAt fork heard h lm first Q s) :
    ∃ F' g, fork s = some F' ∧ heard s = some g ∧ F'.next = first + Forest.elems h ∧
      PscRun.Sized F' := by
  obtain ⟨F, F', g, rs, _, hf, L, hh, hk⟩ := H
  exact ⟨F', g, hk, hh, by rw [L.padLeft.next, hf], L.padLeft.fit⟩

/-- Under the promise that stands at every later record: a bound from below alone. -/
theorem next_le_of_leftOn {S : Type} {fork : S → Option Fork} {heard : S → Option Forest.Heard}
    {h : Forest.Shape} {lm first : ℕ} {Q : Fork → Prop} {s : S}
    (H : K3LeftOn fork heard h lm first Q s) :
    ∃ G g, fork s = some G ∧ heard s = some g ∧ first + Forest.elems h ≤ G.next ∧
      PscRun.Sized G := by
  obtain ⟨F, F', G, g, rs, _, hf, L, hh, hk, hL, hS⟩ := H
  exact ⟨G, g, hk, hh, by rw [← hf, ← L.padLeft.next]; exact hL.next, hS⟩

/-- **The sharp promise at a seat of K4's block: the ledger's sizes, its next free slot, and what
the lookup left.** -/
theorem front_of_leftAt {T : Type} (L : Seat T) {h s0 : Forest.Shape} {lm first : ℕ}
    {Q : Fork → Prop} {s : T} (H : K3LeftAt (fun s => some (L.fork s)) L.look h lm first Q s)
    {Pp : Pub} (hh : Pp.y.fo = h) (hs : ∃ pb, h = { s0 with pub := pb })
    (hok : FoNums.ok h = true) :
    PscRun.Sized (L.fork s) ∧ (L.fork s).next = first + Forest.elems h ∧
      ∀ fo, L.look s = some fo →
        LookLines Pp fo s0 ∧ _root_.Fo.FilledA (L.fork s) fo.cEnd ∧ fo.cEnd.ents = #[] ∧
          (∀ y ∈ fo.cEnd.slots.toList, y.1 < (L.fork s).ns) ∧ FoNums.ok fo.shape = true := by
  obtain ⟨F, F', g, rs, _, hf, K, hl, hk⟩ := H
  obtain rfl : L.fork s = F' := Option.some.inj hk
  refine ⟨K.padLeft.fit, by rw [K.padLeft.next, hf], fun fo e => ?_⟩
  obtain rfl : g = fo := Option.some.inj (hl.symm.trans e)
  obtain ⟨a, b, c, d⟩ := look_of_left K hh hs (_root_.Fo.Later.refl _) hok
  exact ⟨a, b, c, fun y hy => (b y hy).1, d⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.look_of_left
#print axioms OnBytes.Road.K4.next_of_leftAt
#print axioms OnBytes.Road.K4.next_le_of_leftOn
#print axioms OnBytes.Road.K4.front_of_leftAt
