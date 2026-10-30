-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/FlPort/FoPlaneRead.lean: a carried copy, made by a program, not typed by hand.

Of which file: OnBytes/Tie/Pv/Lookup/Forest/FoPlaneRead.lean, as it lies in this library.
What is carried: those of its declarations that depend on a context of the verifier program's
channel, and no other:
  planeClaims_rows
How: by one swap of names throughout: a context becomes a tape; a routine
of the program becomes the library's flat function of the same text (OnBytes/K/Kc/Flat.lean,
OnBytes/K/Kc/FlatHear.lean). The laws on "returns" are those of Johnson/Top/H/FlPort/Kit.lean. Every
other name is the library's own: plain records, pure functions and lemmas on them, used from where
they lie. Those of OnBytes/Tie/Pv/ that the text names, as far as a program sees them:
  FormIs, Later, LedAt, Sized, countAff_value, countK, dgOf, leaves, muOf, planesAff_value,
  planesK, rowRes, sBit
The comments on the declarations are the library's, under the same swap: where they say "run" or
"view", read: on a tape.

Limits. What is proved here is proved of the flat functions alone, and a flat function tests less of
the plan than the program's routine (the paragraph "Not claimed" in the head of
OnBytes/K/Kc/Flat.lean). Nothing is said where a function refuses. A tie: it has no error term. If
the source file turns, this copy does not follow by itself. In the list of names a use by dot
notation on a hypothesis is not seen, and a short name may stand once too often. That no routine
in a context is reached from a statement or a proof here is meant, and is not shown in this
library.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPlaneRead
import Johnson.Top.H.FlPort.Kit
import Johnson.Desc.First.Look.LookPlanes
import Johnson.Top.H.FlPort.PscWhole
import Johnson.Top.H.FlPort.PscRun
import Johnson.Top.H.FlPort.FoPscForm
import Johnson.Top.H.FlPort.FoTieRun
import Johnson.Top.H.FlPort.FoPlaneClaims

set_option autoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open Cb Cb.Fo Cb.Fo.PlaneClaims VerifiableInference.Desc.First.Look
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.PscTie _root_.Fo

section
variable {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K)

theorem planeClaims_rows (g : Heard) (lm : ℕ) (bit : ℕ → ℕ → Fl Aff) (pin : ℕ → Fl Aff)
    (hb : ∀ e col, Quiet (bit e col)) (hp : ∀ col, Quiet (pin col))
    (F0 F G : Fork) (c c' : Tape) (rows : Array Aff)
    (h : planeClaimsF g lm bit pin F c = .ok ((rows, G), c'))
    {first : ℕ} {mu eps : E} {zd : List (E × ℕ)} {rs : List (List E × E)}
    (hR : Ran g.leaves first mu eps zd rs) {tg : K} {inc : List (Pl × K)}
    (hC : FormIs ρ F0 g.leaves.start tg inc) (ht : ρ.val g.leaves.target = tg)
    (h0 : Later F0 F) (hF : Sized F) {L : Led Pl} {n : ℕ} (hL : LedAt L first (dgOf zd) n)
    (hv : g.shape.v < 64) (vals : List K) :
    (planeCols g.shape lm).toBool = true ∧ c' = c ∧ Later F G ∧ Sized G ∧ G.next = F.next ∧
      ∃ r0 r1 r2, rows = #[r0, r1, r2] ∧
        ∀ H, Later G H → ∀ (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K),
          r0.value ρ (H.worldOf ρ mask entry) =
              rowRes (muOf mask) (rowU L (dgOf zd)
                ⟨ρ.val g.leaves.eps, g.leaves.r.toList.map ρ.val, ρ.val g.leaves.claim, vals⟩
                inc 1) +
              ρ.val eps * (ρ.val g.leavesA * planesK g.shape lm (rdL ρ g.zb0) fun col =>
                (got (bit 0 col) F c).value ρ (H.worldOf ρ mask entry)) ∧
          r1.value ρ (H.worldOf ρ mask entry) =
              (H.worldOf ρ mask entry).slot g.sBit - planesK g.shape lm (rdL ρ g.zb1) (fun col =>
                (got (bit 1 col) F c).value ρ (H.worldOf ρ mask entry)) ∧
          r2.value ρ (H.worldOf ρ mask entry) =
              Pin.countK g.shape lm fun col =>
                (got (pin col) F c).value ρ (H.worldOf ρ mask entry) := by
  obtain ⟨hm, row, p', h5, hr⟩ := planeClaims_run g lm bit pin hb hp F G c c' rows h
  obtain ⟨a1, a2, a3, a4, _, a6⟩ := row_form ρ hR h5 hC ht h0 hF hL vals
  refine ⟨hm, a1, a2, a3, a4, row, _, _, hr, fun H hH mask entry => ⟨?_, ?_, ?_⟩⟩
  · rw [a6 H hH mask entry, Aff.value_scale, planesAff_value, ρ.one]
    rfl
  · rw [Aff.value_sub, Aff.value_slot, planesAff_value]
    rfl
  · exact countAff_value ρ _ g lm _ hv

end

end Fo.Tp
