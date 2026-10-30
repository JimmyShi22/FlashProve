-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/KeyLaw/HeardView.lean: a hearing of the kind "lookup" that returns has read
messages whose items are all elements: so on its stretch the reading flatRV of Statement.lean is the
library's reading of a view's rounds; and taking the sealed digest out of a round changes neither.

Main names:
  tape_elems: a stretch that the strict tape takes: every round's items are elements.
  heard_flat: a hearing that returns: flatRV rs = rs.map (Fo.rdRV Reading.gl).
  read_noDigest: the library's reading does not see the sealed digest.
  lamS_out_heard: THE TYPED LOOKUP's OUT AT THE IMAGE of a written transcript is lamRun at flatRV of
    the rounds that the block was shown, where the hearing on these returns.

Limits. Those of ViewAt.lean.

-/
import Johnson.Desc.First.Look.KeyLaw.ViewAt
import Johnson.Desc.First.Look.KeyLaw.Out

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open Iop OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Maker OnBytes.K.Kc
open _root_.Run (ckP)
open OnBytes.Model (Reading Fork)
open Lk6 (Dat Pl)
open Fo.Peel (MeetsT NoAns)

/-- A stretch that the strict tape takes: every round's items are elements. -/
theorem tape_elems : ∀ (rs : List Fmt.RoundView) (es : List Fmt.Entry) (t : Tape),
    First.Tape.tapeT {} rs es = some t → ∀ r ∈ rs, (First.Tape.elemsOf r.vals).isSome
  | [], _, _, _ => fun r hr => (by cases hr)
  | _ :: _, [], t, h => by cases h
  | r :: rs, e :: es, t, h => by
    unfold First.Tape.tapeT at h
    cases h1 : First.Tape.roundT {} r e with
    | none => rw [h1] at h; cases h
    | some x =>
      cases h2 : First.Tape.tapeT {} rs es with
      | none => rw [h1, h2] at h; cases h
      | some t' =>
        intro r' hr'
        rcases List.mem_cons.1 hr' with rfl | hr'
        · unfold First.Tape.roundT at h1
          cases h3 : First.Tape.elemsOf r'.vals with
          | none => rw [h3] at h1; cases h1
          | some _ => rfl
        · exact tape_elems rs es t' h2 r' hr'

/-- **A hearing that returns.** -/
theorem heard_flat {f : Face} {es : List Fmt.Entry} {F G : Fork} {rs : List Fmt.RoundView} {g : HeardG}
    (h : hearE f es F rs = some (g, G)) : flatRV rs = rs.map (Fo.rdRV Reading.gl) := by
  obtain ⟨-, t, ht, -⟩ := hearE_inv h
  exact flat_read rs (tape_elems rs es t ht)

/-- The library's reading does not see the sealed digest. -/
theorem read_noDigest (rs : List Fmt.RoundView) :
    (rs.map noDigest).map (Fo.rdRV Reading.gl) = rs.map (Fo.rdRV Reading.gl) := by
  rw [List.map_map]
  rfl

/-- **The typed lookup's out at the image of a written transcript**, where the hearing returns on
the rounds that the block was shown. -/
theorem lamS_out_heard (A : Dat GE) (P : Pl A) (Ex : ExtSpec) (ds : List RDT)
    (hM : List.Forall₂ MeetsT ds ((Lk6.lamS_runs A P Ex).rd.fms.map spOf))
    (hA : ∀ d ∈ ds, NoAns d.items) (st : A.St) (y : Ex.Str) (τ : Tr (uLT (ckP .two) ds))
    {f : Face} {es : List Fmt.Entry} {F G : Fork} {g : HeardG}
    (h : hearE f es F ((rvT (ckP .two) ds τ).map noDigest) = some (g, G)) :
    (A.lamS P Ex).R.out st y ((mapsOf (Lk6.lamS_runs A P Ex).rd ds hM.length_eq).view τ) =
      some (A.lamRun P st (flatRV ((rvT (ckP .two) ds τ).map noDigest))) := by
  rw [lamS_out_at A P Ex ds hM hA, heard_flat h, read_noDigest]

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.heard_flat
#print axioms VerifiableInference.Desc.K3.KeyLaw.lamS_out_heard
