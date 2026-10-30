-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3RoundsAt.lean: the kind "lookup" (K3): THE ROUNDS OF A LOOKUP AT A PLACE,
IN ONE THEOREM, GENERAL IN THE PLACE (the calls' lookups and the digits'): written rounds that are,
one by one, the kind's own declared rounds have the proved block's shape; the least errors that bear
the proved block's exist; they bear them; each is at most 2^-128 of its written round's own
challenge values; and so they are at most the cap. Statements with their proofs. It imports nothing
of the rule of composition. NO SOUNDNESS OF ANY TEXT THAT RUNS IS CLAIMED.

Why. Johnson/Desc/First/Look/K3CallerErr128.lean has the price alone, with the shape, the errors'
existence and that they bear the typed ones as premises or in other files. Here they are joined.

Main names.
  k3_shape_ok: a yes of the kind's own P.shape passes the library's test FoNums.ok.
  k3_rounds_at r p: from p.shape = some r.c.h, 1 < r.c.h.NC, p.entries.isSome and
    Forall₂ SameAs ds p.rounds, AT EVERY CALLER r, WITH ANY RIDERS:
    Forall₂ MeetsT ds (specF r.c.h) ∧ ∃ ε', bearT ds _ ε = some ε' ∧ BearsT ds _ ε ε' ∧
    Err.Below ε' (2⁻¹ ^ 128) ∧ Err.le ε' (Err.cap 128 _), where ε is the proved block's list of
    errors at r.
  k3_rounds_at_digits: at the closed caller of a link's digits, under DigOK.
NO WORK. The lookup has no round of positions. The bound takes nothing from a round's test bits: it
holds at whatever number of them the setting lays (K3CallerErrW.lean's below_plain drops that
factor): where a round has W test bits the true share is smaller still, and none of that is counted.
Limits. ROUND BY ROUND: no sum over the rounds is bounded; whoever adds over rounds must add the
form at 2^-157 (K3CallerErrW.lean). A LAW AT LETTERS: at no number evaluated here. The counts are
the typed proved block's, each times its written round's sampler's bound: they are not counts of bad
challenges of a text that runs. That written rounds with SameAs exist at all is not shown here. That
a piece's written rounds are the declared ones (SameAs) is owed by whoever cuts the file's rounds. A
lookup with one call alone (NC = 1: no round that draws a shift) is not covered. Nothing on the
sending's, the closing's or the batching's errors; nothing on the hash.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3DigRounds
import Johnson.Top.H.LookupCRideRows
import Iop.ErrCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look
open scoped ENNReal

/-- A typed shape that has a reader for each member of a spec is as long as the spec. -/
private theorem shape_len : ∀ (s' : Shape) (sp : List Tw.RSp), Rds s' sp → s'.length = sp.length
  | [], [], _ => rfl
  | _ :: s', _ :: sp, R => congrArg (· + 1) (shape_len s' sp R.2)
  | [], _ :: _, R => nomatch R
  | _ :: _, [], R => nomatch R

/-- A yes of the kind's own P.shape passes the library's test on the record. -/
theorem k3_shape_ok {p : Desc.First.Look.P} {h : Forest.Shape} (hs : p.shape = some h) :
    FoNums.ok h = true := by
  obtain ⟨h₀, a, b, e⟩ := shape_made hs
  rw [e]
  exact Cb.Fo.shape_ok a b

/-- **THE ROUNDS OF A LOOKUP AT A PLACE.** -/
theorem k3_rounds_at (r : LookupCRCaller) (p : Desc.First.Look.P) (hs : p.shape = some r.c.h)
    (hN : 1 < r.c.h.NC) (hr : p.entries.isSome = true) (ds : List RDT)
    (hR : List.Forall₂ SameAs ds p.rounds) :
    List.Forall₂ MeetsT ds (specF r.c.h) ∧
      ∃ ε' : Err (uLT (ckP .two) ds), bearT ds _ ((kLookupCRN [r]).ε r) = some ε' ∧
        BearsT ds _ ((kLookupCRN [r]).ε r) ε' ∧ Err.Below ε' ((2 : ℝ≥0∞)⁻¹ ^ 128) ∧
        Err.le ε' (Err.cap 128 (uLT (ckP .two) ds)) := by
  have hok := k3_shape_ok hs
  have hE := entries_forEnts hs hok hN hr
  have hpl : ∀ q ∈ p.rounds, EntPlain q.entry := fun q hq =>
    entPlain_forEnts _ _ _ (by
      rw [← hE]
      exact List.mem_map.2 ⟨q, hq, rfl⟩)
  have hP := same_all hR hpl
  have he := same_entries hR
  have hv : 1 ≤ r.c.h.v := by
    rw [Cb.Fo.ok_v hok]
    omega
  have hM := meets_declared hs hv hN hr ds hP he
  have hl : ds.length = ((kLookupCRN [r]).R r).shape.length :=
    hM.length_eq.trans (shape_len _ _ (rkFor r.c.h r.c.L r.c.Ex).R).symm
  obtain ⟨ε', e⟩ := Option.isSome_iff_exists.1 (bearT_some _ _ ((kLookupCRN [r]).ε r) hl)
  have hB : Err.Below ε' ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
    lookupC_written128 [r.c]
      (fun c hc => by
        obtain rfl := List.mem_singleton.1 hc
        exact hok)
      r.c (List.mem_singleton.2 rfl) _ ds hP (he.trans hE) ε' e
  exact ⟨hM, ε', e, bearT_bears _ _ _ _ e, hB, Err.le_cap_of_below_inv 128 ε' hB⟩

/-- **The same at the closed caller of a link's digits.** -/
theorem k3_rounds_at_digits {set : Params.Setting} {x : Desc.First.Look.Place} {tl : HTailF2}
    {D : Desc.First.Look.Sent} {rad : OracleShape → ℕ} {pp : ℕ} (H : DigOK set x tl D rad pp)
    (ds : List RDT)
    (hR : List.Forall₂ SameAs ds (Desc.First.Look.P.ofPlace set true x).rounds) :
    List.Forall₂ MeetsT ds (specF tl.f9) ∧
      ∃ ε' : Err (uLT (ckP .two) ds),
        bearT ds _ ((kLookupCRN [noRider (digCaller x tl D rad extNone Unit)]).ε
          (noRider (digCaller x tl D rad extNone Unit))) = some ε' ∧
        BearsT ds _ ((kLookupCRN [noRider (digCaller x tl D rad extNone Unit)]).ε
          (noRider (digCaller x tl D rad extNone Unit))) ε' ∧
        Err.Below ε' ((2 : ℝ≥0∞)⁻¹ ^ 128) ∧ Err.le ε' (Err.cap 128 (uLT (ckP .two) ds)) :=
  k3_rounds_at (noRider (digCaller x tl D rad extNone Unit)) _ H.shape
    (by
      show 1 < tl.f9.NC
      rw [(DgP.shape2_parts H.tail).2.1.nc]
      decide)
    H.rounds ds hR

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_shape_ok
#print axioms VerifiableInference.OnPublicFiles.k3_rounds_at
#print axioms VerifiableInference.OnPublicFiles.k3_rounds_at_digits
