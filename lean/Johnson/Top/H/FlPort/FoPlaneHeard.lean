-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/FlPort/FoPlaneHeard.lean: a carried copy, made by a program, not typed by hand.

Of which file: OnBytes/Tie/Pv/Lookup/Forest/FoPlaneHeard.lean, as it lies in this library.
What is carried: those of its declarations that depend on a context of the verifier program's
channel, and no other:
  planeClaims_heard
How: by one swap of names throughout: a context becomes a tape; a routine
of the program becomes the library's flat function of the same text (OnBytes/K/Kc/Flat.lean,
OnBytes/K/Kc/FlatHear.lean). The laws on "returns" are those of Johnson/Top/H/FlPort/Kit.lean. Every
other name is the library's own: plain records, pure functions and lemmas on them, used from where
they lie. Those of OnBytes/Tie/Pv/ that the text names, as far as a program sees them:
  HeardIs, Later, Later.refl, Sized, colsK, dgOf, endsOf, forN, forTrace, numsF, pinColK, rowRes,
  thetaOf
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
import OnBytes.Tie.Pv.Lookup.Forest.FoPlaneHeard
import Johnson.Top.H.FlPort.Kit
import Johnson.Desc.First.Look.LookPlanes
import Johnson.Top.H.FlPort.PscWhole
import Johnson.Top.H.FlPort.PscRun
import Johnson.Top.H.FlPort.FoPscForm
import Johnson.Top.H.FlPort.FoTieRun
import Johnson.Top.H.FlPort.FoHeard
import Johnson.Top.H.FlPort.FoPlaneAt
import Johnson.Top.H.FlPort.FoPlaneRead
import Johnson.Top.H.FlPort.FoPlaneClaims

set_option autoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open Cb Cb.Fo Cb.Fo.PlaneClaims VerifiableInference.Desc.First.Look
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.PscTie _root_.Fo

section
variable {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K)

theorem planeClaims_heard (g : Heard) (lm jLK : ℕ) (rsK : Rounds K) (bit : ℕ → ℕ → Fl Aff)
    (pin : ℕ → Fl Aff) (hb : ∀ e col, Quiet (bit e col)) (hp : ∀ col, Quiet (pin col))
    (F G : Fork) (c c' : Tape) (rows : Array Aff)
    (h : planeClaimsF g lm bit pin F c = .ok ((rows, G), c'))
    (hI : HeardIs ρ g F (endsOf g.shape lm jLK rsK)) (hok : FoNums.ok g.shape = true)
    (hF : Sized F) :
    c' = c ∧ Later F G ∧ Sized G ∧ G.next = F.next ∧
      ∃ r0 r1 r2, rows = #[r0, r1, r2] ∧
        ∀ H, Later G H → ∀ (μ : Pl → K) (entry : ℕ → ℕ → ℕ → K), μ .zero = 0 →
          (∀ col, col < g.shape.NC * 2 ^ (g.shape.kT + 5 - lm) →
            (got (bit 0 col) F c).value ρ (H.worldOf ρ (fun j => μ (.mask j)) entry) =
            colsK g.shape lm (endsOf g.shape lm jLK rsK).zb0 μ col) →
          (∀ col, col < g.shape.NC * 2 ^ (g.shape.kT + 5 - lm) →
            (got (bit 1 col) F c).value ρ (H.worldOf ρ (fun j => μ (.mask j)) entry) =
            colsK g.shape lm (endsOf g.shape lm jLK rsK).zb1 μ col) →
          (∀ col, col < g.shape.NC * 2 ^ (g.shape.kT + 5 - lm) →
            (got (pin col) F c).value ρ (H.worldOf ρ (fun j => μ (.mask j)) entry) =
            Pin.pinColK lm μ col) →
          r0.value ρ (H.worldOf ρ (fun j => μ (.mask j)) entry) =
              rowRes μ (rowEnd (forN g.shape lm jLK rsK) (forTrace g.shape lm jLK rsK)) ∧
          r1.value ρ (H.worldOf ρ (fun j => μ (.mask j)) entry) =
              -rowRes μ (rowBitE (forN g.shape lm jLK rsK) (forTrace g.shape lm jLK rsK)) ∧
          r2.value ρ (H.worldOf ρ (fun j => μ (.mask j)) entry) =
              rowRes μ (rowNum (forN g.shape lm jLK rsK)) := by
  obtain ⟨mu, zd, rs, hRan, _, hdg⟩ := hI.lvRan
  have hdg' : dgOf zd = dgE (numsF g.shape lm jLK (thetaOf g.shape rsK)) := by
    have e1 : dgOf zd = (zd.map fun p => p.2).map (· - 1) := by
      unfold dgOf
      rw [List.map_map]
      rfl
    rw [e1, hdg, List.map_map]
    have e2 : ((fun x : ℕ => x - 1) ∘ fun x => x + 1) = id := funext fun x => by simp
    rw [e2, List.map_id]
    rfl
  exact planeClaims_at ρ g lm jLK (thetaOf g.shape rsK) (forTrace g.shape lm jLK rsK) bit pin hb hp
    F F F G c c' rows h hok (Later.refl F) (Later.refl F) hF hRan hdg' hI.lvStart hI.lvTg hI.lvEps
    hI.lvFin hI.lvXs hI.leavesA hI.zb0 hI.zb1 hI.sBitAt

end

end Fo.Tp
