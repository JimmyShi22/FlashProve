-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place of a stored set is shown at which all premises hold together.
Johnson/Desc/First/Look/K3CallsRides.lean: the lookup on a link's CALLS AT THE TABLE OF JOINTS: ONE
NAMED PREMISE OF THE ROW (AttAtTable's and LayAtTable's pinBack) AND THREE OF THE PROMISE BEHIND
(BehindParts' bHeld, bShown, bNoColl, Johnson/Desc/First/Look/K3CallsBehind.lean) AT THE TABLE's OWN
FILLING OF ITS LETTERS ON THE READING OF THE ORACLES (pinJT, shownJT, noCollJT,
Johnson/Desc/Sound/MeaningSig.lean; smpHeld): EACH A CALL OF THE KIND-FREE RULE
(Johnson/Desc/Sound/SigRides.lean), over a list of seats, at a piece over the carried record and a
fixed public part. Statements and proofs. Ties: no error term. NO SOUNDNESS IS CLAIMED.

OBJECT: no text that runs: the table's letters pin, shown, noColl, held at meaningSig's filling.
USER: K3CallsAt.lean, K3CallsAtR.lean, K3DigitsAtSig.lean, K3MeansDigR.lean.
LETTERS: general in the piece: nothing of the kind "lookup" is spent; pi: a fixed public part: the
  rule has one type for the record: it is called at the carried record, with the reader of samples
  fun s => smpT (pi, s).

Main names: `calls_pinBack` · `calls_shown` · `calls_noColl` · `sameBut_held`.

ITS PREMISES: `hbase`: every seat of the list lies in a tree below the piece's base: A BOOL ON THE
PLAN · `hsm`: a yes leaves the sample of every member of ms as it was.

Limits. NEITHER IS SHOWN AT ANY PLAN OR FILLING.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.SigRides
import Johnson.Desc.First.Look.K3CallsTurns

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Maker Fo.Peel Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc (Strs smpHeld)
open VerifiableInference.Desc.Sound
open _root_.Run.PQ (CK)

section
variable {P S Cl W Cells Tok Xi : Type} {C : CK} {Fr : Frame} (cs : Codes)
  (G : Desc.FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smpT : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (pi : P)

/-- **pinBack: the pins of tenants that stand in front of the piece ride back over its yes.** -/
theorem calls_pinBack (p : Piece C Fr S Cl W) (sent : List (ℕ × ℕ))
    (hbase : ∀ t ∈ sent, t.1 < p.base)
    (hsm : ∀ a τ c, p.ior.red.out a τ = some c → ∀ x ∈ ms,
      smpT (pi, c.1) x.1 x.2 = smpT (pi, a.1) x.1 x.2)
    (a c : S × Fr.E.Str) (w : Desc.Wit Cells Tok MsgT) (hy : ∃ τ, p.ior.red.out a τ = some c)
    (h : ∀ t ∈ sent, pinJT cs G arr smpT ms t.1 t.2 (pi, c.1) (strsOf Fr c.2) w) :
    ∀ t ∈ sent, pinJT cs G arr smpT ms t.1 t.2 (pi, a.1) (strsOf Fr a.2) w := by
  obtain ⟨τ, hc⟩ := hy
  intro t ht
  exact (pinJT_rides cs G arr (fun s => smpT (pi, s)) p ms t.1 t.2 (hbase t ht) a c τ hc
    (fun x hx _ => hsm a τ c hc x hx) w).1 (h t ht)

/-- **shown rides forward over a yes.** -/
theorem calls_shown (p : Piece C Fr S Cl W) (sent : List (ℕ × ℕ))
    (hbase : ∀ t ∈ sent, t.1 < p.base) (a c : S × Fr.E.Str)
    (hy : ∃ τ, p.ior.red.out a τ = some c) :
    ∀ t ∈ sent, shownJT cs G ms t.1 t.2 (strsOf Fr a.2) →
      shownJT cs G ms t.1 t.2 (strsOf Fr c.2) := by
  obtain ⟨τ, hc⟩ := hy
  intro t ht h
  exact shownJT_rides cs G p ms t.1 t.2 (hbase t ht) a c τ hc h

/-- **no collision rides forward over a yes.** -/
theorem calls_noColl (p : Piece C Fr S Cl W) (sent : List (ℕ × ℕ))
    (hbase : ∀ t ∈ sent, t.1 < p.base)
    (hsm : ∀ a τ c, p.ior.red.out a τ = some c → ∀ x ∈ ms,
      smpT (pi, c.1) x.1 x.2 = smpT (pi, a.1) x.1 x.2)
    (a c : S × Fr.E.Str) (hy : ∃ τ, p.ior.red.out a τ = some c) :
    ∀ t ∈ sent, noCollJT cs G smpT ms t.1 t.2 (pi, a.1) (strsOf Fr a.2) →
      noCollJT cs G smpT ms t.1 t.2 (pi, c.1) (strsOf Fr c.2) := by
  obtain ⟨τ, hc⟩ := hy
  intro t ht h
  exact noCollJT_rides cs G (fun s => smpT (pi, s)) p ms t.1 t.2 (hbase t ht) a c τ hc
    (fun x hx _ => hsm a τ c hc x hx) h

end

/-- **held rides**: what SameBut leaves holds the same samples. -/
theorem sameBut_held {s s' : Desc.First.S} (h : SameBut s s') (j t : ℕ) :
    smpHeld s'.st s'.book j t = smpHeld s.st s.book j t :=
  smpHeld_rides s.st s'.st s.book s'.book j t h.st h.book

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.calls_pinBack
#print axioms VerifiableInference.OnPublicFiles.calls_shown
#print axioms VerifiableInference.OnPublicFiles.calls_noColl
#print axioms VerifiableInference.OnPublicFiles.sameBut_held
