-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/HpubAtFull.lean: hpub_of
AT THE FULL SIZE's WRITTEN LIST OF PLACES: its premise hT on the table is laid
in by the kernel's fact tied_reads_full. One statement with its proof.
What is not claimed. hMg, hP, hRd and hfound stay. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.HpubOf
import Johnson.Desc.K1.Law.FormsAtFifty

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open Iop Run OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc.First (S Pub Meaning PubData pubAll flatPlacesOf)
open VerifiableInference.Desc.K13.Law (openAt)
open VerifiableInference.Desc.Sound (Frame linksFull)
open IM (k1Ix)

variable {Pp W Cl : Type} {F : Frame}

/-- **The tied public items that come at link l's reads' place hold behind the piece's accepting
run.** -/
theorem hpub_reads_full (D : PubData) (base0 : Pub → Pp × S → Bool) (Mg : Meaning Pp W)
    (hMg : Mg.pub = pubAll D base0) (l : ℕ) (hl : l < 25) (P : Par) (B : Block S Unit)
    (hS : LaterSend P B) (h2 : B.rounds.length = 2) (c : Block S Cl)
    (hu : c.UnderR (B.retype : Block S Cl)) (base : ℕ) (d₁ d₂ : RDT) (cc e : ℕ) (z : Pp) (t : ℕ)
    (ht : t < 3)
    (hP : laterSeatsB D.N P l t
      (D.N.treesAt (flatPlacesOf linksFull true)[14 * l + k1Ix l false + 2]?) = true)
    (hRd : ∀ (s s' : S) rs gs j r, rs.length = 2 → B.decide s rs gs = .ok s' →
      Pub.formsInT l j r ∈ First.pubOfItems
        (openAt linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l false + 2)) →
      ReadersStay D l j r s s')
    (hfound : ∀ (s s' : S) rs gs, rs.length = 2 → B.decide s rs gs = .ok s' →
      SecondFound (idsOf P s.st.oracles.size).toList s s') :
    ∀ (a : S × F.E.Str) τ x,
      Sound.onQ D.N Mg linksFull (flatPlacesOf linksFull true) (fun s : S => (z, s))
        (14 * l + k1Ix l false + 2) a → a.1.failed = none →
      (sendPiece (W := W) (F := F) c base d₁ d₂ cc e).ior.red.out a τ = some x →
      ∀ q ∈ tiedAt linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l false + 2),
        Mg.pub q (z, x.1) = true :=
  hpub_of D base0 Mg hMg linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l false + 2) P B hS
    h2 c hu base d₁ d₂ cc e z l t ht hP _ (tied_reads_full l hl) hRd hfound

end VerifiableInference.Desc.K1
