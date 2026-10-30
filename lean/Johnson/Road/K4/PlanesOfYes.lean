-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/PlanesOfYes.lean: BEHIND K4's HEARING AND ITS RUN "front": IF EVERY FORM OF THE
RUN's LIST IS WORTH 0 IN THE WORLD OF THE LEDGER BEHIND THE RUN, WITH TRUE READS OF THE PLANES'
THREE TABLES, THE LOOKUP's ITEM ON THE PLANES HOLDS AT THE LEDGER IN FRONT OF THE HEARING. One
statement with its proof, and two small ones beneath. Glue between files that are proved elsewhere:
no new argument.

  `hear_fo`: the lookup's record inside what the hearing returns is the one that it was handed (the
    `hear_calls`, `hearNorms_public`, `hearTerms_keeps`, OnBytes/Desc/First/K4/). It says
    what `own_fo` (Johnson/Road/K4/Slots/HearFills.lean) says, by the same proof: typed again here
    so that this file need not import that family.
  `hear_foLater`: the ledger G that the hearing hands on is later than the ledger F at which it was
    called, in the sense of `Fo.Later` (OnBytes/Tie/Pv/Lookup/Forest/FoForm.lean), and has arrays of
    the right sizes if F has (`hearFl_later`, OnBytes/Desc/First/K4/HearGrows.lean, whose
    `PscRun.Later` has `Fo.Later`'s three fields and that fourth).
  **`planes_of_yes`**: from the hearing's return at F, a ledger with arrays of the right sizes, the
    run's return at G, the zeros, `K4ReadsTrue` and the public test
    `FoNums.ok` on the heard shape: `K3OutPlanes` at the handed record fo and at F. It is
    `k4_planes_out_front` (Johnson/Top/H/K4PlanesWorth.lean), called at rows := false, with
    its premises on the two ledgers paid and o.H.fo written as fo.

Limits. THE ZEROS AND `K4ReadsTrue` ARE PREMISES; nothing shows that they can hold together. That F
is the ledger that the lookup's block left is not said here. One direction. Those of
K4PlanesWorth.lean. Nothing on soundness.
-/
import Johnson.Top.H.K4PlanesWorth
import OnBytes.Desc.First.K4.HearGrows
import OnBytes.Desc.First.K4.HearCalls
import OnBytes.Desc.First.K4.NormsPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub HPlan2 Own)
open OnBytes.PscRun (Sized)
open OnBytes.Desc.First.K4 (hear engFl formsFrontWith hear_calls hearNorms_public
  hearTerms_keeps hearFl_later)
open VerifiableInference.OnPublicFiles (K4ReadsTrue k4_planes_out_front)

variable {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F G : Fork} {t u : Tape} {o : Own}

/-- The lookup's record inside what the hearing returns is the one that it was handed. -/
theorem hear_fo (h : hear engFl P hp g fo F t = some (o, G, u)) : o.H.fo = fo := by
  obtain ⟨_, H1, G1, u1, G2, u2, h1, h2, _⟩ := hear_calls h
  obtain ⟨_, _, _, _, _, _, _, e1⟩ := hearNorms_public h1
  exact (hearTerms_keeps h2).1.trans e1

/-- The hearing leads to a later ledger, in the lookup's sense of the word, of the right sizes. -/
theorem hear_foLater (h : hear engFl P hp g fo F t = some (o, G, u)) :
    _root_.Fo.Later F G ∧ (Sized F → Sized G) := by
  have L := hearFl_later (P := P) (hp := hp) (g := g) (fo := fo) h
  exact ⟨⟨L.next, L.ns, L.keep⟩, L.sized⟩

/-- **The planes' item, behind K4's hearing and its run "front".** -/
theorem planes_of_yes {K : Type} [CommRing K] (ρ : Reading K) (hF : Sized F)
    (h : hear engFl P hp g fo F t = some (o, G, u)) {fs₁ : Array Aff} {F₁ : Fork}
    (hr : formsFrontWith false P g o G = some (fs₁, F₁)) (first : ℕ) (ν : _root_.Fo.Pl → K)
    (entry : ℕ → ℕ → ℕ → K) (hok : FoNums.ok fo.shape = true)
    (hz : ∀ f ∈ fs₁.toList, f.value ρ (F₁.worldOf ρ (fun j => ν (.mask j)) entry) = 0)
    (hT : K4ReadsTrue ρ o.v fo F₁ ν entry) :
    VerifiableInference.OnPublicFiles.K3OutPlanes fo.shape o.v.y.h.lmb first ν ρ fo F := by
  obtain ⟨hL, hS⟩ := hear_foLater h
  have e := hear_fo h
  have key := k4_planes_out_front ρ hr F first ν entry (by rw [e]; exact hok) (hS hF) hL hz
    (by rw [e]; exact hT)
  rw [e] at key
  exact key

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.hear_fo
#print axioms OnBytes.Road.K4.hear_foLater
#print axioms OnBytes.Road.K4.planes_of_yes
