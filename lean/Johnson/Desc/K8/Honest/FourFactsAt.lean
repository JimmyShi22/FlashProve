-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/FourFactsAt.lean: THE SMALLNESS TEST: THE BUNDLE `FourFacts`
(Johnson/Desc/K8/Honest/FourFacts.lean) FOLLOWS FROM THE SAME FACTS AT THE DATA THAT WHAT IS FIXED
IN FRONT OF THE BATCHING SHOWS: none of them reads one of the fourteen written fields that
`blank` lays over (Johnson/Desc/First/TailClaims/EquationsBlank.lean). So the bundle's "at every
data tl with that blanked form" asks no more than at one; and whoever pays it need name no state. A
definition and a lemma; none of the library's goals.

  `FourFactsAt π q y`   the bundle's twelve facts and its ∃, at every t₀ with (π q.1).1 = some t₀
                   (there is at most one), the snapshot v and what the lookup heard g
  **`fourFacts_of_at`**   FourFactsAt π q y → FourFacts u π q y, at every u
Limits. `FourFactsAt` IS A PREMISE, AS HEAVY AS THE BUNDLE: THAT AN HONEST STATE MEETS IT IS NOT
SAID HERE. Its three ties of the letters to the data's cells and mask row follow from named premises
(`ties_of_rest`, TiesOfRest.lean). IN A FILE THAT THE LIBRARY MAY NOT HOLD (FourFactsOfWorth.lean,
`fourFactsAt_of_worth`) the whole follows, in scope, under an opening and its test on its plan, at
every state that the blocks with the test on words in front reach in front of a batching, from the
library's two sentences "worth" and five named premises. One direction alone.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.K8.Honest.FourFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.First.K8.Honest
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.DgP Cb.Fo Cb.LdLkp Finset
open _root_.Fo _root_.Fo.Eq
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K9L (Pub9 Bound GE8 four8)
open VerifiableInference.Desc.EntryUnit (entUnit)
open VerifiableInference.Desc.K4Values (winOf InWin)

variable {α : Type}

/-- **The bundle at the data that are fixed.** -/
def FourFactsAt (π : α → Option HTailF2 × Option (Array HFun)) (q : α × Option Pub9)
    (y : Bound GE8) : Prop :=
  ∀ (tl : HTailF2) (v : Pub9) (g : Heard), (π q.1).1 = some tl → q.2 = some v →
    tl.heard = some g →
    (∀ cl ∈ four8 tl g, ∀ x ∈ cl.form.slots.toList,
      InWin (winOf g.leaves) x.1 ∨ OnBytes.PscRun.Filled v.F x.1) ∧
    tl.f9 = g.shape ∧ FoNums.ok g.shape = true ∧ TailOK tl ∧
    2 ^ g.shape.cK = g.shape.NC ∧ 5 ≤ g.shape.kT + g.shape.cK ∧
    (∀ c < 2, (g.zk.getD c #[]).size = (tl.zOf c).call.n) ∧
    (∀ c < 2, (tl.zOf c).call.n ≤ 63) ∧
    (∀ c < 2, ∀ p ∈ piecesL tl c, PieceOK tl c (tl.zOf c).call.n p) ∧
    (∀ c < 2, (piecesL tl c).Pairwise fun p p' =>
      p.off + 2 ^ p.b ≤ p'.off ∨ p'.off + 2 ^ p'.b ≤ p.off) ∧
    CoefOK tl v.F ∧
    (∀ a ∈ allPieces tl, a.2.r0 + a.2.Rp ≤ (v.F.trees.getD a.2.tree {}).R) ∧
    ∃ (jLK : ℕ) (F' : Fork) (J₀ : Type) (en : Ent3 → J₀) (mk : ℕ → J₀) (μ₀ : J₀ → GE8)
      (rs : Rounds GE8), _root_.Fo.Later F' v.F ∧
      (∀ r < 32, ∀ i < tl.bzColumns, entUnit q y tl.ix.BZ r i = μ₀ (en (tl.ix.BZ, r, i))) ∧
      (∀ c < 2, ∀ p ∈ piecesL tl c, ∀ r < p.Rp, ∀ i < p.Cp,
        entUnit q y tl.ix.ZZ (p.r0 + r) (p.c0 + i) = μ₀ (en (tl.ix.ZZ, p.r0 + r, p.c0 + i))) ∧
      (∀ k ∈ four8 tl g, ∀ s ∈ k.form.slots.toList, y.mask s.1 = μ₀ (mk s.1)) ∧
      HeardIs Reading.gl g F' (endsOf g.shape 5 jLK rs) ∧
      K3Planes g.shape 5 jLK (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p)) rs ∧
      K3Keys g.shape 5 jLK (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
        (forK GE8 (digL5 GE8 tl en mk jLK Unit) () (zext μ₀)) rs

/-- **None of the facts reads a written field.** -/
theorem fourFacts_of_at (u : HTailF2) (π : α → Option HTailF2 × Option (Array HFun))
    (q : α × Option Pub9) (y : Bound GE8) (H : FourFactsAt π q y) : FourFacts u π q y := by
  intro tl v g h1 h2 hg
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, jLK, F', J₀, en, mk, μ₀, rs, b1, b2,
    b3, b4, b5, b6, b7⟩ := H (blank u tl) v g h1 h2 hg
  exact ⟨a1, a2, a3, ⟨a4.port, a4.nc, a4.pc, a4.rows, a4.one, a4.cnt⟩, a5, a6, a7, a8,
    fun c hc p hp =>
      have k := a9 c hc p hp
      ⟨k.tree, k.c0, k.le, k.pw, k.rp, k.b, k.bn, k.dvd, k.fit⟩,
    a10, a11, a12, jLK, F', J₀, en, mk, μ₀, rs, b1, b2, b3, b4, b5, b6, b7⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.fourFacts_of_at
#print axioms VerifiableInference.Desc.First.K8.Honest.FourFactsAt
