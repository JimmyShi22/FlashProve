-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/FourZero.lean: THE SMALLNESS TEST: THE FIRST FOUR CLAIMS OF A YES OF THE RUN
"K8.equations" ARE WORTH 0 AT THE ENTRIES AT WHICH THE LIBRARY VALUES THEM OFF WHAT IS FIXED IN
FRONT OF THE BATCHING's DRAW (`LinkJoin.ent4`, Johnson/Desc/First/Link/Law/FullFour.lean), WHERE THE
LOOKUP ON THE DIGITS STANDS AND ITS TWO ITEMS "planes" AND "keys" HOLD. A joining of
Johnson/Desc/K8/Honest/Ent4Rows.lean and FourBack.lean with four of the library's own laws. Lemmas;
none of the library's goals.

  `sameZ_blank`   the data of the test and the same with the fourteen written fields blanked have
                   the same numbers of the arrays, the same two calls and have heard the same
  **`digRows_ent4`**   SO, AT THE RUN's OWN DATA tl: DigRows Reading.gl tl g (ent4 π q y) ‹the
                   data's cells›: by the library's `digRows_of_law` (Johnson/Top/H/K3OutRows.lean)
                   at tlX := blank u tl, Fc := the snapshot's ledger
  **`four_zero_ent4`**   equations front tl funs F = .ok (tl', F1, cls) → … → ∀ k ∈ cls.take 4, valC
                   Reading.gl (H.worldOf Reading.gl y.mask (ent4 π q y)) k = 0, at every ledger H
                   later than F1
THE LETTERS en, mk, μ₀ (in which the lookup's two items are stated) ARE FREE; THREE TIES ARE
PREMISES, each only where the four claims read: hcb, hcz: the data's cells of the array of planes
and of the pieces are μ₀ ∘ en · hm4: the data's mask row under the slots that the four name is μ₀ ∘
mk.
Limits. AN IMPLICATION WITH MANY PREMISES, NONE PAID HERE: beside the three ties: that what is fixed
shows the run's data blanked (h1), the snapshot (h2); the library's promise on the snapshot's ledger
(T, hRw); the public facts on the shape and the pieces (hs, hok, hT, hfull, h5, hn, h63, hP, hD);
that the run's ledger has its sizes and is later than the lookup's (hF, h0); ONE rs at which the
heard structure stands and both items hold (hI, hPl, hK). The world is H.worldOf …: not yet the one
in which the library's term values the claims (its slots are read off the snapshot's ledger).
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.K8.Honest.Ent4Rows
import Johnson.Desc.K8.Honest.FourBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.First.K8.Honest
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.DgP Cb.Fo Cb.LdLkp Finset
open _root_.Fo _root_.Fo.Eq
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.K8.Four (first_four)
open VerifiableInference.Desc.K9L (Pub9 Bound GE8)
open VerifiableInference.Desc.LinkJoin (ent4)
open VerifiableInference.Desc.EntryUnit (entUnit)

/-- Blanking leaves what `SameZ` reads. -/
theorem sameZ_blank (u tl : HTailF2) : SameZ tl (blank u tl) := ⟨rfl, rfl, rfl, rfl⟩

variable {α : Type} (π : α → Option HTailF2 × Option (Array HFun))

/-- **At the run's own data.** -/
theorem digRows_ent4 (u : HTailF2) (q : α × Option Pub9) (y : Bound GE8) {tl : HTailF2} {v : Pub9}
    {g : Heard} (h1 : (π q.1).1 = some (blank u tl)) (h2 : q.2 = some v) (hg : tl.heard = some g)
    (hP : ∀ c < 2, ∀ p ∈ piecesL tl c, PieceOK tl c (tl.zOf c).call.n p)
    (T : CoefOK (blank u tl) v.F)
    (hRw : ∀ a ∈ allPieces tl, a.2.r0 + a.2.Rp ≤ (v.F.trees.getD a.2.tree {}).R) :
    DigRows Reading.gl tl g (ent4 π q y) fun x => entUnit q y x.1 x.2.1 x.2.2 :=
  digRows_of_law Reading.gl tl (blank u tl) (sameZ_blank u tl) g hP v.F T hRw
    ⟨fun _ => 0, ent4 π q y⟩ (fun x => entUnit q y x.1 x.2.1 x.2.2)
    (rowsLaw_ent4 π q y h1 h2 hg fun _ => 0)

variable {J₀ : Type} {front : ℕ}

/-- **The four are worth 0.** -/
theorem four_zero_ent4 (u : HTailF2) (q : α × Option Pub9) (y : Bound GE8) {tl tl' : HTailF2}
    {funs : Array HFun} {F F1 : Fork} {cls : List Desc.Claim}
    (he : equations front tl funs F = .ok (tl', F1, cls)) {v : Pub9} {g : Heard}
    (h1 : (π q.1).1 = some (blank u tl)) (h2 : q.2 = some v) (hg : tl.heard = some g)
    (hs : tl.f9 = g.shape) (jLK : ℕ) (F' : Fork) (h0 : _root_.Fo.Later F' F)
    (hok : FoNums.ok g.shape = true) (hT : TailOK tl) (hF : Sized F)
    (hfull : 2 ^ g.shape.cK = g.shape.NC) (h5 : 5 ≤ g.shape.kT + g.shape.cK)
    (hn : ∀ c < 2, (g.zk.getD c #[]).size = (tl.zOf c).call.n)
    (h63 : ∀ c < 2, (tl.zOf c).call.n ≤ 63)
    (hP : ∀ c < 2, ∀ p ∈ piecesL tl c, PieceOK tl c (tl.zOf c).call.n p)
    (hD : ∀ c < 2, (piecesL tl c).Pairwise fun p p' =>
      p.off + 2 ^ p.b ≤ p'.off ∨ p'.off + 2 ^ p'.b ≤ p.off)
    (T : CoefOK (blank u tl) v.F)
    (hRw : ∀ a ∈ allPieces tl, a.2.r0 + a.2.Rp ≤ (v.F.trees.getD a.2.tree {}).R)
    (en : Ent3 → J₀) (mk : ℕ → J₀) (μ₀ : J₀ → GE8)
    (hcb : ∀ r < 32, ∀ i < tl.bzColumns,
      entUnit q y tl.ix.BZ r i = μ₀ (en (tl.ix.BZ, r, i)))
    (hcz : ∀ c < 2, ∀ p ∈ piecesL tl c, ∀ r < p.Rp, ∀ i < p.Cp,
      entUnit q y tl.ix.ZZ (p.r0 + r) (p.c0 + i) = μ₀ (en (tl.ix.ZZ, p.r0 + r, p.c0 + i)))
    (hm4 : ∀ k ∈ cls.take 4, ∀ s ∈ k.form.slots.toList, y.mask s.1 = μ₀ (mk s.1))
    (H : Fork) (hH : _root_.Fo.Later F1 H)
    (rs : Rounds GE8) (hI : HeardIs Reading.gl g F' (endsOf g.shape 5 jLK rs))
    (hPl : K3Planes g.shape 5 jLK (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p)) rs)
    (hK : K3Keys g.shape 5 jLK (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
      (forK GE8 (digL5 GE8 tl en mk jLK Unit) () (zext μ₀)) rs) :
    ∀ k ∈ cls.take 4, valC Reading.gl (H.worldOf Reading.gl y.mask (ent4 π q y)) k = 0 := by
  obtain ⟨tla, tlb, G1, c1, c2, hJ, hB, _, e4⟩ := first_four he
  have hV : DigRows Reading.gl tl g (ent4 π q y) fun e => μ₀ (en e) :=
    digRows_congr Reading.gl tl g (ent4 π q y) hcb hcz (digRows_ent4 π u q y h1 h2 hg hP T hRw)
  intro k hk
  rw [valC_masks Reading.gl H (mask := y.mask) (mask' := fun j => μ₀ (mk j)) (ent4 π q y) k
    (hm4 k hk)]
  exact rows_of_k3PlanesKeys Reading.gl tl tla tlb F G1 F1 c1 c2 hJ hB g hg hs jLK F' h0 hok hT hF
    hfull h5 hn h63 hP hD en mk μ₀ (ent4 π q y) H hH hV rs hI hPl hK k (e4 ▸ hk)

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.sameZ_blank
#print axioms VerifiableInference.Desc.First.K8.Honest.digRows_ent4
#print axioms VerifiableInference.Desc.First.K8.Honest.four_zero_ent4
