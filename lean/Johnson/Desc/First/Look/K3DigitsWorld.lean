-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3DigitsWorld.lean: the lookup on the digits of a link's smallness test: THE
RELATION BEHIND, PAID AT A WORLD WITH CELLS AND MASKS OF ITS OWN, with two premises fewer than
digBehind_of_true (Johnson/Desc/First/Look/K3DigitsPay.lean). One theorem. NO SOUNDNESS IS CLAIMED.

Why. digBehind_of_true frees the cells of whoever makes the world; its claims are still judged at
the world whose mask under slot j is the closed caller's msg₀ at mkOf, AT EVERY j. What a claim is
worth reads of the masks those under the slots that its form names (valC_masks,
Johnson/Desc/First/Look/K3DigMasks.lean). And two of its premises on public numbers follow from
DigOK with SameDig.

Main names.
  dig_full: under DigOK: 2 ^ tl.f9.cK = tl.f9.NC (the library's PortOK.full).
  digBehind_of_world: digBehind_of_true with the claims judged at a world with ANY masks that, at
    the slots that the claims' forms name, are the caller's msg₀ at mkOf; WITHOUT the premises
    «FoNums.ok g.shape» and «2 ^ g.shape.cK = g.shape.NC»: they come from DigOK, SameDig.f9 and
    tlS.f9 = g.shape.
Limits. Those of K3DigitsPay.lean and K3DigMasks.lean. THE ROW OUT IS SPENDABLE, NOT PAID: owed
stay: that the made world's cells, where they are read, and its masks, at the slots that the claims
name, are what the witness's messages hold · the seam (SameDig along the link; its f9 is an equation
of records) · the three «Later» · that the claims are worth 0. At mask := the caller's msg₀ at mkOf
the two premises on the masks hold by rfl: so it is no emptier than digBehind_of_true.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3DigitsPay
import Johnson.Desc.First.Look.K3DigMasks

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.DgP Cb.Fo Cb.LdLkp Finset
open _root_.Fo _root_.Fo.Eq
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

/-- Under DigOK the calls fill the trees' numbers. -/
theorem dig_full {set : Params.Setting} {x : Desc.First.Look.Place} {tl : HTailF2}
    {D : Desc.First.Look.Sent} {rad : OracleShape → ℕ} {pp : ℕ} (H : DigOK set x tl D rad pp) :
    2 ^ tl.f9.cK = tl.f9.NC := (shape2_parts H.tail).2.2.full

section
variable {S Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  {x : Desc.First.Look.Place} {tl : HTailF2} {D : Desc.First.Look.Sent} {rad : OracleShape → ℕ}
  (seatT : Fin (digList x D rad).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : S → (i : Fin (digList x D rad).length) → Option ((digSg x D rad).om i).Smp)
  (fork : S → Option Fork) (heard : S → Option Heard) {front : ℕ}

/-- **THE RELATION BEHIND, PAID AT A WORLD WITH CELLS AND MASKS OF ITS OWN.** -/
theorem digBehind_of_world {set : Params.Setting} {pp : ℕ} (HD : DigOK set x tl D rad pp)
    (a : S × Fr.E.Str) (w : Desc.Wit Cells Tok MsgT)
    (hpin : PinSig G D.codes (digList x D rad) seatT smp arr (fun _ => True) a.1 (strsOf Fr a.2) w)
    (g : Heard) (F' : Fork) (hf : fork a.1 = some F') (hh : heard a.1 = some g)
    (tlS tl1 tl2 : HTailF2) (h5' : SameDig tl tlS) (F G1 G2 : Fork)
    (c c1 c2 : Array Desc.Claim)
    (hJ : EqM.at (eqKeys tlS) front F c = .ok ((tl1, G1), c1))
    (hB : EqM.at (eqCounts tl1) front G1 c1 = .ok ((tl2, G2), c2))
    (hg : tlS.heard = some g) (hs : tlS.f9 = g.shape) (h0 : _root_.Fo.Later F' F)
    (hF : Sized F) (h5 : 5 ≤ g.shape.kT + g.shape.cK)
    (hn : ∀ q < 2, (g.zk.getD q #[]).size = (tlS.zOf q).call.n)
    (h63 : ∀ q < 2, (tlS.zOf q).call.n ≤ 63)
    (hP : ∀ q < 2, ∀ p ∈ piecesL tlS q, PieceOK tlS q (tlS.zOf q).call.n p)
    (hD : ∀ q < 2, (piecesL tlS q).Pairwise fun p p' =>
      p.off + 2 ^ p.b ≤ p'.off ∨ p'.off + 2 ^ p'.b ≤ p.off)
    (entry : ℕ → ℕ → ℕ → Cb.Gl.E) (H : Fork) (hH : _root_.Fo.Later G2 H)
    (cell : Ent3 → Cb.Gl.E)
    (hcb : ∀ r < 32, ∀ i < tl.bzColumns,
      digVal x D rad (msgsOf D.codes (digList x D rad) seatT arr w) (.cell tl.ix.BZ r i) =
        some (cell (tl.ix.BZ, r, i)))
    (hcz : ∀ q < 2, ∀ p ∈ piecesL tl q, ∀ r < p.Rp, ∀ i < p.Cp,
      digVal x D rad (msgsOf D.codes (digList x D rad) seatT arr w)
          (.cell tl.ix.ZZ (p.r0 + r) (p.c0 + i)) =
        some (cell (tl.ix.ZZ, p.r0 + r, p.c0 + i)))
    (hV : DigRows Reading.gl tlS g entry cell)
    (mask : ℕ → Cb.Gl.E) (clO : List Desc.Claim)
    (hmO : ∀ k ∈ clO, ∀ s ∈ k.form.slots.toList,
      mask s.1 = digMu x D rad seatT arr w (mkOf x.arrays s.1))
    (hm2 : ∀ k ∈ c2.toList, ∀ s ∈ k.form.slots.toList,
      mask s.1 = digMu x D rad seatT arr w (mkOf x.arrays s.1))
    (hO : ∀ rs : Rounds Cb.Gl.E, HeardIs Reading.gl g F' (endsOf g.shape 5 x.F.next rs) →
      clO.map (valC Reading.gl (H.worldOf Reading.gl mask entry)) =
        (endsOf g.shape 5 x.F.next rs).rows.map
          (rowRes fun p => zext (digMu x D rad seatT arr w)
            (NumsEq.placeOf (mkOf x.arrays) (plV tlS (enOf x.arrays)) p)))
    (hzO : ∀ k ∈ clO, valC Reading.gl (H.worldOf Reading.gl mask entry) k = 0)
    (hz : ∀ k ∈ c2.toList, valC Reading.gl (H.worldOf Reading.gl mask entry) k = 0) :
    DigBehind G x tl D rad seatT arr smp fork heard a w :=
  have e9 : g.shape = tl.f9 := hs.symm.trans h5'.f9
  digBehind_of_true G seatT arr smp fork heard HD a w hpin g F' hf hh tlS tl1 tl2 h5' F G1 G2
    c c1 c2 hJ hB hg hs h0 (by rw [e9]; exact dig_foOk HD) hF (by rw [e9]; exact dig_full HD) h5 hn
    h63 hP hD entry H hH cell hcb hcz hV clO
    (fun rs hI => (List.map_congr_left fun k hk =>
      (valC_masks Reading.gl H (mask := mask)
        (mask' := fun j => digMu x D rad seatT arr w (mkOf x.arrays j)) entry k
        (hmO k hk)).symm).trans (hO rs hI))
    (fun k hk => (valC_masks Reading.gl H (mask := mask)
      (mask' := fun j => digMu x D rad seatT arr w (mkOf x.arrays j)) entry k
      (hmO k hk)).symm.trans (hzO k hk))
    (fun k hk => (valC_masks Reading.gl H (mask := mask)
      (mask' := fun j => digMu x D rad seatT arr w (mkOf x.arrays j)) entry k
      (hm2 k hk)).symm.trans (hz k hk))

end

/-- At the caller's own masks the premises on the masks hold outright. -/
example {E : Type} (μ : ℕ → E) (cl : List Desc.Claim) :
    ∀ k ∈ cl, ∀ s ∈ k.form.slots.toList, (fun j => μ j) s.1 = μ s.1 := fun _ _ _ _ => rfl

#print axioms dig_full
#print axioms digBehind_of_world

end VerifiableInference.OnPublicFiles
