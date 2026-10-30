-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3DigitsPay.lean: the lookup on the digits of a link's smallness test: THE
RELATION BEHIND HAS ITS PAYER BY NAME: DigBehind (Johnson/Desc/First/Look/K3DigitsGoodIn.lean) from
the payer into the row out (k3Out_of_rows, Johnson/Top/H/K3OutRows.lean): where the lookup's own
rows' claims and the four claims that the smallness test's run lays (eqKeys, eqCounts) are all worth
0 in a world that meets DigRows, at the masks and cells that the closed caller's msg₀ reads off THE
SAME WITNESS. Two theorems. NO SOUNDNESS IS CLAIMED.

A seam. The closed caller is made of the PLAN's record tl of the smallness test (public). The payer
speaks of THE CARRIED RECORD's tlS at the hour at which eqKeys is called. SameLay tl tlS, SameDig tl
tlS (Johnson/Desc/First/Look/K3DigRows.lean) say in what the two agree.

Main names.
  digBehind_of_rows: PinSig at (a, w) · g and F' in a's record · SameLay tl tlS · k3Out_of_rows'
    premises at en := enOf x.arrays, mk := mkOf x.arrays, μ₀ := the caller's msg₀ of w's messages,
    jLK := the place's first slot ⇒ DigBehind. Of the law of the rows it asks DigRows alone.
  digBehind_of_true: the same with DigRows at the cells of whoever makes the world, free at every
    array but BZ and ZZ; of these cells it asks that, where they are read, they are what the
    witness's messages hold at the cell's seat. Under DigOK and SameDig; the library's test TailOK
    at the carried record is no premise any more (SameDig.tailOK).
Limits. None of the public premises is shown at a value. THE ROW OUT IS THEREBY SPENDABLE, NOT PAID:
owed stay: that the made world's cells AND ITS MASKS are what the witness's messages hold (the
premises hO, hzO, hz stand at the world whose masks are the caller's msg₀ at mkOf, at every j) · the
seam (that the six fields stay along the link; SameDig.f9 is an equation of records) · the three
«Later» · that the claims are worth 0. hz ranges over all of c2, with c a free letter: four members
are spent. All premises together at a real run: tried by nobody. A tie with no error term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3DigitsGoodIn
import Johnson.Desc.First.Look.K3DigRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.DgP Cb.Fo Cb.LdLkp Finset
open _root_.Fo _root_.Fo.Eq
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

section
variable {S Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  {x : Desc.First.Look.Place} {tl : HTailF2} {D : Desc.First.Look.Sent} {rad : OracleShape → ℕ}
  (seatT : Fin (digList x D rad).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : S → (i : Fin (digList x D rad).length) → Option ((digSg x D rad).om i).Smp)
  (fork : S → Option Fork) (heard : S → Option Heard) {front : ℕ}

/-- **THE RELATION BEHIND, PAID BY NAME, UNDER NO MORE OF THE LAW OF THE ROWS THAN THE FOUR CLAIMS
READ** (DigRows: the counts' array's three virtual rows; the pieces' rows on the digits' array).
That the caller's msg₀ is the committed messages' own entry at all these cells: dig_cell_bz,
dig_cell_zz (K3DigRows.lean). -/
theorem digBehind_of_rows (a : S × Fr.E.Str) (w : Desc.Wit Cells Tok MsgT)
    (hpin : PinSig G D.codes (digList x D rad) seatT smp arr (fun _ => True) a.1 (strsOf Fr a.2) w)
    (g : Heard) (F' : Fork) (hf : fork a.1 = some F') (hh : heard a.1 = some g)
    (tlS tl1 tl2 : HTailF2) (hLay : SameLay tl tlS) (F G1 G2 : Fork)
    (c c1 c2 : Array Desc.Claim)
    (hJ : EqM.at (eqKeys tlS) front F c = .ok ((tl1, G1), c1))
    (hB : EqM.at (eqCounts tl1) front G1 c1 = .ok ((tl2, G2), c2))
    (hg : tlS.heard = some g) (hs : tlS.f9 = g.shape) (h0 : _root_.Fo.Later F' F)
    (hok : FoNums.ok g.shape = true) (hT : TailOK tlS) (hF : Sized F)
    (hfull : 2 ^ g.shape.cK = g.shape.NC) (h5 : 5 ≤ g.shape.kT + g.shape.cK)
    (hn : ∀ q < 2, (g.zk.getD q #[]).size = (tlS.zOf q).call.n)
    (h63 : ∀ q < 2, (tlS.zOf q).call.n ≤ 63)
    (hP : ∀ q < 2, ∀ p ∈ piecesL tlS q, PieceOK tlS q (tlS.zOf q).call.n p)
    (hD : ∀ q < 2, (piecesL tlS q).Pairwise fun p p' =>
      p.off + 2 ^ p.b ≤ p'.off ∨ p'.off + 2 ^ p'.b ≤ p.off)
    (entry : ℕ → ℕ → ℕ → Cb.Gl.E) (H : Fork) (hH : _root_.Fo.Later G2 H)
    (hV : DigRows Reading.gl tlS g entry fun e => digMu x D rad seatT arr w (enOf x.arrays e))
    (clO : List Desc.Claim)
    (hO : ∀ rs : Rounds Cb.Gl.E, HeardIs Reading.gl g F' (endsOf g.shape 5 x.F.next rs) →
      clO.map (valC Reading.gl
          (H.worldOf Reading.gl (fun j => digMu x D rad seatT arr w (mkOf x.arrays j)) entry)) =
        (endsOf g.shape 5 x.F.next rs).rows.map
          (rowRes fun p => zext (digMu x D rad seatT arr w)
            (NumsEq.placeOf (mkOf x.arrays) (plV tlS (enOf x.arrays)) p)))
    (hzO : ∀ k ∈ clO, valC Reading.gl
      (H.worldOf Reading.gl (fun j => digMu x D rad seatT arr w (mkOf x.arrays j)) entry) k = 0)
    (hz : ∀ k ∈ c2.toList, valC Reading.gl
      (H.worldOf Reading.gl (fun j => digMu x D rad seatT arr w (mkOf x.arrays j)) entry) k = 0) :
    DigBehind G x tl D rad seatT arr smp fork heard a w := by
  refine ⟨hpin, g, F', hf, hh, ?_⟩
  have k := k3Out_of_rows Reading.gl tlS tl1 tl2 F G1 G2 c c1 c2 hJ hB g hg hs x.F.next F' h0 hok
    hT hF hfull h5 hn h63 hP hD (enOf x.arrays) (mkOf x.arrays) (digMu x D rad seatT arr w) entry
    H hH hV clO hO hzO hz
  rw [← hs, hLay.f9, hLay.pl, hLay.lay] at k
  exact k

/-- **THE RELATION BEHIND, PAID AT THE WORLD's OWN CELLS.** cell: the cells of whoever makes the
world, free at every array but BZ and ZZ. -/
theorem digBehind_of_true {set : Params.Setting} {pp : ℕ} (HD : DigOK set x tl D rad pp)
    (a : S × Fr.E.Str) (w : Desc.Wit Cells Tok MsgT)
    (hpin : PinSig G D.codes (digList x D rad) seatT smp arr (fun _ => True) a.1 (strsOf Fr a.2) w)
    (g : Heard) (F' : Fork) (hf : fork a.1 = some F') (hh : heard a.1 = some g)
    (tlS tl1 tl2 : HTailF2) (h5' : SameDig tl tlS) (F G1 G2 : Fork)
    (c c1 c2 : Array Desc.Claim)
    (hJ : EqM.at (eqKeys tlS) front F c = .ok ((tl1, G1), c1))
    (hB : EqM.at (eqCounts tl1) front G1 c1 = .ok ((tl2, G2), c2))
    (hg : tlS.heard = some g) (hs : tlS.f9 = g.shape) (h0 : _root_.Fo.Later F' F)
    (hok : FoNums.ok g.shape = true) (hF : Sized F)
    (hfull : 2 ^ g.shape.cK = g.shape.NC) (h5 : 5 ≤ g.shape.kT + g.shape.cK)
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
    (clO : List Desc.Claim)
    (hO : ∀ rs : Rounds Cb.Gl.E, HeardIs Reading.gl g F' (endsOf g.shape 5 x.F.next rs) →
      clO.map (valC Reading.gl
          (H.worldOf Reading.gl (fun j => digMu x D rad seatT arr w (mkOf x.arrays j)) entry)) =
        (endsOf g.shape 5 x.F.next rs).rows.map
          (rowRes fun p => zext (digMu x D rad seatT arr w)
            (NumsEq.placeOf (mkOf x.arrays) (plV tlS (enOf x.arrays)) p)))
    (hzO : ∀ k ∈ clO, valC Reading.gl
      (H.worldOf Reading.gl (fun j => digMu x D rad seatT arr w (mkOf x.arrays j)) entry) k = 0)
    (hz : ∀ k ∈ c2.toList, valC Reading.gl
      (H.worldOf Reading.gl (fun j => digMu x D rad seatT arr w (mkOf x.arrays j)) entry) k = 0) :
    DigBehind G x tl D rad seatT arr smp fork heard a w :=
  digBehind_of_rows G seatT arr smp fork heard a w hpin g F' hf hh tlS tl1 tl2 h5'.lay F G1 G2
    c c1 c2 hJ hB hg hs h0 hok (h5'.tailOK (shape2_parts HD.tail).2.1) hF hfull h5 hn h63 hP hD
    entry H hH
    (digRows_at_caller HD (by rw [← h5'.f9, hs]; exact hfull) h5' g entry
      (fun q hq p hp => (hP q hq p hp).c0) _ cell hcb hcz hV)
    clO hO hzO hz

end

#print axioms digBehind_of_rows
#print axioms digBehind_of_true

end VerifiableInference.OnPublicFiles
