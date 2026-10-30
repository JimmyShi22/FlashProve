-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/EqPort/EqFour.lean: THE FOUR CLAIMS OF THE LOOKUP ON THE SMALLNESS TEST's DIGITS, ONE
BY ONE: where `eqKeys` and then `eqCounts` (Johnson/Desc/First/TailClaims/Equations.lean) say yes,
the four claims that they lay on the list, each a form plus runs on virtual rows, are worth
claimJoin, claimLeaves, claimBits and countK: the last four members of the library's list of the
lookup's claims, at the columns' own combinations of committed cells. Theorems with their proofs.

It is the twin of the library's Fo.tail_four_law (OnBytes/Tie/Pv/Lookup/Ends/FoTailLaw.lean), which
speaks of the verifier program's routines linJoin9 and linBits9 in a context and of the one
equation's total with powers of the batching element. Here the claims are said one by one. Whether a
routine in a context is reached from these proofs is held by a walk over constants in a file of its
own (Johnson/Top/H/EqPort/EqWalk.lean [not in this library]), not here: this file imports files
of the library that hold lemmas on such routines, and names their pure lemmas alone.

Main names:
  `valC ρ W k`: what a claim is worth in a world: its form's value plus its runs' values.
  `eq_four`: the four claims, under premises on the three virtual rows of the counts' array and on
    each piece's virtual row (after the library's tail_four and tail_four_dig).
  `eq_four_law`: the same under ONE premise on the world: RowsLaw: every virtual row's entry is the
    combination of its array's rows under its declared weights, at the cells μ₀ (en (t, r, i)).

Premises, and who pays. HeardIs g F0, Later F0 F: the law on the lookup's decide and the frame
between. Sized F: whoever opens the ledger. FoNums.ok: from the public tests. TailOK, CoefOK,
PieceOK, the pieces apart, 2 ^ cK = NC, 5 ≤ kT + cK, the points' sizes, n ≤ 63, the pieces' rows
inside their arrays: tests on public data or on the record, as in the library's law; none is shown
at a value here. RowsLaw: what a row means: owed by whoever turns runs into rows on oracle messages.
Uses of the library, all pure: join9_claim, kf_dig, claimJoin_congr, pay_run, pay_pin, cellsBZ_dig,
virt_bz, virt_piece, mem_allPieces, ends_zb0_len, ends_zb1_len, paid_sized; the definitions
joinRuns, joinConst, bzRun, pinW, kfRun, runK, digKF, plV, coefAll.

Limits. A tie: it has no error term. Nothing is said where a routine refuses. That the claims are in
fact worth 0 is the link's one equation's to give. lm is 5: the arrangement of the planes at the
digits. Over a field.
RowsLaw whole is not payable at the closed caller of Johnson/Desc/First/Look/K3Caller.lean (no seat
for an earlier link's array): there use k3Out_of_rows, Johnson/Top/H/K3OutRows.lean.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoTailLaw
import Johnson.Top.H.EqPort.EqJoin
import Johnson.Top.H.EqPort.EqBits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.Eq
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.DgP Cb.Fo Cb.LdLkp Finset
open VerifiableInference
open VerifiableInference.Desc.First.TailClaims

variable {front : ℕ}

local notation:65 x:66 " ⟫ " F:max c:max => EqM.at x front F c

/-- What a claim is worth in a world: its form's value plus its runs' values. -/
def valC {K : Type} [CommRing K] (ρ : Reading K) (W : World K) (k : Desc.Claim) : K :=
  k.form.value ρ W + (k.runs.toList.map (Run2.value ρ W)).sum

/-- A claim with one run. -/
theorem valC_one {K : Type} [CommRing K] (ρ : Reading K) (W : World K) (f : Aff) (r : Run2) :
    valC ρ W { form := f, runs := #[r] } = f.value ρ W + Run2.value ρ W r := by
  unfold valC
  simp

theorem paid_laterFo (F : Fork) (i : ℕ) : _root_.Fo.Later F (F.paid i) :=
  ⟨Nat.le_refl _, rfl, fun _ h => ⟨h, rfl, rfl⟩⟩

section
variable {K : Type} [Field K] (ρ : Reading K) {J₀ : Type}

/-- **The four claims, one by one**, under premises on the virtual rows that they read. -/
theorem eq_four (tl tl1 tl2 : HTailF2) (F G1 G2 : Fork) (c c1 c2 : Array Desc.Claim)
    (hJ : eqKeys tl ⟫ F c = .ok ((tl1, G1), c1)) (hB : eqCounts tl1 ⟫ G1 c1 = .ok ((tl2, G2), c2))
    (g : Heard) (hg : tl.heard = some g) (hs : tl.f9 = g.shape) (jLK : ℕ) (rsK : Rounds K)
    (F0 : Fork) (hI : HeardIs ρ g F0 (endsOf g.shape 5 jLK rsK)) (h0 : _root_.Fo.Later F0 F)
    (hok : FoNums.ok g.shape = true) (hT : TailOK tl) (hF : Sized F)
    (hfull : 2 ^ g.shape.cK = g.shape.NC) (h5 : 5 ≤ g.shape.kT + g.shape.cK)
    (hn : ∀ q < 2, (g.zk.getD q #[]).size = (tl.zOf q).call.n)
    (h63 : ∀ q < 2, (tl.zOf q).call.n ≤ 63)
    (hP : ∀ q < 2, ∀ p ∈ piecesL tl q, PieceOK tl q (tl.zOf q).call.n p)
    (hD : ∀ q < 2, (piecesL tl q).Pairwise fun p p' =>
      p.off + 2 ^ p.b ≤ p'.off ∨ p'.off + 2 ^ p'.b ≤ p.off)
    (en : Ent3 → J₀) (mk : ℕ → J₀) (μ₀ : J₀ → K) (entry : ℕ → ℕ → ℕ → K)
    (hV0 : VirtRow entry tl.ix.BZ 0
      (fun r => (eqTabK ((endsOf g.shape 5 jLK rsK).zb0.take 5)).getD r 0)
      (fun r i => μ₀ (en (tl.ix.BZ, r, i))) 32 tl.bzColumns)
    (hV1 : VirtRow entry tl.ix.BZ 1
      (fun r => (eqTabK ((endsOf g.shape 5 jLK rsK).zb1.take 5)).getD r 0)
      (fun r i => μ₀ (en (tl.ix.BZ, r, i))) 32 tl.bzColumns)
    (hV2 : VirtRow entry tl.ix.BZ 2 (fun _ => 1) (fun r i => μ₀ (en (tl.ix.BZ, r, i))) 32
      tl.bzColumns)
    (hVp : ∀ q < 2, ∀ p ∈ piecesL tl q, ∀ i < p.Cp, entry p.tree p.row (p.c0 + i) =
      ∑ r ∈ range p.Rp, (eqTabK (exL (rdL ρ (g.zk.getD q #[])) ((tl.zOf q).call.n - p.b)
        ((tl.zOf q).call.n - p.b + p.a))).getD r 0 * μ₀ (en (tl.ix.ZZ, p.r0 + r, p.c0 + i)))
    (H : Fork) (hH : _root_.Fo.Later G2 H) :
    ∃ k1 k2 k3 k4 : Desc.Claim, c2 = (((c.push k1).push k2).push k3).push k4 ∧
      _root_.Fo.Later F G2 ∧ Sized G2 ∧
      [k1].map (valC ρ (H.worldOf ρ (fun j => μ₀ (mk j)) entry)) =
        [claimJoin g.shape 5 jLK rsK (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
          (fun c => AffK.val (digKF tl en (fun c => (endsOf g.shape 5 jLK rsK).zk.getD c []) c)
            (zext μ₀))] ∧
      [k2, k3, k4].map (valC ρ (H.worldOf ρ (fun j => μ₀ (mk j)) entry)) =
        [claimLeaves g.shape 5 jLK rsK (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
            (colsK g.shape 5 (endsOf g.shape 5 jLK rsK).zb0
              fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p)),
          claimBits g.shape 5 jLK rsK (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
            (colsK g.shape 5 (endsOf g.shape 5 jLK rsK).zb1
              fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p)),
          Pin.countK g.shape 5
            (Pin.pinColK 5 fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))] := by
  have h2 : g.shape.NC = 2 := by rw [← hs]; exact hT.nc
  have hB' : CellsBZ g.shape (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
      (fun r i => μ₀ (en (tl.ix.BZ, r, i))) := hs ▸ cellsBZ_dig tl en mk μ₀
  -- the two cuts
  obtain ⟨g', runs, j1, _, j3, j4, j5, j6⟩ := eqKeys_cut tl tl1 F G1 c c1 hJ
  obtain rfl : g = g' := Option.some.inj (hg.symm.trans j1)
  obtain ⟨g'', B1, k1, t1, k2, k3, k4, _⟩ := eqCounts_cut tl1 tl2 G1 G2 c1 c2 hB
  have hh : tl1.heard = tl.heard := by rw [j6]
  obtain rfl : g = g'' := Option.some.inj (hg.symm.trans (hh.symm.trans k1))
  have hf9 : tl1.f9 = tl.f9 := by rw [j6]
  have hrun : ∀ r co w, bzRun tl1 r co w = bzRun tl r co w := fun r co w => by rw [j6]; rfl
  have hpw : pinW tl1 = pinW tl := by rw [j6]; rfl
  rw [hrun, hrun, hrun, hf9, hpw] at k3
  have lJ : _root_.Fo.Later F G1 := by rw [j5]; exact paid_laterFo F _
  have sJ : Sized G1 := by rw [j5]; exact paid_sized _ hF
  obtain ⟨_, q2, q3, _, q5⟩ := Fo.Tp.bits9_claim ρ tl g 5 jLK rsK F0 G1 B1 [] [] _ _ hs
    (Fo.Tp.pscRow_of g.leaves oneE {} G1 B1 [] t1 k2) hI (h0.trans lJ) hok sJ
  have lB : _root_.Fo.Later B1 G2 := by rw [k4]; exact paid_laterFo B1 _
  have e3 := q5 H (lB.trans hH) (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p)) entry _ _ _
    (pay_run tl g.shape hs hok hfull _ rfl _ hB' _ (ends_zb0_len g.shape 5 jLK rsK)
      (H.worldOf ρ (fun j => μ₀ (mk j)) entry) 0 hV0)
    (pay_run tl g.shape hs hok hfull _ rfl _ hB' _ (ends_zb1_len g.shape 5 jLK rsK)
      (H.worldOf ρ (fun j => μ₀ (mk j)) entry) 1 hV1)
    (pay_pin ρ tl g.shape hs hok hfull h5 _ rfl _ hB'
      (H.worldOf ρ (fun j => μ₀ (mk j)) entry) hV2)
  have eJ := join9_claim ρ tl g 5 jLK rsK F0 H hs hI
    ((h0.trans (lJ.trans (q2.trans lB))).trans hH) hok h2
    (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p)) entry
  rw [_root_.Fo.claimJoin_congr g.shape 5 jLK rsK _ _
    (fun c => AffK.val (digKF tl en (fun c => (endsOf g.shape 5 jLK rsK).zk.getD c []) c)
      (zext μ₀)) (fun q hq => kf_dig ρ _ tl g q (h2 ▸ hq) hT hok hs en μ₀ 5 jLK rsK F0 hI
        (hn q (h2 ▸ hq)) (h63 q (h2 ▸ hq)) (hP q (h2 ▸ hq)) (hD q (h2 ▸ hq))
        (hVp q (h2 ▸ hq)))] at eJ
  refine ⟨_, _, _, _, by rw [k3, j4], lJ.trans (q2.trans lB), by rw [k4]; exact paid_sized _ q3,
    ?_, ?_⟩
  · show [valC ρ _ _] = _
    unfold valC
    simp only
    rw [j3]
    exact congrArg (fun x => [x]) eJ
  · show [valC ρ _ _, valC ρ _ _, valC ρ _ _] = _
    rw [valC_one, valC_one, valC_one]
    exact e3

/-- **The four claims, one by one, under the law of the rows.** Fc: the ledger in which the virtual
rows' weights are laid. -/
theorem eq_four_law (tl tl1 tl2 : HTailF2) (F G1 G2 : Fork) (c c1 c2 : Array Desc.Claim)
    (hJ : eqKeys tl ⟫ F c = .ok ((tl1, G1), c1)) (hB : eqCounts tl1 ⟫ G1 c1 = .ok ((tl2, G2), c2))
    (g : Heard) (hg : tl.heard = some g) (hs : tl.f9 = g.shape) (jLK : ℕ) (rsK : Rounds K)
    (F0 : Fork) (hI : HeardIs ρ g F0 (endsOf g.shape 5 jLK rsK)) (h0 : _root_.Fo.Later F0 F)
    (hok : FoNums.ok g.shape = true) (hT : TailOK tl) (hF : Sized F)
    (hfull : 2 ^ g.shape.cK = g.shape.NC) (h5 : 5 ≤ g.shape.kT + g.shape.cK)
    (hn : ∀ q < 2, (g.zk.getD q #[]).size = (tl.zOf q).call.n)
    (h63 : ∀ q < 2, (tl.zOf q).call.n ≤ 63)
    (hP : ∀ q < 2, ∀ p ∈ piecesL tl q, PieceOK tl q (tl.zOf q).call.n p)
    (hD : ∀ q < 2, (piecesL tl q).Pairwise fun p p' =>
      p.off + 2 ^ p.b ≤ p'.off ∨ p'.off + 2 ^ p'.b ≤ p.off)
    (Fc : Fork) (T : CoefOK tl Fc)
    (hRw : ∀ a ∈ allPieces tl, a.2.r0 + a.2.Rp ≤ (Fc.trees.getD a.2.tree {}).R)
    (en : Ent3 → J₀) (mk : ℕ → J₀) (μ₀ : J₀ → K) (entry : ℕ → ℕ → ℕ → K)
    (H : Fork) (hH : _root_.Fo.Later G2 H)
    (hL : RowsLaw ρ (coefAll tl g Fc) (H.worldOf ρ (fun j => μ₀ (mk j)) entry)
      fun t r i => μ₀ (en (t, r, i))) :
    ∃ k1 k2 k3 k4 : Desc.Claim, c2 = (((c.push k1).push k2).push k3).push k4 ∧
      _root_.Fo.Later F G2 ∧ Sized G2 ∧
      [k1].map (valC ρ (H.worldOf ρ (fun j => μ₀ (mk j)) entry)) =
        [claimJoin g.shape 5 jLK rsK (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
          (fun c => AffK.val (digKF tl en (fun c => (endsOf g.shape 5 jLK rsK).zk.getD c []) c)
            (zext μ₀))] ∧
      [k2, k3, k4].map (valC ρ (H.worldOf ρ (fun j => μ₀ (mk j)) entry)) =
        [claimLeaves g.shape 5 jLK rsK (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
            (colsK g.shape 5 (endsOf g.shape 5 jLK rsK).zb0
              fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p)),
          claimBits g.shape 5 jLK rsK (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
            (colsK g.shape 5 (endsOf g.shape 5 jLK rsK).zb1
              fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p)),
          Pin.countK g.shape 5
            (Pin.pinColK 5 fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))] := by
  obtain ⟨v0, v1, v2⟩ := virt_bz ρ tl g Fc T.bz.1 T.bz.2.1 T.bz.2.2 T.mats T.bzR _ _ hL _ _
    (show rdL ρ g.zb0 = _ from hI.zb0) (show rdL ρ g.zb1 = _ from hI.zb1) tl.bzColumns
  refine eq_four ρ tl tl1 tl2 F G1 G2 c c1 c2 hJ hB g hg hs jLK rsK F0 hI h0 hok hT hF
    hfull h5 hn h63 hP hD en mk μ₀ entry v0 v1 v2 (fun q hq p hp i _ => ?_) H hH
  have e := virt_piece ρ tl g Fc T (q, p) (mem_allPieces hq hp) (hRw _ (mem_allPieces hq hp)) _ _
    hL (p.c0 + i)
  rw [(hP q hq p hp).tree] at e ⊢
  exact e

end
end Fo.Eq

#print axioms Fo.Eq.eq_four
#print axioms Fo.Eq.eq_four_law
