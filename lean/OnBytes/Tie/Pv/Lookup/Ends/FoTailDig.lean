-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoTailDig.lean.
The smallness test's four hand-made claims, at the digits' own key forms and cells.

OnBytes/Tie/Pv/Lookup/Ends/FoTailFour.lean says by how much linJoin9 and linBits9 make the
sub-proof's sum of claims grow, with letters for what the runs read. This file pays the letters: at
the cells plV of the layout digL5 (OnBytes/Tie/Pv/Lookup/Digits/PortEnds.lean) of the lookup on the
digits, the four values are the last four of the flat list claimsOf at letters of the form at which
hcClaims (OnBytes/Tie/Pv/Lookup/Forest/FoClaims.lean) ties that list to what the typed verifier of
the lookup puts out: the columns' sums of the lookup's cells, and the values of the digits' key
forms digKF. The rounds rsK are any rounds of which the record holds the end values; this file does
not tie them to a transcript of the typed verifier.

* claimJoin_congr: claimJoin reads its letter kf at the calls' numbers alone.
* heard_zkAt: a call's point in the byte-level record, read, is the flat record's.
* kf_dig: what the runs of call q read is the value of the digits' key form of call q.
* tail_four_dig: tail_four at these letters, under tail_four's own premises at lm = 5 (both runs
  return; the record is the smallness test's and holds the end values endsOf with a state F0; the
  state before the runs is later than F0, Sized, and has as many weights on slots as slots).
Hypotheses on the world, not shown here: each virtual row that the four claims read is the
combination of its array's rows under the weights named in the statement (hV0, hV1, hV2 for the
three rows of BZ, hVp for the pieces' rows of ZZ). That one world meets all of them together is not
shown here either: it asks that the virtual rows named are different rows.
OnBytes/Tie/Pv/Lookup/Ends/FoTailLaw.lean pays all of them from one law, which some world meets.
On public numbers: FoNums.ok, TailOK, PieceOK of each piece, the pieces' key places apart, each
call's point in the record has n coordinates, n at most 63, 2^cK = NC, 5 ≤ kT + cK.

Not claimed: anything on completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoTailFour
import OnBytes.Tie.Pv.Lookup.Ends.FoTailKf
import OnBytes.Tie.Pv.Lookup.Ends.FoBitsPayAt

set_option autoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.DgP Cb.Fo Cb.LdLkp Finset

section
variable {K : Type} [CommRing K]

theorem claimJoin_congr (h : FoNums.Sh) (lm jLK : ℕ) (rs : Rounds K) (ν : Pl → K) (kf kf' : ℕ → K)
    (e : ∀ c < h.NC, kf c = kf' c) :
    claimJoin h lm jLK rs ν kf = claimJoin h lm jLK rs ν kf' := by
  unfold claimJoin
  rw [val_joinK, val_joinK]
  congr 2
  exact sum_congr rfl fun c hc => by
    rw [AffK.val_ofConst, AffK.val_ofConst, e c (mem_range.mp hc)]

/-- A call's point in the byte-level record, read. -/
theorem heard_zkAt (ρ : Reading K) (g : Heard) (F0 : Fork) (En : Ends K) (hI : HeardIs ρ g F0 En)
    (q : ℕ) : En.zk.getD q [] = rdL ρ (g.zk.getD q #[]) := by
  rw [← hI.zk]
  have e : (g.zk.toList.map (rdA ρ)).getD q [] = rdA ρ (g.zk.toList.getD q #[]) := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases g.zk.toList[q]? <;> rfl
  rw [e]
  have e2 : g.zk.toList.getD q #[] = g.zk.getD q #[] := by
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  rw [e2]
  rfl

end

section
variable {K : Type} [Field K] (ρ : Reading K) {J₀ : Type}

/-- What the runs of call q read is the value of the digits' key form. -/
theorem kf_dig (W : World K) (tl : HTailF2) (g : Heard) (q : ℕ) (hq : q < 2) (hT : TailOK tl)
    (hok : FoNums.ok g.shape = true) (hs : tl.f9 = g.shape) (en : Ent3 → J₀) (μ₀ : J₀ → K)
    (lm jLK : ℕ) (rsK : Rounds K) (F0 : Fork) (hI : HeardIs ρ g F0 (endsOf g.shape lm jLK rsK))
    (hn : (g.zk.getD q #[]).size = (tl.zOf q).call.n) (h63 : (tl.zOf q).call.n ≤ 63)
    (hP : ∀ p ∈ piecesL tl q, PieceOK tl q (tl.zOf q).call.n p)
    (hD : (piecesL tl q).Pairwise fun p p' =>
      p.off + 2 ^ p.b ≤ p'.off ∨ p'.off + 2 ^ p'.b ≤ p.off)
    (hV : ∀ p ∈ piecesL tl q, ∀ i < p.Cp, W.entry p.tree p.row (p.c0 + i) = ∑ r ∈ range p.Rp,
      (eqTabK (exL (rdL ρ (g.zk.getD q #[])) ((tl.zOf q).call.n - p.b)
        ((tl.zOf q).call.n - p.b + p.a))).getD r 0 * μ₀ (en (tl.ix.ZZ, p.r0 + r, p.c0 + i))) :
    kfRun ρ W tl g q =
      AffK.val (digKF tl en (fun c => (endsOf g.shape lm jLK rsK).zk.getD c []) q) (zext μ₀) := by
  have hq' : q < tl.f9.NC := by rw [hT.nc]; exact hq
  have hk := dig_KFok_ends hT (hs ▸ hok) en (fun _ => en (0, 0, 0)) 0 () lm jLK rsK (zext μ₀) q hq'
  rw [hs] at hk
  beta_reduce at hk
  rw [hk, extL_ofList, heard_zkAt ρ g F0 _ hI q,
    kf_ext ρ W tl g q (fun x => μ₀ (en x)) hn h63 hP hD hV]
  have hl : (rdL ρ (g.zk.getD q #[])).length = (tl.zOf q).call.n := by
    unfold rdL
    rw [List.length_map, Array.length_toList, hn]
  rw [hl]
  rfl

/-- The four hand-made claims at the digits' own letters. -/
theorem tail_four_dig (tl tl1 tl2 : HTailF2) (F G1 G2 : Fork) (c c1 c2 : Ctx)
    (hJ : tl.linJoin9 F c = .ok ((tl1, G1), c1)) (hB : tl1.linBits9 G1 c1 = .ok ((tl2, G2), c2))
    (g : Heard) (hg : tl.heard = some g) (hs : tl.f9 = g.shape) (jLK : ℕ) (rsK : Rounds K)
    (F0 : Fork) (hI : HeardIs ρ g F0 (endsOf g.shape 5 jLK rsK)) (h0 : Later F0 F)
    (hok : FoNums.ok g.shape = true) (hT : TailOK tl) (hF : Sized F) (hLS : F.LS.size = F.ns)
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
    (H : Fork) (hH : Later G2 H) :
    G2.total ρ (H.worldOf ρ (fun j => μ₀ (mk j)) entry) =
      F.total ρ (H.worldOf ρ (fun j => μ₀ (mk j)) entry) +
        ρ.val F.theta ^ F.nClaim * claimJoin g.shape 5 jLK rsK
          (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
          (fun c => AffK.val (digKF tl en (fun c => (endsOf g.shape 5 jLK rsK).zk.getD c []) c)
            (zext μ₀)) +
        ρ.val F.theta ^ (F.nClaim + 1) * claimLeaves g.shape 5 jLK rsK
          (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
          (colsK g.shape 5 (endsOf g.shape 5 jLK rsK).zb0
            fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p)) +
        ρ.val F.theta ^ (F.nClaim + 2) * claimBits g.shape 5 jLK rsK
          (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
          (colsK g.shape 5 (endsOf g.shape 5 jLK rsK).zb1
            fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p)) +
        ρ.val F.theta ^ (F.nClaim + 3) * Pin.countK g.shape 5
          (Pin.pinColK 5 fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p)) := by
  have h2 : g.shape.NC = 2 := by rw [← hs]; exact hT.nc
  have hB' : CellsBZ g.shape (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
      (fun r i => μ₀ (en (tl.ix.BZ, r, i))) := hs ▸ cellsBZ_dig tl en mk μ₀
  obtain ⟨_, _, _, _, _, key⟩ :=
    tail_four ρ tl tl1 tl2 F G1 G2 c c1 c2 hJ hB g hg hs 5 jLK rsK F0 hI h0 hok h2 hF hLS
  have e := key H hH (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p)) entry _ _ _
    (pay_run tl g.shape hs hok hfull _ rfl _ hB' _ (ends_zb0_len g.shape 5 jLK rsK)
      (H.worldOf ρ (fun j => μ₀ (mk j)) entry) 0 hV0)
    (pay_run tl g.shape hs hok hfull _ rfl _ hB' _ (ends_zb1_len g.shape 5 jLK rsK)
      (H.worldOf ρ (fun j => μ₀ (mk j)) entry) 1 hV1)
    (pay_pin ρ tl g.shape hs hok hfull h5 _ rfl _ hB'
      (H.worldOf ρ (fun j => μ₀ (mk j)) entry) hV2)
  rw [claimJoin_congr g.shape 5 jLK rsK _ _
    (fun c => AffK.val (digKF tl en (fun c => (endsOf g.shape 5 jLK rsK).zk.getD c []) c)
      (zext μ₀)) (fun q hq => kf_dig ρ _ tl g q (h2 ▸ hq) hT hok hs en μ₀ 5 jLK rsK F0 hI
        (hn q (h2 ▸ hq)) (h63 q (h2 ▸ hq)) (hP q (h2 ▸ hq)) (hD q (h2 ▸ hq))
        (hVp q (h2 ▸ hq)))] at e
  exact e

end
end Fo
