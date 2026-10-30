-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/TieOneR.lean: THE FIRST TIE OF THE CODE SWITCH AT A PLACE, WITH «REACHED»:
one theorem: under the table of joints' promise in front and Rch, at a state without a mark, the
condition in front of `k02_place2` (PlaceLaw2.lean) holds, at the closed held OOD samples.

Main names:
  `k02_t1R`. THE PREMISES, AND WHO PAYS EACH. hT1: THE FOLD's SIDE: at the front that the text makes
    of what the way in lets in: the test `frontB2` at the place's numbers of the kept old messages ·
    the notices are the typed list · the invariant on stored sample rows · the test `storedB` · the
    state's and the front's statements hold the same oracle messages. THE TABLE's SIDE, for
    `KeptFree` (`keptFree_at`, KeptFreeAt.lean): as in the fourth tie (TieFourR.lean): six closed
    facts at a written front · `Fit` at every frame of the family · facts on the plan (hSF, hB, ho,
    hal, hN) · hBook · hOld · horc · hsn: every leaf is shown and there is no collision at each kept
    tenant: the promise's two clauses · hAl: each typed kept member has a member of the table's list
    that is alike it, at a kept tenant.
Limits. A SENTENCE WITH MANY PREMISES; NONE IS SHOWN MET HERE; no member. It is no soundness of the
protocol. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.HallAt
import Johnson.Top.H0.K2Caller.KeptFreeAt
import Johnson.Top.H0.K2Caller.TiesFrontR
import Johnson.Top.H0.K2Hears.CheckSkel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb IOR
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (FileDescription Strs Wit Place)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers)
open VerifiableInference.Desc.First.K2Hands
open Johnson.G (smpTop keptBitsB keptShapeB storedB hx_of)
open _root_.Tw.K2 (switchNotices)

variable {F : Frame}

set_option maxHeartbeats 8000000 in
/-- **THE FIRST TIE OF THE CODE SWITCH AT A PLACE, WITH «REACHED»**: under the table of joints'
    promise
in front and Rch, at a state without a mark, the condition in front of `k02_place2` (PlaceLaw2.lean)
holds, at the closed held OOD samples. hT1: the fold's side. The rest: the table's side of «no kept
slot has a collision». -/
theorem k02_t1R {P W' Xi : Type} {r : SwRow} (h : r.ok = true)
    (iJ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says
        h)).oM (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says
        h)).oM (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
    (G : FileDescription Xi) (seat : Fin r.lo.length → ℕ × ℕ) (seatN : Fin r.l.length → ℕ × ℕ)
    (base : ℕ) (d₁ d₂ : RDT) (arr : ℕ → ℕ → ℕ) (seats : List (ℕ × ℕ))
    (d₀ : (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).X ×
      (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).Ex.Str) (y₀ : F.E.Str)
    (pAt : ℕ → K2.P2) (m : ℕ) (enter : Rec → Except String Rec)
    (N : Numbers) (Mg : Meaning P W') (links : List ModelPart) (ps : List Place) (z : P)
    (Rch : ℕ → Rec × F.E.Str → Prop) (k : ℕ) (ms : List Mem)
    (f₀ : _root_.Tw.K2.Front) (W : SwitchFrame) (n0 grp rows : ℕ) (olds : List ℕ)
    (hnd : olds.Nodup) (h0f : K2.frameAt f₀ = some W) (hcs : f₀.st.codes = r.cs)
    (hpub : frontPubB r.l.length f₀ = true) (hkA : r.keptAt W = true)
    (hbB : keptBitsB r W = true) (hsB : keptShapeB r = true)
    (FtF : ∀ W₀, Renumbered W W₀ → Fit r.cs r.l (plainR r (r.ok_says h)).s W₀
      (memK (r := r) (H := (r.ok_says h))) rowK (plK W₀))
    (hT1 : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt (pAt m) t = some fx →
        frontB2 f₀ W grp rows n0 olds fx = true ∧ Tied r.l (switchNotices fx.T fx.others) ∧
        K2.SampleGoodS fx.st ∧ storedB r (placeFrame W n0 olds) fx = true ∧ a.1.st.oracles =
            fx.st.oracles)
    (L : Laid) (trees : ℕ) (news : List (ℕ × ℕ))
    (hSF : ∀ κ : {a // (plainHd r (r.ok_says h)).cl a}, SeatFitAt G r.cs r.lo seat κ.1.1)
    (hB : keptSeatsB G r.cs L seats trees r.lo seat r.kept olds = true)
    (ho : ∀ κ : {a // (plainHd r (r.ok_says h)).cl a},
      olds[r.kept.idxOf κ.1.1.val]? = some (keptK2 r (r.ok_says h) (placeFrame W n0 olds) κ).old)
    (hBook : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t →
        VerifiableInference.Desc.K12.Door.atFirstBook (K2.par9 (pAt m)).firstTree t = true ∧
        VerifiableInference.Desc.K12.Door.atFirstSeats L t = true ∧
        VerifiableInference.Desc.K12.Door.atFirstFits t = true)
    (hOld : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt (pAt m) t = some fx →
        ∀ κ : {a // (plainHd r (r.ok_says h)).cl a},
          (keptK2 r (r.ok_says h) (placeFrame W n0 olds) κ).old < t.book.place.size)
    (horc : ∀ y j, j < trees → ∀ x, K2.orcY F.all F.key y j x = y.col j x)
    (hal : ∀ κ : {a // (plainHd r (r.ok_says h)).cl a}, ∃ v, news[1 + r.kept.idxOf κ.1.1.val]? =
        some v ∧
      arr (seat κ.1.1).1 (seat κ.1.1).2 = arr v.1 v.2)
    (hN : ∀ (n : ℕ) (ho : 1 + n < r.l.length), news[1 + n]? = some (seatN ⟨_, ho⟩))
    (hsn : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none →
      ∀ q ∈ N.keptOf m, shownJT r.cs G ms q.1 q.2 (strsOf F a.2) ∧
        noCollJT r.cs G (smpNamed r.cs seats) ms q.1 q.2 (z, a.1) (strsOf F a.2))
    (hAl : ∀ κ : {a // (plainHd r (r.ok_says h)).cl a}, ∃ q ∈ N.keptOf m, ∃ x ∈ ms, SitsAt x q.1 q.2
        ∧
      VerifiableInference.Desc.Sound.Alike x ⟨⟨r.lo, seat⟩, κ.1.1⟩) :
    ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt (pAt m) t = some fx →
        (∃ olds : List ℕ, olds.Nodup ∧ frontB2 f₀ W grp rows n0 olds fx = true ∧
          Tied r.l (switchNotices fx.T fx.others) ∧ K2.SampleGoodS fx.st ∧
          storedB r (placeFrame W n0 olds) fx = true) ∧
        ((K2.longFront (pAt m) t fx (K2.orcY F.all F.key (strsOf F a.2)) 0).isSome = true →
          switchTargetCheck fx.st fx.f.rows fx.T = true → KeptFree iJ iQ (strsTop iJ iQ (pAt m) (fun
              y => K2.orcS (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y) (smpTop r
              (r.ok_says h) iJ iQ (baseCount r.set .request r.g) (smp₀ r (r.ok_says h))) d₀) (inXTop
              iJ iQ (pAt m) (fun y => K2.orcS (VerifiableInference.Desc.Sound.stg F base [d₁, d₂])
              y) (smpTop r (r.ok_says h) iJ iQ (baseCount r.set .request r.g) (smp₀ r (r.ok_says
              h))) d₀ y₀) (t, a.2)) := by
  intro a ha hrc hm t et fx hfx
  obtain ⟨hB2, hTd, hG, hSt, hor⟩ := hT1 a ha hrc hm t et fx hfx
  refine ⟨⟨olds, hnd, hB2, hTd, hG, hSt⟩, fun hl hc => ?_⟩
  have P12 : Pub12 (r := r) (placeFrame W n0 olds) fx := pub12_of_twelve h0f hcs hpub hnd hTd hB2
  have hRn : Renumbered W (placeFrame W n0 olds) := ⟨_, _, _, rfl⟩
  have hk' : r.keptAt (placeFrame W n0 olds) = true := (keptAt_renumber r W _ _ _).trans hkA
  obtain ⟨b1, b2, b3⟩ := hBook a ha hrc hm t et
  have b4 := hOld a ha hrc hm t et fx hfx
  refine keptFree_at iJ iQ G seat seatN (pAt m) base d₁ d₂ arr seats d₀ y₀ (z, a.1) t a.2 fx
      (placeFrame W n0 olds) hfx
    P12.frameIs (Johnson.Top.H.check_facts hc).1 0 hl ?_ ms ?_
  · intro κ
    obtain ⟨q, hq, x, hx, hs', hA⟩ := hAl κ
    obtain ⟨xo, hmsg, hshp, -⟩ := hx_of hk' hSt ⟨⟨κ.1.1, κ.2.fst⟩, κ.2.snd⟩
    obtain ⟨s1, s2, s3, s4⟩ := tableSide_of G seat (pAt m) (K2.orcY F.all F.key) seats L trees t fx
      (placeFrame W n0 olds) (strsOf F a.2) κ (hSF κ) olds hB (ho κ) b1 b2 b3 0 hl (b4 κ) xo hmsg
          hshp (horc _) ms q
      (hsn a ha hm q hq).1 x hx hs' hA
    exact keptFacts_at G seat seatN (pAt m) (K2.orcY F.all F.key) arr seats (z, a.1) t fx
        (placeFrame W n0 olds)
      (strsOf F a.2) P12 (K2.check_skel fx hc P12.keptPos) hG hk'
      ((keptBits_renumber r W _ _ _).trans hbB) hsB hSt (FtF _ hRn) hor κ s1 s2 s3
      (one_number_of seat news arr seatN (r.kept.idxOf κ.1.1.val) κ.1.1 (hal κ) (hN _)) s4
  · intro κ
    obtain ⟨q, hq, x, hx, hs', hA⟩ := hAl κ
    exact ⟨q, x, hx, hs', hA, (hsn a ha hm q hq).2⟩

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.k02_t1R
