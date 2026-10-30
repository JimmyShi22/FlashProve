-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/EquationsPlanesKeys.lean: The kind "lookup" (K3), at the lookup on the
approximate range proof's digits: THE EXCHANGE AT THE BATCHING's FRONT, FOR THE TWO ITEMS THAT ARE
EXCHANGED THERE ALONE: from an accept of the whole run "K8.equations" and THE FIRST FOUR CLAIMS OF
ITS LIST WORTH 0 IN THE BATCHING's OWN MEASURE AND WORLD: the lookup's items "planes" and "keys"
(K3OutPlanes, K3OutKeys) at the caller's own reading of the witness. NOTHING IS ASKED OF THE
LOOKUP's OWN KEPT ROWS. Statements and proofs: k3Out_of_rows
(Johnson/Top/H/K3OutRows.lean) cut in two, then carried as digBehind_of_true and digBehind_of_world
carry it (Johnson/Desc/First/Look/K3DigitsPay.lean, K3DigitsWorld.lean), to
digRows_worldAt (Johnson/Desc/First/K8/Four/AtWorld.lean).

OBJECT: TailClaims.equations; K9L.claimValue at K9L.worldAt; K3OutPlanes, K3OutKeys.
Used by Johnson/Desc/First/Link/Law/WorthAtFront.lean.
LETTERS: as in Johnson/Desc/First/Look/K3DigitsAtWorld.lean (its B is Dt here).
Compiled with the whole library.

Main names:
  k3PlanesKeys_of_rows: the payer into the two items, at letters en, mk, mu0: from the accepts of
    eqKeys and eqCounts and their claims worth 0, under DigRows.
  digits_planesKeys_at_world: THE END.
  digits_worth_at_world: the same as the two sentences K3WorthPlanes and K3WorthKeys
    (Johnson/Top/H/K3Worth.lean) at a state that holds F' and g.

Limits. Those of K3DigitsAtWorld.lean's digBehind_at_world (that file is not part of this
library: its limits cannot be read here), which ends in the whole
relation behind and asks the rows' claims' worth besides: here its clO, hmO, hO, hzO and hpin are
gone. THE LEDGER IS coefAll tlX g Fc. hcb | hcz | hm4: the data's cells, where the four claims read
them, and its mask row, at the slots that they name, are what the witness's messages hold:
premises. A tie without an error term.

Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3DigitsWorld
import Johnson.Desc.First.K8.Four.AtWorld
import Johnson.Top.H.K3Worth

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.DgP Cb.Fo Cb.LdLkp Finset
open _root_.Fo _root_.Fo.Eq
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.K8.Four (first_four unknownOf digRows_worldAt)

section
variable {K : Type} [Field K] (ρ : Reading K) {J₀ : Type} {front : ℕ}

/-- **The payer into "planes" and "keys", under DigRows: no premise on the rows' claims.** -/
theorem k3PlanesKeys_of_rows (tl tl1 tl2 : HTailF2) (F G1 G2 : Fork) (c c1 c2 : Array Desc.Claim)
    (hJ : EqM.at (eqKeys tl) front F c = .ok ((tl1, G1), c1))
    (hB : EqM.at (eqCounts tl1) front G1 c1 = .ok ((tl2, G2), c2))
    (g : Heard) (hg : tl.heard = some g) (hs : tl.f9 = g.shape) (jLK : ℕ)
    (F' : Fork) (h0 : _root_.Fo.Later F' F)
    (hok : FoNums.ok g.shape = true) (hT : TailOK tl) (hF : Sized F)
    (hfull : 2 ^ g.shape.cK = g.shape.NC) (h5 : 5 ≤ g.shape.kT + g.shape.cK)
    (hn : ∀ q < 2, (g.zk.getD q #[]).size = (tl.zOf q).call.n)
    (h63 : ∀ q < 2, (tl.zOf q).call.n ≤ 63)
    (hP : ∀ q < 2, ∀ p ∈ piecesL tl q, PieceOK tl q (tl.zOf q).call.n p)
    (hD : ∀ q < 2, (piecesL tl q).Pairwise fun p p' =>
      p.off + 2 ^ p.b ≤ p'.off ∨ p'.off + 2 ^ p'.b ≤ p.off)
    (en : Ent3 → J₀) (mk : ℕ → J₀) (μ₀ : J₀ → K) (entry : ℕ → ℕ → ℕ → K)
    (H : Fork) (hH : _root_.Fo.Later G2 H)
    (hV : DigRows ρ tl g entry fun e => μ₀ (en e))
    (hz : ∀ k ∈ c2.toList, valC ρ (H.worldOf ρ (fun j => μ₀ (mk j)) entry) k = 0) :
    K3OutPlanes g.shape 5 jLK (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p)) ρ g F' ∧
      K3OutKeys g.shape 5 jLK (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
        (forK K (digL5 K tl en mk jLK Unit) () (zext μ₀)) ρ g F' := by
  have key : ∀ rs : Rounds K, HeardIs ρ g F' (endsOf g.shape 5 jLK rs) →
      K3Planes g.shape 5 jLK (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p)) rs ∧
        K3Keys g.shape 5 jLK (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
          (forK K (digL5 K tl en mk jLK Unit) () (zext μ₀)) rs := by
    intro rs hI
    have e0 : rdL ρ g.zb0 = (endsOf g.shape 5 jLK rs).zb0 := hI.zb0
    have e1 : rdL ρ g.zb1 = (endsOf g.shape 5 jLK rs).zb1 := hI.zb1
    obtain ⟨k1, k2, k3, k4, e, _, _, vJ, vP⟩ := eq_four ρ tl tl1 tl2 F G1 G2 c c1 c2 hJ hB g hg hs
      jLK rs F' hI h0 hok hT hF hfull h5 hn h63 hP hD en mk μ₀ entry (e0 ▸ hV.bz0) (e1 ▸ hV.bz1)
      hV.bz2 hV.piece H hH
    have m : ∀ x, x = k1 ∨ x = k2 ∨ x = k3 ∨ x = k4 → x ∈ c2.toList := by
      intro x hx
      rw [e]
      simp only [Array.toList_push, List.mem_append, List.mem_singleton]
      tauto
    have z1 := hz k1 (m k1 (by tauto))
    have z2 := hz k2 (m k2 (by tauto))
    have z3 := hz k3 (m k3 (by tauto))
    have z4 := hz k4 (m k4 (by tauto))
    simp only [List.map_cons, List.map_nil, z1, z2, z3, z4] at vJ vP
    injection vJ with j1 _
    injection vP with a1 t1
    injection t1 with a2 t2
    injection t2 with a3 _
    have hk := dig5_KFok_ends hT (by rw [hs]; exact hok) en mk jLK () 5 jLK rs
    rw [hs] at hk
    refine ⟨⟨a1.symm, a2.symm, a3.symm⟩, ?_⟩
    show claimJoin g.shape 5 jLK rs _ (keysAt g.shape 5 jLK
      (forK K (digL5 K tl en mk jLK Unit) () (zext μ₀)) rs) = 0
    exact (_root_.Fo.claimJoin_congr g.shape 5 jLK rs
      (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
      (fun c => (digKF tl en (fun c => (endsOf g.shape 5 jLK rs).zk.getD c []) c).val (zext μ₀))
      (keysAt g.shape 5 jLK (forK K (digL5 K tl en mk jLK Unit) () (zext μ₀)) rs)
      fun q hq => hk (zext μ₀) q hq).symm.trans j1.symm
  exact ⟨fun rs hI => (key rs hI).1, fun rs hI => (key rs hI).2⟩

end

section
variable {Cells Tok : Type}
  {x : Desc.First.Look.Place} {tl : HTailF2} {D : Desc.First.Look.Sent} {rad : OracleShape → ℕ}
  (seatT : Fin (digList x D rad).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ) {front : ℕ}

/-- **THE END.** -/
theorem digits_planesKeys_at_world {set : Params.Setting} {pp : ℕ}
    (HD : DigOK set x tl D rad pp) (w : Desc.Wit Cells Tok MsgT) (g : Heard) (F' : Fork)
    (tlS tl' tlX : HTailF2) (h5' : SameDig tl tlS) (funs : Array HFun) (F F1 Fc : Fork)
    (cls : List Desc.Claim) (he : equations front tlS funs F = .ok (tl', F1, cls))
    (hg : tlS.heard = some g) (hs : tlS.f9 = g.shape) (h0 : _root_.Fo.Later F' F)
    (hF : Sized F) (h5 : 5 ≤ g.shape.kT + g.shape.cK)
    (hn : ∀ q < 2, (g.zk.getD q #[]).size = (tlS.zOf q).call.n)
    (h63 : ∀ q < 2, (tlS.zOf q).call.n ≤ 63)
    (hP : ∀ q < 2, ∀ p ∈ piecesL tlS q, PieceOK tlS q (tlS.zOf q).call.n p)
    (hD : ∀ q < 2, (piecesL tlS q).Pairwise fun p p' =>
      p.off + 2 ^ p.b ≤ p'.off ∨ p'.off + 2 ^ p'.b ≤ p.off)
    (L : LinkCtx) (Dt : Desc.K9L.Bound Cb.Gl.E) (hX : SameZ tlS tlX) (T : CoefOK tlX Fc)
    (hRw : ∀ a ∈ allPieces tlS, a.2.r0 + a.2.Rp ≤ (Fc.trees.getD a.2.tree {}).R)
    (hH : _root_.Fo.Later F1 (coefAll tlX g Fc))
    (hcb : ∀ r < 32, ∀ i < tl.bzColumns,
      digVal x D rad (msgsOf D.codes (digList x D rad) seatT arr w) (.cell tl.ix.BZ r i) =
        some (unknownOf L Dt (Sum.inl (tl.ix.BZ, r, i))))
    (hcz : ∀ q < 2, ∀ p ∈ piecesL tl q, ∀ r < p.Rp, ∀ i < p.Cp,
      digVal x D rad (msgsOf D.codes (digList x D rad) seatT arr w)
          (.cell tl.ix.ZZ (p.r0 + r) (p.c0 + i)) =
        some (unknownOf L Dt (Sum.inl (tl.ix.ZZ, p.r0 + r, p.c0 + i))))
    (hm4 : ∀ k ∈ cls.take 4, ∀ s ∈ k.form.slots.toList,
      Dt.mask s.1 = digMu x D rad seatT arr w (mkOf x.arrays s.1))
    (hz : ∀ k ∈ cls.take 4,
      Desc.K9L.claimValue Reading.gl (Desc.K9L.worldAt Reading.gl L (coefAll tlX g Fc) Dt) k = 0) :
    K3OutPlanes tl.f9 5 x.F.next (digNu x tl D rad seatT arr w) Reading.gl g F' ∧
      K3OutKeys tl.f9 5 x.F.next (digNu x tl D rad seatT arr w)
        (forK Cb.Gl.E (digL5 Cb.Gl.E tl (enOf x.arrays) (mkOf x.arrays) x.F.next Unit) ()
          (zext (digMu x D rad seatT arr w))) Reading.gl g F' := by
  obtain ⟨tla, tlb, G1, c1, c2, hJ, hB, _, e4⟩ := first_four he
  have e9 : g.shape = tl.f9 := hs.symm.trans h5'.f9
  have hfull : 2 ^ g.shape.cK = g.shape.NC := by rw [e9]; exact dig_full HD
  have hzc : ∀ k ∈ c2.toList, valC Reading.gl ((coefAll tlX g Fc).worldOf Reading.gl
      (fun j => digMu x D rad seatT arr w (mkOf x.arrays j))
      (Desc.K9L.worldAt Reading.gl L (coefAll tlX g Fc) Dt).entry) k = 0 := by
    intro k hk
    have hk' : k ∈ cls.take 4 := by rw [e4]; exact hk
    rw [← valC_masks Reading.gl (coefAll tlX g Fc) (mask := Dt.mask)
      (mask' := fun j => digMu x D rad seatT arr w (mkOf x.arrays j))
      (Desc.K9L.worldAt Reading.gl L (coefAll tlX g Fc) Dt).entry k (hm4 k hk')]
    exact hz k hk'
  have k := k3PlanesKeys_of_rows Reading.gl tlS tla tlb F G1 F1 #[] c1 c2 hJ hB g hg hs x.F.next F'
    h0 (by rw [e9]; exact dig_foOk HD) (h5'.tailOK (shape2_parts HD.tail).2.1) hF hfull h5 hn h63
    hP hD (enOf x.arrays) (mkOf x.arrays) (digMu x D rad seatT arr w)
    (Desc.K9L.worldAt Reading.gl L (coefAll tlX g Fc) Dt).entry (coefAll tlX g Fc) hH
    (digRows_at_caller HD (by rw [← h5'.f9, hs]; exact hfull) h5' g _
      (fun q hq p hp => (hP q hq p hp).c0) _ (fun e => unknownOf L Dt (Sum.inl e)) hcb hcz
      (digRows_worldAt Reading.gl L Dt tlS tlX hX g hP Fc T hRw)) hzc
  rw [← hs, h5'.lay.f9, h5'.lay.pl, h5'.lay.lay] at k
  exact k

/-- **The two sentences of the table's items, at a state that holds F' and g.** -/
theorem digits_worth_at_world {S : Type} (fork : S → Option Fork) (heard : S → Option Heard)
    {set : Params.Setting} {pp : ℕ}
    (HD : DigOK set x tl D rad pp) (s : S) (w : Desc.Wit Cells Tok MsgT) (g : Heard) (F' : Fork)
    (hf : fork s = some F') (hh : heard s = some g)
    (tlS tl' tlX : HTailF2) (h5' : SameDig tl tlS) (funs : Array HFun) (F F1 Fc : Fork)
    (cls : List Desc.Claim) (he : equations front tlS funs F = .ok (tl', F1, cls))
    (hg : tlS.heard = some g) (hs : tlS.f9 = g.shape) (h0 : _root_.Fo.Later F' F)
    (hF : Sized F) (h5 : 5 ≤ g.shape.kT + g.shape.cK)
    (hn : ∀ q < 2, (g.zk.getD q #[]).size = (tlS.zOf q).call.n)
    (h63 : ∀ q < 2, (tlS.zOf q).call.n ≤ 63)
    (hP : ∀ q < 2, ∀ p ∈ piecesL tlS q, PieceOK tlS q (tlS.zOf q).call.n p)
    (hD : ∀ q < 2, (piecesL tlS q).Pairwise fun p p' =>
      p.off + 2 ^ p.b ≤ p'.off ∨ p'.off + 2 ^ p'.b ≤ p.off)
    (L : LinkCtx) (Dt : Desc.K9L.Bound Cb.Gl.E) (hX : SameZ tlS tlX) (T : CoefOK tlX Fc)
    (hRw : ∀ a ∈ allPieces tlS, a.2.r0 + a.2.Rp ≤ (Fc.trees.getD a.2.tree {}).R)
    (hH : _root_.Fo.Later F1 (coefAll tlX g Fc))
    (hcb : ∀ r < 32, ∀ i < tl.bzColumns,
      digVal x D rad (msgsOf D.codes (digList x D rad) seatT arr w) (.cell tl.ix.BZ r i) =
        some (unknownOf L Dt (Sum.inl (tl.ix.BZ, r, i))))
    (hcz : ∀ q < 2, ∀ p ∈ piecesL tl q, ∀ r < p.Rp, ∀ i < p.Cp,
      digVal x D rad (msgsOf D.codes (digList x D rad) seatT arr w)
          (.cell tl.ix.ZZ (p.r0 + r) (p.c0 + i)) =
        some (unknownOf L Dt (Sum.inl (tl.ix.ZZ, p.r0 + r, p.c0 + i))))
    (hm4 : ∀ k ∈ cls.take 4, ∀ s ∈ k.form.slots.toList,
      Dt.mask s.1 = digMu x D rad seatT arr w (mkOf x.arrays s.1))
    (hz : ∀ k ∈ cls.take 4,
      Desc.K9L.claimValue Reading.gl (Desc.K9L.worldAt Reading.gl L (coefAll tlX g Fc) Dt) k = 0) :
    K3WorthPlanes fork heard tl.f9 5 x.F.next (fun w => digNu x tl D rad seatT arr w) s w ∧
      K3WorthKeys fork heard tl.f9 5 x.F.next (fun w => digNu x tl D rad seatT arr w)
        (fun w => forK Cb.Gl.E (digL5 Cb.Gl.E tl (enOf x.arrays) (mkOf x.arrays) x.F.next Unit) ()
          (zext (digMu x D rad seatT arr w))) s w := by
  obtain ⟨a1, a2⟩ := digits_planesKeys_at_world seatT arr HD w g F' tlS tl' tlX h5' funs F F1 Fc cls
    he hg hs h0 hF h5 hn h63 hP hD L Dt hX T hRw hH hcb hcz hm4 hz
  exact ⟨k3WorthPlanes_of_out fork heard tl.f9 5 x.F.next _ hf hh a1,
    k3WorthKeys_of_out fork heard tl.f9 5 x.F.next _ _ hf hh a2⟩

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3PlanesKeys_of_rows
#print axioms VerifiableInference.OnPublicFiles.digits_planesKeys_at_world
#print axioms VerifiableInference.OnPublicFiles.digits_worth_at_world
