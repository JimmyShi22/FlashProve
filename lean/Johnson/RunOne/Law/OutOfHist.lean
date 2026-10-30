-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/OutOfHist.lean: BEHIND THE
KIND'S OWN BLOCK, OFF THE HISTORY ALONE: a record of the key file's first chain that was reached at
border 2 + 6 l + 3 holds what the kind's block has heard and the ledger that it has left; the
conclusion of the kind's law K03key_law.out holds of them: SO WHAT IS LEFT, READ AT ANY LATER
LEDGER, IS ONE: two outs at later ledgers are equal, and no form names a virtual entry.

Main names:
  out_of_hist: Hist₁ (Key.descriptionFromSource X N P) D (2 + 6 l + 3) a, the record's ledger G and what was heard g
    ⊢ there are rounds rs and places o, k with, at every riding type, list of homes, state and
    placing: at every ledger H later than G at which planesG says yes, and every K later than the
    ledger behind: no form names a virtual entry, and the typed lookup's lamRun on rs IS outOf at K.
  outs_one: two such outs are one.

Who pays which premise of Law.out: as in k03key_out (Johnson/RunOne/Law/K03KeyOut.lean), but the
block's yes and the words' test come off the history's last step (Reached.last), not off a piece.

Object: the kind's own block at its places in Key.descriptionFromSource X N P; K03key_law. User: the tie at the
fields r1_5 and r1_11.
Letters: X, N, P, D. Premises: those of rec_of_hist.
Limits. Nothing on soundness.

-/
import Johnson.RunOne.Law.K03KeyOut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.OutOfHist
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat OnBytes.Slice
open OnBytes.Model (Fork)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K3 VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (Xi FirstState Claim Source lookupSeat)
open Johnson.RunOne.Sound (FK fk_K3_at)
open Johnson.RunOne.Law.SeatsKeyD
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.LinkAtFK
open Johnson.RunOne.Law.LinkAtCut
open Johnson.RunOne.Law.WalkAtFK
open Johnson.RunOne.Law.RecOfHist
open Johnson.RunOne.Law.K03KeySits
open LPFD (Hist₁ Reached)

variable {X : Source} {N : H2U.PlaceNums} {P : VerifiableInference.Desc.Key.LaterPlaces}

/-- **The kind's law's conclusion, off the history.** -/
theorem out_of_hist (D : WholeD) (y : (frameAt D (allOf D) D.key₁ 0).E.Str)
    (hp : (FK X N P).planOk = true)
    (hR : RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes
      X.Y.k.oneTime.indexMasks.shape)
    (ha : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0) (l : ℕ)
    (hl : l < X.Y.k.oneTime.ranges.lookups.length) (a : Xi × FirstState)
    (hH : Hist₁ (VerifiableInference.Desc.Key.descriptionFromSource X N P) D (2 + 6 * l + 3) a) (G : Fork)
    (g : HeardG) (hG : a.2.base.fork = some G) (hg : a.2.base.heard = some g) :
    ∃ (rs : List Fmt.RoundView) (o k : ℕ → Slot),
      ∀ (T : Type) (hs : List Slot) (st : T)
        (sl : Slot → (datK T X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
          (Lof X.Y.k.oneTime l) hs).J)
        (H H' : Fork) (pl : List PlaneClaim) (u : OnBytes.K.Kc.Tape), PscRun.Later G H →
          planesG (faceOfLkp (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
              X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime l))) g H [] = some (pl, H', u) →
          (∀ x ∈ formsOf g pl, x.ents.isEmpty = true) ∧
          ∀ K, PscRun.Later H' K →
            (datK T X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
              (Lof X.Y.k.oneTime l) hs).lamRun (placesAt _ sl o k) st (flatRV rs) =
              outOf _ sl st K (fun j => a.2.base.home.getD j default) g pl := by
  have hW := fk_admitted X N P hp
  have hadm := Lk6.adm_of_tests X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) _
    (tests_at hW hl).2.1 (tests_at hW hl).2.2
  obtain ⟨a', b, rs, cols, hr, hb, hd, -⟩ := Reached.last (k := 2 + 6 * l + 2) hH
  rw [List.getElem?_map] at hb
  obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb
  have h2 := fk_K3_at X N P l _ (look_at X.Y.k.oneTime l hl)
  rw [← Nat.add_assoc] at h2
  obtain rfl := Option.some.inj (h2.symm.trans hb₀)
  have hrec := rec_of_hist D y hp hR ha (2 + 6 * l + 2) (by omega) a' hr
  rw [Nat.add_assoc] at hrec
  obtain ⟨⟨hS, hI⟩, -⟩ := (recAt_link X l 2 (by omega) a'.2).1 hrec
  have hw := held_words _ _ _ _ _ hd
  obtain ⟨-, hd'⟩ := VerifiableInference.Desc.Plain.held_decide _ _ _ _ _ hd
  obtain ⟨F, g0, G0, es, f1, f2, -, -, f5, f6⟩ := block_law _ _ _ _ _ hd'
  rw [f6] at hG hg ⊢
  obtain rfl : G0 = G := Option.some.inj hG
  obtain rfl : g0 = g := Option.some.inj hg
  obtain ⟨o, k, hh⟩ : ∃ o k : ℕ → Slot, HomeIs (faceOfLkp (Wf.lookupOf
      X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime l))) 0 o k
      fun j => a'.2.base.home.getD j default := by
    rw [hI.1]
    exact ⟨_, _, homeIs_of_size _ _ _ hI.2.2.2.2⟩
  refine ⟨rs.map noDigest, o, k, fun T hs st sl H H' pl u hGH hpl => ?_⟩
  obtain ⟨-, -, -, -, -, hout⟩ := K03key_law.out _ sl st _ 0 o k _ es F _ g0 G0
    (faceIsK T _ _ _ hs st hadm (d_le (tests_at hW hl).2.1)) hadm hh hw f2 (hS F f1) f5
  obtain ⟨-, h3, h4⟩ := hout H H' pl u hGH hpl
  exact ⟨h3, h4⟩

/-- **Two outs at later ledgers are one**, and no form names a virtual entry. -/
theorem outs_one (D : WholeD) (y : (frameAt D (allOf D) D.key₁ 0).E.Str)
    (hp : (FK X N P).planOk = true)
    (hR : RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes
      X.Y.k.oneTime.indexMasks.shape)
    (ha : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0) (l : ℕ)
    (hl : l < X.Y.k.oneTime.ranges.lookups.length) (a : Xi × FirstState)
    (hH : Hist₁ (VerifiableInference.Desc.Key.descriptionFromSource X N P) D (2 + 6 * l + 3) a) (G : Fork)
    (g : HeardG) (hG : a.2.base.fork = some G) (hg : a.2.base.heard = some g) (T : Type)
    (hs : List Slot) (st : T)
    (sl : Slot → (datK T X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
      (Lof X.Y.k.oneTime l) hs).J)
    (H H' : Fork) (pl : List PlaneClaim) (u : OnBytes.K.Kc.Tape) (K : Fork)
    (H₂ H₂' : Fork) (pl₂ : List PlaneClaim) (u₂ : OnBytes.K.Kc.Tape) (K₂ : Fork)
    (h1 : PscRun.Later G H)
    (h2 : planesG (faceOfLkp (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
      X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime l))) g H [] = some (pl, H', u))
    (h3 : PscRun.Later H' K) (h4 : PscRun.Later G H₂)
    (h5 : planesG (faceOfLkp (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
      X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime l))) g H₂ [] = some (pl₂, H₂', u₂))
    (h6 : PscRun.Later H₂' K₂) :
    outOf _ sl st K (fun j => a.2.base.home.getD j default) g pl =
        outOf _ sl st K₂ (fun j => a.2.base.home.getD j default) g pl₂ ∧
      ∀ x ∈ formsOf g pl, x.ents.isEmpty = true := by
  obtain ⟨rs, o, k, h⟩ := out_of_hist D y hp hR ha l hl a hH G g hG hg
  obtain ⟨e1, e2⟩ := h T hs st sl H H' pl u h1 h2
  obtain ⟨-, e3⟩ := h T hs st sl H₂ H₂' pl₂ u₂ h4 h5
  exact ⟨(e2 K h3).symm.trans (e3 K₂ h6), e1⟩

end Johnson.RunOne.Law.OutOfHist

#print axioms Johnson.RunOne.Law.OutOfHist.out_of_hist
#print axioms Johnson.RunOne.Law.OutOfHist.outs_one
