-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/TieFrontLayer.lean: THE
CLAIMS' TIE IN FRONT OF THE LAYER OF EACH LOOKUP (borders 5 and 11 of the key file's first chain),
ONE WAY, WITH THE LAYER'S OWN YES IN HAND: the relation of the links' row gives the table's claim:
the second of the four implications of a tie by keeps_conseq_yes (TieClaimLayer.lean) at the fields
r1_5 and r1_11.

How: that relation says the typed Done at the out read at SOME later ledgers; all such outs are one
(OutsOne: off the history); so Done stands at the ledger in which the kind's own closing at the
record's own ledger ends; that closing returns, with the layer's own three claims, since the layer's
did at that ledger with a debt marked; the layer's yes gives the sentences' side clauses
(TieSide.lean); so the three sentences stand (sentences_of_done, TieDoneBack.lean), at the decoder's
witness, which is the witness that the table's claim is given.

Main names:
  OutsOne X l s: two outs at later ledgers are one. outsOne_of_hist: off the history.
  claim_front_layer₀, claim_front_layer₁.

Object: the links' rows and the table of the first chain (TieStated.lean).
User: r1_5, r1_11 (FieldsLayer.lean).
Letters and premises: those of claim_front₀ | claim_front₁; the bits (as claim_behind₀); OutsOne,
which outsOne_of_hist pays off the history (outs_one, OutOfHist.lean). The kind's own closing at the
record's own ledger: closed_of_paid (PlanesPaid.lean).

Limits. One way. Nothing on soundness.

-/
import Johnson.RunOne.Law.TieClaimLayer
import Johnson.RunOne.Law.TieDoneBack
import Johnson.RunOne.Law.PlanesPaid
import Johnson.RunOne.Law.OutOfHist

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.TieFrontLayer
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Slice
open OnBytes.Model (Fork)
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K3 VerifiableInference.Desc.K3.KeyLaw
open OnBytes.K.Kc (Tape)
open VerifiableInference.Desc.Key (Xi FirstState Source KRead Where KItem closedAt mkOf matOf valOf
  lookupSeat lookupPlace layer caller rowsInOrder layerOrder)
open Johnson.RunOne.Sound (FK)
open Johnson.RunOne.KeyRows23 (BaseSt Fk fr₁ On₁ Cl₁)
open Johnson.RunOne.KeyRows1 (open₁ n₁ on₁_two plan₁ meaning₁At)
open Johnson.RunOne.Law.AtKeyD
open Johnson.RunOne.Law.RideKeyD
open Johnson.RunOne.Law.JoinKeyD
open Johnson.RunOne.Law.SeatsKeyD
open Johnson.RunOne.Law.LinkKeyD
open Johnson.RunOne.Law.PromKeyD
open Johnson.RunOne.Law.FrontSteps
open Johnson.RunOne.Law.SeatsAtFK
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.LinkAtCut
open Johnson.RunOne.Law.LettersAt
open Johnson.RunOne.Law.Walk
open Johnson.RunOne.Law.OffWalk
open Johnson.RunOne.Law.TieStated
open Johnson.RunOne.Law.TiePromise
open Johnson.RunOne.Law.TieKeys
open Johnson.RunOne.Law.TieClaimFront
open Johnson.RunOne.Law.TieClaimBehind
open Johnson.RunOne.Law.TieClaimL1
open Johnson.RunOne.Law.TieEarly
open Johnson.RunOne.Law.TieSide
open Johnson.RunOne.Law.TieDoneBack
open Johnson.RunOne.Law.PlanesPaid
open Johnson.RunOne.Law.OutOfHist
open Johnson.RunOne.Law.WalkAtFK
open Johnson.RunOne.Law.RecOfHist

/-- **Two outs at later ledgers are one**: what the history gives behind the kind's own block of
lookup l (K03key_law.out's last clause). -/
def OutsOne (X : Source) (l : ℕ) (s : FirstState) : Prop :=
  ∀ (G : Fork) (g : HeardG), s.base.fork = some G → s.base.heard = some g → ∀ (st : TK Xi)
    (H H' : Fork) (pl : List PlaneClaim) (u : Tape) (K H₂ H₂' : Fork) (pl₂ : List PlaneClaim)
    (u₂ : Tape) (K₂ : Fork), PscRun.Later G H →
    planesG (faceOfLkp (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
      (Lof X.Y.k.oneTime l))) g H [] = some (pl, H', u) → PscRun.Later H' K → PscRun.Later G H₂ →
    planesG (faceOfLkp (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
      (Lof X.Y.k.oneTime l))) g H₂ [] = some (pl₂, H₂', u₂) → PscRun.Later H₂' K₂ →
    outOf (AK X.Y.k.oneTime X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
        X.Y.k.oneTime l)
        (handed (cntO X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
            X.Y.k.oneTime))
          (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape) l)
        (handed (cntK X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
            X.Y.k.oneTime))
          (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape) l) 0 (TK Xi))
      (slk X.Y.k.oneTime X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
          X.Y.k.oneTime l)
        (handed (cntO X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
            X.Y.k.oneTime))
          (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape) l)
        (handed (cntK X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
            X.Y.k.oneTime))
          (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape) l) 0 (TK Xi)) st K
      (fun j => (homeT X.Y.k.oneTime X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
          (Lof X.Y.k.oneTime l)
        (handed (cntO X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
            X.Y.k.oneTime))
          (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape) l)
        (handed (cntK X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
            X.Y.k.oneTime))
          (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape) l) 0).getD j default) g pl =
    outOf (AK X.Y.k.oneTime X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
        X.Y.k.oneTime l)
        (handed (cntO X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
            X.Y.k.oneTime))
          (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape) l)
        (handed (cntK X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
            X.Y.k.oneTime))
          (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape) l) 0 (TK Xi))
      (slk X.Y.k.oneTime X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
          X.Y.k.oneTime l)
        (handed (cntO X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
            X.Y.k.oneTime))
          (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape) l)
        (handed (cntK X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
            X.Y.k.oneTime))
          (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape) l) 0 (TK Xi)) st K₂
      (fun j => (homeT X.Y.k.oneTime X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
          (Lof X.Y.k.oneTime l)
        (handed (cntO X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
            X.Y.k.oneTime))
          (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape) l)
        (handed (cntK X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
            X.Y.k.oneTime))
          (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape) l) 0).getD j default) g pl₂


variable {Cells Mm Smp Rec : Type} {X : Source} {N : H2U.PlaceNums}
  {P : VerifiableInference.Desc.Key.LaterPlaces} {D : WholeD} {B : BaseSt Cells Mm Smp Rec}
  {at_ : Where} {R : KRead Cells Mm} {coll : Strs → Rec → Prop}

/-- **OutsOne, off the history.** -/
theorem outsOne_of_hist (D : WholeD) (y : (frameAt D (allOf D) D.key₁ 0).E.Str)
    (hp : (FK X N P).planOk = true)
    (hR : RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes
      X.Y.k.oneTime.indexMasks.shape)
    (ha : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0) (l : ℕ)
    (hl : l < X.Y.k.oneTime.ranges.lookups.length) (a : Xi × FirstState)
    (hH : LPFD.Hist₁ (VerifiableInference.Desc.Key.descriptionFromSource X N P) D (2 + 6 * l + 3) a) :
    OutsOne X l a.2 := by
  intro G g hG hg st H H' pl u K H₂ H₂' pl₂ u₂ K₂ h1 h2 h3 h4 h5 h6
  have hrec := rec_of_hist D y hp hR ha (2 + 6 * l + 3) (by omega) a hH
  rw [Nat.add_assoc] at hrec
  obtain ⟨⟨hI, -⟩, -⟩ := (recAt_link X l 3 (by omega) a.2).1 hrec
  have e := (outs_one D y hp hR ha l hl a hH G g hG hg (TK Xi) _ st
    (slk X.Y.k.oneTime X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
        X.Y.k.oneTime l)
      (handed (cntO X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
          X.Y.k.oneTime))
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape) l)
      (handed (cntK X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
          X.Y.k.oneTime))
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape) l) 0 (TK Xi))
    H H' pl u K H₂ H₂' pl₂ u₂ K₂ h1 h2 h3 h4 h5 h6).1
  rw [hI.1] at e
  exact e

set_option maxHeartbeats 1600000 in
/-- **THE CLAIMS' TIE IN FRONT OF THE LAYER OF LOOKUP 0, ONE WAY, WITH THE LAYER'S YES IN HAND**:
border 5. -/
theorem claim_front_layer₀ (hS : B.SmReads) (hsame : R.same = fun a b => readE a = readE b)
    (hp : (FK X N P).planOk = true) (hn : X.Y.k.oneTime.ranges.lookups.length = 2)
    (hbit : ∀ (valB : ℕ → E) (n : ℕ),
      n < 2 ^ ((faceOfLkp (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
          X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime 0))).mu + (faceOfLkp (Wf.lookupOf
              X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime
                  0))).d) →
      readE (VerifiableInference.Desc.Key.bitVec X.Y.k.oneTime.ranges X.Y.k.oneTime.codes 0 valB n)
          =
        Planes.bitsOf X.Y.k.oneTime.ranges X.Y.k.oneTime.codes 0 (fun k => readE (valB k))
          (n / 2 ^ (faceOfLkp (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
              X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime 0))).mu) (n % 2 ^ (faceOfLkp (Wf.lookupOf
                  X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime
                      0))).mu))
    (a : (Xi × FirstState) × (fr₁ D).E.Str) (hon : On₁ X N P D B at_ R coll 5 a)
    (hT : (rowT X N P D B at_ R coll 0 3).on a)
    (hone : OutsOne X 0 a.1.2)
    (s' : FirstState) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hyes : (layer X.Y.k.oneTime X.set 0 (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
        X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime 0))
      (claimsIn [caller X.Y.k.oneTime 0 (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
          X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime 0)),
        lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace X.set 0 (Wf.lookupOf
                X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime 0)))]
        [(1, "objects"), (1, "planes"), (1, "guests")])).decide a.1.2 rs gs = .ok s')
    (hrel : (rowT X N P D B at_ R coll 0 3).rel a) : Cl₁ X N P D B at_ R 5 a := by
  obtain ⟨⟨p₀, s⟩, y⟩ := a
  have h2 := on₁_two _ _ _ _ _ _ _ 5 _ hon
  have hW := fk_admitted X N P hp
  have hid := fk_messageId X N P hp
  have t0 := tests_at hW (i := 0) (by rw [hn]; omega)
  have t1 := tests_at hW (i := 1) (by rw [hn]; omega)
  have hadm := Lk6.adm_of_tests X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) _
      t0.2.1 t0.2.2
  unfold rowT at hT hrel
  obtain ⟨-, ⟨hInv, hHeard⟩, -⟩ := (rows7_on (Fr := fr₁ D) _ _ _ _ _ _ _ _ _ p₀ _ _ _ _ _ _ 0 3
    (by omega) s y).1 ((upF_on (Fr := fr₁ D) _ p₀ s y).1 hT)
  obtain ⟨G, g, hG, hg, -, -, -, d6, d7⟩ := hHeard
  have hG : s.base.fork = some G := hG
  have hg : s.base.heard = some g := hg
  obtain ⟨w, ⟨hdec, hE, hLate, hO⟩, bb, ⟨G1, g1, H, pl, H', tp, K, o1, o2, o3, o4, o5, rfl⟩, hDone⟩
      :=
    (upF_rel (Fr := fr₁ D) _ p₀ s y).1 hrel
  obtain rfl : G1 = G := Option.some.inj ((show s.base.fork = some G1 from o1).symm.trans hG)
  obtain rfl : g1 = g := Option.some.inj ((show s.base.heard = some g1 from o2).symm.trans hg)
  obtain ⟨q1, q2, q3⟩ := decT_some hdec
  -- the layer's yes
  obtain ⟨cls, s1, F, g', rows, keys, c1, c2, c3, c4, c5, -⟩ := layerD_law hyes
  obtain ⟨pl₂, H₂, u₂, p1, rfl, rfl⟩ := claimsD_law hG hg c1
  obtain rfl : H₂.paid g1.owedPlanes = F := Option.some.inj c2
  obtain rfl : g1 = g' := Option.some.inj (hg.symm.trans c3)
  rw [filterL, List.length_map] at c4
  have c4' : rowsInOrder (Wf.planesAt X.Y.k.oneTime.ranges X.Y.k.oneTime.codes 0)
      (layerOrder g1.rows.toList.length) (H₂.paid g1.owedPlanes) s.base.home
      (g1.rows.toList.map Sum.inl ++ pl₂.map Sum.inr) = some rows := c4
  have c5' : keyClaims (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
      (Lof X.Y.k.oneTime 0)) (H₂.paid g1.owedPlanes) s.base.home g1 = some keys := c5
  obtain ⟨a0, b0, e0, rfl⟩ := planesG_three p1
  have hne : g1.rows.toList ≠ [] := by
    intro h0
    rw [h0] at c4'
    unfold rowsInOrder at c4'
    simp [layerOrder] at c4'
  obtain ⟨front, bits, hfb⟩ : ∃ front bits, g1.rows.toList = front ++ [bits] :=
    ⟨_, _, (List.dropLast_append_getLast hne).symm⟩
  rw [hfb] at c4'
  have hgr := rowsByD_group _ (H₂.paid g1.owedPlanes) s.base.home front bits a0 b0 e0 rows c4'
  rw [← hfb] at hgr
  obtain ⟨sO, sP, h3l⟩ := group_side hgr
  have sK := keys_side c5'
  -- the kind's own closing at the record's own ledger
  obtain ⟨G', hc, -⟩ := closed_of_paid p1
  obtain ⟨tp', hpl'⟩ := closed_planes hc
  have hout := (hone G1 g1 hG hg (stK p₀ 0 s) H H' pl tp K G1 G' [a0, b0, e0] tp' G' o3 o4 o5
    (PscRun.Later.refl _) hpl' (PscRun.Later.refl _))
  have hDone' := (congrArg (fun o => Lk6.Dat.Done _ _ o) hout).mp hDone
  rw [hInv.1] at sO sP sK
  obtain ⟨f1, f2, f3⟩ := sentences_of_done (A := (AK X.Y.k.oneTime X.Y.k.oneTime.ranges.messageId
      (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime 0) (handed (cntO
          X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime))
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape) 0)
      (handed (cntK X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
          X.Y.k.oneTime))
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape) 0) 0 (TK Xi)))
    (sl := (slk X.Y.k.oneTime X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
        X.Y.k.oneTime 0) (handed (cntO X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
            X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime))
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape) 0)
      (handed (cntK X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
          X.Y.k.oneTime))
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape) 0) 0 (TK Xi)))
    (μ := msgk X.Y.k.oneTime 0 X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
        X.Y.k.oneTime 0) (handed (cntO X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
            X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime))
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape) 0)
      (handed (cntK X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
          X.Y.k.oneTime))
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape) 0) 0 (TK Xi) (wdT X R) (mxT X R)
            w.1)
    (w := wdT X R w.1) (x := X.Y.k.oneTime.ranges) (codes := X.Y.k.oneTime.codes) (i := 0) hadm
    (tiedK _ _ _ _ _ _ _ _ _ _) (Lof X.Y.k.oneTime 0) t0.1 (mkOf (plan₁ X.Y.k.oneTime) R w.1)
    (fun _ _ => rfl) (stK p₀ 0 s) X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
    (matOf (plan₁ X.Y.k.oneTime) R w.1) rfl t0.2.1 t0.2.2
    (by
      have hk := keysAreK (T := TK Xi) (id := X.Y.k.oneTime.ranges.messageId)
        (m := Wf.matrixOf X.Y.k.oneTime.lin) (l := Lof X.Y.k.oneTime 0) (hs := _) (stK p₀ 0 s)
        (msgk X.Y.k.oneTime 0 X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
            X.Y.k.oneTime 0) (handed (cntO X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
                X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime))
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape) 0)
          (handed (cntK X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
              X.Y.k.oneTime))
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape) 0) 0 (TK Xi) (wdT X R) (mxT X R)
            w.1)
      rw [matOf_cut] at hk
      exact hk)
    (VerifiableInference.Desc.Key.bitVec X.Y.k.oneTime.ranges X.Y.k.oneTime.codes 0
      fun i => R.val (R.of w.1 1) .main i)
    (fun n hnn => by
      rw [hbit _ n hnn, hid]
      rfl)
    g1 G1 G' [a0, b0, e0] hc (d6.trans (List.length_map _))
    (fun q hq => d7 q (lt_of_lt_of_eq hq (List.length_map _).symm)) hne rfl sO sP sK hDone'
  have e0' : VerifiableInference.Desc.Key.lkpOf (plan₁ X.Y.k.oneTime) X.Y.k.oneTime.ranges 0 = some
      (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime
          0)) :=
    Johnson.RunOne.Law.LinkAtFK.look_at X.Y.k.oneTime 0 (by rw [hn]; omega)
  have hhome : VerifiableInference.Desc.Key.K3At.home Johnson.RunOne.KeyRows1.k3At₁ s = _ := hInv.1
  have hmem : ∀ i ∈ open₁ 2 5, i = KItem.unmarked ∨ i = .pinT ∨ i = .inRange 1 ∨ i = .pin 0 ∨
      i = .srow 0 ∨ i = .pin 1 ∨ i = .srow 1 ∨ i = .forms 0 "objects" ∨ i = .worth 0 "planes" ∨
      i = .worth 0 "keys" := by decide
  refine ⟨w.1, ?_⟩
  show ∀ i ∈ open₁ (n₁ X.Y.k.oneTime) 5, _
  rw [h2]
  intro i hi
  rcases hmem i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rfl
  · exact (pinw_atSt p₀ 0 s _ _).1 q1
  · refine ⟨_, t1.1, ?_⟩
    rw [hsame]
    exact (inRange_iff _ _ _ _ t1.2.1 t1.2.2).2 (hLate 1 (by omega) (by rw [hn]; omega))
  · exact (pin_atSt hS p₀ 0 s _ _ _ _).1 q2
  · exact srow_atSt 0 p₀ 0 s _ _ _ (hO (strsOf (fr₁ D) y)).1
  · exact (pin_atSt hS p₀ 0 s _ _ _ _).1 q3
  · exact srow_atSt 1 p₀ 0 s _ _ _ (hO (strsOf (fr₁ D) y)).2
  · refine ⟨rfl, _, g1, G1, e0', hg, hG, ?_⟩
    rw [hsame, hhome]
    exact f1
  · refine ⟨_, _, g1, G1, e0', t0.1, hg, hG, Or.inl ⟨rfl, ?_⟩⟩
    rw [hsame, hhome]
    exact f2
  · refine ⟨_, _, g1, G1, e0', t0.1, hg, hG, Or.inr ⟨rfl, ?_⟩⟩
    rw [hsame, hhome]
    exact f3

set_option maxHeartbeats 1600000 in
/-- **THE CLAIMS' TIE IN FRONT OF THE LAYER OF LOOKUP 1, ONE WAY, WITH THE LAYER'S YES IN HAND**:
border 11. -/
theorem claim_front_layer₁ (hS : B.SmReads) (hsame : R.same = fun a b => readE a = readE b)
    (hp : (FK X N P).planOk = true) (hn : X.Y.k.oneTime.ranges.lookups.length = 2)
    (hbit : ∀ (valB : ℕ → E) (n : ℕ),
      n < 2 ^ ((faceOfLkp (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
          X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime 1))).mu + (faceOfLkp (Wf.lookupOf
              X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime
                  1))).d) →
      readE (VerifiableInference.Desc.Key.bitVec X.Y.k.oneTime.ranges X.Y.k.oneTime.codes 1 valB n)
          =
        Planes.bitsOf X.Y.k.oneTime.ranges X.Y.k.oneTime.codes 1 (fun k => readE (valB k))
          (n / 2 ^ (faceOfLkp (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
              X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime 1))).mu) (n % 2 ^ (faceOfLkp (Wf.lookupOf
                  X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime
                      1))).mu))
    (a : (Xi × FirstState) × (fr₁ D).E.Str) (hon : On₁ X N P D B at_ R coll 11 a)
    (hoff : RowsOff a.1.2) (hT : (rowT X N P D B at_ R coll 1 3).on a)
    (hone : OutsOne X 1 a.1.2)
    (s' : FirstState) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hyes : (layer X.Y.k.oneTime X.set 1 (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
        X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime 1))
      (claimsIn [caller X.Y.k.oneTime 1 (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
          X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime 1)),
        lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace X.set 1 (Wf.lookupOf
                X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime 1)))]
        [(1, "objects"), (1, "planes"), (1, "guests")])).decide a.1.2 rs gs = .ok s')
    (hrel : (rowT X N P D B at_ R coll 1 3).rel a) : Cl₁ X N P D B at_ R 11 a := by
  obtain ⟨⟨p₀, s⟩, y⟩ := a
  have h2 := on₁_two _ _ _ _ _ _ _ 11 _ hon
  have hW := fk_admitted X N P hp
  have hid := fk_messageId X N P hp
  have t0 := tests_at hW (i := 0) (by rw [hn]; omega)
  have t1 := tests_at hW (i := 1) (by rw [hn]; omega)
  have hadm := Lk6.adm_of_tests X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) _
      t1.2.1 t1.2.2
  unfold rowT at hT hrel
  obtain ⟨-, ⟨hInv, hHeard⟩, -⟩ := (rows7_on (Fr := fr₁ D) _ _ _ _ _ _ _ _ _ p₀ _ _ _ _ _ _ 1 3
    (by omega) s y).1 ((upF_on (Fr := fr₁ D) _ p₀ s y).1 hT)
  obtain ⟨G, g, hG, hg, -, -, -, d6, d7⟩ := hHeard
  have hG : s.base.fork = some G := hG
  have hg : s.base.heard = some g := hg
  obtain ⟨w, ⟨hdec, hE, hLate, hO⟩, bb, ⟨G1, g1, H, pl, H', tp, K, o1, o2, o3, o4, o5, rfl⟩, hDone⟩
      :=
    (upF_rel (Fr := fr₁ D) _ p₀ s y).1 hrel
  obtain rfl : G1 = G := Option.some.inj ((show s.base.fork = some G1 from o1).symm.trans hG)
  obtain rfl : g1 = g := Option.some.inj ((show s.base.heard = some g1 from o2).symm.trans hg)
  obtain ⟨q1, q2, q3⟩ := decT_some hdec
  -- the layer's yes
  obtain ⟨cls, s1, F, g', rows, keys, c1, c2, c3, c4, c5, -⟩ := layerD_law hyes
  obtain ⟨pl₂, H₂, u₂, p1, rfl, rfl⟩ := claimsD_law hG hg c1
  obtain rfl : H₂.paid g1.owedPlanes = F := Option.some.inj c2
  obtain rfl : g1 = g' := Option.some.inj (hg.symm.trans c3)
  rw [filterL, List.length_map] at c4
  have c4' : rowsInOrder (Wf.planesAt X.Y.k.oneTime.ranges X.Y.k.oneTime.codes 1)
      (layerOrder g1.rows.toList.length) (H₂.paid g1.owedPlanes) s.base.home
      (g1.rows.toList.map Sum.inl ++ pl₂.map Sum.inr) = some rows := c4
  have c5' : keyClaims (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
      (Lof X.Y.k.oneTime 1)) (H₂.paid g1.owedPlanes) s.base.home g1 = some keys := c5
  obtain ⟨a0, b0, e0, rfl⟩ := planesG_three p1
  have hne : g1.rows.toList ≠ [] := by
    intro h0
    rw [h0] at c4'
    unfold rowsInOrder at c4'
    simp [layerOrder] at c4'
  obtain ⟨front, bits, hfb⟩ : ∃ front bits, g1.rows.toList = front ++ [bits] :=
    ⟨_, _, (List.dropLast_append_getLast hne).symm⟩
  rw [hfb] at c4'
  have hgr := rowsByD_group _ (H₂.paid g1.owedPlanes) s.base.home front bits a0 b0 e0 rows c4'
  rw [← hfb] at hgr
  obtain ⟨sO, sP, h3l⟩ := group_side hgr
  have sK := keys_side c5'
  -- the kind's own closing at the record's own ledger
  obtain ⟨G', hc, -⟩ := closed_of_paid p1
  obtain ⟨tp', hpl'⟩ := closed_planes hc
  have hout := (hone G1 g1 hG hg (stK p₀ 1 s) H H' pl tp K G1 G' [a0, b0, e0] tp' G' o3 o4 o5
    (PscRun.Later.refl _) hpl' (PscRun.Later.refl _))
  have hDone' := (congrArg (fun o => Lk6.Dat.Done _ _ o) hout).mp hDone
  rw [hInv.1] at sO sP sK
  obtain ⟨f1, f2, f3⟩ := sentences_of_done (A := (AK X.Y.k.oneTime X.Y.k.oneTime.ranges.messageId
      (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime 1) (handed (cntO
          X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime))
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape) 1)
      (handed (cntK X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
          X.Y.k.oneTime))
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape) 1) 0 (TK Xi)))
    (sl := (slk X.Y.k.oneTime X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
        X.Y.k.oneTime 1) (handed (cntO X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
            X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime))
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape) 1)
      (handed (cntK X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
          X.Y.k.oneTime))
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape) 1) 0 (TK Xi)))
    (μ := msgk X.Y.k.oneTime 1 X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
        X.Y.k.oneTime 1) (handed (cntO X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
            X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime))
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape) 1)
      (handed (cntK X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
          X.Y.k.oneTime))
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape) 1) 0 (TK Xi) (wdT X R) (mxT X R)
            w.1)
    (w := wdT X R w.1) (x := X.Y.k.oneTime.ranges) (codes := X.Y.k.oneTime.codes) (i := 1) hadm
    (tiedK _ _ _ _ _ _ _ _ _ _) (Lof X.Y.k.oneTime 1) t1.1 (mkOf (plan₁ X.Y.k.oneTime) R w.1)
    (fun _ _ => rfl) (stK p₀ 1 s) X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
    (matOf (plan₁ X.Y.k.oneTime) R w.1) rfl t1.2.1 t1.2.2
    (by
      have hk := keysAreK (T := TK Xi) (id := X.Y.k.oneTime.ranges.messageId)
        (m := Wf.matrixOf X.Y.k.oneTime.lin) (l := Lof X.Y.k.oneTime 1) (hs := _) (stK p₀ 1 s)
        (msgk X.Y.k.oneTime 1 X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
            X.Y.k.oneTime 1) (handed (cntO X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
                X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime))
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape) 1)
          (handed (cntK X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
              X.Y.k.oneTime))
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape) 1) 0 (TK Xi) (wdT X R) (mxT X R)
            w.1)
      rw [matOf_cut] at hk
      exact hk)
    (VerifiableInference.Desc.Key.bitVec X.Y.k.oneTime.ranges X.Y.k.oneTime.codes 1
      fun i => R.val (R.of w.1 1) .main i)
    (fun n hnn => by
      rw [hbit _ n hnn, hid]
      rfl)
    g1 G1 G' [a0, b0, e0] hc (d6.trans (List.length_map _))
    (fun q hq => d7 q (lt_of_lt_of_eq hq (List.length_map _).symm)) hne rfl sO sP sK hDone'
  have e0' : VerifiableInference.Desc.Key.lkpOf (plan₁ X.Y.k.oneTime) X.Y.k.oneTime.ranges 1 = some
      (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime
          1)) :=
    Johnson.RunOne.Law.LinkAtFK.look_at X.Y.k.oneTime 1 (by rw [hn]; omega)
  have hhome : VerifiableInference.Desc.Key.K3At.home Johnson.RunOne.KeyRows1.k3At₁ s = _ := hInv.1
  have hmem : ∀ i ∈ open₁ 2 11, i = KItem.unmarked ∨ i = .pinT ∨ i = .pin 0 ∨
      i = .srow 0 ∨ i = .pin 1 ∨ i = .srow 1 ∨ i = .rows 0 ∨ i = .kclaims 0 ∨
      i = .forms 1 "objects" ∨ i = .worth 1 "planes" ∨ i = .worth 1 "keys" := by decide
  refine ⟨w.1, ?_⟩
  show ∀ i ∈ open₁ (n₁ X.Y.k.oneTime) 11, _
  rw [h2]
  intro i hi
  rcases hmem i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rfl
  · exact (pinw_atSt p₀ 1 s _ _).1 q1
  · exact (pin_atSt hS p₀ 1 s _ _ _ _).1 q2
  · exact srow_atSt 0 p₀ 1 s _ _ _ (hO (strsOf (fr₁ D) y)).1
  · exact (pin_atSt hS p₀ 1 s _ _ _ _).1 q3
  · exact srow_atSt 1 p₀ 1 s _ _ _ (hO (strsOf (fr₁ D) y)).2
  · obtain ⟨rows0, keys0, z1, z2, z3, z4⟩ := done_zero 11 (Or.inr rfl) ((p₀, s), y) hon _ t0.1
    obtain ⟨rw0, ky0, e1, e2, e3, e4⟩ := hE 0 (by omega)
    have e1' : (s.base.rows.take 1)[0]? = some rw0 := e1
    rw [List.getElem?_take_of_lt (by omega)] at e1'
    obtain rfl := Option.some.inj (e1'.symm.trans z1)
    exact rows_of_allSay hsame 0 p₀ 1 s _ w.1 hoff rw0 z1 z2 e3
  · obtain ⟨rows0, keys0, z1, z2, z3, z4⟩ := done_zero 11 (Or.inr rfl) ((p₀, s), y) hon _ t0.1
    obtain ⟨rw0, ky0, e1, e2, e3, e4⟩ := hE 0 (by omega)
    have e2' : (s.base.keys.take 1)[0]? = some ky0 := e2
    rw [List.getElem?_take_of_lt (by omega)] at e2'
    obtain rfl := Option.some.inj (e2'.symm.trans z3)
    exact kclaims_of_pend hsame 0 p₀ s _ w.1 _ t0.1 ky0 z3 z4 e4
  · refine ⟨rfl, _, g1, G1, e0', hg, hG, ?_⟩
    rw [hsame, hhome]
    exact f1
  · refine ⟨_, _, g1, G1, e0', t1.1, hg, hG, Or.inl ⟨rfl, ?_⟩⟩
    rw [hsame, hhome]
    exact f2
  · refine ⟨_, _, g1, G1, e0', t1.1, hg, hG, Or.inr ⟨rfl, ?_⟩⟩
    rw [hsame, hhome]
    exact f3

end Johnson.RunOne.Law.TieFrontLayer

#print axioms Johnson.RunOne.Law.TieFrontLayer.outsOne_of_hist
#print axioms Johnson.RunOne.Law.TieFrontLayer.claim_front_layer₀
#print axioms Johnson.RunOne.Law.TieFrontLayer.claim_front_layer₁
