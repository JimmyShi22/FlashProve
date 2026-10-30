-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/TieClaimBehind.lean: THE
CLAIMS' TIE BEHIND THE KIND'S OWN BLOCK OF THE FIRST LOOKUP (border 5 of the key file's first
chain), ONE WAY: under the table's promise and the condition of the links' row, the table's claim
gives the relation of the links' row at the filling from the table's letters: the fourth of the four
implications that a tie by Leads.conseq asks at the field r1_4.

How: the table's witness is pinned, so the decoder gives a witness; the two agree (TieAgree.lean);
the riding items pass (as at border 4, TieClaimBack.lean); the table's three sentences on what the
kind's block leaves, which stand at the table's witness, give the typed out-relation at the entries
read off the decoder's witness (done_of_sentences, TieDone.lean): what they read of a witness is
what the two agree in; the out is read at the ledger in which the kind's own closing ends, which is
later than itself.

Main names:
  closed_planes: closedAt's yes is planesG's at the record's own ledger.
  claim_behind₀: On₁ … 5 b, (rowT 0 3).on b, Cl₁ … 5 b ⊢ (rowT 0 3).rel b.

Object: the key file's first chain's table (On₁, Cl₁) and the links' rows (rowT, TieStated.lean).
User: r1_4_whole (FieldR14W.lean).
Letters: the table's B (under SmReads), at_, R (same: "read alike"), coll. Premises: the plan's
tests · two lookups · THE BITS: the table's bitVec, read, is the library's Planes.bitsOf at every
real index: at the table's present text that rests on the five facts on the layout
(LayoutFull.lean); at the text bitVecL | bitVecS (TiePlanes.lean) it is a theorem
without a premise. (Where this
and lean/THEOREM.md differ, the page holds.)

Limits. One way, one border, the first lookup. Nothing on soundness.

-/
import Johnson.RunOne.Law.TieClaimBack
import Johnson.RunOne.Law.TieDone

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.TieClaimBehind
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Slice
open OnBytes.Model (Fork)
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K3 VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (Xi FirstState Source KRead Where KItem closedAt mkOf matOf valOf)
open Johnson.RunOne.Sound (FK)
open Johnson.RunOne.KeyRows23 (BaseSt Fk fr₁ On₁ Cl₁)
open Johnson.RunOne.KeyRows1 (open₁ n₁ on₁_two plan₁ meaning₁At)
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
open Johnson.RunOne.Law.TieStated
open Johnson.RunOne.Law.TiePromise
open Johnson.RunOne.Law.TieKeys
open Johnson.RunOne.Law.TieClaimFront
open Johnson.RunOne.Law.TieClaimBack
open Johnson.RunOne.Law.TieAgree
open Johnson.RunOne.Law.TieDone

/-- closedAt's yes is planesG's at the record's own ledger. -/
theorem closed_planes {f : Face} {g : HeardG} {G G' : Fork} {cl : List PlaneClaim}
    (h : closedAt f g G = some (cl, G')) : ∃ u, planesG f g G [] = some (cl, G', u) := by
  unfold closedAt at h
  obtain ⟨z, hz, e⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  exact ⟨z.2.2, hz⟩

variable {Cells Mm Smp Rec : Type} {X : Source} {N : H2U.PlaceNums}
  {P : VerifiableInference.Desc.Key.LaterPlaces} {D : WholeD} {B : BaseSt Cells Mm Smp Rec}
  {at_ : Where} {R : KRead Cells Mm} {coll : Strs → Rec → Prop}

set_option maxHeartbeats 1600000 in
/-- **THE CLAIMS' TIE BEHIND THE KIND'S BLOCK OF LOOKUP 0, ONE WAY.** -/
theorem claim_behind₀ (hS : B.SmReads) (hsame : R.same = fun a b => readE a = readE b)
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
    (b : (Xi × FirstState) × (fr₁ D).E.Str) (hon : On₁ X N P D B at_ R coll 5 b)
    (hT : (rowT X N P D B at_ R coll 0 3).on b) (hcl : Cl₁ X N P D B at_ R 5 b) :
    (rowT X N P D B at_ R coll 0 3).rel b := by
  obtain ⟨⟨p₀, s⟩, y⟩ := b
  have h2 := on₁_two _ _ _ _ _ _ _ 5 _ hon
  have hW := fk_admitted X N P hp
  have hid := fk_messageId X N P hp
  have t0 := tests_at hW (i := 0) (by rw [hn]; omega)
  have t1 := tests_at hW (i := 1) (by rw [hn]; omega)
  have hadm := Lk6.adm_of_tests X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) _
      t0.2.1 t0.2.2
  obtain ⟨w', hw'⟩ := hcl
  have hall : ∀ i ∈ open₁ (n₁ X.Y.k.oneTime) 5, _ := hw'
  rw [h2] at hall
  have iT := hall .pinT (by decide)
  have i0 := hall (.pin 0) (by decide)
  have i1 := hall (.pin 1) (by decide)
  have r1 := hall (.inRange 1) (by decide)
  have s0 := hall (.srow 0) (by decide)
  have s1 := hall (.srow 1) (by decide)
  obtain ⟨-, Sg1, g1, G1, a1, a2, a3, fo⟩ := hall (.forms 0 "objects") (by decide)
  obtain ⟨Sg2, L2, g2, G2, b1, b2, b3, b4, wp⟩ := hall (.worth 0 "planes") (by decide)
  obtain ⟨Sg3, L3, g3, G3, c1, c2, c3, c4, wk⟩ := hall (.worth 0 "keys") (by decide)
  have e0 : VerifiableInference.Desc.Key.lkpOf (plan₁ X.Y.k.oneTime) X.Y.k.oneTime.ranges 0 = some
      (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime
          0)) :=
    Johnson.RunOne.Law.LinkAtFK.look_at X.Y.k.oneTime 0 (by rw [hn]; omega)
  obtain rfl := Option.some.inj (a1.symm.trans e0)
  obtain rfl := Option.some.inj (b1.symm.trans e0)
  obtain rfl := Option.some.inj (c1.symm.trans e0)
  obtain rfl := Option.some.inj (b2.symm.trans t0.1)
  obtain rfl := Option.some.inj (c2.symm.trans t0.1)
  obtain rfl := Option.some.inj (b3.symm.trans a2)
  obtain rfl := Option.some.inj (c3.symm.trans a2)
  obtain rfl := Option.some.inj (b4.symm.trans a3)
  obtain rfl := Option.some.inj (c4.symm.trans a3)
  have wp' := wp.resolve_right fun h => absurd h.1 (by decide)
  have wk' := wk.resolve_left fun h => absurd h.1 (by decide)
  obtain ⟨u, hu⟩ := decT_of_pins (X := X) (N := N) (P := P) (D := D) (B := B) (at_ := at_)
    (a := (pullK (stK p₀ 0 s), y)) (w := w')
    ⟨(pinw_atSt p₀ 0 s _ _).2 iT, (pin_atSt hS p₀ 0 s _ _ _ _).2 i0,
      (pin_atSt hS p₀ 0 s _ _ _ _).2 i1⟩
  obtain ⟨q1, q2, q3⟩ := decT_some hu
  have hag : Agree R w' u := agree_of_pins 5 (by omega) (by omega) ((p₀, s), y) hon w' u iT
    ((pinw_atSt p₀ 0 s _ _).1 q1) i0 ((pin_atSt hS p₀ 0 s _ _ _ _).1 q2) i1
    ((pin_atSt hS p₀ 0 s _ _ _ _).1 q3)
  have h3 := size_three 5 (by omega) (by omega) ((p₀, s), y) hon
  unfold rowT at hT
  obtain ⟨-, ⟨hInv, hHeard⟩, -⟩ := (rows7_on (Fr := fr₁ D) _ _ _ _ _ _ _ _ _ p₀ _ _ _ _ _ _ 0 3
    (by omega) s y).1 ((upF_on (Fr := fr₁ D) _ p₀ s y).1 hT)
  obtain ⟨G0, g0, d1, d2, -, -, -, d6, d7⟩ := hHeard
  obtain rfl := Option.some.inj (d1.symm.trans a3)
  obtain rfl := Option.some.inj (d2.symm.trans a2)
  have fo' := fo
  have wp'' := wp'.2
  have wk'' := wk'.2
  rw [hsame] at fo' wp'' wk''
  have hhome : VerifiableInference.Desc.Key.K3At.home Johnson.RunOne.KeyRows1.k3At₁ s = _ := hInv.1
  rw [hhome] at fo' wp'' wk''
  obtain ⟨cl, G', hc, hDone⟩ := done_of_sentences
    (A := AK X.Y.k.oneTime X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
        X.Y.k.oneTime 0) (handed (cntO X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
            X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime))
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape) 0)
      (handed (cntK X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
          X.Y.k.oneTime))
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape) 0) 0 (TK Xi))
    (sl := slk X.Y.k.oneTime X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
        X.Y.k.oneTime 0) (handed (cntO X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
            X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime))
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape) 0)
      (handed (cntK X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
          X.Y.k.oneTime))
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape) 0) 0 (TK Xi))
    (μ := msgk X.Y.k.oneTime 0 X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
        X.Y.k.oneTime 0) (handed (cntO X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
            X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime))
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape) 0)
      (handed (cntK X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
          X.Y.k.oneTime))
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape) 0) 0 (TK Xi)
      (wdT X R) (mxT X R) u)
    (w := wdT X R u) (x := X.Y.k.oneTime.ranges) (codes := X.Y.k.oneTime.codes) (i := 0) hadm
    (tiedK _ _ _ _ _ _ _ _ _ _) (Lof X.Y.k.oneTime 0) t0.1 (mkOf (plan₁ X.Y.k.oneTime) R w')
    (fun z hz => by
      show readE (valOf (plan₁ X.Y.k.oneTime) R u z.oracle .mask z.index) =
        readE (valOf (plan₁ X.Y.k.oneTime) R w' z.oracle .mask z.index)
      rw [valOf_agree X.Y.k.oneTime hag z.oracle (by rw [← h3]; exact (hInv.2.1.2 z hz).1)])
    (stK p₀ 0 s) X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (matOf (plan₁
        X.Y.k.oneTime) R w') rfl
    t0.2.1 t0.2.2
    (by
      have hk := keysAreK (T := TK Xi) (id := X.Y.k.oneTime.ranges.messageId)
        (m := Wf.matrixOf X.Y.k.oneTime.lin) (l := Lof X.Y.k.oneTime 0) (hs := _) (stK p₀ 0 s)
        (msgk X.Y.k.oneTime 0 X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
            X.Y.k.oneTime 0) (handed (cntO X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
                X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime))
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape) 0)
      (handed (cntK X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
          X.Y.k.oneTime))
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape) 0) 0 (TK Xi)
          (wdT X R) (mxT X R) u)
      rw [matOf_cut] at hk
      rw [matOf_agree X.Y.k.oneTime hag]
      exact hk)
    _ (fun n hnn => by
      rw [hbit _ n hnn, hid, hag.2.2]
      rfl)
    g0 G0 (fun q hq => d7 q (lt_of_lt_of_eq hq (List.length_map _).symm))
    fo' wp'' wk''
  obtain ⟨tp, hpl⟩ := closed_planes hc
  have key1 : KeysIn X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
      X.Y.k.oneTime 1)
      (cutM (Wf.matrixOf X.Y.k.oneTime.lin) (mxT X R u)) := by
    obtain ⟨L', e1, e2⟩ := inRange_agree X.Y.k.oneTime hag 1 r1
    obtain rfl : L' = _ := Option.some.inj (e1.symm.trans t1.1)
    rw [hsame] at e2
    exact (inRange_iff _ _ _ _ t1.2.1 t1.2.2).1 e2
  unfold rowT
  refine (upF_rel (Fr := fr₁ D) _ p₀ s y).2 ⟨(u, ()), ⟨hu, fun k hk => absurd hk (Nat.not_lt_zero
      _),
    fun k h1 hk => ?_, fun y' => ⟨srow_to_atSt 0 p₀ 0 s _ _ _ (srow_agree _ hag 0 (p₀, s) h3 _ s0),
      srow_to_atSt 1 p₀ 0 s _ _ _ (srow_agree _ hag 1 (p₀, s) h3 _ s1)⟩⟩, _,
    ⟨G0, g0, G0, cl, G', tp, G', a3, a2, PscRun.Later.refl _, hpl, PscRun.Later.refl _, rfl⟩,
    hDone⟩
  obtain rfl : k = 1 := by
    rw [hn] at hk
    omega
  exact key1

end Johnson.RunOne.Law.TieClaimBehind

#print axioms Johnson.RunOne.Law.TieClaimBehind.closed_planes
#print axioms Johnson.RunOne.Law.TieClaimBehind.claim_behind₀
