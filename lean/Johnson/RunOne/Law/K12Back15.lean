-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Back15.lean: ROW 1.15 OF THE KEY FILE's TABLES: THE CLAIM's HALF, JOINED, AT THE TABLES' FILES' OWN FILLING (baseK · atSix · kreadFam): gives_of_halvesH's premise «back» (K12Left15H.lean), at the laid table tbl15 (K12Law15At.lean). One statement; its proof is one call of back_15 (KeyRide15.lean), fed with law_15 | coreAt_of and with lemmas of five other sets of files. IT MOVES THE WEIGHT INTO hfacts AND NAMED PUBLIC PREMISES; IT PAYS NONE.
OBJECT. gives_of_halvesH's premise back: its text, cut by a program, with the filling's letters laid. USER. Whoever fills the structure Left15JG at OnH by the two halves.
LETTERS. X N P DK: The35.lean's. decT recOf tab: the filling's. coll: the tables'. oNo mem rdT: the caller's. nl rad rd: «gives»' own.
THE PREMISES, AND WHOSE EACH IS. On the list of rounds and the IOP as written in Lean (our files: the plan, the description): hpl · hl · hn · hR · hans. On the filling: hSm (smOnlyK, Johnson/RunOne/KeyFillSmOnly.lean: not in the build on which this file was written). The caller's letters: hoNo · hmem · hrd. Off the history, in their payers' own forms: hK · hseed. What the IOP as written in Lean tells of tree 1: hlog · told. THE WEIGHT: hfacts: CoreFacts at every state in front at which the sub-protocol accepts.
WHAT IS TAKEN OUT OF THE PROMISE AT BORDER 15 (its second arm; nothing is marked at these readers): the book-keeping · "the state holds an OOD sample (our files: a record) at pins 0 and 1" · of the last letter: ArrOk | ReadsPinned · SampleIn · InOrder · ShownAt.
IT IS ALSO THE CHECK BY LEAN THAT hmask_15 (Hmask15.lean) HAS THE TYPE OF ride_15's BINDER hmask.
Limits. hfacts is shown of nothing here. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12Law15At
import Johnson.RunOne.Law.K12Left15H
import Johnson.RunOne.Law.KeyRide15
import Johnson.RunOne.Law.Hmask15
import Johnson.RunOne.Law.K12Facts15
import Johnson.RunOne.Law.RngDoorIs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

namespace Johnson.RunOne.Law.K12Back15
open H2K.Pin
open Cb Cb.Ood Iop Prob OnBytes OnBytes.Slice OnBytes.Slice.ProxRun Johnson.Pack
open OnBytes.Means H2K.ClaimSays
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.Key (Xi FirstState)
open VerifiableInference.Desc.K1 (SmpStay groundKeeps_smpStay beginRun_smpStay)
open OnBytes.Maker
open _root_.Run
open Johnson.Top.H (csKey)
open Johnson.RunOne Johnson.RunOne.KeyRows1 Johnson.RunOne.KeyRows23
open Johnson.RunOne.KeyRows23 (Fk oneAt On₁ fr₁)
open _root_.Desc.K14.Law.Fence (CoreFacts)
open LPFD LPFD.CandLaid
open Johnson.RunOne.Law.K12Law15At

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD) {Cells Rec : Type}
  (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec)
  (tab : Cells → ℕ → ℕ → OnBytes.F) (coll : Strs → Rec → Prop)
  (oNo : Mem → ℕ) (mem : ℕ → Option Mem)
  (rdT : (x : Mem) → ((sigOf csKey x.1.l).om x.2).Msg → Part → ℕ → GE)

/-- The tables' files' filling, at the plan's own numbering of the messages. -/
abbrev BK : BaseSt Cells Fill.Tab (Σ i : Fin six.length, (OmAt csKey six i).Smp) Rec :=
  baseK csKey six numSix atSix decT recOf (plan₁ (oneAt X)).orc

/-- **The claim's half of row 1.15, at the filling.** -/
theorem back_15_at (hpl : (descriptionFromSource X N P).planOk = true) (hl : (lookupsOf X.Y.k.oneTime).length = 2)
    (hn : X.Y.k.oneTime.ranges.lookups.length = 2)
    (hR : VerifiableInference.Desc.K3.KeyLaw.RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape)
    (hans : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0)
    (hSm : (BK X decT recOf).SmOnly)
    (hoNo : oNo x₁ = 1) (hmem : mem 1 = some x₁)
    (hrd : ∀ x m part i, rdT x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (hK : ∀ a, Hist₁ (Fk X N P) (DK.at frS.P.T.a) 15 a → OpenKinds a.2.d.st)
    (hseed : ∀ a, Hist₁ (Fk X N P) (DK.at frS.P.T.a) 15 a → ∃ ρ y, K1.SeedIs csKey (six.get i₁).1 a.2.d.st 1 ρ y)
    (hlog : ∀ o, (Fk X N P).oracleAt (seatAt six numSix atSix i₁).1 = some o → o.logLength = aOf csKey (six.get i₁).1)
    (told : ((Fk X N P).oracleAt (seatAt six numSix atSix i₁).1).isSome = true)
    (nl : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ)
    (hfacts : ∀ (a : (Xi × FirstState) × (FR DK).E.Str) (t : T12),
      (On₁ X N P (DK.at frS.P.T.a) (BK X decT recOf) atSix (RK tab) coll) 15 a → Hist₁ (Fk X N P) (DK.at frS.P.T.a) 15 a.1 →
      enterAndAsk (enterRanges X.Y.k.oneTime) (rangesParams N) a.1.2 = .ok t →
      QN (rangesParams N) (NTuple (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) (rangesParams N) (nuOf (rangesParams N) nl t) rad rd) (t, a.2) →
      ∀ rs gs b, (held (Johnson.RunOne.Sound.bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim))).decide a.1 rs gs = .ok b →
      CoreFacts csKey (Fk X N P) (FR DK) (rangesParams N) (nuOf (rangesParams N) nl t) rad (smpK oNo) mem (· = x₁) t a.2 a.1 (strsOf (FR DK) a.2)) :
    ∀ a b rs gs t t' w, (On₁ X N P (DK.at frS.P.T.a) (BK X decT recOf) atSix (RK tab) coll) 15 a → Hist₁ (Fk X N P) (DK.at frS.P.T.a) 15 a.1 → (held (Johnson.RunOne.Sound.bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim))).decide a.1 rs gs = .ok b.1 →
      StrsStay (Fk X N P) atSix (open₁ (n₁ (oneAt X)) 15) (strsOf (fr₁ (DK.at frS.P.T.a)) a.2) (strsOf (fr₁ (DK.at frS.P.T.a)) b.2) → (On₁ X N P (DK.at frS.P.T.a) (BK X decT recOf) atSix (RK tab) coll) 16 b →
      enterAndAsk (enterRanges X.Y.k.oneTime) (rangesParams N) a.1.2 = .ok t → leaveRanges a.1.2 t' = .ok b.1.2 → b.1.1 = a.1.1 →
      QN (rangesParams N) (NTuple (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) (rangesParams N) (nuOf (rangesParams N) nl t) rad rd) (t, a.2) →
      R₁ (Fk X N P) (fr₁ (DK.at frS.P.T.a)) (BK X decT recOf).h₁ atSix (oneAt X) (RK tab) 16 b w → R₁ (Fk X N P) (fr₁ (DK.at frS.P.T.a)) (BK X decT recOf).h₁ atSix (oneAt X) (RK tab) 15 a (layAt atSix [1] (fun _ => tbl15 X N P DK oNo mem rdT a w) w) := by
  intro a b rs gs t t' w hon hh hd Hy _ ht _ _ hq hw
  have hn2 : n₁ (oneAt X) = 2 := hl
  obtain ⟨h15n, hsmA, hfree, _⟩ := hon.elim (fun hx => (hx rfl).elim) id
  have h15 : shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) 2 (slots₁ (oneAt X)) 15 a.1.2 = true := hn2 ▸ h15n
  obtain ⟨_, ⟨hA, hRd⟩, _, _, hSin, _, hIo, hSh, _⟩ := hfree
  have hy : (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim).decide a.1.2 rs gs = .ok b.1.2 :=
    (held_decide _ a.1 rs gs b.1 hd).2
  -- of the state in front
  obtain ⟨g, G, hg, hG, hone, _, hne⟩ := K12Shape15.rows_15 h15
  have hc := ((shape₁_iff _ _ _ _ _ _ _).1 h15).2
  rw [K12Shape15.core15_eq] at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨x0, hx0, x0s, _⟩ := (K12Shape15.sentB_iff a.1.2 (k := 0) (o := 0) rfl).1 hc.1.1.1.1.1
  obtain ⟨x1, hx1, _, _⟩ := (K12Shape15.sentB_iff a.1.2 (k := 1) (o := 1) rfl).1 hc.1.1.1.1.2
  have hgrp : (readers₁ (oneAt X)).grpB a.1.2 = some a.1.2.grp := by
    have h' : (if a.1.2.grp == noId then none else some a.1.2.grp) = some g := hg
    show (if a.1.2.grp == noId then none else some a.1.2.grp) = some a.1.2.grp
    split at h'
    · cases h'
    · rename_i hne'
      rw [if_neg hne']
  -- the ties, restricted
  have ha0 : ArrOk (BK X decT recOf).h₁ atSix [0] := hA.mono (by simp)
  have ha1 : ArrOk (BK X decT recOf).h₁ atSix [1] := hA.mono (by simp)
  have hr0 : ReadsPinned (BK X decT recOf).h₁ atSix (RK tab) [0] := fun w k hk => hRd w k (by simp at hk; simp [hk])
  have hr1 : ReadsPinned (BK X decT recOf).h₁ atSix (RK tab) [1] := fun w k hk => hRd w k (by simp at hk; simp [hk])
  have hs : SeatsApart atSix [1] [0] := by
    intro k hk k' hk' e
    simp only [List.mem_singleton] at hk hk'
    subst hk hk'
    exact absurd e (by decide)
  -- the seat of message 1
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 told
  have h1in : 1 ∈ pinned (open₁ 2 15) := by decide
  have h0in : 0 ∈ pinned (open₁ 2 15) := by decide
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 (List.all_eq_true.1 hsmA 1 (by rw [hn2]; exact h1in))
  have hsh : Sound.ShownAt (Fk X N P) csKey six (seatAt six numSix atSix) (strsOf (FR DK) a.2) i₁ :=
    fun x hx => hSh 1 h1in o ho x (by rw [hlog o ho]; exact hx)
  -- the table's row
  obtain ⟨r, hr15, hre⟩ := Option.map_eq_some_iff.1 KeyRide15.row15
  have hins : r.ins = [KItem.grows, KItem.pin 1] := congrArg (·.1) hre
  have hctx : r.ctx = [] := congrArg (·.2.1) hre
  have hstep : ((rows₁ 2)[15]?).map (stepOpen (open₁ 2 15)) = some (open₁ 2 16) := by decide
  rw [hr15] at hstep
  have e16 : stepOpen (open₁ 2 15) r = open₁ 2 16 := Option.some.inj hstep
  have hw' : relAt (Fk X N P) (BK X decT recOf).h₁ atSix (meaning₁At (oneAt X) (RK tab)) (stepOpen (open₁ 2 15) r) b.1 (strsOf (FR DK) b.2) w := by
    rw [e16, ← hn2]
    exact hw
  have Hy' : StrsStay (Fk X N P) atSix (open₁ 2 15) (strsOf (FR DK) a.2) (strsOf (FR DK) b.2) := hn2 ▸ Hy
  show relAt (Fk X N P) (BK X decT recOf).h₁ atSix (meaning₁At (oneAt X) (RK tab)) (open₁ (n₁ (oneAt X)) 15) a.1 (strsOf (FR DK) a.2) _
  rw [hn2]
  refine KeyRide15.back_15 OnBytes.Model.Reading.gl (Fk X N P) (BK X decT recOf).h₁ atSix (oneAt X) (RK tab) r hins hctx a.1 b.1 _ _ w _ Hy'
    (K12Facts15.rec_15 X N (BK X decT recOf) a.1 rs gs b.1 hd)
    (K12Facts15.smp_15 X N (BK X decT recOf) atSix hSm rfl hA a.1 b.1 rs gs hd h15n 0 (by rw [hn2]; decide)).symm
    (K12Keeps.ranges_keeps groundKeeps_smpStay (fun d d' g run hb => beginRun_smpStay d d' g run hb) _ N a.1.2 b.1.2 rs gs hy)
    ⟨x0, hx0, x0s⟩ (hSin 0 h0in 0 rfl)
    (fun l _ => by
      show (b.1.2.base.keys[l]?).bind _ = (a.1.2.base.keys[l]?).bind _
      rw [(RngAtKeyD.keyD_passes hy).1])
    (Hmask15.hmask_15 (DK.at frS.P.T.a) a.2 hpl hR hans hn a.1 hh (BK X decT recOf).h₁ atSix (RK tab) w _ ha0 hr0 hs)
    ((kreadFam_same csKey six numSix atSix tab).trans sameGl_eq) ha0 hr0 hs ?_ hw'
  intro _
  rw [hins]
  exact law_15 X N P DK decT recOf tab oNo mem rdT a w
    (coreAt_of X N P DK oNo mem rdT hrd nl rad rd a t ht (hfacts a t hon hh ht hq rs gs b.1 hd)
      (by rw [RngAtKeyD.door_is _ _ _ _ ht]; exact hIo) hq)
    ⟨g, G, hg, hG, hone, hne⟩
    (fun t' ht' => by rw [RngAtKeyD.door_is _ _ _ _ ht']; exact ⟨rfl, hgrp⟩)
    ⟨x1, hx1⟩ hIo (hK a.1 hh) (hseed a.1 hh) (tie_six i₁) hoNo hmem hrd rfl rfl hlog told o ho z hz hsh ha1 hr1
    (layIdem_h₁ csKey six numSix atSix (rowIsK csKey six) decT recOf (plan₁ (oneAt X)).orc)
    (kreadFam_same csKey six numSix atSix tab)

end

end Johnson.RunOne.Law.K12Back15

#print axioms Johnson.RunOne.Law.K12Back15.back_15_at
