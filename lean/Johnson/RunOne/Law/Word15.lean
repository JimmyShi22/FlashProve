-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/Word15.lean: THEOREMS. **THE WORD AT THE RANGES' PROXIMITY TEST (chain 1, border 15) OF THE KEY FILE's IOP AS WRITTEN IN LEAN: THE SEVENTH CLAUSE OF WHAT THE SEAM ASKS OF A MEMBER (MemberFacts, Johnson/Desc/Sound/SeamMembers.lean), AT THE ONE MEMBER, MESSAGE 1: a join of lemmas;
no new mathematics.** «The word as sent», off the written oracle at the member's tree, is the member's word off the plain strings of the frame's oracles. («State» := what the verifier carries between two sub-protocols (in these files: blocks).)
OBJECT. The seam's clause at m := D.mems.get j · book := D.book · x := x₁ (the second of the six seats) · e0 := (six.get i₁).2 · no := nuOf (rangesParams N) (nlAt (rangesParams N) 0) t. USER. coreFacts_15 (K12Facts15D.lean; its premise hword). LETTERS. X · N · P · DK · file · tag · a (the state at border 15 with the frame's strings) · t (the test's own
state behind the seat's door).
WHO GIVES WHAT. seven_of_parts (SevenOfParts.lean): the clause from hx · hF · hS · hI · hd · hx: member_of_seedIs (Johnson/Desc/Sound/SeedAtKind.lean: the member's shape is the plan's) with one_member (K12MemberCarry.lean: the member's number is 1) · hF: seatFits_one (K12Facts15P.lean) at the main line's plain test seatFaultAt (Johnson/Desc/SeatAt.lean) · hS: A PREMISE (the row's promise holds it) ·
hI: seatIs_of_made (Johnson/Desc/K12/Coin/FramesTie.lean) at book_15_at (BookPlace.lean; off the history: message 1's place in the book is (1, 0); its tree; the tree has the told shape), book_of_fixes, door_is, nuOf_is_place · hd: depth_of_planOk (Johnson/Desc/Sound/SeamDesc.lean).
  word_15           the clause, «at whatever the state fixes», from: planOk · data · the history at 15 · the door's accepting run · the tables' shape₁ at 15 · SeedIs at message 1 · no fault at the seat (1, 0) · ShownAt
  word_15_on        **the same in the very form of the premise hword**: ∀ a t, ‹the tables' promise at 15› a → ‹the history at 15› a.1 → ‹the door's accepting run› → the clause: shape₁ at 15 and ShownAt are drawn out of the promise (as K12Back15.lean draws them)
What is not claimed. That the premises can be met together. Nothing on soundness.

-/
import Johnson.RunOne.Law.SevenOfParts
import Johnson.RunOne.Law.NuOfPlace
import Johnson.RunOne.Law.BookPlace
import Johnson.RunOne.Law.K12Law15At
import Johnson.RunOne.Law.RngDoorIs
import Johnson.RunOne.Law.K12MemberCarry
import Johnson.RunOne.Law.K12Shape15
import Johnson.RunOne.Law.K12Facts15P
import Johnson.Desc.Sound.SeedAtKind
import Johnson.Desc.Sound.SeamDesc
import Johnson.RunOne.Law.K12Back15

set_option autoImplicit false

namespace Johnson.RunOne.Law.Word15

open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.K12.Coin VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces enterRanges lookupsOf enterAndAsk rangesParams)
open VerifiableInference.Desc.Key.Fill
open Johnson.Top.H (csKey)
open Johnson.RunOne Johnson.RunOne.KeyRows1 Johnson.RunOne.KeyRows23
open Johnson.RunOne.KeyRows23 (Fk oneAt)
open H2K.First (Seat1 Plain)
open H2K.Pin (layOf strOf)
open LPFD LPFD.CandLaid
open Johnson.RunOne.Law.K12Law15At (i₁ x₁ FR)
open Johnson.RunOne.Law.RngAtKeyD (door_is recD)

variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD)

/-- **The word at the ranges' test: the seam's seventh clause at message 1.** -/
theorem word_15 (file tag : String) (a : (Xi × FirstState) × (FR DK).E.Str) (t : T12)
    (hp : (Fk X N P).planOk = true) (hD : (Fk X N P).data file = .ok (DK.at frS.P.T.a))
    (hist : Hist₁ (Fk X N P) (DK.at frS.P.T.a) 15 a.1)
    (ht : enterAndAsk (enterRanges (oneAt X)) (rangesParams N) a.1.2 = .ok t)
    (h15 : VerifiableInference.Desc.Key.shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) 2 (slots₁ (oneAt X)) 15 a.1.2 = true)
    (hft : (rangesParams N).nums.firstTree = 0)
    (hseed : ∃ ρ v, K1.SeedIs csKey (six.get i₁).1 a.1.2.d.st 1 ρ v)
    (hfault : seatFaultAt (Fk X N P) csKey tag (six.get i₁).1 1 0 = none)
    (hS : ShownAt (Fk X N P) csKey six (seatAt six numSix atSix) (strsOf (FR DK) a.2) i₁) :
    ∀ a' rest G0 Ly D, Fixes (rangesParams N) t a' rest G0 Ly D → ∀ j : Fin D.mems.length,
      HEq (strOf csKey (D.mems.get j).sh (six.get i₁).2 (layOf (D.mems.get j))
          (W0 (FR DK) (nuOf (rangesParams N) (nlAt (rangesParams N) 0) t) D.book a.2 (D.mems.get j).t).1
          (W0 (FR DK) (nuOf (rangesParams N) (nlAt (rangesParams N) 0) t) D.book a.2 (D.mems.get j).t).2)
        (Sound.wordsOf (Fk X N P) csKey x₁.1.l x₁.1.seat (strsOf (FR DK) a.2) x₁.2) := by
  intro a' rest G0 Ly D hf j
  obtain ⟨hn, _, _, _, ⟨G, hG, hGm⟩, hrid, _, _, _, _, htsz, _, hstep⟩ := K12Shape15.front15 h15
  have et : t = recD a.1.2 := door_is _ _ _ _ ht
  have hmk : t.mask.isSome = true := by rw [et]; show a.1.2.rider.isSome = true; rw [hrid]; rfl
  have htb : t.book = a.1.2.d.book := by rw [et]; rfl
  have hbk : D.book = a.1.2.d.book := (book_of_fixes _ t hmk a' rest G0 Ly D hf).trans htb
  have hG0 : G0.members.toList = [1] := by
    have e : a.1.2.d.st.groups[a.1.2.grp]? = some G0 := by
      have := hf.2.1
      rw [et] at this
      exact this
    rw [hG] at e
    rw [← Option.some.inj e]
    exact hGm
  have hid := (K12MemberCarry.one_member hf 1 hG0).2 j
  obtain ⟨ρ, v, hsd⟩ := hseed
  have hsd' : K1.SeedIs csKey (six.get i₁).1 t.st (D.mems.get j).id ρ v := by rw [hid, et]; exact hsd
  have hsh : (D.mems.get j).sh = (six.get i₁).1 := (_root_.Desc.K14.Law.Fence.member_of_seedIs hf default j hsd').1
  obtain ⟨T, o₀, hpl, htr, hor, hshape⟩ := BookPlace.book_15_at (X := X) (N := N) (P := P) (DK.at frS.P.T.a) hn a.1 hist
  refine SevenOfParts.seven_of_parts csKey (Fk X N P) (FR DK) _ D.book a.2 (D.mems.get j) x₁ (six.get i₁).2 ?_ ?_ hS ?_ ?_
  · show six.get i₁ = ((D.mems.get j).sh, (six.get i₁).2)
    rw [hsh]
  · exact K12Facts15.seatFits_one (Fk X N P) csKey tag (six.get i₁).1 (six.get i₁).2 (1, 0) hfault
  · intro o ho
    have ho' : (Fk X N P).oracleAt 1 = some o := ho
    obtain rfl : o₀ = o := Option.some.inj (hor.symm.trans ho')
    refine seatIs_of_made (H2K.First.made_of _ _ a' Ly D (hf.2.2.2 default)) _ j 1 0 o₀ ?_ ?_
    · intro z u e
      rw [hid, hbk] at e
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hpl.symm.trans e))
      refine ⟨NuOfPlace.nuOf_is_place _ t hf hmk hft (by rw [et]; exact hstep) _ (by rw [htb, htsz]; decide), rfl⟩
    · intro z u T' e eT
      rw [hid, hbk] at e
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hpl.symm.trans e))
      rw [hbk] at eT
      obtain rfl : T = T' := Option.some.inj (htr.symm.trans eT)
      exact hshape
  · intro o ho
    exact _root_.Desc.K14.Law.Fence.depth_of_planOk (Fk X N P) file (DK.at frS.P.T.a) hp hD _ 0 _ o ho

section AtThePromise
open Johnson.RunOne.KeyRows23 (On₁)
open Johnson.RunOne.Law.K12Law15At (RK)
open Johnson.RunOne.Law.K12Back15 (BK)
open Johnson.Pack (aOf)
variable {Cells Rec : Type} (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec)
  (tab : Cells → ℕ → ℕ → OnBytes.F) (coll : Strs → Rec → Prop)

/-- **In the very form of the premise hword.** -/
theorem word_15_on (file tag : String) (hp : (Fk X N P).planOk = true) (hD : (Fk X N P).data file = .ok (DK.at frS.P.T.a))
    (hl : (lookupsOf X.Y.k.oneTime).length = 2) (hft : (rangesParams N).nums.firstTree = 0)
    (hseed : ∀ a, Hist₁ (Fk X N P) (DK.at frS.P.T.a) 15 a → ∃ ρ y, K1.SeedIs csKey (six.get i₁).1 a.2.d.st 1 ρ y)
    (hfault : seatFaultAt (Fk X N P) csKey tag (six.get i₁).1 1 0 = none)
    (hlog : ∀ o, (Fk X N P).oracleAt (seatAt six numSix atSix i₁).1 = some o → o.logLength = aOf csKey (six.get i₁).1) :
    ∀ (a : (Xi × FirstState) × (FR DK).E.Str) (t : T12),
      (On₁ X N P (DK.at frS.P.T.a) (BK X decT recOf) atSix (RK tab) coll) 15 a → Hist₁ (Fk X N P) (DK.at frS.P.T.a) 15 a.1 →
      enterAndAsk (enterRanges X.Y.k.oneTime) (rangesParams N) a.1.2 = .ok t →
      ∀ a' rest G0 Ly D, Fixes (rangesParams N) t a' rest G0 Ly D → ∀ j : Fin D.mems.length,
        HEq (strOf csKey (D.mems.get j).sh (six.get i₁).2 (layOf (D.mems.get j))
            (W0 (FR DK) (nuOf (rangesParams N) (nlAt (rangesParams N) 0) t) D.book a.2 (D.mems.get j).t).1
            (W0 (FR DK) (nuOf (rangesParams N) (nlAt (rangesParams N) 0) t) D.book a.2 (D.mems.get j).t).2)
          (Sound.wordsOf (Fk X N P) csKey x₁.1.l x₁.1.seat (strsOf (FR DK) a.2) x₁.2) := by
  intro a t hon hh ht
  have hn2 : n₁ (oneAt X) = 2 := hl
  obtain ⟨h15n, _, hfree, _⟩ := hon.elim (fun hx => (hx rfl).elim) id
  have h15 : VerifiableInference.Desc.Key.shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) 2 (slots₁ (oneAt X)) 15 a.1.2 = true := hn2 ▸ h15n
  obtain ⟨_, _, _, _, _, _, _, hSh, _⟩ := hfree
  obtain ⟨_, o, _, _, ho, _⟩ := BookPlace.book_15_at (X := X) (N := N) (P := P) (DK.at frS.P.T.a) hl a.1 hh
  have h1in : 1 ∈ VerifiableInference.Desc.Key.pinned (open₁ 2 15) := by decide
  have hsh : Sound.ShownAt (Fk X N P) csKey six (seatAt six numSix atSix) (strsOf (FR DK) a.2) i₁ :=
    fun x hx => hSh 1 h1in o ho x (by rw [hlog o ho]; exact hx)
  exact word_15 X N P DK file tag a t hp hD hh ht h15 hft (hseed a.1 hh) hfault hsh

end AtThePromise

end Johnson.RunOne.Law.Word15

#print axioms Johnson.RunOne.Law.Word15.word_15
#print axioms Johnson.RunOne.Law.Word15.word_15_on
