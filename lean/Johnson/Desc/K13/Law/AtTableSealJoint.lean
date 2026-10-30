-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/AtTableSealJoint.lean: THE SEAL's FIVE TIES WITH BOTH HALVES JOINED: at the two
written lists (the table's half: by the kernel, Johnson/Desc/K13/Law/AtTableSealRow.lean) AND at the
table's files' own filling of the first table's meaning (mg1Joint,
Johnson/Desc/Sound/JointFilling.lean; the letters' half: Johnson/Desc/K13/Law/AtTableSealFill.lean).
Two theorems: a joining.

OBJECT, USER, FIELD as in Johnson/Desc/K13/Law/AtTableSeal.lean.
LETTERS  mg1Joint's own; the seat's gt st pub; N; the piece's base ds back err.

  firstEnd_tied_joint_small | _full **TiedAt N (mg1Joint …) links (flatPlaces true links true) get
    k (the lifted piece that holds c)**, k = 77 of 78 | 357 of 358. LEFT: hc (c is the seal under
    the wrappers) · the seat's three equations · hM (Mg₁'s own door makes nothing at the seal's
    place: not "is empty", which a meaning that bears another kind's layer cannot
    pay) · hT | hMs (by the plan's numbers as many trees and messages
    behind the block as in front) · hI | hV (the index masks' and W's tenants sit in trees below
    the piece's base).
What is not claimed. NO INSTANCE: that a description's last entry is that block, at that place, with
that stretch and base; that the two lists are a plan's. Two numberings of trees (the
book's; the file's base) are tied by nothing. All that the three files do not claim. Nothing on
soundness.

-/
import Johnson.Desc.K13.Law.AtTableSealDoor
import Johnson.Desc.K13.Law.AtTableSealFill
import Johnson.Desc.Sound.JointFilling

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice OnBytes.Flat Iop Run
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More)
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (pieceSeal linksSmall linksFull wSitsMore
  rowSeal_small_door rowSeal_full_door placeSeal riders_of_test riders_small riders_full
  open_of_test openSeal_both)
open _root_.Desc.K14.Law (mg1Joint)

section
variable {A Pp Cl Cells Tok Xi : Type} {C : PQ.CK} (F : Frame) (piece : ℕ)
  (front : List (Block S Cl)) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView)
  (err : Err (uLT C ds)) (c : Block S Cl) (hc : c.UnderR (First.firstEnd piece front))
  (gt : A → S) (st : A → S → A) (h1 : ∀ t s, gt (st t s) = s)
  (h2 : ∀ t s s', st (st t s) s' = st t s') (pub : A → Pp) (hpub : ∀ t s, pub (st t s) = pub t)
  (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells)
  (stOf₁ : Pp × S → OnBytes.Statement) (tabP₁ : Pp × S → Wit Cells Tok MsgT → ℕ → MsgT)
  (Pw : Where) (wSeat : ℕ × ℕ) (matC : Cells → ℕ → ℕ → GE)
  (Mg₁ : Meaning Pp (Wit Cells Tok MsgT)) (N : Numbers)
include hc h1 h2 hpub

/-- **The seal's five ties at the table's files' own filling, at the small list.** -/
theorem firstEnd_tied_joint_small (hM : (Mg₁.more.rows linksSmall placeSeal).makes = [])
    (hT : N.treesAt (First.flatPlaces true linksSmall true)[77 + 1]? =
      N.treesAt (First.flatPlaces true linksSmall true)[77]?)
    (hMs : N.msgsAt (First.flatPlaces true linksSmall true)[77 + 1]? =
      N.msgsAt (First.flatPlaces true linksSmall true)[77]?)
    (hI : N.index.1 < base) (hV : N.w.1 < base) :
    TiedAt N (mg1Joint cs G arr smp ms decT stOf₁ tabP₁ Pw wSeat matC Mg₁) linksSmall
      (First.flatPlaces true linksSmall true) (fun a : A => (pub a, gt a)) 77
      (((pieceSeal (W := Wit Cells Tok MsgT) F piece front base ds back err).seat c).lift gt
        st) := by
  have hR := rowSeal_small_door N (Mg₁.more.merge wSitsMore) (by
    show (Mg₁.more.rows linksSmall placeSeal).makes ++ [] = []
    rw [hM]
    rfl) hT hMs
  exact firstEnd_tied_sig F piece front base ds back err c hc gt st h1 h2 pub hpub cs G arr smp ms
    decT (mg1Joint cs G arr smp ms decT stOf₁ tabP₁ Pw wSeat matC Mg₁) N linksSmall _ 77 placeSeal
    hR
    (riders_of_test _ _ _ riders_small) (open_of_test _ _ _ openSeal_both.1) hI hV
    fun _ _ _ _ _ h => h

/-- At the full list. -/
theorem firstEnd_tied_joint_full (hM : (Mg₁.more.rows linksFull placeSeal).makes = [])
    (hT : N.treesAt (First.flatPlaces true linksFull true)[357 + 1]? =
      N.treesAt (First.flatPlaces true linksFull true)[357]?)
    (hMs : N.msgsAt (First.flatPlaces true linksFull true)[357 + 1]? =
      N.msgsAt (First.flatPlaces true linksFull true)[357]?)
    (hI : N.index.1 < base) (hV : N.w.1 < base) :
    TiedAt N (mg1Joint cs G arr smp ms decT stOf₁ tabP₁ Pw wSeat matC Mg₁) linksFull
      (First.flatPlaces true linksFull true) (fun a : A => (pub a, gt a)) 357
      (((pieceSeal (W := Wit Cells Tok MsgT) F piece front base ds back err).seat c).lift gt
        st) := by
  have hR := rowSeal_full_door N (Mg₁.more.merge wSitsMore) (by
    show (Mg₁.more.rows linksFull placeSeal).makes ++ [] = []
    rw [hM]
    rfl) hT hMs
  exact firstEnd_tied_sig F piece front base ds back err c hc gt st h1 h2 pub hpub cs G arr smp ms
    decT (mg1Joint cs G arr smp ms decT stOf₁ tabP₁ Pw wSeat matC Mg₁) N linksFull _ 357 placeSeal
    hR
    (riders_of_test _ _ _ riders_full) (open_of_test _ _ _ openSeal_both.2) hI hV
    fun _ _ _ _ _ h => h

end

end VerifiableInference.Desc.Sound
