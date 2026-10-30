-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/SecondTieAt.lean: THE SECOND TIE OF THE MERGE OF THE CLAIMS ON THE COMMITTED
TABLE (kind K11), AT THE COMPOSED MEANING `mgAll D Mg₀` AND THE WRITTEN LIST OF PLACES: the table's
condition in front of the merge, and its accepting step, give the table's condition behind. One
theorem: a joining of lemmas.

What is said. `merge_t2_all`: `onQ … 346 a`, the merge's accepting step from a to b, and "b's
strings are what the merge's stretch leaves of a's" give `onQ … 347 b`. It is `merge_t2`
(TieOneTwo.lean) with NINE of its premises PAID:
  five closed facts on the two places: by the kernel (`k11_hp`, `k11_hp'`, `k11_hq`, `k11_hst`,
    `k11_hlk`: Johnson/Desc/Sound/MgAt/K11Places.lean);
  "decodes" rides: `merge_hD_of_hdec` (DecodesAtMerge.lean);
    what the public items say beside their tests: `merge_hPP_all` (SaidRides.lean);
    "held": `merge_hHeld_full` (HeldRides.lean);
    "shown" and "no collision": `merge_hSN_all` (ShownRidesAll.lean).

THE PREMISES THAT ARE LEFT. htr, hms: the numbers of trees and of messages are the same at the two
places. hdec, hsmp: the two readers of the state are blind to what the merge writes. low: every
sampled place that is open at 346 was sent in front of the merge's stretch. hIn: "in order" rides.
hbP: the meaning beneath says of b what it says of a. hPub: the public tests behind
(`merge_pubHeld`, Johnson/Desc/Sound/MgAt/K11Pub.lean). hnl, hmk: two closed facts on the open
public sets, and what the row's new items say.

Limits. Shown at no closed value of D. Nothing on soundness.
-/
import Johnson.Top.H0.MergeLaw.TieOneTwo
import Johnson.Top.H0.MergeLaw.DecodesAtMerge
import Johnson.Top.H0.MergeLaw.SaidRides
import Johnson.Top.H0.MergeLaw.ShownRidesAll
import Johnson.Top.H0.MergeLaw.HeldRides
import Johnson.Desc.Sound.MgAt.K11Pub
import Johnson.Desc.Sound.MgAt.K11Places

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.First.MergeLaw
open Iop
open OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open _root_.Run (ckP)
open VerifiableInference.Desc (Link Claim Place Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S HeadOwn ModelPart Item Pub Meaning Numbers start flatPlacesOf
  openSets pubSets stepOpen pubStep pubRowM rowOf pubOfItems sampledIn)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeClaim headMergeDecide)
open Johnson.Desc.First.Walk.Law (hasRow)
open VerifiableInference.Desc.Sound.MgAt (mergeAt behindAt k11_hp k11_hp' k11_hq k11_hst k11_hlk)

variable {Xi Pp Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public} {Fr : Frame}
  (D : MgData Xi Pp Tok rows cols nR X) (Mg₀ : Meaning Pp (Wit (CellsQ rows cols) Tok MsgT))

/-- **THE MERGE's SECOND TIE AT THE COMPOSED MEANING, AT THE WRITTEN LIST**: the table's condition
in front of the merge, and its accepting step, give the table's condition behind. -/
theorem merge_t2_all (Pm : HeadMergeP) (Nn : Numbers) (base : ℕ) (ds : List RDT)
    -- two facts on the numbers at the two places
    (htr : Nn.treesAt (some behindAt) = Nn.treesAt (some mergeAt))
    (hms : Nn.msgsAt (some behindAt) = Nn.msgsAt (some mergeAt))
    -- the readers of the state are blind to what the merge writes; the fence
    (hdec : ∀ z c (s : S) (a' : HeadOwn),
      D.decT c (z, { s with rowsOwed := none, here := .head a' }) = D.decT c (z, s))
    (hsmp : ∀ z (s : S) (a' : HeadOwn),
      D.smp (z, { s with rowsOwed := none, here := .head a' }) = D.smp (z, s))
    (low : ∀ x ∈ sampledIn Nn ((openSets linksFull (flatPlacesOf linksFull true)
      (start linksFull))[346]?.getD []), x.1 < base)
    (z : Pp) (a b : S × Fr.E.Str)
    (ha : onQ Nn (mgAll D Mg₀) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a)
    (hy : ∃ rs, headMergeDecide Pm a.1 rs = .ok b.1)
    (hb : ∃ τ : Iop.Tr (uLT (ckP .two) ds), b.2 = behind (ckP .two) Fr base ds a.2 τ)
    -- the meaning beneath
    (hIn : (mgAll D Mg₀).inOrder (z, a.1) = true → (mgAll D Mg₀).inOrder (z, b.1) = true)
    (hbP : ∀ q, Mg₀.pubP q (z, a.1) → Mg₀.pubP q (z, b.1))
    -- the public tests
    (hPub : pubHeld (mgAll D Mg₀)
        ((openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[346]?.getD [])
        ((pubSets (mgAll D Mg₀).more linksFull (flatPlacesOf linksFull true))[346]?.getD [])
        (z, a.1) = true →
      pubHeld (mgAll D Mg₀)
        (stepOpen ((openSets linksFull (flatPlacesOf linksFull true)
          (start linksFull))[346]?.getD []) (rowOf linksFull mergeAt))
        (pubStep
          ((pubSets (mgAll D Mg₀).more linksFull (flatPlacesOf linksFull true))[346]?.getD [])
          (pubRowM (mgAll D Mg₀).more linksFull mergeAt)) (z, b.1) = true)
    -- what the public items say beside their tests
    (hnl : ∀ q ∈ (pubSets (mgAll D Mg₀).more linksFull (flatPlacesOf linksFull true))[346]?.getD [],
      q ∈ pubStep ((pubSets (mgAll D Mg₀).more linksFull
        (flatPlacesOf linksFull true))[346]?.getD [])
        (pubRowM (mgAll D Mg₀).more linksFull mergeAt) → ∀ m, q ≠ .left m)
    (hmk : ∀ q ∈ (pubRowM (mgAll D Mg₀).more linksFull mergeAt).makes,
      q ∉ (pubSets (mgAll D Mg₀).more linksFull (flatPlacesOf linksFull true))[346]?.getD [] →
      (mgAll D Mg₀).pubP q (z, b.1)) :
    onQ Nn (mgAll D Mg₀) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) (346 + 1) b :=
  merge_t2 Nn (mgAll D Mg₀) linksFull (flatPlacesOf linksFull true) 346 Pm mergeAt behindAt k11_hp
    k11_hp' k11_hq k11_hst k11_hlk htr hms z a b ha hy
    (merge_hD_of_hdec D Mg₀ Pm base ds hdec z a b hy hb)
    hIn hPub
    (merge_hPP_all D Mg₀ _ _ Pm z hy hbP hnl hmk)
    (merge_hHeld_full D Mg₀ Pm Nn z a b hy)
    (merge_hSN_all D Mg₀ Nn linksFull (flatPlacesOf linksFull true) 346 Pm base ds low hsmp z a b hy
      hb)

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.merge_t2_all
