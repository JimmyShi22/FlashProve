-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/TieFourPadsAtPlan.lean: code switching: hE AND hNd OF THE FOURTH TIE AT A
PLACE (k02_t4R, K2Caller/TieFourR.lean) AT THE COMPOSED MEANING's OWN MEMBERS,
ms := P5T.msAtR Z rad (Johnson/P5T/MembersByMake.lean): TieFourPadsAt.lean's two theorems with the
lengths and the seats' difference taken from ONE test, membersPlanB (MembersAtPlan.lean). Two
theorems with their proofs. NO SUB-PROTOCOL IMPORTS THIS FILE.
  k02_t4R_hE_plan    hE, at seatN := seatNew N m r
  k02_t4R_hNd_plan   hNd
  both at minePad := minePadAt (P5T.msAtR Z rad) N links p
THE PREMISES. m: the segment in front of the code switch (behind the last code switch there is no
segment: its group has the number links.length). On public data:
  numbersFit os N links.length = true (hE alone; os: any list) · m < links.length (hE alone) ·
  p.link.getD links.length = m + 1 · membersPlanB Z rad N (m + 1) r = true.
  Not on public data alone: for hE, the tie's own binder hext.
The two on the place, at the full size's written list and at the tie's own m: k2_m_full
(TieFourPlacesFull.lean), by Lean's kernel. The two tests' values at the stored full-size example:
the sheet Johnson/Loose/PVK2/PadsAtFull.lean; at the form of the composed meaning's numbers they are
the same: TieFourNumbersSame.lean. That the conclusions are the tie's binders:
Johnson/Loose/PVK2/TieFourFits.lean.
LIMITS. The tests' values are premises; no theorem here shows one. TieFourPadsAt.lean's limits hold
here too: where the extractor at p lays no pad both conclusions say little, and this choice of
minePad serves the tie only at a place of the kind K2 whose row lays. That the sub-protocol's
extractor is extAt at these lists (hext) is shown by nobody here. That N, Z, rad and r are those of
the program that makes the list of rounds is said by nothing here. No soundness is claimed. On
hiding nothing.
-/
import Johnson.Top.H0.K2Caller.TieFourPadsAt
import Johnson.Top.H0.K2Caller.MembersAtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Maker Iop Cb Johnson.Pack Johnson.Top.H
open VerifiableInference.Desc (FileDescription Strs Wit Place Oracle)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Numbers numbersFit)
open VerifiableInference.Desc.First.K2Hands
open _root_.Run (ckP)

/-- **hE OF THE FOURTH TIE AT A PLACE, AT THE COMPOSED MEANING's MEMBERS.** smp stands where the
tie has smpNamed r.cs seats. -/
theorem k02_t4R_hE_plan {F : Frame} {os : List Oracle} {N : Numbers} {m : ℕ}
    {P Cells Tok Xi : Type} {r : SwRow} (G : FileDescription Xi) (d₁ d₂ : RDT) (arr : ℕ → ℕ → ℕ)
    (smp : P × VerifiableInference.Desc.First.S → (s : Sending) → (i : Fin s.l.length) →
      Option ((sigOf r.cs s.l).om i).Smp)
    (decT : (ℕ → Option (ℕ × List UInt64)) → P × VerifiableInference.Desc.First.S → Option Cells)
    (c₀ : Cells)
    (ext' : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
    (links : List ModelPart) (p : Place) (z : P) (Z : ProofFile.Pub) (rad : ℕ → ℕ → ℕ)
    (hext : ∀ a τ w, ext' a τ w = extAt r.cs G arr smp decT c₀ []
      (minePadAt (P5T.msAtR Z rad) N links p) false none (z, a.1) (strsOf F a.2) w)
    (h : numbersFit os N links.length = true) (hm : m < links.length)
    (hp : p.link.getD links.length = m + 1) (hB : membersPlanB Z rad N (m + 1) r = true) :
    ∀ a τ w, msgsOf r.cs r.l (seatNew N m r) arr (ext' a τ w) =
      msgsOf r.cs r.l (seatNew N m r) arr w :=
  k02_t4R_hE G d₁ d₂ arr smp decT c₀ ext' links p z (P5T.msAtR Z rad) hext h hm
    (by rw [hp, Nat.add_sub_cancel]) (new_long_enough hB)

/-- **hNd OF THE FOURTH TIE AT A PLACE, AT THE COMPOSED MEANING's MEMBERS.** -/
theorem k02_t4R_hNd_plan {N : Numbers} {m : ℕ} {r : SwRow} (links : List ModelPart) (p : Place)
    (Z : ProofFile.Pub) (rad : ℕ → ℕ → ℕ) (hp : p.link.getD links.length = m + 1)
    (hB : membersPlanB Z rad N (m + 1) r = true) :
    ((minePadAt (P5T.msAtR Z rad) N links p).map seatOf).Nodup := by
  rw [← hp] at hB
  exact k02_t4R_hNd N links p hB

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.k02_t4R_hE_plan
#print axioms VerifiableInference.Desc.First.K2Caller.k02_t4R_hNd_plan
