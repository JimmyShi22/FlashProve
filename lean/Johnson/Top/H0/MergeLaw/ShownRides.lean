-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/ShownRides.lean: K11's SECOND TIE: THE TABLE's TWO PROMISES "shown" AND "no
collision", AT EVERY SAMPLED PLACE OF THE OPEN SET, RIDE FORWARD PAST THE MERGE's ACCEPTING STEP:
the premise hSN of `merge_t2` (Johnson/Top/H0/MergeLaw/TieOneTwo.lean), PAID, general in the
filling. Theorems.

Why it can ride at all. "No collision" is, member by member, `CfAt`
(Johnson/Desc/Sound/MsgSig.lean): the verifier's state holds the member's OOD sample; every leaf of
its tree is shown; no two members of the list of ITS OWN word have one answer at the sample's seed.
It reads the strings at the member's own tree alone. A stretch of rounds behind that tree's sending
leaves these strings (`wordStays`, `wordsStay`): so strings that are added behind can make no new
collision in this sense.

What is said.
  `shownAt_rides`, `cfAt_rides`: the two, at one member, both ways (the second half of the library's
    `rides`, Johnson/Desc/Sound/SendLaw.lean, without a piece; beside CtxBack.lean's `pin_rides`,
    which has the first half).
  `shownNoColl_rides`: the table's two promises (`shownJT`, `noCollJT`,
    Johnson/Desc/Sound/MeaningSig.lean) at a place of a tree, forward.
  `merge_hSN`: **hSN to the letter at Q := the sampled places of the open set**, where: the
    filling's "shown" and "no collision" are the library's over a list of members ms; every member
    of ms that sits at a place of Q was sent in front of the merge's stretch (the fence); the reader
    of the samples does not read what the merge writes; the strings behind are what the stretch
    leaves of the strings in front.

Limits. Implications. The four premises are shown here at no filling: the fence at the closed values
is an evaluation member by member; hshown, hnoColl and hsmp are the filling's own laws. WHERE NO
MEMBER OF ms SITS AT A PLACE "shown" IS FALSE THERE, IN FRONT AND BEHIND: the implication then holds
idly. Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.Law
import Johnson.Desc.Sound.MeaningSig
import Johnson.Desc.Sound.SendLaw
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open Iop
open OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open _root_.Run (ckP)
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (FileDescription Place Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S HeadOwn Meaning)
open Johnson.Pack (sigOf)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)

section
variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {A : Type}
  (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  {C : CK} {Fr : Frame}

/-- **"Every leaf is shown" rides past a stretch of rounds**, both ways, at a member whose tree was
sent in front of the stretch. -/
theorem shownAt_rides (base : ℕ) (ds : List RDT) (x : Mem) (hF : Fenced base [x]) (y : Fr.E.Str)
    (τ : Iop.Tr (uLT C ds)) :
    ShownAt G cs x.1.l x.1.seat (strsOf Fr (behind C Fr base ds y τ)) x.2 ↔
      ShownAt G cs x.1.l x.1.seat (strsOf Fr y) x.2 := by
  unfold ShownAt
  rw [wordStays Xi G C Fr base ds y τ (x.1.seat x.2).1 (x.1.seat x.2).2 (hF x (by simp))]

/-- **So does "the member has no collision"**, where the two states hold one OOD sample for it. -/
theorem cfAt_rides (base : ℕ) (ds : List RDT) (x : Mem) (hF : Fenced base [x]) (a b : A)
    (y : Fr.E.Str) (τ : Iop.Tr (uLT C ds)) (es : smp b x.1 x.2 = smp a x.1 x.2) :
    CfAt G cs x.1.l x.1.seat (fun z => smp z x.1) x.2 b (strsOf Fr (behind C Fr base ds y τ)) ↔
      CfAt G cs x.1.l x.1.seat (fun z => smp z x.1) x.2 a (strsOf Fr y) := by
  have hw := wordsStay G cs x.1.l x.1.seat C Fr base ds y τ x.2 (hF x (by simp))
  have hsh := shownAt_rides cs G base ds x hF y τ
  unfold CfAt
  simp only [es, hw, hsh]

/-- **The table's two promises at a place of a tree ride forward past a stretch of rounds**, where
every member of the list that sits there is so. -/
theorem shownNoColl_rides (ms : List Mem) (base : ℕ) (ds : List RDT) (j t : ℕ)
    (hF : ∀ x ∈ ms, SitsAt x j t → Fenced base [x]) (a b : A) (y : Fr.E.Str)
    (τ : Iop.Tr (uLT C ds)) (es : ∀ x ∈ ms, SitsAt x j t → smp b x.1 x.2 = smp a x.1 x.2)
    (h : shownJT cs G ms j t (strsOf Fr y) ∧ noCollJT cs G smp ms j t a (strsOf Fr y)) :
    shownJT cs G ms j t (strsOf Fr (behind C Fr base ds y τ)) ∧
      noCollJT cs G smp ms j t b (strsOf Fr (behind C Fr base ds y τ)) :=
  ⟨⟨h.1.1, fun x hx hs => (shownAt_rides cs G base ds x (hF x hx hs) y τ).2 (h.1.2 x hx hs)⟩,
    fun x hx hs => (cfAt_rides cs G smp base ds x (hF x hx hs) a b y τ (es x hx hs)).2
      (h.2 x hx hs)⟩

end

section
variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {Pp W : Type}
  (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  {Fr : Frame}

/-- **"SHOWN" AND "NO COLLISION" RIDE PAST THE MERGE's ACCEPTING STEP**: the premise hSN of
`merge_t2` (TieOneTwo.lean), PAID, at every filling whose two promises are the library's. Q: the
sampled places of the open set. -/
theorem merge_hSN (ms : List Mem) (Mg : Meaning Pp W) (Q : List (ℕ × ℕ)) (P : HeadMergeP)
    (base : ℕ) (ds : List RDT)
    (hshown : ∀ j t y, Mg.shown j t y ↔ shownJT cs G ms j t y)
    (hnoColl : ∀ j t a y, Mg.noColl j t a y ↔ noCollJT cs G smp ms j t a y)
    (hF : ∀ p ∈ Q, ∀ x ∈ ms, SitsAt x p.1 p.2 → Fenced base [x])
    (hsmp : ∀ z (s : S) (a' : HeadOwn),
      smp (z, { s with rowsOwed := none, here := .head a' }) = smp (z, s))
    (z : Pp) (a b : S × Fr.E.Str) (hy : ∃ rs, headMergeDecide P a.1 rs = .ok b.1)
    (hb : ∃ τ : Iop.Tr (uLT (ckP .two) ds), b.2 = behind (ckP .two) Fr base ds a.2 τ) :
    ∀ x ∈ Q, Mg.shown x.1 x.2 (strsOf Fr a.2) ∧ Mg.noColl x.1 x.2 (z, a.1) (strsOf Fr a.2) →
      Mg.shown x.1 x.2 (strsOf Fr b.2) ∧ Mg.noColl x.1 x.2 (z, b.1) (strsOf Fr b.2) := by
  obtain ⟨rs, hy⟩ := hy
  obtain ⟨τ, hb⟩ := hb
  obtain ⟨_, a', _, _, e, _⟩ := isLocal P a.1 rs b.1 hy
  have es : smp (z, b.1) = smp (z, a.1) := by rw [e, hsmp]
  intro x hx h
  rw [hshown, hnoColl] at h ⊢
  rw [hb]
  exact shownNoColl_rides cs G smp ms base ds x.1 x.2 (hF x hx) (z, a.1) (z, b.1) a.2 τ
    (fun y _ _ => by rw [es]) h

end

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.shownAt_rides
#print axioms VerifiableInference.Desc.First.MergeLaw.cfAt_rides
#print axioms VerifiableInference.Desc.First.MergeLaw.shownNoColl_rides
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_hSN
