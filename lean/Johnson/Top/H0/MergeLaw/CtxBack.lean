-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/CtxBack.lean: what the merge's row of the table of joints READS rides back
past the merge's accepting step. Theorems with their proofs.

Why. The fourth tie (`merge_t4`, TieThreeFour.lean) owes, in front of the merge, the items that its
row reads: the pin of the committed table's cells, the pins of the messages of the head's first
sending, the pin of the index masks' message. They stand behind the accepting step already; the tie
takes as a premise (hcb) that they ride back. The table's rule on what rides does not speak of them:
it leaves out what a row reads.

Main names:
  `pin_rides`: a member's pin rides past a stretch of rounds, both ways: where the strings behind
    are what the stretch leaves of the strings in front, the member's tree was sent in front of the
    stretch, and the two verifier's states hold one OOD sample (our files call it the record) for
    the member. It is the library's `rides` (Johnson/Desc/Sound/SendLaw.lean) without a piece.
  `pinJT_rides`: so does the table's pin at a place of a tree (`pinJT`,
    Johnson/Desc/Sound/MeaningSig.lean).
  `merge_hcb`: THE PREMISE hcb, PAID, at every filling whose pins are the library's (`pinJT` over a
    list of members; `pinWOf`).

Its premises. hpin, hpinW: the filling's form. hF: every member of the list that sits at a place
which the row reads was sent in front of the merge's stretch: a fact on the numbers of the trees.
hsmp, hdec: the reader of the stored OOD samples and the decoder of the stored table do not read
what the merge writes. The accepting step, and the equation on the strings behind it: both are in
hand in the fourth tie of `merge_seatLawsZ` (TieLawsZ.lean).

Limits. hF, hsmp and hdec are shown at no filling here. Nothing on soundness.
-/
import Johnson.Top.H0.MergeLaw.TieThreeFour
import Johnson.Desc.Sound.MeaningSig
import Johnson.Desc.Sound.SendLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.First.MergeLaw
open Iop
open OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open _root_.Run (ckP)
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (FileDescription Place Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S HeadOwn ModelPart Item Meaning Numbers)
open Johnson.Pack (sigOf)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)

section
variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {A Cells Tok : Type} (arr : ℕ → ℕ → ℕ)
  (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  {C : CK} {Fr : Frame}

/-- **A pin rides past a stretch of rounds**, both ways: where the strings behind are what the
stretch leaves of the strings in front, the member's tree was sent in front of the stretch, and the
two states hold one OOD sample for the member. (The library's `rides`,
Johnson/Desc/Sound/SendLaw.lean, without a piece.) -/
theorem pin_rides (base : ℕ) (ds : List RDT) (x : Mem) (hF : Fenced base [x]) (a b : A)
    (y : Fr.E.Str) (τ : Iop.Tr (uLT C ds)) (es : smp b x.1 x.2 = smp a x.1 x.2)
    (w : Wit Cells Tok MsgT) :
    PinAt G cs x.1.l x.1.seat (fun z => smp z x.1) arr x.2 b (strsOf Fr (behind C Fr base ds y τ)) w
        ↔
      PinAt G cs x.1.l x.1.seat (fun z => smp z x.1) arr x.2 a (strsOf Fr y) w := by
  have hw := wordsStay G cs x.1.l x.1.seat C Fr base ds y τ x.2 (hF x (by simp))
  have hsh : ShownAt G cs x.1.l x.1.seat (strsOf Fr (behind C Fr base ds y τ)) x.2 ↔
      ShownAt G cs x.1.l x.1.seat (strsOf Fr y) x.2 := by
    unfold ShownAt
    rw [wordStays Xi G C Fr base ds y τ (x.1.seat x.2).1 (x.1.seat x.2).2 (hF x (by simp))]
  unfold PinAt
  simp only [es, hw, hsh]

/-- **So does the table's pin at a place of a tree**, where every member of the list that sits there
is so. -/
theorem pinJT_rides (ms : List Mem) (base : ℕ) (ds : List RDT) (j t : ℕ)
    (hF : ∀ x ∈ ms, SitsAt x j t → Fenced base [x]) (a b : A) (y : Fr.E.Str)
    (τ : Iop.Tr (uLT C ds)) (es : ∀ x ∈ ms, SitsAt x j t → smp b x.1 x.2 = smp a x.1 x.2)
    (w : Wit Cells Tok MsgT)
    (h : pinJT cs G arr smp ms j t b (strsOf Fr (behind C Fr base ds y τ)) w) :
    pinJT cs G arr smp ms j t a (strsOf Fr y) w :=
  ⟨h.1, fun x hx hs =>
    (pin_rides cs G arr smp base ds x (hF x hx hs) a b y τ (es x hx hs) w).1 (h.2 x hx hs)⟩

end

section
variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {Pp Cells Tok : Type} (arr : ℕ → ℕ → ℕ)
  (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells) {Fr : Frame}

/-- **WHAT THE MERGE's ROW READS RIDES BACK PAST ITS ACCEPTING STEP**: the premise hcb of `merge_t4`
(TieThreeFour.lean), PAID, at every filling whose pins are the library's (`pinJT` over a list of
members ms; `pinWOf`): where every member of ms that sits at a place which the row reads was sent in
front of the merge's stretch of rounds, and the two readers of the verifier's state do not read what
the merge writes. -/
theorem merge_hcb (ms : List Mem) (Nn : Numbers) (Mg : Meaning Pp (Wit Cells Tok MsgT)) (m : ℕ)
    (P : HeadMergeP) (base : ℕ) (ds : List RDT)
    (hpin : ∀ j t a y w, Mg.pin j t a y w ↔ pinJT cs G arr smp ms j t a y w)
    (hpinW : ∀ a y w, Mg.pinW a y w ↔ pinWOf decT a y w)
    (hF : ∀ p ∈ Nn.index :: Nn.sent m 0, ∀ x ∈ ms, SitsAt x p.1 p.2 → Fenced base [x])
    (hsmp : ∀ z (s : S) (a' : HeadOwn),
      smp (z, { s with rowsOwed := none, here := .head a' }) = smp (z, s))
    (hdec : ∀ z c (s : S) (a' : HeadOwn),
      decT c (z, { s with rowsOwed := none, here := .head a' }) = decT c (z, s))
    (z : Pp) (a b : S × Fr.E.Str) (w : Wit Cells Tok MsgT)
    (hy : ∃ rs, headMergeDecide P a.1 rs = .ok b.1)
    (hb : ∃ τ : Iop.Tr (uLT (ckP .two) ds), b.2 = behind (ckP .two) Fr base ds a.2 τ) :
    ∀ i ∈ [Item.pinW, .pin m 0, .pinI], meansQ Nn Mg (fun s => (z, s)) i b w →
      meansQ Nn Mg (fun s => (z, s)) i a w := by
  obtain ⟨rs, hy⟩ := hy
  obtain ⟨τ, hb⟩ := hb
  obtain ⟨_, a', _, _, e, _⟩ := isLocal P a.1 rs b.1 hy
  have es : smp (z, b.1) = smp (z, a.1) := by rw [e, hsmp]
  have back : ∀ p ∈ Nn.index :: Nn.sent m 0, Mg.pin p.1 p.2 (z, b.1) (strsOf Fr b.2) w →
      Mg.pin p.1 p.2 (z, a.1) (strsOf Fr a.2) w := by
    intro p hp h
    rw [hpin] at h ⊢
    rw [hb] at h
    exact pinJT_rides cs G arr smp ms base ds p.1 p.2 (hF p hp) (z, a.1) (z, b.1) a.2 τ
      (fun x _ _ => by rw [es]) w h
  intro i hi h
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · have h' : Mg.pinW (z, b.1) (strsOf Fr b.2) w := h
    show Mg.pinW (z, a.1) (strsOf Fr a.2) w
    rw [hpinW] at h' ⊢
    unfold pinWOf at h' ⊢
    rw [hb, e, hdec] at h'
    exact h'
  · have h' : ∀ x ∈ Nn.sent m 0, Mg.pin x.1 x.2 (z, b.1) (strsOf Fr b.2) w := h
    show ∀ x ∈ Nn.sent m 0, Mg.pin x.1 x.2 (z, a.1) (strsOf Fr a.2) w
    exact fun x hx => back x (List.mem_cons_of_mem _ hx) (h' x hx)
  · have h' : Mg.pin Nn.index.1 Nn.index.2 (z, b.1) (strsOf Fr b.2) w := h
    show Mg.pin Nn.index.1 Nn.index.2 (z, a.1) (strsOf Fr a.2) w
    exact back Nn.index (List.mem_cons_self) h'

end

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.merge_hcb
#print axioms VerifiableInference.Desc.First.MergeLaw.pin_rides
#print axioms VerifiableInference.Desc.First.MergeLaw.pinJT_rides
