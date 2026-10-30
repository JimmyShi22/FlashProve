-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
One file of the set on the key file's table of joints (Johnson/Desc/Key/KeyBorders.lean).
Johnson/Desc/Sound/KeyKeepsOfSeats.lean: FROM THE COIN OF THE TABLE's FILES TO THE PLAIN ROAD's: what fills a seat between two rows of the table of joints (Johnson/Desc/Sound/KeyJoints.lean: JointRow; KeyRelLaw.lean: QuietTie; KeySeatsAt.lean: SeatGood) gives the plain road's law «Keeps»
(Johnson/Desc/Plain/Leads.lean:51) at the rows' own conditions and relations. General in the state, the frame and the piece.
  keeps_of_tie    a block whose yes ties two rows for certain (QuietTie), where the row behind reads no tree from the piece's place on: Keeps, at any errors
  keeps_of_good   a piece that is good between two rows (the knowledge form, with a lost promise paid in its counts), WHERE BESIDES THE PROMISE BEHIND IS KEPT FOR CERTAIN: Keeps, at the piece's errors.
                  WHY THE SECOND PREMISE: KeyRowsPlain.lean's head: a carried typed block gives «(true behind, or the promise behind is lost) → true in front», not «the promise behind is kept»: at a TRUE statement Keeps asks the promise behind too.
  keeps_of_good_leads   the same where the promise behind is kept up to the piece's own errors (one Leads): it reaches the sendings; keeps_of_good is its case «for certain»
  keeps_conseq    a law between two rows, carried to a stronger promise in front and a weaker row behind: how two tables are tied at a border
Nothing on soundness of any protocol.
-/
import Johnson.Desc.Sound.KeyRowsPlain
import Johnson.Desc.Plain.PieceYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.Plain
open _root_.Run (ckP)
open _root_.Iop (Err Reduction Doomed)

variable {S Cl W : Type} {F : Frame}

theorem out_imp (p : Piece (ckP .two) F S Cl W) (a b : S × F.E.Str) (τ : Iop.Tr (uLT (ckP .two) p.ds)) (h : p.ior.red.out a τ = some b) : b = (b.1, p.ior.imp a.2 τ) := by
  have h' : (p.ior.out a.1 a.2 τ).map (fun x => (x, p.ior.imp a.2 τ)) = some b := h
  obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.1 h'
  rfl

/-- **A tie gives Keeps.** -/
theorem keeps_of_tie (p : Piece (ckP .two) F S Cl W) (A B : JointRow S F) (h : QuietTie p.b A B) (hnd : (F.all.map (·.no)).Nodup)
    (hon : ReadsBelow p.base B.on) (hrel : ReadsBelow p.base B.rel) : p.ior.red.Keeps A.on B.on A.rel B.rel p.err := by
  unfold Reduction.Keeps
  refine Reduction.Leads.of_sure (K := p.ior.red) p.err fun a τ b ha hb => ?_
  have hd := piece_decides_at p a τ b hb
  obtain ⟨h1, h2⟩ := h a.1 b.1 a.2 _ _ ha hd
  rw [out_imp p a b τ hb, hon.imp hnd p (Nat.le_refl _) b.1 a.2 τ, hrel.imp hnd p (Nat.le_refl _) b.1 a.2 τ]
  exact ⟨h1, h2⟩

/-- **A good piece that keeps the promise behind for certain gives Keeps.** -/
theorem keeps_of_good [Inhabited W] (p : Piece (ckP .two) F S Cl W) (A B : JointRow S F)
    (h : (p.bk A.on B.on (fun a _ => A.rel a) (fun a _ => B.rel a)).Good)
    (hs : ∀ a τ b, A.on a → p.ior.red.out a τ = some b → B.on b) : p.ior.red.Keeps A.on B.on A.rel B.rel p.err := by
  intro a ha
  by_cases hr : A.rel a
  · exact Doomed.of_forall _ _ fun τ b hb => ⟨hs a τ b ha hb, fun _ => hr⟩
  · exact Doomed.mono _ _ (fun τ hτ b hb => ⟨(hτ b hb).1, fun hb' => absurd hb' (hτ b hb).2⟩) (outright_leads_false p A B h a ⟨ha, hr⟩)

/-- **The same with the second premise weakened**: the promise behind need not be kept FOR CERTAIN: it is enough that it is kept UP TO THE PIECE's OWN ERRORS (one Leads): so it reaches a block that opens a pin (a sending: NoColl at the new pin costs the error). -/
theorem keeps_of_good_leads [Inhabited W] (p : Piece (ckP .two) F S Cl W) (A B : JointRow S F)
    (h : (p.bk A.on B.on (fun a _ => A.rel a) (fun a _ => B.rel a)).Good)
    (hs : p.ior.red.Leads A.on (fun _ b => B.on b) p.err) : p.ior.red.Keeps A.on B.on A.rel B.rel p.err := by
  intro a ha
  by_cases hr : A.rel a
  · exact Doomed.mono _ _ (fun τ hτ b hb => ⟨hτ b hb, fun _ => hr⟩) (hs a ha)
  · exact Doomed.mono _ _ (fun τ hτ b hb => ⟨(hτ b hb).1, fun hb' => absurd hb' (hτ b hb).2⟩) (outright_leads_false p A B h a ⟨ha, hr⟩)

/-- **Two tables tied at a border.** -/
theorem keeps_conseq {A B : Type} {K : Reduction A B} {on on₀ : A → Prop} {on' on₀' : B → Prop} {L L₀ : A → Prop} {L' L₀' : B → Prop} {ε : Err K.shape}
    (h : K.Keeps on on' L L' ε) (h1 : ∀ a, on₀ a → on a) (h2 : ∀ a, on₀ a → L a → L₀ a)
    (h3 : ∀ a τ b, on₀ a → K.out a τ = some b → on' b → on₀' b) (h4 : ∀ a τ b, on₀ a → K.out a τ = some b → on' b → L₀' b → L' b) : K.Keeps on₀ on₀' L₀ L₀' ε :=
  Reduction.Leads.conseq h h1 fun a τ b ha hb hq => ⟨h3 a τ b ha hb hq.1, fun hl => h2 a ha (hq.2 (h4 a τ b ha hb hq.1 hl))⟩

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.keeps_of_tie
#print axioms VerifiableInference.Desc.Sound.keeps_of_good
#print axioms VerifiableInference.Desc.Sound.keeps_conseq
#print axioms VerifiableInference.Desc.Sound.keeps_of_good_leads
