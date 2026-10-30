-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/RealPiece.lean: a law in the plain form over a written stretch is
carried to a description's piece over that stretch.

  `piece_leads_of_written`: let p be a piece with no rounds put behind. If the block's decision,
  wherever it says yes on a list of as many rounds as the piece's stretch has, is matched by a
  decision f on that list (hdec), a law
  `Leads on Q` of `writtenRed p.ds f` (Law/RealLeads.lean) gives the law `Leads on Q'` of the
  piece's own reduction, at the same errors. By `Piece.out_decide`
  (Johnson/Desc/Sound/PieceOut.lean): where a piece puts out, the tests of work have passed and its
  block's decision has said yes on the view's rounds without the sealed digest.
Limits. A carriage, general in the block: it proves no law. Q' is asked at the record that the
decision returns with the oracles that the piece's stage leaves (`p.ior.imp`), at every transcript.
f is handed the rounds alone: a block that reads columns has no place in `writtenRed`.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Close.Law.RealLeads
import Johnson.Desc.Sound.PieceOut
import OnBytes.Tie.Pv.Lookup.Peel.FoPeelJoinT

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Maker Iop Run KObj
open VerifiableInference.Desc.Sound

/-- What a piece with no rounds put behind shows its block has as many rounds as its stretch. -/
theorem shown_len {S Cl W : Type} {F : Frame} (p : Piece (ckP .two) F S Cl W) (hb : p.back = [])
    (y : F.E.Str) (τ : Iop.Tr (uLT (ckP .two) p.ds)) :
    (((sView (ckP .two) p.stage y τ).rounds ++ p.back).map noDigest).length = p.ds.length := by
  rw [hb, List.append_nil, List.length_map]
  exact Fo.Peel.rvT_length (C := ckP .two) p.ds τ

/-- **From the written stretch to the piece.** -/
theorem piece_leads_of_written {S Cl W : Type} {F : Frame} (p : Piece (ckP .two) F S Cl W)
    (hb : p.back = []) {B : Type} (f : S × F.E.Str → List Fmt.RoundView → Option B)
    (on : S × F.E.Str → Prop) (Q : S × F.E.Str → B → Prop)
    (Q' : S × F.E.Str → S × F.E.Str → Prop) (ε : Err (uLT (ckP .two) p.ds))
    (hdec : ∀ (a : S × F.E.Str) (rs : List Fmt.RoundView) gs (s' : S), rs.length = p.ds.length →
      p.b.decide a.1 rs gs = .ok s' → ∃ b, f a rs = some b ∧
        ∀ τ : Iop.Tr (uLT (ckP .two) p.ds), Q a b → Q' a (s', p.ior.imp a.2 τ))
    (h : (writtenRed p.ds f).Leads on Q ε) : p.ior.red.Leads on Q' ε := by
  refine Reduction.leads_sim (writtenRed p.ds f) p.ior.red.out on Q ε on Q'
    (fun a ha => Or.inr ⟨a, ha, fun τ a' h' => ?_⟩) h
  obtain ⟨ht, -, ⟨gs, hd⟩, himp⟩ := p.out_decide a a' τ h'
  have hlen := shown_len p hb a.2 τ
  rw [hb, List.append_nil] at hd hlen
  obtain ⟨b, hf, hq⟩ := hdec a _ gs a'.1 hlen hd
  have hp : passT (ckP .two) p.ds (rhoT (ckP .two) p.ds τ) = true := by
    unfold sTests at ht
    simp only [Bool.and_eq_true] at ht
    exact ht.1.1
  refine ⟨b, ?_, fun hQ => by
    have h1 := hq τ hQ
    rw [← himp] at h1
    exact h1⟩
  show (if passT (ckP .two) p.ds (rhoT (ckP .two) p.ds τ) = true then
      f a ((rvT (ckP .two) p.ds τ).map noDigest) else none) = some b
  rw [if_pos hp]
  exact hf

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.shown_len
#print axioms VerifiableInference.Desc.First.Close.piece_leads_of_written
