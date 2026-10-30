-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/PieceOf.lean: THE THREE PREMISES THAT `k10_piece` ASKS OF A PIECE, AT
K10's BLOCK LIFTED TO A WIDER RECORD. A definition, statements and proofs.

`k10_piece` (AtPiece.lean, beside this file) asks of a piece: nothing is put behind its rounds; its
rounds' data are dB, dE and k times dR; its block's decision is `closeFrame`'s.
  `lift_decide_iff`: K10's block at a place P (Johnson/Desc/First/Close/Kind.lean), lifted to a
    wider record by get and set (`Block.lift`, Johnson/Desc/Block.lean), says yes with a record s'
    exactly if `closeFrame`, at what is owed, the frame and the statement of the part that get
    reads, at the place's entries, says yes with some x, and s' is set of "nothing owed", the frame
    and the statement behind.
  `below_yes`: a yes of `below b` (Johnson/Desc/Sound/ChainRule.lean: the proof's device that first
    tests that the words shown are below the prime, then decides as b does) is a yes of b.
  `pieceAt P get set base dB dE dR k ext err`: the piece with that block UNDER `below`, as the rules
    above a piece ask of the pieces' blocks, and these rounds' data.
  `pieceAt_back`, `pieceAt_ds`, `pieceAt_dec`: it meets the three premises: the first two by make.
Limits. dB, dE, dR and k are letters: that they are the data of the rounds that the block declares
(`entries P`) is not asked here, and what a law of the piece is worth where they are not is not
shown. ext and err are letters too: `k10_piece` is a law in the form `Leads` and says nothing of
ext; who carries it to what a chain's rule asks of a piece (`GoodIn`) is not named here. Whether a
description's list holds this block as a block of its own is that list's matter. Nothing on
soundness.

-/
import Johnson.Desc.First.Close.Law.KindDecide
import Johnson.Desc.Sound.ChainRule

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Flat OnBytes.Maker Iop Run
open VerifiableInference.Desc.Sound

theorem lift_decide_iff {Cl T : Type} (P : Par) (get : T → Rec) (set : T → Rec → T) (s s' : T)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    (((kind (Cl := Cl)) P).lift get set).decide s rs gs = .ok s' ↔
      ∃ x, closeFrame (get s).owed (get s).frame (get s).st (entries P) rs = .ok x ∧
        s' = set s ⟨none, x.1, x.2⟩ := by
  show (((kind (Cl := Cl)) P).decide (get s) rs gs).map (set s) = .ok s' ↔ _
  constructor
  · intro h
    cases hd : ((kind (Cl := Cl)) P).decide (get s) rs gs with
    | error e => rw [hd] at h; cases h
    | ok y =>
      rw [hd] at h
      obtain ⟨x, hx, rfl⟩ := (kind_decide_iff P (get s) y rs gs).1 hd
      exact ⟨x, hx, (Except.ok.inj h).symm⟩
  · rintro ⟨x, hx, rfl⟩
    rw [(kind_decide_iff (Cl := Cl) P (get s) _ rs gs).2 ⟨x, hx, rfl⟩]
    rfl

/-- A yes of `below b` is a yes of b. -/
theorem below_yes {S Cl : Type} (b : Block S Cl) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (below b).decide s rs gs = .ok s') :
    b.decide s rs gs = .ok s' := by
  have h' : (if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then b.decide s rs gs
      else .error "a word is not below the prime") = .ok s' := h
  split at h'
  · exact h'
  · cases h'

/-- The piece of K10's block, lifted, UNDER `below`, with these rounds' data. -/
def pieceAt {Cl T W : Type} {F : Frame} (P : Par) (get : T → Rec) (set : T → Rec → T) (base : ℕ)
    (dB dE dR : RDT) (k : ℕ)
    (ext : T × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dE :: List.replicate k dR)) → W → W)
    (err : Err (uLT (ckP .two) (dB :: dE :: List.replicate k dR))) :
    Piece (ckP .two) F T Cl W :=
  { b := below (((kind (Cl := Cl)) P).lift get set), base := base
    ds := dB :: dE :: List.replicate k dR, ext := ext, err := err }

section
variable {Cl T W : Type} {F : Frame} (P : Par) (get : T → Rec) (set : T → Rec → T) (base : ℕ)
  (dB dE dR : RDT) (k : ℕ)
  (ext : T × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dE :: List.replicate k dR)) → W → W)
  (err : Err (uLT (ckP .two) (dB :: dE :: List.replicate k dR)))

theorem pieceAt_back : (pieceAt (Cl := Cl) P get set base dB dE dR k ext err).back = [] := rfl

theorem pieceAt_ds : (pieceAt (Cl := Cl) P get set base dB dE dR k ext err).ds =
    dB :: dE :: List.replicate k dR := rfl

theorem pieceAt_dec (s : T) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (s' : T)
    (h : (pieceAt (Cl := Cl) P get set base dB dE dR k ext err).b.decide s rs gs = .ok s') :
    ∃ x, closeFrame ((get s).owed, (get s).frame, (get s).st).1
        ((get s).owed, (get s).frame, (get s).st).2.1
        ((get s).owed, (get s).frame, (get s).st).2.2 (entries P) rs = .ok x ∧
      s' = set s ⟨none, x.1, x.2⟩ :=
  (lift_decide_iff P get set s s' rs gs).1 (below_yes _ s s' rs gs h)

end

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.lift_decide_iff
#print axioms VerifiableInference.Desc.First.Close.below_yes
#print axioms VerifiableInference.Desc.First.Close.pieceAt_dec
