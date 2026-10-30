-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3DigitsLookOut.lean: the lookup on the digits of a link's smallness test:
THE PROMISE BEHIND THE LOOKUP's PLACE (k3OnOut, Johnson/Desc/First/Look/K3Borders.lean) FROM THE
PROMISE IN FRONT (k3OnIn) AND A YES OF K3.block's decide: the twin of
Johnson/Desc/First/Look/K3CallsLookOut.lean, whose proofs it follows line by line with the digits'
seat's own lemmas. Statements and proofs. A tie: no error term.

Main names.
  k3LeavesAtDigits: K3LeavesAtDigits (Johnson/Top/H/K3LeftDigits.lean), no premise left: by
    lkPadCEnd (Johnson/Top/H/K3CEnd.lean).
  k3_digits_lookOut: THE END, at decide.
  k3_digits_lookOut_piece: at a piece that holds «below b» for a block b whose decide says yes only
    where K3.block's does.
OBJECT. Desc.K3.block's decide at Desc.K3.seatDigits, as K3.theOwn lays it where digits = true; at a
piece: any block b whose decide says yes only where that one does.
USER. Nobody yet. Meant: t2 of the digits' lookup's row at the table of joints (the public item
lookOut).
LETTERS. claim, piece, laid, before, guests free; p with p.digits = true.
Compiled with the whole library.

Limits. At the digits' seat. At rounds whose words are below the prime (okRoundsE): a piece's yes
gives that. It gives k3OnOut alone, not the rest of the table's promise behind.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallsLookOut
import Johnson.Top.H.K3LeftDigits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open OnBytes.PscRun
open VerifiableInference.Desc.Sound (Frame Piece below)
open VerifiableInference.Desc.K3 (sizedB freeB heardAt k3OnIn k3OnOut)

/-- **K3.block's decide at the digits' seat leaves the record**: no premise left. -/
theorem k3LeavesAtDigits : K3LeavesAtDigits := k3LeavesAtDigits_of Fo.Tp.lkPadCEnd

/-- **From the promise in front and a yes to the promise behind.** -/
theorem k3_digits_lookOut {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) {h : Forest.Shape}
    (hs : p.shape = some h) (hdg : p.digits = true) (s s' : Desc.First.S) (rs : List Fmt.RoundView)
    (cols : List (List (ℕ × List UInt64))) (hw : okRoundsE rs = true)
    (hd : (Desc.K3.block (Desc.K3.seatDigits claim) piece laid before p guests).decide s rs cols =
      .ok s') (hIn : k3OnIn p s = true) : k3OnOut p s' = true := by
  obtain ⟨Fk, hf, hz, hn, hfree⟩ := k3OnIn_free hs hIn
  obtain ⟨F, F', g, hF, hF', hg, hL⟩ :=
    k3LeavesAtDigits Cl claim piece laid before p guests h hs Cb.Gl.E Reading.gl p.lm s s' rs cols
      hw hd
  obtain rfl : Fk = F := Option.some.inj (hf.symm.trans hF)
  obtain ⟨F1, y, hF1, hn1, e1, hE⟩ :=
    decide_exact (Desc.K3.seatDigits claim) piece laid before p guests s s' rs cols hd
  obtain rfl : Fk = F1 := Option.some.inj (hf.symm.trans hF1)
  have hsome : ((Desc.K3.seatDigits claim).fork s).isSome = true := by
    rw [hF1]
    rfl
  have hg1 : (Desc.K3.seatDigits claim).heard s' = some y.1 := by
    rw [e1]
    exact Desc.K3.seatDigits_reads claim _ _ _ hsome hn1
  have hF1' : (Desc.K3.seatDigits claim).fork s' = some y.2 := by
    rw [e1]
    exact seatDigits_keeps claim _ _ _ hsome hn1
  obtain rfl : g = y.1 := Option.some.inj (hg.symm.trans hg1)
  obtain rfl : F' = y.2 := Option.some.inj (hF'.symm.trans hF1')
  have L := hL hz
  have E := (hE hz).1
  rw [L.shape] at E
  refine k3OnOut_of_left p s' hs ?_ hF' L E hn hfree (_root_.Fo.Pay.shapeOf_ok (shape_some p h hs))
  rw [hdg]
  exact hg

/-- The same at a piece. -/
theorem k3_digits_lookOut_piece {Cl W : Type} {Fr : Frame} (claim : Aff → Cl) (piece : ℕ)
    (laid : Array Nat) (before : List (ℕ × ℕ)) (pp : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (b : Desc.Block Desc.First.S Cl)
    (hyes : ∀ s rs cols s', b.decide s rs cols = .ok s' →
      (Desc.K3.block (Desc.K3.seatDigits claim) piece laid before pp guests).decide s rs cols =
        .ok s')
    (p : Piece (ckP .two) Fr Desc.First.S Cl W) (hb : p.b = below b) (hback : p.back = [])
    {h : Forest.Shape} (hs : pp.shape = some h) (hdg : pp.digits = true)
    (a a' : Desc.First.S × Fr.E.Str) (τ : Tr (uLT (ckP .two) p.ds))
    (hout : p.ior.red.out a τ = some a') (hIn : k3OnIn pp a.1 = true) :
    k3OnOut pp a'.1 = true := by
  obtain ⟨-, -, hw, cols, hd⟩ := piece_hears_below p b hb hback a τ a' hout
  exact k3_digits_lookOut claim piece laid before pp guests hs hdg a.1 a'.1 _ cols hw
    (hyes _ _ _ _ hd) hIn

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3LeavesAtDigits
#print axioms VerifiableInference.OnPublicFiles.k3_digits_lookOut
#print axioms VerifiableInference.OnPublicFiles.k3_digits_lookOut_piece
