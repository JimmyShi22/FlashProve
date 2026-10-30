-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3CallsLookOut.lean: the lookup on a link's CALLS: THE PROMISE BEHIND THE
LOOKUP's PLACE (k3OnOut, Johnson/Desc/First/Look/K3Borders.lean) FROM THE PROMISE IN FRONT (k3OnIn)
AND A YES OF K3.block's decide. Statements and proofs. A tie: no error term.

OBJECT: Desc.K3.block's decide, as K3.theOwn lays it (Johnson/Desc/First/Look/K3Own.lean:78:
  seat := seatCalls claim or seatDigits claim, guests := []); at a piece: any
  block b whose decide says yes only where that one does.
USER: k3_att_atTable (Johnson/Desc/First/Look/K3AttAtTable.lean).
LETTERS: seat := seatCalls claim; piece, laid, before, guests free; p with p.digits = false.
Built on: Johnson/Desc/Block.lean,
  Johnson/Desc/First/State.lean,
  Johnson/Desc/First/Look/K3Lookup.lean.

Main names:
  `k3OnIn_free`: what the promise in front says of the ledger: it is open, has its sizes, stands at
    the place's first slot, and the lookup's slots are free.
  `k3_calls_leaves`: what a yes leaves, under the promise in front. `k3_calls_next`: directly behind
    the lookup the ledger stands at the place's first slot and the lookup's count of slots.
  `k3_calls_lookOut`: THE END, at decide. `k3_calls_lookOut_piece`: at a piece that holds "below b"
    for a block b whose decide says yes only where K3.block's does.

Limits. At the calls' seat. At rounds whose words are below the prime (okRoundsE): a piece's yes
gives that. It gives k3OnOut alone, not the rest of the table's promise behind.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3OnOutOfLeft
import Johnson.Top.H.K3CEnd
import Johnson.Top.H.K3PieceHears

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open OnBytes.PscRun
open VerifiableInference.Desc.Sound (Frame Piece below)
open VerifiableInference.Desc.K3 (sizedB freeB heardAt k3OnIn k3OnOut)

theorem k3OnIn_free {p : Desc.First.Look.P} {s : Desc.First.S} {h : Forest.Shape}
    (hs : p.shape = some h) (hIn : k3OnIn p s = true) :
    ∃ Fk, s.fork? = some Fk ∧ Sized Fk ∧ Fk.next = p.first ∧
      freeB Fk p.first (Forest.elems h) = true := by
  unfold k3OnIn at hIn
  rw [hs] at hIn
  simp only [Bool.and_eq_true] at hIn
  obtain ⟨-, hany⟩ := hIn
  cases hf : s.fork? with
  | none =>
    rw [hf] at hany
    simp at hany
  | some Fk =>
    rw [hf] at hany
    have h2 : (Fk.next == p.first && sizedB Fk && freeB Fk p.first (Forest.elems h)) = true := hany
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    have h3 : sizedB Fk = true := h2.1.2
    simp only [sizedB, Bool.and_eq_true, beq_iff_eq] at h3
    exact ⟨Fk, rfl, ⟨h3.1.1, h3.1.2, h3.2⟩, h2.1.1, h2.2⟩

/-- **What a yes leaves, under the promise in front**: one ledger in front, one behind, one heard
record, with both records of what the hearing leaves. -/
theorem k3_calls_leaves {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) {h : Forest.Shape}
    (hs : p.shape = some h) (s s' : Desc.First.S) (rs : List Fmt.RoundView)
    (cols : List (List (ℕ × List UInt64))) (hw : okRoundsE rs = true)
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') (hIn : k3OnIn p s = true) :
    ∃ (F F' : Fork) (g : Forest.Heard), s.fork? = some F ∧ F.next = p.first ∧
      freeB F p.first (Forest.elems h) = true ∧ s'.fork? = some F' ∧ s'.lookHeard? = some g ∧
      K3Left Reading.gl h p.lm F F' g (rs.map (rdRV Reading.gl)) ∧ Fo.Tp.PadExact h F F' g := by
  obtain ⟨Fk, hf, hz, hn, hfree⟩ := k3OnIn_free hs hIn
  obtain ⟨F, F', g, hF, hF', hg, hL⟩ :=
    k3LeavesAtCalls Cl claim piece laid before p guests h hs Cb.Gl.E Reading.gl p.lm s s' rs cols
      hw hd
  obtain rfl : Fk = F := Option.some.inj (hf.symm.trans hF)
  obtain ⟨F1, y, hF1, hn1, e1, hE⟩ :=
    decide_exact (Desc.K3.seatCalls claim) piece laid before p guests s s' rs cols hd
  obtain rfl : Fk = F1 := Option.some.inj (hf.symm.trans hF1)
  have hsome : ((Desc.K3.seatCalls claim).fork s).isSome = true := by
    rw [hF1]
    rfl
  have hg1 : (Desc.K3.seatCalls claim).heard s' = some y.1 := by
    rw [e1]
    exact Desc.K3.seatCalls_reads claim _ _ _ hsome hn1
  have hF1' : (Desc.K3.seatCalls claim).fork s' = some y.2 := by
    rw [e1]
    exact seatCalls_keeps claim _ _ _ hsome hn1
  obtain rfl : g = y.1 := Option.some.inj (hg.symm.trans hg1)
  obtain rfl : F' = y.2 := Option.some.inj (hF'.symm.trans hF1')
  have L := hL hz
  have E := (hE hz).1
  rw [L.shape] at E
  exact ⟨Fk, _, _, hf, hn, hfree, hF', hg, L, E⟩

/-- **From the promise in front and a yes to the promise behind.** -/
theorem k3_calls_lookOut {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) {h : Forest.Shape}
    (hs : p.shape = some h) (hdg : p.digits = false) (s s' : Desc.First.S) (rs : List Fmt.RoundView)
    (cols : List (List (ℕ × List UInt64))) (hw : okRoundsE rs = true)
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') (hIn : k3OnIn p s = true) : k3OnOut p s' = true := by
  obtain ⟨F, F', g, -, hn, hfree, hF', hg, L, E⟩ :=
    k3_calls_leaves claim piece laid before p guests hs s s' rs cols hw hd hIn
  refine k3OnOut_of_left p s' hs ?_ hF' L E hn hfree (_root_.Fo.Pay.shapeOf_ok (shape_some p h hs))
  rw [hdg]
  exact hg

/-- **Directly behind the lookup the ledger stands at one public number**: the place's first slot
and the lookup's count of slots. -/
theorem k3_calls_next {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) {h : Forest.Shape}
    (hs : p.shape = some h) (s s' : Desc.First.S) (rs : List Fmt.RoundView)
    (cols : List (List (ℕ × List UInt64))) (hw : okRoundsE rs = true)
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') (hIn : k3OnIn p s = true) :
    ∃ F', s'.fork? = some F' ∧ F'.next = p.first + Forest.elems h := by
  obtain ⟨F, F', g, -, hn, -, hF', -, -, E⟩ :=
    k3_calls_leaves claim piece laid before p guests hs s s' rs cols hw hd hIn
  exact ⟨F', hF', by rw [E.next, hn]⟩

/-- The same at a piece. -/
theorem k3_calls_lookOut_piece {Cl W : Type} {Fr : Frame} (claim : Aff → Cl) (piece : ℕ)
    (laid : Array Nat) (before : List (ℕ × ℕ)) (pp : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (b : Desc.Block Desc.First.S Cl)
    (hyes : ∀ s rs cols s', b.decide s rs cols = .ok s' →
      (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before pp guests).decide s rs cols =
        .ok s')
    (p : Piece (ckP .two) Fr Desc.First.S Cl W) (hb : p.b = below b) (hback : p.back = [])
    {h : Forest.Shape} (hs : pp.shape = some h) (hdg : pp.digits = false)
    (a a' : Desc.First.S × Fr.E.Str) (τ : Tr (uLT (ckP .two) p.ds))
    (hout : p.ior.red.out a τ = some a') (hIn : k3OnIn pp a.1 = true) :
    k3OnOut pp a'.1 = true := by
  obtain ⟨-, -, hw, cols, hd⟩ := piece_hears_below p b hb hback a τ a' hout
  exact k3_calls_lookOut claim piece laid before pp guests hs hdg a.1 a'.1 _ cols hw
    (hyes _ _ _ _ hd) hIn

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3OnIn_free
#print axioms VerifiableInference.OnPublicFiles.k3_calls_leaves
#print axioms VerifiableInference.OnPublicFiles.k3_calls_next
#print axioms VerifiableInference.OnPublicFiles.k3_calls_lookOut
#print axioms VerifiableInference.OnPublicFiles.k3_calls_lookOut_piece
