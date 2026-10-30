-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstTop.lean: THE JOIN's FRAME: FROM THE LEDGER's TOP's END TO K14's LAW
ON THE SHARED CHAIN AT THE CONSTANT (Sh.Law, Johnson/Desc/K14/Law/SharedConstLedger.lean), AT ANY
ROW OF PIECES THAT HOLD THE CHAIN's SUB-PROTOCOLS IN THE WRAP. The top ends at the promise without
the tests for the last chain's door, the three shapes written as K1 reads them, and its keys at a
number t. Sh.law_of_ledger asks hXD: each piece's accepting step hands the door's tests on. HERE hXD
is had from one step of the walk of Sh.X (Sh.X_step), so that nothing is asked of the pieces but
which sub-protocol each holds.

  Sh.parts_of_on  inside the constant's promise: XK (the shapes as K1 reads them) and "the book
                  fits".
  Sh.xd_of_steps  **hXD**, where each piece's accepting step is an accepting step of the
                  sub-protocol at its number in the wrapped list (hq: by held_at and
                  piece_step_below, from the row's being cut off the IOP as written in Lean).
  Sh.law_of_top   **the join**: the top's end, in its own spelling, gives Sh.Law.
What is not claimed. No law of its own. No soundness; no level.

-/
import Johnson.Desc.K14.Law.SharedConstReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack
open _root_.Run.PQ (CK)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Strs Wit FileDescription First.S Grows)
open VerifiableInference.Desc.ChainEnd (untestedL Exact)
open VerifiableInference.Desc.K1 (sendPiece sampledAt shapeAt shapesOf condPort errPort seedEntry
  seedMaps)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets openSets start)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu Seat.onGomega)
open VerifiableInference.Desc.K12.Coin
open Desc.K14.Law.Fence
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0 PayPub)
open H2K.First (batOneOk)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf wSitsItem wSitsMore)
open VerifiableInference.Desc.Third (P₁₄)
open Johnson.Desc.First.Walk.Tied (StepYes)

namespace Sh

variable {Xi P₀ P₁ Cl Cells Tok : Type} {Fr : Frame} (A : ShPlan Xi)
  (O : ShOpen P₀ P₁ Cells Tok A.Q)
  (hUw : withU A.Q.S = some (sentU A)) (hS : A.Q.S.sharedSplitNeeded = true)

/-- Inside the constant's promise: XK, the shapes as K1 reads them, and "the book fits". -/
theorem parts_of_on (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (l : List (Piece
    (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))) (k : ℕ) (a : (P₁ × St) × Fr.E.Str)
    (ha : onQ₂ (nums A O) (pm A O) (own A O) true f l k a) :
    XK A.Q (sentU A) (layU A) (layO A) (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU A)).1
        hUw⟩, shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩, shapeAt (parO A.Q) ⟨1, (places A.Q
        (sentU A)).2.2 hS⟩, smpK A.Q.codes (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU
        A)).1 hUw⟩) (shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩) (shapeAt (parO A.Q) ⟨1,
        (places A.Q (sentU A)).2.2 hS⟩) (sentU A).size) (sentU A).size k a.1.2 = true ∧ fitsX k
        a.1.2 = true := by
  obtain ⟨e1, e2, e3⟩ := shapes_are A hUw hS
  refine ⟨?_, ((XD_iff A.p k _).1 (XD_of_on A O f l k a ha)).1⟩
  rw [e1, e2, e3]
  exact XK_of_on A O f l k a ha

variable (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
  (hbl : blocks A.Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
  (hlU : layTrees A.Q.codes (sentU A) = some (layU A))
  (hlO : layTrees A.Q.codes (withOmega A.Q.S) = some (layO A))
  (hm : A.Q.par.S.masksAhead = true)
  (hp : ∀ b ∈ [b1, b2, b3, b4, b5, b6, b7, b8], b.planOk = true)
  (hok : A.Q.S.ok = true)
  (hC2 : condPort (parU A.Q (sentU A)) A.rad2 = true) (hC5 : condPort (parO A.Q) A.rad5 = true)
  (pyU : PlanY A.Q.codes A.Q.S.fold.u) (pyO : PlanY A.Q.codes A.Q.S.omega)
  (pyS : PlanY A.Q.codes A.Q.S.sharedSplit)
  (πA πB : P12) (heA : πA.early = true) (ha1A : πA.answers = 1)
  (hftA : πA.nums.firstTree = A.Q.par.toGPar.firstTree)
  (heB : πB.early = true) (ha1B : πB.answers = 1)
  (hftB : πB.nums.firstTree = A.Q.par.toGPar.firstTree)
  (hl : A.Q.codes.lengthsOk = true) (hsU : (sentU A).size = 2)

include hUw hS hbl hlU hlO hm hp hok hC2 hC5 pyU pyO pyS heA ha1A hftA heB ha1B hftB hl hsU in
/-- **hXD, from the pieces' steps.** -/
theorem xd_of_steps (bs : List (Block St Cl))
    (h0 : ∀ b, bs[0]? = some b → ∀ s rs gs s', b.decide s rs gs = .ok s' →
      ∃ c : Model.Verify.Chains, (frontBlock c).decide s rs gs = .ok s')
    (h8 : ∀ i b, i < 8 → bs[i + 1]? = some b → ∃ (c : Block St Cl) (b' : Block St Unit),
      [b1, b2, b3, b4, b5, b6, b7, b8][i]? = some b' ∧ b = below c ∧ DecidesAs c b' ∧
        c.rounds = b'.rounds)
    (h9 : ∀ b, bs[9]? = some b → ∀ s rs gs s', b.decide s rs gs = .ok s' →
      (Seat.onGu (proximityTestKind guardedProximityTestParts πA : Block T12 Unit)).decide s rs gs = .ok s')
    (h10 : ∀ b, bs[10]? = some b → ∀ s rs gs s', b.decide s rs gs = .ok s' →
      (Seat.onGomega (proximityTestKind guardedProximityTestParts πB : Block T12 Unit)).decide s rs gs = .ok s')
    (h11 : ∀ b, bs[11]? = some b → ∀ s rs gs s', b.decide s rs gs = .ok s' → s' = s)
    (hlen : bs.length = 12) (hpS : A.p.S.omega = A.Q.S.omega)
    (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (l : List (Piece (ckP .two) Fr (P₁ ×
        St) Cl (Wit Cells Tok MsgT)))
    (hq : ∀ (i : ℕ) (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)), (f :: l)[i]? = some
        x → ∃
        B, bs[i]? = some B ∧ ∀ (a : (P₁ × St) × Fr.E.Str) (τ : Iop.Tr (uLT (ckP .two) x.ds)) (b :
        (P₁ × St) × Fr.E.Str), x.ior.red.out a τ = some b → StepYes Fr.ft B a.1.2 b.1.2) :
    ∀ i x, (f :: l)[i]? = some x → ∀ a τ b,
      onQ₂ (nums A O) (pm A O) (own A O) true f l i a → x.ior.red.out a τ = some b →
      XD A.p (i + 1) b.1.2 = true := by
  intro i x hx a τ b ha hout
  obtain ⟨B, hB, hy⟩ := hq i x hx
  obtain ⟨k1, k2⟩ := X_step A hUw hS b1 b2 b3 b4 b5 b6 b7 b8 hbl hlU hlO hm hp hok hC2 hC5 pyU pyO
      pyS
    πA πB heA ha1A hftA heB ha1B hftB hl hsU bs h0 h8 h9 h10 h11 hlen Fr.ft i B a.1.2 b.1.2 hB
    (hy a τ b hout) (parts_of_on A O hUw hS f l i a ha)
  have hX := X_of_parts A hUw hS hlO pyO hpS (i + 1) b.1.2 k1 k2
  rw [← X_is A hUw hS] at hX
  exact ((XW_iff A.Q (sentU A) (layU A) (layO A) _ _ A.p (i + 1) _).1 hX).2

/-- **THE JOIN.** L: the top's end, in its own spelling. -/
theorem law_of_top (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (l : List (Piece (ckP
    .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))) (slots t : ℕ) (ht : t = (nums A O).lo)
    (hXD : ∀ i x, (f :: l)[i]? = some x → ∀ a τ b,
      onQ₂ (nums A O) (pm A O) (own A O) true f l i a → x.ior.red.out a τ = some b →
      XD A.p (i + 1) b.1.2 = true)
    (L : EachLawsBN (keyAt Prod.snd t f l)
      (onQ₂ (nums A O) (pmK A.Q.codes A.G (smp₂ A) (ms A) (decT₂ A O) (shiftBook (nums A O).lo) (pm₀
          A O) A.Q.S.fold.columns 0 (sentU A).size A.Q (XK A.Q (sentU A) (layU A) (layO A) (shapeAt
          (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU A)).1 hUw⟩, shapeAt (parO A.Q) ⟨0, (places A.Q
          (sentU A)).2.1⟩, shapeAt (parO A.Q) ⟨1, (places A.Q (sentU A)).2.2 hS⟩, smpK A.Q.codes
          (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU A)).1 hUw⟩) (shapeAt (parO A.Q) ⟨0,
          (places A.Q (sentU A)).2.1⟩) (shapeAt (parO A.Q) ⟨1, (places A.Q (sentU A)).2.2 hS⟩)
          (sentU A).size) (sentU A).size)) (own A O) true f l)
      (stepAt (nums A O) (mg A O) (pmK A.Q.codes A.G (smp₂ A) (ms A) (decT₂ A O) (shiftBook (nums A
          O).lo) (pm₀ A O) A.Q.S.fold.columns 0 (sentU A).size A.Q (XK A.Q (sentU A) (layU A) (layO
          A) (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU A)).1 hUw⟩, shapeAt (parO A.Q) ⟨0,
          (places A.Q (sentU A)).2.1⟩, shapeAt (parO A.Q) ⟨1, (places A.Q (sentU A)).2.2 hS⟩, smpK
          A.Q.codes (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU A)).1 hUw⟩) (shapeAt (parO
          A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩) (shapeAt (parO A.Q) ⟨1, (places A.Q (sentU A)).2.2
          hS⟩) (sentU A).size) (sentU A).size)) (own A O) true f l
        (extOf (nums A O) f l (ex A O Fr))) slots 0 (f :: l)) : Law A O f l slots := by
  subst ht
  rw [pmXK_is A O hUw hS] at L
  exact law_of_ledger A O f l slots hXD L

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.parts_of_on
#print axioms Desc.K14.Law.Sh.xd_of_steps
#print axioms Desc.K14.Law.Sh.law_of_top
