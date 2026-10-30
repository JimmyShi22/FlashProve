-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerRowAtField.lean: THE SHARED ROW's LETTERS, BOUND BY "THERE ARE", WITH THE
FACTS OF THE ROW BY MAKE, AT THE FIELD's OWN LIST OF PIECES: so that the ledger's top need not ask
the 37 letters of the row (f · the eight sub-protocols b1 … b8 · the pieces, bases, written rounds,
extractors and error bounds) with equations: they come out of one "obtain" in front of the call.
  row_at_field   at F₀ := fieldF … and TT := atDesc F₀ (piecesAt (ckP .two) F₀ Dw c₁ k₁ c₂ k₂ c₃ k₃
  (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd): from withU Q.S = some sentU · tests.length = 2 ·
  the three chains' sub-protocols by name · F₀.data fileN = .ok Dw · F₀.sealLast: THERE ARE b1 … b8
  with blocks Q = some [b1, …, b8] (hbl) and base d ext err … x11 with (hlf) TT.l₂ = PT :: MM ·
  (htF) Tiled TT.p₂ (PT :: MM), the whole row from the front · (hfr) the first piece's sub-protocol
  declares no round · (hf0) it has no written round · (hr3) x3's sub-protocol declares b3's rounds ·
  (hal) each piece's written rounds are its sub-protocol's declared rounds' data · (ht₁) TT.p₂.base
  = Dw.t₁ · (hps) the pieces hold the seated chain's sub-protocols · (hop) no piece opens a tree
  below Dw.t₁ · (hcap) each piece's error bounds are the cap.
By calls: blocks_eight (BlocksEight.lean) · seat_layer · row_of_cut · letters_of_cut
(LedgerLettersOfCut.lean) · front_of_chain · row_forms_all (LedgerFormsAll.lean). hr1 · hr2 · hr4 ·
hr5 of the numbers' lemma are rfl at PT | pc2 | pc1.
What is not claimed. Anything on the two proximity tests' pieces x9, x10 beyond these. No law is
paid here. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.LedgerByMakeTop
import Johnson.Desc.K14.Law.LedgerLettersOfCut
import Johnson.Desc.K14.Law.BlocksEight

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Cb Johnson.Pack Desc.Plain
open Iop Run OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc (Block Strs Wit FileDescription)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared

theorem row_at_field {σ₁ Cells Tok : Type} (Dw : WholeD) (oH : ProofFile.SecondHashFunctionArgument) (mkL : ProofFile.LinksBy)
    (Zp : ProofFile.Pub) (lt : String) (st₂ : ProofFile.InstPub → St) (en₂ : St → Option
                OnBytes.Proof.SharedEnd) (ok₂ : ProofFile.InstPub → Bool) (fo₂ : Bool) (si₂ : List String) (Bs :
                      ProofFile.SecondSeat) (getS : σ₁ → VerifiableInference.Desc.First.S) (startS : ProofFile.InstPub → σ₁) (cF :
                                  VerifiableInference.Desc.Chain σ₁ ProofFile.Cl) (ch : Model.Verify.Chains) (Q : P14) (tests : List
                                        (Block St Unit)) (sentU : Array OracleNotice) (hUw : withU Q.S = some sentU) (htl : tests.length
                                        = 2)
    (c₁ : Block (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).S₁ (fieldF oH
        mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).Cl) (k₁ : List (Block (fieldF oH
        mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).S₁ (fieldF oH mkL Zp lt st₂ en₂
        ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).Cl))
    (c₂ : Block (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).S₂ (fieldF oH
        mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).Cl) (k₂ : List (Block (fieldF oH
        mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).S₂ (fieldF oH mkL Zp lt st₂ en₂
        ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).Cl))
    (c₃ : Block (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).S₃ (fieldF oH
        mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).Cl) (k₃ : List (Block (fieldF oH
        mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).S₃ (fieldF oH mkL Zp lt st₂ en₂
        ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).Cl))
    (h₁f : (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).first.blocksInOrder = c₁ ::
        k₁) (h₂f : (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q
        tests).shared.blocksInOrder = c₂ :: k₂) (h₃f : (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                 startS cF ch Q tests).second.blocksInOrder = c₃ :: k₃)
    (e₁ : (i : ℕ) → (ds : List RDT) → ((fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch
        Q tests).XiPub × (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).S₁)
        × (frameAt Dw (allOf Dw) Dw.key₁ 0).E.Str → Iop.Tr (uLT (ckP .two) ds) → (Wit Cells Tok
        MsgT) → (Wit Cells Tok MsgT))
    (e₂ : (i : ℕ) → (ds : List RDT) → (((fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
        ch Q tests).XiPub × (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q
        tests).S₁) × (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).S₂) ×
        (frameAt Dw (allOf Dw) Dw.key₂ 0).E.Str → Iop.Tr (uLT (ckP .two) ds) → (Wit Cells Tok MsgT)
        → (Wit Cells Tok MsgT))
    (e₃ : (i : ℕ) → (ds : List RDT) → (((fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
        ch Q tests).XiPub × (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q
        tests).S₁ × (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).S₂) ×
        (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).S₃) × (frameAt Dw
        (allOf Dw) Dw.key₃ (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q
        tests).lastChainFirstTreeNumber).E.Str → Iop.Tr (uLT (ckP .two) ds) → (Wit Cells Tok MsgT) → (Wit Cells
                      Tok MsgT))
    (dW wEnd : (Wit Cells Tok MsgT)) (fileN : String) (hDw : (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂
        si₂ Bs getS startS cF ch Q tests).data fileN = .ok Dw) (hsl : (fieldF oH mkL Zp lt st₂ en₂
        ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).sealLast = true) :
    ∃ (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit), blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8] ∧
    ∃ (base : ℕ) (d : RDT) (ext : ((ProofFile.InstPub × σ₁) × St) × (frameAt Dw (allOf Dw) Dw.key₂
              0).E.Str → Iop.Tr (uLT (ckP .two) [d]) → (Wit Cells Tok MsgT) → (Wit Cells Tok MsgT)) (err :
              Err (uLT (ckP .two) [d])) (base2 : ℕ) (d21 d22 : RDT) (ex2 : ((ProofFile.InstPub × σ₁) × St) ×
              (frameAt Dw (allOf Dw) Dw.key₂ 0).E.Str → Iop.Tr (uLT (ckP .two) [d21, d22]) → (Wit Cells
              Tok MsgT) → (Wit Cells Tok MsgT)) (er2 : Err (uLT (ckP .two) [d21, d22])) (x3 : Piece (ckP
              .two) (frameAt Dw (allOf Dw) Dw.key₂ 0) ((ProofFile.InstPub × σ₁) × St) ProofFile.Cl (Wit Cells Tok
                          MsgT)) (base4 : ℕ) (d4 : RDT) (ex4 : ((ProofFile.InstPub × σ₁) × St) × (frameAt Dw (allOf Dw)
                                Dw.key₂ 0).E.Str → Iop.Tr (uLT (ckP .two) [d4]) → (Wit Cells Tok MsgT) → (Wit Cells Tok
                                MsgT)) (er4 : Err (uLT (ckP .two) [d4])) (base5 : ℕ) (d51 d52 : RDT) (ex5 : ((ProofFile.InstPub ×
                                σ₁) × St) × (frameAt Dw (allOf Dw) Dw.key₂ 0).E.Str → Iop.Tr (uLT (ckP .two) [d51, d52]) →
                                (Wit Cells Tok MsgT) → (Wit Cells Tok MsgT)) (er5 : Err (uLT (ckP .two) [d51, d52])) (x6 :
                                Piece (ckP .two) (frameAt Dw (allOf Dw) Dw.key₂ 0) ((ProofFile.InstPub × σ₁) × St) ProofFile.Cl (Wit
                                            Cells Tok MsgT)) (base7 : ℕ) (d7 : RDT) (ex7 : ((ProofFile.InstPub × σ₁) × St) × (frameAt Dw
                                                  (allOf Dw) Dw.key₂ 0).E.Str → Iop.Tr (uLT (ckP .two) [d7]) → (Wit Cells Tok MsgT) → (Wit
                                                  Cells Tok MsgT)) (er7 : Err (uLT (ckP .two) [d7])) (x8 x9 x10 x11 : Piece (ckP .two)
                                                  (frameAt Dw (allOf Dw) Dw.key₂ 0) ((ProofFile.InstPub × σ₁) × St) ProofFile.Cl (Wit Cells Tok MsgT)),
      (atDesc (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) (piecesAt (ckP
          .two) (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) Dw c₁ k₁ c₂
          k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).l₂ = seatedPiece (W := (Wit
          Cells Tok MsgT)) (Cl' := ProofFile.Cl) (F := (frameAt Dw (allOf Dw) Dw.key₂ 0)) (P₁ :=
                (ProofFile.InstPub × σ₁)) b1 base d ext err :: [pc2 (b2.retype (Cl' := ProofFile.Cl)) base2 d21 d22
                      ex2 er2, x3, pc1 (b4.retype (Cl' := ProofFile.Cl)) base4 d4 ex4 er4, pc2 (b5.retype (Cl' :=
                            ProofFile.Cl)) base5 d51 d52 ex5 er5, x6, pc1 (b7.retype (Cl' := ProofFile.Cl)) base7 d7 ex7 er7, x8,
                      x9, x10, x11] ∧
      Tiled (atDesc (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) (piecesAt
          (ckP .two) (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) Dw c₁ k₁
          c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).p₂ (seatedPiece (W := (Wit
          Cells Tok MsgT)) (Cl' := ProofFile.Cl) (F := (frameAt Dw (allOf Dw) Dw.key₂ 0)) (P₁ :=
                (ProofFile.InstPub × σ₁)) b1 base d ext err :: [pc2 (b2.retype (Cl' := ProofFile.Cl)) base2 d21 d22
                      ex2 er2, x3, pc1 (b4.retype (Cl' := ProofFile.Cl)) base4 d4 ex4 er4, pc2 (b5.retype (Cl' :=
                            ProofFile.Cl)) base5 d51 d52 ex5 er5, x6, pc1 (b7.retype (Cl' := ProofFile.Cl)) base7 d7 ex7 er7, x8,
                      x9, x10, x11]) ∧
      (atDesc (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) (piecesAt (ckP
          .two) (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) Dw c₁ k₁ c₂
          k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).p₂.b.rounds = [] ∧ (atDesc
          (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) (piecesAt (ckP
          .two) (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) Dw c₁ k₁ c₂
          k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).p₂.ds = [] ∧ x3.b.rounds =
          b3.rounds ∧
      (∀ p ∈ (atDesc (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests)
          (piecesAt (ckP .two) (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q
          tests) Dw c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).p₂ ::
          seatedPiece (W := (Wit Cells Tok MsgT)) (Cl' := ProofFile.Cl) (F := (frameAt Dw (allOf Dw)
                Dw.key₂ 0)) (P₁ := (ProofFile.InstPub × σ₁)) b1 base d ext err :: [pc2 (b2.retype (Cl' :=
                      ProofFile.Cl)) base2 d21 d22 ex2 er2, x3, pc1 (b4.retype (Cl' := ProofFile.Cl)) base4 d4 ex4 er4, pc2
                      (b5.retype (Cl' := ProofFile.Cl)) base5 d51 d52 ex5 er5, x6, pc1 (b7.retype (Cl' := ProofFile.Cl))
                      base7 d7 ex7 er7, x8, x9, x10, x11], Along (RoundIs (VerifiableInference.Desc.numAt Dw.t₁
                      Dw.t₂ 1)) p.b.rounds p.ds) ∧
      (atDesc (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) (piecesAt (ckP
          .two) (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) Dw c₁ k₁ c₂
          k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).p₂.base = Dw.t₁ ∧
      ((atDesc (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) (piecesAt (ckP
          .two) (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) Dw c₁ k₁ c₂
          k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).p₂ :: seatedPiece (W := (Wit
          Cells Tok MsgT)) (Cl' := ProofFile.Cl) (F := (frameAt Dw (allOf Dw) Dw.key₂ 0)) (P₁ :=
                (ProofFile.InstPub × σ₁)) b1 base d ext err :: [pc2 (b2.retype (Cl' := ProofFile.Cl)) base2 d21 d22
                      ex2 er2, x3, pc1 (b4.retype (Cl' := ProofFile.Cl)) base4 d4 ex4 er4, pc2 (b5.retype (Cl' :=
                            ProofFile.Cl)) base5 d51 d52 ex5 er5, x6, pc1 (b7.retype (Cl' := ProofFile.Cl)) base7 d7 ex7 er7, x8,
                      x9, x10, x11]).map (·.b) = (((chainOf ch Q tests
                      VerifiableInference.Desc.K12.Seat.last).retype (Cl' := ProofFile.Cl)).blocksInOrder.map below).map
          (Block.lift Prod.snd fun t s => (t.1, s)) ∧
      (∀ x ∈ (atDesc (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests)
          (piecesAt (ckP .two) (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q
          tests) Dw c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).p₂ ::
          seatedPiece (W := (Wit Cells Tok MsgT)) (Cl' := ProofFile.Cl) (F := (frameAt Dw (allOf Dw)
                Dw.key₂ 0)) (P₁ := (ProofFile.InstPub × σ₁)) b1 base d ext err :: [pc2 (b2.retype (Cl' :=
                      ProofFile.Cl)) base2 d21 d22 ex2 er2, x3, pc1 (b4.retype (Cl' := ProofFile.Cl)) base4 d4 ex4 er4, pc2
                      (b5.retype (Cl' := ProofFile.Cl)) base5 d51 d52 ex5 er5, x6, pc1 (b7.retype (Cl' := ProofFile.Cl))
                      base7 d7 ex7 er7, x8, x9, x10, x11], ∀ d₀ ∈ x.ds, ∀ j ∈ d₀.opens, Dw.t₁ ≤ j) ∧
      EachCapped 128 ((atDesc (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests)
          (piecesAt (ckP .two) (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q
          tests) Dw c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).p₂ ::
          seatedPiece (W := (Wit Cells Tok MsgT)) (Cl' := ProofFile.Cl) (F := (frameAt Dw (allOf Dw)
                Dw.key₂ 0)) (P₁ := (ProofFile.InstPub × σ₁)) b1 base d ext err :: [pc2 (b2.retype (Cl' :=
                      ProofFile.Cl)) base2 d21 d22 ex2 er2, x3, pc1 (b4.retype (Cl' := ProofFile.Cl)) base4 d4 ex4 er4, pc2
                      (b5.retype (Cl' := ProofFile.Cl)) base5 d51 d52 ex5 er5, x6, pc1 (b7.retype (Cl' := ProofFile.Cl))
                      base7 d7 ex7 er7, x8, x9, x10, x11]) := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hbl⟩ := blocks_eight Q sentU hUw
  obtain ⟨g₁, g₂, g₃, hcut, hcp, hrow⟩ := seat_layer (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs
      getS startS cF ch Q tests) Dw (ckP .two) c₁ k₁ c₂ k₂ c₃ k₃ h₁f h₂f h₃f e₁ e₂ e₃ dW wEnd
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := row_of_cut (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
      startS cF ch Q tests) fileN Dw hDw hsl (atDesc (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs
      getS startS cF ch Q tests) (piecesAt (ckP .two) (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs
      getS startS cF ch Q tests) Dw c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW
      wEnd)) (VerifiableInference.Desc.Sound.held c₁) (k₁.map VerifiableInference.Desc.Sound.held)
      (VerifiableInference.Desc.Sound.held c₂) (k₂.map VerifiableInference.Desc.Sound.held)
      (VerifiableInference.Desc.Sound.held c₃) (k₃.map VerifiableInference.Desc.Sound.held) (restCap
      e₁) (restCap e₂) (restCap e₃) sealRound g₁ g₂ g₃ hcut hcp
  obtain ⟨base, d, ext, err, base2, d21, d22, ex2, er2, x3, base4, d4, ex4, er4, base5, d51, d52,
      ex5, er5, x6, base7, d7, ex7, er7, x8, x9, x10, x11, hlf⟩ := letters_of_cut (fieldF oH mkL Zp
      lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) fileN Dw (atDesc (fieldF oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) (piecesAt (ckP .two) (fieldF oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) Dw c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂)
      (restCap e₃) dW wEnd)) ch Q b1 b2 b3 b4 b5 b6 b7 b8 tests
      VerifiableInference.Desc.K12.Seat.last hbl htl hDw hsl (VerifiableInference.Desc.Sound.held
      c₁) (k₁.map VerifiableInference.Desc.Sound.held) (VerifiableInference.Desc.Sound.held c₂)
      (k₂.map VerifiableInference.Desc.Sound.held) (VerifiableInference.Desc.Sound.held c₃) (k₃.map
      VerifiableInference.Desc.Sound.held) (restCap e₁) (restCap e₂) (restCap e₃) sealRound g₁ g₂ g₃
      hcut hcp hrow
  rw [hlf] at q1 q2 q3 q4 q5
  have hps : ((atDesc (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests)
      (piecesAt (ckP .two) (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) Dw
      c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).p₂ :: seatedPiece (W :=
      (Wit Cells Tok MsgT)) (Cl' := ProofFile.Cl) (F := (frameAt Dw (allOf Dw) Dw.key₂ 0)) (P₁ :=
            (ProofFile.InstPub × σ₁)) b1 base d ext err :: [pc2 (b2.retype (Cl' := ProofFile.Cl)) base2 d21 d22 ex2
                  er2, x3, pc1 (b4.retype (Cl' := ProofFile.Cl)) base4 d4 ex4 er4, pc2 (b5.retype (Cl' := ProofFile.Cl))
                  base5 d51 d52 ex5 er5, x6, pc1 (b7.retype (Cl' := ProofFile.Cl)) base7 d7 ex7 er7, x8, x9, x10,
                  x11]).map (·.b) = (((chainOf ch Q tests VerifiableInference.Desc.K12.Seat.last).retype (Cl' :=
                  ProofFile.Cl)).blocksInOrder.map below).map (Block.lift Prod.snd fun t s => (t.1, s)) := q1.trans hrow
  obtain ⟨fb, restB, hflat, hokF, hrF⟩ := front_of_chain (Cl := ProofFile.Cl) ch Q tests
      VerifiableInference.Desc.K12.Seat.last
  have hbk : (atDesc (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests)
      (piecesAt (ckP .two) (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) Dw
      c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).p₂.b = (below fb).lift
      Prod.snd fun (t : (ProofFile.InstPub × σ₁) × St) (s : St) => (t.1, s) := by
    have h' := hps
    rw [hflat] at h'
    exact Option.some.inj (congrArg List.head? h')
  have hfr : (atDesc (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests)
      (piecesAt (ckP .two) (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) Dw
      c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).p₂.b.rounds = [] := by
    rw [hbk]
    exact hrF
  have hf0 : (atDesc (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests)
      (piecesAt (ckP .two) (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) Dw
      c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).p₂.ds = [] := by
    have ho := q2.1.1
    rw [hfr] at ho
    exact List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_add_eq_zero_right ho)
  obtain ⟨t9, t10, -, ⟨-, hx3, -⟩, -⟩ := row_forms_all ch Q b1 b2 b3 b4 b5 b6 b7 b8 tests
      VerifiableInference.Desc.K12.Seat.last hbl (atDesc (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs
      getS startS cF ch Q tests) (piecesAt (ckP .two) (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs
      getS startS cF ch Q tests) Dw c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW
      wEnd)).p₂ _ _ x3 _ _ x6 _ x8 x9 x10 x11 hps q2
  have hr3 : x3.b.rounds = b3.rounds := by
    rw [hx3]
    rfl
  exact ⟨b1, b2, b3, b4, b5, b6, b7, b8, hbl, base, d, ext, err, base2, d21, d22, ex2, er2, x3,
      base4, d4, ex4, er4, base5, d51, d52, ex5, er5, x6, base7, d7, ex7, er7, x8, x9, x10, x11,
      hlf, q2, hfr, hf0, hr3, q5, q6, hps, q3, q4⟩

end Desc.K14.Law
