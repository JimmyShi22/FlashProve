-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerRowTiesAtField.lean: row_at_field's NEIGHBOUR: THE FIVE TIES OF THE
LEDGER (hdW · t2 · t4 · t5 · t7: the written rounds of the pieces at places 1, 2, 4, 5, 7 of the
shared row have the entries and kinds of the written list of the full proof file) AT THE LETTERS
THAT COME BY MAKE: no letter of the row is asked.
  row_ties_at_field   row_at_field (Johnson/Desc/K14/Law/LedgerRowAtField.lean) WITH EIGHT CLAUSES
  MORE under the same "there are": (hrowD) the row's written rounds in a row ARE the data's second
  chain's · x3.ds = [] · x6.ds = [] · hdW · t2 · t4 · t5 · t7 at Wr := dryProofFull.2.1.
IN   the scope: VerifierAndGoals.InScope Zs = true · LPFD.Full.proofDataAndDecisionOfPublicFiles oL Zs.pol Zs.lay Zs.KL = .ok (Dw, rP):
the data Dw are the full proof file's.
By calls: row_at_field · paidAtDesc (its Fits.data₂) · x3_no_data | x6_no_data
(LedgerNoData.lean) · tiesJoin (LedgerTiesJoin.lean).
What is not claimed. That the field's description's data (hDw) and the scope's (hlaid) come from one
file: both are asked, at one letter Dw. No law is paid here. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.LedgerRowAtField
import Johnson.Desc.K14.Law.LedgerTiesJoin
import Johnson.Desc.K14.Law.LedgerNoData

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Cb Johnson.Pack Desc.Plain
open Iop Run OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc (Block Strs Wit FileDescription)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared

theorem row_ties_at_field {σ₁ Cells Tok : Type} (Dw : WholeD) (oH : ProofFile.SecondHashFunctionArgument) (mkL :
          ProofFile.LinksBy) (Zp : ProofFile.Pub) (lt : String) (st₂ : ProofFile.InstPub → St) (en₂ : St → Option
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
        ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).sealLast = true) (oL : ProofFile.SecondHashFunctionArgument) (Zs :
              VerifierAndGoals.PublicFiles) (rP : LPFD.Full.RunPF) (hZs : VerifierAndGoals.InScope Zs = true) (hlaid :
                      LPFD.Full.proofDataAndDecisionOfPublicFiles oL Zs.pol Zs.lay Zs.KL = .ok (Dw, rP)) :
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
                      base7 d7 ex7 er7, x8, x9, x10, x11]) ∧
      rowData (atDesc (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests)
          (piecesAt (ckP .two) (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q
          tests) Dw c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).p₂
          (seatedPiece (W := (Wit Cells Tok MsgT)) (Cl' := ProofFile.Cl) (F := (frameAt Dw (allOf Dw)
                Dw.key₂ 0)) (P₁ := (ProofFile.InstPub × σ₁)) b1 base d ext err :: [pc2 (b2.retype (Cl' :=
                      ProofFile.Cl)) base2 d21 d22 ex2 er2, x3, pc1 (b4.retype (Cl' := ProofFile.Cl)) base4 d4 ex4 er4, pc2
                      (b5.retype (Cl' := ProofFile.Cl)) base5 d51 d52 ex5 er5, x6, pc1 (b7.retype (Cl' := ProofFile.Cl))
                      base7 d7 ex7 er7, x8, x9, x10, x11]) = Dw.ds₂ ∧ x3.ds = [] ∧ x6.ds = [] ∧
      atW Johnson.G.dryProofFull.2.1 0 = some (d.entry, d.kind) ∧ Ties Johnson.G.dryProofFull.2.1 2
          [d21, d22] ∧ Ties Johnson.G.dryProofFull.2.1 4 [d4] ∧ Ties Johnson.G.dryProofFull.2.1 5
          [d51, d52] ∧ Ties Johnson.G.dryProofFull.2.1 7 [d7] := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hbl, base, d, ext, err, base2, d21, d22, ex2, er2, x3,
      base4, d4, ex4, er4, base5, d51, d52, ex5, er5, x6, base7, d7, ex7, er7, x8, x9, x10, x11,
      hlf, htF, hfr, hf0, hr3, hal, hbase, hps, hopA, hcap⟩ := row_at_field Dw oH mkL Zp lt st₂ en₂
      ok₂ fo₂ si₂ Bs getS startS cF ch Q tests sentU hUw htl c₁ k₁ c₂ k₂ c₃ k₃ h₁f h₂f h₃f e₁ e₂ e₃
      dW wEnd fileN hDw hsl
  have hrowD : rowData (atDesc (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q
      tests) (piecesAt (ckP .two) (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q
      tests) Dw c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).p₂ (seatedPiece
      (W := (Wit Cells Tok MsgT)) (Cl' := ProofFile.Cl) (F := (frameAt Dw (allOf Dw) Dw.key₂ 0)) (P₁ :=
            (ProofFile.InstPub × σ₁)) b1 base d ext err :: [pc2 (b2.retype (Cl' := ProofFile.Cl)) base2 d21 d22 ex2
                  er2, x3, pc1 (b4.retype (Cl' := ProofFile.Cl)) base4 d4 ex4 er4, pc2 (b5.retype (Cl' := ProofFile.Cl))
                  base5 d51 d52 ex5 er5, x6, pc1 (b7.retype (Cl' := ProofFile.Cl)) base7 d7 ex7 er7, x8, x9, x10,
                  x11]) = Dw.ds₂ := by
    have hd₂ := (paidAtDesc _ _ (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q
        tests) fileN Dw hDw hsl (ckP .two) c₁ k₁ c₂ k₂ c₃ k₃ h₁f h₂f h₃f (restCap e₁) (restCap e₂)
        (restCap e₃) dW wEnd).2.1.data₂
    rw [hlf] at hd₂
    exact hd₂
  have T2 := htF.2.2.2.2.2.2.2.2
  have h3 : x3.ds = [] := x3_no_data Q b1 b2 b3 b4 b5 b6 b7 b8 hbl base d ext err (atDesc (fieldF oH
      mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) (piecesAt (ckP .two) (fieldF oH
      mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) Dw c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁)
      (restCap e₂) (restCap e₃) dW wEnd)).p₂ x3 x6 x8 x9 x10 x11 base2 d21 d22 ex2 er2 base4 d4 ex4
      er4 base5 d51 d52 ex5 er5 base7 d7 ex7 er7 T2 ch tests VerifiableInference.Desc.K12.Seat.last
      hps
  have h6 : x6.ds = [] := x6_no_data Q b1 b2 b3 b4 b5 b6 b7 b8 hbl base d ext err (atDesc (fieldF oH
      mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) (piecesAt (ckP .two) (fieldF oH
      mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) Dw c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁)
      (restCap e₂) (restCap e₃) dW wEnd)).p₂ x3 x6 x8 x9 x10 x11 base2 d21 d22 ex2 er2 base4 d4 ex4
      er4 base5 d51 d52 ex5 er5 base7 d7 ex7 er7 T2 ch tests VerifiableInference.Desc.K12.Seat.last
      hps
  obtain ⟨k0, k2, k4, k5, k7⟩ := tiesJoin oL Zs Dw rP hZs hlaid (ckP .two) _ _ _ _ (atDesc (fieldF
      oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) (piecesAt (ckP .two) (fieldF oH
      mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) Dw c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁)
      (restCap e₂) (restCap e₃) dW wEnd)).p₂ _ _ x3 _ _ x6 _ [x8, x9, x10, x11] d d21 d22 d4 d51 d52
      d7 hrowD hf0 rfl rfl h3 rfl rfl h6 rfl
  exact ⟨b1, b2, b3, b4, b5, b6, b7, b8, hbl, base, d, ext, err, base2, d21, d22, ex2, er2, x3,
      base4, d4, ex4, er4, base5, d51, d52, ex5, er5, x6, base7, d7, ex7, er7, x8, x9, x10, x11,
      hlf, htF, hfr, hf0, hr3, hal, hbase, hps, hopA, hcap, hrowD, h3, h6, k0, k2, k4, k5, k7⟩

end Desc.K14.Law
