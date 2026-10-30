-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.P5J.RowsAtAll
import Johnson.Loose.H2K12.TieAt354
import Johnson.Loose.H2K12.PlacesAtMg
/-
Johnson/Loose/H2K12/K12KindAtMg.lean:
THE LAW OF THE PROXIMITY TEST (the kind K12) ON THE PROOF FILE's FIRST CHAIN, IN
THE FORM IN WHICH A KIND's LAW IS COUNTED: AtMgA.Kind h 𝔏 K12 (Johnson/P5J/RowsAtAll.lean):
KindTiedR at the closed meaning mgAtAll h, at the table's own extractor, at the first chain's
own pieces, with "reached" and "the public part is a typed instance's" in hand. A joining:
k12_kind_of (H2K12/TieAt354.lean) called at the composed meaning's letters. Of K12's files on
the kind, this one and H2K12/PlacesAtMg.lean alone stand over the files in Johnson/P5J/.
  f0t_is_descN     the seated description's own term, as the files in Johnson/P5J/ spell it (F0T,
                   Johnson/P5J/AtTerm.lean), is K12's files' spelling descN at
                   the plain road's links and the parts guardedProximityTestParts: by unfolding
  Owed354          Owed354 h 𝔏 mem rdN: WHAT IS LEFT: at the piece q at number 354 of h's row, with
                   Seat354 in hand: T2At, T4aAt, T4bAt, T5At (H2K12/Frame354.lean) at the composed
                   meaning's letters
  k12_kind_at_mg   the head AtMgA at the format's second hash function, the first flat list's head,
                   Owed354: then LastTypedAt → h.Kind 𝔏 K12. That the flat list's places are the
                   written list is paid by places_at_mg (H2K12/PlacesAtMg.lean)
WHAT IT IS NOT. IT PAYS NO LAW. Owed354 holds all the content and it is not paid; whether it can
be met is shown nowhere; where it is false the end says nothing. Whether AtMgA can be met at the
release's own files is not shown in Lean. The full size alone.
No soundness statement. Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K12

open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Slice KObj
open _root_.Run (ckP)
open VerifiableInference.Desc (KindName)
open VerifiableInference.Desc.Sound
open P5J (AtMgA mgAtAll F0T TS Free fullLinks)

/-- The seated description's own term is K12's files' spelling of it. -/
theorem f0t_is_descN (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) (N : H2U.Places4)
    (c : VerifiableInference.Desc.Chain TS ProofFile.Cl) :
    F0T o Z N c = FN o Z N c := rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **What is left of the kind's law at the counted letters.** -/
def Owed354 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (mem : ProofFile.InstPub × VerifiableInference.Desc.First.S → ℕ → Option Mem) (rdN : ℕ → ℕ) : Prop :=
  ∀ q : Piece (ckP .two)
      (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
      (ProofFile.InstPub × VerifiableInference.Desc.First.S) ProofFile.Cl
      (VerifiableInference.Desc.Wit (P5J.CellsM numsFull) P5J.At.Tok MsgT),
    (h.toAtMg.row 𝔏)[354]? = some q → Seat354 Zp Np (D.at frS.P.T.a) q →
    T2At (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
      (P5J.At.N Zp cF) (mgAtAll h) fullLinks P5J.At.ps h.toAtMg.rch 354 q ∧
    T4aAt (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
      (P5J.At.N Zp cF) (mgAtAll h) fullLinks P5J.At.ps h.toAtMg.rch 354 q
      (R354 (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
        (H2K.JointK.pL Np) (no354 Np) (fun s => H2K.Member.rLFull s.st) rdN)
      (fun a => Tuple354 h.𝔇.cs h.𝔇.G h.𝔇.smp (mem a.1) a.1
        (strsOf (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
          a.2)) ∧
    T4bAt (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
      (P5J.At.N Zp cF) (mgAtAll h) fullLinks P5J.At.ps h.toAtMg.rch 354 q
      (h.toAtMg.ex 𝔏 354)
      (fun a => Tuple354 h.𝔇.cs h.𝔇.G h.𝔇.smp (mem a.1) a.1
        (strsOf (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
          a.2)) ∧
    T5At (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
      (P5J.At.N Zp cF) (mgAtAll h) fullLinks P5J.At.ps h.toAtMg.rch 354 q (h.toAtMg.ex 𝔏 354)

set_option maxHeartbeats 4000000 in
/-- **THE KIND's LAW IN THE COUNTED FORM, FROM WHAT IS LEFT.** -/
theorem k12_kind_at_mg (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (mem : ProofFile.InstPub × VerifiableInference.Desc.First.S → ℕ → Option Mem) (rdN : ℕ → ℕ)
    (owed : Owed354 h 𝔏 mem rdN) :
    LastTypedAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL → h.Kind 𝔏 KindName.K12 := fun hT =>
  k12_kind_of (o := OnBytes.secondHashFunction) (S := Z) (Z := Zp) (N := Np) (c := cF)
    (D := D.at frS.P.T.a) (ps := P5J.At.ps) h.scope h.laid.pub h.laid.places h.laid.value
    h.laid.planOk (LPFD.asks_written h.laid.asks)
    (by rw [P5J.LaidAt.atDepth h.scope h.laid]; exact h.laid.data) k12AllB_full
    (places_at_mg h.toAtMg)
    𝔏.c₁ 𝔏.k₁ 𝔏.c₂ 𝔏.k₂ 𝔏.c₃ 𝔏.k₃ 𝔏.e₁ 𝔏.e₂ 𝔏.e₃ 𝔏.dW 𝔏.wEnd q₁
    (P5J.At.N Zp cF) (mgAtAll h) fullLinks h.toAtMg.rch (h.toAtMg.ex 𝔏) h.𝔇.decT rfl
    (fun y a a' e => by
      obtain ⟨z, s⟩ := a
      obtain ⟨z', s'⟩ := a'
      obtain rfl : z' = z := e
      first
        | rfl
        | exact P5J.At.noRec_decT _ _ _ _ _ _)
    h.𝔇.cs h.𝔇.G h.𝔇.smp mem rdN owed hT

end H2K12

#print axioms H2K12.f0t_is_descN
#print axioms H2K12.k12_kind_at_mg
