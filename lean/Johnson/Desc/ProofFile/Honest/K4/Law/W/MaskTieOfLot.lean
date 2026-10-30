-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/MaskTieOfLot.lean: CONDITIONAL. Three statements
with their proofs; no definition.

What is here. THE TIE ON THE MASK ROW OF THE MEMBER OF THE FEED-FORWARD LAYERS' OWN ROUNDS
(sub-protocol K4), `K4MaskTieAt` (Law/ScriptAt.lean), AS THE END OF A STATEMENT, where the thread
with the library's own values stands. `k4MaskTie_of_ownMsgsG`: from `OwnMsgs` at the three fields of
K4's lot `k4MaskLotG`: the step that stood inside the proof of `k4MaskTie_coinsG`
(Law/W/MaskLotGPub.lean): `k4PubG_of` lays the lot's text open, `k4MaskTie_of_own`
(Law/W/MaskOfOwn.lean) does the rest. `k4MaskTie_of_covers`: from `OwnMsgs` at a lot Ls that covers
K4's (`Covers`, `ownMsgs_of_covers`, Honest/Small/Covers.lean, of other writers).
`k4MaskTie_of_lot`: from the lock J, hn, hA, hE and hL on the sender's lot (`k4Mask_covers`,
Law/W/MaskCovers.lean) and `OwnMsgs` at that lot. Ls IS A LETTER: no kind of sender is named.

Not shown here. THAT ANY SCRIPT MEETS `OwnMsgs` AT ANY LOT; that hn, hA or hE holds of any sender's
text; that J holds of the book over which Q is typed; that the thread stands anywhere: where it
stands at no state all three are empty. WHERE THE BOOK LENDS K4's PLACE NO ROW THE TIE ASKS NOTHING.
The row's last element is not in the tie. The full size and the format's second hash function alone. Each
statement is an equation at the stand's own coins, entry by entry: nothing is said on how an element
of the coins is sampled. The other limits of the three files named hold here too. Nothing on
soundness, on completeness or on any other property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MaskCovers

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no standing table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Rt (k4Takes)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.Sound (MsgT seatTab)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead OwnMsgs MsgLot Covers ownMsgs_of_covers)
open ProofFile.Honest.K4.SeatedHead (LaidK4)
open ProofFile.Honest.K4.Lot (k4MaskLotG k4MaskNum k4PubG)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

variable {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL on h, Lh, hQ, O, hT, hV and hN. **THE TIE ON THE MASK ROW, FROM `OwnMsgs` AT THE
THREE FIELDS OF K4's LOT.** -/
theorem k4MaskTie_of_ownMsgsG {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {cells : Tr → Cells} {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp) {Vq : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ}
    (O : OwnMsgs Q Vq N
      (k4MaskLotG (Bk := Bk) (Rc := Rc) X' cells weights tokens look Zp g).n
      (k4MaskLotG (Bk := Bk) (Rc := Rc) X' cells weights tokens look Zp g).fx
      (k4MaskLotG (Bk := Bk) (Rc := Rc) X' cells weights tokens look Zp g).txt)
    {c : Coins Bk} {s : TS} {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    (hV : Vq mm.st.input) (hN : N ≤ mm.st.heard.length) :
    K4MaskTieAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread cells weights
      tokens look Qp (h.𝔇.N.sent m 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm := by
  have hP := k4PubG_of Lh hQ
  obtain rfl := Lh.seg
  have O' : OwnMsgsForm Q Vq N (maskNumAt Zp (2 * g)) 0
      (k4MaskTxt X' cells weights tokens look Qp (Forest.elems (P5J.At.X Zp).y.fo)) := by
    intro k' w' hd' hv hn mask row place y hy
    refine O k' w' hd' hv hn mask row place y ?_
    show ((k4PubG Zp g).bind fun Qp => Lot.k4MaskTextG X' cells weights tokens look Qp
      (Forest.elems (P5J.At.X Zp).y.fo) k' w' (hd'.take 0) mask row place) = some y
    rw [hP]
    exact hy
  exact k4MaskTie_of_own h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hQ O' hT hV hN

/-- CONDITIONAL on h, Lh, hQ, C, OS, hT, hV and hN. **THE TIE, FROM `OwnMsgs` AT A LOT THAT COVERS
K4's.** Ls: a letter. -/
theorem k4MaskTie_of_covers {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {cells : Tr → Cells} {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp) {Vq : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ}
    {Ls : MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr)}
    (C : Covers Vq N Ls (k4MaskLotG (Bk := Bk) (Rc := Rc) X' cells weights tokens look Zp g))
    (OS : OwnMsgs Q Vq N Ls.n Ls.fx Ls.txt)
    {c : Coins Bk} {s : TS} {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    (hV : Vq mm.st.input) (hN : N ≤ mm.st.heard.length) :
    K4MaskTieAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread cells weights
      tokens look Qp (h.𝔇.N.sent m 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm :=
  k4MaskTie_of_ownMsgsG h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hQ
    (ownMsgs_of_covers C OS) hT hV hN

/-- CONDITIONAL on h, Lh, hQ, J, hn, hA, hE, hL, OS, hT, hV and hN. **THE TIE, FROM THE LOCK, THREE
SENTENCES ON THE SENDER's LOT AND `OwnMsgs` AT THAT LOT.** Ls: a letter. -/
theorem k4MaskTie_of_lot {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {cells : Tr → Cells} {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp) {o : Addr} {base : ℕ}
    (J : K4MaskLockAt Bk Qp (Forest.elems (P5J.At.X Zp).y.fo) o base)
    (Ls : MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr)) (hn : Ls.n = k4MaskNum Zp (2 * g))
    {Vq : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ}
    (hA : ∀ k w (hd : List Fmt.Drawn) ν, Vq w → N ≤ hd.length →
      Forest.elems (P5J.At.X Zp).y.fo ≤ ν →
      ν + 1 < Forest.elems (P5J.At.X Zp).y.fo + k4Takes Qp.P Qp.hp Qp.g →
      (Ls.txt k w (hd.take Ls.fx) true 0 ν).isSome = true)
    {L : ℕ}
    (hE : ∀ k w hd ν y', ν < L → Ls.txt k w hd true 0 ν = some y' →
      (k.look 0 o).2.eAt (base + ν) = .ok y')
    (hL : Forest.elems (P5J.At.X Zp).y.fo + k4Takes Qp.P Qp.hp Qp.g ≤ L + 1)
    (OS : OwnMsgs Q Vq N Ls.n Ls.fx Ls.txt)
    {c : Coins Bk} {s : TS} {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    (hV : Vq mm.st.input) (hN : N ≤ mm.st.heard.length) :
    K4MaskTieAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread cells weights
      tokens look Qp (h.𝔇.N.sent m 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm :=
  k4MaskTie_of_covers h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hQ
    (k4Mask_covers (k4PubG_of Lh hQ) J Ls hn hA hE hL) OS hT hV hN

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4MaskTie_of_ownMsgsG
#print axioms ProofFile.Honest.K4.W.k4MaskTie_of_covers
#print axioms ProofFile.Honest.K4.W.k4MaskTie_of_lot
