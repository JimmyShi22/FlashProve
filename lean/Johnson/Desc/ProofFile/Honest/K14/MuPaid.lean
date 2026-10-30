-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/MuPaid.lean: kind K14: ONE OF THE FOUR PREMISES ON WHAT A MEMBER's
OWN PLAY SHOWS FOLLOWS FROM OTHER PREMISES: ShowsMu (Honest/K14/Exchange2.lean): the scalar that
"SPLIT" is shown is the honest tables' scalar. Statements with their proofs.

The part at "SPLIT" (Honest/K14/Parts.lean: splitPart) sends one element, which
Honest/K14/Debts.lean names as a term (split_moved: scalarAt, defined in Honest/K14/PartsFit.lean).
The thread says which challenges have been heard: those of the run of steps in front. So that term
is the coded scalar at the run's two points, and Johnson/Desc/K14/Honest/MuCoded.lean reads it.

Main names:
  SpOneCoin           A PREMISE's FORM, on the book and the letter holds together: the coin that the
                      part at "SPLIT" spends is the entry number 0 of o_sp's mask row as the prover
                      holds it. If it failed, the scalar sent would in general not meet the
                      constraint that "SPLIT" lays on o_omega's group: a reason for the premise,
                      borne by no theorem
  elems_one           a small one
  showsMu_of          **ShowsMu**, under the premises listed below but hN
  exchange8_of        so «Exchange» at "SPLIT" with no premise on what is shown, under all of them

What is assumed, as premises: Plan2 (Debts2.lean). In exchange8_of also hN: no two messages have one
tenant. AtSplit at the member number 8 (Honest/K14/Paid.lean): what it declares, and that the kind's
half stands at its place (hAt). The part's public data: the shape is the plan's (hS); "LIN point" is
the chain's round number 0, "LIN zeta" its round number 6 (h0, h6). The rows held are the rows that
the part is handed, read, at the places that hold the matrix (hRows). SpOneCoin (hCoin).

What is not claimed. That these premises hold at a thread of the protocol's. The two premises on
what the sendings show. That the thread holds at any run. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.Exchange2
import Johnson.Desc.ProofFile.Honest.K14.Paid
import Johnson.Desc.K14.Honest.MuCoded

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes OnBytes.Params
open OnBytes.Slice (rdE)
open Desc.K14 (P14 first)
open Desc.K14.Honest

variable {Bk : ProverCoinCounts} {W₀ Rc X₀ P₁ Wt : Type} {Q : P14} {sentU : Array OracleNotice} {layO : TreeLay}

/-- **THE COIN THAT "SPLIT" SPENDS IS THE ENTRY NUMBER 0 OF o_sp's MASK ROW, AS THE PROVER HOLDS
IT.** A premise's form, on the book and on the letter holds together. It speaks wherever lendRow
returns at the row of "SPLIT", at every run's coins k and EVERY input w, valid or not. The coin is
read by headD zeroE: where the row is lent no coin of the extension field to spend, 0 is read. The
chain's number is the literal 1 (Bk.rowsOf 1, k.look 1). Where the list has no member number 8 it
holds vacuously. -/
def SpOneCoin (Q : P14) (sentU : Array OracleNotice) (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type)
    (A : Data) (weights : W₀ → Weights) : Prop :=
  ∀ k w blk c, (letters2 Q sentU O Cl).thread.bs[8]? = some blk →
    lendRow Bk (Bk.rowsOf 1) (k.look 1) blk.place
      [(liftK14 A weights (splitPart A) : Part Empty (Common W₀ Rc TableKey) X₀)] 0 = .ok c →
    kappaOf (O.holds k w).cSp Q.par.S.sharedSplit.maskRows 0 =
      rdE.val ((coinsE c.1.2.1.1).headD zeroE)

/-- The elements of one challenge. -/
theorem elems_one (d : Fmt.Drawn) : elems [d] = Desc.K14.drawn (rvOf d) := by
  show d.elems.map E.ofTriple ++ [] = _
  rw [List.append_nil]
  rfl

/-- **ShowsMu**: the scalar that the part at "SPLIT" sends is the honest tables' scalar: under
Plan2, AtSplit at the member number 8 (hAt), the three facts on the public data (hS, h0, h6), hRows
and SpOneCoin (hCoin): see the head. -/
theorem showsMu_of (hQ : Plan2 Q sentU layO) (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type) (A : Data)
    (weights : W₀ → Weights)
    (hAt : AtSplit (letters2 Q sentU O Cl).thread 8 A weights) (hS : A.S = Q.par.S)
    (h0 : A.atPoint = 0) (h6 : A.atZeta = 6)
    (hRows : ∀ k w r j, j < Q.par.S.matrixRows * 2 ^ Q.par.S.kLo →
      (O.holds k w).Rw r j = rdE.val (entriesOf A.S (weights w.w₀) r j))
    (hCoin : SpOneCoin Q sentU O Cl A weights) : ShowsMu Q sentU O Cl := by
  obtain ⟨B⟩ := hQ.eight
  intro blk k s m E ds y cols R hblk hd hA hMv hrs
  obtain ⟨-, -, -, -, hM, -, -⟩ := hA
  obtain ⟨hsm, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes m.st.input.key := hbeg
  obtain ⟨⟨l, hl, hy⟩, -⟩ := hMv
  obtain ⟨d, hr, ho, hi, hop, hst⟩ := hAt.member blk hblk
  obtain ⟨x, c, -, hc, hp, -⟩ :=
    split_moved A weights blk d hr ho hi hop hst (hAt.half blk hblk) hl m ds hd
  obtain rfl := Except.ok.inj (hy.symm.trans hp)
  obtain rfl : (⟨[.e (Slice.ofE (scalarAt A c.1 (askOf A weights m.st)))], x⟩ : Fmt.RoundView) = R := by
    simpa [roundsOf] using hrs
  have F := flatOf_carried (Cl := Cl) O.c Q B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 O.tests O.last
    B.made
  obtain ⟨W, D, hseen, -, -, u⟩ := FlatAt.stepTo7 (B := B) F hQ.facts.goes 0 _ s _ [] c₀ [] hfold
  have S := hQ.pub m.st.input.key
  obtain ⟨x2, ids2, x5, ids5, t⟩ := S.to7 u
  have hpt : (Desc.K14.drawn W.view.r1).length = Q.par.S.kCol :=
    t.front.front.front.front.front.front.point
  have hseen' : m.seen = [W.R1, W.R2a, W.R2b, W.R4, W.R5a, W.R5b, W.R7] := hseen
  have hh : m.st.heard = [W.R1, W.R2a, W.R2b, W.R4, W.R5a, W.R5b, W.R7].map (·.drawn) := by
    rw [← hsm, hseen']
  have e1 : firstRv m.st.heard = rvOf W.R1.drawn := by rw [hh]; rfl
  have e7 : m.st.heard.getD 6 noChallenge = W.R7.drawn := by rw [hh]; rfl
  have p1 : elems (heardFrom (askOf A weights m.st) A.atPoint 1) =
      Desc.K14.drawn (rvOf W.R1.drawn) := by
    rw [h0, ← elems_one]
    show elems ((m.st.heard.drop 0).take 1) = _
    rw [hh]
    rfl
  have p7 : elems (heardFrom (askOf A weights m.st) A.atZeta 1) =
      Desc.K14.drawn (rvOf W.R7.drawn) := by
    rw [h6, ← elems_one]
    show elems ((m.st.heard.drop 6).take 1) = _
    rw [hh]
    rfl
  rw [e1, e7]
  have key : scalarAt A c.1 (askOf A weights m.st) =
      muRun Q (first Q.codes m.st.input.key) (rvOf W.R1.drawn) (rvOf W.R7.drawn)
        (O.holds k m.st.input) := by
    show rdE.val (muAtE A.S (elems (heardFrom (askOf A weights m.st) A.atPoint 1))
      (elems (heardFrom (askOf A weights m.st) A.atZeta 1))
      (entriesOf A.S (weights m.st.input.w₀)) ((coinsE c.1.2.1.1).headD zeroE)) = _
    rw [p1, p7, hS]
    exact mu_coded Q _ (rvOf W.R1.drawn) (rvOf W.R7.drawn) (O.holds k m.st.input) _ _ hpt
      (fun r _ j hj => by rw [hRows k _ r j hj, hS]) (hCoin k _ blk c hblk hc)
  rw [← key]

/-- **«Exchange» at "SPLIT", with the premise on what is shown had from the part's own text**: under
showsMu_of's premises and hN (no two messages have one tenant). -/
theorem exchange8_of (hQ : Plan2 Q sentU layO) (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type)
    (hN : Function.Injective O.N.tenant) (A : Data) (weights : W₀ → Weights)
    (hAt : AtSplit (letters2 Q sentU O Cl).thread 8 A weights) (hS : A.S = Q.par.S)
    (h0 : A.atPoint = 0) (h6 : A.atZeta = 6)
    (hRows : ∀ k w r j, j < Q.par.S.matrixRows * 2 ^ Q.par.S.kLo →
      (O.holds k w).Rw r j = rdE.val (entriesOf A.S (weights w.w₀) r j))
    (hCoin : SpOneCoin Q sentU O Cl A weights) : Exchange (letters2 Q sentU O Cl).thread 8 :=
  exchange8 hQ O Cl hN (showsMu_of hQ O Cl A weights hAt hS h0 h6 hRows hCoin)

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.elems_one
#print axioms ProofFile.Honest.K14.showsMu_of
#print axioms ProofFile.Honest.K14.exchange8_of
