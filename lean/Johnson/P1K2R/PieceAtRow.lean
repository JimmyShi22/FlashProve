-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/PieceAtRow.lean: code switching (K2): THE PIECE AT A PLACE OF THE KIND IN THE
ROW OF PIECES (h.row L, at the closed constant): WHAT THE KIND's CONDITION ASKS OF IT, GATHERED:
two of the condition's fields (Johnson/Top/H0/K2Ties/Assembly.lean: w2 · hkeys) at that piece's
own data, with the facts on its base and trees beside. Every step a call. NO BLOCK IMPORTS THIS
FILE.
  atRow_fits      the row is a tiling of the first chain's written rounds from base 0: the rule of
                  composition's own premises (Three.Fits) at the seated term: the SECOND part of
                  paidAtDesc (Johnson/Desc/Sound/PaidAtDesc.lean), of which P5J.AtMg.ofDesc takes
                  the first
  piece_at_row    (h.row L)[i]? = some q · i < 357 · cF.blocksInOrder[i]? = some B · B.rounds = K2.rounds p
                  · hp : P2At r p · bookFit N ps (toldOf cF.blocksInOrder) = true · i ≤ ps.length ⟹ ∃ d₁ d₂
                  extq: q is the kind's typed piece at q.base, d₁, d₂ ∧ the two rounds' entries
                  and kinds are the declared ones ∧ K2Wr r d₁ d₂ (THE FIELD w2) ∧ q.base =
                  N.treesAt ps[i]? ∧ d₁.trees.length = p.roots
  keysFit_at_row  with p.firstTree = 0 and q.ds = [d₁, d₂]: KeysFit X iJ iQ d₁ d₂ ρ p q.base ext,
                  at every X, iJ, iQ, ρ, ext (THE FIELD hkeys is its value at Letters.plain,
                  wordsMade and idExt)
BY: k2_written_at_row (Johnson/P1K2R/PlaceThree.lean) · K2Caller.k2Wr_of
(P2At.lean) · P1K2.piece_base_trees · keysFit_in_scope (K2Caller/KeysScope.lean)
· atRow_more.
WHAT STAYS. hp (the place's numbers are the typed structure's): the third field: not here. No
example. No soundness is claimed.
-/
import Johnson.P1K2R.PlaceThree
import Johnson.P1K2R.PieceBaseTrees
import Johnson.Top.H0.K2Caller.KeysScope
import Johnson.Top.H0.K2Caller.P2At
import Johnson.Desc.Laid.ProofFullLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open OnBytes OnBytes.Maker OnBytes.Slice
open _root_.Run (ckP)
open VerifiableInference.Desc (Block Chain Place Wit)
open VerifiableInference.Desc.First (Numbers bookFit)
open VerifiableInference.Desc.First.K2 (P2)
open VerifiableInference.Desc.First.K2Caller (SwRow P2At K2Wr k2Wr_of k2Q)
open VerifiableInference.Desc.Sound (toldOf below atDesc piecesAt restCap paidAtDesc MsgT
  sealLast_of_planOk)
open VerifiableInference.Desc.Kinds.Head.Law (atRow_more atRow_lift atRow_in)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl}

theorem atRow_fits (h : P5J.AtMg OnBytes.secondHashFunction Z D r₀ Zp Np cF)
    (L : P5J.Free OnBytes.Flat.numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) :
    (atDesc (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (piecesAt (ckP .two)
                  (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (D.at frS.P.T.a) L.c₁ L.k₁ L.c₂ L.k₂ L.c₃ L.k₃
                  (restCap L.e₁) (restCap L.e₂) (restCap L.e₃) L.dW L.wEnd)).Fits :=
  (paidAtDesc _ (Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (P5J.F0T OnBytes.secondHashFunction Zp Np cF) "proof file" _
    (by rw [P5J.LaidAt.atDepth h.scope h.laid]; exact h.laid.data)
    (sealLast_of_planOk (P5J.F0T OnBytes.secondHashFunction Zp Np cF) h.laid.planOk) (ckP .two) L.c₁ L.k₁
    L.c₂ L.k₂ L.c₃ L.k₃ q₁ q₂ q₃ (restCap L.e₁) (restCap L.e₂) (restCap L.e₃) L.dW L.wEnd).2.1

theorem piece_at_row (h : P5J.AtMg OnBytes.secondHashFunction Z D r₀ Zp Np cF)
    (L : P5J.Free OnBytes.Flat.numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) (i : Nat) (q)
    (hq : (h.row L)[i]? = some q) (hi : i < 357) (B : Block P5J.TS ProofFile.Cl)
    (hB : cF.blocksInOrder[i]? = some B) (p : P2)
    (hr : B.rounds = VerifiableInference.Desc.First.K2.rounds p) {r : SwRow} (hp : P2At r p)
    (N : Numbers) (ps : List Place) (hf : bookFit N ps (toldOf cF.blocksInOrder) = true)
    (hk : i ≤ ps.length) :
    ∃ d₁ d₂ extq, q = k2Q ((below B).lift Prod.snd fun t s => (t.1, s)) q.base d₁ d₂ extq ∧
      [d₁, d₂].map (·.entry) = (VerifiableInference.Desc.First.K2.rounds p).map (·.entry) ∧
      (∀ d ∈ [d₁, d₂], Fmt.kindOf d.entry.name = some d.kind) ∧ K2Wr r d₁ d₂ ∧
      q.base = N.treesAt ps[i]? ∧ d₁.trees.length = p.roots := by
  obtain ⟨d₁, d₂, extq, e, he, hkd⟩ := k2_written_at_row h L q₁ q₂ q₃ i q hq hi B hB p hr
  obtain ⟨hb, ht⟩ := piece_base_trees h L q₁ q₂ q₃ i q hq hi B hB p hr N ps hf hk
  have hds : q.ds = [d₁, d₂] := by rw [e]
  rw [hds] at ht
  exact ⟨d₁, d₂, extq, e, he, hkd, k2Wr_of hp he hkd, hb, (List.cons.inj ht).1⟩

end

end P1K2

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (numAt Block Chain)
open VerifiableInference.Desc.Sound (Frame Piece Tiled rowData Along RoundIs)
open VerifiableInference.Desc.First.K2Hands
open VerifiableInference.Desc.Kinds.Head.Law (atRow_more atRow_lift atRow_in)
open _root_.Run (ckP)
open _root_.Run.PQ (CK)

/-- The frame of the row of pieces (h.row L). -/
noncomputable abbrev frRow (D : WholeD) : Frame :=
  VerifiableInference.Desc.Sound.frameAt (D.at frS.P.T.a)
    (VerifiableInference.Desc.Sound.allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

theorem keysFit_at_row {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D r₀ Zp Np cF)
    (L : P5J.Free OnBytes.Flat.numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) (i : ℕ) (q)
    (hq : (h.row L)[i]? = some q) (hi : i < 357) (B : Block P5J.TS ProofFile.Cl)
    (hB : cF.blocksInOrder[i]? = some B) (p : K2.P2) (hr : B.rounds = K2.rounds p)
    (hft : p.firstTree = 0) {d₁ d₂ : RDT} (hds : q.ds = [d₁, d₂]) {W₁ : Type} {r : SwRow}
    {H : r.OK} (X : Letters r H)
    (iJ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
    (ρ : WordsOf (selZ X iJ iQ) d₁)
    (ext : Rec × (frRow D).E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → W₁ → W₁) :
    KeysFit (F := frRow D) (W := W₁) X iJ iQ d₁ d₂ ρ p q.base ext := by
  obtain ⟨hm, _⟩ := atRow_more h L q₁ q₂ q₃ i q hq (atRow_in h i hi)
  have hl := atRow_lift h L q₁ q₂ q₃ i q B hq hB
  have hb : q.b.rounds = K2.rounds p := by
    rw [hl]
    exact hr
  have hF := hm.rounds
  rw [hb, hds] at hF
  obtain ⟨r₁, r₂, e⟩ : ∃ r₁ r₂, K2.rounds p = [r₁, r₂] := ⟨_, _, rfl⟩
  have hA : Along (RoundIs (numAt (D.at frS.P.T.a).t₁ (D.at frS.P.T.a).t₂ 0)) (K2.rounds p)
      [d₁, d₂] := by
    rw [e] at hF ⊢
    cases hF with
    | cons a t =>
      cases t with
      | cons b u => exact ⟨a, b, trivial⟩
  have Ft := P1K2.atRow_fits h L q₁ q₂ q₃
  have hlaid := LPFD.Full.laidPOf_of h.laid.value h.laid.planOk h.laid.data h.laid.asks
  have hd := Ft.data₁.trans (congrArg (·.ds₁) (P5J.LaidAt.atDepth h.scope h.laid))
  exact keysFit_in_scope h.scope hlaid frS.P.T.a rfl _ _ Ft.tiled₁ Ft.base₁ hd hq p hft hds hA X
    iJ iQ ρ ext

end VerifiableInference.Desc.First.K2Caller

#print axioms P1K2.atRow_fits
#print axioms P1K2.piece_at_row
#print axioms VerifiableInference.Desc.First.K2Caller.keysFit_at_row
