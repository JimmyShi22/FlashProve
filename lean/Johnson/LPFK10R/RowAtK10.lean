-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK10R/RowAtK10.lean: THE JOIN OF K10's FIELD law TO THE SEATED TERM's OWN PIECE: at the
one head `P5J.AtMg` (Johnson/P5J/AtMg.lean), at the second hash function: THE PIECE OF
`h.row 𝔏` (Johnson/P5J/RowsAtMg.lean) AT THE NUMBER OF EACH SUB-PROTOCOL OF THE KIND K10 IS THE
PIECE
OF WHICH `k10_law_full_lay` SPEAKS, at the written data, the cap, the place's own numbers and the
group in front of the link of the same number. Statements and proofs: calls. (In the Lean names a
"block" is a sub-protocol.)

What is said.
  `k10_row_piece`: `k10_piece_at_desc` (Close/Law/PieceAtDescK10.lean) at the head's letters: its
    premises "the data return" and "the last sub-protocol has a round" are the head's.
  `written_at`: at the head the declared rounds, written out, are the full size's written lists.
  `k10_row_at`: **at every sub-protocol b of cF.blocksInOrder of the kind K10: l < 25, p, Q, gs in frontFull,
    base with: k9At Zp l = some p · k10Par … = some Q · cF.blocksInOrder[ixK10 l]? = some b · (h.row 𝔏)[ixK10
    l]? = some (pieceOf (held b) base (dBat Q.rows :: dEps :: Q.k times dTwo) [] (restCap 𝔏.e₁ ..))
·
    Q.k = gs.k · gs.k = kLay ‹the l-th written list› ‹the written request's flags› · a yes of b is
    a yes of closeFrame at Q's entries.** "NO PROOF OF WORK" IS NOT A PREMISE: it is paid at the
head
    (`works_of_written`, `one_le_k`, WorksLive.lean).
  `k10_good_at_row`: **SO, from `k10_law_at_row` (Close/Law/KindK10LawCap.lean): that piece, with a
    map e laid on its extractor, has `GoodIn` in `k10_law_full_lay`'s letters at n := Q.rows.**

Limits. ONE PREMISE ON THE PUBLIC PART: Zp.first.shape = shapeFull (shown from the same
head AtMg in Johnson/P5J/ShapeFullAtMg.lean (P5J.AtMg.shape_full); not called
here).
In `k10_good_at_row`: hQ IS SHOWN NOWHERE; fa, N, keep,
B, num, A₀, w₀, w₁, L, pS, e are letters; num asks a claim of just Q.rows less the group's samples'
rows (`num_exists`: there is one where these are at most Q.rows: NOT SHOWN at any link; AND, by
a reading of `RowsTied`, the promise K10OnS can hold only at THE numbering that
sends each member's sample's row to its place among the verifier's rows: num is to be laid as a term
by whoever lays fa); Q.rows ≤ 2 ^ 57 is a premise. THE PAIRING IS BY THE NUMBER l: that the l-th
written list IS the list of the
members of the verifier's group at link l is not said; AT l = 0 AN EVALUATION FINDS THE
WRITTEN LIST ONE MEMBER LONGER THAN THE TABLE's GROUP (the index masks' message). At secondHashFunction, in
scope, the first chain, the full size. No soundness statement.

-/
import Johnson.P5J.RowsAtMg
import Johnson.LPFK10R.RoundsLive
import Johnson.LPFK10R.KLive
import Johnson.LPFK10R.SitsFullU
import Johnson.Desc.First.Close.Law.KindK10LawCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFK10
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Slice
open VerifiableInference.Desc (Block Chain Wit KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Close (Par kind dBat dEps dTwo k10_piece_at_desc kbAt kLay
  real_full closeFrame entries rdK wrK)
open VerifiableInference.Desc.ReqLit (shapeFull)
open Johnson.G (linksFullLit dryProofFull frontFull)
open P5J
open IM
open _root_.Run (ckP)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- The maker's piece at K10's number, at the head's letters. -/
theorem k10_row_piece (h : AtMg o Z D r Zp Np cF) (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (q₁ : (F0T o Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T o Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T o Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (i : ℕ) (b : Block (F0T o Zp Np cF).S₁ (F0T o Zp Np cF).Cl)
    (hb : (F0T o Zp Np cF).first.blocksInOrder[i]? = some b)
    (hi : i + 1 < (F0T o Zp Np cF).first.blocksInOrder.length) (Q : Par) (w1 : Q.workField = 0)
    (w2 : Q.workClose = 0) (hr : b.rounds = (kind (Cl := Unit) Q).rounds) :
    ∃ base : ℕ, (h.row 𝔏)[i]? =
      some (pieceOf (held b) base (dBat Q.rows :: dEps :: List.replicate Q.k dTwo) []
        (restCap 𝔏.e₁ i (dBat Q.rows :: dEps :: List.replicate Q.k dTwo))) :=
  k10_piece_at_desc (C := ckP .two) (F0T o Zp Np cF) "proof file" (D.at frS.P.T.a)
    (by rw [LaidAt.atDepth h.scope h.laid]; exact h.laid.data)
    (sealLast_of_planOk (F0T o Zp Np cF) h.laid.planOk) 𝔏.c₁ 𝔏.k₁ 𝔏.c₂ 𝔏.k₂ 𝔏.c₃ 𝔏.k₃ q₁ q₂ q₃
    (restCap 𝔏.e₁) (restCap 𝔏.e₂) (restCap 𝔏.e₃) 𝔏.dW 𝔏.wEnd i b hb hi Q w1 w2 hr

/-- The declared rounds, written out, are the full size's written lists. -/
theorem written_at (h : AtMg o Z D r Zp Np cF) :
    Johnson.G.OfPlan.writtenOf "proof file" (F0T o Zp Np cF).roundsDeclaredByBlocks = .ok dryProofFull :=
  (VerifiableInference.PlanWritten.seat_in_scope _ _ Z h.scope (LPFD.asks_written h.laid.asks)).1

/-- **THE SEATED TERM's PIECE AT EACH SUB-PROTOCOL OF THE KIND K10.** -/
theorem k10_row_at (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (hsh : Zp.first.shape = shapeFull) :
    ∀ b ∈ cF.blocksInOrder, b.place.kind = KindName.K10 →
      ∃ l, ∃ _ : l < 25, ∃ (p : VerifiableInference.Desc.K9.Where) (Q : Par)
        (gs : OnBytes.Params.GroupSize) (_ : gs ∈ frontFull) (base : ℕ),
        k9At Zp l = some p ∧ ProofFile.k10Par Zp (ProofFile.k9Stretches Zp) p = some Q ∧
        cF.blocksInOrder[ixK10 l]? = some b ∧
        (h.row 𝔏)[ixK10 l]? =
          some (pieceOf (held b) base (dBat Q.rows :: dEps :: List.replicate Q.k dTwo) []
            (restCap 𝔏.e₁ (ixK10 l) (dBat Q.rows :: dEps :: List.replicate Q.k dTwo))) ∧
        Q.k = gs.k ∧
        gs.k = kLay (linksFullLit.getD l []) (kbAt shapeFull l (linksFullLit.getD l [])) ∧
        ∀ s rs gs' s', b.decide s rs gs' = .ok s' → ∃ x, closeFrame (rdK s).1 (rdK s).2.1
          (rdK s).2.2 (entries Q) rs = .ok x ∧ s' = wrK s x.1 x.2 := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  intro b hb hK
  obtain ⟨l, hl, Lk, p, Q, -, e1, e2, -, e3, e6⟩ := k10_sits_each h.scope h.reads O b hb hK
  have e4 : b.rounds = (kind (Cl := Unit) Q).rounds := alone_rounds e6
  have hk1 : 1 ≤ Q.k := one_le_k h.laid.planOk hb e6
  obtain ⟨w1, w2⟩ := works_of_written (F := F0T OnBytes.secondHashFunction Zp Np cF) (written_at h)
    (b := b) hb e4 hk1
  obtain ⟨base, e5⟩ := k10_row_piece h 𝔏 q₁ q₂ q₃ (ixK10 l) b e3
    (ix_lt_flat h.scope h.reads O hl) Q w1 w2 e4
  have hp : p.link = l := k9At_link e1
  have e7 := k_of_shape h.laid.pub hsh e2 (by rw [hp]; exact hl)
  rw [hp] at e7
  obtain ⟨gs, hgs, hgk, -⟩ := realAt_group (real_full l hl)
  exact ⟨l, hl, p, Q, gs, hgs, base, e1, e2, e3, e5, e7.trans hgk.symm, hgk,
    fun s rs gs' s' hy => (seated_yes e6 (by simp) s s' rs gs' hy).1⟩

end LPFK10

namespace VerifiableInference.Desc.First.Close

open scoped ENNReal
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker Iop IOR
open Prob Run KObj Johnson.Pack Johnson.G
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.Sound
open Johnson.Top.H.ArrAdd (FreeAt)
open OnBytes.PscRun (drawnOf)
open VerifiableInference.Desc.K9 (recOf putRec)

variable (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksFullLit) (gs : GroupSize)
  (hgs : gs ∈ Johnson.G.frontFull) (kb : Fin lo.length → Bool)

local notation "RF" => groupFullLayK lo hlo gs hgs kb
local notation "SF" => sigOf codesFull2 lo
local notation "fx1" => ((1 : Fin 3), (1 : GE))
local notation "S1" => VerifiableInference.Desc.First.S

variable (keep : (sigOf codesFull2 lo).O → Prop) [DecidablePred keep] {B : Type} [Fintype B] (n : ℕ)
  (num : (groupFullLayK lo hlo gs hgs kb).G.Row B ≃ Fin n) {Kc St₀ Wp : Type} {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf codesFull2 lo).sub ((groupFullLayK lo hlo gs hgs kb).sizeB keep
    (SbV (groupFullLayK lo hlo gs hgs kb) B)
    (slV (groupFullLayK lo hlo gs hgs kb) (pullOf (groupFullLayK lo hlo gs hgs kb)))
    (ZV (groupFullLayK lo hlo gs hgs kb) n num)).kp).Msg × Wp))
  (w₀ : (sigOf codesFull2 lo).Wit × Wp)
  (w₁ : LdBrW (groupFullLayK lo hlo gs hgs kb).G ((groupFullLayK lo hlo gs hgs kb).sizeB keep
    (SbV (groupFullLayK lo hlo gs hgs kb) B)
    (slV (groupFullLayK lo hlo gs hgs kb) (pullOf (groupFullLayK lo hlo gs hgs kb)))
    (ZV (groupFullLayK lo hlo gs hgs kb) n num)).kp Wp)

set_option quotPrecheck false in
/-- The caller of the proved batching and fold at the real group. -/
local notation "CK" => (groupFullLayK lo hlo gs hgs kb).foldCaller keep
  (SbV (groupFullLayK lo hlo gs hgs kb) B)
  (slV (groupFullLayK lo hlo gs hgs kb) (pullOf (groupFullLayK lo hlo gs hgs kb)))
  (ZV (groupFullLayK lo hlo gs hgs kb) n num) ((1 : Fin 3), (1 : GE)) A₀ (placeFull gs.k).bC
  (placeFull gs.k).bZ w₀ w₁


open P5J in
/-- **K10's FIELD law AT THE SEATED TERM's OWN PIECE.** -/
theorem k10_good_at_row {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl}
    (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (hk : gs.k = kLay lo kb) (N : SlotNames RF)
    (L : List (BatFoldCaller GE))
    (ρ : Rd (CK) (wT (dBat n)) (wT dEps) (wT dTwo))
    (hρ : ρ = realRd (CK) (dBat n) dEps dTwo (oneOf id) (oneOf id))
    (pS : ∀ as : (Σ a : (RF).G.A, ((SF).om a.1).Z.S), ((SF).om as.1.1).Z.D → (RF).Sh.Cin.J → GE)
    (Pr : Par) (b : Block S1 ProofFile.Cl)
    (H : ∀ s rs gs' s', b.decide s rs gs' = .ok s' → ∃ x, closeFrame (rdK s).1 (rdK s).2.1
      (rdK s).2.2 (entries Pr) rs = .ok x ∧ s' = wrK s x.1 x.2)
    (base : ℕ)
    (i : ℕ) (e : _ → _ → _ → _)
    (fa : _ → _ → ((kBatFoldRide L).src (CK)).X × ((kBatFoldRide L).src (CK)).E.Str)
    (hn57 : n ≤ 2 ^ 57)
    (Rin Rout : _ → _ → Prop)
    (hQ : ∀ z a τ a', K10OnS RF N keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC
        (placeFull gs.k).bZ w₀ w₁ L pS Pr (fa z) a →
      (pieceOn b base (dBat n) dEps dTwo (Yc (CK)).k
        (fun a τ w => ((pieceOf (held b) base ((dBat n) :: dEps :: List.replicate (Yc (CK)).k dTwo)
    []
          (restCap 𝔏.e₁ i _)).withMap e).ext ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two)
          ((dBat n) :: dEps :: List.replicate (Yc (CK)).k dTwo)))).ior.red.out a τ = some a' →
      K10EndS RF N keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁ L
        (dBat n) dEps dTwo Pr b base
        (fun a τ w => ((pieceOf (held b) base ((dBat n) :: dEps :: List.replicate (Yc (CK)).k dTwo)
    []
          (restCap 𝔏.e₁ i _)).withMap e).ext ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two) ((dBat n) :: dEps :: List.replicate (Yc (CK)).k dTwo))) (fa z)
    a a' →
      ∀ w, Rout ((z, a'.1), a'.2) w → Rin ((z, a.1), a.2)
        (((pieceOf (held b) base ((dBat n) :: dEps :: List.replicate (Yc (CK)).k dTwo) [] (restCap
    𝔏.e₁ i _)).withMap e).ext
          ((z, a.1), a.2) τ w))
    (k' : ℕ) (hk' : k' = gs.k)
    (hrow : (h.row 𝔏)[i]? = some (pieceOf (held b) base
      (dBat n :: dEps :: List.replicate k' dTwo) [] (restCap 𝔏.e₁ i _))) :
    ∃ q, (h.row 𝔏)[i]? = some q ∧ (q.withMap e).GoodIn
      (fun a => K10OnS RF N keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ
        w₀ w₁ L pS Pr (fa a.1.1) (a.1.2, a.2))
      (fun _ => True) Rin Rout :=
  k10_law_at_row lo hlo gs hgs kb keep n num A₀ w₀ w₁ hk N L ρ hρ pS Pr b H base 𝔏.e₁ i e fa hn57
    Rin Rout hQ (h.row 𝔏) k' hk' hrow

end VerifiableInference.Desc.First.Close

#print axioms LPFK10.k10_row_piece
#print axioms LPFK10.written_at
#print axioms LPFK10.k10_row_at
#print axioms VerifiableInference.Desc.First.Close.k10_good_at_row
