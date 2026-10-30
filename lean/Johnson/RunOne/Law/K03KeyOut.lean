-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/K03KeyOut.lean: THE TWO
ARMS OF THE ROW "K03key_sits" COMPOSE: at the maker's own piece of the kind's block in the key
file's first chain (piece 2 + 6 l + 2), from the history in front and THE PIECE'S YES, at a plan
that passes the tests named under "Premises": the conclusion of the kind's law K03key_law.out
(Johnson/Desc/First/Look/KeyLaw/TotalB.lean, Statement.lean) at the constant hearE, at the plan's
numbers: ALL SEVEN PREMISES OF Law.out ARE PAID INSIDE.

Main names:
  k03key_out: Hist₁ (Key.descriptionFromSource X N P) D (2 + 6 l + 2) a.1, the piece's out a τ = some b ⊢ there are
    the open ledger F, what was heard g, the ledger behind G, the entries es and the rounds rs with
    hearE face es F rs = some (g, G), b's record is a's with g and G put, and Law.out's conclusion
    holds of them at the typed lookup datK at every riding type, list of homes, state and placing of
    mask entries.

Who pays which premise: FaceIs, Adm: the plan (faceIsK, adm_of_tests) · F.next = first, hearE's yes:
the block's yes (block_law) · Sized F, HomeIs: the history (rec_of_hist) · viewWordsBelowPrime: the piece's
"below" (held_words, K03KeySits.lean).

Object: the kind's own block at its places in Key.descriptionFromSource X N P; hearE; K03key_law.
User: none yet; in this library as it lies: none (OutOfHist.lean imports this file and calls no name of it).
Letters: X, N, P, D; the frame's heads, tails and rests. Premises: planOk · RoomFor · the own
message counts an answer (both theorems in scope) · the first flat list's head and tail.

Limits. It runs over the lookups' numbers. Nothing on soundness.

-/
import Johnson.RunOne.Law.RecOfHist
import Johnson.RunOne.Law.K03KeySits
import Johnson.RunOne.KeyRowsAtFk
import Johnson.Top.Fire.Code.RowPieces
import Johnson.Desc.Plain.PieceYes
import Johnson.Desc.Plain.PaidKeeps
import Johnson.Desc.First.Look.KeyLaw.TotalB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K03KeyOut
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat OnBytes.Slice
open OnBytes.Model (Fork)
open _root_.Run (ckP)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K3 VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (Xi FirstState Claim Source lookupSeat)
open Johnson.RunOne.Sound (FK fk_K3_at)
open Johnson.RunOne.KeyRows23 (Fk fr₁)
open Johnson.RunOne.Law.SeatsKeyD
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.LinkAtFK
open Johnson.RunOne.Law.LinkAtCut
open Johnson.RunOne.Law.WalkAtFK
open Johnson.RunOne.Law.RecOfHist
open Johnson.RunOne.Law.K03KeySits
open LPFD (Hist₁)

variable {W : Type} (X : Source) (N : H2U.PlaceNums)
  (P : VerifiableInference.Desc.Key.LaterPlaces) (D : WholeD)
  (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl))
  (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl) (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl))
  (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
  (rest₁ : (i : ℕ) → (ds : List RDT) →
    Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) ((Fk X N P).XiPub × (Fk X N P).S₁) W ds)
  (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₂ 0)
    (((Fk X N P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) W ds)
  (rest₃ : (i : ℕ) → (ds : List RDT) →
    Rest (ckP .two) (frameAt D (allOf D) D.key₃ (Fk X N P).lastChainFirstTreeNumber)
      (((Fk X N P).XiPub × (Fk X N P).S₁ × (Fk X N P).S₂) × (Fk X N P).S₃) W ds)
  (dW wEnd : W)

/-- **THE TWO ARMS COMPOSE**: from the history in front and the piece's yes: the conclusion of
K03key_law.out at hearE, no premise of its seven left. -/
theorem k03key_out (hp : (FK X N P).planOk = true)
    (hR : RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes
      X.Y.k.oneTime.indexMasks.shape)
    (ha : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (l : ℕ)
    (hl : l < X.Y.k.oneTime.ranges.lookups.length) (p)
    (hq : ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃
        dW
      wEnd)).p₁ ::
    (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).l₁)[2 + 6 * l + 2]? = some p) (a b : (Xi × FirstState) × (fr₁ D).E.Str)
    (τ : Iop.Tr (uLT (ckP .two) p.ds))
    (hH : Hist₁ (VerifiableInference.Desc.Key.descriptionFromSource X N P) D (2 + 6 * l + 2) a.1)
    (hout : p.ior.red.out a τ = some b) :
    ∃ (F : Fork) (g : HeardG) (G : Fork) (es : List Fmt.Entry) (rs : List Fmt.RoundView)
      (o k : ℕ → Slot),
      lookupSeat.fork a.1.2 = some F ∧ hearE (faceOfLkp (Wf.lookupOf X.Y.k.oneTime.ranges.messageId
          (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime l))) es F rs = some (g, G) ∧
      b.1 = (a.1.1, lookupSeat.put a.1.2 g G) ∧ viewWordsBelowPrime ⟨rs, []⟩ = true ∧
      ∀ (T : Type) (hs : List Slot) (st : T)
        (sl : Slot → (datK T X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
          (Lof X.Y.k.oneTime l) hs).J),
        g.theta = zeroE ∧ (flatRV rs).head? = some ([], [readE g.alpha]) ∧
        PscRun.Later F G ∧ PscRun.Sized G ∧ G.next = 0 + (faceOfLkp (Wf.lookupOf
            X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime
                l))).slots ∧
        ∀ (H H' : Fork) (pl : List PlaneClaim) (u : OnBytes.K.Kc.Tape), PscRun.Later G H →
          planesG (faceOfLkp (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
              X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime l))) g H [] = some (pl, H', u) →
          PscRun.Later H H' ∧ (∀ x ∈ formsOf g pl, x.ents.isEmpty = true) ∧
          ∀ K, PscRun.Later H' K →
            (datK T X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
              (Lof X.Y.k.oneTime l) hs).lamRun (placesAt _ sl o k) st (flatRV rs) =
              outOf _ sl st K (fun j => a.1.2.base.home.getD j default) g pl := by
  have hW := fk_admitted X N P hp
  have hadm := Lk6.adm_of_tests X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) _
    (tests_at hW hl).2.1 (tests_at hW hl).2.2
  have hpb : p.b = held (lookupKind lookupSeat [(1, 0), (1, 1)] 0 []
      (VerifiableInference.Desc.Key.lookupPlace X.set l (Wf.lookupOf X.Y.k.oneTime.ranges.messageId
          (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime l)))) := by
    have h1 := LPFD.rowBlocks₁ (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd
      (2 + 6 * l + 2) p hq
    have h2 : (c₁ :: k₁)[2 + 6 * l + 2]? =
        some (lookupKind lookupSeat [(1, 0), (1, 1)] 0 []
          (VerifiableInference.Desc.Key.lookupPlace X.set l (Wf.lookupOf
              X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime
                  l)))) := by
      rw [← q₁, Nat.add_assoc]
      exact fk_K3_at X N P l _ (look_at X.Y.k.oneTime l hl)
    rw [List.getElem?_map, h2] at h1
    exact (Option.some.inj h1).symm
  have hrec := rec_of_hist D a.2 hp hR ha (2 + 6 * l + 2) (by omega) a.1 hH
  rw [Nat.add_assoc] at hrec
  obtain ⟨⟨hS, hI⟩, -⟩ := (recAt_link X l 2 (by omega) a.1.2).1 hrec
  have hd := piece_decides_at p a τ b hout
  rw [hpb] at hd
  have hw := held_words _ _ _ _ _ hd
  obtain ⟨e1, hd'⟩ := VerifiableInference.Desc.Plain.held_decide _ _ _ _ _ hd
  obtain ⟨F, g, G, es, f1, f2, -, -, f5, f6⟩ := block_law _ _ _ _ _ hd'
  obtain ⟨o, k, hh⟩ : ∃ o k : ℕ → Slot, HomeIs (faceOfLkp (Wf.lookupOf
      X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime l))) 0 o k
      fun j => a.1.2.base.home.getD j default := by
    rw [hI.1]
    exact ⟨_, _, homeIs_of_size _ _ _ hI.2.2.2.2⟩
  refine ⟨F, g, G, es, _, o, k, f1, f5, Prod.ext e1 f6, hw, fun T hs st sl => ?_⟩
  exact K03key_law.out _ sl st _ 0 o k _ es F _ g G
    (faceIsK T _ _ _ hs st hadm (d_le (tests_at hW hl).2.1)) hadm hh hw f2 (hS F f1) f5

end Johnson.RunOne.Law.K03KeyOut

#print axioms Johnson.RunOne.Law.K03KeyOut.k03key_out
