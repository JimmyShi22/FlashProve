-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/LinkAtCut.lean: It stands on Johnson/RunOne/Sound/.
THE SIX SEATS OF EACH LOOKUP'S LINK AT THE PIECES THAT THE MAKER CUTS
(piecesAt, Johnson/Desc/Sound/PaidAtDesc.lean), FROM THE DESCRIPTION'S OWN TESTS: fk_link_seats
(LinkAtFK.lean) where the key file's description passes its tests on the plan and its data are made.

What falls. The plan passes Wf.admitted, and the own message has the number 1: two of the
description's own public tests by name. The pieces hold the flat list's blocks; no two trees have
one number. The piece of the kind's block puts no round back, and its stretch is MadeOf the lookup's
shape: the stretches tile the chain, a stretch is the data of its block's declared rounds, and the
block passes its own test on the plan.

Main names:
  fk_clauses, fk_admitted, fk_messageId, fk_block_ok: what the description's tests on the plan give.
  tiled_at: in a tiled row, a piece that is not the last is owed just its stretch and puts no round
    back.
  made_at_cut: AT THE MAKER'S PIECES OF ANY DESCRIPTION THAT SEALS LAST AND WHOSE DATA ARE MADE,
    the piece that holds a block of the kind "lookup" at a face without a shift, a block that
    passes its own test on the plan and is not the chain's last: no round is put back; the stretch
    is MadeOf the lookup's shape.
  fk_link_cut: THE SIX SEATS OF LOOKUP NUMBER l.

Limits. Left as letters: the decoder dec, its condition cond and what else rides, Oth (Blind; LowDec
at each piece's place) · wd, mx · the two ledgers lo, lk in front of the first link · what else is
promised, Ex (Kept) · the index-mask message's number idxN, which is not 1 · the heads of the
description's three flat lists (with their equations) · the rests: each piece's extractor and errors
· the file's name and the two witnesses d, wEnd that the maker of pieces is handed · a value st0 of
the riding part's type. Left as premises: the lookup's number lies below the number of the plan's
lookups · the description passes its tests on the plan and its data are made · the witnesses' type M
× Wp is not empty · the seven rows are the link's · each piece's errors lie below the bound · the
typed lookup's errors along the maps lie below the errors of the piece of the kind's block. Named
nowhere in the theorem, and owed beside it: that PromL 0 holds at the record that stands behind the
sending of the second message.

-/
import Johnson.RunOne.Law.LinkAtFK
import Johnson.RunOne.Sound.StretchAtPieces
import Johnson.RunOne.Sound.KeySeatsAtFK
import Johnson.Desc.First.Look.KeyLaw.MadeStretch

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace Johnson.RunOne.Law.LinkAtCut
open Iop OnBytes OnBytes.Slice OnBytes.Params OnBytes.Maker OnBytes.Flat KObj
open _root_.Run (ckP)
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (Block FileDescription blocksOk)
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key (FirstState Claim Source lookupLink layerOrder lookupsOf
  lookupSeat lookupPlace fileClauses)
open Johnson.RunOne.Sound (FK H₁ fk_link_at fk_K3_at fk_layer_at fk_sealLast allOf_nodup
  stretchAtPieces)
open Johnson.RunOne.Law.RideKeyD
open Johnson.RunOne.Law.JoinKeyD
open Johnson.RunOne.Law.PromKeyD
open Johnson.RunOne.Law.SeatsAtFK
open Johnson.RunOne.Law.LinkSeats
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.LinkAtFK

/-! ## What the description's tests on the plan give -/

section
variable (X : Source) (N : H2U.PlaceNums) (P : VerifiableInference.Desc.Key.LaterPlaces)

/-- The public tests by name all hold; the first chain's blocks pass their own tests. -/
theorem fk_clauses (h : (FK X N P).planOk = true) :
    (VerifiableInference.Desc.Key.sourceClauses X.Y).all (·.2) = true ∧
      blocksOk (FK X N P).first.blocksInOrder = true := by
  unfold FileDescription.planOk FileDescription.planOkCore at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hf, hb⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  have hf' : ((fileClauses X N P _ _ _).all (·.2) && _) = true := hf
  rw [Bool.and_eq_true] at hf'
  have hc := hf'.1
  unfold fileClauses at hc
  simp only [List.all_append, Bool.and_eq_true] at hc
  exact ⟨hc.1.1.1, hb⟩

theorem fk_admitted (h : (FK X N P).planOk = true) :
    Wf.admitted X.Y.k.oneTime.codes X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) = true :=
  List.all_eq_true.1 (fk_clauses X N P h).1
    ("ranges", Wf.admitted X.Y.k.oneTime.codes X.Y.k.oneTime.ranges
      (Wf.matrixOf X.Y.k.oneTime.lin)) (by simp [VerifiableInference.Desc.Key.sourceClauses])

theorem fk_messageId (h : (FK X N P).planOk = true) : X.Y.k.oneTime.ranges.messageId = 1 := by
  have e := List.all_eq_true.1 (fk_clauses X N P h).1
    ("messageId", X.Y.k.oneTime.ranges.messageId == 1)
    (by simp [VerifiableInference.Desc.Key.sourceClauses])
  simpa using e

theorem fk_block_ok (h : (FK X N P).planOk = true) (i : ℕ) (b : Block FirstState Claim)
    (hb : (FK X N P).first.blocksInOrder[i]? = some b) : b.planOk = true := by
  have e := List.all_eq_true.1 (fk_clauses X N P h).2 b (List.mem_of_getElem? hb)
  rw [Bool.and_eq_true] at e
  exact e.1

end

/-! ## At the maker's pieces -/

/-- In a tiled row, a piece that is not the last is owed just its stretch and puts no round back. -/
theorem tiled_at {C : CK} {F : Frame} {S Cl W : Type} : ∀ (p : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)) (i : ℕ) (q : Piece C F S Cl W), Tiled p l →
    (p :: l)[i]? = some q → i < l.length → q.Owed ∧ q.back = []
  | _, [], _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | p, r :: l, 0, q, h, hq, _ => by
    have h' : p.Owed ∧ p.Listed ∧ p.back = [] ∧ r.base = p.base + p.trees ∧ Tiled r l := h
    obtain rfl : p = q := Option.some.inj hq
    exact ⟨h'.1, h'.2.2.1⟩
  | p, r :: l, i + 1, q, h, hq, hi => by
    have h' : p.Owed ∧ p.Listed ∧ p.back = [] ∧ r.base = p.base + p.trees ∧ Tiled r l := h
    exact tiled_at r l i q h'.2.2.2.2 hq (Nat.lt_of_succ_lt_succ hi)

/-- **At the maker's pieces of any description that seals last and whose data are made**: the piece
that holds a block of the kind "lookup" at a face without a shift, where that block passes its own
test on the plan and is not the first chain's last block. -/
theorem made_at_cut {Xi W : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (hD : F.data file = .ok D) (hs : F.sealLast = true)
    (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
    (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
    (h₁ : F.first.blocksInOrder = b₁ :: l₁) (h₂ : F.shared.blocksInOrder = b₂ :: l₂) (h₃ : F.second.blocksInOrder = b₃ :: l₃)
    (rest₁) (rest₂) (rest₃) (d wEnd : W) (i : ℕ) (σ : SeatG F.S₁ F.Cl) (before : List (ℕ × ℕ))
    (bits : ℕ) (guests : List (VerifiableInference.Desc.First.Look.Guest F.S₁ F.Cl)) (pg : PG)
    (hb : F.first.blocksInOrder[i]? = some (lookupKind σ before bits guests pg))
    (hnext : i + 1 < F.first.blocksInOrder.length) (hok : (lookupKind σ before bits guests pg).planOk = true)
    (hsh : pg.face.shifted = false) :
    let T := piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd
    ∀ p, (T.p₁ :: T.l₁)[i]? = some p →
      p.back = [] ∧ List.Forall₂ MadeOf p.ds (shapeG pg.face) := by
  intro T p hp
  obtain ⟨hO, hF, -⟩ := paidAtDesc Xi W F file D hD hs (ckP .two) b₁ l₁ b₂ l₂ b₃ l₃ h₁ h₂ h₃ rest₁
    rest₂ rest₃ d wEnd
  have hlen : (T.p₁ :: T.l₁).length = F.first.blocksInOrder.length := by
    have e := congrArg List.length hO.b₁
    simpa using e
  have hi : i < T.l₁.length := by
    have e : (T.p₁ :: T.l₁).length = T.l₁.length + 1 := rfl
    omega
  obtain ⟨hw, hbk⟩ := tiled_at T.p₁ T.l₁ i p hF.tiled₁ hp hi
  have hpb : p.b = liftP _ (below (lookupKind σ before bits guests pg)) :=
    block_at (T.p₁ :: T.l₁) F.first.blocksInOrder hO.b₁ i p _ hp hb
  have hal := (stretchAtPieces F file D hD (ckP .two) b₁ l₁ b₂ l₂ b₃ l₃ h₁ h₂ h₃ rest₁ rest₂ rest₃
    d wEnd).1 p (List.mem_of_getElem? hp)
  have hw1 := hw.1
  rw [hpb] at hal hw1
  rw [hbk] at hw1
  exact ⟨hbk, made_of_block σ before bits guests pg _ p.ds hsh hok hw1 hal⟩

/-! ## The six seats -/

variable (X : Source) (N : H2U.PlaceNums) (P : VerifiableInference.Desc.Key.LaterPlaces)

local notation "one" => X.Y.k.oneTime
local notation "idM" => X.Y.k.oneTime.ranges.messageId
local notation "mM" => Wf.matrixOf X.Y.k.oneTime.lin
local notation "nL" => X.Y.k.oneTime.ranges.lookups.length

variable {W : Type} {idxN : ℕ} {M Wp : Type} {wd : M → Means.Words GE} {mx : M → ℕ → ℕ → GE}
  {lo lk : Ledger} {Ex : FirstState → Prop}

/-- **THE SIX SEATS OF THE LINK OF LOOKUP NUMBER l, AT THE PIECES THAT THE MAKER CUTS.** -/
theorem fk_link_cut (hp : (FK X N P).planOk = true) (file : String) (D : WholeD)
    (hD : (FK X N P).data file = .ok D)
    (b₁ : Block (FK X N P).S₁ (FK X N P).Cl) (l₁ : List (Block (FK X N P).S₁ (FK X N P).Cl))
    (b₂ : Block (FK X N P).S₂ (FK X N P).Cl) (l₂ : List (Block (FK X N P).S₂ (FK X N P).Cl))
    (b₃ : Block (FK X N P).S₃ (FK X N P).Cl) (l₃ : List (Block (FK X N P).S₃ (FK X N P).Cl))
    (h₁ : (FK X N P).first.blocksInOrder = b₁ :: l₁) (h₂ : (FK X N P).shared.blocksInOrder = b₂ :: l₂)
    (h₃ : (FK X N P).second.blocksInOrder = b₃ :: l₃) (rest₁) (rest₂) (rest₃) (d wEnd : W)
    {dec : TK (H₁ X N P) × (frameAt D (allOf D) D.key₁ 0).E.Str → Option M}
    {cond : TK (H₁ X N P) × (frameAt D (allOf D) D.key₁ 0).E.Str → Prop} {Oth : TK (H₁ X N P) → M ×
        Wp → Prop}
    (l : ℕ) (hl : l < nL) (εs : ℝ≥0∞)
    (A0 : JointRow (H₁ X N P × FirstState) (frameAt D (allOf D) D.key₁ 0))
    (rs : List (JointRow (H₁ X N P × FirstState) (frameAt D (allOf D) D.key₁ 0))) (hidx : idxN ≠ 1)
    (hE : Kept one idM mM (Lof one) Ex)
    (hr : ∀ j ≤ 6, keyRowAt A0 rs (2 + 6 * l + j) =
      upF fun p₀ => (rows7 p₀ one X.set idM mM (Lof one) (handed (cntO idM mM (Lof one)) lo)
        (handed (cntK idM mM (Lof one)) lk) idxN wd mx dec cond nL
        (PromL one idM mM (Lof one) idxN nL lo lk Ex) l Wp Oth j))
    (hB : Blind dec cond Oth) (st0 : TK (H₁ X N P)) (hw : Nonempty (M × Wp)) :
    let T := piecesAt (ckP .two) (FK X N P) D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd
    (∀ j < 6, ∀ p, (T.p₁ :: T.l₁)[2 + 6 * l + j]? = some p →
      Err.Below p.err εs ∧ LowDec dec cond p.base) →
    (∀ p, (T.p₁ :: T.l₁)[2 + 6 * l + 2]? = some p →
      ∀ hds : List.Forall₂ MadeOf p.ds (shapeG (faceOfLkp (Wf.lookupOf idM mM (Lof one l)))),
        Err.le ((mapsAt (Fr := frameAt D (allOf D) D.key₁ 0) one idM mM (Lof one)
          (handed (cntO idM mM (Lof one)) lo) (handed (cntK idM mM (Lof one)) lk) idxN l
          (Lk6.adm_of_tests idM mM _ (tests_at (fk_admitted X N P hp) hl).2.1
            (tests_at (fk_admitted X N P hp) hl).2.2)
          (d_le (tests_at (fk_admitted X N P hp) hl).2.1) st0 p.ds hds).err
          (kAt one idM mM (Lof one) (handed (cntO idM mM (Lof one)) lo)
            (handed (cntK idM mM (Lof one)) lk) idxN wd mx dec cond nL l Wp Oth).err) p.err) →
    ∀ j < 6, SeatGood εs A0 (T.p₁ :: T.l₁) rs (2 + (6 * l + j)) := by
  intro T hpc herr
  have hs := fk_sealLast X N P
  obtain ⟨hO, -, -⟩ := paidAtDesc _ W (FK X N P) file D hD hs (ckP .two) b₁ l₁ b₂ l₂ b₃ l₃ h₁ h₂
    h₃ rest₁ rest₂ rest₃ d wEnd
  have hx := look_at one l hl
  have h2 := fk_K3_at X N P l _ hx
  have h3 := fk_layer_at X N P l _ hx
  have hnext : 2 + (6 * l + 2) + 1 < (FK X N P).first.blocksInOrder.length := by
    have e : 2 + (6 * l + 2) + 1 = 2 + (6 * l + 3) := by omega
    rw [e]
    exact (List.getElem?_eq_some_iff.1 h3).1
  have hmade := made_at_cut (FK X N P) file D hD hs b₁ l₁ b₂ l₂ b₃ l₃ h₁ h₂ h₃ rest₁ rest₂ rest₃
    d wEnd (2 + (6 * l + 2)) lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace X.set l _) h2 hnext
    (fk_block_ok X N P hp _ _ h2) rfl
  refine fk_link_seats X N P l hl εs A0 (T.p₁ :: T.l₁) rs (fk_admitted X N P hp)
    (by rw [fk_messageId X N P hp]; exact Ne.symm hidx) hE hO.b₁ hr (allOf_nodup D) hB st0 hw hpc
    fun p hq => ?_
  have hq' : (T.p₁ :: T.l₁)[2 + (6 * l + 2)]? = some p := by
    rw [← Nat.add_assoc]
    exact hq
  exact ⟨(hmade p hq').1, (hmade p hq').2, herr p hq (hmade p hq').2⟩

end Johnson.RunOne.Law.LinkAtCut

#print axioms Johnson.RunOne.Law.LinkAtCut.fk_clauses
#print axioms Johnson.RunOne.Law.LinkAtCut.fk_admitted
#print axioms Johnson.RunOne.Law.LinkAtCut.fk_messageId
#print axioms Johnson.RunOne.Law.LinkAtCut.fk_block_ok
#print axioms Johnson.RunOne.Law.LinkAtCut.tiled_at
#print axioms Johnson.RunOne.Law.LinkAtCut.made_at_cut
#print axioms Johnson.RunOne.Law.LinkAtCut.fk_link_cut
