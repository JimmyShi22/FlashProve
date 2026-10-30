-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/GameHeld.lean: **THE GAME OF THE PROXIMITY TEST AT THE PIECE THAT A
DESCRIPTION HOLDS.** Statements and proofs, over the block's parts with guard (c).

At a description the rows of pieces (`piecesAt`, Johnson/Desc/Sound/PaidAtDesc.lean) are the maker's
(`cutRow`) at the blocks `held b`: `below b` (the test "every word is below the prime" in front),
lifted to the pair of what was handed to the chain and the chain's own state. GameTile.lean's
`k12_game_tile` asks a row that holds the seat itself: so it does not speak of these rows. Here the
law is carried through both wraps, by `leads_under` and `leads_lift`
(Johnson/Desc/Plain/LiftBelow.lean).

  (`leftBehind_eq`: what is left behind a row of blocks, in closed form: in
    Johnson/Desc/Sound/TilesAt.lean.)
  `k12_game_held` | `k12_game_heldO`: the law at ANY piece over P × S whose block is `held` of the
    seat, with nothing put back, base, data dB :: dt, errors (e, εt): read at the state's second
    part; and, for certain, the first part rides along unturned.
  `k12_game_heldTile` | `k12_game_heldTileO`: for a chain's row of blocks pre ++ seat :: b' :: post:
    the maker's piece number pre.length IN THE ROW OF THE HELD BLOCKS has the law, at the base and
    the data in closed form.
  `piecesAt_row₁` | `₂` | `₃`: for every description F and data D: the three rows of `piecesAt` ARE
    `cutRow`'s at the held blocks, at (rest₁, [sealRound], 0, 0, D.ds₁), (rest₂, [], 0, D.t₁,
    D.ds₂), (rest₃, [], 0, D.t₁ + D.t₂, D.ds₃): by definition.
WHEN `k12_game_heldTile` SPEAKS OF A DESCRIPTION's ROW: where C is `ckP .two`, F.Cl is Unit, the
chain's own state (F.S₁ | F.S₂ | F.S₃) is the doors' S, and the chain's flat list of blocks is
pre ++ seat :: b' :: post: four facts on the description, none shown here of any F.
Limits: those of GameSeat.lean and GameTile.lean. NO SOUNDNESS IS CLAIMED. A rule under letters: no
description is named: that a description's flat list of blocks is pre ++ seat :: b' :: post, at
which π and doors, is a premise. The seat must not be the row's last block.

-/
import Johnson.Desc.K12.Coin.GameTile
import Johnson.Desc.Plain.LiftBelow
import Johnson.Desc.Sound.PaidAtDesc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.Pin (NTuple)
open H2K.Pub (PayPub johOk batV0)
open H2K.First (batOneOk)

/-- **The game at any piece that holds the seat as a description holds it**, first arm. -/
theorem k12_game_held (P S : Type) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ)
    (no : ℕ → ℕ) (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT)
    (dt : List RDT) (e : ℕ) (εt : Err (uLT (ckP .two) dt)) (r : Fmt.M1.Stage → ℕ)
    (p : Piece (ckP .two) F (P × S) Unit W)
    (hb : p.b = held (P := P) ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave))
    (h0 : p.back = []) (hbase : p.base = base) (hds : p.ds = dB :: dt)
    (herr : HEq p.err ((e, εt) : Err (uLT (ckP .two) (dB :: dt))))
    (hA : AtPlace F π num L mC mS mW rad base dB dt εt)
    (hr : ∀ s, rad s = r s.st) (hj : johOk π r = true) (hb1 : batOneOk π = true)
    (hle : batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e) :
    p.ior.red.Leads (fun a => ∀ t, enter a.1.2 = .ok t → FirstOpens π num no base t)
      (fun a b => (∃ t t', enter a.1.2 = .ok t ∧ leave a.1.2 t' = .ok b.1.2 ∧
        QN π (NTuple F π no rad rd) (t, a.2)) ∧ b.1 = (a.1.1, b.1.2))
      p.err := by
  obtain ⟨pb, pbase, pds, pback, pext, perr⟩ := p
  dsimp only at hb h0 hbase hds herr
  subst hb h0 hbase hds
  obtain rfl := eq_of_heq herr
  exact leads_lift (S := P × S) Prod.snd (fun t s => (t.1, s))
    (pieceOf (C := ckP .two) (F := F) (W := W)
      ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) pbase (dB :: dt) []
      ⟨fun _ _ w => w, (e, εt)⟩).under
    (fun a => ∀ t, enter a.1 = .ok t → FirstOpens π num no pbase t)
    (fun a b => ∃ t t', enter a.1 = .ok t ∧ leave a.1 t' = .ok b.1 ∧
      QN π (NTuple F π no rad rd) (t, a.2))
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (leads_under _ rfl _ _
      (k12_gameSeat S enter leave F W π num no L mC mS mW rad rd pbase dB dt (fun _ _ w => w)
        e εt r hA hr hj hb1 hle))

/-- **THE GAME AT THE MAKER's PIECE IN A ROW OF HELD BLOCKS**, first arm. -/
theorem k12_game_heldTile (P S : Type) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ)
    (no : ℕ → ℕ) (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT)
    (dt : List RDT) (e : ℕ) (εt : Err (uLT (ckP .two) dt)) (r : Fmt.M1.Stage → ℕ)
    (rest : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) F (P × S) W ds) (putBack : List Fmt.RoundView)
    (pre : List (Block S Unit)) (b' : Block S Unit) (post : List (Block S Unit))
    (b₀ : Block S Unit) (l : List (Block S Unit)) (i base₀ : ℕ) (ds : List RDT)
    (hL : b₀ :: l = pre ++ (proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave :: b' :: post)
    (hbase : base₀ + nTrees (ds.take (pre.map (·.rounds.length)).sum) = base)
    (hds : (ds.drop (pre.map (·.rounds.length)).sum).take
      (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length = dB :: dt)
    (herr : ∀ ds', ds' = dB :: dt → HEq (rest (i + pre.length) ds').err
      ((e, εt) : Err (uLT (ckP .two) (dB :: dt))))
    (hA : AtPlace F π num L mC mS mW rad base dB dt εt)
    (hr : ∀ s, rad s = r s.st) (hj : johOk π r = true) (hb1 : batOneOk π = true)
    (hle : batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e) :
    ∃ p, ((cutRow rest putBack i base₀ ds (held b₀) (l.map held)).1 ::
        (cutRow rest putBack i base₀ ds (held b₀) (l.map held)).2)[pre.length]? = some p ∧
      p.ior.red.Leads (fun a => ∀ t, enter a.1.2 = .ok t → FirstOpens π num no base t)
        (fun a b => (∃ t t', enter a.1.2 = .ok t ∧ leave a.1.2 t' = .ok b.1.2 ∧
          QN π (NTuple F π no rad rd) (t, a.2)) ∧ b.1 = (a.1.1, b.1.2))
        p.err := by
  have hL' : held (P := P) b₀ :: l.map held = pre.map held ++
      held ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) :: held b' :: post.map held := by
    have := congrArg (List.map (held (P := P))) hL
    simpa using this
  have hat := cutRow_at rest putBack _ (held b') (post.map held) (pre.map held) (held b₀)
    (l.map held) i base₀ ds hL'
  rw [List.length_map] at hat
  have hlb := leftBehind_eq (pre.map (held (P := P))) base₀ ds
  have hsum : ((pre.map (held (P := P))).map (·.rounds.length)).sum =
      (pre.map (·.rounds.length)).sum := by
    rw [List.map_map]; rfl
  rw [hsum] at hlb
  refine ⟨_, hat, k12_game_held P S enter leave F W π num no L mC mS mW rad rd base dB dt
    e εt r _ rfl rfl ?_ ?_ ?_ hA hr hj hb1 hle⟩
  · show (leftBehind (pre.map held) base₀ ds).1 = base
    rw [hlb]; exact hbase
  · show (leftBehind (pre.map held) base₀ ds).2.take _ = dB :: dt
    rw [hlb]; exact hds
  · refine herr _ ?_
    rw [hlb]; exact hds

/-- **The game at any piece that holds the seat as a description holds it**, second arm. -/
theorem k12_game_heldO (P S : Type) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ)
    (no : ℕ → ℕ) (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT)
    (dt : List RDT) (e v₀ : ℕ) (εt : Err (uLT (ckP .two) dt))
    (p : Piece (ckP .two) F (P × S) Unit W)
    (hb : p.b = held (P := P) ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave))
    (h0 : p.back = []) (hbase : p.base = base) (hds : p.ds = dB :: dt)
    (herr : HEq p.err ((e, εt) : Err (uLT (ckP .two) (dB :: dt))))
    (hA : AtPlaceOwn F π num L mC mS mW rad base dB dt εt)
    (hP : PayPub π rad dB.entry.rows v₀) (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0])
    (hlog : dB.entry.logN ≤ 64) (hle : v₀ * (bsRound .two dB.entry dB.kind).w ≤ e) :
    p.ior.red.Leads (fun a => ∀ t, enter a.1.2 = .ok t → FirstOpensOwn π num no base t)
      (fun a b => (∃ t t', enter a.1.2 = .ok t ∧ leave a.1.2 t' = .ok b.1.2 ∧
        QN π (NTuple F π no rad rd) (t, a.2)) ∧ b.1 = (a.1.1, b.1.2))
      p.err := by
  obtain ⟨pb, pbase, pds, pback, pext, perr⟩ := p
  dsimp only at hb h0 hbase hds herr
  subst hb h0 hbase hds
  obtain rfl := eq_of_heq herr
  exact leads_lift (S := P × S) Prod.snd (fun t s => (t.1, s))
    (pieceOf (C := ckP .two) (F := F) (W := W)
      ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) pbase (dB :: dt) []
      ⟨fun _ _ w => w, (e, εt)⟩).under
    (fun a => ∀ t, enter a.1 = .ok t → FirstOpensOwn π num no pbase t)
    (fun a b => ∃ t t', enter a.1 = .ok t ∧ leave a.1 t' = .ok b.1 ∧
      QN π (NTuple F π no rad rd) (t, a.2))
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (leads_under _ rfl _ _
      (k12_gameSeatO S enter leave F W π num no L mC mS mW rad rd pbase dB dt (fun _ _ w => w)
        e v₀ εt hA hP h1 hlog hle))

/-- **THE GAME AT THE MAKER's PIECE IN A ROW OF HELD BLOCKS**, second arm. -/
theorem k12_game_heldTileO (P S : Type) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ)
    (no : ℕ → ℕ) (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT)
    (dt : List RDT) (e v₀ : ℕ) (εt : Err (uLT (ckP .two) dt))
    (rest : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) F (P × S) W ds) (putBack : List Fmt.RoundView)
    (pre : List (Block S Unit)) (b' : Block S Unit) (post : List (Block S Unit))
    (b₀ : Block S Unit) (l : List (Block S Unit)) (i base₀ : ℕ) (ds : List RDT)
    (hL : b₀ :: l = pre ++ (proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave :: b' :: post)
    (hbase : base₀ + nTrees (ds.take (pre.map (·.rounds.length)).sum) = base)
    (hds : (ds.drop (pre.map (·.rounds.length)).sum).take
      (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length = dB :: dt)
    (herr : ∀ ds', ds' = dB :: dt → HEq (rest (i + pre.length) ds').err
      ((e, εt) : Err (uLT (ckP .two) (dB :: dt))))
    (hA : AtPlaceOwn F π num L mC mS mW rad base dB dt εt)
    (hP : PayPub π rad dB.entry.rows v₀) (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0])
    (hlog : dB.entry.logN ≤ 64) (hle : v₀ * (bsRound .two dB.entry dB.kind).w ≤ e) :
    ∃ p, ((cutRow rest putBack i base₀ ds (held b₀) (l.map held)).1 ::
        (cutRow rest putBack i base₀ ds (held b₀) (l.map held)).2)[pre.length]? = some p ∧
      p.ior.red.Leads (fun a => ∀ t, enter a.1.2 = .ok t → FirstOpensOwn π num no base t)
        (fun a b => (∃ t t', enter a.1.2 = .ok t ∧ leave a.1.2 t' = .ok b.1.2 ∧
          QN π (NTuple F π no rad rd) (t, a.2)) ∧ b.1 = (a.1.1, b.1.2))
        p.err := by
  have hL' : held (P := P) b₀ :: l.map held = pre.map held ++
      held ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) :: held b' :: post.map held := by
    have := congrArg (List.map (held (P := P))) hL
    simpa using this
  have hat := cutRow_at rest putBack _ (held b') (post.map held) (pre.map held) (held b₀)
    (l.map held) i base₀ ds hL'
  rw [List.length_map] at hat
  have hlb := leftBehind_eq (pre.map (held (P := P))) base₀ ds
  have hsum : ((pre.map (held (P := P))).map (·.rounds.length)).sum =
      (pre.map (·.rounds.length)).sum := by
    rw [List.map_map]; rfl
  rw [hsum] at hlb
  refine ⟨_, hat, k12_game_heldO P S enter leave F W π num no L mC mS mW rad rd base dB dt
    e v₀ εt _ rfl rfl ?_ ?_ ?_ hA hP h1 hlog hle⟩
  · show (leftBehind (pre.map held) base₀ ds).1 = base
    rw [hlb]; exact hbase
  · show (leftBehind (pre.map held) base₀ ds).2.take _ = dB :: dt
    rw [hlb]; exact hds
  · refine herr _ ?_
    rw [hlb]; exact hds

/-! ## The rows of `piecesAt` are the maker's, at the held blocks -/

section
variable {Xi W : Type} (C : PQ.CK) (F : FileDescription Xi) (D : WholeD)
  (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
  (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
  (rest₁ : (i : ℕ) → (ds : List RDT) →
    Rest C (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
  (rest₂ : (i : ℕ) → (ds : List RDT) →
    Rest C (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
  (rest₃ : (i : ℕ) → (ds : List RDT) →
    Rest C (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
  (d wEnd : W)

theorem piecesAt_row₁ :
    (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₁ ::
      (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₁ =
    (cutRow rest₁ [sealRound] 0 0 D.ds₁ (held b₁) (l₁.map held)).1 ::
      (cutRow rest₁ [sealRound] 0 0 D.ds₁ (held b₁) (l₁.map held)).2 := rfl

theorem piecesAt_row₂ :
    (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₂ ::
      (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₂ =
    (cutRow rest₂ [] 0 D.t₁ D.ds₂ (held b₂) (l₂.map held)).1 ::
      (cutRow rest₂ [] 0 D.t₁ D.ds₂ (held b₂) (l₂.map held)).2 := rfl

theorem piecesAt_row₃ :
    (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₃ ::
      (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₃ =
    (cutRow rest₃ [] 0 (D.t₁ + D.t₂) D.ds₃ (held b₃) (l₃.map held)).1 ::
      (cutRow rest₃ [] 0 (D.t₁ + D.t₂) D.ds₃ (held b₃) (l₃.map held)).2 := rfl

end

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.k12_game_held
#print axioms VerifiableInference.Desc.K12.Coin.k12_game_heldO
#print axioms VerifiableInference.Desc.K12.Coin.k12_game_heldTile
#print axioms VerifiableInference.Desc.K12.Coin.k12_game_heldTileO
#print axioms VerifiableInference.Desc.K12.Coin.piecesAt_row₁
#print axioms VerifiableInference.Desc.K12.Coin.piecesAt_row₂
#print axioms VerifiableInference.Desc.K12.Coin.piecesAt_row₃
