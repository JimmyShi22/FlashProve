-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/GameTile.lean: **THE GAME OF THE PROXIMITY TEST AT THE TILING's OWN PIECE.**
Definitions, statements and proofs, over the block's parts with guard (c).

The rule of composition takes a chain's blocks each with its stretch, as the maker `cutRow`
(Johnson/Desc/Sound/Tiles.lean) cuts them. GameSeat.lean's law stands at a piece written out
(`pieceOf` at letters). Here: the maker's piece at the seat's number IS such a piece.

  (`leftBehind`, `cutRow_at`: the maker's piece at a block of a row: they name no kind and stand in
    Johnson/Desc/Sound/TilesAt.lean.)
  `k12_game_piece` | `k12_game_pieceO`: the law at ANY piece whose five fields are the seat's:
    block, nothing put back, base, data dB :: dt, errors (e, εt).
  `k12_game_tile` | `k12_game_tileO`: so the maker's piece at the seat's number has the law.
Limits: those of GameSeat.lean. NO SOUNDNESS IS CLAIMED. The seat must not be the row's last block
(the last takes all the data that are left and has rounds put back). That the data behind pre begin
with dB :: dt, that the family's errors there are (e, εt), and `AtPlace` | `AtPlaceOwn` at that base
are premises. A rule under letters: no description is named.

-/
import Johnson.Desc.K12.Coin.GameSeat
import Johnson.Desc.Sound.TilesAt

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

/-- **The game at any piece of the seated block**, first arm: the piece's block is the proximity
test's inside the two doors, nothing is put back, its base, data and errors are base, dB :: dt,
(e, εt). -/
theorem k12_game_piece (S : Type) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ)
    (no : ℕ → ℕ) (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT)
    (dt : List RDT) (e : ℕ) (εt : Err (uLT (ckP .two) dt)) (r : Fmt.M1.Stage → ℕ)
    (p : Piece (ckP .two) F S Unit W)
    (hb : p.b = (proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) (h0 : p.back = [])
    (hbase : p.base = base) (hds : p.ds = dB :: dt)
    (herr : HEq p.err ((e, εt) : Err (uLT (ckP .two) (dB :: dt))))
    (hA : AtPlace F π num L mC mS mW rad base dB dt εt)
    (hr : ∀ s, rad s = r s.st) (hj : johOk π r = true) (hb1 : batOneOk π = true)
    (hle : batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e) :
    p.ior.red.Leads (fun a => ∀ t, enter a.1 = .ok t → FirstOpens π num no base t)
      (fun a b => ∃ t t', enter a.1 = .ok t ∧ leave a.1 t' = .ok b.1 ∧
        QN π (NTuple F π no rad rd) (t, a.2))
      p.err := by
  obtain ⟨pb, pbase, pds, pback, pext, perr⟩ := p
  dsimp only at hb h0 hbase hds herr
  subst hb h0 hbase hds
  obtain rfl := eq_of_heq herr
  exact k12_gameSeat S enter leave F W π num no L mC mS mW rad rd pbase dB dt pext e εt r hA hr hj
    hb1 hle

/-- **THE GAME AT THE TILING's OWN PIECE**, first arm: in a row of blocks pre ++ seat :: b' :: post
the maker's piece number pre.length has the law. -/
theorem k12_game_tile (S : Type) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ)
    (no : ℕ → ℕ) (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT)
    (dt : List RDT) (e : ℕ) (εt : Err (uLT (ckP .two) dt)) (r : Fmt.M1.Stage → ℕ)
    (rest : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) F S W ds) (putBack : List Fmt.RoundView)
    (pre : List (Block S Unit)) (b' : Block S Unit) (post : List (Block S Unit))
    (b₀ : Block S Unit) (l : List (Block S Unit)) (i base₀ : ℕ) (ds : List RDT)
    (hL : b₀ :: l = pre ++ (proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave :: b' :: post)
    (hbase : (leftBehind pre base₀ ds).1 = base)
    (hds : (leftBehind pre base₀ ds).2.take
      ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave).rounds.length = dB :: dt)
    (herr : HEq (rest (i + pre.length) ((leftBehind pre base₀ ds).2.take
      ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave).rounds.length)).err
      ((e, εt) : Err (uLT (ckP .two) (dB :: dt))))
    (hA : AtPlace F π num L mC mS mW rad base dB dt εt)
    (hr : ∀ s, rad s = r s.st) (hj : johOk π r = true) (hb1 : batOneOk π = true)
    (hle : batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e) :
    ∃ p, ((cutRow rest putBack i base₀ ds b₀ l).1 ::
        (cutRow rest putBack i base₀ ds b₀ l).2)[pre.length]? = some p ∧
      p.ior.red.Leads (fun a => ∀ t, enter a.1 = .ok t → FirstOpens π num no base t)
        (fun a b => ∃ t t', enter a.1 = .ok t ∧ leave a.1 t' = .ok b.1 ∧
          QN π (NTuple F π no rad rd) (t, a.2))
        p.err :=
  ⟨_, cutRow_at rest putBack _ b' post pre b₀ l i base₀ ds hL,
    k12_game_piece S enter leave F W π num no L mC mS mW rad rd base dB dt e εt r _ rfl rfl hbase
      hds herr hA hr hj hb1 hle⟩

/-- **The game at any piece of the seated block**, second arm: the piece's block is the proximity
test's inside the two doors, nothing is put back, its base, data and errors are base, dB :: dt,
(e, εt). -/
theorem k12_game_pieceO (S : Type) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ)
    (no : ℕ → ℕ) (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT)
    (dt : List RDT) (e v₀ : ℕ) (εt : Err (uLT (ckP .two) dt))
    (p : Piece (ckP .two) F S Unit W)
    (hb : p.b = (proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) (h0 : p.back = [])
    (hbase : p.base = base) (hds : p.ds = dB :: dt)
    (herr : HEq p.err ((e, εt) : Err (uLT (ckP .two) (dB :: dt))))
    (hA : AtPlaceOwn F π num L mC mS mW rad base dB dt εt)
    (hP : PayPub π rad dB.entry.rows v₀) (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0])
    (hlog : dB.entry.logN ≤ 64) (hle : v₀ * (bsRound .two dB.entry dB.kind).w ≤ e) :
    p.ior.red.Leads (fun a => ∀ t, enter a.1 = .ok t → FirstOpensOwn π num no base t)
      (fun a b => ∃ t t', enter a.1 = .ok t ∧ leave a.1 t' = .ok b.1 ∧
        QN π (NTuple F π no rad rd) (t, a.2))
      p.err := by
  obtain ⟨pb, pbase, pds, pback, pext, perr⟩ := p
  dsimp only at hb h0 hbase hds herr
  subst hb h0 hbase hds
  obtain rfl := eq_of_heq herr
  exact k12_gameSeatO S enter leave F W π num no L mC mS mW rad rd pbase dB dt pext e v₀ εt hA hP
    h1 hlog hle

/-- **THE GAME AT THE TILING's OWN PIECE**, second arm: in a row of blocks pre ++ seat :: b' :: post
the maker's piece number pre.length has the law. -/
theorem k12_game_tileO (S : Type) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ)
    (no : ℕ → ℕ) (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT)
    (dt : List RDT) (e v₀ : ℕ) (εt : Err (uLT (ckP .two) dt))
    (rest : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) F S W ds) (putBack : List Fmt.RoundView)
    (pre : List (Block S Unit)) (b' : Block S Unit) (post : List (Block S Unit))
    (b₀ : Block S Unit) (l : List (Block S Unit)) (i base₀ : ℕ) (ds : List RDT)
    (hL : b₀ :: l = pre ++ (proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave :: b' :: post)
    (hbase : (leftBehind pre base₀ ds).1 = base)
    (hds : (leftBehind pre base₀ ds).2.take
      ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave).rounds.length = dB :: dt)
    (herr : HEq (rest (i + pre.length) ((leftBehind pre base₀ ds).2.take
      ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave).rounds.length)).err
      ((e, εt) : Err (uLT (ckP .two) (dB :: dt))))
    (hA : AtPlaceOwn F π num L mC mS mW rad base dB dt εt)
    (hP : PayPub π rad dB.entry.rows v₀) (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0])
    (hlog : dB.entry.logN ≤ 64) (hle : v₀ * (bsRound .two dB.entry dB.kind).w ≤ e) :
    ∃ p, ((cutRow rest putBack i base₀ ds b₀ l).1 ::
        (cutRow rest putBack i base₀ ds b₀ l).2)[pre.length]? = some p ∧
      p.ior.red.Leads (fun a => ∀ t, enter a.1 = .ok t → FirstOpensOwn π num no base t)
        (fun a b => ∃ t t', enter a.1 = .ok t ∧ leave a.1 t' = .ok b.1 ∧
          QN π (NTuple F π no rad rd) (t, a.2))
        p.err :=
  ⟨_, cutRow_at rest putBack _ b' post pre b₀ l i base₀ ds hL,
    k12_game_pieceO S enter leave F W π num no L mC mS mW rad rd base dB dt e v₀ εt _ rfl rfl hbase
      hds herr hA hP h1 hlog hle⟩

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.k12_game_piece
#print axioms VerifiableInference.Desc.K12.Coin.k12_game_pieceO
#print axioms VerifiableInference.Desc.K12.Coin.k12_game_tile
#print axioms VerifiableInference.Desc.K12.Coin.k12_game_tileO
