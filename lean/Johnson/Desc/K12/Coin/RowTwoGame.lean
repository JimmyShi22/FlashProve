-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/RowTwoGame.lean: **THE LAST CHAIN's BLOCK 2: "THE ONE ROW THAT IS OWED" AT
THAT ROW's OWN PIECE, WITH THE GAME PAID**: `TestGivesCand` at `pieceTwoX`
(Johnson/Flat/Last/RowTwoCand.lean), at that row's own errors. Statements and proofs.

RowTwoCand.lean's `rowTwo_cand` takes the debt `RowTwoOwes`: place (`AtPlace`) · opens · NH · bat
(the batching's converse, `BatAtN`, at every statement inside the promise) · seam · behind. The game
(GameJ.lean, GameAlike.lean, GameCandAt.lean) pays the batching's converse by a count, and takes
what it wants of the record off the block's own yes. So here place, NH and bat are gone:
  `alike_of`: the elder `Block.Alike` (Johnson/Flat/Last/AnyClaims.lean) is `Alike` (Alike.lean).
  `cand_mono_err`: `TestGivesCand` at a piece holds at the same piece with greater errors.
  `rowTwo_cand_game`: PUBLIC: `PlaceB` · the numbering's equation · `johOk` · `batOneOk` · the
    batching's count is at most e₀ · `errJ π r dt` is at most εt; OF THE ROW's LETTERS: opens · seam
    at NH := `NTuple Fr π no (fun s => r s.st) rd` · behind: each to the letter as in `RowTwoOwes`;
    THEN `TestGivesCand` at `pieceTwoX` at the errors (e₀, εt), at any type of claims and any
    extractor.
First arm: the first fold's mask has come from outside.
Limits: those of GameCandAt.lean. NO SOUNDNESS IS CLAIMED. opens, seam and behind are paid nowhere
here. That the two comparisons hold at a cap is not said.

-/
import Johnson.Desc.K12.Coin.GameCandAt
import Johnson.Flat.Last.RowTwoCand

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open VerifiableInference.OnPublicFiles.Last (pieceTwoX candN)
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0)
open H2K.First (batOneOk)
open Johnson.Pack (sigOf)

/-- The elder relation is this one. -/
theorem alike_of {S Cl Cl' : Type} {b' : Block S Cl'} {b : Block S Cl} (h : b'.Alike b) :
    Alike b b' := ⟨h.1, h.2.1, h.2.2⟩

section
variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {A Cl Cells Tok : Type}
  (arr : ℕ → ℕ → ℕ)
  (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  {C : PQ.CK} {Fr : Frame}

/-- The row at a piece holds at the same piece with greater errors. -/
theorem cand_mono_err (b : Block A Cl) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView)
    (x : A × Fr.E.Str → Iop.Tr (uLT C ds) → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
    (ε ε' : Err (uLT C ds)) (hε : Err.le ε ε') (mine : List Mem) (on on' : A × Fr.E.Str → Prop)
    (ins outs : A × Fr.E.Str → Wit Cells Tok MsgT → Prop)
    (h : TestGivesCand cs G arr smp (⟨b, base, ds, back, x, ε⟩ : Piece C Fr A Cl _) mine on on' ins
      outs) :
    TestGivesCand cs G arr smp (⟨b, base, ds, back, x, ε'⟩ : Piece C Fr A Cl _) mine on on' ins
      outs :=
  fun hS hF a ha hp => Doomed.mono_err _ hε (h hS hF a ha hp)

end

section
variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {Pp S₃ Cl Cells Tok : Type}
  (arr : ℕ → ℕ → ℕ)
  (smp : Pp × S₃ → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)

/-- **The one row that is owed, at block 2 of the last chain, with the game paid.** -/
theorem rowTwo_cand_game (Fr : Frame) (π : P12) (base : ℕ) (dB : RDT) (dt : List RDT) (e₀ : ℕ)
    (εt : Err (uLT (ckP .two) dt)) (enter : S₃ → Except String T12)
    (leave : S₃ → T12 → Except String S₃) (mine : List Mem)
    (on on' : (Pp × S₃) × Fr.E.Str → Prop)
    (ins : (Pp × S₃) × Fr.E.Str → Wit Cells Tok MsgT → Prop) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (rd : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ)
    (x : (Pp × S₃) × Fr.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dt)) → Wit Cells Tok MsgT →
      Wit Cells Tok MsgT)
    (hB : PlaceB Fr π num base dB dt = true) (hnum : ∀ n, num (.own (π.nums.free + n)) = base + n)
    (hj : johOk π r = true) (hb1 : batOneOk π = true)
    (hle : batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e₀) (hε : Err.le (errJ π r dt) εt)
    (opens : ∀ a t, on a → Promised cs G smp mine a.1 (strsOf Fr a.2) → enter a.1.2 = .ok t →
      FirstOpens π num no base t)
    (seam : ∀ a t st rest G0 Ly D, on a → Promised cs G smp mine a.1 (strsOf Fr a.2) →
      enter a.1.2 = .ok t → Fixes π t st rest G0 Ly D →
      NTuple Fr π no (fun s => r s.st) rd (t, a.2) st rest G0 Ly D →
      candN cs G arr smp Fr mine ins a)
    (behind : ∀ a τ b, on a → Promised cs G smp mine a.1 (strsOf Fr a.2) →
      (pieceTwoX (Cl := Cl) Fr π base dB dt e₀ εt enter leave x).ior.red.out a τ = some b → on' b)
    (outs : (Pp × S₃) × Fr.E.Str → Wit Cells Tok MsgT → Prop) :
    TestGivesCand cs G arr smp (pieceTwoX (Cl := Cl) Fr π base dB dt e₀ εt enter leave x) mine on
      on' ins outs := by
  refine cand_mono_err cs G arr smp _ base (dB :: dt) [] x (e₀, errJ π r dt) (e₀, εt)
    ⟨Nat.le_refl _, hε⟩ mine on on' ins outs ?_
  refine k12_cand_at cs G arr smp enter leave Fr π num no rd base dB dt e₀ r _
    (alike_of (alike_lift _ _ (alike_below (alike_inside enter leave
      (K12.k12_alike guardedProximityTestParts π))))) rfl rfl rfl HEq.rfl hB hnum hj hb1 hle mine on on' ins outs
    (fun a ha hp t ht => opens a t ha hp ht) (fun a τ b ha hp hb => behind a τ b ha hp hb) ?_
  intro _ _ a ha hp hq b w _
  obtain ⟨t, ht, st, rest, G0, Ly, D, hf, hN⟩ := hq
  obtain ⟨c, hc, hi⟩ := seam a t st rest G0 Ly D ha hp ht hf hN
  exact ⟨c, hc, fun w' hw' => hi w w' hw'⟩

end

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.cand_mono_err
#print axioms VerifiableInference.Desc.K12.Coin.rowTwo_cand_game
