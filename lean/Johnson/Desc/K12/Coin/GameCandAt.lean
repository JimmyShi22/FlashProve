-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/GameCandAt.lean: **THE ROW's END: `TestGivesCand` AT A PIECE THAT A
DESCRIPTION HOLDS**: over the pair of the instance's public part and a chain's state, at whatever
type of claims, with the game paid and its public premises tests with code. Statements and proofs:
each is `k12_game_alike` | `k12_game_alikeO` (GameAlike.lean) at GameJ.lean's letters and errors,
handed to `cand_of_leads` (Game.lean).

  `k12_cand_at` | `k12_cand_atO`: FOR a piece p over P × S, at any type of claims, whose block is
    alike to `held` of the proximity test's seat, with the stretch dB :: dt from base on, nothing
    put back and the errors (e, errJ π r dt):
    PUBLIC: `PlaceB` | `PlaceOwnB` · the numbering's equation · `johOk` · `batOneOk` · e at least
      the batching's count;
    OF THE ROW's LETTERS: hon (the row's promises give `FirstOpens` | `FirstOpensOwn` behind the
      door in) · hkeep (a yes hands on the promise behind) · `SeatSeams` (GameCand.lean);
    THEN `TestGivesCand cs G arr smp p mine on on' ins outs` (Johnson/Desc/Sound/WordsLaw.lean), to
      the letter.
Limits: those of GameJ.lean, GameAlike.lean and GameCand.lean. NO SOUNDNESS IS CLAIMED. hon, hkeep
and the seams are paid nowhere here. That the counts are small is not said.

-/
import Johnson.Desc.K12.Coin.GameAlike
import Johnson.Desc.K12.Coin.GameCand
import Johnson.Desc.K12.Coin.GameJ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0 codes_of_johOk)
open H2K.First (batOneOk)
open Johnson.Pack (sigOf)

section
variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {P S Cl' Cells Tok : Type}
  (arr : ℕ → ℕ → ℕ)
  (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)

/-- **The row's end at a piece that a description holds**, first arm. -/
theorem k12_cand_at (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT)
    (dt : List RDT) (e : ℕ) (r : Fmt.M1.Stage → ℕ)
    (p : Piece (ckP .two) F (P × S) Cl' (Wit Cells Tok MsgT))
    (hb : Alike (held (P := P) ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave)) p.b)
    (h0 : p.back = []) (hbase : p.base = base) (hds : p.ds = dB :: dt)
    (herr : HEq p.err ((e, errJ π r dt) : Err (uLT (ckP .two) (dB :: dt))))
    (hB : PlaceB F π num base dB dt = true) (hnum : ∀ n, num (.own (π.nums.free + n)) = base + n)
    (hj : johOk π r = true) (hb1 : batOneOk π = true)
    (hle : batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e)
    (mine : List Mem) (on on' : (P × S) × F.E.Str → Prop)
    (ins outs : (P × S) × F.E.Str → Wit Cells Tok MsgT → Prop)
    (hon : ∀ a, on a → Promised cs G smp mine a.1 (strsOf F a.2) →
      ∀ t, enter a.1.2 = .ok t → FirstOpens π num no base t)
    (hkeep : ∀ a τ b, on a → Promised cs G smp mine a.1 (strsOf F a.2) →
      p.ior.red.out a τ = some b → on' b)
    (hseam : SeatSeams cs G arr smp (fun a : P × S => enter a.2) F π no (fun s => r s.st) rd
      p.base mine on ins outs) :
    TestGivesCand cs G arr smp p mine on on' ins outs := by
  have hl : likeOk π (dB :: dt) = true := by
    simp only [PlaceB, Bool.and_eq_true] at hB
    exact hB.1.1.1.1.2
  have hA := atPlace_of F π num _ _ _ _ _ base dB dt _ hB (codes_of_johOk r π hj) hnum
    (bears_errJ π r dB dt (like_of_ok π _ hl))
  have hg := k12_game_alike P S Cl' enter leave F (Wit Cells Tok MsgT) π num no _ _ _ _ _ rd base
    dB dt e (errJ π r dt) r p hb h0 hbase hds herr hA (fun _ => rfl) hj hb1 hle
  exact cand_of_leads cs G arr smp p mine on on' ins outs _
    (fun a => ∃ t, enter a.1.2 = .ok t ∧ QN π (NTuple F π no (fun s => r s.st) rd) (t, a.2))
    (Reduction.Leads.conseq hg (fun _ h => h)
      (fun _ _ _ _ _ q => by obtain ⟨⟨t, _, h1, _, h3⟩, _⟩ := q; exact ⟨t, h1, h3⟩))
    hon hkeep hseam

/-- **The row's end at a piece that a description holds**, second arm. -/
theorem k12_cand_atO (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT)
    (dt : List RDT) (e : ℕ) (r : Fmt.M1.Stage → ℕ)
    (p : Piece (ckP .two) F (P × S) Cl' (Wit Cells Tok MsgT))
    (hb : Alike (held (P := P) ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave)) p.b)
    (h0 : p.back = []) (hbase : p.base = base) (hds : p.ds = dB :: dt)
    (herr : HEq p.err ((e, errJ π r dt) : Err (uLT (ckP .two) (dB :: dt))))
    (hB : PlaceOwnB F π num base dB dt = true) (hnum : ∀ n, num (.own (π.nums.free + n)) = base + n)
    (hj : johOk π r = true) (hb1 : batOneOk π = true)
    (hle : batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e)
    (mine : List Mem) (on on' : (P × S) × F.E.Str → Prop)
    (ins outs : (P × S) × F.E.Str → Wit Cells Tok MsgT → Prop)
    (hon : ∀ a, on a → Promised cs G smp mine a.1 (strsOf F a.2) →
      ∀ t, enter a.1.2 = .ok t → FirstOpensOwn π num no base t)
    (hkeep : ∀ a τ b, on a → Promised cs G smp mine a.1 (strsOf F a.2) →
      p.ior.red.out a τ = some b → on' b)
    (hseam : SeatSeams cs G arr smp (fun a : P × S => enter a.2) F π no (fun s => r s.st) rd
      p.base mine on ins outs) :
    TestGivesCand cs G arr smp p mine on on' ins outs := by
  have hl : likeOk π (dB :: dt) = true := by
    simp only [PlaceOwnB, Bool.and_eq_true] at hB
    exact hB.1.1.1.1.2
  have hA := atPlaceOwn_of F π num _ _ _ _ _ base dB dt _ hB (codes_of_johOk r π hj) hnum
    (bears_errJ π r dB dt (like_of_ok π _ hl))
  obtain ⟨hP, h1, hlog⟩ := own_pays π (fun s => r s.st) r (fun _ => rfl) hj hb1 dB dt hA.like
  have hg := k12_game_alikeO P S Cl' enter leave F (Wit Cells Tok MsgT) π num no _ _ _ _ _ rd base
    dB dt e _ (errJ π r dt) p hb h0 hbase hds herr hA hP h1 hlog hle
  exact cand_of_leads cs G arr smp p mine on on' ins outs _
    (fun a => ∃ t, enter a.1.2 = .ok t ∧ QN π (NTuple F π no (fun s => r s.st) rd) (t, a.2))
    (Reduction.Leads.conseq hg (fun _ h => h)
      (fun _ _ _ _ _ q => by obtain ⟨⟨t, _, h1, _, h3⟩, _⟩ := q; exact ⟨t, h1, h3⟩))
    hon hkeep hseam

end

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.k12_cand_at
#print axioms VerifiableInference.Desc.K12.Coin.k12_cand_atO
