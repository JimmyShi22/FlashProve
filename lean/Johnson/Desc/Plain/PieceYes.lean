-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/PieceYes.lean: WHAT A PIECE's YES SAYS, WITH THE VIEW BY NAME. `piece_decides`
(Johnson/Desc/Plain/K7Law.lean) forgets which rounds and columns the block's decision was shown.
Here they are named: the rounds ARE the transcript's own (`rvT C p.ds τ`, with what the piece puts
behind them), each without its sealed digest; the groups ARE the stage's opened columns, cut as
`Block.step` cuts them.

  `step_decides`: of `Block.step`. `piece_decides_at`: of a piece's reduction.
  `under_ok`: the yes of the piece with the test "below the prime" in front gives that test's yes ON
    THE STAGE's OWN VIEW, and the piece's yes. `leads_under_of`: so a law that is proved only at the
    transcripts whose view passes that test is a law of `p.under`.
Imports the small laws on the fold (`pieceOk`, `chainAtOk`, `foldConsOk`, `bindOk`:
Johnson/Desc/Sound/).
Nearest kin: `Piece.out_iff` (Johnson/Desc/Sound/RunIsDecide.lean): meant as THE HOME of this
step: `piece_decides_at` is to be re-seated on it as a corollary.

-/
import Johnson.Desc.Plain.LiftBelow
import Johnson.Desc.Sound.ExtHeardProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Plain
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)
open VerifiableInference.Desc.Sound

variable {S Cl W : Type} {C : CK} {F : Frame}

/-- The groups that `Block.step` hands to a block's decision. -/
def groupsAt (ft : ℕ) (b : Block S Cl) (rs : List Fmt.RoundView) (cols : List OpenedColumn) :
    List (List (ℕ × List UInt64)) :=
  regroup ((groupsOf ft b.rounds (rs.map (·.drawn))).map (·.length))
    (cols.take ((groupsOf ft b.rounds (rs.map (·.drawn))).flatMap id).length)

theorem step_decides {ft : ℕ} {b : Block S Cl} {s : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    {s' : S} {k : ℕ} (H : b.step ft s rs cols = .ok (s', k)) :
    b.decide s (rs.map noDigest) (groupsAt ft b rs cols) = .ok s' := by
  unfold Block.step at H
  obtain ⟨_, _, H⟩ := bindOk H
  obtain ⟨_, _, H⟩ := bindOk H
  obtain ⟨t, ht, H⟩ := bindOk H
  have e : t = s' := congrArg Prod.fst (Except.ok.inj H)
  exact e ▸ ht

/-- **Where a piece's reduction puts out b: its block's decision went on to b's record, ON THE
TRANSCRIPT's OWN ROUNDS AND THE STAGE's OWN OPENED COLUMNS.** -/
theorem piece_decides_at (p : Piece C F S Cl W) (a : S × F.E.Str) (τ : Iop.Tr (uLT C p.ds))
    (b : S × F.E.Str) (hb : p.ior.red.out a τ = some b) :
    p.b.decide a.1 ((rvT C p.ds τ ++ p.back).map noDigest)
      (groupsAt F.ft p.b (rvT C p.ds τ ++ p.back) (sView C p.stage a.2 τ).opened) = .ok b.1 := by
  obtain ⟨s', k, hst, H'⟩ := foldConsOk (chainAtOk (pieceOk p a τ b hb))
  have e : (s', (rvT C p.ds τ ++ p.back).drop p.b.rounds.length, _) =
      (b.1, ([] : List Fmt.RoundView), ([] : List OpenedColumn)) := Except.ok.inj H'
  have e₁ : s' = b.1 := congrArg Prod.fst e
  have e₂ : (rvT C p.ds τ ++ p.back).drop p.b.rounds.length = [] :=
    congrArg (fun x => x.2.1) e
  have e₃ : (rvT C p.ds τ ++ p.back).take p.b.rounds.length = rvT C p.ds τ ++ p.back :=
    List.take_of_length_le (List.drop_eq_nil_iff.1 e₂)
  rw [e₃, e₁] at hst
  exact step_decides hst

/-- The yes of the piece with the test in front: the test's yes on the stage's own view, and the
piece's yes. -/
theorem under_ok (p : Piece C F S Cl W) (hb : viewWordsBelowPrime ⟨p.back, []⟩ = true) (a : S × F.E.Str)
    (τ : Iop.Tr (uLT C p.ds)) (b : S × F.E.Str) (h : p.under.ior.red.out a τ = some b) :
    viewWordsBelowPrime (sView C p.stage a.2 τ) = true ∧ p.ior.red.out a τ = some b := by
  refine ⟨?_, under_out p hb a τ b h⟩
  have e : p.under.run = foldRunW F p.b.name [p.b] p.back :=
    foldBelow S Cl F p.b.name [p.b] p.back hb
  have h' : ((if sTests C p.stage a.2 τ then p.under.run a.1 (sView C p.stage a.2 τ) else none).map
      fun xo => (xo, p.ior.imp a.2 τ)) = some b := h
  rw [e] at h'
  unfold foldRunW at h'
  split at h'
  · split at h'
    · rename_i hv
      exact hv
    · cases h'
  · cases h'

/-- **A law proved only where the view is below the prime is a law of the piece that a description
holds.** -/
theorem leads_under_of (p : Piece C F S Cl W) (hb : viewWordsBelowPrime ⟨p.back, []⟩ = true)
    (on : S × F.E.Str → Prop) (Q : S × F.E.Str → S × F.E.Str → Prop)
    (h : ∀ a, on a → Doomed (uLT C p.ds) p.err fun τ =>
      viewWordsBelowPrime (sView C p.stage a.2 τ) = true → ∀ b, p.ior.red.out a τ = some b → Q a b) :
    p.under.ior.red.Leads on Q p.under.err := fun a ha =>
  Doomed.mono _ _ (fun τ hτ b hb' =>
    hτ (under_ok p hb a τ b hb').1 b (under_ok p hb a τ b hb').2) (h a ha)

end VerifiableInference.Desc.Plain

#print axioms VerifiableInference.Desc.Plain.piece_decides_at
#print axioms VerifiableInference.Desc.Plain.under_ok
#print axioms VerifiableInference.Desc.Plain.leads_under_of
