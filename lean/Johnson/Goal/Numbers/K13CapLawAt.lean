-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/K13CapLawAt.lean: the law of the kind K13's batching AT THE CAP, at the written
rounds: the piece whose errors are the cap (Iop/ErrCap.lean: Err.cap 128) is GoodIn, by two
calls: Err.le_cap_of_below_inv and goodIn_atCap (Johnson/Desc/Sound/GoodInErr.lean).

  K13LawAtCap P Wr i, k13_law_at_cap: of pieceM3 (the proof file's first chain's record): from
      Johnson/Goal/Numbers/K13CalledAt.lean's K13Called
  K13AnyAtCap P Wr i, k13_any_at_cap: of pieceAt (K13/Law/GoodAny.lean), at ANY state T and block b
      that goes by the batching (ByBatt b P partF rowB): the law goodIn_any called, and carried to
      the cap: THE FORM THAT FITS, BY TYPE, A KEY FILE's PLACE, where the kind is seated through a
      lens on another record
  k13_law_at_cap_real: both, in a proof file
  k13_any_at_cap_key, k13_any_at_cap_key_at_scope: in a key file; there at the planner's own
      numbers, at every three public files in the scope of the goals

IT IS AN INSTANCE AT THE TYPED NUMBERS AND THE WRITTEN ROUNDS, NO MORE. Left as letters, each with
the law's own premise: the frame, the base, nR, rw, Pin, on (on'), hdet, hback (hon); for pieceAt
also T, b, partF, rowB with ByBatt: that a key file's block at its lens goes by the batching is
typed nowhere here.

What is not claimed. Johnson/Goal/Numbers/K13CalledAt.lean's k13_called_key speaks of pieceM3 at the
key file's numbers: it is true, and it is NOT the key file's place: use k13_any_at_cap_key. What the
heads of the files named do not claim. Nothing on soundness of a verifier, on an honest prover or on
hiding.

-/
import Johnson.Goal.Numbers.K13CapAt
import Johnson.Goal.Numbers.K13CalledAt
import Johnson.Desc.K13.Law.GoodAny
import Johnson.Desc.Sound.GoodInErr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model Cb Iop Run
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Params (Rounds LinSized)
open OnBytes.Params.Prices (AtRecord)
open Johnson.G (dryProofFull dryKeyFull codesFull2)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Frame Piece goodIn_atCap)
open VerifiableInference.Desc.K1 (realSized)
open Lk6.AtPlan (keyFull key_eq_at_scope)
open scoped ENNReal

/-- **The law at the cap, of pieceM3.** -/
def K13LawAtCap (P : Where) (Wr : Rounds) (i : ℕ) : Prop :=
  ∀ (dZ d0 : RDT) (ds : List RDT),
    (dZ :: d0 :: ds).map (fun d => (d.entry, d.kind)) = stretch Wr i (2 + P.lin.kCol) →
    ∀ (Cl W : Type) (nR : ℕ) (F : Frame) (base : ℕ) (rw : W → Wit GE nR ds.length)
      (Pin : S × F.E.Str → W → Prop) (on : S × F.E.Str → Prop)
      (_ : ∀ a w w', on a → Pin a w → Pin a w' → AgreeAt a.1.out.indexMasks (rw w) (rw w'))
      (_ : ∀ a τ b w, (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).ior.red.out a τ = some b →
        Pin b w → Pin a w),
      ({ pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds with
          err := Err.cap 128 (uLT (ckP .two) (dZ :: d0 :: ds)) } :
        Piece (ckP .two) F S Cl W).GoodIn on (FrontOk P) (RowsHoldA rw Pin) (RowsHoldA rw Pin)

theorem k13_law_at_cap {P : Where} {Wr : Rounds} {i : ℕ} (h : K13Called P Wr i) :
    K13LawAtCap P Wr i := by
  intro dZ d0 ds hd Cl W nR F base rw Pin on hdet hback
  obtain ⟨g, hb⟩ := h dZ d0 ds hd Cl W nR F base rw Pin on hdet hback
  exact goodIn_atCap (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds)
    (Err.le_cap_of_below_inv 128 _ hb) _ _ _ _ g

/-- **The law at the cap, of pieceAt: at any state and any block that goes by the batching.** -/
def K13AnyAtCap (P : Where) (Wr : Rounds) (i : ℕ) : Prop :=
  ∀ (dZ d0 : RDT) (ds : List RDT),
    (dZ :: d0 :: ds).map (fun d => (d.entry, d.kind)) = stretch Wr i (2 + P.lin.kCol) →
    ∀ (T Cl W : Type) (nR : ℕ) (F : Frame) (b : Block T Cl) (base : ℕ)
      (partF : T → Option Part) (rowB : T → List TensorRow) (_ : ByBatt b P partF rowB)
      (rw : W → Wit GE nR ds.length) (Pin : T × F.E.Str → W → Prop)
      (on on' : T × F.E.Str → Prop)
      (_ : ∀ a p w w', on a → partF a.1 = some p → Pin a w → Pin a w' →
        AgreeAt p.indexMasks (rw w) (rw w'))
      (_ : ∀ a τ b' w, on a →
        (pieceAt (W := W) F b P.rows base dZ d0 ds).ior.red.out a τ = some b' →
        Pin b' w → Pin a w)
      (_ : ∀ a τ b', on a →
        (pieceAt (W := W) F b P.rows base dZ d0 ds).ior.red.out a τ = some b' → on' b'),
      ({ pieceAt (W := W) F b P.rows base dZ d0 ds with
          err := Err.cap 128 (uLT (ckP .two) (dZ :: d0 :: ds)) } :
        Piece (ckP .two) F T Cl W).GoodIn on on'
        (fun a w => Pin a w ∧ ∀ p, partF a.1 = some p → ∀ r ∈ p.pile, Holds ρg (rw w) r)
        (fun a w => Pin a w ∧ ∀ r ∈ rowB a.1, Holds ρg (rw w) r)

theorem k13_any_at_cap {P : Where} {Wr : Rounds} {i : ℕ} (h : K13AtCap P Wr i) :
    K13AnyAtCap P Wr i := by
  intro dZ d0 ds hd T Cl W nR F b base partF rowB hb rw Pin on on' hdet hback hon
  obtain ⟨hD, -, hle⟩ := h dZ d0 ds hd
  exact goodIn_atCap (pieceAt (W := W) F b P.rows base dZ d0 ds) hle _ _ _ _
    (goodIn_any F P b base dZ d0 ds hD ds.length rfl partF rowB hb rw Pin on on' hdet hback hon)

/-- **In a proof file.** -/
theorem k13_law_at_cap_real : ∃ x : LinSized, realSized = some (x, codesFull2) ∧ AtRecord x ∧
    ∀ P : Where, P.rows = 13 → P.lin = x.shape → P.work = (0, 0, 0) →
      K13LawAtCap P dryProofFull.1 48270 ∧ K13AnyAtCap P dryProofFull.1 48270 := by
  obtain ⟨x, a1, a2, a3⟩ := k13_called_real
  obtain ⟨x', b1, -, b3⟩ := k13_at_cap_real
  obtain rfl : x' = x := by
    have := b1.symm.trans a1
    exact congrArg Prod.fst (Option.some.inj this)
  exact ⟨x', a1, a2, fun P h1 h2 h3 =>
    ⟨k13_law_at_cap (a3 P h1 h2 h3), k13_any_at_cap (b3 P h1 h2 h3)⟩⟩

/-- **In a key file.** -/
theorem k13_any_at_cap_key (P : Where) (h1 : P.rows = keyFull.ranges.pending)
    (h2 : P.lin = keyFull.once.shape) (h3 : P.work = (0, 0, 0)) :
    K13AnyAtCap P dryKeyFull.1 18828 := k13_any_at_cap (k13_at_cap_key P h1 h2 h3)

/-- **In a key file, at the planner's own numbers.** -/
theorem k13_any_at_cap_key_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {p : Model.Verify.Planned} (hp : Model.Verify.planned Z.pol Z.KL (some Z.lay) = .ok p)
    (P : Where) (h1 : P.rows = p.chains.made.sized.key.ranges.pending)
    (h2 : P.lin = p.chains.made.sized.key.once.shape) (h3 : P.work = (0, 0, 0)) :
    K13AnyAtCap P dryKeyFull.1 18828 :=
  k13_any_at_cap (k13_at_cap_key_at_scope hZ hp P h1 h2 h3)

end VerifiableInference.Desc.K13.Law
