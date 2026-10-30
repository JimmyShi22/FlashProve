-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05SeamSilly.lean: THE SEAM AND THE LAW's FORM AGAINST THE TWO SILLY TEXTS: a
block with the kind's ROUNDS whose decision says yes to all and hands the record on (`k5Yes`), and
one whose decision says no to all (`k5No`), each at the kind's own written rounds.

Main names:
  `yes_out`: the yes-text puts out the record as it came, at every written transcript whose work
    passes.
  `yes_not_seam`: IT DOES NOT MEET hyes: at a record at which something is owed it puts out, and the
    kind's own decide refuses there. So a tooth sits in the seam: hyes names the kind's own decide.
  `LtPass`, `not_doomed_of_pass`: GENERAL: towards a property that fails at every written
    transcript whose work passes the prover has not lost, at errors each below its round's number
    of verifier's messages that pass the work.
  `ltPass_of_below`: errors that are shares of at most 2^-k of their rounds' verifier's messages
    (Err.Below, Iop/InteractiveOracleProof.lean), at rounds with fewer than k bits of work, have LtPass.
  `yes_not_keeps`: **THE LAW's FORM FAILS AT THE YES-TEXT**: KeepsW on on' R R' ε fails, at every ε
    with LtPass, wherever there are a statement a with "on" and a world w such that what stands in
    front fails at (a, w) and what stands behind holds at w at the record as it came, whatever the
    oracles.
  `no_out`, `no_keeps`: the no-text never puts out; it has the form KeepsW at all letters and all
    errors, for nothing: the form says nothing on acceptance. What shuts it out is
    `seam_accepts` (Att/K05SeamBack.lean), which fails of it.

Limits. `yes_not_keeps` is at letters: that there are such a and w at the law's own letters (Todo
fails at (x0 a, part w); R' holds at the record in front) is a premise: no member is shown. By
BillsAllJ (Att/K05KeepsAny.lean) R' is bound only at records that the seat's lay returns: at a seat
whose lay marks the record, a record in front is none. That the law's own errors (bearErr …) have
LtPass is shown in Att/K05SeamParts.lean, from a yes of the Boolean k5Held, which is evaluated in no
file of this tree.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05SeamBack
import Johnson.Desc.Plain.World
import Iop.GrindProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob OnBytes OnBytes.Model OnBytes.Flat OnBytes.Maker Fo.Peel
open VerifiableInference.Desc (Block roundsFit noDigest)
open VerifiableInference.Desc.Sound (Frame Piece)
open _root_.Run (ckP)
open _root_.Run.PQ (CK)

section
variable {S Cl W : Type} {F : Frame}

/-- The kind's text with a decision that says yes to all and hands the record on. -/
def k5Yes (seat : Seat S) (claims : List (String × (Nat → S → Except String (List Cl × S))))
    (p : Par) : Block S Cl := { attentionKind seat claims p with decide := fun s _ _ => .ok s }

/-- The kind's text with a decision that says no to all. -/
def k5No (seat : Seat S) (claims : List (String × (Nat → S → Except String (List Cl × S))))
    (p : Par) : Block S Cl := { attentionKind seat claims p with decide := fun _ _ _ => .error "no" }

/-- Any block at the kind's written rounds; the extractor hands the witness through. -/
abbrev pieceAt (b : Block S Cl) (p : Par) (base : ℕ) (err : Err (uLT (ckP .two) (written p))) :
    Piece (ckP .two) F S Cl W := ⟨b, base, written p, [], fun _ _ w => w, err⟩

theorem yes_out (seat : Seat S) (claims : List (String × (Nat → S → Except String (List Cl × S))))
    (p : Par) (base : ℕ) (err : Err (uLT (ckP .two) (written p))) (a : S × F.E.Str)
    (τ : Tr (uLT (ckP .two) (written p)))
    (hp : passT (ckP .two) (written p) (rhoT (ckP .two) (written p) τ) = true) :
    (pieceAt (W := W) (F := F) (k5Yes seat claims p) p base err).ior.red.out a τ =
      some (a.1, (pieceAt (W := W) (F := F) (k5Yes seat claims p) p base err).ior.imp a.2 τ) :=
  block_out (k5Yes seat claims p) p rfl base _ err a τ a.1 hp rfl

/-- **The yes-text does not meet hyes.** -/
theorem yes_not_seam (seat : Seat S)
    (claims : List (String × (Nat → S → Except String (List Cl × S)))) (p : Par) (base : ℕ)
    (err : Err (uLT (ckP .two) (written p))) (a : S × F.E.Str) (n : ℕ)
    (ho : seat.owed a.1 = some n) (τ : Tr (uLT (ckP .two) (written p)))
    (hp : passT (ckP .two) (written p) (rhoT (ckP .two) (written p) τ) = true) :
    ∃ b, (pieceAt (W := W) (F := F) (k5Yes seat claims p) p base err).ior.red.out a τ = some b ∧
      decide seat p a.1 ((rvT (ckP .two) (written p) τ).map noDigest) ≠ .ok b.1 := by
  refine ⟨_, yes_out seat claims p base err a τ hp, fun h => ?_⟩
  have := ((decide_lays seat p a.1 _ _).1 h).1
  rw [ho] at this
  cases this

end

/-- Each error is below its round's number of verifier's messages that pass the work. -/
def LtPass (C : CK) : (ds : List RDT) → Err (uLT C ds) → Prop
  | [], _ => True
  | d :: ds, (e, ε) =>
    e < cnt (fun c : (roundT C d).up.Chal => GChal.pass (b := d.entry.work) c = true) ∧
      LtPass C ds ε

/-- Towards a property that fails wherever the work passes, the prover has not lost at such
errors. -/
theorem not_doomed_of_pass (C : CK) : ∀ (ds : List RDT) (ε : Err (uLT C ds))
    (bad : Tr (uLT C ds) → Prop), LtPass C ds ε →
    (∀ τ, passT C ds (rhoT C ds τ) = true → ¬ bad τ) → ¬ Doomed (uLT C ds) ε bad
  | [], _, _, _, h => fun hd => h () rfl hd
  | d :: ds, (e, ε), bad, hl, h => fun hd => by
    have h1 : cnt (fun c : (roundT C d).up.Chal => ¬ Doomed (uLT C ds) ε
        (fun τ => bad (((roundT C d).up.dOrc, (roundT C d).up.dPlain), c, τ))) ≤ e :=
      hd ((roundT C d).up.dOrc, (roundT C d).up.dPlain)
    have h2 : cnt (fun c : (roundT C d).up.Chal => GChal.pass (b := d.entry.work) c = true) ≤
        cnt (fun c : (roundT C d).up.Chal => ¬ Doomed (uLT C ds) ε
          (fun τ => bad (((roundT C d).up.dOrc, (roundT C d).up.dPlain), c, τ))) :=
      cnt_mono fun c hc => not_doomed_of_pass C ds ε _ hl.2 fun τ hτ =>
        h (((roundT C d).up.dOrc, (roundT C d).up.dPlain), c, τ) (by
          show (GChal.pass (b := d.entry.work) c && passT C ds (rhoT C ds τ)) = true
          rw [hc, hτ]
          rfl)
    exact absurd (le_trans h2 h1) (not_le.2 hl.1)

open scoped ENNReal in
/-- Errors that are shares of at most 2^-k of their rounds' verifier's messages, at rounds with
fewer
than k bits of work, are each below the number of messages that pass the work. -/
theorem ltPass_of_below (C : CK) (k : ℕ) : ∀ (ds : List RDT) (ε : Err (uLT C ds)),
    Err.Below ε ((2 : ℝ≥0∞)⁻¹ ^ k) → (∀ d ∈ ds, d.entry.work < k) → LtPass C ds ε
  | [], _, _, _ => trivial
  | d :: ds, (e, ε), hb, hw => by
    refine ⟨?_, ltPass_of_below C k ds ε hb.2 fun x hx => hw x (List.mem_cons_of_mem _ hx)⟩
    have hc : cnt (fun c : GChal d.entry.work (C.Ch d.entry d.kind) => GChal.pass c = true) =
        Fintype.card (C.Ch d.entry d.kind) := by
      have h0 := GChal.cnt_pass d.entry.work (fun _ : C.Ch d.entry d.kind => True)
      simp only [and_true] at h0
      rw [h0, cnt_true]
    show e < cnt (fun c : GChal d.entry.work (C.Ch d.entry d.kind) => GChal.pass c = true)
    rw [hc]
    have h1 : (e : ℝ≥0∞) ≤ (2 : ℝ≥0∞)⁻¹ ^ k *
        (Fintype.card (GChal d.entry.work (C.Ch d.entry d.kind)) : ℝ≥0∞) := hb.1
    rw [GChal.card_eq] at h1
    have h2 : (e : ℝ≥0∞) * 2 ^ k ≤
        ((Fintype.card (C.Ch d.entry d.kind) * 2 ^ d.entry.work : ℕ) : ℝ≥0∞) := by
      calc (e : ℝ≥0∞) * 2 ^ k
          ≤ ((2 : ℝ≥0∞)⁻¹ ^ k *
              ((Fintype.card (C.Ch d.entry d.kind) * 2 ^ d.entry.work : ℕ) : ℝ≥0∞)) * 2 ^ k :=
            by gcongr
        _ = ((Fintype.card (C.Ch d.entry d.kind) * 2 ^ d.entry.work : ℕ) : ℝ≥0∞) *
              ((2 : ℝ≥0∞)⁻¹ ^ k * 2 ^ k) := by ring
        _ = _ := by
            rw [← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow, mul_one]
    have h3 : e * 2 ^ k ≤ Fintype.card (C.Ch d.entry d.kind) * 2 ^ d.entry.work := by
      exact_mod_cast h2
    by_contra hge
    have hN : 0 < Fintype.card (C.Ch d.entry d.kind) := Fintype.card_pos
    have h4 : Fintype.card (C.Ch d.entry d.kind) * 2 ^ k ≤
        Fintype.card (C.Ch d.entry d.kind) * 2 ^ d.entry.work :=
      le_trans (Nat.mul_le_mul_right _ (not_lt.1 hge)) h3
    have h5 : 2 ^ k ≤ 2 ^ d.entry.work := Nat.le_of_mul_le_mul_left h4 hN
    have h6 : k ≤ d.entry.work := (Nat.pow_le_pow_iff_right (by norm_num)).1 h5
    exact absurd (hw d List.mem_cons_self) (not_lt.2 h6)

section
variable {S Cl W : Type} {F : Frame}

/-- **The law's form fails at the yes-text.** -/
theorem yes_not_keeps (seat : Seat S)
    (claims : List (String × (Nat → S → Except String (List Cl × S)))) (p : Par) (base : ℕ)
    (ε : Err (uLT (ckP .two) (written p))) (hε : LtPass (ckP .two) (written p) ε)
    (on on' : S × F.E.Str → Prop) (R R' : S × F.E.Str → W → Prop) (a : S × F.E.Str) (w : W)
    (ha : on a) (hR : ¬ R a w) (hR' : ∀ y', R' (a.1, y') w) :
    ¬ (pieceAt (W := W) (F := F) (k5Yes seat claims p) p base ε).ior.red.KeepsW on on' R R' ε := by
  intro h
  refine not_doomed_of_pass (ckP .two) (written p) ε _ hε (fun τ hτ hb => ?_) (h a ha)
  exact hR ((hb _ (yes_out seat claims p base ε a τ hτ)).2 w (hR' _))

/-- The no-text never puts out. -/
theorem no_out (seat : Seat S) (claims : List (String × (Nat → S → Except String (List Cl × S))))
    (p : Par) (base : ℕ) (err : Err (uLT (ckP .two) (written p))) (a : S × F.E.Str)
    (τ : Tr (uLT (ckP .two) (written p))) (b : S × F.E.Str) :
    (pieceAt (W := W) (F := F) (k5No seat claims p) p base err).ior.red.out a τ ≠ some b := by
  intro h
  obtain ⟨_, ⟨cols, k, hs⟩, _⟩ :=
    piece_out_step (pieceAt (W := W) (F := F) (k5No seat claims p) p base err) rfl a b τ h
  obtain ⟨_, gs, hd⟩ := VerifiableInference.Desc.Keeps.step_fit _ _ _ _ _ _ _ hs
  cases hd

/-- It has the law's form at all letters and all errors, for nothing. -/
theorem no_keeps (seat : Seat S) (claims : List (String × (Nat → S → Except String (List Cl × S))))
    (p : Par) (base : ℕ) (ε : Err (uLT (ckP .two) (written p))) (on on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop) :
    (pieceAt (W := W) (F := F) (k5No seat claims p) p base ε).ior.red.KeepsW on on' R R' ε :=
  fun a _ => Doomed.of_forall _ _ fun τ b hb => absurd hb (no_out seat claims p base ε a τ b)

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.yes_not_seam
#print axioms VerifiableInference.Desc.First.Att.P.not_doomed_of_pass
#print axioms VerifiableInference.Desc.First.Att.P.ltPass_of_below
#print axioms VerifiableInference.Desc.First.Att.P.yes_not_keeps
#print axioms VerifiableInference.Desc.First.Att.P.no_keeps
