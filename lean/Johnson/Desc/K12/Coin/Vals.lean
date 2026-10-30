-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Coin/Vals.lean: THE BATCHING's CONVERSE, FROM A COUNT OF TYPED VALUES TO THE COUNT
OF CHALLENGES. Definitions, statements and proofs.

An error of a written round counts values of its challenge: blocks of a hash's output, with bits of
work. What is proved of a batching counts values of the drawn element. Between the two stands the
format's sampler: at most w challenges that pass the test of work are read as one tuple of typed
values (`chalTo_fib`, OnBytes/Slice/Draws.lean).

  `cnt_by_vals`: for a round's data d and a property P of its typed values: the challenges that pass
    the work and whose typed values have P are at most (the values with P) · w.
  `rvOf`: "BAT"'s round as a view shows it, of the message and the typed values. `r0Of_vals`: that
    is `r0Of` (Sheet.lean) at a challenge's typed values: by unfolding.
  `BatVals`: `BatAtN` (LawN.lean) with typed values in the challenges' place, at a count v₀.
  `batAtN_of_vals`: `BatVals` at v₀ gives `BatAtN` at e₀ := v₀ · w, where the round's positions have
    at most 64 bits.
Limits: `BatVals` is paid by nobody here. A typed value of a round that draws one element is that
element in the field and nothing else only where `Fmt.dsOf` says so: not looked at here. No
soundness is claimed.
A tool.
-/
import Johnson.Desc.K12.Coin.LawN
import OnBytes.Flat.RoundsT

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker OnBytes.Flat
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open H2K.JointK (yOf)
open H2K.Pub (sgOf)
open H2K.First (gpL Plain)

theorem cnt_by_vals (d : PQ.RD) (hlog : d.entry.logN ≤ 64)
    (P : Vals .two (Fmt.dsOf d.entry d.kind) → Prop) :
    cnt (fun c : (wRound d).Chal => GChal.pass (b := d.entry.work) c = true ∧ P (valsOf d c)) ≤
      cnt P * (bsRound .two d.entry d.kind).w := by
  refine le_trans (cnt_mono fun c hc => ?_)
    (cnt_some_le (chalTo d id) (chalTo_fib d id Function.injective_id hlog) P)
  refine ⟨valsOf d c, ?_, hc.2⟩
  unfold chalTo
  rw [if_pos hc.1]
  rfl

/-- "BAT"'s round as a view shows it, of the message and the round's typed values. -/
def rvOf (dB : RDT) (m : (roundT (ckP .two) dB).up.Msg)
    (v : Vals .two (Fmt.dsOf dB.entry dB.kind)) : Fmt.RoundView :=
  ⟨PQ.PlainOf.gots dB.items (GPlain.old (b := dB.entry.work) m.2), drawnOf .two dB.entry dB.kind v⟩

theorem r0Of_vals (dB : RDT) (m : (roundT (ckP .two) dB).up.Msg)
    (c : (roundT (ckP .two) dB).up.Chal) : r0Of dB m c = rvOf dB m (valsOf (toRD dB) c) := rfl

/-- The batching's converse at one statement, towards N, counted in typed values. -/
def BatVals (F : Frame) (π : P12) (no : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (dB : RDT) (v₀ : ℕ)
    (N : ConclK F) (x : T12 × F.E.Str) : Prop :=
  ∀ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (row₀ : GroupRow) (hok : H2K.First.ok (gpL π a row₀ D) = true), Fixes π x.1 a rest G0 Ly D →
    ∀ m : (roundT (ckP .two) dB).up.Msg,
    cnt (fun v : Vals .two (Fmt.dsOf dB.entry dB.kind) =>
      ∃ (row : GroupRow) (w : (sgOf a).cIn.N.Wit),
        First.Close.bat x.1.st x.1.g dB.entry (noDigest (rvOf dB m v)) =
          .ok (row, Ly, begun x.1.st x.1.g G0) ∧
        (sgOf a).RIn (rad (sgOf a))
          (stmG (sgOf a) row, yOf π a row₀ D hok rd (W0 F no D.book x.2)) w ∧
        ¬ N x a rest G0 Ly D) ≤ v₀

theorem batAtN_of_vals (F : Frame) (π : P12) (no : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (dB : RDT)
    (v₀ : ℕ) (N : ConclK F) (x : T12 × F.E.Str) (hlog : dB.entry.logN ≤ 64)
    (h : BatVals F π no rad rd dB v₀ N x) :
    BatAtN F π no rad rd dB (v₀ * (bsRound .two dB.entry dB.kind).w) N x := by
  intro a rest G0 Ly D row₀ hok hf m
  have h1 := cnt_by_vals (toRD dB) hlog fun v =>
    ∃ (row : GroupRow) (w : (sgOf a).cIn.N.Wit),
      First.Close.bat x.1.st x.1.g dB.entry (noDigest (rvOf dB m v)) =
        .ok (row, Ly, begun x.1.st x.1.g G0) ∧
      (sgOf a).RIn (rad (sgOf a))
        (stmG (sgOf a) row, yOf π a row₀ D hok rd (W0 F no D.book x.2)) w ∧
      ¬ N x a rest G0 Ly D
  refine le_trans (le_trans (cnt_mono ?_) h1)
    (Nat.mul_le_mul_right _ (h a rest G0 Ly D row₀ hok hf m))
  rintro c ⟨hp, row, w, hb, hr, hn⟩
  rw [r0Of_vals] at hb
  exact ⟨hp, row, w, hb, hr, hn⟩

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.cnt_by_vals
#print axioms VerifiableInference.Desc.K12.Coin.batAtN_of_vals
