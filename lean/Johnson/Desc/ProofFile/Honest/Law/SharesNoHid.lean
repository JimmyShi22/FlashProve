-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/SharesNoHid.lean: for a part whose second stop never fires,
nothing has to be proved for the second stop, whatever its first stop does (`stopDebt_no_hid`).
`StopDebt` (Honest/Law/SharesParts.lean) at `(· == some Why.hid)` bounds the probability of the
challenges at which the part is stopped by its second stop. `stopDebt_none` proves it for a part
that is never stopped at all. Here the first stop may fire. Probabilities are over the verifier's
messages, drawn uniformly (`Iop.prRho`), at a fixed private input and instance.

  1  `findSome_ne`   on lists: a value that the function never returns is not found
  2  `stopAt_not_hid`   where the second stop never fires, the part is not stopped by it
  3  `stopDebt_no_hid`   so `StopDebt` for the second stop holds at any number

Limits.
  * The hypothesis is on the part's definition: its second stop returns `none` at every input, every
    list of challenges heard before the part's own and every list of its own challenges. It is
    proved here of no part.
  * Nothing is said on first stops: for them `StopDebt` at `(·.isSome)` is another condition.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.SharesParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open scoped ENNReal
open OnBytes.Maker (RDT uLT drawnT)
open _root_.Run.PQ (CK)

variable {V W Y : Type}

/-- A value that the function never returns is not found. -/
theorem findSome_ne (f : Nat → Option Why) (y : Why) (h : ∀ j, f j ≠ some y) :
    ∀ l : List Nat, l.findSome? f ≠ some y
  | [] => by simp
  | j :: l => by
    have e1 : (j :: l).findSome? f = (f j).or (l.findSome? f) := by
      cases h' : f j <;> simp [h']
    rw [e1]
    cases hj : f j with
    | none => exact findSome_ne f y h l
    | some z =>
      intro e
      exact h j (hj.trans e)

/-- Where the second stop never fires, the part is not stopped by it. -/
theorem stopAt_not_hid (p : Part V W Y) (v : Option V) (loc ds : List Fmt.Drawn)
    (hh : ∀ u j, p.hid u loc (ds.take j) = none) : p.stopAt v loc ds ≠ some Why.hid := by
  unfold Part.stopAt
  refine findSome_ne _ _ (fun j => ?_) _
  have e : (v.bind fun u => p.hid u loc (ds.take j)) = none := by
    cases v with
    | none => rfl
    | some u => exact hh u j
  by_cases hb : (p.bad loc (ds.take j)).isSome = true
  · simp only [hb, if_true]
    intro c
    cases c
  · simp only [hb, Bool.false_eq_true, if_false, e, Option.isSome_none]
    intro c
    cases c

/-- **For a part whose second stop never fires nothing has to be proved for the second stop**: its
condition holds at any number. The first stop may fire. -/
theorem stopDebt_no_hid (C : CK) (v : Option V) (p : Part V W Y) (dsp : List RDT) (q : ℝ≥0∞)
    (hh : ∀ u l o, p.hid u l o = none) : StopDebt C (· == some Why.hid) v p dsp q := fun fr =>
  le_trans (Iop.prRho_empty _ fun ρ hρ => by
    have h' : (p.stopAt v fr (drawnT C dsp ρ) == some Why.hid) = true := hρ
    exact stopAt_not_hid p v fr _ (fun u _ => hh u _ _) (beq_iff_eq.1 h')) (zero_le _)

end ProofFile.Honest

#print axioms ProofFile.Honest.findSome_ne
#print axioms ProofFile.Honest.stopAt_not_hid
#print axioms ProofFile.Honest.stopDebt_no_hid
