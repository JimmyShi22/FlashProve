-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/U3LaysOfSized.lean: WHERE THE DATA OF THE MESSAGES "U3"
(`u3Rows`, Johnson/HonestTrace/U3Rows.lean, another group of authors', a file that is not in this
library) LAY AN ELEMENT HANGS ON THE COVERED POSITIONS THROUGH ONE Bool ALONE: THE VERIFIER's TEST
ON THEIR FOUR ARRAYS' SIZES (`Head.Covered.sized`, OnBytes/Model/HeadLayout.lean) AT THE HEAD's
NUMBER OF POSITIONS. FACTS ON THAT FILE's TERMS: GUESTS IN THIS FOLDER: typed for
LightHangsOnSized.lean beside it. PUBLIC DATA ALONE: the public part, the ground, covered positions
of a request. Lemmas with their proofs; no definition; none of the library's goals.

  `map_bind_congr`      a helper: two binds of one first step read alike behind a reading φ where
                        their second steps do
  `lookup_congr`        a helper: the like of a lookup in a list of pairs (l, f l)
  `headVals_n_congr`    where the Bool is the same at cov and cov': `headVals` returns at both or at
                        neither, with one number of reads
  `valsAt_n_congr`      so `valsAt`, at every segment
  `u3Vals_size_congr`   so the field size of `u3Vals`
  `u3Rows_lays_congr`   SO THE FIELD lays OF `u3Rows`

How. `headVals` asks one test of the covered positions; the number of reads that it returns is the
plan's. `valsAt` hands them to `headVals` alone. `u3Vals`' field size reads of what `valsAt` returns
that number alone; `laidData`'s field lays (Honest/LaidData.lean) reads of the values their field
size alone.

WHAT IT IS NOT. NOTHING ON THE FIELDS entry AND ready: both read the covered positions themselves.
That the data lay anything anywhere is not said. NEAR. `map_bind`, `bind_congr'`
(Johnson/Goal/Meaning/ScopeScan.lean): the library's helpers on two steps in a row: the first helper
here is their like behind a reading of what is returned.

Limits. Unfoldings. Nothing on any property.
-/
import Johnson.HonestTrace.U3Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes.HonestTrace.U3 (SegVals headVals valsAt u3Vals u3Rows)

/-- Two binds of one first step read alike behind φ where their second steps do. -/
theorem map_bind_congr {α β γ : Type} (x : Except String α) (f g : α → Except String β)
    (φ : β → γ) (h : ∀ a, (f a).toOption.map φ = (g a).toOption.map φ) :
    (x >>= f).toOption.map φ = (x >>= g).toOption.map φ := by
  cases x with
  | error e => rfl
  | ok a => exact h a

/-- The like of a lookup in a list of pairs (l, f l). -/
theorem lookup_congr {β γ : Type} (L : List Nat) (f g : Nat → Except String β) (φ : β → γ)
    (h : ∀ l, (f l).toOption.map φ = (g l).toOption.map φ) (k : Nat) :
    (((L.map fun l => (l, f l)).lookup k).bind (·.toOption)).map φ =
      (((L.map fun l => (l, g l)).lookup k).bind (·.toOption)).map φ := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.map_cons, List.lookup_cons]
    cases k == a with
    | true => exact h a
    | false => exact ih

variable {Z : ProofFile.Pub} {G : ProofFile.Ground} {cov cov' : OnBytes.Model.Head.Covered}

/-- The head's values: returned at both or at neither, with one number of reads. -/
theorem headVals_n_congr (h : cov.sized G.W.hS.T = cov'.sized G.W.hS.T) (sps : List ProofFile.Spot)
    (seg : Nat) {γ : Type} (φ : Nat → γ) :
    (headVals Z G cov sps seg).toOption.map (fun V => φ V.n) =
      (headVals Z G cov' sps seg).toOption.map (fun V => φ V.n) := by
  unfold headVals
  dsimp only
  rw [h]
  refine map_bind_congr _ _ _ _ fun k6 => ?_
  refine map_bind_congr _ _ _ _ fun k3 => ?_
  refine map_bind_congr _ _ _ _ fun _ => ?_
  refine map_bind_congr _ _ _ _ fun _ => ?_
  refine map_bind_congr _ _ _ _ fun _ => ?_
  refine map_bind_congr _ _ _ _ fun _ => ?_
  simp only [pure, Except.pure, Except.toOption, Option.map]

/-- The values at a segment: the like. -/
theorem valsAt_n_congr (h : cov.sized G.W.hS.T = cov'.sized G.W.hS.T) (seg : Nat) {γ : Type}
    (φ : Nat → γ) :
    (valsAt Z G cov seg).toOption.map (fun V => φ V.n) =
      (valsAt Z G cov' seg).toOption.map (fun V => φ V.n) := by
  unfold valsAt
  refine map_bind_congr _ _ _ _ fun sps => ?_
  refine map_bind_congr _ _ _ _ fun Y => ?_
  refine map_bind_congr _ _ _ _ fun _ => ?_
  refine map_bind_congr _ _ _ _ fun _ => ?_
  split
  · rfl
  · split
    · rfl
    · split
      · exact headVals_n_congr h sps seg φ
      · rfl

/-- The field size of the values. -/
theorem u3Vals_size_congr (h : cov.sized G.W.hS.T = cov'.sized G.W.hS.T) :
    (u3Vals Z G cov).size = (u3Vals Z G cov').size := by
  funext l name
  unfold u3Vals
  dsimp only
  split
  · exact lookup_congr _ _ _ _ (fun s => valsAt_n_congr h s fun n => (1, n)) l
  · rfl

/-- **Where the data lay an element hangs on the covered positions through the Bool alone.** -/
theorem u3Rows_lays_congr (h : cov.sized G.W.hS.T = cov'.sized G.W.hS.T) :
    (u3Rows Z G cov).lays = (u3Rows Z G cov').lays := by
  unfold u3Rows OnBytes.HonestTrace.laidRows ProofFile.Honest.laidData
  dsimp only
  rw [u3Vals_size_congr h]

end ProofFile.Honest.K2.Law

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K2.Law.map_bind_congr
#print axioms ProofFile.Honest.K2.Law.lookup_congr
#print axioms ProofFile.Honest.K2.Law.headVals_n_congr
#print axioms ProofFile.Honest.K2.Law.valsAt_n_congr
#print axioms ProofFile.Honest.K2.Law.u3Vals_size_congr
#print axioms ProofFile.Honest.K2.Law.u3Rows_lays_congr
