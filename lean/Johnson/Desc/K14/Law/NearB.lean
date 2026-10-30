--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/NearB.lean: two of the shared chain's claims on the folded row, as tests with
code: for words that are given as the program's own elements, a function that computes whether the
claim holds, and the theorem that its yes gives the claim.

The claims are propositions over a field K, at words m : Words K (Johnson/Desc/Means/Says.lean):
LocAt and NearAt (Johnson/Desc/K14/Law/LocSound.lean, LocNear.lean) and RecAt and RecAll
(Johnson/Desc/K14/Law/RecSound.lean, RecRow.lean). Here the words are mE : Words E, elements as the
program computes with them, and they are read into K by a reading (OnBytes/Model/HideLaws.lean:
Reading): wordsOf.

  sumE, eqE, bitsE   a sum, eq(z, j) and the product over the set bits, by the program's
                     arithmetic, with val_sumE, val_eqE, val_bitsE: read into K they are the
                     field's.
  locAtB             (loc_x)'s equation at one location. locAt_of_B: a yes gives LocAt.
  farB, nearB        at how many locations it fails; whether these are at most e'. nearAt_of_B: a
                     yes gives NearAt.
  recAtB, recAllB    (rec_gamma)'s equation at one seed of the record; at all. recAll_of_B: a yes
                     gives RecAll.

The theorems hold at every reading, every record and all words; they have no premise but the yes.

What is not claimed. The converse: a no of a test does not give the claim's negation (two elements
of E that differ can read as one element of K). That any words are an honest prover's. Nothing on
soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K14.Law.LocNear
import Johnson.Desc.K14.Law.RecRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Means (Words)

variable {K : Type} [Field K] (ρ : OnBytes.Model.Reading K)

/-! ## The program's arithmetic, read -/

/-- The sum of f j over the j below n, by the program's addition. -/
def sumE (n : Nat) (f : Nat → E) : E := (List.range n).foldl (fun s j => addE s (f j)) zeroE

theorem val_sumE (n : Nat) (f : Nat → E) :
    ρ.val (sumE n f) = ∑ j ∈ Finset.range n, ρ.val (f j) := by
  unfold sumE
  induction n with
  | zero => simpa using ρ.zero
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ρ.add, ih,
      Finset.sum_range_succ]

/-- eq(z, j), by the program's arithmetic. -/
def eqE : List E → Nat → E
  | [], _ => oneE
  | x :: l, j => mulE (if j % 2 = 1 then x else subE oneE x) (eqE l (j / 2))

theorem val_eqE : ∀ (z : List E) (j : Nat), ρ.val (eqE z j) = eqK (z.map ρ.val) j
  | [], _ => ρ.one
  | x :: l, j => by
    show ρ.val (mulE (if j % 2 = 1 then x else subE oneE x) (eqE l (j / 2))) =
      (if j % 2 = 1 then ρ.val x else 1 - ρ.val x) * eqK (l.map ρ.val) (j / 2)
    rw [ρ.mul, val_eqE l]
    by_cases h : j % 2 = 1
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, ρ.sub, ρ.one]

/-- The product of the factors at the bits that are set in j, by the program's arithmetic. -/
def bitsE : List E → Nat → E
  | [], _ => oneE
  | x :: l, j => mulE (if j % 2 = 1 then x else oneE) (bitsE l (j / 2))

theorem val_bitsE : ∀ (z : List E) (j : Nat), ρ.val (bitsE z j) = bitsK (z.map ρ.val) j
  | [], _ => ρ.one
  | x :: l, j => by
    show ρ.val (mulE (if j % 2 = 1 then x else oneE) (bitsE l (j / 2))) =
      (if j % 2 = 1 then ρ.val x else 1) * bitsK (l.map ρ.val) (j / 2)
    rw [ρ.mul, val_bitsE l]
    by_cases h : j % 2 = 1
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, ρ.one]

/-- Words of the program's elements, read. -/
def wordsOf (mE : Words E) : Words K := fun o q i => ρ.val (mE o q i)

/-! ## (loc_x) -/

/-- The left side of (loc_x)'s equation at the location x, computed. -/
def locL (p : Par) (d : St) (mE : Words E) (x : Nat) : E :=
  addE (mulE (OnBytes.ofF (generatorAt p.S.fold.index.code x).messageScale)
      (sumE p.S.fold.index.code.ell fun j =>
        mulE (bitsE (((generatorAt p.S.fold.index.code x).f.map OnBytes.ofF).take
          p.S.fold.index.code.logEll) j)
          (mE d.loc.oU.oracle .main (d.loc.oU.lay.index j))))
    (mulE (OnBytes.ofF (generatorAt p.S.fold.index.code x).tailScale)
      (sumE p.S.fold.index.code.r fun j =>
        mulE (bitsE (((generatorAt p.S.fold.index.code x).f.map OnBytes.ofF).take
          p.S.fold.index.code.logR) j)
          (mE d.loc.oU.oracle .main (d.loc.oU.lay.index (p.S.fold.tailFirst + j)))))

/-- Its right side. -/
def locR (p : Par) (d : St) (tab : Nat → List UInt64) (x : Nat) : E :=
  sumE (weights p.S d.loc).size fun r =>
    mulE ((weights p.S d.loc).getD r zeroE) (OnBytes.ofF ((tab x).toArray.getD r 0))

/-- (loc_x)'s equation at the location x, computed. -/
def locAtB (p : Par) (d : St) (mE : Words E) (tab : Nat → List UInt64) (x : Nat) : Bool :=
  decide (locL p d mE x = locR p d tab x)

theorem locAt_of_B (p : Par) (d : St) (mE : Words E) (tab : Nat → List UInt64) (x : Nat)
    (h : locAtB p d mE tab x = true) : LocAt ρ p d (wordsOf ρ mE) tab x := by
  simp only [locAtB, decide_eq_true_eq] at h
  have e := congrArg ρ.val h
  simp only [locL, locR, ρ.add, ρ.mul, val_sumE, val_bitsE, List.map_take, List.map_map] at e
  unfold LocAt LocEq
  exact e

theorem len_filter_range (q : Nat → Bool) : ∀ N : Nat,
    ((List.range N).filter q).length = ((Finset.range N).filter fun x => q x = true).card
  | 0 => by simp
  | n + 1 => by
    have ih := len_filter_range q n
    by_cases h : q n = true
    · simp [List.range_succ, List.filter_append, Finset.range_add_one, Finset.filter_insert, h, ih]
    · simp [List.range_succ, List.filter_append, Finset.range_add_one, Finset.filter_insert, h, ih]

/-- At how many locations the equation fails, computed. -/
def farB (p : Par) (d : St) (mE : Words E) (tab : Nat → List UInt64) : Nat :=
  ((List.range (2 ^ p.S.fold.index.code.logN)).filter fun x => !locAtB p d mE tab x).length

/-- Is it at most e'? -/
def nearB (p : Par) (d : St) (mE : Words E) (tab : Nat → List UInt64) (e' : Nat) : Bool :=
  decide (farB p d mE tab ≤ e')

open Classical in
theorem nearAt_of_B (p : Par) (d : St) (mE : Words E) (tab : Nat → List UInt64) (e' : Nat)
    (h : nearB p d mE tab e' = true) : NearAt ρ p d (wordsOf ρ mE) tab e' := by
  simp only [nearB, decide_eq_true_eq] at h
  unfold NearAt
  refine le_trans ?_ h
  unfold farB
  rw [len_filter_range]
  refine Finset.card_le_card_of_injOn (fun x => x.val) ?_ (fun a _ b _ e => Fin.ext e)
  intro x hx
  have hx' := (Finset.mem_filter.1 hx).2
  refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_range.2 x.isLt, ?_⟩)
  cases hb : locAtB p d mE tab x.val with
  | false => rfl
  | true => exact absurd (locAt_of_B ρ p d mE tab x.val hb) hx'

/-! ## (rec_gamma) -/

def recL (p : Par) (d : St) (mE : Words E) (x : SampleSeed × Nat) : E :=
  addE (sumE p.S.fold.index.plain fun k =>
      mulE (eqE x.1.z k) (mE d.loc.oU.oracle .main (d.loc.oU.lay.index k)))
    (sumE 3 fun t => mulE (mulE x.1.beta (thetaE t))
      (mE d.loc.oU.oracle .main (d.loc.oU.lay.index (p.S.fold.index.padPlace x.2 t))))

def recR (p : Par) (d : St) (x : SampleSeed × Nat) : E :=
  sumE p.S.fold.index.rows fun r => mulE ((weights p.S d.loc).getD r zeroE)
    (d.loc.key.record.getD (r * p.S.fold.index.answers + x.2) zeroE)

/-- (rec_gamma)'s equation at a seed of the record with its number, computed. -/
def recAtB (p : Par) (d : St) (mE : Words E) (x : SampleSeed × Nat) : Bool :=
  decide (recL p d mE x = recR p d x)

theorem recAt_of_B (p : Par) (d : St) (mE : Words E) (x : SampleSeed × Nat)
    (h : recAtB p d mE x = true) : RecAt ρ p d (wordsOf ρ mE) x := by
  simp only [recAtB, decide_eq_true_eq] at h
  have e := congrArg ρ.val h
  simp only [recL, recR, ρ.add, ρ.mul, val_sumE, val_eqE] at e
  unfold RecAt RecEq
  exact e

/-- At every seed of the record. -/
def recAllB (p : Par) (d : St) (mE : Words E) : Bool :=
  d.loc.key.seeds.zipIdx.all fun x => recAtB p d mE x

theorem recAll_of_B (p : Par) (d : St) (mE : Words E) (h : recAllB p d mE = true) :
    RecAll ρ p d (wordsOf ρ mE) :=
  fun x hx => recAt_of_B ρ p d mE x (List.all_eq_true.1 h x hx)

end Desc.K14.Law
