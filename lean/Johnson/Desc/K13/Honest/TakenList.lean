-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Honest/TakenList.lean: UNDER `LedgerAt d.st o k` (the ledger of the oracle message
o is that of k takes since it was made: Johnson/Desc/K13/Law/LedgerWithin.lean) THE GROUND's TAKE OF
n MASK ENTRIES (`takeMasksP`, Johnson/Desc/First/Base/Ground.lean), WHERE IT RETURNS, HANDS OUT JUST
THE NUMBERS `takenNo R k`, …, `takenNo R (k + n - 1)`, IN THAT ORDER, R the message's number of mask
rows; AND, WHERE THE SHAPE HAS AN ANSWER, A FREE ENTRY IS NO PLACE OF THE PAD (`padB`,
Johnson/Desc/SeatAt.lean). Four statements with their proofs (`numbers_succ`: a step on lists); no
definition. Of the verifier's own text alone: no prover, no witness.

Main names: `takeMasksInto_numbers`, `takeMasksP_numbers`: **the list.** `free_off_pad`: **where the
shape has at least one answer and k is below the count of free entries, (row k % R, place k / R) of
the mask table is no place of the pad.**

Why. Kind K13's batching takes 1 + 2 kCol entries at once, and what is said of them is read at the
one state in front of the taking: so each entry's number is wanted as a function of k and its place
in the list. With `OnBytes.Road.K4.Rec.mask_entry_at` (Johnson/Road/K4/Rec/MaskEntry.lean), which is
stated at `takenNo R k` at every k, the list gives what the reader of the rows on the table reads at
each.

How. The list: by induction on n, as `takeMasksInto_within` (LedgerWithin.lean): one take by
`takeMaskP_is` (LedgerBound.lean) and `nextOf_no` (LedgerNo.lean); behind it the ledger is that of k
+ 1 takes (`takeMaskP_within`) and the message has its shape (`layLedger_at`). The pad: arithmetic
on the count.

Nearest kin. `Fo.Hands.takes_eq` (Johnson/Top/H/Hands/HandsCore.lean): the closed form of n takings
ON A BARE LEDGER (`takesOf`), with `realAt_takenNo`: it cannot be called here: that `takeMasksP` is
`takesOf` on the ledger that the statement holds is shown in no file of the library (so that file's
own head). `takeMasksP_within`, `takeMasksP_real` (RealReached.lean), `takeMasks_sorted` (Fresh.lean
of this folder): the entries lie within the table, are real, rise strictly: none gives their
numbers. `takeMasks_list` (ShapeSim.lean of this folder): two states with one ledger hand out one
list: not which. `takeMaskP_bound` (LedgerBound.lean): one take's number. For the pad: THE NEAREST:
`Meaning.mask_arith` and `Meaning.mask_geometry` (Johnson/Goal/Meaning/MaskInside.lean): the first
has this arithmetic as its third clause; the second has `padB … = false` where the number of mask
rows is a power of two, which is not asked here; that file's `tooth_answers` shows that the premise
1 ≤ answers cannot be dropped. They are not called: that file lies under Johnson/Goal/, which this
folder's files do not import. `nextOf_no_pad` (LedgerBound.lean): against the indices of
`Send.pad`'s places; `Fmt.Places.freeAt_ne_pad` (Fmt/PlacesLaws.lean): against the format page's
`padRow` and `padEntry`; these two do not name `padB`.

Limits. Conditional: that a state's ledger has `LedgerAt` at any k is shown here of no state; where
the taking does not return nothing is said. `padB` is the pad AT ONE ANSWER (its own docstring): at
more answers `free_off_pad` still holds, and says less than that the entry is off the whole pad.

What is not claimed. Anything on a prover, a witness or a coin. It is none of the library's goals.
Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.K13.Law.LedgerNo
import Johnson.Desc.K13.Law.LedgerBound
import Johnson.Desc.SeatAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes
open VerifiableInference.Desc.Ground (takeMaskP takeMasksInto takeMasksP)
open VerifiableInference.Desc.K13.Law
open Desc.Plain (DState)

variable {L : Type}

/-- The numbers from k on: the first, then those from k + 1 on. -/
theorem numbers_succ (R k n : ℕ) :
    ((List.range (n + 1)).map fun j => takenNo R (k + j)) =
      takenNo R k :: (List.range n).map fun j => takenNo R (k + 1 + j) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  refine congrArg (takenNo R k :: ·) (List.map_congr_left fun j _ => ?_)
  show takenNo R (k + (j + 1)) = takenNo R (k + 1 + j)
  rw [Nat.add_assoc, Nat.add_comm 1 j]

/-- **The loop of the taking, under `LedgerAt`**: CONDITIONAL: where it returns, it appends to what
was taken before just the numbers of the takes k, k + 1, …, k + n - 1. x: the message o. -/
theorem takeMasksInto_numbers (o : ℕ) : ∀ (n : ℕ) (d : DState L) (acc : Array ℕ)
    (t : List ℕ × DState L) (k : ℕ) (x : OnBytes.Oracle), LedgerAt d.st o k →
    d.st.oracles[o]? = some x → takeMasksInto o n d acc = some t →
    t.1 = acc.toList ++ (List.range n).map fun j => takenNo x.shape.maskRows (k + j)
  | 0, d, acc, t, k, x, _, _, ht => by
    have e : some (acc.toList, d) = some t := ht
    rw [← Option.some.inj e]
    simp
  | n + 1, d, acc, t, k, x, h, hx, ht => by
    unfold takeMasksInto at ht
    cases hm : takeMaskP d o with
    | none =>
      rw [hm] at ht
      cases ht
    | some q =>
      obtain ⟨i, d'⟩ := q
      rw [hm] at ht
      have h3 := (takeMaskP_within h hm).2.2
      obtain ⟨l, hl, _, hi, hd⟩ := takeMaskP_is hm
      rw [hx] at hl
      have hl' : x.ledger = some l := hl
      have hx' : d'.st.oracles[o]? = some { x with ledger := some (taken l) } := by
        rw [hd]
        exact layLedger_at hx (taken l)
      have ih : t.1 = (acc.push i).toList ++
          (List.range n).map fun j => takenNo x.shape.maskRows (k + 1 + j) :=
        takeMasksInto_numbers o n d' (acc.push i) t (k + 1) { x with ledger := some (taken l) } h3
          hx' ht
      rw [ih, numbers_succ, Array.toList_push, List.append_assoc, hi, nextOf_no h hx hl']
      rfl

/-- **The ground's take of n entries, under `LedgerAt`**: CONDITIONAL: where it returns, it hands
out just the numbers of the takes k, k + 1, …, k + n - 1, in that order. -/
theorem takeMasksP_numbers {d : DState L} {o k n : ℕ} {x : OnBytes.Oracle}
    {t : List ℕ × DState L}
    (h : LedgerAt d.st o k) (hx : d.st.oracles[o]? = some x) (ht : takeMasksP d o n = some t) :
    t.1 = (List.range n).map fun j => takenNo x.shape.maskRows (k + j) := by
  have e := takeMasksInto_numbers o n d #[] t k x h hx ht
  rw [e]
  rfl

/-- **A free entry is no place of the pad**: CONDITIONAL: the shape has at least one answer (h1),
and k is below its count of free mask entries. -/
theorem free_off_pad (cs : Codes) (sh : OracleShape) (k : ℕ) (h1 : 1 ≤ sh.answers)
    (hk : k < Send.freeMaskEntries sh.maskRows (cs.mask.getD sh.maskCode default).ell
      sh.answers) :
    padB cs sh true (k % sh.maskRows) (k / sh.maskRows) = false := by
  unfold padB
  rw [if_pos rfl, Bool.and_eq_false_iff]
  generalize (cs.mask.getD sh.maskCode default).ell = e at hk ⊢
  have hk' : sh.answers ≤ e ∧ k < sh.maskRows * (e - sh.answers) + (sh.maskRows - 1) := by
    unfold Send.freeMaskEntries at hk
    split at hk
    · exact absurd hk (Nat.not_lt_zero _)
    · rename_i hc
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or, Nat.not_lt] at hc
      exact ⟨hc.2, hk⟩
  by_cases hr : k % sh.maskRows + 1 = sh.maskRows
  · right
    rw [beq_eq_false_iff_ne]
    intro hp
    have hdiv := Nat.div_add_mod k sh.maskRows
    have hmul : sh.maskRows * (e - sh.answers) ≤ sh.maskRows * (k / sh.maskRows) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  · left
    rw [beq_eq_false_iff_ne]
    exact hr

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.numbers_succ
#print axioms VerifiableInference.Desc.K13.Honest.takeMasksInto_numbers
#print axioms VerifiableInference.Desc.K13.Honest.takeMasksP_numbers
#print axioms VerifiableInference.Desc.K13.Honest.free_off_pad
