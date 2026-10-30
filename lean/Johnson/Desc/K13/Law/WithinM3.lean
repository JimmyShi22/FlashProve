-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/WithinM3.lean: the proof of the statement `OwedWithinM3`
(Johnson/Desc/K13/Law/OwedWithin.lean): over a yes of kind K13's block (`atM3 P`) the item
"K13.pileWithin" goes on: every ledger in the statement is that of so many takes since it was made,
and every mask entry that a row on the table names lies within its table.

OwedWithin.lean's QUESTION, ANSWERED AS A THEOREM (`atM3_st`): the batching takes its entries at a
state whose statement IS s.st (`dOf s`: by definition), and the statement behind the block IS that
of the batching's answer's second component, ON THE NOSE, not only up to what `SameAll` covers: the
front turns "here" alone; the batching lays its answer's state back; the quiet part lays the
message alone.
Main names:
  `atM3_st`: the answer above.
  `tableSize_sameAll`: two statements with the same codes and each message's same shape have the
    same sizes of tables.
  `ledger_of_take`: where one entry or more is taken of message o's ledger, the message is there
    and has a ledger.
  `withinM3`: **the statement**, under two binders: `OwedLedgersC` (the
    test on the ledgers says what the laws' word says) and `OwedLedgersKept` (the ground's ten plain
    functions keep `LedgersFit`). The ledgers behind: `atM3_keeps` at `OwedLedgersKept`, CALLED. The
    one row behind (`atM3_ok`, `batt_ok`, CALLED) names the fresh entries, zipped, and the pile's
    own, scaled (`run_fields`, CALLED; the walk is `rowOf_onLedger`'s): the fresh ones lie within by
    `takeMasksP_within`, CALLED, at the ledger that `LedgersFit` in front gives for the index masks'
    message; the pile's own by the rows' clause in front; the sizes stay by `atM3_same`, CALLED.
What is not claimed. That the block says yes anywhere. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Law.OwedWithin
import Johnson.Desc.K13.Law.PinDec
import Johnson.Desc.K13.Law.Agree
import Johnson.Desc.K13.Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice
open OnBytes.Means (tableSize)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground (takeMaskP takeMasksInto takeMasksP)
open Desc.Plain (DState)

variable {Cl : Type}

/-- **OwedWithin.lean's question.** The batching answers at a state whose statement is s.st, and the
statement behind the joined block is that of its answer's second component. -/
theorem atM3_st {P : Where} {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (atM3 (Cl := Cl) P).decide s rs gs = .ok s') :
    (dOf s).st = s.st ∧ ∃ (d : St) (out : TensorRow × St) (owed : Johnson.Desc.First.ForkGround.RowsOwed) (k n : ℕ)
      (pile : List TensorRow) (ledger : ℕ) (rs' : List Fmt.RoundView), d.st = s.st ∧
      batt owed k n pile ledger d rs' = .ok out ∧ s'.st = out.2.st := by
  refine ⟨rfl, ?_⟩
  have h' : (((frontB (Cl := Cl) atS P).decide s _ _).bind fun s₁ =>
      (claimCombinationBlock (Cl := Cl) atS P).decide s₁ _ _).bind (fun s₂ =>
                      (quietB (Cl := Cl) atS P).decide s₂ _ _) = .ok s' := h
  obtain ⟨s₂, h12, h3⟩ := ebind_ok.1 h'
  obtain ⟨s₁, h1, h2⟩ := ebind_ok.1 h12
  obtain ⟨rfl, _⟩ := enter_eq (frontB_ok atS P h1)
  obtain ⟨p, out, hp, hb, rfl⟩ := battB_ok atS P h2
  obtain ⟨p', msg, hp', rfl⟩ := quietB_ok atS P h3
  obtain rfl := Option.some.inj hp
  obtain rfl := Option.some.inj hp'
  exact ⟨_, out, _, _, _, _, _, _, rfl, hb, rfl⟩

/-- The same codes and each message's same shape: the same sizes of tables. -/
theorem tableSize_sameAll {A B : Statement} (h : SameAll A B) (o : ℕ) (pt : OnBytes.Part) :
    tableSize B o pt = tableSize A o pt := by
  have hj := h.2 o
  unfold sampleOf at hj
  cases ha : A.oracles[o]? with
  | none =>
    rw [ha] at hj
    cases hb : B.oracles[o]? with
    | none => simp [tableSize, Statement.has, ha, hb]
    | some y =>
      rw [hb] at hj
      cases hj
  | some x =>
    rw [ha] at hj
    cases hb : B.oracles[o]? with
    | none =>
      rw [hb] at hj
      cases hj
    | some y =>
      rw [hb] at hj
      have hs : y.shape = x.shape := congrArg (·.1) (Option.some.inj hj)
      simp [tableSize, Statement.has, Statement.tableBits, Statement.rowBits,
        Statement.placeBits, ha, hb, hs, h.1]

/-- Where one entry or more is taken, the message is there and has a ledger. -/
theorem ledger_of_take {L : Type} {d : DState L} {o n : ℕ} {t : List ℕ × DState L}
    (h : takeMasksP d o (n + 1) = some t) :
    ∃ x : OnBytes.Oracle, d.st.oracles[o]? = some x ∧ x.ledger.isSome = true := by
  have h' : (match takeMaskP d o with
    | none => none
    | some (i, d') => takeMasksInto o n d' ((#[] : Array ℕ).push i)) = some t := h
  cases hm : takeMaskP d o with
  | none =>
    rw [hm] at h'
    cases h'
  | some q =>
    unfold takeMaskP at hm
    split at hm
    · cases hx : d.st.oracles[o]? with
      | none =>
        rw [hx] at hm
        cases hm
      | some x =>
        rw [hx] at hm
        cases hl : x.ledger with
        | none =>
          have hm' : (Option.map _ (x.ledger)) = some q := hm
          rw [hl] at hm'
          cases hm'
        | some l => exact ⟨x, rfl, by rw [hl]; rfl⟩
    · cases hm

/-- **Over a yes of kind K13's block "K13.pileWithin" goes on.** -/
theorem withinM3 (hC : OwedLedgersC) (hK : OwedLedgersKept) : OwedWithinM3 := by
  intro Cl P s s' rs gs h hw
  have hw' : (ledgersFitC s && rowsWithinC s) = true := hw
  rw [Bool.and_eq_true] at hw'
  obtain ⟨hL, hR⟩ := hw'
  have hLs : LedgersFit s.st := (hC s).1 hL
  have hLs' : LedgersFit s'.st := atM3_keeps hK.quiet P s rs gs s' h hLs
  have hsame := atM3_same h
  obtain ⟨out, hb, hrows, hr⟩ := atM3_ok h
  obtain ⟨r, rs', x, t, hd, o, _, _, hfit, _, _, htk, _, hrun, _, rfl⟩ := batt_ok hb
  have hk1 : Batt.masksOf P.lin.kCol = 2 * P.lin.kCol + 1 := by
    unfold Batt.masksOf
    omega
  obtain ⟨x₀, hx₀, hl₀⟩ := ledger_of_take (hk1 ▸ htk)
  obtain ⟨k₀, hLA⟩ := hLs s.out.indexMasks x₀ hx₀ hl₀
  have hfresh := (takeMasksP_within (d := dOf s) hLA htk).1
  show (ledgersFitC s' && rowsWithinC s') = true
  rw [Bool.and_eq_true]
  refine ⟨(hC s').2 hLs', ?_⟩
  unfold rowsWithinC
  rw [hr]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  refine List.all_eq_true.2 fun u hu => decide_eq_true ?_
  show u.1.index < tableSize s'.st u.1.oracle .mask
  rw [tableSize_sameAll hsame]
  have hu' : u ∈ o.rowMasks := hu
  obtain ⟨_, _, _, _, hmk, _, _⟩ := run_fields hfit hrun
  rw [hmk] at hu'
  rcases List.mem_append.1 hu' with h1 | h1
  · obtain ⟨i, hi, e⟩ := List.mem_map.1 (List.of_mem_zip h1).1
    rw [← e]
    exact hfresh i hi
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 h1
    have hv' : v ∈ (zipT (Psc.powers oneE x s.out.pending.length) s.out.pending).flatMap
        fun p => Psc.scaleForm p.1 p.2.masks := hv
    obtain ⟨p, hpm, hvp⟩ := List.mem_flatMap.1 hv'
    obtain ⟨w, hw', rfl⟩ := List.mem_map.1 hvp
    rw [zipT_eq] at hpm
    have hp2 : p.2 ∈ s.rows := hrows ▸ (List.of_mem_zip hpm).2
    exact of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 hR p.2 hp2) w hw')

end VerifiableInference.Desc.K13.Law
