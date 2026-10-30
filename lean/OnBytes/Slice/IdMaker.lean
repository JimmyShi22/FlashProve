-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/IdMaker.lean: under one random oracle, on the experiment "a first algorithm with its
log, then a second": the event "two strings of the log have one answer, or the key under the ID is
not the first of that ID in the first log" has probability at most (tC + tP + 2)^2 / 2^256. No
probability of the program.

In this file "the commitment ID" ("the ID"), where it stands by itself, is not the format's. It is
the hash function's answer at a shorter string, the format's string for its ID without the record's
seed (`idCode`, OnBytes/Tie/IdKey.lean). The format's rule (R4.11; `Fmt.publishedBytes`,
Fmt/Rules4.lean) hashes the string with the seed.

OnBytes/Slice/OneMaker.lean brings bounds over one random oracle to one experiment:
`(twoExp C P).withTrace`, in which a first algorithm C runs, a second one P runs on its output, and
C's output with its log, P's output and the whole log are kept. OnBytes/Tie/IdRom.lean has the bound
on the key behind a commitment ID in the library's language of one oracle. Here it is carried to
that experiment by the library's bridge between the two languages (Rom/Bridge.lean).

Main theorems: `id_maker`, which uses `toRom_both` and `clash_of_not_noClash`;
`measurableSet_id_maker`, `measurable_id_maker`: for each outcome the oracles under which it lies in
the event form a measurable set, so the event's probability over the algorithms' coins is a
measurable function of the oracle. `clash_iff` ties the two forms of "two strings with one answer".

The statement. The oracle is drawn: a function from bit strings to strings of 256 bits, each value
uniform, all independent. C asks it at most tC strings and puts out b, off which `dig` reads a
digest. P, on b, asks at most tP strings and puts out x, off which `key` reads a key. A key
(`IdKey`) is a shape, 32 bytes for the digest of the public files, and a table; it is the library's
word for what a digest stands for, not the key file. The event: the whole log holds two different
strings with one answer (`NoClash` fails); or the key has a code at which the drawn oracle answers
the digest, and `Tie.firstId` of the digest in C's own log is not that key (the log may hold no key
of the digest at all). Its probability is at most (tC + tP + 2)^2 / 2^256.

What is not claimed. No probability is stated of the program, which is the Lean port built from
OnBytes/, or of BLAKE2b. No verifier stands in the statement: that a verifier says yes only if the
oracle answers the ID at the code of the key that it checks is a hypothesis for whoever uses this
bound, and no checker of OnBytes/ compares an ID (`commonOf`, OnBytes/Model/VerifyStages.lean, the
steps that the model's stages share, compares the caller's ID with `Key.commitmentId`: at the
program's own hash, and at the string with the seed). `key` and `dig` read the outputs alone, not
the oracle: the 32 bytes for the digest of the public files are P's to put out, the query by which P
forms them counts in tP, and that they are the oracle's answer at any files is a clause that the
user's event must hold. Nothing on soundness. What lies under the key's root is not the matter of
this file. The bound is not tight and says nothing once it reaches 1. All limits in the heads of the
files named above, and of OnBytes/Tie/IdKey.lean, hold here too. For proofs only; the program does
not import this file.

-/
import OnBytes.Slice.OneMaker
import OnBytes.Tie.IdRom

set_option autoImplicit false

namespace OnBytes.Slice

open Rom
open OnBytes.Tie (IdKey idCode firstId Clash)
open scoped ENNReal

variable {β δ : Type}

/-- A log of the generic language in which `NoClash` fails has, in the language of one oracle, two
different entries with one answer. -/
theorem clash_of_not_noClash {σ : Trace (rom 256)} (h : ¬ NoClash σ) : Clash (trOf σ) := by
  unfold NoClash at h
  push Not at h
  obtain ⟨e, he, e', he', ha, hne⟩ := h
  exact ⟨(e.2.1, e.2.2), List.mem_map_of_mem he, (e'.2.1, e'.2.2), List.mem_map_of_mem he',
    fun hh => hne (congrArg Prod.fst hh), ha⟩

/-- `Tie.Clash`, on a log in the language of one oracle, is the failure of `NoClash`
(OnBytes/Slice/OneLog.lean) on the log in the generic language. -/
theorem clash_iff (log : ZKCP.Trace 256) : Clash log ↔ ¬ NoClash (trTo log) := by
  constructor
  · rintro ⟨e1, h1, e2, h2, hne, ha⟩ hn
    have := hn ⟨(), e1.1, e1.2⟩ (List.mem_map_of_mem h1) ⟨(), e2.1, e2.2⟩
      (List.mem_map_of_mem h2) ha
    exact hne (Prod.ext this ha)
  · intro h
    have := clash_of_not_noClash h
    rwa [trOf_trTo] at this

/-- The experiment that keeps both logs, written in the language of one oracle and taken to the
generic language, is `bothExp` with both logs taken the other way. An equation between two
algorithms: nothing is drawn. -/
theorem toRom_both (C : OComp (rom 256) β) (P : β → OComp (rom 256) δ) :
    toRom ((ofRom C).withTrace.bind fun o => (ofRom (P o.1)).withTrace.bind fun o' =>
        .pure (o, o')) =
      (bothExp C P).bind fun z => .pure ((z.1.1, trOf z.1.2), (z.2.1, trOf z.2.2)) := by
  unfold bothExp
  simp only [toRom_bind, toRom_withTrace, toRom_ofRom, toRom_pure, OComp.bind_assoc, OComp.bind]

/-- **A clash, or another key under the ID: one event, one bound.** See the head for the experiment
and the event. With probability at most (tC + tP + 2)^2 / 2^256 the whole log of C and P holds two
different strings with one answer, or the key that is read off P's output has a code at which the
drawn oracle answers the digest that is read off C's output, and is not the first key of that digest
in C's own log (which may hold none). No verifier stands in the statement; no probability is stated
of the program or of BLAKE2b; the bound says nothing once it reaches 1. -/
theorem id_maker (C : OComp (rom 256) β) (dig : β → ZKCP.Digest 256)
    (P : β → OComp (rom 256) δ) (key : δ → IdKey) (tC tP : ℕ) (hC : C.QueryBound tC)
    (hP : ∀ b, (P b).QueryBound tP) :
    Rom.Pr (twoExp C P).withTrace (fun g => {w | ¬ NoClash w.2 ∨
        ∃ s, idCode (key w.1.2) = some s ∧ g () s = dig w.1.1.1 ∧
          firstId (dig w.1.1.1) w.1.1.2 ≠ some (key w.1.2)})
      ≤ (((tC + tP + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [twoExp_withTrace, Rom.Pr_bind_pure]
  have hz := Tie.first_id_at (ofRom C) dig (fun b => ofRom (P b)) key tC tP
    ((queryBound_toRom _ _).1 (by rw [toRom_ofRom]; exact hC))
    (fun b => (queryBound_toRom _ _).1 (by rw [toRom_ofRom]; exact hP b))
  have e := Rom.Pr_toRom ((ofRom C).withTrace.bind fun o => (ofRom (P o.1)).withTrace.bind fun o' =>
      .pure (o, o'))
    (fun g => {y : (β × ZKCP.Trace 256) × (δ × ZKCP.Trace 256) | Clash (y.1.2 ++ y.2.2) ∨
      ∃ s, idCode (key y.2.1) = some s ∧ g () s = dig y.1.1 ∧
        ZKCP.firstKey idCode (dig y.1.1) y.1.2 ≠ some (key y.2.1)})
  rw [toRom_both, Rom.Pr_bind_pure] at e
  refine le_trans (Rom.Pr_mono _ fun g z hzE => ?_) (le_of_eq e |>.trans hz)
  rcases hzE with hc | ⟨s, h1, h2, h3⟩
  · left
    have := clash_of_not_noClash hc
    unfold trOf at this ⊢
    rwa [List.map_append] at this
  · right
    exact ⟨s, h1, h2, by rw [Tie.firstId_trOf]; exact h3⟩

/-- For each outcome w, the oracles under which w lies in `id_maker`'s event form a measurable set:
all, none, or those with one given value at one string. -/
theorem measurableSet_id_maker (dig : β → ZKCP.Digest 256) (key : δ → IdKey)
    (w : ((β × Trace (rom 256)) × δ) × Trace (rom 256)) :
    MeasurableSet {g : Fam (rom 256) | w ∈ {w : ((β × Trace (rom 256)) × δ) × Trace (rom 256) |
      ¬ NoClash w.2 ∨ ∃ s, idCode (key w.1.2) = some s ∧ g () s = dig w.1.1.1 ∧
        firstId (dig w.1.1.1) w.1.1.2 ≠ some (key w.1.2)}} := by
  cases hs : idCode (key w.1.2) with
  | none =>
    have e : {g : Fam (rom 256) | w ∈ {w : ((β × Trace (rom 256)) × δ) × Trace (rom 256) |
        ¬ NoClash w.2 ∨ ∃ s, idCode (key w.1.2) = some s ∧ g () s = dig w.1.1.1 ∧
          firstId (dig w.1.1.1) w.1.1.2 ≠ some (key w.1.2)}} = {_g | ¬ NoClash w.2} := by
      ext g
      simp only [Set.mem_setOf_eq, hs]
      constructor
      · rintro (h | ⟨s, h, _⟩)
        · exact h
        · cases h
      · exact Or.inl
    rw [e]
    exact MeasurableSet.const _
  | some s =>
    have hev : MeasurableSet {g : Fam (rom 256) | g () s = dig w.1.1.1} := by
      have hm : Measurable fun g : Fam (rom 256) => g () s :=
        (measurable_pi_apply s).comp (measurable_pi_apply ())
      exact hm (MeasurableSet.of_discrete
        (s := ({(dig w.1.1.1 : (rom 256).Rng ())} : Set ((rom 256).Rng ()))))
    have e : {g : Fam (rom 256) | w ∈ {w : ((β × Trace (rom 256)) × δ) × Trace (rom 256) |
        ¬ NoClash w.2 ∨ ∃ s, idCode (key w.1.2) = some s ∧ g () s = dig w.1.1.1 ∧
          firstId (dig w.1.1.1) w.1.1.2 ≠ some (key w.1.2)}} =
        {_g | ¬ NoClash w.2} ∪ ({g | g () s = dig w.1.1.1} ∩
          {_g | firstId (dig w.1.1.1) w.1.1.2 ≠ some (key w.1.2)}) := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, hs]
      constructor
      · rintro (h | ⟨s', h1, h2, h3⟩)
        · exact Or.inl h
        · obtain rfl := Option.some.inj h1
          exact Or.inr ⟨h2, h3⟩
      · rintro (h | ⟨h2, h3⟩)
        · exact Or.inl h
        · exact Or.inr ⟨s, rfl, h2, h3⟩
    rw [e]
    exact (MeasurableSet.const _).union (hev.inter (MeasurableSet.const _))

/-- The probability of `id_maker`'s event over the coins of C and P is a measurable function of the
oracle: for each outcome the oracles under which it lies in the event are given by one value of the
oracle. So the bound is on a true average, and in a sum of bounds (`Pr_union_le`,
OnBytes/Slice/OneMaker.lean) the event may stand in any place. -/
theorem measurable_id_maker (C : OComp (rom 256) β) (dig : β → ZKCP.Digest 256)
    (P : β → OComp (rom 256) δ) (key : δ → IdKey) :
    Measurable fun g => PrCoins g (twoExp C P).withTrace {w | ¬ NoClash w.2 ∨
      ∃ s, idCode (key w.1.2) = some s ∧ g () s = dig w.1.1.1 ∧
        firstId (dig w.1.1.1) w.1.1.2 ≠ some (key w.1.2)} :=
  Rom.measurable_PrCoins_dep _ (fun g : Fam (rom 256) =>
    {w : ((β × Trace (rom 256)) × δ) × Trace (rom 256) | ¬ NoClash w.2 ∨
      ∃ s, idCode (key w.1.2) = some s ∧ g () s = dig w.1.1.1 ∧
        firstId (dig w.1.1.1) w.1.1.2 ≠ some (key w.1.2)}) (measurableSet_id_maker dig key)

end OnBytes.Slice
