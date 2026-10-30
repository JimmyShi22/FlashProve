-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Keep/RowKeepLaw.lean: a lookup's row that passes its tables on
(`lookRowKeep`, Honest/K3/RowKeep.lean), played alone, shows the rounds of the row that passes
nothing on (`lookRow`, Honest/K3/Row.lean), and leaves the row's own state as it found it.
Conditional on `Keeps.Lawful`, on `Keeps.SteadyFrom`, on a hypothesis on alpha's number in the row,
and on a.base ≤ h.length at the state in front. Stated at the row's letters (`Keeps`): no job and no
store is named. Definitions that the statements need, and theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: a row played alone is `aloneRow`, the state behind it
`endRow` (Honest/K3/Law/PlayPart.lean); `PairSame`, `RowSame`, `RowRel` are the hypotheses of
Honest/K3/Law/Keep/RowTwin.lean.

What is defined.
  `Keeps.StoreOk`: where a store is passed on, it is the one that the letters' maker makes of the
    input and the challenges heard.
  `Keeps.SteadyFrom w n`: once n challenges are heard, the maker makes the same store of more.
  `Keeps.Lawful R J a`: the letters fit the earlier row: a job just where the stage has a call; its
    earlier job is `jobOfAt` at the stage and the call; at the stages of the row it meets
    `KeepJob.FaithfulOn` at `Keeps.StoreOk`.
  `KeepInv`: the invariant in front of the part number j: no kept state; a.base + j challenges are
    heard at least; a store that is passed on is the maker's, and n challenges are heard; behind the
    row's last part no store is passed on.
  `SpentSame`: the relation on the coins of two parts: the stretches that they spend are read alike.

What is shown.
  `partKeep_none`, `partKeep_alpha`, `partKeep_some`, `partKeep_bits`, `partOf_call`,
    `partOf_quiet`: the arms of `partKeep` and of `partOf` as equations.
  `stages_last`: the row's last stage is `Stage.bits`.
  `spent_reads`, `spentSame_total`: coins in `SpentSame` at two masked sumchecks of one call are
    read alike; where two parts spend stretches of the same counts, all coins of the one have coins
    of the other in the relation.
  `none_some`: `none` is no `some`: a helper.
  `keepInv_front`, `keepInv_more`: the invariant holds in front of the row; it stays as more is
    heard.
  `pairSame_partKeep`: **`PairSame` of the two rows' parts at each stage of the row.**
  `rowSame_keep`, `aloneRow_keep`: **the two rows show the same rounds.**
  `endRow_keep`: **behind the row its own state is `rowOwn₀` again.**
  `spends_partKeep`, `rowRel_keep_total`: for all coins of the kept row there are coins of the
    earlier row in the relation.

Hypotheses that remain, by name.
  `hL : Kp.Lawful R J a`, `hS : Kp.SteadyFrom w n`: for whoever fills the letters to show
    (Honest/K3/Law/Keep/SameRounds.lean does).
  `hα`: alpha's own challenge is the n-th at the latest, counted from the chain's first round, if
    a.base rounds stand in front of the row and each part in front of alpha has a round at least.
  `hb : a.base ≤ h.length`: at the state in front of the row at least a.base challenges are heard.
    Without it the store could be made of challenges that are not yet there, and the statement could
    fail.
  `hc : RowRel SpentSame …`: the two rows' coins are read alike, part by part.
  `hl`: (in `endRow_keep`) as many challenges as the row has moves.
  In the steps: `h`, `hs`: which arm of `partKeep` or `partOf` it is (the letters' job at the stage;
    the stage's call; the stage is not alpha, or not the bits). `h`, `hl`, `hj`: a stage's number in
    the row. `hI`, `hd`: (in `keepInv_more`) the invariant; a challenge more. `hk`, `h`: (in
    `spent_reads`, `spentSame_total`) one call; lists of coins, or counts, that are equal. `e`: (in
    `none_some`) the equation that cannot hold: `none` is a `some`.

Imported: Honest/SumKeepLaw.lean, Honest/SumKeep.lean and Honest/SumLaw/.

Users. Honest/K3/Law/Keep/SameRounds.lean and Honest/K3/Law/Keep/RowKeepFits.lean.

Limits. The rows are played alone: nothing on stops, on the shapes of messages, or on the frame's
player. The row starts at `rowOwn₀`. Nothing on how long a move takes.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.RowKeep
import Johnson.Desc.ProofFile.Honest.K3.Law.RowPlays
import Johnson.Desc.ProofFile.Honest.K3.Law.Keep.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open VerifiableInference.Desc.Part.MaskedSum (Call)

/-! ## 1 The hypotheses on the letters -/

/-- Where a store is passed on, it is the one that the maker makes of the input and the challenges
heard. A definition, meant as a hypothesis. Where none is passed on it holds. -/
def Keeps.StoreOk (Kp : Keeps) (w : Ask) (h : List Fmt.Drawn) (x : Option Store) : Prop :=
  ∀ st, x = some st → st = Kp.store w h

/-- Once n challenges are heard, the maker makes the same store of more. A definition, meant as a
hypothesis. -/
def Keeps.SteadyFrom (Kp : Keeps) (w : Ask) (n : Nat) : Prop :=
  ∀ h more : List Fmt.Drawn, n ≤ h.length → Kp.store w (h ++ more) = Kp.store w h

/-- **The letters fit the earlier row.** A definition, meant as a hypothesis. -/
structure Keeps.Lawful (Kp : Keeps) (R : Reads) (J : LookJobs Ask) (a : At) : Prop where
  /-- at a stage with a call there is a job, and its earlier job is `jobOfAt` there -/
  job_some : ∀ s k, s.call a.face = some k → ∃ Jk, Kp.job s = some Jk ∧ Jk.base = jobOfAt R J a s k
  /-- at a stage without a call there is none -/
  job_none : ∀ s, s.call a.face = none → Kp.job s = none
  /-- at the stages of the row the kept state gives what the earlier job computes, where the store
  is the maker's -/
  faithful : ∀ s ∈ stages a.face, ∀ Jk, Kp.job s = some Jk → Jk.FaithfulOn Kp.StoreOk

/-- **The invariant in front of the part number j.** n: the number of `Keeps.SteadyFrom`. -/
def KeepInv (Kp : Keeps) (a : At) (w : Ask) (n j : Nat) (h : List Fmt.Drawn) (y : RowOwn) : Prop :=
  y.2 = none ∧ a.base + j ≤ h.length ∧ (∀ st, y.1 = some st → st = Kp.store w h ∧ n ≤ h.length) ∧
    ((stages a.face).length ≤ j → y.1 = none)

end ProofFile.Honest.K3

namespace ProofFile.Honest.K3.Law
open OnBytes (E)
open VerifiableInference.Desc.Part.MaskedSum (Call)
open ProofFile.Honest.SumLaw (alone SumCoins)

variable {V W X : Type}

/-- **The stretches that two parts spend are read alike.** -/
def SpentSame (p : Part V W X) (q : Part V W Unit) (c : p.Coins) (c' : q.Coins) : Prop :=
  csAllE p.spends c.2.1 = csAllE q.spends c'.2.1

/-! ## 2 The arms of the two parts -/

theorem partKeep_none (Kp : Keeps) (a : At) (s : Stage) (i : Nat) (h : Kp.job s = none)
    (hs : s ≠ .alpha) : partKeep (V := V) Kp a s i = quietAt := by
  simp only [partKeep, h, if_neg hs]

theorem partKeep_alpha (Kp : Keeps) (a : At) (i : Nat) (h : Kp.job .alpha = none) :
    partKeep (V := V) Kp a .alpha i =
      quietLay fun t => (some (Kp.store t.input t.heard), none) := by
  simp only [partKeep, h, if_true]

theorem partKeep_some (Kp : Keeps) (a : At) (s : Stage) (i : Nat)
    (Jk : KeepJob Ask (Option Store) Kept) (h : Kp.job s = some Jk) (hs : s ≠ .bits) :
    partKeep (V := V) Kp a s i = keepPart (sumName a.place i) (endName a.place i) Jk := by
  simp only [partKeep, h, if_neg hs]

theorem partKeep_bits (Kp : Keeps) (a : At) (i : Nat) (Jk : KeepJob Ask (Option Store) Kept)
    (h : Kp.job .bits = some Jk) :
    partKeep (V := V) Kp a .bits i =
      (keepPart (sumName a.place i) (endName a.place i) Jk).lastHand fun _ => rowOwn₀ := by
  simp only [partKeep, h, if_true]

theorem partOf_call (R : Reads) (J : LookJobs W) (a : At) (s : Stage) (i : Nat) (k : Call)
    (h : s.call a.face = some k) :
    partOf (V := V) R J a s i =
      sumPart (sumName a.place i) (endName a.place i) (jobOf R J a s k) := by
  simp only [partOf, h]

theorem partOf_quiet (R : Reads) (J : LookJobs W) (a : At) (s : Stage) (i : Nat)
    (h : s.call a.face = none) : partOf (V := V) R J a s i = quiet := by
  simp only [partOf, h]

/-- The row's last stage is `Stage.bits`. -/
theorem stages_last (f : LFace) (j : Nat) (s : Stage) (h : (stages f)[j]? = some s)
    (hl : (stages f).length ≤ j + 1) : s = .bits := by
  obtain ⟨L, hL⟩ : ∃ L, stages f = L ++ [Stage.leaves, Stage.zero, Stage.bits] := ⟨_, rfl⟩
  rw [hL] at h hl
  have hlt := (List.getElem?_eq_some_iff.1 h).1
  simp only [List.length_append, List.length_cons, List.length_nil] at hl hlt
  obtain rfl : j = L.length + 2 := by omega
  rw [List.getElem?_append_right (by omega)] at h
  have e : L.length + 2 - L.length = 2 := by omega
  rw [e] at h
  exact (Option.some.inj h).symm

/-! ## 3 The relation on coins -/

/-- Coins of two masked sumchecks of one call whose stretches are read alike. -/
theorem spent_reads (n e : String) (k k' : Call) (hk : k = k') (c : CsAll (runsOf n e k))
    (c' : CsAll (runsOf n e k')) (h : csAllE _ c = csAllE _ c') :
    coinsE c.1 = coinsE c'.1 ∧ endCoins e k.ends c.2 = endCoins e k'.ends c'.2 := by
  subst hk
  exact runs_of_csAllE n e n e k c c' h

/-- **The relation has members**: where two parts spend stretches of the same counts, for all coins
of the one there are coins of the other in the relation. -/
theorem spentSame_total (p : Part V W X) (q : Part V W Unit)
    (h : q.spends.map (·.2.e) = p.spends.map (·.2.e)) (c : p.Coins) :
    ∃ c' : q.Coins, SpentSame p q c c' :=
  ⟨(fillCs q.takes fun _ => 0, fillRuns q.spends (readRuns p.spends c.2.1),
      fillRuns q.carries fun _ _ => 0),
    (csAllE_fill p.spends q.spends c.2.1 h).symm⟩

/-! ## 4 The invariant -/

theorem none_some {α : Type} {P : Prop} {x : α} (e : (none : Option α) = some x) : P := by
  cases e

/-- In front of the row. The hypothesis: a.base challenges are heard at least. -/
theorem keepInv_front (Kp : Keeps) (a : At) (w : Ask) (n : Nat) (h : List Fmt.Drawn)
    (hb : a.base ≤ h.length) : KeepInv Kp a w n 0 h rowOwn₀ :=
  ⟨rfl, hb, fun _ e => none_some e, fun _ => rfl⟩

/-- It stays as a part's challenges are heard and what is passed on stays, in front of the row's
last part. Conditional on `Keeps.SteadyFrom`. -/
theorem keepInv_more {Kp : Keeps} {a : At} {w : Ask} {n j : Nat} (hS : Kp.SteadyFrom w n)
    {h : List Fmt.Drawn} {y : RowOwn} (hI : KeepInv Kp a w n j h y) (ds : List Fmt.Drawn)
    (hd : 0 < ds.length) (hj : ¬ (stages a.face).length ≤ j + 1) :
    KeepInv Kp a w n (j + 1) (h ++ ds) y :=
  ⟨hI.1, by rw [List.length_append]; have := hI.2.1; omega,
    fun st e => ⟨((hI.2.2.1 st e).1).trans (hS h ds (hI.2.2.1 st e).2).symm, by
      rw [List.length_append]; have := (hI.2.2.1 st e).2; omega⟩,
    fun hl => absurd hl hj⟩

/-! ## 5 Pair by pair -/

/-- **`PairSame` of the two rows' parts at a stage of the row.** Conditional on `Keeps.Lawful`,
`Keeps.SteadyFrom` and hα: alpha's own challenge is the n-th at the latest. -/
theorem pairSame_partKeep (Kp : Keeps) (R : Reads) (J : LookJobs Ask) (a : At) (w : Ask) (n : Nat)
    (hL : Kp.Lawful R J a) (hS : Kp.SteadyFrom w n)
    (hα : ∀ j, (stages a.face)[j]? = some .alpha → n ≤ a.base + j + 1) (s : Stage) (j : Nat)
    (hj : (stages a.face)[j]? = some s) :
    PairSame w (KeepInv Kp a w n j) (KeepInv Kp a w n (j + 1)) (partKeep (V := V) Kp a s j)
      (partOf R J a s j) (SpentSame _ _) := by
  have hmem : s ∈ stages a.face := List.mem_of_getElem? hj
  have hlast : (stages a.face).length ≤ j + 1 → s = .bits := stages_last a.face j s hj
  cases hk : s.call a.face with
  | none =>
    have hjn := hL.job_none s hk
    have hnb : ¬ (stages a.face).length ≤ j + 1 := fun hl => by
      rw [hlast hl] at hk
      exact nomatch hk
    rw [partOf_quiet R J a s j hk]
    by_cases hs : s = .alpha
    · subst hs
      rw [partKeep_alpha Kp a j hjn]
      refine pairSame_quietLay w _ _ _ _ fun h x d hI => ⟨rfl, ?_, fun st e => ⟨?_, ?_⟩,
        fun hl => absurd hl hnb⟩
      · rw [List.length_append]
        have := hI.2.1
        exact Nat.succ_le_succ this
      · exact (Option.some.inj e).symm
      · rw [List.length_append]
        have h1 := hI.2.1
        have h2 := hα j hj
        show n ≤ h.length + 1
        omega
    · rw [partKeep_none Kp a s j hjn hs]
      exact pairSame_quietLay w _ _ _ _ fun h x d hI =>
        keepInv_more hS hI [d] (Nat.succ_pos 0) hnb
  | some k =>
    obtain ⟨Jk, hJ, hb⟩ := hL.job_some s k hk
    rw [partOf_call R J a s j k hk]
    have base : ∀ I' : List Fmt.Drawn → RowOwn → Prop,
        (∀ h y (ds : List Fmt.Drawn), KeepInv Kp a w n j h y →
          ds.length = (scalarsOf Jk.base.shape).length → I' (h ++ ds) y) →
        PairSame w (KeepInv Kp a w n j) I'
          (keepPart (V := V) (sumName a.place j) (endName a.place j) Jk)
          (sumPart (sumName a.place j) (endName a.place j) (jobOf R J a s k)) (SpentSame _ _) :=
      fun I' hI' => pairSame_keepAt _ _ Jk R J a s k hb Kp.StoreOk (hL.faithful s hmem Jk hJ) w _ I'
        _ (fun c c' hr => spent_reads _ _ Jk.base.shape k (by rw [hb]; rfl) c.2.1 c'.2.1 hr)
        (fun h y hI => ⟨hI.1, fun st e => (hI.2.2.1 st e).1⟩) hI'
    by_cases hs : s = .bits
    · subst hs
      rw [partKeep_bits Kp a j Jk hJ]
      refine (base (fun _ _ => True) fun _ _ _ _ _ => True.intro).lastHand _
        (keepPart_ne_nil _ _ Jk) fun h x z ds hI hl => ⟨rfl, ?_,
          fun _ e => none_some e, fun _ => rfl⟩
      rw [List.length_append, hl, keepPart_length]
      have h1 := hI.2.1
      have h2 := scalarsOf_pos Jk.base.shape
      omega
    · rw [partKeep_some Kp a s j Jk hJ hs]
      exact base _ fun h y ds hI hl =>
        keepInv_more hS hI ds (by rw [hl]; exact scalarsOf_pos _) fun hl' => hs (hlast hl')

/-! ## 6 The rows -/

/-- `RowSame` of the two rows. Conditional as `pairSame_partKeep`. -/
theorem rowSame_keep (Kp : Keeps) (R : Reads) (J : LookJobs Ask) (a : At) (w : Ask) (n : Nat)
    (hL : Kp.Lawful R J a) (hS : Kp.SteadyFrom w n)
    (hα : ∀ j, (stages a.face)[j]? = some .alpha → n ≤ a.base + j + 1) :
    RowSame w SpentSame (KeepInv Kp a w n) 0 (lookRowKeep (V := V) Kp a) (lookRow R J a) :=
  rowSame_zipIdx w SpentSame (KeepInv Kp a w n) (fun x => partKeep Kp a x.1 x.2)
    (fun x => partOf R J a x.1 x.2) (stages a.face) 0 fun y hy =>
      pairSame_partKeep Kp R J a w n hL hS hα y.1 y.2 (List.mem_zipIdx_iff_getElem?.1 hy)

/-- **The row that passes its tables on, played alone, shows the rounds of the row that passes
nothing on.** Conditional on `Keeps.Lawful`, `Keeps.SteadyFrom`, hα (alpha's own challenge is the
n-th at the latest), hb (a.base challenges at least are heard in front of the row) and hc (the two
rows' coins are read alike). -/
theorem aloneRow_keep (Kp : Keeps) (R : Reads) (J : LookJobs Ask) (a : At) (w : Ask) (n : Nat)
    (hL : Kp.Lawful R J a) (hS : Kp.SteadyFrom w n)
    (hα : ∀ j, (stages a.face)[j]? = some .alpha → n ≤ a.base + j + 1)
    (c : RowCoins (lookRowKeep (V := V) Kp a)) (c' : RowCoins (lookRow (V := V) R J a))
    (hc : RowRel SpentSame _ _ c c') (h : List Fmt.Drawn) (hb : a.base ≤ h.length)
    (seen : Seen) (ds : List Fmt.Drawn) :
    aloneRow (lookRowKeep Kp a) c ⟨w, h, rowOwn₀⟩ seen ds =
      aloneRow (lookRow R J a) c' ⟨w, h, ()⟩ seen ds :=
  aloneRow_twin w SpentSame (KeepInv Kp a w n) _ _ 0 (rowSame_keep Kp R J a w n hL hS hα) c c' hc h
    rowOwn₀ seen ds (keepInv_front Kp a w n h hb)

/-- **Behind the row its own state is `rowOwn₀` again**, and the row's challenges are heard.
Conditional on `Keeps.Lawful`, `Keeps.SteadyFrom`, hα and hb, as `aloneRow_keep`; hl: there are as
many challenges as the row has moves. -/
theorem endRow_keep (Kp : Keeps) (R : Reads) (J : LookJobs Ask) (a : At) (w : Ask) (n : Nat)
    (hL : Kp.Lawful R J a) (hS : Kp.SteadyFrom w n)
    (hα : ∀ j, (stages a.face)[j]? = some .alpha → n ≤ a.base + j + 1) (h : List Fmt.Drawn)
    (hb : a.base ≤ h.length) (ds : List Fmt.Drawn)
    (hl : ds.length = ((lookRowKeep (V := V) Kp a).map (·.moves.length)).sum) :
    endRow (lookRowKeep (V := V) Kp a) ⟨w, h, rowOwn₀⟩ ds = ⟨w, h ++ ds, rowOwn₀⟩ := by
  have hI := endRow_twin w SpentSame (KeepInv Kp a w n) _ _ 0
    (rowSame_keep (V := V) Kp R J a w n hL hS hα) h rowOwn₀ ds (keepInv_front Kp a w n h hb) hl
  have hlen : (lookRowKeep (V := V) Kp a).length = (stages a.face).length := by
    simp [lookRowKeep]
  have e1 := hI.2.2.2 (by rw [hlen]; omega)
  have e2 := hI.1
  rw [endRow_eq _ _ ds hl]
  exact congrArg (fun z => (⟨w, h ++ ds, z⟩ : State Ask RowOwn)) (Prod.ext e1 e2)

/-! ## 7 The relation has members at the two rows -/

/-- The two rows' parts spend the same stretches. Conditional on `Keeps.Lawful`. -/
theorem spends_partKeep (Kp : Keeps) (R : Reads) (J : LookJobs Ask) (a : At)
    (hL : Kp.Lawful R J a) (s : Stage) (j : Nat) :
    (partOf (V := V) R J a s j).spends = (partKeep (V := V) Kp a s j).spends := by
  cases hk : s.call a.face with
  | none =>
    have hjn := hL.job_none s hk
    rw [partOf_quiet R J a s j hk]
    by_cases hs : s = .alpha
    · subst hs
      rw [partKeep_alpha Kp a j hjn]
      rfl
    · rw [partKeep_none Kp a s j hjn hs]
      rfl
  | some k =>
    obtain ⟨Jk, hJ, hb⟩ := hL.job_some s k hk
    have e : Jk.base.shape = k := by rw [hb]; rfl
    rw [partOf_call R J a s j k hk]
    by_cases hs : s = .bits
    · subst hs
      rw [partKeep_bits Kp a j Jk hJ]
      show runsOf _ _ k = runsOf _ _ Jk.base.shape
      rw [e]
    · rw [partKeep_some Kp a s j Jk hJ hs]
      show runsOf _ _ k = runsOf _ _ Jk.base.shape
      rw [e]

/-- **For all coins of the kept row there are coins of the earlier row that are read alike.**
Conditional on `Keeps.Lawful`. -/
theorem rowRel_keep_total (Kp : Keeps) (R : Reads) (J : LookJobs Ask) (a : At)
    (hL : Kp.Lawful R J a) (c : RowCoins (lookRowKeep (V := V) Kp a)) :
    ∃ c' : RowCoins (lookRow (V := V) R J a), RowRel SpentSame _ _ c c' :=
  rowRel_total_zipIdx SpentSame (fun x => partKeep Kp a x.1 x.2) (fun x => partOf R J a x.1 x.2)
    (stages a.face) 0 (fun y _ c₀ => spentSame_total _ _
      (by rw [spends_partKeep Kp R J a hL y.1 y.2]) c₀) c

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.partKeep_none
#print axioms ProofFile.Honest.K3.Law.partKeep_alpha
#print axioms ProofFile.Honest.K3.Law.partKeep_some
#print axioms ProofFile.Honest.K3.Law.partKeep_bits
#print axioms ProofFile.Honest.K3.Law.partOf_call
#print axioms ProofFile.Honest.K3.Law.partOf_quiet
#print axioms ProofFile.Honest.K3.Law.stages_last
#print axioms ProofFile.Honest.K3.Law.spent_reads
#print axioms ProofFile.Honest.K3.Law.spentSame_total
#print axioms ProofFile.Honest.K3.Law.none_some
#print axioms ProofFile.Honest.K3.Law.keepInv_front
#print axioms ProofFile.Honest.K3.Law.keepInv_more
#print axioms ProofFile.Honest.K3.Law.pairSame_partKeep
#print axioms ProofFile.Honest.K3.Law.rowSame_keep
#print axioms ProofFile.Honest.K3.Law.aloneRow_keep
#print axioms ProofFile.Honest.K3.Law.endRow_keep
#print axioms ProofFile.Honest.K3.Law.spends_partKeep
#print axioms ProofFile.Honest.K3.Law.rowRel_keep_total
