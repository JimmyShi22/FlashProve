-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Own/AgreeOwn.lean: WHOSE COINS FOLD THE FIRST FOLD's OWN MASK: the
two parts' readers agree (`Agree`, CoinsAgree.lean in the folder above) at the coins that the frame
lends, where the first fold sends its fresh table itself. One definition; statements and proofs. The
fellows of `agree_came`, `tiesB` and `agree_of_ties` (AgreeBook.lean in the folder above), which
stand where that table has come earlier alone.

FIRST, WHAT IT IS NOT.
- A LAW ON COINS THAT THE FRAME LENDS: general in the book and in the run's coins, which are not
  looked into. It says nothing on any state on entry, door, tree or budget.
- THAT `tiesOB` SAYS YES AT ANY BOOK IS NOT SHOWN HERE. It is shown in
  AtFullSide/K12/TiesOwnAtLaid.lean (`tiesO_at_laid`): at the book that the maker returns at the
  library's written sendings, in the goals' scope, where the description is laid, at the place of
  the test on G_omega, at two members. That a filling's book is that book is not shown.
- `hrows` stays a premise, as in the other case.
- Nothing on completeness, soundness or hiding.

What. At `fresh = none` the first part takes coins of its own: the hiding polynomial's 2k + 1
coefficients, then the mask rows' tails (`firstPart`, Parts.lean); it spends none. The second part
carries that stretch by name, as the last of its carried stretches (`freshRun`, `restPart`). The
frame gives a part its own coins as a cut of its own purse from 0 on, and a carried block as a cut
of the entry's owner's purse from the entry's start on (`lendPart`, `lend`,
Johnson/Desc/ProofFile/Honest/Frame.lean). So where the second part's last carried entry has the
first part as its owner and starts at 0, the two are one cut of one purse.

  `own_is_carried`   the first part's own coins are the stretch that the second part carries last
  `agree_own`   the two readers agree
  `tiesOB`, `agree_of_tiesO`   the equations on the book's entries as one test; the same from its
                 yes

No `hk`, which `agree_came` asks: there the spent stretch and the carried one agree only as far as
the 2k + 1 coefficients reach; here they are one stretch whole.

By what. `own_of_lendPart` (Sim/SenderInFront.lean), `lend_stretch`, `stretch_tie` (AgreeBook.lean),
`lendRow_cons_ok`, `lendPart_ok` (Johnson/Desc/ProofFile/Honest/Law/Rule/).
Terms: RunBySpec.lean in the folder above.
-/
import Johnson.Desc.ProofFile.Honest.K12.AgreeBook
import Johnson.Desc.ProofFile.Honest.K12.Sim.SenderInFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Own
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)

variable {V W X : Type}

/-- **The first part's own coins are the stretch that the second part carries last.** -/
theorem own_is_carried (p : P12) (ms : List (Addr × ℕ × Due)) (r : W → Front X → T12)
    (ro : W → Front X → (ℕ → Stretch) → PS) (tr : W → Front X → (ℕ → Stretch) → PS → List Tree)
    (Bk : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (c : RowCoins [(firstPart ⟨p, ms, none, r, ro, tr⟩ : Part V W X),
      restPart ⟨p, ms, none, r, ro, tr⟩])
    (h : lendRow Bk rows look p.place
      [(firstPart ⟨p, ms, none, r, ro, tr⟩ : Part V W X), restPart ⟨p, ms, none, r, ro, tr⟩] 0 =
        .ok c)
    (e₂ : Ahead) (hf : (carryE Bk ⟨p.place, 0 + 1⟩)[ms.length]? = some e₂)
    (ho : e₂.owner = ⟨p.place, 0⟩) (hst : e₂.start = ⟨0, 0⟩) :
    stretchOf c.1.1 = stretches _ c.2.1.2.2 ms.length := by
  obtain ⟨l1, l2'⟩ := lendRow_cons_ok h
  obtain ⟨l2, -⟩ := lendRow_cons_ok l2'
  have o1 := Light.own_of_lendPart l1
  obtain ⟨-, -, c2⟩ := lendPart_ok l2
  obtain ⟨q2, x2, k2, z2⟩ := lend_stretch look _ _ _ c2 ms.length e₂ hf
  have n2 : e₂.count = ⟨0, dueFresh (TestJob.s₀ ⟨p, ms, none, r, ro, tr⟩)⟩ := by
    have e : ((memberRuns (⟨p, ms, none, r, ro, tr⟩ : TestJob W X) ⟨p.place, 1⟩ ++
        [freshRun ⟨p, ms, none, r, ro, tr⟩])[ms.length]?).map (·.2) = some e₂.count := q2
    rw [List.getElem?_append_right (by simp [memberRuns])] at e
    simp only [memberRuns, List.length_map, Nat.sub_self, List.getElem?_cons_zero,
      Option.map_some] at e
    exact (Option.some.inj e).symm
  have t := stretch_tie look
    ⟨"", ⟨p.place, 0⟩, ⟨0, 0⟩, ⟨0, dueFresh (TestJob.s₀ ⟨p, ms, none, r, ro, tr⟩)⟩, e₂.spender,
      false⟩ e₂ c.1.1 x2 o1 k2 ho.symm hst.symm n2.symm
  exact t.trans z2.symm

/-- **The two parts' readers agree, where the first fold sends its own mask.** `agree_came`'s
fellow: no spent entry is asked (the first part spends none); no `hk` (the whole stretch is one, not
its first 2k + 1 coins). -/
theorem agree_own (p : P12) (ms : List (Addr × ℕ × Due)) (r : W → Front X → T12)
    (ro : W → Front X → (ℕ → Stretch) → PS) (tr : W → Front X → (ℕ → Stretch) → PS → List Tree)
    (Bk : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (c : RowCoins [(firstPart ⟨p, ms, none, r, ro, tr⟩ : Part V W X),
      restPart ⟨p, ms, none, r, ro, tr⟩])
    (h : lendRow Bk rows look p.place
      [(firstPart ⟨p, ms, none, r, ro, tr⟩ : Part V W X), restPart ⟨p, ms, none, r, ro, tr⟩] 0 =
        .ok c)
    (w : W) (fr : Front X) (e₂ : Ahead)
    (hf : (carryE Bk ⟨p.place, 0 + 1⟩)[ms.length]? = some e₂)
    (ho : e₂.owner = ⟨p.place, 0⟩) (hst : e₂.start = ⟨0, 0⟩)
    (hm : ∀ t, t < ms.length → ∃ a a', (carryE Bk ⟨p.place, 0⟩)[t]? = some a ∧
      (carryE Bk ⟨p.place, 0 + 1⟩)[t]? = some a' ∧ a.owner = a'.owner ∧ a.start = a'.start ∧
      a.count = a'.count)
    (hrows : ∀ mem mem' : ℕ → Stretch, (∀ t, t < ms.length → mem t = mem' t) →
      μOf (sgOf (TestJob.s₀ ⟨p, ms, none, r, ro, tr⟩)) (ro w fr mem) =
        μOf (sgOf (TestJob.s₀ ⟨p, ms, none, r, ro, tr⟩)) (ro w fr mem')) :
    Agree ⟨p, ms, none, r, ro, tr⟩ w fr (TestJob.s₀ ⟨p, ms, none, r, ro, tr⟩)
      (firstRd ⟨p, ms, none, r, ro, tr⟩ c.1) (restCoins ⟨p, ms, none, r, ro, tr⟩ c.2.1) := by
  have E := own_is_carried p ms r ro tr Bk rows look c h e₂ hf ho hst
  obtain ⟨l1, l2'⟩ := lendRow_cons_ok h
  obtain ⟨l2, -⟩ := lendRow_cons_ok l2'
  obtain ⟨-, -, c1⟩ := lendPart_ok l1
  obtain ⟨-, -, c2⟩ := lendPart_ok l2
  refine ⟨?_, ?_, fun _ => ?_⟩
  · -- the coefficients
    show hideAt _ (stretchOf c.1.1).e = hideAt _ (stretches _ c.2.1.2.2 ms.length).e
    rw [E]
  · -- the first stage's message
    have e : ∀ K : TestCoins, μOf (sgOf (TestJob.s₀ ⟨p, ms, none, r, ro, tr⟩))
        (TestJob.first ⟨p, ms, none, r, ro, tr⟩ w fr K) =
        μOf (sgOf (TestJob.s₀ ⟨p, ms, none, r, ro, tr⟩)) (ro w fr K.mem) := fun K => by
      funext x
      cases x <;> rfl
    rw [e, e]
    refine hrows _ _ fun t ht => ?_
    obtain ⟨a, a', ha, ha', o1, o2, o3⟩ := hm t ht
    obtain ⟨-, x1, k1, z1⟩ := lend_stretch look _ _ _ c1 t a ha
    obtain ⟨-, x2, k2, z2⟩ := lend_stretch look _ _ _ c2 t a' ha'
    show stretches _ c.1.2.2 t = stretches _ c.2.1.2.2 t
    rw [z1, z2]
    exact stretch_tie look a a' x1 x2 k1 k2 o1 o2 o3
  · -- the tails
    show tailsIn (TestJob.s₀ ⟨p, ms, none, r, ro, tr⟩) (stretchOf c.1.1).e =
      tailsIn (TestJob.s₀ ⟨p, ms, none, r, ro, tr⟩) (stretches _ c.2.1.2.2 ms.length).e
    rw [E]

/-- The equations on the book's entries, as a test that returns a `Bool`. pl: the test's place. n:
the number of the job's members. `tiesB`'s fellow: its first two clauses (a spent entry of the first
part; its owner and start are the carried one's) give way to one: the second part's carried entry
number n is the first part's own coins from their start. -/
def tiesOB (Bk : ProverCoinCounts) (pl : VerifiableInference.Desc.Place) (n : ℕ) : Bool :=
  (((carryE Bk ⟨pl, 0 + 1⟩)[n]?).map fun e => (e.owner, e.start)) ==
    some ((⟨pl, 0⟩, ⟨0, 0⟩) : Addr × Due) &&
  decide (n ≤ (carryE Bk ⟨pl, 0⟩).length) &&
  ((carryE Bk ⟨pl, 0⟩).take n).map (fun e => (e.owner, e.start, e.count)) ==
    ((carryE Bk ⟨pl, 0 + 1⟩).take n).map fun e => (e.owner, e.start, e.count)

/-- **The conclusion of `agree_own` where the test on the book returns true.** -/
theorem agree_of_tiesO (p : P12) (ms : List (Addr × ℕ × Due)) (r : W → Front X → T12)
    (ro : W → Front X → (ℕ → Stretch) → PS) (tr : W → Front X → (ℕ → Stretch) → PS → List Tree)
    (Bk : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (c : RowCoins [(firstPart ⟨p, ms, none, r, ro, tr⟩ : Part V W X),
      restPart ⟨p, ms, none, r, ro, tr⟩])
    (h : lendRow Bk rows look p.place
      [(firstPart ⟨p, ms, none, r, ro, tr⟩ : Part V W X), restPart ⟨p, ms, none, r, ro, tr⟩] 0 =
        .ok c)
    (w : W) (fr : Front X) (hT : tiesOB Bk p.place ms.length = true)
    (hrows : ∀ mem mem' : ℕ → Stretch, (∀ t, t < ms.length → mem t = mem' t) →
      μOf (sgOf (TestJob.s₀ ⟨p, ms, none, r, ro, tr⟩)) (ro w fr mem) =
        μOf (sgOf (TestJob.s₀ ⟨p, ms, none, r, ro, tr⟩)) (ro w fr mem')) :
    Agree ⟨p, ms, none, r, ro, tr⟩ w fr (TestJob.s₀ ⟨p, ms, none, r, ro, tr⟩)
      (firstRd ⟨p, ms, none, r, ro, tr⟩ c.1) (restCoins ⟨p, ms, none, r, ro, tr⟩ c.2.1) := by
  unfold tiesOB at hT
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hT
  obtain ⟨⟨t2, t3⟩, t4⟩ := hT
  obtain ⟨e₂, he₂, k2⟩ := Option.map_eq_some_iff.1 t2
  refine agree_own p ms r ro tr Bk rows look c h w fr e₂ he₂ (congrArg (·.1) k2)
    (congrArg (·.2) k2) (fun t ht => ?_) hrows
  have e := congrArg (·[t]?) t4
  simp only [List.getElem?_map, List.getElem?_take, if_pos ht] at e
  obtain ⟨a, ha⟩ : ∃ a, (carryE Bk ⟨p.place, 0⟩)[t]? = some a :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  rw [ha, Option.map_some] at e
  obtain ⟨a', ha', k3⟩ := Option.map_eq_some_iff.1 e.symm
  exact ⟨a, a', ha, ha', (congrArg (·.1) k3).symm, (congrArg (·.2.1) k3).symm,
    (congrArg (·.2.2) k3).symm⟩

end ProofFile.Honest.K12.Own

#print axioms ProofFile.Honest.K12.Own.own_is_carried
#print axioms ProofFile.Honest.K12.Own.agree_own
#print axioms ProofFile.Honest.K12.Own.tiesOB
#print axioms ProofFile.Honest.K12.Own.agree_of_tiesO
