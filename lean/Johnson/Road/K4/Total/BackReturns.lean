-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Total/BackReturns.lean: THE OTHER DIRECTION, FOR K4's RUN "back": BEHIND K4's
HEARING THE LISTING `formsBack o Fb` (OnBytes/Desc/First/K4/Plain.lean) RETURNS, at every ledger Fb
with arrays of the right sizes in which the window of the merge's sumcheck is there and free; and
that window IS there and free in the ledger that the hearing leaves, if the ledger from which it
started had arrays of the right sizes and was free from its next free number on. Statements and
proofs.

Why. Every law on K4's two runs of claims begins "where the run returns". K4's block's decision is
its hearing alone: the runs are called at the batching. A test on the record that asks the run
itself ("every form that the run gives names only what is there") is false where the run is silent:
so whoever promises that test behind a yes of K4's block owes the return.

  `ownClaim_returns`: a sumcheck's own claim is made wherever its four marks stand (no claim made
    yet; begun; a variable; as many challenges as variables) and its window is there and free, in a
    ledger with arrays of the right sizes (`hideRun_returns`, `pscRow_returns`:
    OnBytes/Desc/First/P1/Returns.lean).
  `merge_ready`: behind the merge's hearing its sumcheck has the four marks (`mergeHear_inv`).
  **`back_returns`**: the statement on top, first half. `back_part`: it is the part `BackPart` of
    the law's statement (Total/Returns.lean, where `Ready` and `WinFree` are defined).
  `merge_win_free`: behind the merge's hearing from a sized ledger whose slots from its next free
    number on are free: the window is there and free (the hearing fills one slot, behind the
    window).
  **`back_win_free`**: the statement on top, second half: behind K4's whole hearing.
  `back_list`: the list does not hang on the ledger: at any two ledgers at which the listing returns
    it returns one list.

Limits. ONLY "back". "There and free" at the ledger from which "back" is really called (behind the
run "front", or at a border's record) is the caller's: RunsSpare.lean says what "front" turns. The
premise "free from the next free number on" is the table of joints' item freeAbove. Nothing on what
a form is worth. K04_law, the law of K4's block itself, IS NOT PROVED. Nothing on soundness.

-/
import Johnson.Road.K4.Total.Returns
import Johnson.Road.K4.Slots.RunsSpare
import Johnson.Road.K4.MergeSizes
import OnBytes.Desc.First.P1.Returns

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Total

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub HPlan2 Own Heard)
open OnBytes.PscRun (Sized Filled Later)
open OnBytes.Psc (Weight)
open OnBytes.Desc.First.P1 (hideRun_returns pscRow_returns)
open OnBytes.Desc.First.K4.Slots (Spares Fresh SameAt run_same win_three front_fills merge_next)
open VerifiableInference.Desc.First.MergeLaw (hear_of_flat mergeHear_inv)

/-- A sumcheck's own claim is made: where its four marks stand, in a sized ledger in which its
window is
there and free. -/
theorem ownClaim_returns {p : Psc} (hp : Ready p) (S0 : E) (kept : Aff) {F : Fork} (hF : Sized F)
    (hw : WinFree p F) : ∃ G, ownClaim p S0 kept F = some (p.rowForm S0 kept, G) := by
  obtain ⟨G, hG⟩ := hideRun_returns (first := p.first)
    (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) hF
    (fun i hi => hw i (by simpa using hi))
  refine ⟨G, ?_⟩
  unfold ownClaim
  rw [pscRow_returns hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 S0 kept [] hG]
  rfl

/-- Behind the merge's hearing its sumcheck has the four marks. -/
theorem merge_ready {lay : WsLay} {cl : Array WsClaim} {sv : Array ℕ} {F G : Fork} {t u : Tape}
    {wo : WsForkOut} (h : flatForkEnd lay cl sv F t = some (wo, G, u)) :
    Ready wo.toWsMerged.p := by
  obtain ⟨_, _, _, _, beta, v, _, _, _, _, qs, hq, _, _, _, _, _, _, _, _, hr, _, _, _, _, hv,
    _, _, hs, hm, _⟩ := mergeHear_inv (hear_of_flat h)
  refine ⟨hm, hs, ?_, ?_⟩
  · have : wo.p.vars.toList ≠ [] := by
      rw [hv]
      simp
    cases e : wo.p.vars.isEmpty with
    | false => rfl
    | true =>
      exfalso
      apply this
      have := Array.isEmpty_iff.mp e
      rw [this]
  · have a : wo.p.r.toList.length = lay.lk + 1 := by
      rw [hr]
      simp [hq]
    have b : wo.p.vars.toList.length = lay.lk + 1 := by
      rw [hv]
      simp
    have a' : wo.p.r.size = lay.lk + 1 := by simpa using a
    have b' : wo.p.vars.size = lay.lk + 1 := by simpa using b
    show wo.p.r.size = wo.p.vars.size
    rw [a', b']

variable {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own} {F G : Fork} {t u : Tape}

/-- **Behind K4's hearing the listing "back" returns**, at every sized ledger in which the merge's
window is there and free. -/
theorem back_returns (h : hear engFl P hp g fo F t = some (o, G, u)) {Fb : Fork} (hb : Sized Fb)
    (hw : WinFree o.wo.toWsMerged.p Fb) : ∃ fs Gb, formsBack o Fb = some (fs, Gb) := by
  obtain ⟨_, _, _, _, H1, hd2, cl, G1, G2, G3, G4, G5, u1, u2, u3, u4, u5, _, _, _, _, _, _,
    _, _, hE⟩ := hear_parts h
  obtain ⟨Gm, hm⟩ := ownClaim_returns (merge_ready hE) o.wo.toWsMerged.fvp {} hb hw
  refine ⟨(back o (o.wo.toWsMerged.p.rowForm o.wo.toWsMerged.fvp {})).toArray,
    Gm.paid o.H.fo.owedJoin, ?_⟩
  unfold formsBack
  rw [hm]
  rfl

/-- The part, in the statement's own words. -/
theorem back_part : BackPart :=
  fun _ _ _ _ _ _ _ _ _ _ h hb hw => back_returns h hb hw

/-- The list does not hang on the ledger. -/
theorem back_list {Fa Fb Ga Gb : Fork} {fa fb : Array Aff} (ha : formsBack o Fa = some (fa, Ga))
    (hb : formsBack o Fb = some (fb, Gb)) : fa = fb := by
  obtain ⟨_, ea, _⟩ := formsBack_some ha
  obtain ⟨_, eb, _⟩ := formsBack_some hb
  rw [ea, eb]

/-- Behind the merge's hearing, from a sized ledger that is free from its next free number on, the
window is there and free. -/
theorem merge_win_free {lay : WsLay} {cl : Array WsClaim} {sv : Array ℕ} {F G : Fork} {t u : Tape}
    {wo : WsForkOut} (hF : Sized F) (hfree : ∀ j, F.next ≤ j → ¬ Filled F j)
    (h : flatForkEnd lay cl sv F t = some (wo, G, u)) : WinFree wo.toWsMerged.p G := by
  obtain ⟨_, _, _, _, beta, v, _, _, _, _, qs, hq, _, _, _, _, _, _, _, _, _, hsF, hh, hsh, _, hv,
    hfirst, _⟩ := mergeHear_inv (hear_of_flat h)
  have hlen : wo.p.walk.1.length ≤ 1 + 2 * lay.lk + 1 := by
    have := win_three wo.p (List.replicate lay.lk (Weight.plain 3)) 1
      (fun w hw => by rw [List.eq_of_mem_replicate hw]; rfl) hv
    simpa using this
  obtain ⟨sG, _, same⟩ :=
    run_same (show Sized ({ F with next := F.next + 1 + 2 * lay.lk + 2 } : Fork) from hF) hh
  have hns : wo.sFv < G.ns := by
    unfold Fork.shown at hsh
    by_cases c : (decide (wo.sFv < G.ns) && G.gotF.getD wo.sFv false) = true
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at c
      exact c.1
    · rw [if_neg c] at hsh
      cases hsh
  intro i hi
  have hi' : wo.p.first + i < wo.sFv := by
    have : i < wo.p.walk.1.length := hi
    rw [hfirst, hsF]
    omega
  refine ⟨Nat.lt_trans hi' hns, fun hfil => ?_⟩
  have s := same (wo.p.first + i) (Or.inl hi')
  exact hfree (wo.p.first + i) (by rw [hfirst]; omega) (s.1.mp hfil)

/-- **Behind K4's whole hearing, from a sized ledger that is free from its next free number on, the
merge's window is there and free.** -/
theorem back_win_free (hF : Sized F) (hfree : ∀ j, F.next ≤ j → ¬ Filled F j)
    (h : hear engFl P hp g fo F t = some (o, G, u)) : WinFree o.wo.toWsMerged.p G := by
  obtain ⟨_, _, _, _, H1, hd2, cl, G1, G2, G3, G4, G5, u1, u2, u3, u4, u5, hN, hT, hS, hG, _, hM,
    _, _, hE⟩ := hear_parts h
  obtain ⟨s1, f1⟩ := Spares.fresh hN hF
  obtain ⟨s2, f2⟩ := Spares.fresh hT s1
  obtain ⟨s3, f3⟩ := Spares.fresh hS s2
  obtain ⟨s4, f4⟩ := Spares.fresh hG s3
  obtain ⟨s5, f5⟩ : Sized G5 ∧ Fresh G4 G5 := by
    unfold mergeFront at hM
    by_cases hg : (g == 0) = true
    · rw [if_pos hg] at hM
      exact Spares.fresh hM s4
    · rw [if_neg hg] at hM
      obtain ⟨_, rfl, _⟩ := hM
      exact ⟨s4, Fresh.refl _⟩
  have f := (((f1.trans f2).trans f3).trans f4).trans f5
  refine merge_win_free s5 (fun j hj hfil => ?_) hE
  exact hfree j (Nat.le_trans f.next hj) ((f.same j (Or.inr hj)).1.mp hfil)

end OnBytes.Desc.First.K4.Total

#print axioms OnBytes.Desc.First.K4.Total.ownClaim_returns
#print axioms OnBytes.Desc.First.K4.Total.back_returns
#print axioms OnBytes.Desc.First.K4.Total.back_part
#print axioms OnBytes.Desc.First.K4.Total.back_win_free
#print axioms OnBytes.Desc.First.K4.Total.back_list
