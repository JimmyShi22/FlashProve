-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/SaysAtFall.lean

What it proves. A fact that takes away from AsksWhole.lean. The sentence on values SaysAt
(AsksWhole.lean) holds for nothing wherever the job's state on entry is the fall-back fallU
(ShapeBehind.lean): at every input, whatever precedes the test, and all random values, whatever the
job's rows are. For fallU is made of lift (Johnson/Desc/K14/Shape/Up.lean), whose rows have no
summand and the right side 0: each says 0 = 0 of all words. And doorUF (DoorsByShape.lean) gives
fallU wherever the fold over the blocks in front of the test fails. So there both premises of
asks_head can be had without anything honest: heardFit is on the form of the challenges, and SaysAt
is empty.

What follows for a reader. A statement that rests on SaysAt at doorUF says nothing on a run where
the fold fails. Whoever uses asks_head or asks_heard for a statement on an honest prover has to show
two things besides: that the fold returns (the seat's way in, enter, always returns:
Johnson/Desc/K12/Seat.lean), and that the columns which the reader cols hands the fold are the run's
own: cols is a free function, and a fold that returns at other columns gives a state that is not the
verifier's. Nothing shows either here; DoorReturns.lean and DoorOfFold.lean have a reader of the
input with which the fold returns at the test on G_u, under premises that their heads name. SaysAt
also holds for nothing where the state has no group of the number under test.

Names.
  Bare, says_of_bare   a row without a summand and with the right side 0 says its claim of all
      words.
  bare_lift_rows, bare_lift_samples   the open rows and the sample rows of lift's statement are
      such.
  allSay_lift   so are all rows that a test on one of its groups takes in.
  saysAt_fallU   SaysAt at a job whose state on entry is fallU.
  doorUF_fails   where the fold fails, doorUF gives fallU.
  saysAt_fails   SaysAt at a job with doorUF, where the fold fails.

By what. mem_samples (Johnson/Desc/Means/Order.lean). says_of_bare's proof follows that of says_bare
(Johnson/Desc/K12/Coin/ChecksAtO.lean), which is on the right side 1.

Limits. Nothing is said where the fold returns. The test on G_u alone. It stands over files that are
not in the library yet, as MarksBehind.lean does. Nothing on completeness, on soundness or on what a
view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.AsksWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (Statement Group Oracle Row OracleNotice TableKey zeroE)
open OnBytes.Slice (rdE runRows)
open OnBytes.Means (AllSay Says Words value onTable mem_samples)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks)
open Desc.K14 (P14 St first)
open Desc.K14.Shape (Sh2 lift grpLift orcLift)
open ProofFile.Honest.K12 (TestCoins)

variable {W X : Type}

/-- A row without a summand and with the right side 0. -/
def Bare (r : Row) : Prop :=
  r.terms = #[] ∧ r.units = #[] ∧ r.runs = #[] ∧ r.forms = #[] ∧ r.target = zeroE

/-- Such a row says its claim of all words, at every statement: 0 = 0. -/
theorem says_of_bare {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K) (S : Statement) (r : Row)
    (m : Words K) (h : Bare r) : Says ρ S r m := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hc : ∀ o part i, r.coefficient o part i = zeroE := by
    intro o part i
    unfold OnBytes.Row.coefficient
    rw [h1, h2, h3, h4]
    rfl
  unfold Says value onTable
  simp only [hc, ρ.zero, zero_mul, Finset.sum_const_zero, add_zero, h5]

theorem bare_lift_rows (a : Sh2) (g : ℕ) (G : Group) (hG : (lift a).st.groups[g]? = some G) :
    ∀ r ∈ G.rows.toList, Bare r := by
  intro r hr
  have e : (lift a).st.groups = (a.core.st.groups.map grpLift).toArray := rfl
  rw [e, List.getElem?_toArray, List.getElem?_map] at hG
  obtain ⟨Gs, -, rfl⟩ := Option.map_eq_some_iff.1 hG
  have hr' : r ∈ Gs.kinds.map fun k => ({ kind := k } : Row) := hr
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hr'
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem bare_lift_samples (a : Sh2) (o : ℕ) (x : Oracle) (hx : (lift a).st.oracles[o]? = some x) :
    ∀ r ∈ x.sampleRows.toList, Bare r := by
  intro r hr
  have e : (lift a).st.oracles = (a.core.st.oracles.map orcLift).toArray := rfl
  rw [e, List.getElem?_toArray, List.getElem?_map] at hx
  obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.1 hx
  have hr' : r ∈ (Array.replicate y.rows (default : Row)).toList := hr
  rw [Array.toList_replicate] at hr'
  obtain rfl := List.eq_of_mem_replicate hr'
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **All rows that a test on a group of lift's statement takes in say their claims of all words**,
at every statement at which the tables' sizes are read. -/
theorem allSay_lift (a : Sh2) (g : ℕ) (G : Group) (hG : (lift a).st.groups[g]? = some G)
    (S : Statement) (m : Words Cb.Gl.E) : AllSay rdE S (runRows (lift a).st G).toList m := by
  intro r hr
  refine says_of_bare rdE S r m ?_
  unfold runRows at hr
  simp only [Array.toList_append, List.mem_append, Array.toList_filter, List.mem_filter] at hr
  rcases hr with (c | c) | c
  · exact bare_lift_rows a g G hG r c.1
  · rw [← Array.foldl_toList] at c
    rcases mem_samples (lift a).st r _ _ c with c' | ⟨o, _, x, hx, hr''⟩
    · simp at c'
    · exact bare_lift_samples a o x hx r hr''
  · exact bare_lift_rows a g G hG r c.1

/-- **SaysAt holds for nothing where the state on entry is fallU.** -/
theorem saysAt_fallU (A : ManyJob W X) (Q : P14) (sentU : Array OracleNotice) (w : W)
    (fr : Front X) (h : A.rec₀ w fr = fallU Q sentU) (C : TestCoins) : SaysAt A w fr C := by
  intro G hG
  rw [h] at hG ⊢
  exact allSay_lift (endOf Q sentU) _ G hG _ _

/-- Where the fold over the blocks in front of the test fails, doorUF gives fallU. -/
theorem doorUF_fails (Q : P14) (sentU : Array OracleNotice) (bs : List (Block St Unit))
    (key : W → TableKey) (cols : W → Front X → List OpenedColumn) (w : W) (fr : Front X) (e : String)
    (h : foldBlocks 0 bs (first Q.codes (key w)) fr.seen.rounds (cols w fr) = .error e) :
    doorUF Q sentU bs key cols w fr = fallU Q sentU := by
  unfold doorUF doorOf
  simp only [h]

/-- **SaysAt at a job with doorUF, where the fold fails**: at all random values, whatever the job's
rows are. -/
theorem saysAt_fails (A : ManyJob W X) (Q : P14) (sentU : Array OracleNotice)
    (bs : List (Block St Unit)) (key : W → TableKey) (cols : W → Front X → List OpenedColumn)
    (hA : A.rec₀ = doorUF Q sentU bs key cols) (w : W) (fr : Front X) (e : String)
    (h : foldBlocks 0 bs (first Q.codes (key w)) fr.seen.rounds (cols w fr) = .error e)
    (C : TestCoins) : SaysAt A w fr C :=
  saysAt_fallU A Q sentU w fr (by rw [hA]; exact doorUF_fails Q sentU bs key cols w fr e h) C

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.Bare
#print axioms ProofFile.Honest.K12.Light.says_of_bare
#print axioms ProofFile.Honest.K12.Light.bare_lift_rows
#print axioms ProofFile.Honest.K12.Light.bare_lift_samples
#print axioms ProofFile.Honest.K12.Light.allSay_lift
#print axioms ProofFile.Honest.K12.Light.saysAt_fallU
#print axioms ProofFile.Honest.K12.Light.doorUF_fails
#print axioms ProofFile.Honest.K12.Light.saysAt_fails
