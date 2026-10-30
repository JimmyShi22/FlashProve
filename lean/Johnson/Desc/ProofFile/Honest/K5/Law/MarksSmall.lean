-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/MarksSmall.lean: CONDITIONAL ON THE HYPOTHESIS ON THE PUBLIC
INPUT: HOW LONG THE LISTS OF ROUNDS OF THE TWO MARKS OF AN ATTENTION SEGMENT's OWN ROUNDS ARE (138;
at most 33), AND: THE VALUE OF EACH OF THE 24 STATED SHARES IS BELOW 1. Six theorems; no definition.
No property is claimed.

Why. A sentence `MarkDebt` at a number of 1 or more says nothing: a measure is at most 1. The
sentences of Law/MarksDebt.lean stand at the marks' own stated shares' values; here these are shown
to be below 1.

Main names:
  `own_head` under the head the eleven numbers of a group's own rounds are the written ones
    (`H2K5.Row.ownW`, Johnson/Desc/First/Att/Row/K5OwnW.lean), by `H2K5.Row.own_in_scope`
    (K5OwnInScope.lean beside it)
  `live_length_head` the second mark lists 138 rounds: `liveRounds_length`
    (Johnson/Desc/K5/Honest/Law/LiveCount.lean) at these numbers
  `reads_length_head` the first mark lists at most 33: `readRounds_length` and `reads_fit`
    (ReadRounds.lean beside it): twice the bits of a token and the bits of a slot are at most the
    variables of two sumchecks, 13 and 20. The number itself is not shown
  `mkLive_small_head`, `mkReads_small_head` so each share's value is below 1, by `pair_small`
    (Law/MarksDebt.lean)
  `k5Marks_small`   **every mark of `k5Marks` has a stated share whose value is below 1**

Limits. "BELOW 1" IS ALL THAT IS SAID OF A VALUE: none is evaluated, no number of bits is stated,
and how large the 24 are together is not said. `pair_small` spends 2 ^ 64 where 138 and 66 would do:
the bound is far from sharp. ALL SIX ARE CONDITIONAL on h: at the library's full size and the
format's second hash function alone. It can be met: AtFullSide.Top.headMember_zFull
(AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it is worth).
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.MarksDebt
import Johnson.Desc.First.Att.Row.K5OwnInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First
open H2K5.Honest (liveRounds readRounds liveRounds_length readRounds_length reads_fit
  public_at_head)
open P5J (AtMgA TS)
open scoped ENNReal

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place}

/-- **Under the head the eleven numbers of a group's own rounds are the written ones.** Conditional:
h; hg; ea. -/
theorem own_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} (ea : (P5J.At.X Zp).A[g]? = some a) :
    a.own = { H2K5.Row.ownW with rows := a.own.rows } :=
  H2K5.Row.own_in_scope h.scope h.reads h.pubOne hg ea

/-- **The second mark lists 138 rounds.** Conditional: h; hg; ea. -/
theorem live_length_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} (ea : (P5J.At.X Zp).A[g]? = some a) :
    (liveRounds a.own).length = 138 := by
  obtain ⟨ρ, e⟩ : ∃ ρ, a.own = { H2K5.Row.ownW with rows := ρ } := ⟨_, own_head h hg ea⟩
  rw [liveRounds_length, e]
  rfl

/-- **The first mark lists at most 33 rounds.** Conditional: h; hg; ea. -/
theorem reads_length_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} (ea : (P5J.At.X Zp).A[g]? = some a) :
    (readRounds a.own (Att.P.parCOf a).geo).length ≤ 33 := by
  obtain ⟨ρ, e⟩ : ∃ ρ, a.own = { H2K5.Row.ownW with rows := ρ } := ⟨_, own_head h hg ea⟩
  have Pu := public_at_head h hg ea
  obtain ⟨f1, f2⟩ := reads_fit Pu.sized Pu.planned
  have g1 : (Att.P.parCOf a).geo.lgk + (Att.P.parCOf a).geo.lt ≤ a.own.e := f1
  have g2 : (Att.P.parCOf a).geo.lt + (Att.P.parCOf a).geo.lgk + (Att.P.parCOf a).geo.ls ≤
      a.own.attained := f2
  have n1 : a.own.e = 13 := by rw [e]; rfl
  have n2 : a.own.attained = 20 := by rw [e]; rfl
  rw [readRounds_length]
  omega

/-- **The second mark's stated share's value is below 1.** Conditional: h; hg; ea. -/
theorem mkLive_small_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} (ea : (P5J.At.X Zp).A[g]? = some a) :
    (mkLive (2 * g + 1) a.own).share.val < 1 :=
  pair_small (1 * (liveRounds a.own).length) (by
    rw [live_length_head h hg ea]
    norm_num)

/-- **The first mark's stated share's value is below 1.** Conditional: h; hg; ea. -/
theorem mkReads_small_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} (ea : (P5J.At.X Zp).A[g]? = some a) :
    (mkReads (2 * g + 1) a.own (Att.P.parCOf a).geo).share.val < 1 :=
  pair_small (2 * (readRounds a.own (Att.P.parCOf a).geo).length) (by
    have := reads_length_head h hg ea
    calc 2 * (readRounds a.own (Att.P.parCOf a).geo).length ≤ 2 * 33 :=
          Nat.mul_le_mul_left 2 this
      _ ≤ 2 ^ 64 := by norm_num)

/-- **EACH OF THE MARKS OF THE LIST HAS A STATED SHARE WHOSE VALUE IS BELOW 1**: so the sentences of
Law/MarksDebt.lean at these values are no idle ones. Conditional: h: the head; hB: the base's
return. -/
theorem k5Marks_small (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    ∀ mk ∈ k5Marks Zp Bs.G₀, mk.share.val < 1 := by
  intro mk hm
  obtain ⟨b, hb, hp⟩ := k5Marks_stands h hB mk hm
  obtain ⟨g, hg, a, ea, -, rfl | rfl⟩ := k5Marks_member_is_head h hB hm hb hp.symm
  · exact mkReads_small_head h hg ea
  · exact mkLive_small_head h hg ea

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.own_head
#print axioms ProofFile.Honest.K5.live_length_head
#print axioms ProofFile.Honest.K5.reads_length_head
#print axioms ProofFile.Honest.K5.mkLive_small_head
#print axioms ProofFile.Honest.K5.mkReads_small_head
#print axioms ProofFile.Honest.K5.k5Marks_small
