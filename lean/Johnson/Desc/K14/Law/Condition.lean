-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/Condition.lean: the condition under which the laws of the linear claim's shared
rounds are stated, as one record with a test for each part that can be computed.

Main names: Condition, conditionB, condition_iff (the public part: the public shape's conditions and
two codes), linPoint_ok ("LIN point" asks the first itself), placedU_of_seated,
premises_of_seated (Condition and Seated give the two premises of the law of (fold)).

What is not claimed. That Seated holds behind the two sendings of a run: Placed.lean shows it of two
receivings of oracle messages and statements that grow. Nothing on (rec_gamma) and (loc_x) pinning
the folded row. Nothing on soundness of a verifier.

-/
import Johnson.Desc.K14.Law.MeansLoc
import Johnson.Desc.Own.LinAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Model (Reading)
open OnBytes.Means (Words)
open VerifiableInference.Desc.Ground (ok)

/-- **The public condition**: on the codes and the public shape alone. -/
structure Condition (codes : Codes) (S : LinShape) : Prop where
  /-- the public shape's conditions, with the codes that it names -/
  shape : linOk codes S = true
  /-- o_u and o_omega have two codes, so that (fold) is split -/
  twoCodes : S.sharedSplitNeeded = true

/-- The public condition as a test. -/
def conditionB (codes : Codes) (S : LinShape) : Bool := linOk codes S && S.sharedSplitNeeded

/-- The public condition holds just if its test says yes. -/
theorem condition_iff (codes : Codes) (S : LinShape) :
    Condition codes S ↔ conditionB codes S = true := by
  unfold conditionB
  rw [Bool.and_eq_true]
  exact ⟨fun h => ⟨h.shape, h.twoCodes⟩, fun h => ⟨h.1, h.2⟩⟩

/-- "LIN point" asks the public shape's conditions itself. -/
theorem linPoint_ok (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : linPoint p d rs = some d') :
    linOk d.st.codes p.S = true := by
  unfold linPoint at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨u0, hg, _⟩ := h
    have hok : ok (linPointL p d) = true := by
      by_contra hne
      simp [guard, hne] at hg
    simp only [ok, linPointL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hok
    exact (VerifiableInference.Desc.Own.linFits_eq _ _).symm.trans hok.2
  · cases h

/-- The message o_u has its table, which holds a row's message and its random tail. -/
theorem placedU_of_seated {T : Statement} {codes : Codes} {S : LinShape} {l : Lin}
    (h : Seated T codes S l) (hok : linOk codes S = true) : PlacedU T S.fold l.oU := by
  have hP := placed_of_seated h hok
  simp only [linOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  have hF : foldeqOk codes S.fold = true := by tauto
  simp only [foldeqOk, Bool.and_eq_true, decide_eq_true_eq] at hF
  have c2 : S.fold.entries ≤ vectorRoom codes S.fold.u S.fold.rowsHigh := by tauto
  have hE : S.fold.entries ≤ 2 ^ l.oU.lay.bits := by
    rw [h.lay]; exact Nat.le_trans c2 (vectorRoom_le _ _ _)
  have e2 : S.fold.index.code.ell ≤ S.fold.tailFirst := le_roundUp _ _ (Nat.two_pow_pos _)
  unfold FoldeqShape.entries at hE
  refine ⟨hP.hasU, hP.bitsU, ceilLog2_le _ _ (by omega), hE, ?_⟩
  unfold FoldeqShape.tailFirst
  exact Nat.mul_mod_left _ _

/-- The public condition and the messages' seats give the two premises of the law of (fold). -/
theorem premises_of_seated (p : Par) (d : St) (T : Statement)
    (hC : Condition d.st.codes p.S) (hS : Seated T d.st.codes p.S d.loc) :
    Placed T p.S d.loc (linLayOmega d.st.codes p.S) ∧ p.S.sharedSplitNeeded = true :=
  ⟨placed_of_seated hS hC.shape, hC.twoCodes⟩

end Desc.K14.Law
