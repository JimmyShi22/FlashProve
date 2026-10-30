-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/TwelveOurs.lean: THE TWELVE TABLES OF THE OUTPUT HEAD's READS IN THE KIND's OWN LETTERS: Law/TieReads.lean's TwelveTrue speaks of the program's record of what was heard (R.x) and of the run's own vectors of weights. HERE: where the run's points and vectors are the kind's letters (RunIs), EACH ENTRY THAT THE FORMS CAN NAME
OF EACH OF THE KIND's TWELVE READS IS WORTH THAT READ IN TRUTH, AT THE READ's OWN WEIGHTS (Head.Read.of, FinalNorm.Read.of: the very terms of TrueReads and of NormReads | NormKeyReads | NormedReads): STATED AND PROVED. AND: WHAT OF RunIs THE SEAT's OWN TEXT PAYS.
  nameH · nameN    a read's table, by the program's name: as the seat has them (Johnson/Stored/HeadSeatAt.lean).
  RunIs R          fourteen clauses and eight on sizes: FIVE ON WHAT THE BLOCK HEARD (PV = pV · wpl.r = squares.r · tV.r = products.r · tN.r = normed.r · tH.r = rH) · FOUR ON THE LOOKUP's POINTS (Zl = zl ++ zt · the position part of the key points of the calls with the segments CNF, ROW and of call qH is zt · the last ls coordinates of
                   call qN's column part are zl) · ONE ON THE REQUEST (the run's marks of the positions with a cost are costed) · THREE THAT THE RUN's OWN ROUTINE tablesOf ASKS (there are calls with the segments CNF and ROW; the cut of call qN's
                   column part returns) · the letters' sizes.
  OursTrue         the twelve: for every read of the head's five and of the normalization's seven, and for "wide".
  cost_phi · cost_rho   the run's two vectors of the positions with a cost read as phiC and as the count's weights.
  ours_of_twelve   RunIs → TwelveTrue → OursTrue.
  heardOf_five     AT x := heardOf g1 H (HeadSeat.lean: what the seat lays into the record behind the block's hearing) THE FIVE CLAUSES ON WHAT THE BLOCK HEARD HOLD BY THE TEXT (rfl).
  last_cut · heardOf_Zl   the clause on Zl, at the letters that the kind takes off the lookup's point (fromLookup), where that point has at least ls + lt coordinates.
  rd_short_congr | rd_long_congr · extract_left | extract_right   small tools.
WHAT IT DOES NOT SAY. **EIGHT OTHER CLAUSES OF RunIs AND THE SIZES ARE PREMISES**: the lookup's other three hang on the layout's numbers of columns (L.calls' lJ against the kind's lJ floor), on which call has which segment, AND ON R.x.qN | qH: heardOf LAYS qN := 0, qH := 0: whether the calls number 0 are the ones that the program's tablesOf means there is NOT HELD: given's own
test ("the calls' key points end in the lookup's point") says that EVERY call's key point ends in (zl, zt), which would make the choice of the call idle for zt: not typed here. The request's clause ties Covered.hOnC to costed: not typed. All that Law/TieReads.lean does not say. Valid e alone: below the table's length. No chance in it.

-/
import Mathlib
import Johnson.Stored.HeadSeat
import Johnson.Desc.Kinds.Law.TieReads

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE oneE)
open OnBytes.Model (Reading World lastOf cutLast longPoint)
open OnBytes.Model.Head (costWeights ztOf zjOf callNo)
open Norm (lt ls d lPd lNI S2 T)

/-- A read's table, by the program's name. -/
def nameH : Read → String
  | .wideAtKeys => "hf@Z" | .wideAtCosts => "hf@phiZ" | .actAtLogits => "hd@r_H"
  | .rowAtCosts => "hr@phiC" | .rowCount => "hr@rhoC"

@[inherit_doc nameH] def nameN : FinalNorm.Read → String
  | .streamAtSquares => "xbL@Z_V" | .streamAtNormed => "xbL@Y_N" | .actAtKeys => "hd@zt_FC"
  | .rowAtKeys => "hr@zt_ROW" | .rowAtPV => "hr@P_V" | .rowAtProducts => "hr@r_tV"
  | .rowAtNormed => "hr@rt_N"

variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] [Norm.Heard] [FinalNorm.Heard] [Heard]

/-- **The run's points and vectors are the kind's letters.** -/
structure RunIs (R : OnBytes.Model.Head.Run) : Prop where
  PV : R.x.PV = Norm.pV
  sq : R.x.wpl.r = Norm.squares.r
  tV : R.x.tV.r = Norm.products.r
  tN : R.x.tN.r = FinalNorm.normed.r
  tH : R.x.tH.r = rH
  Zl : R.x.Zl = FinalNorm.zl ++ FinalNorm.zt
  ztFC : ∀ q, callNo R.L "CNF" = some q → ztOf R.h R.L R.x.g1 q = FinalNorm.zt
  ztROW : ∀ q, callNo R.L "ROW" = some q → ztOf R.h R.L R.x.g1 q = FinalNorm.zt
  ztH : ztOf R.h R.L R.x.g1 R.x.qH = FinalNorm.zt
  low : ∀ lowN, cutLast (zjOf R.L R.x.g1 R.x.qN) R.h.ls = .ok lowN → lowN.2 = FinalNorm.zl
  cov : ∀ t, t < T → R.cov.hOnC.getD t false = costed t
  hasFC : ∃ q, callNo R.L "CNF" = some q
  hasROW : ∃ q, callNo R.L "ROW" = some q
  lowOk : ∀ m, cutLast (zjOf R.L R.x.g1 R.x.qN) R.h.ls ≠ .error m
  szt : (FinalNorm.zt).size = lt
  szl : (FinalNorm.zl).size = ls
  spV : (Norm.pV).size = lt
  ssq : (Norm.squares.r).size = lNI + lPd + lt
  stV : (Norm.products.r).size = lt
  stN : (FinalNorm.normed.r).size = lt
  stH : rH.size = lt
  hls : ls ≤ lNI + lPd

/-- **THE TWELVE, IN THE KIND's OWN LETTERS.** -/
structure OursTrue (W : World K) (R : OnBytes.Model.Head.Run) (K3 : Nat) (c : NCells) : Prop where
  head : ∀ r : Read, EntryIs W R K3 (nameH r) (readAt c.toCells r.of)
  norm : ∀ r : FinalNorm.Read, EntryIs W R K3 (nameN r) (readAtN c r.of)
  wide : EntryIs W R K3 "hf@Z"
    (readAt c.toCells (.wide, .long (eq FinalNorm.zl) (eq FinalNorm.zt)))

namespace Came

omit [Policy] [Request] [Token] [FinalNorm.In] [In] [Norm.Heard] [FinalNorm.Heard] [Heard] in
/-- Two vectors of weights that read alike give sums that read alike. -/
theorem rd_short_congr {g g' : Nat → E} (h : ∀ i, i < T → rd (g i) = rd (g' i)) (x : Nat → E) :
    rd (sumTo T fun i => g i * x i) = rd (sumTo T fun i => g' i * x i) := by
  rw [rd_sumTo, rd_sumTo]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [rd_mul, rd_mul, h i (Finset.mem_range.1 hi)]

omit [Policy] [Request] [Token] [FinalNorm.In] [In] [Norm.Heard] [FinalNorm.Heard] [Heard] in
theorem rd_long_congr {f g g' : Nat → E} (h : ∀ i, i < T → rd (g i) = rd (g' i))
    (x : Nat → Nat → E) :
    rd (sumTo S2 fun j => sumTo T fun i => f j * g i * x j i)
      = rd (sumTo S2 fun j => sumTo T fun i => f j * g' i * x j i) := by
  rw [rd_sumTo, rd_sumTo]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [rd_sumTo, rd_sumTo]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [rd_mul, rd_mul, rd_mul, rd_mul, h i (Finset.mem_range.1 hi)]

omit [Policy] [Token] [In] [Norm.Heard] [FinalNorm.Heard] [Heard] in
/-- The run's vector phiC reads as ours. -/
theorem cost_phi {cov : OnBytes.Model.Head.Covered} (hz : (FinalNorm.zt).size = lt)
    (hc : ∀ t, t < T → cov.hOnC.getD t false = costed t) (i : Nat) (hi : i < T) :
    rd ((costWeights cov FinalNorm.zt).1.getD i zeroE) = rd (phiC i) := by
  have hs : i < (OnBytes.Model.eqTab FinalNorm.zt).size := by
    rw [OnBytes.Road.eqTab_size, hz]
    exact hi
  have e : (costWeights cov FinalNorm.zt).1.getD i zeroE
      = if cov.hOnC.getD i false then (OnBytes.Model.eqTab FinalNorm.zt).getD i zeroE else zeroE := by
    simp [costWeights, Array.getD, hs]
  rw [e, hc i hi]
  unfold phiC
  by_cases hcst : costed i = true
  · rw [if_pos hcst, if_pos hcst]
    exact eqTab_reads _ _ (by rw [hz]; exact hi)
  · rw [if_neg hcst, if_neg hcst]
    exact congrArg rd rfl

omit [Policy] [Token] [In] [Norm.Heard] [FinalNorm.Heard] [Heard] in
/-- The run's vector rhoCv reads as the count's weights. -/
theorem cost_rho {cov : OnBytes.Model.Head.Covered} (hz : (FinalNorm.zt).size = lt)
    (hc : ∀ t, t < T → cov.hOnC.getD t false = costed t) (i : Nat) (hi : i < T) :
    rd ((costWeights cov FinalNorm.zt).2.2.getD i zeroE) = rd (if costed i then (1 : E) else 0) := by
  have hs : i < (OnBytes.Model.eqTab FinalNorm.zt).size := by
    rw [OnBytes.Road.eqTab_size, hz]
    exact hi
  have e : (costWeights cov FinalNorm.zt).2.2.getD i zeroE
      = if cov.hOnC.getD i false then oneE else zeroE := by
    simp [costWeights, Array.getD, hs]
  rw [e, hc i hi]
  split <;> rfl

omit [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] [Norm.Heard] [FinalNorm.Heard] [Heard] in
theorem extract_left (a b : Point) : (a ++ b).extract 0 a.size = a := by
  apply Array.ext'
  simp

omit [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] [Norm.Heard] [FinalNorm.Heard] [Heard] in
theorem extract_right (a b : Point) : (a ++ b).extract a.size (a.size + b.size) = b := by
  apply Array.ext'
  simp

/-- **THE TWELVE IN OUR LETTERS.** -/
theorem ours_of_twelve {W : World K} {R : OnBytes.Model.Head.Run} {K3 : Nat} {c : NCells}
    (I : RunIs R) (hla : R.h.la = ls + lt) (H : TwelveTrue W R K3 c) : OursTrue W R K3 c := by
  have hZs : R.x.Zl.size = ls + lt := by rw [I.Zl, Array.size_append, I.szl, I.szt]
  have eZ1 : R.x.Zl.extract 0 ls = FinalNorm.zl := by
    rw [I.Zl, ← I.szl]
    exact extract_left _ _
  have eZ2 : R.x.Zl.extract ls (ls + lt) = FinalNorm.zt := by
    rw [I.Zl, ← I.szl, ← I.szt]
    exact extract_right _ _
  have hWide : EntryIs W R K3 "hf@Z"
      (readAt c.toCells (.wide, .long (eq FinalNorm.zl) (eq FinalNorm.zt))) := by
    have h := H.hfZ hZs
    rwa [eZ1, eZ2] at h
  refine ⟨fun r => ?_, fun r => ?_, hWide⟩
  · cases r with
    | wideAtKeys => exact hWide
    | wideAtCosts =>
      intro tb hs e hv
      rw [H.hfPhiZ tb hs e hv, I.ztH]
      exact rd_long_congr (cost_phi I.szt I.cov) _
    | actAtLogits =>
      have h := H.hdRH (by rw [I.tH]; exact I.stH)
      rwa [I.tH] at h
    | rowAtCosts =>
      intro tb hs e hv
      rw [H.hrPhiC tb hs e hv, I.ztH]
      exact rd_short_congr (cost_phi I.szt I.cov) _
    | rowCount =>
      intro tb hs e hv
      rw [H.hrRhoC tb hs e hv, I.ztH]
      exact rd_short_congr (cost_rho I.szt I.cov) _
  · cases r with
    | streamAtSquares =>
      -- the last ls + lt coordinates of the squares' challenges
      have hsz : R.x.wpl.r.size = lNI + lPd + lt := by rw [I.sq]; exact I.ssq
      have hle := I.hls
      have hlast : lastOf R.x.wpl.r R.h.la
          = .ok (R.x.wpl.r.extract (R.x.wpl.r.size - R.h.la) R.x.wpl.r.size) := by
        unfold lastOf cutLast
        rw [if_neg (by rw [hsz, hla]; omega)]
        rfl
      have hs2 : (R.x.wpl.r.extract (R.x.wpl.r.size - R.h.la) R.x.wpl.r.size).size = ls + lt := by
        rw [Array.size_extract, hsz, hla]
        omega
      have h := H.xZV _ hlast hs2
      have e1 : (R.x.wpl.r.extract (R.x.wpl.r.size - R.h.la) R.x.wpl.r.size).extract 0 ls
          = Norm.squares.r.extract (lNI + lPd - ls) (lNI + lPd) := by
        rw [hsz, hla, I.sq, Array.extract_extract]
        congr 1 <;> omega
      have e2 : (R.x.wpl.r.extract (R.x.wpl.r.size - R.h.la) R.x.wpl.r.size).extract ls (ls + lt)
          = Norm.squares.r.extract (lNI + lPd) (lNI + lPd + lt) := by
        rw [hsz, hla, I.sq, Array.extract_extract]
        congr 1 <;> omega
      rw [e1, e2] at h
      exact h
    | streamAtNormed =>
      intro tb hs e hv
      cases hl : cutLast (zjOf R.L R.x.g1 R.x.qN) R.h.ls with
      | error m => exact absurd hl (I.lowOk m)
      | ok lowN =>
        have hz := I.low lowN hl
        have hsz : (longPoint lowN.2 R.x.tN.r).size = ls + lt := by
          unfold longPoint
          rw [Array.size_append, hz, I.tN, I.szl, I.stN]
        have h := H.xYN lowN hl hsz tb hs e hv
        have e1 : (longPoint lowN.2 R.x.tN.r).extract 0 ls = FinalNorm.zl := by
          unfold longPoint
          rw [hz, ← I.szl]
          exact extract_left _ _
        have e2 : (longPoint lowN.2 R.x.tN.r).extract ls (ls + lt) = FinalNorm.normed.r := by
          unfold longPoint
          rw [hz, I.tN, ← I.szl, ← I.stN]
          exact extract_right _ _
        rw [e1, e2] at h
        exact h
    | actAtKeys =>
      intro tb hs e hv
      obtain ⟨q, hq⟩ := I.hasFC
      have h := H.hdFC q hq (by rw [I.ztFC q hq]; exact I.szt) tb hs e hv
      rw [I.ztFC q hq] at h
      exact h
    | rowAtKeys =>
      intro tb hs e hv
      obtain ⟨q, hq⟩ := I.hasROW
      have h := H.hrROW q hq (by rw [I.ztROW q hq]; exact I.szt) tb hs e hv
      rw [I.ztROW q hq] at h
      exact h
    | rowAtPV =>
      have h := H.hrPV (by rw [I.PV]; exact I.spV)
      rwa [I.PV] at h
    | rowAtProducts =>
      have h := H.hrTV (by rw [I.tV]; exact I.stV)
      rwa [I.tV] at h
    | rowAtNormed =>
      have h := H.hrTN (by rw [I.tN]; exact I.stN)
      rwa [I.tN] at h

end Came

end VerifiableInference.Desc.Kinds.Head.Law

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open OnBytes (E)
open Norm (lt ls)

/-- **AT WHAT THE SEAT LAYS INTO THE RECORD BEHIND THE BLOCK's HEARING, THE FIVE CLAUSES ON WHAT THE BLOCK HEARD HOLD BY THE TEXT.** -/
theorem heardOf_five [Sizes] [Request] [Token] (g1 : OnBytes.Model.Forest.Heard) (H : HeardAll) :
    letI : Norm.Heard := H.1
    letI : FinalNorm.Heard := H.2.1
    letI : Heard := H.2.2
    (heardOf g1 H).PV = Norm.pV ∧ (heardOf g1 H).wpl.r = Norm.squares.r ∧
      (heardOf g1 H).tV.r = Norm.products.r ∧ (heardOf g1 H).tN.r = FinalNorm.normed.r ∧
      (heardOf g1 H).tH.r = rH :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A point's last a + b coordinates are the first a of these, then its last b. -/
theorem last_cut (z : Point) (a b : Nat) (h : a + b ≤ z.size) :
    (z.last (a + b)).extract 0 a ++ z.last b = z.last (a + b) := by
  unfold Point.last
  have e : min (z.size - (a + b) + a) z.size = z.size - b := by omega
  rw [Array.extract_extract, e, Array.extract_append_extract]
  congr 1 <;> omega

/-- **The clause on Zl**, at the letters that the kind takes off the lookup's point (HeadIn.lean: fromLookup), where that point has at least ls + lt coordinates. -/
theorem heardOf_Zl [Sizes] [Policy] [Request] [Token] (g1 : OnBytes.Model.Forest.Heard)
    (H : HeardAll) (floor : Nat) (zk : Nat → Point) (h : ls + lt ≤ g1.zx.size) :
    (heardOf g1 H).Zl
      = (fromLookup floor g1.zx zk).norm.zl ++ (fromLookup floor g1.zx zk).norm.zt :=
  (last_cut g1.zx ls lt h).symm

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.heardOf_five
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.heardOf_Zl
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.cost_phi
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.ours_of_twelve
