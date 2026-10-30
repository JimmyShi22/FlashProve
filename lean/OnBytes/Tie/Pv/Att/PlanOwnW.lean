-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Att/PlanOwnW.lean: the rounds that the planner adds for an attention sub-proof's own
part, with every field of each round, the error among them.

The planner's routine is planAttentionOwn (OnBytes/Params/SubRounds.lean). Its rounds are given here
as a closed function of the setting s and of the record x : AttentionRounds, for every s and x.

The list is cut into named stretches by one rule. A stretch is either one whole planPsc, from its
round PSC epsilon to its round PSC values, or one single round BAT-sigma or ZERO. planScalars adds
no round: what it sends is counted in the message of the next round that is closed. Each stretch's
definition says these further bytes (24 for a scalar). In the routine's order, each sumcheck under
the words that the comments on the record's fields, and on attentionScd, have for it (no statement
here ties a stretch to a routine of the verifier):
  scoreW   one sumcheck for each member of x.score (unitW). Each has 7 further scalars; the first
           also has the 3 * planeMessages scalars of the routine's first line.
  aEW      the denominator times the output. 5 + lt + 2 further scalars, and those of the first
           line if x.score is empty.
  batVW    a batch of 2 rows, before the two sumchecks of the value product.
  aVMW     the value product off the diagonal. 2 further scalars.
  aVDW     the value product on the diagonal.
  zeroFHW  one message of 2 lgk + 2 lt + 4 elements.
  batFW    a batch of pairs rows. Its own message has pairs scalars.
  aFW      query times key at the maximum.
  batDW    a batch of pairs rows.
  aDW      the key at the index: the one sumcheck of the size attentionScd.
  batHW    a batch of pairs rows.
  aHW      the index bits.

Main names:
  `att_eq`: planAttentionOwn x is the flat chain of its sixteen calls.
  `att_addsW`: AddsW s 0 0 (planAttentionOwn x) (attRounds s x).
  `att_finishW`: the same of the planner's finish.
  `attBounds`, `attRounds_errors`: each round's error is that of its bound, as close counts it.
  `bPsc_sc3`, `bPsc_scd`, `bounds_closed`: the bounds in closed form, as the planner's Bound.ratio.
  `attRounds_beside`: the five other fields of every round.
Limits: att_addsW stands under At s 0 p and under the premise that the routine ends well from p. No
statement says that it does end well, or that the state behind the lookup, which the planner runs
first (attentionRounds), has At s 0. att_finishW speaks of the routine run alone from an empty plan.
No statement says that a bound holds of the protocol. The planner's arithmetic on bounds (ratio, the
product, error) is not opened. The plan's verdict adds the draws' distance from uniform to a round's
error (wholeError); that is not counted here.
-/
import OnBytes.Tie.Pv.Att.PlanCalc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Att.Plan

open OnBytes OnBytes.Params

/-! ### The stretches, as whole rounds -/

/-- The bytes of the scalars of the routine's first line. -/
def planeBytes (x : AttentionRounds) : Nat := 24 * (3 * x.planeMessages)

/-- One score unit u = (variables, pieces), with b bytes open before its 7 scalars. -/
def unitW (s : Setting) (b : Nat) (u : Nat × Nat) : List PlanRound :=
  wPsc s (b + 24 * 7) (attentionSc3 u.1 u.2)

/-- The score units, the first with b bytes open. -/
def unitsW (s : Setting) : Nat → List (Nat × Nat) → List PlanRound
  | _, [] => []
  | b, u :: t => unitW s b u ++ unitsW s 0 t

/-- The bytes that are still open behind the score units. -/
def leftOpen (b : Nat) : List (Nat × Nat) → Nat
  | [] => b
  | _ :: _ => 0

def scoreW (s : Setting) (x : AttentionRounds) : List PlanRound :=
  unitsW s (planeBytes x) x.score
def aEW (s : Setting) (x : AttentionRounds) : List PlanRound :=
  wPsc s (leftOpen (planeBytes x) x.score + 24 * (5 + x.lt + 2)) (attentionSc3 x.e x.pairs)
def batVW (s : Setting) (_x : AttentionRounds) : List PlanRound := [rBat s 0 2]
def aVMW (s : Setting) (x : AttentionRounds) : List PlanRound :=
  wPsc s (24 * 2) (attentionSc3 x.valueM x.pairs)
def aVDW (s : Setting) (x : AttentionRounds) : List PlanRound :=
  wPsc s 0 (attentionSc3 x.valueD x.pairs)
def zeroFHW (s : Setting) (x : AttentionRounds) : List PlanRound :=
  [rZero s 0 (2 * x.lgk + 2 * x.lt + 4)]
def batFW (s : Setting) (x : AttentionRounds) : List PlanRound := [rBat s (24 * x.pairs) x.pairs]
def aFW (s : Setting) (x : AttentionRounds) : List PlanRound :=
  wPsc s 0 (attentionSc3 x.attained x.pairs)
def batDW (s : Setting) (x : AttentionRounds) : List PlanRound := [rBat s 0 x.pairs]
def aDW (s : Setting) (x : AttentionRounds) : List PlanRound :=
  wPsc s 0 (attentionScd x.lt x.lgk x.pairs x.Lam)
def batHW (s : Setting) (x : AttentionRounds) : List PlanRound := [rBat s 0 x.pairs]
def aHW (s : Setting) (x : AttentionRounds) : List PlanRound :=
  wPsc s 0 (attentionSc3 x.bits x.pairs)

/-- The whole list of whole rounds. -/
def attRounds (s : Setting) (x : AttentionRounds) : List PlanRound :=
  scoreW s x ++ aEW s x ++ batVW s x ++ aVMW s x ++ aVDW s x ++ zeroFHW s x ++ batFW s x ++
    aFW s x ++ batDW s x ++ aDW s x ++ batHW s x ++ aHW s x

/-! ### planAttentionOwn -/

theorem leftOpen_zero (l : List (Nat × Nat)) : leftOpen 0 l = 0 := by cases l <;> rfl

theorem addsW_units (s : Setting) : ∀ (b : Nat) (l : List (Nat × Nat)),
    AddsW s b (leftOpen b l)
      (forEach l fun u => planScalars 7 >>= fun _ => planPsc (attentionSc3 u.1 u.2))
      (unitsW s b l)
  | b, [] => AddsW.pure s b
  | b, u :: t =>
    (AddsW.bind
      (AddsW.bind (addsW_scalars s b 7) (addsW_psc s (b + 24 * 7) (attentionSc3 u.1 u.2)))
      (addsW_units s 0 t)).cast rfl (leftOpen_zero t) (by simp [unitsW, unitW])

/-- planAttentionOwn with its one condition laid flat: the routine is this chain. -/
theorem att_eq (x : AttentionRounds) : planAttentionOwn x =
    ((if x.planeMessages != 0 then planScalars (3 * x.planeMessages) else pure ()) >>= fun _ =>
     (forEach x.score fun u => planScalars 7 >>= fun _ => planPsc (attentionSc3 u.1 u.2))
       >>= fun _ =>
     planScalars (5 + x.lt + 2) >>= fun _ =>
     planPsc (attentionSc3 x.e x.pairs) >>= fun _ =>
     planBatSigma 2 >>= fun _ =>
     planScalars 2 >>= fun _ =>
     planPsc (attentionSc3 x.valueM x.pairs) >>= fun _ =>
     planPsc (attentionSc3 x.valueD x.pairs) >>= fun _ =>
     planZero (2 * x.lgk + 2 * x.lt + 4) >>= fun _ =>
     planScalars x.pairs >>= fun _ =>
     planBatSigma x.pairs >>= fun _ =>
     planPsc (attentionSc3 x.attained x.pairs) >>= fun _ =>
     planBatSigma x.pairs >>= fun _ =>
     planPsc (attentionScd x.lt x.lgk x.pairs x.Lam) >>= fun _ =>
     planBatSigma x.pairs >>= fun _ =>
     planPsc (attentionSc3 x.bits x.pairs)) := by
  unfold planAttentionOwn
  by_cases h1 : (x.planeMessages != 0) = true <;>
    simp only [h1, ↓reduceIte, pure_bind, Bool.false_eq_true]

theorem addsW_planes (s : Setting) (x : AttentionRounds) :
    AddsW s 0 (planeBytes x)
      (if x.planeMessages != 0 then planScalars (3 * x.planeMessages) else pure ()) [] := by
  by_cases h1 : (x.planeMessages != 0) = true
  · simp only [h1, if_true]
    exact (addsW_scalars s 0 (3 * x.planeMessages)).cast rfl (by simp [planeBytes]) rfl
  · simp only [h1, if_false, Bool.false_eq_true]
    have h0 : x.planeMessages = 0 := by simpa using h1
    exact (AddsW.pure s 0).cast rfl (by simp [planeBytes, h0]) rfl

/-- planAttentionOwn adds just attRounds: every field of every round. -/
theorem att_addsW (s : Setting) (x : AttentionRounds) :
    AddsW s 0 0 (planAttentionOwn x) (attRounds s x) := by
  rw [att_eq]
  refine (AddsW.bind (addsW_planes s x)
    (AddsW.bind (addsW_units s (planeBytes x) x.score)
    (AddsW.bind (addsW_scalars s _ (5 + x.lt + 2))
    (AddsW.bind (addsW_psc s _ (attentionSc3 x.e x.pairs))
    (AddsW.bind (addsW_bat s 0 2)
    (AddsW.bind (addsW_scalars s 0 2)
    (AddsW.bind (addsW_psc s _ (attentionSc3 x.valueM x.pairs))
    (AddsW.bind (addsW_psc s 0 (attentionSc3 x.valueD x.pairs))
    (AddsW.bind (addsW_zero s 0 (2 * x.lgk + 2 * x.lt + 4))
    (AddsW.bind (addsW_scalars s 0 x.pairs)
    (AddsW.bind (addsW_bat s _ x.pairs)
    (AddsW.bind (addsW_psc s 0 (attentionSc3 x.attained x.pairs))
    (AddsW.bind (addsW_bat s 0 x.pairs)
    (AddsW.bind (addsW_psc s 0 (attentionScd x.lt x.lgk x.pairs x.Lam))
    (AddsW.bind (addsW_bat s 0 x.pairs)
      (addsW_psc s 0 (attentionSc3 x.bits x.pairs))))))))))))))))).cast rfl rfl ?_
  simp only [attRounds, scoreW, aEW, batVW, aVMW, aVDW, zeroFHW, batFW, aFW, batDW, aDW, batHW, aHW,
    List.nil_append, List.append_assoc, Nat.zero_add]

/-- The same of the planner's finish. -/
theorem att_finishW (s : Setting) (x : AttentionRounds) (P : Planned)
    (h : finish s .request (planAttentionOwn x) = .ok P) :
    P.set = s ∧ P.rounds = attRounds s x := by
  unfold finish at h
  split at h
  · cases h
  · rename_i q hq
    split at h
    · cases h
    · obtain rfl := Except.ok.inj h
      obtain ⟨_, el⟩ :=
        att_addsW s x { set := s, scope := .request } q ⟨rfl, rfl, rfl, rfl, rfl⟩ hq
      refine ⟨rfl, ?_⟩
      show q.rounds.toList = _
      rw [el]
      simp

/-! ### The plan's bounds, round by round -/

/-- The error that the plan writes beside a round whose bound is e. none: a round in which the
verifier says nothing. -/
def errorOf (s : Setting) : Option Bound → Binary
  | some e => (scaled s e).error
  | none => {}

/-- The bounds of a sumcheck's rounds. -/
def bPsc (s : Setting) (x : PscSize) : List (Option Bound) :=
  [some (fieldError s 1)] ++ x.degree.map (fun g => some (fieldError s (g - 1))) ++
    (if x.withY then [some (fieldErrorNonzero s x.degreeY), none] else [])

/-- The bounds, in the order of attRounds. -/
def attBounds (s : Setting) (x : AttentionRounds) : List (Option Bound) :=
  (x.score.map fun u => bPsc s (attentionSc3 u.1 u.2)).flatten ++
  bPsc s (attentionSc3 x.e x.pairs) ++
  [some (powersError s 2)] ++
  bPsc s (attentionSc3 x.valueM x.pairs) ++
  bPsc s (attentionSc3 x.valueD x.pairs) ++
  [some (fieldError s (2 * x.lgk + 2 * x.lt + 4))] ++
  [some (powersError s x.pairs)] ++
  bPsc s (attentionSc3 x.attained x.pairs) ++
  [some (powersError s x.pairs)] ++
  bPsc s (attentionScd x.lt x.lgk x.pairs x.Lam) ++
  [some (powersError s x.pairs)] ++
  bPsc s (attentionSc3 x.bits x.pairs)

theorem wPsc_errors (s : Setting) (b : Nat) (x : PscSize) :
    (wPsc s b x).map (·.error) = (bPsc s x).map (errorOf s) := by
  cases h : x.withY <;>
    simp [wPsc, bPsc, h, rEps, rVar, rY, roundOf, quietOf, errorOf, Function.comp_def]

theorem unitsW_errors (s : Setting) : ∀ (b : Nat) (l : List (Nat × Nat)),
    (unitsW s b l).map (·.error) =
      ((l.map fun u => bPsc s (attentionSc3 u.1 u.2)).flatten).map (errorOf s)
  | _, [] => rfl
  | b, u :: t => by
    simp only [unitsW, unitW, List.map_append, List.map_cons, List.flatten_cons, wPsc_errors,
      unitsW_errors s 0 t]

/-- Each round's error is that of its bound, as close counts it. -/
theorem attRounds_errors (s : Setting) (x : AttentionRounds) :
    (attRounds s x).map (·.error) = (attBounds s x).map (errorOf s) := by
  simp only [attRounds, attBounds, scoreW, aEW, batVW, aVMW, aVDW, zeroFHW, batFW, aFW, batDW, aDW,
    batHW, aHW, List.map_append, wPsc_errors, unitsW_errors]
  simp [rZero, rBat, roundOf, errorOf]

/-- A sumcheck of the size attentionSc3: 1 / cardE, then 3 / cardE for each of the nv variables,
then 2 / (cardE - 1), then a round without a bound. -/
theorem bPsc_sc3 (s : Setting) (nv pairs : Nat) : bPsc s (attentionSc3 nv pairs) =
    [some (Bound.ratio 1 s.cardE)] ++ List.replicate nv (some (Bound.ratio 3 s.cardE)) ++
      [some (Bound.ratio 2 (s.cardE - 1)), none] := by
  simp [bPsc, attentionSc3, fieldError, fieldErrorNonzero]

/-- The sumcheck of the size attentionScd: 1 / cardE, then lt times 2 / cardE, lgk times
(lt + 2) / cardE and lt times (lt + 1) / cardE, then (lt + 1) / (cardE - 1), then a round without a
bound. -/
theorem bPsc_scd (s : Setting) (lt lgk pairs Lam : Nat) :
    bPsc s (attentionScd lt lgk pairs Lam) =
      [some (Bound.ratio 1 s.cardE)] ++ List.replicate lt (some (Bound.ratio 2 s.cardE)) ++
        List.replicate lgk (some (Bound.ratio (lt + 2) s.cardE)) ++
        List.replicate lt (some (Bound.ratio (lt + 1) s.cardE)) ++
        [some (Bound.ratio (lt + 1) (s.cardE - 1)), none] := by
  simp [bPsc, attentionScd, fieldError, fieldErrorNonzero]

/-- A batch of rows: (rows - 1) / cardE, where the subtraction stops at 0. A point of v elements:
v / cardE. -/
theorem bounds_closed (s : Setting) (rows v : Nat) :
    powersError s rows = Bound.ratio (rows - 1) s.cardE ∧
      fieldError s v = Bound.ratio v s.cardE := ⟨rfl, rfl⟩

/-! ### The five other fields -/

/-- What stands beside the entry and the error in a round of these lists: no group; the default
word on what a count rests on; a request's scope; the kind field, or zero at PSC values; and the
word's fault is raised just at a batch of 0 rows. -/
def Beside (r : PlanRound) : Prop :=
  r.group = none ∧ r.rests = .johnson ∧ r.scope = .request ∧
    r.why = (if r.entry.name = "PSC values" then .zero else .field) ∧
    r.wordFault = (r.entry.name == "BAT-sigma" && r.entry.rows == 0)

theorem wf_alone (n z : Nat) (e : Binary) :
    wordFaultOf { drawE := n, drawNZ := z, priced := .settingAlone } e = false := by
  unfold wordFaultOf
  cases e.isZero <;> rfl

theorem wf_itself (n z : Nat) (e : Binary) :
    wordFaultOf { drawE := n, drawNZ := z, priced := .roundItself } e = false := by
  unfold wordFaultOf
  cases e.isZero <;> rfl

theorem wf_bat (rows : Nat) (e : Binary) :
    wordFaultOf { drawE := 1, rows := rows, priced := .asSaid } e = (rows == 0) := by
  unfold wordFaultOf
  cases e.isZero <;> cases h : (rows == 0) <;> simp [bne, h]

theorem beside_eps (s : Setting) (b : Nat) : Beside (rEps s b) :=
  ⟨rfl, rfl, rfl, by simp [rEps, roundOf, entryOf], by simp [rEps, roundOf, entryOf, wf_alone]⟩

theorem beside_var (s : Setting) (g : Nat) : Beside (rVar s g) :=
  ⟨rfl, rfl, rfl, by simp [rVar, roundOf, entryOf], by simp [rVar, roundOf, entryOf, wf_itself]⟩

theorem beside_y (s : Setting) (dy : Nat) : Beside (rY s dy) :=
  ⟨rfl, rfl, rfl, by simp [rY, roundOf, entryOf], by simp [rY, roundOf, entryOf, wf_itself]⟩

theorem beside_values (b : Nat) : Beside (quietOf "PSC values" b) :=
  ⟨rfl, rfl, rfl, by simp [quietOf], by simp [quietOf]⟩

theorem beside_zero (s : Setting) (b v : Nat) : Beside (rZero s b v) :=
  ⟨rfl, rfl, rfl, by simp [rZero, roundOf, entryOf], by simp [rZero, roundOf, entryOf, wf_itself]⟩

theorem beside_bat (s : Setting) (b rows : Nat) : Beside (rBat s b rows) :=
  ⟨rfl, rfl, rfl, by simp [rBat, roundOf, entryOf], by simp [rBat, roundOf, entryOf, wf_bat]⟩

theorem beside_psc (s : Setting) (b : Nat) (x : PscSize) : ∀ r ∈ wPsc s b x, Beside r := by
  intro r hr
  unfold wPsc at hr
  rcases List.mem_append.mp hr with h | h
  · rcases List.mem_append.mp h with h | h
    · obtain rfl := List.mem_singleton.mp h
      exact beside_eps s b
    · obtain ⟨g, _, rfl⟩ := List.mem_map.mp h
      exact beside_var s g
  · split at h
    · rcases List.mem_cons.mp h with rfl | h
      · exact beside_y s _
      · obtain rfl := List.mem_singleton.mp h
        exact beside_values _
    · cases h

theorem beside_units (s : Setting) :
    ∀ (b : Nat) (l : List (Nat × Nat)), ∀ r ∈ unitsW s b l, Beside r
  | _, [], _, h => by cases h
  | b, u :: t, r, h => by
    rcases List.mem_append.mp h with h | h
    · exact beside_psc s _ _ r h
    · exact beside_units s 0 t r h

/-- The five other fields of every round. -/
theorem attRounds_beside (s : Setting) (x : AttentionRounds) :
    ∀ r ∈ attRounds s x, Beside r := by
  intro r hr
  simp only [attRounds, scoreW, aEW, batVW, aVMW, aVDW, zeroFHW, batFW, aFW, batDW, aDW, batHW, aHW,
    List.mem_append, List.mem_singleton] at hr
  rcases hr with ((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h
  · exact beside_units s _ _ r h
  · exact beside_psc s _ _ r h
  · exact h ▸ beside_bat s _ _
  · exact beside_psc s _ _ r h
  · exact beside_psc s _ _ r h
  · exact h ▸ beside_zero s _ _
  · exact h ▸ beside_bat s _ _
  · exact beside_psc s _ _ r h
  · exact h ▸ beside_bat s _ _
  · exact beside_psc s _ _ r h
  · exact h ▸ beside_bat s _ _
  · exact beside_psc s _ _ r h

end OnBytes.Tie.Pv.Att.Plan

#print axioms OnBytes.Tie.Pv.Att.Plan.att_eq
#print axioms OnBytes.Tie.Pv.Att.Plan.att_addsW
#print axioms OnBytes.Tie.Pv.Att.Plan.att_finishW
#print axioms OnBytes.Tie.Pv.Att.Plan.attRounds_errors
#print axioms OnBytes.Tie.Pv.Att.Plan.bPsc_sc3
#print axioms OnBytes.Tie.Pv.Att.Plan.bPsc_scd
#print axioms OnBytes.Tie.Pv.Att.Plan.bounds_closed
#print axioms OnBytes.Tie.Pv.Att.Plan.attRounds_beside
