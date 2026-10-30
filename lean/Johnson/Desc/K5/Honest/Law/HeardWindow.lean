-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/HeardWindow.lean: CONDITIONAL: AN ATTENTION SEGMENT's OWN ROUNDS (kind
K5), ON THE VERIFIER's OWN DATA: EVERY SLOT OF WHICH THE KIND's CLAIMS SPEAK, AND EVERY SLOT THAT A
KEY FORM NAMES, LIES IN THE WINDOW OF SLOTS THAT THE KIND's HEARING TAKES: from the ledger's next
slot in front of the hearing up to, not with, the plan's number behind it. Two definitions; eight
statements with their proofs. Over the library alone. No prover is in this file.

  Win lo hi j       lo ≤ j ∧ j < hi
  endOf x k         the next slot behind the slots that the hearing takes from k on, by the plan:
                    the text of k5End (Johnson/Desc/K5/Honest/Law/Live.lean) under a second name,
                    so that this file stands over the library alone; endOf_is (KeysWindow.lean)
                    says that the two are one
  sumAt_len         a sumcheck's coefficients' stretch ends in front of its end values
  sumSlots_win      one sumcheck's record (SumSlots) in a window
  planes_win · unitsNext_ge · units_win   the plan's lists of numbers, in a window
  heardSlots_win    CONDITIONAL: **HeardSlots (Win F.next (endOf x F.next)) g h**
  keys_win          CONDITIONAL: the key forms that the run "first" hands on
  keysRun_win       CONDITIONAL: **every key form that the run "keys" returns names slots of the
                    window alone**

What for. The library's record HeardSlots Ps g h (Johnson/Desc/First/Att/Claims/HeardSlots.lean) is
general in the predicate Ps on slots, and so are the laws that spend it (heard_pts, heard_rows;
keys_slots_K05, keysRun_slots, Claims/SlotsCoveredKeys.lean). The library makes the record at one
predicate: "filled in the ledger behind the hearing". Here it is made at the window: so that a law
on a slot outside the window can say that no key form names it.

The premises. hh: the hearing returns (h, G, rest, lead) from the ledger F · hz: F's arrays have
their length · gf: GeoFits: the place's shape has the plan's numbers: public (geoFits_of_B,
Att/K05PtsSlots.lean, makes it of a Bool) · in the last two: LeftIs; pointsOf's, firstRun's and
keysRun's returns.

THE ROAD. Every number that the hearing lays into its record is the plan's, from F.next on:
numbers_of_plan (Att/K05Numbers.lean) · the sumchecks' start forms: hear_said (Att/K5SaidAll.lean)
with sumAt_start (Att/K05RowsCov.lean) · the hiding polynomial has at most as many weights as the
plan counts slots: hidingAt_length_le (Johnson/Desc/Part/MaskedSumSound.lean) · the two sizes:
om_sizes (Claims/EndsOfPts.lean). The rest is arithmetic. The proof of heardSlots_win has the shape
of the library's heardSlots_of_said, with a bound where that has a mark.

Limits. Conditional. THAT THE PREMISES HOLD TOGETHER AT ANY RECORD IS NOT PROVED HERE: no member, at
no size. Where the hearing, pointsOf or a run does not return, the statements say nothing. The
window says where a named slot lies: nothing on what lies under it, on entries, on a slot that is
filled. That every slot of the window is named is not said. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.Claims.HeardSlots
import Johnson.Desc.First.Att.Claims.SlotsBehind
import Johnson.Desc.First.Att.K05Numbers
import Johnson.Desc.Part.MaskedSumSound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest.Window
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo Heard Left Pts hear GeoFits SumAt UnitsAt products
  keyStage numsOf numsPlan numbers_of_plan planesPlan unitsPlan unitsNext own3 ownOf ownKey kB kE kV
  kM kVD kX kF kD kH)
open K5Law (SlotsIn SlotsJ SumSlots HeardSlots)

/-- The slots from lo up to, not with, hi. -/
def Win (lo hi j : ℕ) : Prop := lo ≤ j ∧ j < hi

/-- The next slot behind the slots that the kind's hearing takes from the slot k on, by the plan. -/
def endOf (x : Params.AttentionRounds) (k : ℕ) : ℕ := kH x k + own3 x.bits + 2 * x.pairs

variable {lo hi : ℕ}

/-- A sumcheck's coefficients' stretch ends in front of its end values. -/
theorem sumAt_len {C : Aff} {st : P.Stage} {pre : List E} {H : OnBytes.Tie.Pv.Att.PscH}
    {hh : MaskedSum.Heard} {G : Fork} (s : SumAt C st pre H hh G) :
    hh.first + (MaskedSum.hidingAt (hh.vars.zip hh.r)).1.length ≤ hh.sEnd := by
  obtain ⟨vs, e, F, G0, used, -, sd, -⟩ := s
  have hl : hh.vars.length = hh.r.length := by
    have h1 := congrArg List.length sd.lens
    rw [List.length_map, List.length_map] at h1
    rw [sd.vars, sd.r, List.length_append, List.length_append, List.length_map, h1]
    rfl
  have hm : (hh.vars.zip hh.r).map (·.1) = hh.vars := List.map_fst_zip (Nat.le_of_eq hl)
  have h2 := MaskedSum.hidingAt_length_le (hh.vars.zip hh.r)
  rw [hm] at h2
  rw [sd.first, sd.sEnd, ← sd.vars]
  omega

/-- One sumcheck's record, in a window. -/
theorem sumSlots_win {C : Aff} {st : P.Stage} {pre : List E} {H : OnBytes.Tie.Pv.Att.PscH}
    {hh : MaskedSum.Heard} {G : Fork} {n : ℕ} (s : SumAt C st pre H hh G)
    (hC : SlotsIn (Win lo hi) C) (h1 : lo ≤ hh.first) (h2 : hh.sEnd + n ≤ hi) :
    SumSlots (Win lo hi) hh n := by
  have hl := sumAt_len s
  refine ⟨by rw [P.sumAt_start s]; exact hC, fun i hi' => ⟨by omega, by omega⟩,
    fun i hi' => ⟨by omega, by omega⟩⟩

/-- Where n runs of three scalars begin, from k on: each run lies from k up to k + 3 n. -/
theorem planes_win : ∀ (n k j : ℕ), j ∈ planesPlan n k → k ≤ j ∧ j + 3 ≤ k + 3 * n
  | 0, _, _, h => by cases h
  | n + 1, k, j, h => by
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := planes_win n (k + 3) j h
      omega

/-- The next slot behind the units does not lie in front of their first. -/
theorem unitsNext_ge : ∀ (us : List (ℕ × ℕ)) (k : ℕ), k ≤ unitsNext us k
  | [], _ => Nat.le_refl _
  | u :: us, k => by
    have := unitsNext_ge us (k + 7 + own3 u.1 + 2 * u.2)
    show k ≤ unitsNext us (k + 7 + own3 u.1 + 2 * u.2)
    omega

/-- The softmax-table units, in a window. -/
theorem units_win {G : Fork} : ∀ (ps : List (ℕ × ℕ)) (os : List (ℕ × MaskedSum.Heard))
    (pre : List E) (l : List (List E × OnBytes.Tie.Pv.Att.PscH)) (k : ℕ), UnitsAt ps os pre l G →
    (os.map fun o => (o.1, o.2.first, o.2.sEnd)) = unitsPlan ps k → lo ≤ k →
    unitsNext ps k ≤ hi → ∀ o ∈ os, (∀ i, i < 7 → Win lo hi (o.1 + i)) ∧
      ∃ t ∈ ps, SumSlots (Win lo hi) o.2 (2 * t.2)
  | [], [], _, [], _, _, _, _, _ => fun _ ho => by cases ho
  | u :: ps, o :: os, _, (_, _) :: l, k, ⟨_, _, a3, _, a5⟩, e, h1, h2 => fun o' ho => by
    have e' : (o.1, o.2.first, o.2.sEnd) :: (os.map fun o => (o.1, o.2.first, o.2.sEnd)) =
        (k, k + 7, k + 7 + own3 u.1) :: unitsPlan ps (k + 7 + own3 u.1 + 2 * u.2) := e
    obtain ⟨e0, et⟩ := List.cons.inj e'
    have c1 : o.1 = k := congrArg (·.1) e0
    have c2 : o.2.first = k + 7 := congrArg (·.2.1) e0
    have c3 : o.2.sEnd = k + 7 + own3 u.1 := congrArg (·.2.2) e0
    have h2' : unitsNext ps (k + 7 + own3 u.1 + 2 * u.2) ≤ hi := h2
    have g := unitsNext_ge ps (k + 7 + own3 u.1 + 2 * u.2)
    rcases List.mem_cons.1 ho with rfl | ho
    · refine ⟨fun i hi' => ⟨by omega, by omega⟩, u, List.mem_cons_self .., ?_⟩
      exact sumSlots_win a3 (OnBytes.Desc.First.K4.Slots.slotsIn_slot ⟨by omega, by omega⟩)
        (by omega) (by omega)
    · obtain ⟨b1, t, ht, b2⟩ := units_win ps os [] l _ a5 et (by omega) h2' o' ho
      exact ⟨b1, t, List.mem_cons_of_mem _ ht, b2⟩
  | [], [], _, _ :: _, _, h, _, _, _ => h.elim
  | [], _ :: _, _, _, _, h, _, _, _ => h.elim
  | _ :: _, [], _, _, _, h, _, _, _ => h.elim
  | _ :: _, _ :: _, _, [], _, h, _, _, _ => h.elim

variable {x : Params.AttentionRounds} {F G : Fork} {rs rest : List Fmt.RoundView} {lead : ℕ} {g : Geo}
  {h : Heard}

/-- **EVERY SLOT OF WHICH THE KIND's CLAIMS SPEAK LIES IN THE WINDOW THAT THE HEARING TAKES.**
CONDITIONAL: the hearing returns from F; F's arrays have their length; GeoFits. -/
theorem heardSlots_win (hh : hear x (F, rs, 0) = some (h, G, rest, lead)) (hz : Road.Sized F)
    (gf : GeoFits g x) : HeardSlots (Win F.next (endOf x F.next)) g h := by
  obtain ⟨L, _, _, _, hs, _, _⟩ := P.hear_said hh hz
  obtain ⟨o1, o2⟩ := K5Law.om_sizes hs gf
  have N := (numbers_of_plan hh hz).1
  have nP : h.remainders.toList = planesPlan x.planeMessages F.next := congrArg (·.planes) N
  have nU : (h.scores.toList.map fun o => (o.1, o.2.first, o.2.sEnd)) =
      unitsPlan x.score (F.next + 3 * x.planeMessages) := congrArg (·.units) N
  have n5 : h.five = kB x F.next := congrArg (·.five) N
  have nI : h.bits = kB x F.next + 5 := congrArg (·.bits) N
  have n2 : h.two = kB x F.next + 5 + x.lt := congrArg (·.two) N
  have nV : h.values = kV x F.next := congrArg (·.values) N
  have nX : h.maxima = kX x F.next := congrArg (·.maxima) N
  have fE : h.division.first = kE x F.next := congrArg (·.fE) N
  have eE : h.division.sEnd = kE x F.next + own3 x.e := congrArg (·.eE) N
  have fM : h.below.first = kM x F.next := congrArg (·.fM) N
  have eM : h.below.sEnd = kM x F.next + own3 x.valueM := congrArg (·.eM) N
  have fVD : h.on.first = kVD x F.next := congrArg (·.fVD) N
  have eVD : h.on.sEnd = kVD x F.next + own3 x.valueD := congrArg (·.eVD) N
  have fF : h.atIndex.first = kF x F.next := congrArg (·.fF) N
  have eF : h.atIndex.sEnd = kF x F.next + own3 x.attained := congrArg (·.eF) N
  have fD : h.key.first = kD x F.next := congrArg (·.fD) N
  have eD : h.key.sEnd = kD x F.next + ownKey x := congrArg (·.eD) N
  have fH : h.cells.first = kH x F.next := congrArg (·.fH) N
  have eH : h.cells.sEnd = kH x F.next + own3 x.bits := congrArg (·.eH) N
  have b0 : F.next + 3 * x.planeMessages ≤ kB x F.next := unitsNext_ge _ _
  have b1 : kE x F.next = kB x F.next + 5 + x.lt + 2 := rfl
  have b2 : kV x F.next = kE x F.next + own3 x.e + 2 * x.pairs := rfl
  have b3 : kM x F.next = kV x F.next + 2 := rfl
  have b4 : kVD x F.next = kM x F.next + own3 x.valueM + 2 * x.pairs := rfl
  have b5 : kX x F.next = kVD x F.next + own3 x.valueD + 2 * x.pairs := rfl
  have b6 : kF x F.next = kX x F.next + x.pairs := rfl
  have b7 : kD x F.next = kF x F.next + own3 x.attained + 2 * x.pairs := rfl
  have b8 : kH x F.next = kD x F.next + ownKey x + (x.Lam + x.pairs * x.lt) := rfl
  have b9 : endOf x F.next = kH x F.next + own3 x.bits + 2 * x.pairs := rfl
  have hU := units_win (lo := F.next) (hi := endOf x F.next) _ _ _ _ _ hs.units nU (by omega)
    (by show kB x F.next ≤ _; omega)
  refine ⟨fun j hj i hi' => ?_, fun o ho => (hU o ho).1, fun y hy => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, o1, o2⟩
  · have := planes_win _ _ j (nP ▸ hj)
    exact ⟨by omega, by omega⟩
  · rw [Array.toList_zip] at hy
    have ho : y.2 ∈ h.scores.toList := (List.of_mem_zip hy).2
    have hu : y.1 ∈ g.scores := by simpa using (List.of_mem_zip hy).1
    obtain ⟨t, ht, b⟩ := (hU y.2 ho).2
    refine ⟨b.start, b.coefs, fun i hi' => b.ends i ?_⟩
    have := gf.pieces y.1 hu
    rw [gf.score t ht]
    omega
  · exact fun i hi' => ⟨by omega, by omega⟩
  · rw [gf.lt]; exact fun i hi' => ⟨by omega, by omega⟩
  · exact fun i hi' => ⟨by omega, by omega⟩
  · exact fun i hi' => ⟨by omega, by omega⟩
  · rw [gf.NP]; exact fun i hi' => ⟨by omega, by omega⟩
  · rw [gf.NP]
    exact sumSlots_win hs.sE (OnBytes.Desc.First.K4.Slots.slotsIn_slot ⟨by omega, by omega⟩)
      (by omega) (by omega)
  · rw [gf.NP]
    exact sumSlots_win hs.sM (OnBytes.Desc.First.K4.Slots.slotsIn_slot ⟨by omega, by omega⟩)
      (by omega) (by omega)
  · rw [gf.NP]
    exact sumSlots_win hs.sVD (OnBytes.Desc.First.K4.Slots.slotsIn_slot ⟨by omega, by omega⟩)
      (by omega) (by omega)
  · rw [gf.NP]
    exact sumSlots_win hs.sF (P.slotsIn_batched _ _ _ _ _ fun b hb => ⟨by omega, by omega⟩)
      (by omega) (by omega)
  · rw [gf.NP, gf.Lam, gf.lt]
    exact sumSlots_win hs.sD (P.slotsIn_batched _ _ _ _ _ fun b hb => ⟨by omega, by omega⟩)
      (by omega) (by omega)
  · rw [gf.NP]
    exact sumSlots_win hs.sH (OnBytes.Desc.First.K4.Slots.slotsIn_ofConst _) (by omega) (by omega)

variable {i : P.Runs.In} {zk : Array (Array E)} {l : Left} {F' : Fork} {K : ℕ} {l₁ : List Aff}
  {j : P.Runs.JoinsP}

/-- **SO DOES EVERY SLOT THAT A KEY FORM NAMES.** CONDITIONAL: as `heardSlots_win`; LeftIs; pointsOf
and the run "first" return. -/
theorem keys_win (hh : hear x (F, rs, 0) = some (h, G, rest, lead)) (hz : Road.Sized F)
    (li : P.LeftIs i.g zk h F' l) (hp : P.pointsOf i.g zk h l = some i.p) (gf : GeoFits i.g x)
    (h1 : P.Runs.firstRun i K = some (l₁, j)) : SlotsJ (Win F.next (endOf x F.next)) j :=
  K5Law.keys_slots_K05 (K5Law.heard_pts (heardSlots_win hh hz gf) hp)
    (K5Law.heard_rows (heardSlots_win hh hz gf) li (K5Law.points_are hp)) h1

/-- The same of what the run "keys" returns. CONDITIONAL: as `keys_win`; the run "keys" returns. -/
theorem keysRun_win {k3 : P.Runs.PadIn} {kf : Array Aff}
    (hh : hear x (F, rs, 0) = some (h, G, rest, lead)) (hz : Road.Sized F)
    (li : P.LeftIs i.g zk h F' l) (hp : P.pointsOf i.g zk h l = some i.p) (gf : GeoFits i.g x)
    (h1 : P.Runs.firstRun i K = some (l₁, j)) (hk : P.Runs.keysRun i k3 j = some kf) :
    ∀ f ∈ kf.toList, SlotsIn (Win F.next (endOf x F.next)) f :=
  K5Law.keysRun_slots (K5Law.heard_pts (heardSlots_win hh hz gf) hp)
    (K5Law.heard_rows (heardSlots_win hh hz gf) li (K5Law.points_are hp)) h1 hk

end H2K5.Honest.Window

#print axioms H2K5.Honest.Window.sumAt_len
#print axioms H2K5.Honest.Window.sumSlots_win
#print axioms H2K5.Honest.Window.planes_win
#print axioms H2K5.Honest.Window.unitsNext_ge
#print axioms H2K5.Honest.Window.units_win
#print axioms H2K5.Honest.Window.heardSlots_win
#print axioms H2K5.Honest.Window.keys_win
#print axioms H2K5.Honest.Window.keysRun_win
