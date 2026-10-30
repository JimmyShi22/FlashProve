-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Open.lean: the sumcheck on the table side's leaves, which the hearing
leaves open (pscBegin, roundsIn) and the run "planes" closes (pscRow), against the course's sixth
stretch (a sumcheck without shown values, with one kept map).

Main names:
  loopEq_fl: the rounds, each with its own degree.
  heardF_n: what the course hears of a sumcheck that shows no value.
  open_sim: THE STEP: rounds and mask entries taken; the course's row; and: in every later ledger in
    which the sumcheck's own slots hold the hiding polynomial's coefficients, the form that pscRow
    makes has the value of that row's share in mask entries.
  byVar_down: a point put back from the highest variable down is the list turned.

Limits. One world W of mask entries; where the flat functions return.

-/
import Johnson.Desc.First.Look.KeyLaw.Mid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.Slice OnBytes.K.Kc
open OnBytes.Model (Fork Aff Psc RoundName RoundForm Reading World)
open OnBytes.PscRun (took Later Sized Filled Ran)
open Lk6.PortSim (noClaim sLeaves byVarF)
open Lk6.Mid (Dt Cs RowF pscC heardF slots eqPairsF ordDown)

/-- The rounds of a sumcheck under equality weights, each with its own degree. -/
theorem loopEq_fl {first : ℕ} {mu eps : E} (zs : List (E × ℕ)) : ∀ (x x' : Array E × Psc)
    (F G : Fork) (t u : Tape) (zd : List (E × ℕ)) (rs : List (List E × E)),
    (zs.foldlM (m := Fl) (fun (s : Array E × Psc) z => do
      let (r, q) ← Fl.roundIn .eq s.2 z.1 z.2
      pure (s.1.push r, q)) x) F t = some (x', G, u) →
    Ran x.2 first mu eps zd rs →
    ∃ rs' : List (List E × E), rs'.length = zs.length ∧
      rs'.map (fun r => r.1.length) = zs.map (·.2) ∧
      Ran x'.2 first mu eps (zd ++ zs.map fun z => (z.1, z.2 + 1)) (rs ++ rs') ∧
      t.map key = (rs'.map fun r => kr .pscRound 0 r.1 [r.2]) ++ u.map key ∧
      Adv F G (zs.map (·.2)).sum ∧ x'.2.start = x.2.start ∧ x'.2.target = x.2.target ∧
      x'.1.toList = x.1.toList ++ rs'.map (·.2) := by
  induction zs with
  | nil =>
    intro x x' F G t u zd rs h hR
    cases pure_some h
    exact ⟨[], rfl, rfl, by simpa using hR, rfl, Adv.refl _, rfl, rfl, by simp⟩
  | cons z zs ih =>
    intro x x' F G t u zd rs h hR
    rw [List.foldlM_cons] at h
    replace h := bind_some h
    obtain ⟨x1, G1, u1, h1, h⟩ := h
    replace h1 := bind_some h1
    obtain ⟨⟨r, q⟩, G2, u2, h2, h1⟩ := h1
    cases pure_some h1
    obtain ⟨w, sent, hw, e1, e2, hG, hq⟩ := round_fl h2
    obtain rfl := PscRun.weight_eq z.1 z.2 w hw
    have hr := PscRun.ran_push hR z.1 (z.2 + 1) sent r e2 q (by rw [hq]) (by rw [hq]) (by rw [hq])
      (by rw [hq]) (by rw [hq]) (by rw [hq])
    obtain ⟨rs', l, l2, hR', e3, a, e5, e6, e7⟩ := ih (x.1.push r, q) x' _ G _ u _ _ h hr
    refine ⟨(sent.toList, r) :: rs', by simp [l], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.map_cons, l2, List.map_cons]
      congr 1
      show sent.toList.length = z.2
      have : sent.size + 1 = z.2 + 1 := e2
      rw [Array.length_toList]; omega
    · simpa [List.append_assoc] using hR'
    · rw [e1, e3]; rfl
    · have hd : (OnBytes.Psc.Weight.equality z.1 (z.2 + 1)).d - 1 = z.2 := Nat.add_sub_cancel z.2 1
      rw [hG, hd] at a
      exact ((adv_took F z.2).trans a).cast (by rw [List.map_cons, List.sum_cons])
    · have e5' : x'.2.start = q.start := e5
      rw [e5', hq]
    · have e6' : x'.2.target = q.target := e6
      rw [e6', hq]
    · rw [e7]; simp

/-- What the course hears of a sumcheck that shows no value. -/
theorem heardF_n (k : ℕ) (m e : GE) (rs : List (List GE × GE)) (rest : List (Lk6.Flat.RV GE))
    (h : rs.length = k) :
    heardF k false (([m], [e]) :: (rs.map (fun r => (r.1, [r.2])) ++ rest)) = ⟨m, e, rs, []⟩ := by
  have e1 : ((([m], [e]) :: (rs.map (fun r => (r.1, [r.2])) ++ rest) :
      List (Lk6.Flat.RV GE)).drop 1).take k = rs.map (fun r => (r.1, [r.2])) := by
    rw [List.drop_succ_cons, List.drop_zero]
    exact List.take_left' (by rw [List.length_map, h])
  unfold heardF
  simp only [Bool.false_eq_true, if_false, e1, List.headD_cons, List.map_map]
  congr 1
  conv_rhs => rw [← List.map_id rs]
  exact List.map_congr_left fun r _ => rfl

theorem ordDown_succ (m : ℕ) : ordDown (m + 1) = m :: ordDown m := by
  unfold ordDown
  rw [List.range_succ, List.reverse_append]
  rfl

/-- From the highest variable down: the list turned. -/
theorem byVar_down : ∀ (m : ℕ) (cs : List GE), cs.length = m → byVarF cs (ordDown m) = cs.reverse
  | 0, [], _ => rfl
  | m + 1, c :: cs, h => by
    have hl : cs.length = m := by simpa using h
    have ih := byVar_down m cs hl
    unfold byVarF at ih ⊢
    rw [ordDown_succ, List.length_cons, hl, List.range_succ, List.map_append, List.reverse_cons,
      ← ih, hl]
    congr 1
    · refine List.map_congr_left fun t ht => ?_
      rw [List.zip_cons_cons, List.lookup_cons]
      have : (t == m) = false := by
        have := List.mem_range.1 ht
        simp; omega
      rw [this]
    · simp [List.lookup_cons]

variable {W : PscF.World} {home : ℕ → Slot} {D : Dt}

/-- **The open sumcheck.** -/
theorem open_sim {C : Aff} {zs : List (E × ℕ)} {F G0 G : Fork} {t u0 u : Tape} {p0 p : Psc}
    {zb0 : Array E} {s : Cs} {c : PscF.Claim} {factor : List GE → GE}
    {place : List GE → List GE} {pat : List Bool} {rows : List Aff}
    (h1 : Fl.pscBegin C F t = some (p0, G0, u0))
    (h2 : Fl.roundsIn .eq p0 zs G0 u0 = some ((zb0, p), G, u)) (hne : zs ≠ [])
    (hst : St W home D F t s (own (1 + (zs.map (·.2)).sum) ++ pat) rows)
    (hcv : c.vars = zs.map fun z => PscF.Weight.equality (readE z.1) (z.2 + 1))
    (hC : Reads W home F C c.masks c.target) :
    ∃ row : RowF,
      (pscC D c (sLeaves factor) false 1 place s).2.rows = s.rows ++ [row] ∧
      St W home D G u { (pscC D c (sLeaves factor) false 1 place s).2 with rows := s.rows } pat rows
          ∧
      row.maps = [(readE p.eps * factor (zb0.toList.map readE),
        eqPairsF (place (zb0.toList.map readE)))] ∧
      zb0.size = zs.length ∧ p.first = F.next ∧ p.walk.1.length = 1 + (zs.map (·.2)).sum ∧
      NoEnt (p.rowForm oneE {}) ∧
      (∀ H, Later G H →
        (∀ i < 1 + (zs.map (·.2)).sum, (hidW W home H).slot (F.next + i) =
          W.mask (home (F.next + i))) →
        hidV W home H (p.rowForm oneE {}) = W.form row.masks - row.target) ∧
      Later F G ∧ Shp t u (pscShape (zs.map (·.2)) none) := by
  obtain ⟨τ, mu, eps, hτ, k0, rfl, rfl⟩ := begin_fl h1
  unfold Fl.roundsIn at h2
  obtain ⟨rs, hl, hl2, hR, k1, a1, hps, hpt, hz⟩ := loopEq_fl zs _ (zb0, p) _ G _ u [] [] h2
    (PscRun.ran_begin C τ mu eps F.next)
  rw [List.nil_append, List.nil_append] at hR
  have hps' : p.start = C := hps
  have hpt' : p.target = τ := hpt
  have hz' : zb0.toList = rs.map (·.2) := by simpa using hz
  obtain ⟨hcl, hwk⟩ := ran_read hR
  obtain ⟨-, hτv⟩ := public_reads hτ
  obtain ⟨hfr, hal⟩ := Al.plain hst.al
  have a : Adv F G (1 + (zs.map (·.2)).sum) := (adv_took F 1).trans a1
  have hvars : PscF.varsOf c (sLeaves factor) = wF (zs.map fun z => (z.1, z.2 + 1)) := by
    show c.vars = _
    rw [hcv]
    unfold wF
    rw [List.map_map]
    rfl
  have hent : PscF.hidingEntries (wF (zs.map fun z => (z.1, z.2 + 1))) =
      1 + (zs.map (·.2)).sum := by
    rw [entries_wF, List.map_map]
    rfl
  have hN : PscF.masksOf c (sLeaves factor) = 1 + (zs.map (·.2)).sum := by
    unfold PscF.masksOf
    rw [hvars, hent]
    rfl
  have hrd : s.rounds = ([readE mu], [readE eps]) ::
      ((rs.map readRound).map (fun r => (r.1, [r.2])) ++ flatK (u.map key)) := by
    rw [hst.base.rounds, k0, k1]
    simp [flatK, kr, readRound]
  have hlen : (rs.map readRound).length = zs.length := by simp [hl]
  have hdrop : s.rounds.drop (c.vars.length + 1) = flatK (u.map key) := by
    rw [hrd, hcv, List.length_map, List.drop_succ_cons, ← hlen,
      show (rs.map readRound).length = ((rs.map readRound).map fun r => (r.1, [r.2])).length by
          simp,
      List.drop_left]
  have ho : oOf D c (sLeaves factor) false s =
      PscF.outOf c (sLeaves factor) ((List.range' F.next (1 + (zs.map (·.2)).sum)).map home)
        ⟨readE mu, readE eps, rs.map readRound, []⟩ := by
    unfold oOf
    rw [hN, hfr, hrd, hcv, List.length_map]
    show PscF.outOf _ _ _ (heardF zs.length false _) = _
    rw [heardF_n _ _ _ _ _ hlen]
  have hw1 : (PscF.hidingWalk ((wF (zs.map fun z => (z.1, z.2 + 1))).zip
      ((rs.map readRound).map (·.2)))).1 = p.walk.1.map readE := (congrArg Prod.fst hwk).symm
  have hw2 : (PscF.hidingWalk ((wF (zs.map fun z => (z.1, z.2 + 1))).zip
      ((rs.map readRound).map (·.2)))).2 = 1 := by
    rw [← congrArg Prod.snd hwk]
    exact (PscRun.ran_walk rho hR).2
  have hwl : p.walk.1.length = 1 + (zs.map (·.2)).sum := by
    have := PscF.hidingWalk_length (wF (zs.map fun z => (z.1, z.2 + 1)))
      ((rs.map readRound).map (·.2)) (by simpa [wF] using hne) (by simp [wF, hl])
      (fun w hw => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hw
        obtain ⟨z, -, rfl⟩ := List.mem_map.1 hq
        exact Nat.le_add_left 1 z.2)
    rw [hw1, List.length_map, hent] at this
    exact this
  have htg : readE p.target = c.target := by rw [hpt', hτv, hC.pub]
  have hpnt : (oOf D c (sLeaves factor) false s).point = zb0.toList.map readE := by
    rw [ho]
    show ((rs.map readRound).map (·.2)).take c.vars.length = _
    rw [hz', read_challenges, hcv, List.length_map, ← hl]
    exact List.take_of_length_le (by simp)
  have heps : (oOf D c (sLeaves factor) false s).eps = readE p.eps := by
    rw [ho, hR.eps_eq]; rfl
  refine ⟨⟨(oOf D c (sLeaves factor) false s).rowMasks,
    [(readE p.eps * factor (zb0.toList.map readE), eqPairsF (place (zb0.toList.map readE)))],
    (oOf D c (sLeaves factor) false s).rowTarget⟩, ?_, ⟨⟨a.later.sized hst.base.sized, ?_⟩, ?_, ?_⟩,
    rfl, ?_, hR.first_eq, hwl, NoEnt.rowForm (hps' ▸ hC.ne) _, ?_, a.later,
    ⟨pscKeys mu eps rs none, ?_, ?_⟩⟩
  · rw [pscC_eq]
    show s.rows ++ [⟨(oOf D c (sLeaves factor) false s).rowMasks,
      ((oOf D c (sLeaves factor) false s).rowMaps.take 1).map fun a =>
        (a, eqPairsF (place (oOf D c (sLeaves factor) false s).point)),
      (oOf D c (sLeaves factor) false s).rowTarget⟩] = _
    have hm : (oOf D c (sLeaves factor) false s).rowMaps =
        [(oOf D c (sLeaves factor) false s).eps *
          factor (oOf D c (sLeaves factor) false s).point] := rfl
    rw [hm, hpnt, heps]
    rfl
  · rw [pscC_eq]
    exact hdrop
  · rw [pscC_eq, a.next]
    show Al home D.ms D.ix pat _ (s.own + PscF.masksOf c (sLeaves factor)) (s.idx + 0)
    rw [hN]
    exact hal
  · exact hst.rows.later a.later
  · rw [← Array.length_toList, hz', List.length_map, hl]
  · intro H hH hsl
    have hCH : C.value rho (hidW W home H) = c.target - W.form c.masks :=
      (hC.later (a.later.trans hH)).hid
    have hsum := sum_dot W home (hidW W home H).slot p.walk.1 F.next
      (1 + (zs.map (·.2)).sum) (by omega) (fun i hi => hsl i (by omega))
    show (p.rowForm oneE {}).value rho (hidW W home H) =
      W.form (oOf D c (sLeaves factor) false s).rowMasks -
        (oOf D c (sLeaves factor) false s).rowTarget
    rw [PscRun.ran_row rho hR (hidW W home H), hps', Aff.value_empty, hsum, hCH, ho]
    show _ = W.form (((List.range' F.next (1 + (zs.map (·.2)).sum)).map home).zip
        (PscF.hidingWalk ((PscF.varsOf c (sLeaves factor)).zip
          ((rs.map readRound).map (·.2)))).1 ++
        PscF.scaleForm (readE eps * (PscF.hidingWalk ((PscF.varsOf c (sLeaves factor)).zip
          ((rs.map readRound).map (·.2)))).2) c.masks) -
      (PscF.claimAfter (PscF.varsOf c (sLeaves factor)) (rs.map readRound)
          (readE mu + readE eps * c.target) - readE eps * 1)
    rw [hvars, hw1, hw2, PscF.World.form_append, PscF.World.form_zip, PscF.World.form_scale,
      ← htg, ← hcl]
    simp only [rho_val, readE_one]
    ring
  · rw [k0, k1]
    simp [pscKeys]
  · exact pscKeys_shape mu eps rs _ hl2 none

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.open_sim
#print axioms VerifiableInference.Desc.K3.KeyLaw.byVar_down
