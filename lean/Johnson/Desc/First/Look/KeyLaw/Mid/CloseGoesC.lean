-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Mid/CloseGoesC.lean: the course over the field goes with the plain
function of the described lookup at the closing.

The course over the field is our text of the program's lookup, over the field
(Johnson/Desc/First/Look/KeyLaw/Mid/Course.lean). That the program's run, read in the field, is this
course is shown in files that are not in this library yet.

It imports CloseGoesA.lean and ClosePort.lean (`ordC_default`, `ofFn_rev`). `Sim` is that of
Johnson/Desc/First/Look/KeyLaw/Mid/Relation.lean, `Goes` that of
Johnson/Desc/First/Look/KeyLaw/Mid/Seams.lean, `cClo`, `pscC`, `heardF`, `slots` those of
Johnson/Desc/First/Look/KeyLaw/Mid/Course.lean, `closeRun` that of CloseRun.lean.
Main names:
  `pscC_leaves` one sumcheck of the course that shows no value, under equality weights with a degree
    for each variable, on rounds that are written out: the stand behind it.
  `clo_goes` `Goes` from seam 5 to seam 6, for `cClo` and `closeRun`, under five conditions: the
    course's public record is that of the data; 0 < mu + d; pl ≤ 2^mu; the course's `tabAt` is the
    extension of the data's table; the place of the name i of the closing's hiding polynomial is the
    ledger's entry number own + ownAt 5 + `Cf.portIdx` i.
Limits: nothing on the program's blocks on machine words.

-/
import Johnson.Desc.First.Look.KeyLaw.Mid.CloseGoesA
import OnBytes.Tie.Pv.KeyLookup.ClosePort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.Mid.Clo
open Lk6.PortSim Lk6.Clo

open OnBytes OnBytes.Slice Flat Cb Cb.LdLkp Finset Lk6.PortSim

/-! ### small rules -/

theorem walk_hidM' {J : Type} [DecidableEq J] (sl : Slot → J) (j : J) : ∀ (k : ℕ), 0 < k →
    ∀ (dg : Fin k → ℕ) (z : Fin k → GE) (cs : List GE) (fr : List Slot)
    (w : PIdx (pfMix GE k dg) → J), cs.length = k → 1 + ∑ i, dg i ≤ fr.length →
    (∀ i, w i = sl (fr.getD (Cf.portIdx (pfMix GE k dg) i) default)) →
    rdMF sl (fr.zip (PscF.hidingWalk
      ((List.ofFn fun i => PscF.Weight.equality (z i) (dg i + 1)).zip cs)).1) j =
      hidM k dg w (fun i => cs.getD i 0) j
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | k + 1, _ => walk_hidM sl j k

theorem slots_getD (e : ℕ → Slot) (first n p : ℕ) (h : p < n) :
    (slots e first n).getD p default = e (first + p) := by
  unfold slots
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

theorem slots_length (e : ℕ → Slot) (first n : ℕ) : (slots e first n).length = n := by
  simp [slots]

theorem chC_map : ∀ (rs : List (List GE × GE)) (i : ℕ),
    Lev.chC (rs.map fun r => (r.1, [r.2])) i = (rs.map (·.2)).getD i 0
  | [], i => by simp [Lev.chC]
  | _ :: _, 0 => rfl
  | _ :: rs, i + 1 => chC_map rs i

theorem heard_no (k : ℕ) (m e : GE) (rs : List (List GE × GE)) (rest : List (RV GE))
    (h : rs.length = k) :
    heardF k false (([m], [e]) :: (rs.map (fun r => (r.1, [r.2])) ++ rest)) = ⟨m, e, rs, []⟩ := by
  show (⟨m, e, ((rs.map (fun r => (r.1, [r.2])) ++ rest).take k).map
    (fun r : RV GE => (r.1, r.2.headD 0)), []⟩ : PscF.Heard) = _
  rw [List.take_left' (by rw [List.length_map]; exact h), List.map_map]
  have e1 : ((fun r : RV GE => (r.1, r.2.headD 0)) ∘ fun r : List GE × GE => (r.1, [r.2])) = id :=
    funext fun _ => rfl
  rw [e1, List.map_id]

theorem ofFn_drop (a b : ℕ) (π : Fin (a + b) → GE) :
    (List.ofFn π).drop a = List.ofFn fun r : Fin b => π (Fin.natAdd a r) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [Fin.natAdd]

theorem mle_c_sub {n : ℕ} (c : GE) (u : (Fin n → Bool) → GE) (p : Fin n → GE) :
    Alg.mle (fun r => c - u r) p = c - Alg.mle u p := by
  have e : (fun r => c - u r) = (fun _ => c) - u := rfl
  rw [e, Alg.mle_sub, Alg.mle_const]

theorem masks_mix (k : ℕ) (dg : Fin k → ℕ) (z : Fin k → GE) (masks : PscF.MaskForm) (tg : GE)
    (factor : List GE → GE) :
    PscF.masksOf ⟨List.ofFn fun i => PscF.Weight.equality (z i) (dg i + 1), masks, tg⟩
      (sLeaves factor) = 1 + ∑ i, dg i := by
  show 1 + ((List.ofFn fun i => PscF.Weight.equality (z i) (dg i + 1)).map fun w => w.d - 1).sum +
    0 = _
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

/-! ### one sumcheck of the course that shows no value -/

theorem pscC_leaves (D : Dt) (k : ℕ) (dg : Fin k → ℕ) (z : Fin k → GE) (masks : PscF.MaskForm)
    (tg : GE) (factor : List GE → GE) (place : List GE → List GE) (s : Cs) (m e : GE)
    (rs : List (List GE × GE)) (rest : List (RV GE))
    (hs : s.rounds = ([m], [e]) :: (rs.map (fun r => (r.1, [r.2])) ++ rest))
    (hrk : rs.length = k) :
    (pscC D ⟨List.ofFn fun i => PscF.Weight.equality (z i) (dg i + 1), masks, tg⟩ (sLeaves factor)
      false 1 place s).2 =
      { s with
        rounds := rest
        own := s.own + (1 + ∑ i, dg i)
        idx := s.idx + 0
        rows := s.rows ++
          [⟨(slots D.ms s.own (1 + ∑ i, dg i)).zip (PscF.hidingWalk
                ((List.ofFn fun i => PscF.Weight.equality (z i) (dg i + 1)).zip
                  (rs.map (·.2)))).1 ++
              PscF.scaleForm (e * (PscF.hidingWalk
                ((List.ofFn fun i => PscF.Weight.equality (z i) (dg i + 1)).zip
                  (rs.map (·.2)))).2) masks,
            [(e * factor (rs.map (·.2)), eqPairsF (place (rs.map (·.2))))],
            PscF.claimAfter (List.ofFn fun i => PscF.Weight.equality (z i) (dg i + 1)) rs
              (m + e * tg) - e * 1⟩] } := by
  have key : ∀ (kk n : ℕ) (H : PscF.Heard),
      kk = (List.ofFn fun i => PscF.Weight.equality (z i) (dg i + 1)).length →
      n = PscF.masksOf ⟨List.ofFn fun i => PscF.Weight.equality (z i) (dg i + 1), masks, tg⟩
        (sLeaves factor) → H = heardF kk false s.rounds →
      (pscC D ⟨List.ofFn fun i => PscF.Weight.equality (z i) (dg i + 1), masks, tg⟩
        (sLeaves factor) false 1 place s).2 =
      { s with
        rounds := s.rounds.drop (kk + 1)
        own := s.own + n
        idx := s.idx + 0
        rows := s.rows ++
          [⟨(slots D.ms s.own n).zip (PscF.hidingWalk
                ((List.ofFn fun i => PscF.Weight.equality (z i) (dg i + 1)).zip
                  (H.rounds.map (·.2)))).1 ++
              PscF.scaleForm (H.eps * (PscF.hidingWalk
                ((List.ofFn fun i => PscF.Weight.equality (z i) (dg i + 1)).zip
                  (H.rounds.map (·.2)))).2) masks,
            [(H.eps * factor ((H.rounds.map (·.2)).take kk),
              eqPairsF (place ((H.rounds.map (·.2)).take kk)))],
            PscF.claimAfter (List.ofFn fun i => PscF.Weight.equality (z i) (dg i + 1)) H.rounds
              (H.mu + H.eps * tg) - H.eps * 1⟩] } := by
    rintro _ _ _ rfl rfl rfl
    rfl
  rw [key k (1 + ∑ i, dg i) ⟨m, e, rs, []⟩ (List.length_ofFn).symm
    (masks_mix k dg z masks tg factor).symm
    (by rw [hs, heard_no k m e rs rest hrk])]
  have e1 : s.rounds.drop (k + 1) = rest := by
    rw [hs, List.drop_succ_cons, List.drop_left' (by rw [List.length_map]; exact hrk)]
  have e2 : (rs.map (·.2)).take k = rs.map (·.2) :=
    List.take_of_length_le (by rw [List.length_map, hrk])
  rw [e1]
  show ({ s with
    rounds := rest
    own := s.own + (1 + ∑ i, dg i)
    idx := s.idx + 0
    rows := s.rows ++ [⟨_, [(e * factor ((rs.map (·.2)).take k),
      eqPairsF (place ((rs.map (·.2)).take k)))], _⟩] } : Cs) = _
  rw [e2]

/-! ### the closing -/

theorem sum_dgEnd (w d : ℕ) : ∑ i, dgEnd w d (ordC (w + d)) i = w + 2 * d := by
  rw [← List.sum_ofFn]
  have e : List.ofFn (dgEnd w d (ordC (w + d))) = List.replicate d 2 ++ List.replicate w 1 :=
    dgEnd_rev w d
  rw [e]
  simp
  omega

theorem ownAt_6 (S : Pub) : ownAt S 6 = ownAt S 5 + (1 + S.mu + 2 * S.d) := by
  first | rfl | simp [ownAt]

variable (A : Dat GE) (sl : Slot → A.J) (st : A.St) (own idx : ℕ)

theorem clo_goes (P : ClPl A) (D : Dt) (hD : D.S = A.toPub) (hk : 0 < A.mu + A.d)
    (hr : A.pl ≤ 2 ^ A.mu)
    (hT : ∀ p : Fin A.d → GE,
      D.tabAt (List.ofFn p) = Alg.mle (fun r : Fin A.d → Bool => A.tab st (numLE r)) p)
    (hP : ∀ i, P.wE i = sl (D.ms (own + ownAt A.toPub 5 + Cf.portIdx _ i))) :
    Goes (Sim A sl st own idx 5) (Sim A sl st own idx 6) (cClo D) (A.closeRun P) A.fmClo := by
  intro s x h hf
  have hlen : A.fmClo.length = A.mu + A.d + 1 := congrArg Nat.succ (fmM_length _ _)
  rw [hlen] at hf ⊢
  obtain ⟨m, e, l', hl, hl'⟩ :=
    fits_head (a := fmM (A.mu + A.d) (dgEnd A.mu A.d (ordC (A.mu + A.d)))) hf
  obtain ⟨rs, rfl, hrk, hrq⟩ := fits_mix _ _ l' hl'
  have hs : s.rounds = ([m], [e]) ::
      (rs.map (fun r => (r.1, [r.2])) ++ s.rounds.drop (A.mu + A.d + 1)) := by
    rw [← List.cons_append, ← hl, List.take_append_drop]
  obtain ⟨htop, hplen, hpt⟩ := h.top (by decide) (by decide)
  have hplen' : s.top.point.length = A.mu + A.d := by simpa using hplen
  have hcs : (rs.map (·.2)).length = A.mu + A.d := by rw [List.length_map, hrk]
  have hvars : (ordDown (A.mu + A.d)).map (fun t =>
      PscF.Weight.equality (s.top.point.getD t 0) (if t < A.mu then 2 else 3)) =
      List.ofFn fun i : Fin (A.mu + A.d) => PscF.Weight.equality (x.pt (ordC (A.mu + A.d) i))
        (dgEnd A.mu A.d (ordC (A.mu + A.d)) i + 1) := by
    have e0 : ordDown (A.mu + A.d) =
        List.ofFn fun i : Fin (A.mu + A.d) => ((ordC (A.mu + A.d) i : Fin (A.mu + A.d)) : ℕ) :=
      (ordC_default _).symm
    rw [e0, List.map_ofFn]
    refine congrArg List.ofFn (funext fun i => ?_)
    show PscF.Weight.equality (s.top.point.getD (ordC (A.mu + A.d) i).val 0)
      (if (ordC (A.mu + A.d) i).val < A.mu then 2 else 3) = _
    rw [hpt _ (by rw [hplen']; exact (ordC (A.mu + A.d) i).isLt)]
    unfold dgEnd
    by_cases c : ((ordC (A.mu + A.d) i : Fin (A.mu + A.d)) : ℕ) < A.mu
    · rw [if_pos c, if_pos c]
    · rw [if_neg c, if_neg c]
  have hc : cClo D s = (pscC D ⟨List.ofFn fun i : Fin (A.mu + A.d) =>
        PscF.Weight.equality (x.pt (ordC (A.mu + A.d) i))
          (dgEnd A.mu A.d (ordC (A.mu + A.d)) i + 1), s.top.masks, s.top.value⟩
      (sLeaves fun p => s.alpha - 1 - D.tabAt ((byVarF p (ordDown (A.mu + A.d))).drop A.mu))
      false 1 (byVarF · (ordDown (A.mu + A.d))) s).2 := by
    rw [← hvars]
    show (pscC D ⟨(ordDown (D.S.mu + D.S.d)).map fun t =>
        PscF.Weight.equality (s.top.point.getD t 0) (if t < D.S.mu then 2 else 3),
      s.top.masks, s.top.value⟩
      (sLeaves fun p => s.alpha - 1 - D.tabAt ((byVarF p (ordDown (D.S.mu + D.S.d))).drop D.S.mu))
      false 1 (byVarF · (ordDown (D.S.mu + D.S.d))) s).2 = _
    rw [hD]
  rw [hc, pscC_leaves D _ _ _ _ _ _ _ s m e rs _ hs hrk, hl]
  have hch : ∀ i, Lev.chC (([m], [e]) :: rs.map fun r => (r.1, [r.2])) (i + 1) =
      (rs.map (·.2)).getD i 0 := fun i => chC_map rs i
  have hb : byVarF (rs.map (·.2)) (ordDown (A.mu + A.d)) = (rs.map (·.2)).reverse := by
    rw [← hcs]
    exact byVarF_down _
  have hπ : List.ofFn (fun t : Fin (A.mu + A.d) =>
      Lev.chC (([m], [e]) :: rs.map fun r => (r.1, [r.2])) (t.rev.val + 1)) =
      (rs.map (·.2)).reverse := by
    have e0 : (fun t : Fin (A.mu + A.d) =>
        Lev.chC (([m], [e]) :: rs.map fun r => (r.1, [r.2])) (t.rev.val + 1)) =
        fun t => (fun i : Fin (A.mu + A.d) => (rs.map (·.2)).getD i.val 0) t.rev :=
      funext fun t => hch _
    rw [e0, ofFn_rev (A.mu + A.d) fun i : Fin (A.mu + A.d) => (rs.map (·.2)).getD i.val 0,
      ofFn_getD _ _ hcs]
  have hlt : ∀ i : PIdx (pfMix GE (A.mu + A.d) (dgEnd A.mu A.d (ordC (A.mu + A.d)))),
      Cf.portIdx _ i < 1 + ∑ i, dgEnd A.mu A.d (ordC (A.mu + A.d)) i := fun i => by
    have h0 := Cf.portIdx_lt _ i
    rwa [mix_degs, List.sum_ofFn] at h0
  refine ⟨⟨h.st, h.al, ?_, ?_, ?_, fun a => absurd a (by decide), fun a => absurd a (by decide),
    fun _ a => absurd a (by decide), fun _ a => absurd a (by decide), fun _ => h.cls (by decide),
    fun a => absurd a (by decide)⟩, rfl⟩
  · show x.rows ++ [_] = (s.rows ++ [_]).map (rdRow A sl)
    rw [List.map_append, h.rows]
    refine congrArg (_ ++ ·) (congrArg (fun r => [r])
      (congrArg₂ LdLkp.Row.mk (funext fun j => ?_) ?_))
    · show _ = rdMF sl (_ ++ _) j + (e * (s.alpha - 1 - D.tabAt
        ((byVarF (rs.map (·.2)) (ordDown (A.mu + A.d))).drop A.mu)) *
        onCell A (eqPairsF (byVarF (rs.map (·.2)) (ordDown (A.mu + A.d)))) j + 0)
      rw [rdMF_append, rdMF_scale, walk_snd _ (allEq_zip _ _ _),
        walk_hidM' sl j _ hk _ _ _ _ P.wE hcs (by rw [slots_length]) (fun i => by
          rw [slots_getD _ _ _ _ (hlt i), h.own, hP]), hb, ← hπ, ofFn_drop, hT,
        ← cellW_onCell A hr]
      have e1 : (fun i => Lev.chC (([m], [e]) :: rs.map fun r => (r.1, [r.2])) (i + 1)) =
          fun i => (rs.map (·.2)).getD i 0 := funext hch
      show hidM _ _ P.wE (fun i => Lev.chC (([m], [e]) :: rs.map fun r => (r.1, [r.2])) (i + 1)) j +
        e * x.top.mf j +
        e * (Alg.mle (fun r : Fin A.d → Bool => x.al - 1 - A.tab x.st (numLE r)) _ * _) = _
      rw [e1, mle_c_sub, htop, h.al, h.st]
      show _ + e * rdMF sl s.top.masks j + _ = _
      ring
    · show finM _ _ _ (m + e * x.top.tg) (rs.map fun r => (r.1, [r.2])) - e = _
      rw [claim_finM _ _ _ _ rs hrk hrq, mul_one, htop]
      rfl
  · show s.own + (1 + ∑ i, dgEnd A.mu A.d (ordC (A.mu + A.d)) i) = _
    rw [h.own, sum_dgEnd, ownAt_6]
    show _ = own + (ownAt A.toPub 5 + (1 + A.mu + 2 * A.d))
    omega
  · exact h.idx

end Lk6.Mid.Clo

#print axioms Lk6.Mid.Clo.pscC_leaves
#print axioms Lk6.Mid.Clo.clo_goes
