-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/InRunAll.lean: kind K5: the twins' added premises, paid from the
kind's own runs' return: where "first" and "second" return at inOld h, InTail h holds, and InUnit at
each visited softmax-table unit (Johnson/Desc/First/Att/Claims/EndsAll.lean): every index that a
reader reads lies in its table; every head's features are lawful.

Main names:
  `first_rc5`, `second_rc6`, `second_rc7`, `second_rc8`: a condition that holds wherever a claim's
    routine returns holds where the run returns.
  `rc_endValuesE`, `rc_valueProduct`, `rc_endValues`, `rc_unitKFD_in`, and the way through claims 4
    to 8.
  `in_tail`: firstRun (inOld h) K = some x → secondRun (inOld h) K = some l → h.S.G = 2 ^ h.S.cf.lgk
    → InTail h. `in_unit`: the like at a unit.
One premise on a public number: the heads of keys and values are 2 ^ lgk (shapedG_of_hid,
Johnson/Road/Rows/AttReadRow.lean, gives it from AttAt.shape).
Used: as Johnson/Desc/First/Att/Claims/InRun.lean.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.InRun

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (tenOf w1Of W1 sum3Of)
open VerifiableInference.Desc.First.Att.P.Runs (W JoinsP)

variable {K : ℕ} (h : Attention.Heard)

local macro "yl" : tactic => `(tactic| repeat (first | exact Yl.pure | refine Yl.bind fun _ => ?_))

theorem first_rc5 {C : Prop} (hC : ∀ j, RC K (P.Runs.claim5 (inOld h) j) C) {x : List Aff × JoinsP}
    (hr : P.Runs.firstRun (inOld h) K = some x) : C := by
  unfold P.Runs.firstRun P.Runs.gather at hr
  simp only [Option.map_eq_some_iff] at hr
  obtain ⟨_, ⟨y, hy, _⟩, _⟩ := hr
  exact RC.right (K := K) (fun j3 => RC.right fun j4 => hC j4) #[] y hy

theorem second_rc6 {C : Prop} (hC : RC K (P.Runs.claim6 (inOld h)) C) {l : List Aff}
    (hr : P.Runs.secondRun (inOld h) K = some l) : C := by
  unfold P.Runs.secondRun P.Runs.gather at hr
  simp only [Option.map_eq_some_iff] at hr
  obtain ⟨_, ⟨y, hy, _⟩, _⟩ := hr
  exact RC.left (K := K) hC #[] y hy

theorem second_rc7 {C : Prop} (hC : RC K (P.Runs.claim7 (inOld h)) C) {l : List Aff}
    (hr : P.Runs.secondRun (inOld h) K = some l) : C := by
  unfold P.Runs.secondRun P.Runs.gather at hr
  simp only [Option.map_eq_some_iff] at hr
  obtain ⟨_, ⟨y, hy, _⟩, _⟩ := hr
  exact RC.right (K := K) (fun _ => RC.left hC) #[] y hy

theorem second_rc8 {C : Prop} (hC : RC K (P.Runs.claim8 (inOld h)) C) {l : List Aff}
    (hr : P.Runs.secondRun (inOld h) K = some l) : C := by
  unfold P.Runs.secondRun P.Runs.gather at hr
  simp only [Option.map_eq_some_iff] at hr
  obtain ⟨_, ⟨y, hy, _⟩, _⟩ := hr
  exact RC.right (K := K) (fun _ => RC.right fun _ => hC) #[] y hy

theorem rc_endValuesE (b : ℕ) (w : W1) : RC K (P.Runs.endValuesE (inOld h) b w)
    ((∀ g < h.S.G, ∀ l < 4, h.S.oZr + (l * h.S.Lam + w.lam) * h.S.cf.H + (g * h.S.HA + w.a) <
        (h.t.tabLen.lookup h.t.hE).getD 0) ∧
      InLongG h h.t.qO h.S.atO w.lam (fun g => g * h.S.HA + w.a) h.d.zcW) := by
  unfold P.Runs.endValuesE
  exact RC.and (rc_readDenominator h _ _ _ _) fun _ => RC.right fun _ =>
    RC.left (rc_readHead h _ h.S.atO _ _ _ _)

theorem rc_claim5_ends (j : JoinsP) {b : ℕ} (hb : b < h.S.NP) : RC K (P.Runs.claim5 (inOld h) j)
    ((∀ g < h.S.G, ∀ l < 4, h.S.oZr + (l * h.S.Lam + ((w1Of h.d.pwW).getD b default).lam) * h.S.cf.H +
        (g * h.S.HA + ((w1Of h.d.pwW).getD b default).a) < (h.t.tabLen.lookup h.t.hE).getD 0) ∧
      InLongG h h.t.qO h.S.atO ((w1Of h.d.pwW).getD b default).lam
        (fun g => g * h.S.HA + ((w1Of h.d.pwW).getD b default).a) h.d.zcW) := by
  unfold P.Runs.claim5
  iterate 12 (refine RC.right fun _ => ?_)
  refine RC.left (RC.forIn_mem (a := b) (fun _ => by yl) ?_ (List.mem_range.2 hb))
  exact RC.left (rc_endValuesE h b _)

theorem rc_valueProduct (sc : Sc3) (tS : ℕ) (pt : Array E) (isD : Bool) (tV : ℕ) {b : ℕ}
    (hb : b < h.S.NP) : RC K (P.Runs.valueProduct (inOld h) (sum3Of sc) tS pt isD tV)
    ((∀ x, x = 3 ∨ x = 4 →
        ∀ hi < (eqTab (pt.extract 0 ((if isD then h.S.nD else h.S.nM) - h.S.cf.lmS))).size,
          Rows.planeFirst h.S x ((w1Of h.d.pwW).getD b default).lam ((w1Of h.d.pwW).getD b default).a isD >>>
            h.S.cf.lmS + hi < (h.t.tabLen.lookup tS).getD 0) ∧
      InLongG h tV h.S.atV ((w1Of h.d.pwW).getD b default).lam (fun g => g) h.d.zcW) := by
  unfold P.Runs.valueProduct
  refine RC.right fun _ => RC.left (RC.forIn_mem (a := b) (fun _ => by yl) ?_ (List.mem_range.2 hb))
  refine (RC.and (rc_plane h tS 3 _ _ pt isD) fun _ => RC.and (rc_plane h tS 4 _ _ pt isD) fun _ =>
    RC.right fun _ => RC.left (rc_readGroup h tV h.S.atV _ _ _)).mono ?_
  rintro ⟨c3, c4, cg⟩
  refine ⟨?_, cg⟩
  rintro x (rfl | rfl)
  · exact c3
  · exact c4

theorem rc_claim7_hT {b : ℕ} (hb : b < h.S.NP) : RC K (P.Runs.claim7 (inOld h))
    (∀ g < h.S.G, ∀ l < 4, h.S.oMr + (l * h.S.Lam + b / h.S.HA) * h.S.cf.H + (g * h.S.HA + b % h.S.HA) <
      (h.t.tabLen.lookup h.t.hT).getD 0) := by
  unfold P.Runs.claim7
  refine RC.left (RC.forIn_mem (a := b) (fun _ => by yl) ?_ (List.mem_range.2 hb))
  exact RC.left (rc_readMaximum h _ _ _ _)

theorem rc_claim7_qF {b : ℕ} (hb : b < h.S.NP) : RC K (P.Runs.claim7 (inOld h))
    (InLongG h h.t.qF h.S.atQ (b / h.S.HA) (fun g => g * h.S.HA + b % h.S.HA) (h.x.rc h.S)) := by
  unfold P.Runs.claim7
  iterate 2 (refine RC.right fun _ => ?_)
  refine RC.left (RC.forIn_mem (a := b) (fun _ => by yl) ?_ (List.mem_range.2 hb))
  exact RC.left (rc_readHead h _ h.S.atQ _ _ _ _)

theorem rc_claim7_qKx {lam : ℕ} (hl : lam < h.S.Lam) : RC K (P.Runs.claim7 (inOld h))
    (InLongG h h.t.qKx h.S.atK lam (fun g => g) (h.x.rc h.S)) := by
  unfold P.Runs.claim7
  iterate 4 (refine RC.right fun _ => ?_)
  refine RC.left (RC.forIn_mem (a := lam) (fun _ => by yl) ?_ (List.mem_range.2 hl))
  exact RC.left (rc_readGroup h _ h.S.atK _ _ _)

theorem rc_claim7_hPi {b k : ℕ} (hb : b < h.S.NP) (hk : k < h.S.cf.lt) : RC K (P.Runs.claim7 (inOld h))
    (∀ g < h.S.G, ∀ l < 1, h.S.oIb + (l * h.S.Lam + b / h.S.HA) * (h.S.cf.lt * h.S.cf.H) +
      (k * h.S.cf.H + g * h.S.HA + b % h.S.HA) < (h.t.tabLen.lookup h.t.hPi).getD 0) := by
  unfold P.Runs.claim7
  iterate 5 (refine RC.right fun _ => ?_)
  refine RC.left (RC.forIn_mem (a := b) (fun _ => by yl) ?_ (List.mem_range.2 hb))
  refine RC.left (RC.forIn_mem (a := k) (fun _ => by yl) ?_ (List.mem_range.2 hk))
  exact RC.left (rc_readIndexBit h _ _ _ _ _)

theorem rc_claim8_hR2 {b k : ℕ} (hb : b < h.S.NP) (hk : k < h.S.cf.lt) : RC K (P.Runs.claim8 (inOld h))
    (∀ g < h.S.G, ∀ l < 1, h.S.oIb + (l * h.S.Lam + b / h.S.HA) * (h.S.cf.lt * h.S.cf.H) +
      (k * h.S.cf.H + g * h.S.HA + b % h.S.HA) < (h.t.tabLen.lookup h.t.hR2).getD 0) := by
  unfold P.Runs.claim8
  refine RC.right fun _ => RC.left (RC.forIn_mem (a := b) (fun _ => by yl) ?_ (List.mem_range.2 hb))
  refine RC.right fun _ => RC.left (RC.foldlM (a := k) (fun s => ?_) (List.mem_range.2 hk) _)
  exact RC.left (rc_readIndexBit h _ _ _ _ _)

theorem piece_lam {v : Array PW} {b : ℕ} {w : PW} (hw : v[b]? = some w) :
    ((w1Of v).getD b default).lam = w.lam ∧ ((w1Of v).getD b default).a = w.a := by
  rw [getD_lam, getD_a, getD_of hw]
  exact ⟨rfl, rfl⟩

/-- **Where "first" and "second" return, the twins' added premises behind the units hold.** -/
theorem in_tail {x : List Aff × JoinsP} {l : List Aff} (h1 : P.Runs.firstRun (inOld h) K = some x)
    (h2 : P.Runs.secondRun (inOld h) K = some l) (hG : h.S.G = 2 ^ h.S.cf.lgk) : InTail h := by
  have c6M : ∀ b < h.S.NP, _ := fun b hb => second_rc6 h (RC.right fun _ => RC.left
    (rc_valueProduct (K := K) h h.d.vpm h.t.tVM h.t.ptM false h.t.qVM hb)) h2
  have c6D : ∀ b < h.S.NP, _ := fun b hb => second_rc6 h (RC.right fun _ => RC.right fun _ =>
    rc_valueProduct (K := K) h h.d.vpd h.t.tVD h.t.ptD true h.t.qVD hb) h2
  have c5 : ∀ b < h.S.NP, _ := fun b hb => first_rc5 h (fun j => rc_claim5_ends (K := K) h j hb) h1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb w hw
    have e := (c5 b hb).1
    rw [(piece_lam hw).1, (piece_lam hw).2, hG] at e
    exact e
  · intro b hb w hw
    have e := (c5 b hb).2
    rw [(piece_lam hw).1, (piece_lam hw).2] at e
    exact e.long hG
  · intro b hb w hw
    have e := (c6M b hb).1
    rw [(piece_lam hw).1, (piece_lam hw).2] at e
    exact e
  · intro b hb w hw
    have e := (c6M b hb).2
    rw [(piece_lam hw).1] at e
    exact e.long hG
  · intro b hb w hw
    have e := (c6D b hb).1
    rw [(piece_lam hw).1, (piece_lam hw).2] at e
    exact e
  · intro b hb w hw
    have e := (c6D b hb).2
    rw [(piece_lam hw).1] at e
    exact e.long hG
  · intro b hb
    have e := second_rc7 h (rc_claim7_hT (K := K) h hb) h2
    rw [hG] at e
    exact e
  · exact fun b hb => (second_rc7 h (rc_claim7_qF (K := K) h hb) h2).long hG
  · exact fun lam hl => (second_rc7 h (rc_claim7_qKx (K := K) h hl) h2).long hG
  · intro b hb k hk
    have e := second_rc7 h (rc_claim7_hPi (K := K) h hb hk) h2
    rw [hG] at e
    exact e
  · intro b hb k hk
    have e := second_rc8 h (rc_claim8_hR2 (K := K) h hb hk) h2
    rw [hG] at e
    exact e

/-! ### the softmax-table units -/

theorem rc_endValues (k : Score) (tb : ScoreTables) (rc : Array E) (b : ℕ) (w : PW) :
    RC K (P.Runs.endValues (inOld h) (scoreOf k) (scoreTOf tb) rc b (w1 w))
      (InLongG h tb.tQ h.S.atQ w.lam (fun g => g * h.S.HA + w.a) rc ∧
        InLongG h tb.tK h.S.atK w.lam (fun g => g) rc) := by
  unfold P.Runs.endValues
  exact RC.and (rc_readHead h _ h.S.atQ _ _ _ _) fun _ => RC.right fun _ =>
    RC.left (rc_readGroup h _ h.S.atK _ _ _)

theorem rc_unitKFD_in (n : ℕ) (k : Score) {tb : ScoreTables} (ht : h.t.score[n]? = some tb) {b : ℕ}
    {w : PW} (hw : k.pw[b]? = some w) : RC K (P.Runs.unitKFD (inOld h) n (scoreOf k))
      (InLongG h tb.tQ h.S.atQ w.lam (fun g => g * h.S.HA + w.a) (lastCoords k.sc.r h.S.cf.ldh) ∧
        InLongG h tb.tK h.S.atK w.lam (fun g => g) (lastCoords k.sc.r h.S.cf.ldh)) := by
  unfold P.Runs.unitKFD
  dsimp only
  rw [scoreT_inOld, Array.getElem?_map, ht]
  show RC K (P.Runs.W.need (some (scoreTOf tb)) >>= _) _
  rw [show (P.Runs.W.need (some (scoreTOf tb)) : W _) = pure (scoreTOf tb) from rfl, pure_bind]
  iterate 5 (refine RC.right fun _ => ?_)
  show RC K ((w1Of k.pw).toList.zipIdx.forM _) _
  rw [w1Of_zip]
  refine RC.forM_mem (a := (w1 w, b)) (rc_endValues h k tb _ b w) ?_
  refine List.mem_map.2 ⟨(w, b), ?_, rfl⟩
  rw [List.mem_zipIdx_iff_getElem?]
  simpa using hw

/-- **Where "first" returns, the twins' added premises hold at each visited softmax-table unit.** -/
theorem in_unit {x : List Aff × JoinsP} (h1 : P.Runs.firstRun (inOld h) K = some x)
    (hG : h.S.G = 2 ^ h.S.cf.lgk) {c : ACall} {q : ℕ} (hc : (c, q) ∈ h.S.calls.toList.zipIdx)
    (hk : (c.kind == Table.kfd) = true) {k : Score} {n : ℕ} (hn : (k, n) ∈ h.scores.toList.zipIdx)
    (hq : (k.call == q) = true) {tb : ScoreTables} (ht : h.t.score[n]? = some tb) : InUnit h k tb := by
  have key : ∀ (b : ℕ) (w : PW), k.pw[b]? = some w →
      InLongG h tb.tQ h.S.atQ w.lam (fun g => g * h.S.HA + w.a) (lastCoords k.sc.r h.S.cf.ldh) ∧
        InLongG h tb.tK h.S.atK w.lam (fun g => g) (lastCoords k.sc.r h.S.cf.ldh) := by
    intro b w hw
    unfold P.Runs.firstRun P.Runs.gather at h1
    simp only [Option.map_eq_some_iff] at h1
    obtain ⟨_, ⟨y, hy, _⟩, _⟩ := h1
    refine RC.right (K := K) (fun j3 => RC.left (k := fun j => P.Runs.claim5 (inOld h) j) ?_) #[] y hy
    unfold P.Runs.claim4
    show RC K ((P.geoOf h.S).calls.toList.zipIdx.foldlM _ _) _
    rw [calls_zip]
    refine RC.foldlM (a := (P.callOf c, q)) (fun s => ?_) (List.mem_map.2 ⟨(c, q), hc, rfl⟩) _
    rw [if_pos (by rw [← tab_eq c.kind Table.kfd] at hk; exact hk)]
    refine RC.left ?_
    unfold P.Runs.callKFD
    rw [scores_zip]
    refine RC.foldlM (a := (scoreOf k, n)) (fun s => ?_) (List.mem_map.2 ⟨(k, n), hn, rfl⟩) _
    rw [if_pos (show ((scoreOf k, n).1.call == (P.callOf c, q).2) = true from hq)]
    exact RC.left (rc_unitKFD_in h n k ht hw)
  exact ⟨fun b w hw => (key b w hw).1.long hG, fun b w hw => (key b w hw).2.long hG⟩

end K5Law
