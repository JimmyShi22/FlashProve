-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/EquationsTotal.lean: what the ties and reads of the list "K8.equations"
add to a sub-proof's one equation, once the list is added: proved of the list's own text.

Definitions, statements and proofs. After OnBytes/Tie/Pv/Tail/EndClaims.lean and EndLoops.lean, which
say the like of `verify-on-bytes`'s routines; no routine of that program is named here: of these two
files the definitions on plain data alone are used (tieBracket, readBracket, tieTerm, readTerm,
readsList, segsOf, sumFrom, Kept, colsU) and the laws on values (lessBeta_value, highDigit_val,
readEnts_value, colsU_frame, val_beta). ALSO USED, ON RECORDS AND PLAIN DATA ALONE: scaleE_val,
scaleNat, HTailF2.lessBeta, Reading.pow, treesFrame, Aff.ofConst, Aff.value, Run2.value; and, in
eqTail's text, which is Equations.lean's to the letter: markRead, tablesTile, funsHeld, allDistinct,
sumE, mulE, isZeroE.
Main names:
  PushStep F0 t s s': the routine has laid one claim on the list; and to add it to a record that
    has kept F0's batching element, plan's number and arrays' frame keeps these, counts one claim
    and lets the total grow by t.
  PushAll F0 n t s s': the like for n claims.
  eqTie_step, eqRead_step: a tie lays tieTerm; a read lays readTerm.
  eqTail_total: the text behind the four first claims.
Limits: nothing where a step refuses. Totals at a reading.

-/
import Johnson.Desc.First.TailClaims.EquationsRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open OnBytes.Tie.Pv.Tail.Port

variable {K : Type} [CommRing K] (ρ : Reading K) (W : World K)

/-- The record's arrays have F0's frame. -/
def Fr (F0 F : Fork) : Prop := treesFrame F.trees = treesFrame F0.trees

def PushStep (F0 : Fork) (t : K) (s s' : St) : Prop :=
  ∃ cl, s' = (s.1, s.2.push cl) ∧ (Fr F0 s.1 → ∀ A A', Kept F0 A → addClaim A cl = some A' →
    Kept F0 A' ∧ A'.nClaim = A.nClaim + 1 ∧ A'.total ρ W = A.total ρ W + t)

def PushAll (F0 : Fork) (n : Nat) (t : K) (s s' : St) : Prop :=
  ∃ new : List Claim, s' = (s.1, s.2 ++ new.toArray) ∧ new.length = n ∧
    (Fr F0 s.1 → ∀ A A', Kept F0 A → addAll A new = some A' →
      Kept F0 A' ∧ A'.nClaim = A.nClaim + n ∧ A'.total ρ W = A.total ρ W + t)

theorem PushAll.refl (F0 : Fork) (s : St) : PushAll ρ W F0 0 0 s s := by
  refine ⟨[], by simp, rfl, fun _ A A' hk hA => ?_⟩
  obtain rfl : A = A' := Option.some.inj hA
  exact ⟨hk, rfl, by simp⟩

theorem addAll_cons (A : Fork) (c : Claim) (l : List Claim) :
    addAll A (c :: l) = (addClaim A c).bind fun B => addAll B l := by
  unfold addAll
  rw [List.foldlM_cons]
  rfl

theorem PushStep.andThen {F0 : Fork} {t t' : K} {n : Nat} {s s1 s2 : St}
    (h1 : PushStep ρ W F0 t s s1) (h2 : PushAll ρ W F0 n t' s1 s2) :
    PushAll ρ W F0 (n + 1) (t + t') s s2 := by
  obtain ⟨cl, rfl, k1⟩ := h1
  obtain ⟨new, rfl, hl, k2⟩ := h2
  refine ⟨cl :: new, by simp, by simp [hl], fun fr A A' hk hA => ?_⟩
  rw [addAll_cons] at hA
  obtain ⟨B, hB, hA⟩ := Option.bind_eq_some_iff.1 hA
  obtain ⟨kB, nB, tB⟩ := k1 fr A B hk hB
  obtain ⟨kA, nA, tA⟩ := k2 fr B A' kB hA
  exact ⟨kA, by rw [nA, nB]; omega, by rw [tA, tB]; ring⟩

theorem PushAll.trans {F0 : Fork} {t t' : K} {n m : Nat} {s s1 s2 : St}
    (h1 : PushAll ρ W F0 n t s s1) (h2 : PushAll ρ W F0 m t' s1 s2) :
    PushAll ρ W F0 (n + m) (t + t') s s2 := by
  obtain ⟨l1, rfl, e1, k1⟩ := h1
  obtain ⟨l2, rfl, e2, k2⟩ := h2
  refine ⟨l1 ++ l2, by simp, by simp [e1, e2], fun fr A A' hk hA => ?_⟩
  rw [addAll_append] at hA
  obtain ⟨B, hB, hA⟩ := Option.bind_eq_some_iff.1 hA
  obtain ⟨kB, nB, tB⟩ := k1 fr A B hk hB
  obtain ⟨kA, nA, tA⟩ := k2 fr B A' kB hA
  exact ⟨kA, by rw [nA, nB]; omega, by rw [tA, tB]; ring⟩

theorem runFoldE_adds {α β : Type} (F0 : Fork) (term : α → K) :
    ∀ (l : List α) (b : β) (s : St) (b' : β) (s' : St),
      RunFoldE (fun a (_ : β) s (_ : β) s1 => PushStep ρ W F0 (term a) s s1) l b s b' s' →
      PushAll ρ W F0 l.length (l.map term).sum s s'
  | [], _, s, _, _, h => by
    obtain ⟨_, rfl⟩ := h
    exact PushAll.refl ρ W F0 _
  | a :: l, _, _, _, _, h => by
    obtain ⟨b1, s1, hs, hr⟩ := h
    have := PushStep.andThen ρ W hs (runFoldE_adds F0 term l b1 s1 _ _ hr)
    simpa using this

theorem runFoldE_counts {α β : Type} (F0 : Fork) (cnt : β → Nat) (term : Nat → α → K) :
    ∀ (l : List α) (b : β) (s : St) (b' : β) (s' : St),
      RunFoldE (fun a b s b1 s1 => cnt b1 = cnt b + 1 ∧ PushStep ρ W F0 (term (cnt b) a) s s1)
        l b s b' s' →
      cnt b' = cnt b + l.length ∧ PushAll ρ W F0 l.length (sumFrom term (cnt b) l) s s'
  | [], _, _, _, _, h => by
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by simpa [sumFrom] using PushAll.refl ρ W F0 _⟩
  | a :: l, b, _, _, _, h => by
    obtain ⟨b1, s1, ⟨hc, hs⟩, hr⟩ := h
    obtain ⟨hc2, hs2⟩ := runFoldE_counts F0 cnt term l b1 s1 _ _ hr
    refine ⟨by rw [hc2, hc, List.length_cons]; omega, ?_⟩
    rw [hc] at hs2
    have := PushStep.andThen ρ W hs hs2
    simpa [sumFrom] using this

/-- The three steps of one claim keep what Kept names. -/
theorem kept_claim {F0 A A1 A2 A3 : Fork} {k w : E} {a : Aff} {runs : Array Run2} (hk : Kept F0 A)
    (a1 : A.kap = some (k, A1)) (a2 : A1.push w a = some A2) (a3 : A2.pushRuns w runs = some A3) :
    Kept F0 A3 ∧ A3.nClaim = A.nClaim + 1 := by
  obtain ⟨o, hn, hs⟩ := onlySums_claim hk.sized a1 a2 a3
  exact ⟨⟨o.theta.trans hk.theta, o.plan.trans hk.plan, hs, o.trees.trans hk.frame⟩, hn⟩

theorem addClaim_one {A A' : Fork} {cl : Claim} (h : addClaim A cl = some A') :
    addAll A [cl] = some A' := by
  rw [addAll_cons, h]
  rfl

/-- One tie. -/
theorem eqTie_step (tl : HTailF2) (mu : Nat) (F0 : Fork) (front : Nat) (s s' : St) (u : Unit)
    (h : eqTie tl mu front s = .ok (u, s')) : PushStep ρ W F0 (tieTerm ρ W tl F0 mu) s s' := by
  unfold eqTie at h
  dsimp only at h
  obtain ⟨wl, t1, h1, k1⟩ := (eq_bind_ok _ _ _ _ _).1 h
  obtain ⟨hwl, e1⟩ := eq_get_ok h1
  rw [e1] at k1
  obtain ⟨wr, t2, h2, k2⟩ := (eq_bind_ok _ _ _ _ _).1 k1
  obtain ⟨hwr, e2⟩ := eq_get_ok h2
  rw [e2] at k2
  obtain ⟨c0, t3, h3, k3⟩ := (eq_bind_ok _ _ _ _ _).1 k2
  obtain ⟨hc0, e3⟩ := eq_get_ok h3
  rw [e3] at k3
  obtain ⟨c1, t4, h4, k4⟩ := (eq_bind_ok _ _ _ _ _).1 k3
  obtain ⟨hc1, e4⟩ := eq_get_ok h4
  rw [e4] at k4
  refine ⟨_, emit_ok k4, fun _ A A' hk hA => ?_⟩
  obtain ⟨k, A1, w, A2, a1, hw, a2, a3⟩ := addOne (addClaim_one hA)
  dsimp only at hw a2 a3
  split at hw
  · obtain rfl := Option.some.inj hw
    obtain ⟨kk, hn⟩ := kept_claim hk a1 a2 a3
    refine ⟨kk, hn, ?_⟩
    rw [total_claim ρ W hk.sized a1 a2 a3, ρ.pow, hk.theta, hk.plan, tieTerm, lessBeta_value]
    simp only [tieBracket, hwl, hwr, hc0, hc1, Option.getD_some, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Run2.value, ρ.mul, ρ.sub, ρ.zero, ρ.one, highDigit_val,
      Nat.zero_add, add_zero]
    ring
  · cases hw

/-- One read. -/
theorem eqRead_step (tl : HTailF2) (Fn : HFun) (sg laid : Nat) (F0 : Fork) (front : Nat)
    (s s' : St) (u : Unit)
    (h : eqRead tl Fn sg laid (mulE (sumE Fn.phi) (sumE tl.vt)) front s = .ok (u, s')) :
    PushStep ρ W F0 (readTerm ρ W tl F0 laid (Fn, sg)) s s' := by
  unfold eqRead at h
  dsimp only at h
  obtain ⟨tU, t1, h1, k1⟩ := (eq_bind_ok _ _ _ _ _).1 h
  obtain ⟨htU, e1⟩ := eq_get_ok h1
  rw [e1] at k1
  obtain ⟨cols, t2, h2, k2⟩ := (eq_bind_ok _ _ _ _ _).1 k1
  obtain ⟨hcols, e2⟩ := eq_ask_ok h2
  rw [e2] at k2
  obtain ⟨u3, t3, h3, k3⟩ := (eq_bind_ok _ _ _ _ _).1 k2
  obtain ⟨_, e3⟩ := eq_must_ok h3
  rw [e3] at k3
  obtain ⟨en, t4, h4, k4⟩ := (eq_bind_ok _ _ _ _ _).1 k3
  obtain ⟨hen, e4⟩ := eq_get_ok h4
  rw [e4] at k4
  obtain ⟨ents, nz⟩ := en
  dsimp only at k4
  obtain ⟨u5, t5, h5, k5⟩ := (eq_bind_ok _ _ _ _ _).1 k4
  obtain ⟨_, e5⟩ := eq_test_ok h5
  rw [e5] at k5
  obtain ⟨c0, t6, h6, k6⟩ := (eq_bind_ok _ _ _ _ _).1 k5
  obtain ⟨hc0, e6⟩ := eq_get_ok h6
  rw [e6] at k6
  obtain ⟨c1, t7, h7, k7⟩ := (eq_bind_ok _ _ _ _ _).1 k6
  obtain ⟨hc1, e7⟩ := eq_get_ok h7
  rw [e7] at k7
  refine ⟨_, emit_ok k7, fun fr A A' hk hA => ?_⟩
  obtain ⟨k, A1, w, A2, a1, hw, a2, a3⟩ := addOne (addClaim_one hA)
  dsimp only at hw a2 a3
  split at hw
  · obtain rfl := Option.some.inj hw
    obtain ⟨kk, hn⟩ := kept_claim hk a1 a2 a3
    refine ⟨kk, hn, ?_⟩
    have hc : cols = colsU F0 tU := by
      rw [← Option.some.inj hcols]
      exact colsU_frame s.1 F0 fr tU
    have v1 := readEnts_value ρ W tl Fn sg tU _ _ _ _ _ _ _ ents nz hen
    rw [total_claim ρ W hk.sized a1 a2 a3, ρ.pow, hk.theta, hk.plan, readTerm]
    simp only [readBracket, htU, hc0, hc1, Option.getD_some, Aff.value, HTailF2.lessBeta,
      Aff.ofConst, v1, hc, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Run2.value,
      ρ.mul, ρ.sub, ρ.zero, ρ.one, highDigit_val, Nat.zero_add, add_zero, scaleNat,
      OnBytes.scaleE_val ρ, val_beta, Array.toList_empty, Array.emptyWithCapacity]
    ring
  · cases hw

/-! ## The text's tail, as a handle -/

/-- eqAll behind the claims on the keys and the counts: Equations.lean's text, to the letter; tied to
it by eqAll_split. -/
def eqTail (before : Nat) (tl : HTailF2) (funs : Array HFun) : EqM HTailF2 := do
  EqM.mustAs "internal-f-exist" ((← EqM.claims) - before == 4)
  let tl ← eqWeights tl
  let mut tieObj : Array Nat := #[]
  let mut tiesOn : Array Nat :=
    Array.replicate (← EqM.ask "objectsF:1060" fun F => some F.trees.size) 0
  for mu in List.range tl.NM do
    tieObj := tieObj.push (← EqM.claims)
    eqTie tl mu
    tiesOn := tiesOn.modify (tl.gtTree.getD mu 0) (· + 1)
  let mut rd : Array (Array Bool) := tl.tabLen.map fun n => Array.replicate n false
  let mut laid := 0
  for mu in List.range tl.NM do
    let M := tl.mats.getD mu {}
    for un in [0, 2] do
      for Fn in funs do
        if Fn.mat == mu && Fn.tree == un then
          EqM.mustAs "internal-t2f-unit" (tl.ix.U.getD un none).isSome
          EqM.mustAs "shape-functional"
            (Fn.len != 0 && M.m % Fn.len == 0 && Fn.phi.size == Fn.len)
          let sums := mulE (sumE Fn.phi) (sumE tl.vt)
          for sg in List.range (M.m / Fn.len) do
            rd ← EqM.get "objectsF:1077" (tl.markRead Fn sg rd)
            eqRead tl Fn sg laid sums
            laid := laid + 1
  EqM.mustAs "internal-t2f-functional"
    (funs.all fun Fn => decide (Fn.mat < tl.NM) && (Fn.tree == 0 || Fn.tree == 2))
  EqM.mustAs "internal-f-table-read" (rd.all fun a => a.all id)
  let segments1 ← EqM.get "objectsF:1085" (tl.tablesTile funs 0)
  let segments3 ← EqM.get "objectsF:1086" (tl.tablesTile funs 2)
  let kinds ← EqM.ask "objectsF:1089" fun F => some (F.trees.map (·.kind))
  EqM.mustAs "internal-f-exist" ((List.range kinds.size).all fun t =>
    tiesOn.getD t 0 == (if kinds.getD t .table == .symbols then 1 else 0))
  EqM.mustAs "internal-f-exist" (tiesOn.foldl (· + ·) 0 == tl.NM && laid == segments1 + segments3)
  EqM.mustAs "internal-f-exist" (allDistinct tieObj.toList && allDistinct tl.gtTree.toList)
  pure { tl with tieObj := tieObj, tiesOn := tiesOn, nX4Laid := laid }

/-- eqAll behind its count on the heard rows. -/
def eqRest (tl : HTailF2) (funs : Array HFun) : EqM HTailF2 := do
  let before ← EqM.claims
  let tl ← eqKeys tl
  let tl ← eqCounts tl
  eqTail before tl funs

theorem eqAll_split (tl : HTailF2) (funs : Array HFun) : eqAll tl funs = (do
    EqM.mustAs "internal-f-fun-closed" (tl.funClosed && funs.size == tl.funs.size)
    EqM.mustAs "internal-f-fun-moved" (tl.funsHeld funs)
    EqM.testAs "internal-f-tail-slot"
      (← EqM.ask "objectsF:1047" fun F => some ((F.LS.extract tl.slotA tl.slotB).all isZeroE))
    let g ← EqM.get "objectsF:1048" tl.heard
    EqM.mustAs "internal-f-exist" (g.rows.size == lookRows tl)
    eqRest tl funs) := rfl

theorem eq_claims_iff (front : Nat) (s s' : St) (a : Nat) :
    EqM.claims front s = .ok (a, s') ↔ a = front + s.2.size ∧ s' = s :=
  ⟨eq_claims_ok, by rintro ⟨rfl, rfl⟩; rfl⟩

theorem eq_must_iff (n : String) (b : Bool) (front : Nat) (s s' : St) (u : Unit) :
    EqM.mustAs n b front s = .ok (u, s') ↔ b = true ∧ s' = s :=
  ⟨eq_must_ok, by rintro ⟨rfl, rfl⟩; rfl⟩

theorem eq_get_iff {α : Type} (n : String) (o : Option α) (front : Nat) (s s' : St) (a : α) :
    EqM.get n o front s = .ok (a, s') ↔ o = some a ∧ s' = s :=
  ⟨eq_get_ok, by rintro ⟨rfl, rfl⟩; rfl⟩

/-- A step of the reads' loops. -/
def stepRE (tl : HTailF2) (F0 : Fork) (x : HFun × Nat) (b : MProd Nat (Array (Array Bool)))
    (s : St) (b1 : MProd Nat (Array (Array Bool))) (s1 : St) : Prop :=
  b1.fst = b.fst + 1 ∧ PushStep ρ W F0 (readTerm ρ W tl F0 b.fst x) s s1

@[reducible] def stepPE (tl : HTailF2) (F0 : Fork) (x : HFun × Nat)
    (b : MProd Nat (Array (Array Bool))) (s : St) (b1 : MProd Nat (Array (Array Bool)))
    (s1 : St) : Prop :=
  x.1.phi.size = x.1.len ∧ stepRE ρ W tl F0 x b s b1 s1

/-- **The ties and reads of the list.** After objectsF_total (OnBytes/Tie/Pv/Tail/EndLoops.lean). -/
theorem eqTail_total (F0 : Fork) (before : Nat) (tlb tl' : HTailF2) (funs : Array HFun)
    (front : Nat) (s s' : St) (h : eqTail before tlb funs front s = .ok (tl', s')) :
    ∃ tl1, eqWeights tlb front s = .ok (tl1, s) ∧ front + s.2.size - before = 4 ∧
      tl'.nX4Laid = (readsList tl1 funs).length ∧
      tl' = { tl1 with tieObj := tl'.tieObj, tiesOn := tl'.tiesOn, nX4Laid := tl'.nX4Laid } ∧
      (∀ x ∈ readsList tl1 funs, x.1.phi.size = x.1.len) ∧
      PushAll ρ W F0 (tl1.NM + (readsList tl1 funs).length)
        (((List.range tl1.NM).map (tieTerm ρ W tl1 F0)).sum
          + sumFrom (readTerm ρ W tl1 F0) 0 (readsList tl1 funs)) s s' := by
  unfold eqTail at h
  obtain ⟨n0, t0, h0, k0⟩ := (eq_bind_ok _ _ _ _ _).1 h
  obtain ⟨en0, et0⟩ := eq_claims_ok h0
  rw [en0, et0] at k0
  obtain ⟨u1, t1, h1, k1⟩ := (eq_bind_ok _ _ _ _ _).1 k0
  obtain ⟨b4, et1⟩ := eq_must_ok h1
  rw [et1] at k1
  obtain ⟨tl1, t2, hW, k2⟩ := (eq_bind_ok _ _ _ _ _).1 k1
  have eW : t2 = s := by
    unfold eqWeights at hW
    obtain ⟨x3, t3, g1, g2⟩ := (eq_bind_ok _ _ _ _ _).1 hW
    rw [(eq_ask_ok g1).2] at g2
    exact (eq_get_ok g2).2
  rw [eW] at hW k2
  obtain ⟨sz, t3, h3, k3⟩ := (eq_bind_ok _ _ _ _ _).1 k2
  rw [(eq_ask_ok h3).2] at k3
  obtain ⟨bT, sT, hT, k4⟩ := (eq_bind_ok _ _ _ _ _).1 k3
  obtain ⟨bR, sR, hR, k5⟩ := (eq_bind_ok _ _ _ _ _).1 k4
  obtain ⟨u6, t6, h6, k6⟩ := (eq_bind_ok _ _ _ _ _).1 k5
  rw [(eq_must_ok h6).2] at k6
  obtain ⟨u7, t7, h7, k7⟩ := (eq_bind_ok _ _ _ _ _).1 k6
  rw [(eq_must_ok h7).2] at k7
  obtain ⟨g1, t8, h8, k8⟩ := (eq_bind_ok _ _ _ _ _).1 k7
  rw [(eq_get_ok h8).2] at k8
  obtain ⟨g3, t9, h9, k9⟩ := (eq_bind_ok _ _ _ _ _).1 k8
  rw [(eq_get_ok h9).2] at k9
  obtain ⟨kinds, t10, h10, k10⟩ := (eq_bind_ok _ _ _ _ _).1 k9
  rw [(eq_ask_ok h10).2] at k10
  obtain ⟨u11, t11, h11, k11⟩ := (eq_bind_ok _ _ _ _ _).1 k10
  rw [(eq_must_ok h11).2] at k11
  obtain ⟨u12, t12, h12, k12⟩ := (eq_bind_ok _ _ _ _ _).1 k11
  rw [(eq_must_ok h12).2] at k12
  obtain ⟨u13, t13, h13, k13⟩ := (eq_bind_ok _ _ _ _ _).1 k12
  rw [(eq_must_ok h13).2] at k13
  obtain ⟨etl, es'⟩ := (eq_pure_ok _ _ _ _ _).1 k13
  -- the ties
  have rT := forInE_inv front _
    (fun mu (_ : MProd (Array Nat) (Array Nat)) s (_ : MProd (Array Nat) (Array Nat)) s1 =>
      PushStep ρ W F0 (tieTerm ρ W tl1 F0 mu) s s1)
    (by
      intro mu b s r s1 hb
      obtain ⟨n, x1, c1, d1⟩ := (eq_bind_ok _ _ _ _ _).1 hb
      rw [(eq_claims_ok c1).2] at d1
      obtain ⟨u, x2, c2, d2⟩ := (eq_bind_ok _ _ _ _ _).1 d1
      obtain ⟨u', x3, c3, d3⟩ := (eq_bind_ok _ _ _ _ _).1 d2
      rw [((eq_pure_ok _ _ _ _ _).1 c3).2] at d3
      obtain ⟨er, ex⟩ := (eq_pure_ok _ _ _ _ _).1 d3
      rw [ex]
      exact ⟨_, er, eqTie_step ρ W tl1 mu F0 front _ _ _ c2⟩) _ _ _ _ _ hT
  have aT := runFoldE_adds ρ W F0 _ _ _ _ _ _ rT
  -- the reads: four loops, flattened
  have rR := forInE_inv front _
    (fun mu => RunFoldE (fun un => RunFoldE (fun (Fn : HFun) => RunFoldE (stepPE ρ W tl1 F0)
      (segsOf tl1 mu un Fn)) funs.toList) [0, 2])
    (by
      intro mu b s r s1 hb
      obtain ⟨b2, x1, c1, d1⟩ := (eq_bind_ok _ _ _ _ _).1 hb
      obtain ⟨u', x2, c2, d2⟩ := (eq_bind_ok _ _ _ _ _).1 d1
      rw [((eq_pure_ok _ _ _ _ _).1 c2).2] at d2
      obtain ⟨er, ex⟩ := (eq_pure_ok _ _ _ _ _).1 d2
      rw [ex]
      refine ⟨_, er, ?_⟩
      refine forInE_inv front _ _ ?_ _ _ _ _ _ c1
      intro un b s r s1 hb
      obtain ⟨b3, y1, c3, d3⟩ := (eq_bind_ok _ _ _ _ _).1 hb
      obtain ⟨u'', y2, c4, d4⟩ := (eq_bind_ok _ _ _ _ _).1 d3
      rw [((eq_pure_ok _ _ _ _ _).1 c4).2] at d4
      obtain ⟨er', ex'⟩ := (eq_pure_ok _ _ _ _ _).1 d4
      rw [ex']
      refine ⟨_, er', ?_⟩
      refine forInE_inv_array front _ _ ?_ _ _ _ _ _ c3
      intro Fn b s r s1 hb
      by_cases hc : (Fn.mat == mu && Fn.tree == un) = true
      · rw [if_pos hc] at hb
        obtain ⟨v1, z1, e1, f1⟩ := (eq_bind_ok _ _ _ _ _).1 hb
        rw [(eq_must_ok e1).2] at f1
        obtain ⟨v2, z2, e2, f2⟩ := (eq_bind_ok _ _ _ _ _).1 f1
        obtain ⟨hsf, ez2⟩ := eq_must_ok e2
        rw [ez2] at f2
        obtain ⟨b4', z3, e3, f3⟩ := (eq_bind_ok _ _ _ _ _).1 f2
        obtain ⟨v4, z4, e4, f4⟩ := (eq_bind_ok _ _ _ _ _).1 f3
        rw [((eq_pure_ok _ _ _ _ _).1 e4).2] at f4
        obtain ⟨er2, ex2⟩ := (eq_pure_ok _ _ _ _ _).1 f4
        rw [ex2]
        simp only [Bool.and_eq_true, beq_iff_eq] at hsf
        refine ⟨_, er2, ?_⟩
        rw [segsOf, if_pos hc]
        apply runFoldE_map
        refine forInE_inv front _ _ ?_ _ _ _ _ _ e3
        intro sg b s r s1 hb
        obtain ⟨rd, w1, p1, q1⟩ := (eq_bind_ok _ _ _ _ _).1 hb
        rw [(eq_get_ok p1).2] at q1
        obtain ⟨v5, w2, p2, q2⟩ := (eq_bind_ok _ _ _ _ _).1 q1
        obtain ⟨v6, w3, p3, q3⟩ := (eq_bind_ok _ _ _ _ _).1 q2
        rw [((eq_pure_ok _ _ _ _ _).1 p3).2] at q3
        obtain ⟨er3, ex3⟩ := (eq_pure_ok _ _ _ _ _).1 q3
        rw [ex3]
        exact ⟨_, er3, hsf.2, rfl, eqRead_step ρ W tl1 Fn sg _ F0 front _ _ _ p2⟩
      · rw [if_neg hc] at hb
        obtain ⟨v1, z1, e1, f1⟩ := (eq_bind_ok _ _ _ _ _).1 hb
        rw [((eq_pure_ok _ _ _ _ _).1 e1).2] at f1
        obtain ⟨er2, ex2⟩ := (eq_pure_ok _ _ _ _ _).1 f1
        rw [ex2]
        refine ⟨_, er2, ?_⟩
        rw [segsOf, if_neg hc]
        exact ⟨rfl, rfl⟩) _ _ _ _ _ hR
  have s1 := runFoldE_mono _
    (fun mu => RunFoldE (fun un => RunFoldE (stepPE ρ W tl1 F0)
      (funs.toList.flatMap (segsOf tl1 mu un))) [0, 2])
    (fun mu _ _ _ _ h2 => runFoldE_mono _
      (fun un => RunFoldE (stepPE ρ W tl1 F0) (funs.toList.flatMap (segsOf tl1 mu un)))
      (fun un _ _ _ _ h3 => runFoldE_flat (stepPE ρ W tl1 F0) (segsOf tl1 mu un) _ _ _ _ _ h3)
      _ _ _ _ _ h2) _ _ _ _ _ rR
  have s2 := runFoldE_mono _
    (fun mu => RunFoldE (stepPE ρ W tl1 F0)
      ([0, 2].flatMap fun un => funs.toList.flatMap (segsOf tl1 mu un)))
    (fun mu _ _ _ _ h2 => runFoldE_flat (stepPE ρ W tl1 F0)
      (fun un => funs.toList.flatMap (segsOf tl1 mu un)) _ _ _ _ _ h2) _ _ _ _ _ s1
  have fP := runFoldE_flat (stepPE ρ W tl1 F0)
    (fun mu => [0, 2].flatMap fun un => funs.toList.flatMap (segsOf tl1 mu un)) _ _ _ _ _ s2
  obtain ⟨hall, fR⟩ := runFoldE_all (fun x : HFun × Nat => x.1.phi.size = x.1.len)
    (stepRE ρ W tl1 F0) _ _ _ _ _ fP
  have cR := runFoldE_counts ρ W F0 (fun b : MProd Nat (Array (Array Bool)) => b.fst)
    (readTerm ρ W tl1 F0) _ _ _ _ _ fR
  refine ⟨tl1, hW, by simpa using b4, ?_, ?_, hall, ?_⟩
  · rw [etl]
    have := cR.1
    simpa [readsList] using this
  · rw [etl]
  · rw [es']
    have := PushAll.trans ρ W aT cR.2
    simpa [readsList] using this

end VerifiableInference.Desc.First.TailClaims.Law

#print axioms VerifiableInference.Desc.First.TailClaims.Law.eqTail_total
