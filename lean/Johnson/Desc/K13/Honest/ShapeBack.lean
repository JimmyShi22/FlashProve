--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/ShapeBack.lean: kind K13, the members' batching: WHERE THE JOINED
SUB-PROTOCOL RETURNS, THE TEST ON THE STATE's SHAPE ACCEPTS (`readySh`, Shape.lean of this folder):
the converse of `atM3_accepts_shape`. So that test is exactly what the decision asks of the state.
Statements with their proofs.
Main names:
  `takeMask_left`, `takeMasksInto_left`, `takeMasks_left`: where the taking of n + 1 mask entries
    returns, the ledger was open and had n + 1 entries left.
  `frontB_tests`, `quietB_tests`: what the front's and the quiet part's return say of the part.
  `shape_of_nine`, `readySh_iff`: the nine premises give the test on the shape; that test accepts
    exactly where the test on the state does (`readyC`, Ready.lean of this folder).
  `shape_of_return`: **the statement.**
  `atM3_returns_iff`: the two directions, at rounds of the kind's form.

What is not claimed. What the shape behind the sub-protocol is. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Honest.Shape
import Johnson.Desc.K13.Law.M3Fits
import Johnson.Desc.K13.Law.AtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc.Ground (takeMaskP takeMaskL takeMasksInto takeMasksP ok has)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law
open Desc.Plain (DState)

variable {L : Type}

/-- Where one entry is handed out, the ledger was open and had one; behind, it has one less. -/
theorem takeMask_left {d d' : DState L} {o i : ℕ} (h : takeMaskP d o = some (i, d')) :
    ∃ (x : OnBytes.Oracle) (l : Ledger), d.st.oracles[o]? = some x ∧ x.ledger = some l ∧
      l.closed = false ∧ 0 < l.left ∧ d'.st = layLedger d.st o (taken l) := by
  unfold takeMaskP at h
  split at h
  · rename_i hok
    simp only [ok, takeMaskL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hok
    obtain ⟨h1, h2, h3, h4⟩ := hok
    cases hx : d.st.oracles[o]? with
    | none =>
      rw [hx] at h1
      cases h1
    | some x =>
      cases hl : x.ledger with
      | none =>
        rw [hx] at h
        have h' : (x.ledger.map fun l => _) = some (i, d') := h
        rw [hl] at h'
        cases h'
      | some l =>
        have hb : (d.st.oracles[o]?).bind (·.ledger) = some l := by
          rw [hx]
          exact hl
        rw [hb] at h h3 h4
        have e := Option.some.inj h
        refine ⟨x, l, rfl, hl, ?_, ?_, ?_⟩
        · have : (!l.closed) = true := h3
          simpa using this
        · exact of_decide_eq_true h4
        · rw [← (Prod.mk.inj e).2]
          rfl
  · cases h

/-- Where the loop of the taking returns on n + 1 entries, so many were left. -/
theorem takeMasksInto_left (o : ℕ) : ∀ (n : ℕ) (d : DState L) (acc : Array ℕ)
    (t : List ℕ × DState L), takeMasksInto o (n + 1) d acc = some t → LeftAt d.st o (n + 1)
  | 0, d, acc, t, h => by
    unfold takeMasksInto at h
    cases hm : takeMaskP d o with
    | none =>
      rw [hm] at h
      cases h
    | some q =>
      obtain ⟨x, l, hx, hl, hc, h0, -⟩ := takeMask_left (i := q.1) (d' := q.2) hm
      exact ⟨x, l, hx, hl, hc, h0⟩
  | n + 1, d, acc, t, h => by
    unfold takeMasksInto at h
    cases hm : takeMaskP d o with
    | none =>
      rw [hm] at h
      cases h
    | some q =>
      rw [hm] at h
      obtain ⟨x, l, hx, hl, hc, h0, hd⟩ := takeMask_left (i := q.1) (d' := q.2) hm
      obtain ⟨x', l', hx', hl', -, hn⟩ := takeMasksInto_left o n q.2 (acc.push q.1) t h
      rw [hd, layLedger_at hx (taken l)] at hx'
      obtain rfl := Option.some.inj hx'
      obtain rfl : taken l = l' := Option.some.inj hl'
      refine ⟨x, l, hx, hl, hc, ?_⟩
      have e : n + 1 ≤ l.left - 1 := hn
      omega

/-- **Where the taking of n + 1 entries returns, the ledger was open and had so many left.** -/
theorem takeMasks_left {d : DState L} {o n : ℕ} {t : List ℕ × DState L}
    (h : takeMasksP d o (n + 1) = some t) : leftAtC d.st o (n + 1) = true :=
  (leftAtC_iff _ _ _).2 (takeMasksInto_left o n d #[] t h)

variable {Cl : Type}

/-- What the front's return says of the part behind the entering. -/
theorem frontB_tests {T : Type} (X : Lens T) (P : Where) {t t' : T} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (frontB (Cl := Cl) X P).decide t rs gs = .ok t') :
    ∃ p : Part, X.enter t = some t' ∧ X.get? t' = some p ∧
      (!P.reply || p.heard.isSome) = true ∧ p.pile.length = P.rows ∧
      memberRowsFit p.d.st P.lin p.indexMasks p.pile = true := by
  simp only [frontB, still, front_is, Law.bind_ok, Law.there_ok, Law.need_ok, Law.pure_ok,
    Lens.part, beq_iff_eq] at h
  obtain ⟨t₁, h1, p, hp, _, ⟨_, ha, _, hb, hc⟩, rfl⟩ := h
  exact ⟨p, h1, hp, ha, hb, hc⟩

/-- What the quiet part's return says of the part. -/
theorem quietB_tests {T : Type} (X : Lens T) (P : Where) {t t' : T} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (quietB (Cl := Cl) X P).decide t rs gs = .ok t') :
    ∃ (p : Part) (msg : Array OracleNotice), X.get? t = some p ∧
      linOk p.d.st.codes P.lin = true ∧ linMessageW P.lin = some msg := by
  simp only [quietB, still, quiet_is, Law.bind_ok, Law.there_ok, Law.need_ok, Law.pure_ok,
    Lens.part] at h
  obtain ⟨p, hp, _, _, msg, ⟨_, hl, hm⟩, rfl⟩ := h
  exact ⟨p, msg, hp, hl, hm⟩

/-- Where the nine premises hold, the test on the state's shape accepts: the converse of
`ready_of_shape`. -/
theorem shape_of_nine {P : Where} {s : S} {f : First.FinOwn} {t : List ℕ × St}
    {msg : Array OracleNotice} (a1 : s.here = .fin f)
    (a2 : (!P.reply || s.out.reply.isSome) = true) (a3 : s.out.pending.length = P.rows)
    (a4 : memberRowsFit s.st P.lin s.out.indexMasks s.out.pending = true)
    (a5 : s.noneWaits = true) (a6 : Batt.fits P.lin.kCol s.out.pending = true)
    (a7 : takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol) = some t)
    (a8 : linOk s.st.codes P.lin = true) (a9 : linMessageW P.lin = some msg) :
    readySh P (shOf s) = true := by
  unfold readySh
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨(atFinC_iff s).2 ⟨f, a1⟩, a2⟩, ?_⟩, ?_⟩, a5⟩, ?_⟩, ?_⟩, a8⟩, ?_⟩
  · show ((s.out.pending.map rowSh).length == P.rows) = true
    rw [List.length_map]
    exact beq_iff_eq.2 a3
  · rw [fitSh_eq]
    exact a4
  · show formSh P.lin.kCol (s.out.pending.map rowSh) = true
    rw [formSh_eq]
    exact a6
  · rw [roomSh_eq]
    have e : Batt.masksOf P.lin.kCol = 2 * P.lin.kCol + 1 := by
      unfold Batt.masksOf
      omega
    rw [e] at a7 ⊢
    exact takeMasks_left a7
  · rw [a9]
    rfl

/-- **The test on the shape accepts exactly where the test on the state does** (`readyC`, Ready.lean
of this folder). -/
theorem readySh_iff (P : Where) (s : S) : readySh P (shOf s) = true ↔ readyC P s = true :=
  ⟨fun h => (ready_iff P s).2 (ready_of_shape h),
    fun h => by
      obtain ⟨f, t, msg, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := (ready_iff P s).1 h
      exact shape_of_nine a1 a2 a3 a4 a5 a6 a7 a8 a9⟩

/-- **Where the joined sub-protocol returns, the test on the state's shape accepts.** -/
theorem shape_of_return {P : Where} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (atM3 (Cl := Cl) P).decide s rs gs = .ok s') :
    readySh P (shOf s) = true := by
  have h' : (((frontB (Cl := Cl) atS P).decide s _ _).bind fun s₁ =>
      (claimCombinationBlock (Cl := Cl) atS P).decide s₁ _ _).bind (fun s₂ =>
                      (quietB (Cl := Cl) atS P).decide s₂ _ _) = .ok s' := h
  obtain ⟨s₂, h12, h3⟩ := ebind_ok.1 h'
  obtain ⟨s₁, h1, h2⟩ := ebind_ok.1 h12
  obtain ⟨p₁, he, hp₁, a2, a3, a4⟩ := frontB_tests atS P h1
  obtain ⟨p, out, hp, hb, rfl⟩ := battB_ok atS P h2
  obtain ⟨p₃, msg, hp₃, a8, a9⟩ := quietB_tests atS P h3
  obtain ⟨f, -, -, hfin, -⟩ := atM3_rec h
  have e1 : atS.enter s = some s.enterMem := by simp only [atS, hfin]
  rw [e1] at he
  have e2 : s₁ = { s with here := .mem { msg := #[], ids := #[], lin := none } } := by
    rw [← Option.some.inj he]
    simp only [S.enterMem, hfin]
  subst e2
  obtain rfl := Option.some.inj hp₁
  obtain rfl := Option.some.inj hp
  obtain rfl := Option.some.inj hp₃
  obtain ⟨_, _, _, t, _, _, _, b1, b2, _, _, b4, _, _, _, rfl⟩ := batt_ok hb
  have a5 : s.noneWaits = true := by
    have q : (if s.noneWaits then none else s.rowsOwed : Option Nat).isNone = true := b1
    by_cases hw : s.noneWaits = true
    · exact hw
    · rw [if_neg hw] at q
      unfold S.noneWaits
      cases hr : s.rowsOwed with
      | none => rfl
      | some r =>
        rw [hr] at q
        cases q
  have a8' : linOk s.st.codes P.lin = true := by
    have q : linOk t.2.st.codes P.lin = true := a8
    rw [(takeMasks_same b4).1] at q
    exact q
  exact shape_of_nine hfin a2 a3 a4 a5 b2 b4 a8' a9

/-- **The test on the shape is exactly what the decision asks of the state**: at any elements in
rounds of the kind's form. -/
theorem atM3_returns_iff {P : Where} {s : S} (x : E) (h : Psc.Heard)
    (hl : h.rounds.length = P.lin.kCol) (h2 : ∀ p ∈ h.rounds, p.1.length = 2) (hv : h.values = [])
    (cols : List (List (Nat × List UInt64))) :
    (∃ s', (atM3 (Cl := Cl) P).decide s (roundsOf x h) cols = .ok s') ↔
      readySh P (shOf s) = true :=
  ⟨fun ⟨_, q⟩ => shape_of_return q, fun q => atM3_accepts_shape q x h hl h2 hv cols⟩

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.takeMask_left
#print axioms VerifiableInference.Desc.K13.Honest.takeMasksInto_left
#print axioms VerifiableInference.Desc.K13.Honest.takeMasks_left
#print axioms VerifiableInference.Desc.K13.Honest.frontB_tests
#print axioms VerifiableInference.Desc.K13.Honest.quietB_tests
#print axioms VerifiableInference.Desc.K13.Honest.shape_of_nine
#print axioms VerifiableInference.Desc.K13.Honest.readySh_iff
#print axioms VerifiableInference.Desc.K13.Honest.shape_of_return
#print axioms VerifiableInference.Desc.K13.Honest.atM3_returns_iff
