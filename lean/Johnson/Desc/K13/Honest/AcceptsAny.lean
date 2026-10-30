--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/AcceptsAny.lean: kind K13, the members' batching: THE DECISION TESTS NO
VALUE THAT IS SENT IN ITS OWN ROUNDS, AS A STATEMENT: under the nine premises on the verifier's own
state and on the plan (`atM3_accepts_code`, Accepts.lean of this folder) the field `decide` of the
joined sub-protocol `atM3` returns `.ok` at ANY elements in rounds of the kind's form. Statements
with their proofs.

Why. Whoever shows that the sub-protocol accepts an honest run owes these nine premises and the
rounds' form, and nothing on the values sent, on a matrix or on a mask entry. What hangs on the
values is whether the row that is laid as the claim is true: Accepts.lean.
Main names:
  `batt_returns_any`: the batching's text returns on any rounds of the form.
  `atM3_accepts_any`: **the statement.** `atM3_accepts_moves`: at the rounds `movesAtM3`, at any
    matrix, mask entries, pile and slots.

What is not claimed. Values that were sent earlier stand in the state (each pending row's target;
the reply), and the state stands under the nine premises: that these nine read none of them is not
said here (Shape.lean of this folder: `fitSh_eq`, `formSh_eq`, `roomSh_eq`). "Accepts" is the field
`decide` alone: the test of the sub-protocol's step on the rounds (each round against its declared
entry; words below the prime) is not treated. Nothing on the row of the claim. That the nine
premises hold at a state of a run. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Honest.Accepts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Model Cb Iop
open Johnson.Desc.First.ForkGround (RowsOwed)
open VerifiableInference.Desc.Ground (takeMasksP)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law

/-- The batching's text returns on any rounds of the form: one element for the sum; for each of the
k variables two elements; no end value. -/
theorem batt_returns_any {k : ℕ} {owed : RowsOwed} {n : ℕ} {pile : List TensorRow} {ledger : ℕ}
    {d : St} {t : List ℕ × St} (h1 : owed.isNone = true) (hf : Batt.fits k pile = true)
    (h3 : pile.length = n) (ht : takeMasksP d ledger (Batt.masksOf k) = some t) (x : E)
    (h : Psc.Heard) (hl : h.rounds.length = k) (h2 : ∀ p ∈ h.rounds, p.1.length = 2)
    (hv : h.values = []) :
    ∃ row, batt owed k n pile ledger d (roundsOf x h) = .ok (row, t.2) := by
  have hfr : (t.1.map fun i => (⟨ledger, i⟩ : Slot)).length = 1 + 2 * k := by
    rw [List.length_map, takeMasks_length ht]
    rfl
  obtain ⟨o, ho⟩ := Law.run_some (x := x) (h := h) hf hfr hl h2 hv
  have h4 : o.rowMaps.length = pile.length := by
    obtain ⟨-, -, -, -, -, hmp, -⟩ := Law.run_fields hf ho
    rw [hmp, List.length_map, List.length_zip, OnBytes.Road.Hd.powers_len, Nat.min_self]
  exact ⟨Batt.rowOf pile o,
    batt_answers k owed n pile ledger d _ _ x t _ o h1 hf (oneDrawn_mk _ _ _) h3 ht
      (heard_roundsOf _ hv) ho h4⟩

variable {Cl : Type}

/-- **The joined sub-protocol accepts any elements in rounds of the kind's form.** The nine premises
are those of `atM3_accepts_code`. -/
theorem atM3_accepts_any {P : Where} {s : S} {f : First.FinOwn} {t : List ℕ × St}
    {msg : Array OracleNotice} (hs : s.here = .fin f)
    (hreply : (!P.reply || s.out.reply.isSome) = true) (hcount : s.out.pending.length = P.rows)
    (hfit : memberRowsFit s.st P.lin s.out.indexMasks s.out.pending = true)
    (hw : s.noneWaits = true) (hform : Batt.fits P.lin.kCol s.out.pending = true)
    (ht : takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol) = some t)
    (hlin : linOk s.st.codes P.lin = true) (hmsg : linMessageW P.lin = some msg) (x : E)
    (h : Psc.Heard) (hl : h.rounds.length = P.lin.kCol) (h2 : ∀ p ∈ h.rounds, p.1.length = 2)
    (hv : h.values = []) (cols : List (List (Nat × List UInt64))) :
    ∃ row, (atM3 (Cl := Cl) P).decide s (roundsOf x h) cols =
      .ok (withClaim s t.2.st msg row) := by
  have howed : (owedOf s).isNone = true := by
    unfold owedOf
    rw [if_pos hw]
    rfl
  obtain ⟨row, hb⟩ := batt_returns_any howed hform hcount ht x h hl h2 hv
  have hq : quiet t.2.st.codes P.lin = .ok msg := by
    rw [(takeMasks_same ht).1]
    exact quiet_returns hlin hmsg
  refine ⟨row, atM3_of_batt hs hreply hcount hfit hb ?_ hq cols⟩
  rw [roundsOf_length, hl]

/-- The same at the rounds `movesAtM3`, at any matrix and mask entries w, any pile and any slots:
they need not be the state's. -/
theorem atM3_accepts_moves {K : Type} [Field K] (ρ : Reading K) (σ : K → E) {nR : ℕ} {P : Where}
    {s : S} {f : First.FinOwn} {t : List ℕ × St} {msg : Array OracleNotice}
    (hs : s.here = .fin f) (hreply : (!P.reply || s.out.reply.isSome) = true)
    (hcount : s.out.pending.length = P.rows)
    (hfit : memberRowsFit s.st P.lin s.out.indexMasks s.out.pending = true)
    (hw : s.noneWaits = true) (hform : Batt.fits P.lin.kCol s.out.pending = true)
    (ht : takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol) = some t)
    (hlin : linOk s.st.codes P.lin = true) (hmsg : linMessageW P.lin = some msg)
    (w : Wit K nR P.lin.kCol) (pile : List TensorRow) (fresh : List Slot) (x eps : E)
    (gs : List E) (hg : gs.length = P.lin.kCol) (cols : List (List (Nat × List UInt64))) :
    ∃ row, (atM3 (Cl := Cl) P).decide s (movesAtM3 ρ σ w pile fresh x eps gs) cols =
      .ok (withClaim s t.2.st msg row) := by
  have hl : (sent (maskAt w fresh) (ρ.val eps) P.lin.kCol 0 (tabsOf ρ w pile (ρ.val x))
      (gs.map ρ.val)).length = gs.length := by rw [sent_length, hg]
  exact atM3_accepts_any hs hreply hcount hfit hw hform ht hlin hmsg x
    (codeHeard ρ σ (maskAt w fresh) (tabsOf ρ w pile (ρ.val x)) P.lin.kCol eps gs)
    (by
      show (codeRounds σ _ gs).length = _
      rw [codeRounds_len σ _ gs hl, sent_length])
    (codeRounds_two σ _ gs) rfl cols

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.batt_returns_any
#print axioms VerifiableInference.Desc.K13.Honest.atM3_accepts_any
#print axioms VerifiableInference.Desc.K13.Honest.atM3_accepts_moves
