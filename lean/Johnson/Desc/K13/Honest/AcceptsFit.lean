-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Honest/AcceptsFit.lean: kind K13, the members' batching: THE JOINED SUB-PROTOCOL
(`atM3`) RETURNS ON ALL ROUNDS THAT PASS THE STEP's OWN TEST ON ROUNDS (`roundsFit`,
Johnson/Desc/Block.lean), under the nine premises on the state of `atM3_accepts_any`
(AcceptsAny.lean of this folder). No form of the rounds is asked beside that test. Statements with
their proofs.
Main names:
  `sentE_items`, `oneDrawn_one`, `oneRound_fit`, `rounds_fit`: what the test on rounds gives the
    text's readers of a round.
  `heard_fit`: the text's reader of the sumcheck's rounds returns, with kCol rounds of two elements.
  `batt_returns_fit`, `atM3_accepts_fit`: **the statements.**

What is not claimed. The field `decide` alone is treated, not `Block.step`. That the rounds which
`atM3 P` declares are `battRounds P`. That any list of rounds passes the test. Nothing of the row
that is handed on. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Honest.AcceptsAny
import Johnson.Desc.K13.Law.Then

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Model Cb Iop
open VerifiableInference.Desc (roundsFit noDigest itemOf)
open VerifiableInference.Desc.Ground (takeMasksP)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.End (sentE)
open Johnson.Desc.First.ForkGround (RowsOwed)
open VerifiableInference.Desc.K13.Law

/-- Items that are n elements are read as n elements. -/
theorem sentE_items (dr : Fmt.Drawn) : ∀ (vals : List Fmt.ItemValue) (n : ℕ),
    vals.map itemOf = List.replicate n Fmt.Item.e → ∃ q, sentE ⟨vals, dr⟩ = some q ∧ q.length = n
  | [], n, h => by
    cases n with
    | zero => exact ⟨[], rfl, rfl⟩
    | succ m => cases h
  | v :: l, n, h => by
    cases n with
    | zero => cases h
    | succ m =>
      rw [List.map_cons, List.replicate_succ] at h
      injection h with h1 h2
      obtain ⟨q, hq, hl⟩ := sentE_items dr l m h2
      cases v with
      | e a =>
        refine ⟨E.ofTriple a :: q, ?_, by rw [List.length_cons, hl]⟩
        unfold sentE at hq ⊢
        simp only [List.mapM_cons] at hq ⊢
        rw [hq]
        rfl
      | _ => cases h1

/-- A round with one sampled element. -/
theorem oneDrawn_one (name : String) (r : Fmt.RoundView) (h : r.drawn.elems.length = 1) :
    ∃ x, oneDrawn name r = .ok x := by
  unfold oneDrawn
  cases he : r.drawn.elems with
  | nil =>
    rw [he] at h
    cases h
  | cons a l =>
    cases l with
    | nil => exact ⟨E.ofTriple a, rfl⟩
    | cons b l' =>
      rw [he] at h
      cases h

/-- A round of n elements and one sampled element is read. -/
theorem oneRound_fit (r : Fmt.RoundView) (n : ℕ) (h1 : r.vals.map itemOf = List.replicate n Fmt.Item.e)
    (h2 : r.drawn.elems.length = 1) : ∃ q x, oneRound (noDigest r) = .ok (q, x) ∧ q.length = n := by
  obtain ⟨q, hq, hl⟩ := sentE_items (noDigest r).drawn r.vals n h1
  obtain ⟨x, hx⟩ := oneDrawn_one "K13.read-one-drawn" (noDigest r) h2
  refine ⟨q, x, ?_, hl⟩
  unfold oneRound
  have e : sentE (noDigest r) = some q := hq
  rw [e, hx]
  rfl

/-- A variable's round states two elements. -/
theorem roundItems (p : Where) :
    ({ entry := roundEntry p } : Fmt.DeclaredRound).items.filter (· != .root) =
      List.replicate 2 Fmt.Item.e := by
  simp [Fmt.DeclaredRound.items, Fmt.Entry.cut, roundEntry, List.replicate_succ]

/-- The round of the sum states one. -/
theorem epsItems (p : Where) :
    ({ entry := epsEntry p } : Fmt.DeclaredRound).items.filter (· != .root) =
      List.replicate 1 Fmt.Item.e := by
  simp [Fmt.DeclaredRound.items, Fmt.Entry.cut, epsEntry, List.replicate_succ]

/-- What the test on rounds says of the first of some rounds. -/
theorem roundsFit_cons {d : Fmt.DeclaredRound} {ds : List Fmt.DeclaredRound} {r : Fmt.RoundView}
    {rs : List Fmt.RoundView} (h : roundsFit (d :: ds) (r :: rs) = true) :
    r.vals.map itemOf = d.items.filter (· != .root) ∧ r.drawn.elems.length = d.entry.drawE ∧
      roundsFit ds rs = true := by
  unfold roundsFit at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.2⟩

/-- The variables' rounds are read: as many, of two elements each. -/
theorem rounds_fit (p : Where) : ∀ (k : ℕ) (l : List Fmt.RoundView),
    roundsFit (List.replicate k { entry := roundEntry p }) l = true →
    ∃ inX, (l.map noDigest).mapM oneRound = .ok inX ∧ inX.length = k ∧
      ∀ q ∈ inX, q.1.length = 2
  | 0, [], _ => ⟨[], rfl, rfl, fun _ hq => nomatch hq⟩
  | 0, _ :: _, h => by cases h
  | k + 1, [], h => by cases h
  | k + 1, r :: l, h => by
    rw [List.replicate_succ] at h
    obtain ⟨h1, h2, h3⟩ := roundsFit_cons h
    rw [roundItems] at h1
    obtain ⟨q, x, hq, hl⟩ := oneRound_fit r 2 h1 h2
    obtain ⟨inX, hi, hn, h2'⟩ := rounds_fit p k l h3
    refine ⟨(q, x) :: inX, ?_, by rw [List.length_cons, hn], ?_⟩
    · rw [List.map_cons, List.mapM_cons, hq, hi]
      rfl
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hl
      · exact h2' y hy

/-- **The text's reader of the sumcheck's rounds returns.** -/
theorem heard_fit (p : Where) (l : List Fmt.RoundView)
    (h : roundsFit ({ entry := epsEntry p } :: List.replicate p.lin.kCol { entry := roundEntry p })
      l = true) :
    ∃ hd, heard (l.map noDigest) = .ok hd ∧ hd.rounds.length = p.lin.kCol ∧
      (∀ q ∈ hd.rounds, q.1.length = 2) ∧ hd.values = [] := by
  cases l with
  | nil => cases h
  | cons r l =>
    obtain ⟨h1, h2, h3⟩ := roundsFit_cons h
    rw [epsItems] at h1
    obtain ⟨q, x, hq, hl⟩ := oneRound_fit r 1 h1 h2
    obtain ⟨inX, hi, hn, h2'⟩ := rounds_fit p _ l h3
    cases q with
    | nil => cases hl
    | cons mu q' =>
      refine ⟨⟨mu, x, inX, []⟩, ?_, hn, h2', rfl⟩
      rw [List.map_cons]
      show (do
        let a ← oneRound (noDigest r)
        let mu ← there "K13.read-sum" a.1.head?
        let inX ← (l.map noDigest).mapM oneRound
        pure (⟨mu, a.2, inX, []⟩ : Psc.Heard) : Ans Psc.Heard) = _
      rw [hq, hi]
      rfl

/-- **The batching's text returns on all rounds that pass the test on rounds.** -/
theorem batt_returns_fit (p : Where) {owed : RowsOwed} {n : ℕ} {pile : List TensorRow} {ledger : ℕ}
    {d : St} {t : List ℕ × St} (h1 : owed.isNone = true) (hf : Batt.fits p.lin.kCol pile = true)
    (h3 : pile.length = n) (ht : takeMasksP d ledger (Batt.masksOf p.lin.kCol) = some t)
    (rs : List Fmt.RoundView) (hr : roundsFit (battRounds p) rs = true) :
    ∃ row, batt owed p.lin.kCol n pile ledger d (rs.map noDigest) = .ok (row, t.2) := by
  cases rs with
  | nil => cases hr
  | cons r l =>
    obtain ⟨-, e2, e3⟩ := roundsFit_cons hr
    obtain ⟨x, hx⟩ := oneDrawn_one "K13.sigma-one-drawn" (noDigest r) e2
    obtain ⟨hd, hh, hl, h2, hv⟩ := heard_fit p l e3
    have hfr : (t.1.map fun i => (⟨ledger, i⟩ : Slot)).length = 1 + 2 * p.lin.kCol := by
      rw [List.length_map, takeMasks_length ht]
      rfl
    obtain ⟨o, ho⟩ := Law.run_some (x := x) (h := hd) hf hfr hl h2 hv
    have h4 : o.rowMaps.length = pile.length := by
      obtain ⟨-, -, -, -, -, hmp, -⟩ := Law.run_fields hf ho
      rw [hmp, List.length_map, List.length_zip, OnBytes.Road.Hd.powers_len, Nat.min_self]
    exact ⟨Batt.rowOf pile o,
      batt_answers p.lin.kCol owed n pile ledger d _ _ x t hd o h1 hf hx h3 ht hh ho h4⟩

variable {Cl : Type}

/-- **The joined sub-protocol returns on all rounds that pass the step's own test on rounds**, shown
without the sealed digest, under the nine premises on the state. -/
theorem atM3_accepts_fit {P : Where} {s : S} {f : First.FinOwn} {t : List ℕ × St}
    {msg : Array OracleNotice} (hs : s.here = .fin f)
    (hreply : (!P.reply || s.out.reply.isSome) = true) (hcount : s.out.pending.length = P.rows)
    (hfit : memberRowsFit s.st P.lin s.out.indexMasks s.out.pending = true)
    (hw : s.noneWaits = true) (hform : Batt.fits P.lin.kCol s.out.pending = true)
    (ht : takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol) = some t)
    (hlin : linOk s.st.codes P.lin = true) (hmsg : linMessageW P.lin = some msg)
    (rs : List Fmt.RoundView) (hr : roundsFit (battRounds P) rs = true)
    (cols : List (List (Nat × List UInt64))) :
    ∃ row, (atM3 (Cl := Cl) P).decide s (rs.map noDigest) cols =
      .ok (withClaim s t.2.st msg row) := by
  have howed : (owedOf s).isNone = true := by
    unfold owedOf
    rw [if_pos hw]
    rfl
  obtain ⟨row, hb⟩ := batt_returns_fit P howed hform hcount ht rs hr
  have hq : quiet t.2.st.codes P.lin = .ok msg := by
    rw [(takeMasks_same ht).1]
    exact quiet_returns hlin hmsg
  refine ⟨row, atM3_of_batt hs hreply hcount hfit hb ?_ hq cols⟩
  rw [List.length_map, roundsFit_length _ _ hr]
  simp [battRounds]
  omega

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.sentE_items
#print axioms VerifiableInference.Desc.K13.Honest.oneDrawn_one
#print axioms VerifiableInference.Desc.K13.Honest.oneRound_fit
#print axioms VerifiableInference.Desc.K13.Honest.roundItems
#print axioms VerifiableInference.Desc.K13.Honest.epsItems
#print axioms VerifiableInference.Desc.K13.Honest.roundsFit_cons
#print axioms VerifiableInference.Desc.K13.Honest.rounds_fit
#print axioms VerifiableInference.Desc.K13.Honest.heard_fit
#print axioms VerifiableInference.Desc.K13.Honest.batt_returns_fit
#print axioms VerifiableInference.Desc.K13.Honest.atM3_accepts_fit
