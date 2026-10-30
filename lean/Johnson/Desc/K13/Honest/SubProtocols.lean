--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/SubProtocols.lean: kind K13, the members' batching: THE SUB-PROTOCOLS'
ACCEPTANCE, FROM THE PREMISES TO THE RETURN: from what their tests ask of the verifier's own state,
and from a return of the batching's text, to the acceptance by the three sub-protocols at any lens
and by the joined sub-protocol at the state that a proof file's first chain carries (`atM3`,
Johnson/Desc/K13/AtS.lean), with the state that it leaves as a term. Statements with their proofs.
No prover and no field stands in this file. "Accepts" is: the field `decide` returns `.ok`.

The sub-protocols test no sent value. Their tests read the state (where the chain stands; the reply;
the pile's number and form; the message of index masks and its ledger; the public shape) and count
what was sent. What they ask of the state stands here as premises, each in the words of the test.
Main names:
  `takeMasks_length`: the taking of mask entries (`takeMasksP`,
    Johnson/Desc/First/Base/Ground.lean) hands out as many as it is asked for.
  `roundsOf_length`, `shownRound_eq`, `heard_roundsOf`: the rounds of
    Johnson/Desc/K13/Honest/MovesAtM3.lean are 2 + k; the kind's text hears in them what they were
    made of.
  `frontB_accepts`, `battB_accepts`, `quiet_returns`, `quietB_accepts`: the three sub-protocols at
    any lens.
  `atEnd`, `withClaim`: the state at the chain's end; the state with the claim laid.
  `frontS_accepts`, `battS_accepts`, `quietS_accepts`: the same at the first chain's state.
  `atM3_of_batt`: **the joined sub-protocol accepts where the batching's text returns.**

What is not claimed. That the premises on the state hold at the place: they are owed by the
sub-protocols in front and by the tests on the plan. That the text returns:
Johnson/Desc/K13/Honest/Accepts.lean. The sub-protocol's test on the plan (`planOk`) and the
format's step in front of the decision (each round against its declared entry; words below the
prime) are not treated. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Honest.MovesAtM3
import Johnson.Desc.K13.Law.PinDec
import Johnson.Desc.K13.Law.Silly

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Model Cb Iop
open OnBytes.Params (LinShape)
open Johnson.Desc.First.ForkGround (RowsOwed)
open VerifiableInference.Desc.Ground (takeMaskP takeMasksInto takeMasksP)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law

/-! ## The taking of mask entries hands out as many as it is asked for -/

/-- The loop of the taking. -/
theorem takeMasksInto_length (o : ℕ) : ∀ (n : ℕ) (d : St) (acc : Array ℕ) (t : List ℕ × St),
    takeMasksInto o n d acc = some t → t.1.length = acc.size + n
  | 0, d, acc, t, h => by
    have e : some (acc.toList, d) = some t := h
    rw [← Option.some.inj e]
    simp
  | n + 1, d, acc, t, h => by
    unfold takeMasksInto at h
    cases hm : takeMaskP d o with
    | none =>
      rw [hm] at h
      cases h
    | some q =>
      obtain ⟨i, d'⟩ := q
      rw [hm] at h
      have e := takeMasksInto_length o n d' _ t h
      rw [e, Array.size_push]
      omega

/-- The taking. -/
theorem takeMasks_length {d : St} {o n : ℕ} {t : List ℕ × St} (h : takeMasksP d o n = some t) :
    t.1.length = n := by
  have e := takeMasksInto_length o n d #[] t h
  simpa using e

/-! ## The rounds -/

/-- There are 2 + k rounds. -/
theorem roundsOf_length (x : E) (h : Psc.Heard) : (roundsOf x h).length = 2 + h.rounds.length := by
  simp only [roundsOf, List.length_cons, List.length_map]
  omega

/-- A round of Johnson/Desc/K13/Honest/MovesAtM3.lean is the round of the kind's laws. -/
theorem shownRound_eq (s : List E) (c : E) : shownRound s c = rvMk s c := rfl

/-- In the rounds behind the first, the kind's text hears the sum, eps and the pairs
of which they were made, where no value is shown. -/
theorem heard_roundsOf (h : Psc.Heard) (hv : h.values = []) :
    heard (shownRound [h.mu] h.eps :: h.rounds.map fun p => shownRound p.1 p.2) = .ok h := by
  show heard (rvMk [h.mu] h.eps :: h.rounds.map fun p => rvMk p.1 p.2) = .ok h
  rw [heard_mk]
  cases h with
  | mk mu eps rounds values =>
    have e : values = [] := hv
    rw [e]

/-! ## The three sub-protocols, at any lens -/

section AnyLens
variable {T Cl : Type} (X : Lens T) (P : Where)

/-- The front accepts. -/
theorem frontB_accepts {t t₁ : T} {p : Part} (he : X.enter t = some t₁) (hp : X.get? t₁ = some p)
    (h1 : (!P.reply || p.heard.isSome) = true) (h2 : p.pile.length = P.rows)
    (h3 : memberRowsFit p.d.st P.lin p.indexMasks p.pile = true) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    (frontB (Cl := Cl) X P).decide t rs gs = .ok t₁ := by
  simp only [frontB, still, front_is, Law.bind_ok, Law.there_ok, Law.need_ok, Law.pure_ok,
    Lens.part]
  exact ⟨t₁, he, p, hp, (), ⟨(), h1, (), beq_iff_eq.2 h2, h3⟩, rfl⟩

/-- The batching's sub-protocol accepts where its text returns. -/
theorem battB_accepts {t : T} {p : Part} {out : TensorRow × St} {rs : List Fmt.RoundView}
    (hp : X.get? t = some p) (hl : p.lin.isNone = true)
    (ho : batt p.owed P.lin.kCol P.rows p.pile p.indexMasks p.d rs = .ok out)
    (gs : List (List (Nat × List UInt64))) :
    (claimCombinationBlock (Cl := Cl) X P).decide t rs gs =
      .ok (X.set t { p with owed := none, lin := some { claim := memberClaim out.1 }, d := out.2 })
    := by
  simp only [claimCombinationBlock, Law.bind_ok, Law.there_ok, Law.need_ok, Law.pure_ok, Lens.part]
  exact ⟨p, hp, (), hl, out, ho, rfl⟩

/-- The text in front of W's commitment returns at a lawful shape. -/
theorem quiet_returns {codes : Codes} {Sh : LinShape} {msg : Array OracleNotice}
    (h1 : linOk codes Sh = true) (h2 : linMessageW Sh = some msg) : quiet codes Sh = .ok msg := by
  simp only [quiet_is, Law.bind_ok, Law.need_ok, Law.there_ok]
  exact ⟨(), h1, h2⟩

/-- So does its sub-protocol. -/
theorem quietB_accepts {t : T} {p : Part} {msg : Array OracleNotice} (hp : X.get? t = some p)
    (hl : p.lin.isSome = true) (hq : quiet p.d.st.codes P.lin = .ok msg) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    (quietB (Cl := Cl) X P).decide t rs gs = .ok (X.set t { p with msg := msg }) := by
  simp only [quietB, still, Law.bind_ok, Law.there_ok, Law.need_ok, Law.pure_ok, Lens.part]
  exact ⟨p, hp, (), hl, msg, hq, rfl⟩

end AnyLens

/-! ## The joined sub-protocol, at the first chain's state -/

variable {Cl : Type}

/-- The state at the chain's end, with nothing laid yet. -/
abbrev atEnd (s : S) : S := { s with here := .mem { msg := #[], ids := #[], lin := none } }

/-- The state behind the batching: the ledger moved on, the claim laid. -/
abbrev withClaim (s : S) (st : Statement) (msg : Array OracleNotice) (row : TensorRow) : S :=
  { s with st := st, rowsOwed := none, here := .mem ⟨msg, #[], some { claim := memberClaim row }⟩ }

/-- The front, at the first chain's state. -/
theorem frontS_accepts {P : Where} {s : S} {f : First.FinOwn} (hs : s.here = .fin f)
    (hreply : (!P.reply || s.out.reply.isSome) = true) (hcount : s.out.pending.length = P.rows)
    (hfit : memberRowsFit s.st P.lin s.out.indexMasks s.out.pending = true) (a : List Fmt.RoundView)
    (b : List (List (Nat × List UInt64))) :
    (frontB (Cl := Cl) atS P).decide s a b = .ok (atEnd s) := by
  have e1 : atS.enter s = some s.enterMem := by simp only [atS, hs]
  have e2 : s.enterMem = atEnd s := by simp only [S.enterMem, hs]
  have he : atS.enter s = some (atEnd s) := by rw [e1, e2]
  exact frontB_accepts atS P he rfl hreply hcount hfit a b

/-- The batching's sub-protocol, at the first chain's state. -/
theorem battS_accepts {P : Where} {s : S} {row : TensorRow} {d' : St} {rs : List Fmt.RoundView}
    (hb : batt (owedOf s) P.lin.kCol P.rows s.out.pending s.out.indexMasks (dOf s) rs =
      .ok (row, d')) (b : List (List (Nat × List UInt64))) :
    (claimCombinationBlock (Cl := Cl) atS P).decide (atEnd s) rs b = .ok (withClaim s d'.st #[] row) :=
  battB_accepts atS P (t := atEnd s)
    (p := { owed := owedOf s, heard := s.out.reply, indexMasks := s.out.indexMasks,
            pile := s.out.pending, msg := #[], ids := #[], lin := none, d := dOf s })
    (out := (row, d')) rfl rfl hb b

/-- The sub-protocol in front of W's commitment, at the first chain's state. -/
theorem quietS_accepts {P : Where} {s : S} {row : TensorRow} {st : Statement}
    {msg : Array OracleNotice} (hq : quiet st.codes P.lin = .ok msg) (a : List Fmt.RoundView)
    (b : List (List (Nat × List UInt64))) :
    (quietB (Cl := Cl) atS P).decide (withClaim s st #[] row) a b =
      .ok (withClaim s st msg row) :=
  quietB_accepts atS P (t := withClaim s st #[] row)
    (p := { owed := none, heard := s.out.reply, indexMasks := s.out.indexMasks,
            pile := s.out.pending, msg := #[], ids := #[],
            lin := some { claim := memberClaim row },
            d := { st := st, book := s.book, roots := s.roots, opened := [], loc := () } })
    (msg := msg) rfl rfl hq a b

/-- **The joined sub-protocol accepts where the batching's text returns.** -/
theorem atM3_of_batt {P : Where} {s : S} {f : First.FinOwn} {row : TensorRow} {d' : St}
    {msg : Array OracleNotice} {rs : List Fmt.RoundView} (hs : s.here = .fin f)
    (hreply : (!P.reply || s.out.reply.isSome) = true) (hcount : s.out.pending.length = P.rows)
    (hfit : memberRowsFit s.st P.lin s.out.indexMasks s.out.pending = true)
    (hb : batt (owedOf s) P.lin.kCol P.rows s.out.pending s.out.indexMasks (dOf s) rs =
      .ok (row, d')) (hlen : rs.length = 2 + P.lin.kCol)
    (hq : quiet d'.st.codes P.lin = .ok msg) (cols : List (List (Nat × List UInt64))) :
    (atM3 (Cl := Cl) P).decide s rs cols = .ok (withClaim s d'.st msg row) := by
  have h' : (((frontB (Cl := Cl) atS P).decide s ((rs.take (2 + P.lin.kCol)).take 0)
      ((cols.take ((frontB (Cl := Cl) atS P).andThen "the front and the batching"
        (claimCombinationBlock atS P)).openings).take (frontB (Cl := Cl) atS P).openings)).bind fun s₁ =>
      (claimCombinationBlock (Cl := Cl) atS P).decide s₁ ((rs.take (2 + P.lin.kCol)).drop 0)
        ((cols.take ((frontB (Cl := Cl) atS P).andThen "the front and the batching"
          (claimCombinationBlock atS P)).openings).drop (frontB (Cl := Cl) atS P).openings)).bind (fun s₂ =>
                      (quietB (Cl := Cl) atS P).decide s₂ (rs.drop (2 + P.lin.kCol))
                        (cols.drop ((frontB (Cl := Cl) atS P).andThen "the front and the batching"
                          (claimCombinationBlock atS P)).openings)) = .ok (withClaim s d'.st msg row) := by
    rw [List.drop_zero, List.take_of_length_le (le_of_eq hlen)]
    exact ebind_ok.2 ⟨_,
      ebind_ok.2 ⟨_, frontS_accepts hs hreply hcount hfit _ _, battS_accepts hb _⟩,
      quietS_accepts hq _ _⟩
  have e : ((frontB (Cl := Cl) atS P).andThen "the front and the batching"
      (claimCombinationBlock atS P)).rounds.length = 2 + P.lin.kCol := by
    simp [Block.andThen, frontB, still, claimCombinationBlock, battRounds]
    omega
  rw [← e] at h'
  exact h'

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.takeMasksInto_length
#print axioms VerifiableInference.Desc.K13.Honest.takeMasks_length
#print axioms VerifiableInference.Desc.K13.Honest.shownRound_eq
#print axioms VerifiableInference.Desc.K13.Honest.roundsOf_length
#print axioms VerifiableInference.Desc.K13.Honest.heard_roundsOf
#print axioms VerifiableInference.Desc.K13.Honest.frontB_accepts
#print axioms VerifiableInference.Desc.K13.Honest.battB_accepts
#print axioms VerifiableInference.Desc.K13.Honest.quiet_returns
#print axioms VerifiableInference.Desc.K13.Honest.quietB_accepts
#print axioms VerifiableInference.Desc.K13.Honest.frontS_accepts
#print axioms VerifiableInference.Desc.K13.Honest.battS_accepts
#print axioms VerifiableInference.Desc.K13.Honest.quietS_accepts
#print axioms VerifiableInference.Desc.K13.Honest.atM3_of_batt
