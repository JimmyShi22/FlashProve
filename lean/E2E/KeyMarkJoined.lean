--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyMarkJoined.lean: THE MARK ON THE ROW WEIGHTS, JOINED ALONG THE KEY FILE's FIRST CHAIN's LAST
THREE SUB-PROTOCOLS. E2E/KeyWeightsMark.lean shows, step by step, that the weights which "the rows
on the table" makes lie below the matrix's rows and that the batching keeps that. Here the steps are
joined at the sub-protocols as the description lays them: where "batt.1.batt" accepts, the claim
that it lays has such weights; "w.1.send" hands the claim on; the seal turns nothing. So the state
that the third chain's start reads has the mark. Statements and proofs, at all values. On what the
verifier's steps write where they accept: NOTHING IS SHOWN OF ANY PROVER.

  **`batch_low`**: where "batt.1.batt" (`Key.batchTableRows`) accepts, under the public test "the
    parameters are admitted": the state behind has a claim, and its row weights are `Low`. By the
    library's
    `Key.seat_says` (Johnson/Desc/Key/KeyBattSays.lean).
  **`sendW_claim`**: where "w.1.send" (`Key.sendW`) accepts at a state with a claim, the state
    behind has the same claim. By the library's `rowsB_ok` and `rows_ok` (Johnson/Desc/K13/Law/).
  `seal_same`: the seal returns the state as it is.
  **`three_low`**: the three in a row. **`three_mark`**: so `linSh` (E2E/KeyShapeDoor.lean) of the
    claim at the chain's last state has the mark `weights`, where the table's two bounds hold.

Limits.
- "The parameters are admitted" is a premise here; the first chain asks it behind the own message's
  sending, at the codes that its statement holds.
- The library's files KeyBattSays.lean and KeyTensorOk.lean, which are called, are not reviewed.



-/
import E2E.KeyWeightsMark
import E2E.KeyShapeDoor
import Johnson.Desc.Key.KeyBattSays
import Johnson.Desc.K13.Law.M4Proof

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.AtFiles
open OnBytes OnBytes.Params
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Key (ChainState batchTableRows sendW firstChainEnd Pieces)
open VerifiableInference.Desc.K13.Law (ebind_ok)

variable {β Cl : Type}

/-- **Where "batt.1.batt" accepts, the claim that it lays has weights below the matrix's rows.** -/
theorem batch_low (keysOf : β → List (List Lkp.Keys)) (one : OneTime) (N : Pieces) (sent : Nat)
    (s s' : ChainState β) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (batchTableRows (Cl := Cl) keysOf one N sent).decide s rs gs = .ok s') (codes : Codes)
    (ha : Wf.admitted codes one.ranges (Wf.matrixOf one.lin) = true) :
    ∃ l, s'.lin = some l ∧ ∀ t ∈ l.claim.g, Low one.lin.kRow one.lin.matrixRows t := by
  obtain ⟨rows, out, msg, rs', h1, -, hb, rfl⟩ :=
    VerifiableInference.Desc.Key.seat_says keysOf one N sent s s' rs gs h
  exact ⟨_, rfl, batt_low _ _ _ rows _ _ _ out hb
    (layPile_low_admitted keysOf one s _ h1 codes ha)⟩

/-- **"w.1.send" hands the claim on.** -/
theorem sendW_claim (one : OneTime) (N : Pieces) (sent : Nat) (groups : List (List Nat))
    (bw : Block (ChainState β) Cl) (hw : sendW one N sent groups = some bw) (s s' : ChainState β)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (h : bw.decide s rs gs = .ok s')
    (l : LinFirst) (hl : s.lin = some l) : ∃ l', s'.lin = some l' ∧ l'.claim = l.claim := by
  unfold sendW at hw
  obtain ⟨msg, -, rfl⟩ := Option.map_eq_some_iff.1 hw
  dsimp only at h
  rw [VerifiableInference.Desc.decide_andThen] at h
  obtain ⟨t₃, h3, hr⟩ := ebind_ok.1 h
  rw [VerifiableInference.Desc.decide_andThen] at h3
  obtain ⟨t₂, h2, hq⟩ := ebind_ok.1 h3
  rw [VerifiableInference.Desc.decide_andThen] at h2
  obtain ⟨t₁, h1, hs⟩ := ebind_ok.1 h2
  have e1 : t₁.lin = s.lin := by
    have h1' : (do
      VerifiableInference.Desc.need "K1: the record does not announce what ROUNDS says"
        (s.msgW == (VerifiableInference.Desc.Key.sendingPar one N.w "W and what rides with it" msg
          groups).sent)
      pure s : Except String (ChainState β)) = .ok t₁ := h1
    obtain ⟨_, _, h1'⟩ := VerifiableInference.Desc.Third.Law.ok_of_bind h1'
    rw [← Except.ok.inj h1']
  have e2 : t₂.lin = t₁.lin := by
    unfold VerifiableInference.Desc.Key.sendingSeat at hs
    dsimp only at hs
    cases hb : (VerifiableInference.Desc.K1.sendOwn (Cl := Cl)
        (VerifiableInference.Desc.Key.sendingPar one N.w "W and what rides with it" msg
          groups)).decide { owed := t₁.debt, held := VerifiableInference.Desc.Key.withLoc t₁.d #[] }
        _ _ with
    | error e =>
      rw [hb] at hs
      cases hs
    | ok y =>
      rw [hb] at hs
      rw [← Except.ok.inj hs]
  have e3 : t₃.lin = t₂.lin := by
    have hq' : (pure { t₂ with ids := t₂.sent } : Except String (ChainState β)) = .ok t₃ := hq
    rw [← Except.ok.inj hq']
  obtain ⟨p, l₀, o, hp, hpl, ho, rfl⟩ := VerifiableInference.Desc.K13.Law.rowsB_ok _ _ hr
  obtain ⟨-, rfl⟩ := (VerifiableInference.Desc.Key.lens_get _ _).1 hp
  obtain ⟨-, -, -, hc, -⟩ := VerifiableInference.Desc.K13.Law.rows_ok ho
  have hl₀ : l₀ = l := by
    have e4 : t₃.lin = some l₀ := hpl
    rw [e3, e2, e1, hl] at e4
    exact (Option.some.inj e4).symm
  refine ⟨o.1, ?_, by rw [hc, hl₀]⟩
  rw [VerifiableInference.Desc.Key.lens_set]

/-- The seal returns the state as it is. -/
theorem seal_same (N : Pieces) (inFront : List Fmt.DeclaredRound) (s s' : ChainState β)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (firstChainEnd (β := β) (Cl := Cl) N inFront).decide s rs gs = .ok s') : s' = s := by
  have h' : (VerifiableInference.Desc.ChainEnd.refuse
      ([("end: no count of rows is owed", s.noneWaits)] ++
        VerifiableInference.Desc.Key.untestedButOwn s)).map (fun _ => s) = .ok s' := h
  cases hr : VerifiableInference.Desc.ChainEnd.refuse
      ([("end: no count of rows is owed", s.noneWaits)] ++
        VerifiableInference.Desc.Key.untestedButOwn s) with
  | error e =>
    rw [hr] at h'
    cases h'
  | ok u =>
    rw [hr] at h'
    exact (Except.ok.inj h').symm

/-- **The three in a row**: the last state has a claim whose row weights lie below the matrix's
rows.
-/
theorem three_low (keysOf : β → List (List Lkp.Keys)) (one : OneTime) (N : Pieces) (sent : Nat)
    (groups : List (List Nat)) (bw : Block (ChainState β) Cl)
    (hw : sendW one N sent groups = some bw) (inFront : List Fmt.DeclaredRound)
    (s a b c : ChainState β) (r₁ r₂ r₃ : List Fmt.RoundView)
    (g₁ g₂ g₃ : List (List (Nat × List UInt64)))
    (h₁ : (batchTableRows (Cl := Cl) keysOf one N sent).decide s r₁ g₁ = .ok a)
    (h₂ : bw.decide a r₂ g₂ = .ok b)
    (h₃ : (firstChainEnd (β := β) (Cl := Cl) N inFront).decide b r₃ g₃ = .ok c) (codes : Codes)
    (ha : Wf.admitted codes one.ranges (Wf.matrixOf one.lin) = true) :
    ∃ l, c.lin = some l ∧ ∀ t ∈ l.claim.g, Low one.lin.kRow one.lin.matrixRows t := by
  obtain ⟨l, hl, hlow⟩ := batch_low keysOf one N sent s a r₁ g₁ h₁ codes ha
  obtain ⟨l', hl', e⟩ := sendW_claim one N sent groups bw hw a b r₂ g₂ h₂ l hl
  obtain rfl := seal_same N inFront b c r₃ g₃ h₃
  exact ⟨l', hl', by rw [e]; exact hlow⟩

/-- **So what the third chain's start reads of that claim has the mark.** cs: the codes at which the
layout of Omega's table is taken. -/
theorem three_mark {one : OneTime} {l : LinFirst}
    (h : ∀ t ∈ l.claim.g, Low one.lin.kRow one.lin.matrixRows t) (cs : Codes)
    (h2 : one.lin.kRow ≤ (linLayOmega cs one.lin).bits) (h3 : (linLayOmega cs one.lin).bits ≤ 63) :
    (linSh one.lin cs l).weights = true :=
  weightsB_of_low one.lin _ _ h h2 h3

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.batch_low
#print axioms AtPublicFiles.AtFiles.sendW_claim
#print axioms AtPublicFiles.AtFiles.seal_same
#print axioms AtPublicFiles.AtFiles.three_low
#print axioms AtPublicFiles.AtFiles.three_mark
