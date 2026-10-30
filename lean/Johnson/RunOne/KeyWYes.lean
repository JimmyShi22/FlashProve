-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyWYes.lean: THE KEY FILE's ROW 1.17 (w.1.send: W and the mask that rides with it are sent; then K13's rows: the request's own group, the joinings, the row (Eval)): THE SEAT's YES, PART BY PART. By row 1.1's pattern (KeySendYes1.msg_yes | group_yes).
OBJECT: sendW one N sent groups (Johnson/Desc/Key/One.lean:191) · USER: row 1.17's (yes) · LETTERS: β Cl · one N sent groups.
  parW'     the sending kind's parameters at the place
  w_yes     PROVED: a yes of the block on two rounds IS: the shape has a message with W · the record announces what ROUNDS says · a yes of the sending's seat · the chain has come to its end, a claim lies · a yes of K13's rows at the numbers just sent · the state behind written out
  rows_mask PROVED: what RowsLaid does not carry: which number the record calls W's mask: where masks ride ahead, the last of the numbers sent
CALLED AS THEY LIE: K13.Law.rowsB_ok (Johnson/Desc/K13/Law/M4Proof.lean:35: general in the lens) · lens_get | lens_set (KeyLensLaws) · decide_andThen (KeyAndThen).
Nothing on soundness.
-/
import Johnson.RunOne.KeySendYes1
import Johnson.Desc.Key.KeyLensLaws
import Johnson.Desc.Key.KeyAndThen
import Johnson.Desc.K13.Law.M4Proof

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows1
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key
open VerifiableInference.Desc.K1 (Par)
open VerifiableInference.Desc.K13.Law (rowsB_ok)

section
variable {β Cl : Type}

/-- The place's parameters. -/
abbrev parW' (one : OneTime) (N : Pieces) (groups : List (List Nat)) (msg : Array OracleNotice) : Par :=
  sendingPar one N.w "W and what rides with it" msg groups

theorem w_yes (one : OneTime) (N : Pieces) (sent : Nat) (groups : List (List Nat)) (bw : Block (ChainState β) Cl)
    (hb : sendW one N sent groups = some bw) (s s' : ChainState β) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : bw.decide s [r₁, r₂] gs = .ok s') :
    ∃ (msg : Array OracleNotice) (s₁ : ChainState β) (gs' : List (List (Nat × List UInt64))) (l : LinFirst) (o : LinFirst × K13.St),
      linMessageW one.lin = some msg ∧ (s.msgW == (parW' one N groups msg).sent) = true ∧
      (sendingSeat "K1: W's sending" (parW' one N groups msg) : Block (ChainState β) Cl).decide s [r₁, r₂] gs' = .ok s₁ ∧
      s₁.atEnd = true ∧ s₁.lin = some l ∧ K13.rows one.lin l.claim s₁.sent s₁.d = .ok o ∧
      s' = { s₁ with ids := s₁.sent, owed := s₁.debt, lin := some o.1, d := o.2 } := by
  unfold sendW at hb
  cases hm : linMessageW one.lin with
  | none => rw [hm] at hb; cases hb
  | some msg =>
    rw [hm] at hb
    obtain rfl := Option.some.inj hb
    dsimp only at h
    rw [decide_andThen] at h
    obtain ⟨t₃, h3, hr⟩ := K13.Law.ebind_ok.1 h
    rw [decide_andThen] at h3
    obtain ⟨t₂, h2, hq⟩ := K13.Law.ebind_ok.1 h3
    rw [decide_andThen] at h2
    obtain ⟨t₁, h1, hs⟩ := K13.Law.ebind_ok.1 h2
    have h1' : (do need "K1: the record does not announce what ROUNDS says" (s.msgW == (parW' one N groups msg).sent); pure s : Except String (ChainState β)) = .ok t₁ := h1
    obtain ⟨_, hn, hp⟩ := ChainEnd.bind_ok h1'
    obtain rfl : s = t₁ := Except.ok.inj hp
    obtain rfl : { t₂ with ids := t₂.sent } = t₃ := Except.ok.inj hq
    obtain ⟨p, l, o, hg, hl, ho, rfl⟩ := rowsB_ok batchLens _ hr
    obtain ⟨ha, rfl⟩ := (lens_get _ _).1 hg
    exact ⟨msg, t₂, _, l, o, rfl, Plain.need_ok hn, hs, ha, hl, ho, rfl⟩

end

/-- **Which number the record calls W's mask.** -/
theorem rows_mask (S : LinShape) (claim : LinClaim) (ids : Array Nat) (d d' : K13.St) (lin : LinFirst)
    (h : K13.rows S claim ids d = .ok (lin, d')) : lin.mask = if S.masksAhead then ids.back? else none := by
  unfold K13.rows at h
  obtain ⟨w, _, k1⟩ := (LaidW.ok_bind _ _ _).1 h
  obtain ⟨b, _, k2⟩ := (LaidW.ok_bind _ _ _).1 k1
  obtain ⟨d₁, _, k3⟩ := (LaidW.ok_bind _ _ _).1 k2
  obtain ⟨d₂, _, k4⟩ := (LaidW.ok_bind _ _ _).1 k3
  obtain ⟨split, _, k5⟩ := (LaidW.ok_bind _ _ _).1 k4
  obtain ⟨d₃, _, k6⟩ := (LaidW.ok_bind _ _ _).1 k5
  obtain ⟨mask, hmk, k7⟩ := (LaidW.ok_bind _ _ _).1 k6
  obtain ⟨row, _, k8⟩ := (LaidW.ok_bind _ _ _).1 k7
  obtain ⟨d₄, _, hfin⟩ := (LaidW.ok_bind _ _ _).1 k8
  have hmk' := (LaidW.there_ok _ _ _).1 hmk
  have e : lin = { w := w, split := split, own := b.1, mask := mask, claim := claim } := (congrArg Prod.fst (Except.ok.inj hfin)).symm
  rw [e]
  show mask = _
  cases hS : S.masksAhead with
  | false =>
    rw [hS] at hmk'
    simpa using (Option.some.inj hmk').symm
  | true =>
    rw [hS] at hmk'
    simp only [if_true] at hmk' ⊢
    cases hbk : ids.back? with
    | none => rw [hbk] at hmk'; cases hmk'
    | some m =>
      rw [hbk] at hmk'
      exact (Option.some.inj hmk').symm

end Johnson.RunOne.KeyRows1

#print axioms Johnson.RunOne.KeyRows1.w_yes
#print axioms Johnson.RunOne.KeyRows1.rows_mask
