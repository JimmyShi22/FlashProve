-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Coin/Inside.lean: FROM A BLOCK's PLAIN LAW AT ITS OWN RECORD TO THE BLOCK SEATED BY
`Block.inside` (Johnson/Desc/Block.lean): a block whose own record T is born and dies inside it:
`enter` makes it of the chain's record S, `leave` lays what is to stay back. Statements and proofs.

  `foldOne`: what the fold over one block's list says, both ways.
  `chainOne`: the like for `chainAt`.
  `seated`: the piece with `p.b.inside enter leave` in p.b's place: the same stretch and errors.
  `seated_out`: where the seated piece puts out b: `enter` returned t, the piece put out t' from t
    at the same oracles and the same transcript and left the same oracles, and `leave` returned
    b's record.
  `leads_seated`: **the law goes over**, at the same errors: the promise is asked at what `enter`
    returns; the relation holds at (t, t').
A rule for every block: a tool. The kind K12 alone is seated so (five places).
Nearest kin: `leads_lift`, `leads_under` (Johnson/Desc/Plain/LiftBelow.lean); `Seat.step_inside`
(Johnson/Desc/K12/SeatLaws.lean), which is called.

-/
import Johnson.Desc.Plain.PieceYes
import Johnson.Desc.K12.SeatLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.K12.Coin
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain

variable {S T Cl W : Type} {C : CK} {F : Frame}

/-- What the fold over the list of one block says. -/
theorem foldOne (ft : ℕ) (b : Block S Cl) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (out : S × List Fmt.RoundView × List OpenedColumn) :
    foldBlocks ft [b] s rs cols = .ok out ↔
      (rs.take b.rounds.length).length = b.rounds.length ∧
        ∃ s' k, b.step ft s (rs.take b.rounds.length) cols = .ok (s', k) ∧
          out = (s', rs.drop b.rounds.length, cols.drop k) := by
  simp only [foldBlocks, List.splitAt_eq]
  constructor
  · intro H
    split at H
    next => exact nomatch H
    next hl =>
      split at H
      next => exact nomatch H
      next s' k hst => exact ⟨not_not.1 hl, s', k, hst, (Except.ok.inj H).symm⟩
  · rintro ⟨hl, s', k, hst, rfl⟩
    rw [if_neg (not_not.2 hl), hst]

/-- The like for a chain of one block. -/
theorem chainOne (name : String) (ft : ℕ) (b : Block S Cl) (s e : S) (v : Fmt.View) :
    chainAt name ft [b] s v = .ok e ↔ foldBlocks ft [b] s v.rounds v.opened = .ok (e, [], []) := by
  constructor
  · exact chainAtOk
  · intro H
    unfold chainAt
    rw [if_neg (by simp), H]

/-- The piece with the block seated inside. -/
def seated (p : Piece C F T Cl W) (enter : S → Except String T)
    (leave : S → T → Except String S) : Piece C F S Cl W :=
  ⟨p.b.inside enter leave, p.base, p.ds, p.back, fun _ _ w => w, p.err⟩

theorem seated_out (p : Piece C F T Cl W) (enter : S → Except String T)
    (leave : S → T → Except String S) (a : S × F.E.Str) (τ : Iop.Tr (uLT C p.ds))
    (b : S × F.E.Str) (h : (seated p enter leave).ior.red.out a τ = some b) :
    ∃ t t', enter a.1 = .ok t ∧ p.ior.red.out (t, a.2) τ = some (t', b.2) ∧
      leave a.1 t' = .ok b.1 := by
  obtain ⟨s', hs, rfl⟩ := Option.map_eq_some_iff.1 h
  have hs' : (if sTests C p.stage a.2 τ then
      (seated p enter leave).run a.1 (sView C p.stage a.2 τ) else none) = some s' := hs
  split at hs'
  · rename_i ht
    have hc := (chainOne _ _ _ _ _ _).1 (toOptionOk hs')
    obtain ⟨hl, s₁, k, hst, he⟩ := (foldOne _ _ _ _ _ _).1 hc
    obtain ⟨t, t', h1, h2, h3⟩ := (Seat.step_inside F.ft enter p.b leave a.1 s₁ _ _ k).1 hst
    have e₁ : s' = s₁ := congrArg Prod.fst he
    refine ⟨t, t', h1, ?_, e₁ ▸ h3⟩
    have hf : foldBlocks F.ft [p.b] t ((sView C p.stage a.2 τ).rounds ++ p.back)
        (sView C p.stage a.2 τ).opened = .ok (t', [], []) :=
      (foldOne _ _ _ _ _ _).2 ⟨hl, t', k, h2,
        Prod.ext rfl (Prod.ext (congrArg (fun x => x.2.1) he) (congrArg (fun x => x.2.2) he))⟩
    have hr : p.run t (sView C p.stage a.2 τ) = some t' := by
      show (chainAt p.b.name F.ft [p.b] t
        ⟨(sView C p.stage a.2 τ).rounds ++ p.back, (sView C p.stage a.2 τ).opened⟩).toOption = _
      rw [(chainOne _ _ _ _ _ _).2 hf]
      rfl
    show ((if sTests C p.stage a.2 τ then p.run t (sView C p.stage a.2 τ) else none).map
      fun xo => (xo, p.ior.imp a.2 τ)) = some _
    rw [if_pos ht, hr]
    rfl
  · cases hs'

/-- **The law goes over to the seated block.** -/
theorem leads_seated (p : Piece C F T Cl W) (enter : S → Except String T)
    (leave : S → T → Except String S) (on : T × F.E.Str → Prop)
    (Q : T × F.E.Str → T × F.E.Str → Prop) (h : p.ior.red.Leads on Q p.err) :
    (seated p enter leave).ior.red.Leads (fun a => ∀ t, enter a.1 = .ok t → on (t, a.2))
      (fun a b => ∃ t t', enter a.1 = .ok t ∧ leave a.1 t' = .ok b.1 ∧ Q (t, a.2) (t', b.2))
      (seated p enter leave).err := by
  intro a ha
  cases he : enter a.1 with
  | error e =>
    refine Doomed.of_forall _ _ fun τ b hb => ?_
    obtain ⟨t, _, h1, _⟩ := seated_out p enter leave a τ b hb
    rw [he] at h1
    cases h1
  | ok t =>
    refine Doomed.mono _ _ ?_ (h (t, a.2) (ha t he))
    intro τ hτ b hb
    obtain ⟨t₁, t', h1, h2, h3⟩ := seated_out p enter leave a τ b hb
    rw [he] at h1
    cases h1
    exact ⟨t, t', he, h3, hτ _ h2⟩

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.seated_out
#print axioms VerifiableInference.Desc.K12.Coin.leads_seated
