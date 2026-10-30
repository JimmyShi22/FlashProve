-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/OneWay.lean: **A PLAIN LAW GOES OVER ONE WAY**: from a piece p to a piece q
over the same stretch whose every yes holds a yes of p on the same view. Statements and proofs.

`leads_alike` (Alike.lean) carries a law between pieces whose blocks have ONE decision. A seat in a
description's flat list may stand behind guards, or be joined with a block behind it: then the entry
has another decision, and `Alike` fails. A plain law (`Reduction.Leads`) speaks of the transcripts
at which the piece puts out: so it asks less: that q says yes only where p does.
  `leads_oneway`: q.base = p.base · q.ds = p.ds · q.err is p.err · WHEREVER q's RUN RETURNS s', p's
    RUN ON THE SAME RECORD AND VIEW RETURNS SOME s'' WITH R s s'' s' (R: a letter: what lies between
    p's record behind and q's) · p leads from on to Q ⇒ q leads from on to
    "there is s'' with Q a (s'', b's oracles) and R a.1 s'' b.1". The pieces' extractors, types of
    claims and rounds put back may part.
  `leads_guarded`: at R := "they are one": q's yes is p's yes with the same record behind: the very
    Q goes over.
  `run_one`: what a yes of one block's run is · `run_of_step`: THE RULE's PREMISE FROM THE BLOCKS'
    STEPS: as many rounds declared, the same rounds put back, and: wherever q's block's `Block.step`
    says yes, p's says yes on the same rounds and columns, takes as many columns, and R holds.
THE RIDER. The rule hands a law to q only from a p that says yes wherever q does. q := no to all:
every law holds of it for nothing, with or without the rule. q := yes to all: the premise forces p
to say yes to all too: and such a p has no law with a conclusion that can fail
(GameHeldChecks.lean): `oneway_yesAll`: the premise at a q that always returns makes p always
return.
Limits. A rule on pieces; no seat is shown to meet its premise. Nothing on soundness.

-/
import Johnson.Desc.K12.Coin.Alike

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes.Maker
open Iop _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain

variable {S Cl Cl' W W' : Type} {C : PQ.CK} {F : Frame}

/-- **One way.** -/
theorem leads_oneway (p : Piece C F S Cl W) (q : Piece C F S Cl' W') (h1 : q.base = p.base)
    (h2 : q.ds = p.ds) (h4 : HEq q.err p.err) (R : S → S → S → Prop)
    (hrun : ∀ s v s', q.run s v = some s' → ∃ s'', p.run s v = some s'' ∧ R s s'' s')
    (on : S × F.E.Str → Prop) (Q : S × F.E.Str → S × F.E.Str → Prop)
    (h : p.ior.red.Leads on Q p.err) :
    q.ior.red.Leads on (fun a b => ∃ s'', Q a (s'', b.2) ∧ R a.1 s'' b.1) q.err := by
  obtain ⟨pb, pbase, pds, pback, pext, perr⟩ := p
  obtain ⟨qb, qbase, qds, qback, qext, qerr⟩ := q
  dsimp only at h1 h2 h4
  subst h1 h2
  obtain rfl := eq_of_heq h4
  intro a ha
  refine Doomed.mono _ _ ?_ (h a ha)
  intro τ hτ b hout
  have hout' : ((if sTests C ⟨F.a, qbase, F.all, qds, F.key, F.all⟩ a.2 τ then
      (⟨qb, qbase, qds, qback, qext, qerr⟩ : Piece C F S Cl' W').run a.1
        (sView C ⟨F.a, qbase, F.all, qds, F.key, F.all⟩ a.2 τ) else none).map
      fun xo => (xo, (⟨qb, qbase, qds, qback, qext, qerr⟩ : Piece C F S Cl' W').ior.imp a.2 τ)) =
      some b := hout
  obtain ⟨xo, hx, rfl⟩ := Option.map_eq_some_iff.1 hout'
  by_cases ht : sTests C ⟨F.a, qbase, F.all, qds, F.key, F.all⟩ a.2 τ = true
  · rw [if_pos ht] at hx
    obtain ⟨s'', hs, hR⟩ := hrun _ _ _ hx
    refine ⟨s'', hτ _ ?_, hR⟩
    show ((if sTests C ⟨F.a, qbase, F.all, qds, F.key, F.all⟩ a.2 τ then
      (⟨pb, qbase, qds, pback, pext, qerr⟩ : Piece C F S Cl W).run a.1
        (sView C ⟨F.a, qbase, F.all, qds, F.key, F.all⟩ a.2 τ) else none).map
      fun xo => (xo, (⟨pb, qbase, qds, pback, pext, qerr⟩ : Piece C F S Cl W).ior.imp a.2 τ)) = _
    rw [if_pos ht, hs]
    rfl
  · rw [if_neg ht] at hx
    cases hx

/-- Where q's yes is p's yes with the same record behind, the very conclusion goes over. -/
theorem leads_guarded (p : Piece C F S Cl W) (q : Piece C F S Cl' W') (h1 : q.base = p.base)
    (h2 : q.ds = p.ds) (h4 : HEq q.err p.err)
    (hrun : ∀ s v s', q.run s v = some s' → p.run s v = some s')
    (on : S × F.E.Str → Prop) (Q : S × F.E.Str → S × F.E.Str → Prop)
    (h : p.ior.red.Leads on Q p.err) : q.ior.red.Leads on Q q.err := by
  have h' := leads_oneway p q h1 h2 h4 (fun _ s'' s' => s'' = s')
    (fun s v s' hq => ⟨s', hrun s v s' hq, rfl⟩) on Q h
  intro a ha
  refine Doomed.mono _ _ ?_ (h' a ha)
  intro τ hτ b hb
  obtain ⟨s'', hQ, rfl⟩ := hτ b hb
  exact hQ

/-- What a yes of one block's run is: the stretch has just the block's rounds; `Block.step` says yes
on them; no column is left. -/
theorem run_one (b : Block S Cl) (name : String) (back : List Fmt.RoundView) (s : S) (v : Fmt.View)
    (s' : S) : foldRun F name [b] back s v = some s' ↔
      ∃ k, (v.rounds ++ back).length = b.rounds.length ∧
        b.step F.ft s (v.rounds ++ back) v.opened = .ok (s', k) ∧ v.opened.drop k = [] := by
  simp only [foldRun, chainAt, foldBlocks, List.isEmpty_cons, List.splitAt_eq]
  constructor
  · intro h
    split at h
    · cases h
    · split at h
      · rename_i s₁ hf
        split at hf
        · cases hf
        · rename_i hl
          split at hf
          · cases hf
          · rename_i s₂ k hs
            have e := Except.ok.inj hf
            have e1 : s₂ = s₁ := congrArg (·.1) e
            have e2 : (v.rounds ++ back).drop b.rounds.length = [] := congrArg (·.2.1) e
            have e3 : v.opened.drop k = [] := congrArg (·.2.2) e
            have hlen : (v.rounds ++ back).length = b.rounds.length := by
              have a1 := List.drop_eq_nil_iff.1 e2
              have a2 : ((v.rounds ++ back).take b.rounds.length).length = b.rounds.length := by
                simpa using hl
              rw [List.length_take] at a2
              omega
            have ht : (v.rounds ++ back).take b.rounds.length = v.rounds ++ back :=
              List.take_of_length_le (by omega)
            rw [ht] at hs
            have e4 : s₁ = s' := Option.some.inj h
            exact ⟨k, hlen, by rw [hs, e1, e4], e3⟩
      · cases h
      · cases h
  · rintro ⟨k, hlen, hs, hc⟩
    have ht : (v.rounds ++ back).take b.rounds.length = v.rounds ++ back :=
      List.take_of_length_le (by omega)
    have hd : (v.rounds ++ back).drop b.rounds.length = [] :=
      List.drop_eq_nil_iff.2 (by omega)
    simp [ht, hd, hlen, hs, hc, Except.toOption]

/-- **The rule's premise from the blocks' steps**: as many rounds declared; the same rounds put
back; wherever q's block's step says yes, p's says yes on the same rounds and columns, takes as many
columns, and R holds. -/
theorem run_of_step (p : Piece C F S Cl W) (q : Piece C F S Cl' W') (R : S → S → S → Prop)
    (hr : q.b.rounds.length = p.b.rounds.length) (hb : q.back = p.back)
    (hstep : ∀ s rs cols s' k, q.b.step F.ft s rs cols = .ok (s', k) →
      ∃ s'', p.b.step F.ft s rs cols = .ok (s'', k) ∧ R s s'' s') :
    ∀ s v s', q.run s v = some s' → ∃ s'', p.run s v = some s'' ∧ R s s'' s' := by
  intro s v s' h
  obtain ⟨k, hlen, hs, hc⟩ := (run_one q.b q.b.name q.back s v s').1 h
  obtain ⟨s'', hp, hR⟩ := hstep _ _ _ _ _ hs
  refine ⟨s'', (run_one p.b p.b.name p.back s v s'').2 ⟨k, ?_, ?_, hc⟩, hR⟩
  · rw [← hb, hlen, hr]
  · rw [← hb]
    exact hp

/-- The rider: the premise at a q that always returns makes p always return. -/
theorem oneway_yesAll (p : Piece C F S Cl W) (q : Piece C F S Cl' W') (R : S → S → S → Prop)
    (hrun : ∀ s v s', q.run s v = some s' → ∃ s'', p.run s v = some s'' ∧ R s s'' s')
    (hq : ∀ s v, (q.run s v).isSome = true) : ∀ s v, (p.run s v).isSome = true := by
  intro s v
  obtain ⟨s', hs⟩ := Option.isSome_iff_exists.1 (hq s v)
  obtain ⟨s'', h, _⟩ := hrun s v s' hs
  rw [h]
  rfl

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.leads_oneway
#print axioms VerifiableInference.Desc.K12.Coin.leads_guarded
#print axioms VerifiableInference.Desc.K12.Coin.run_one
#print axioms VerifiableInference.Desc.K12.Coin.run_of_step
#print axioms VerifiableInference.Desc.K12.Coin.oneway_yesAll
