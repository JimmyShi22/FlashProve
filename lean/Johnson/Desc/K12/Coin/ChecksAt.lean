-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/ChecksAt.lean: THE FORMS OF THE PROXIMITY TEST's LAWS AGAINST THE VERIFIER
THAT SAYS YES TO ALL, AT A STATEMENT WITH A GROUP. Statements and proofs.

The other checks (SheetChecks, ChecksN, ChecksY, ChecksPaid, and those in SeatF2, PaidRec, FreeOff)
stand at a statement without a group: there every promise behind "what the record fixes" is idle and
the conclusion fails whatever N: so they read neither N nor a clause of a promise. Here:

  `fixes_one`: a record fixes at most one (stage, later stages, group, layout, plain data).
  `qn_iff`: where the record fixes these, the conclusion `QN π N x` IS N of them.
  `yesAll_failsAt`: **whatever the promise `on` and whatever N**: at ANY statement x that meets the
    promise, whose record fixes its data, and AT WHICH N FAILS OF THEM, a piece that puts out at
    every transcript from x, at errors below its rounds' numbers of challenges, has not the form
    "Leads on (QN π N)". So the form bites wherever the promise can be met while N is false.
  `yesAll_failsRecAt`: that at PaidRec.lean's first arm's promise and N := `NTuple`.
Limits. THAT SUCH A STATEMENT EXISTS (the promise met, the record fixing its data, `NTuple` false)
IS A PREMISE HERE, SHOWN OF NO RECORD: it wants a record with a group, built or run. Nothing on
soundness.
-/
import Johnson.Desc.K12.Coin.PaidRec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open H2K.First (Plain)
open H2K.Pin (NTuple PayRec)

/-- A record fixes at most one. -/
theorem fixes_one (π : P12) (t : T12) {a a' : Fmt.M1.Stage} {rest rest' : List Fmt.M1.Stage}
    {G0 G0' : Group} {Ly Ly' : GroupLayout} {D D' : Plain} (h : Fixes π t a rest G0 Ly D)
    (h' : Fixes π t a' rest' G0' Ly' D') :
    a = a' ∧ rest = rest' ∧ G0 = G0' ∧ Ly = Ly' ∧ D = D' := by
  obtain ⟨rfl, rfl⟩ := List.cons.inj (h.1.symm.trans h'.1)
  obtain rfl := Option.some.inj (h.2.1.symm.trans h'.2.1)
  obtain rfl := Option.some.inj (h.2.2.1.symm.trans h'.2.2.1)
  exact ⟨rfl, rfl, rfl, rfl, Option.some.inj ((h.2.2.2 default).symm.trans (h'.2.2.2 default))⟩

/-- Where the record fixes its data, the conclusion is N of them. -/
theorem qn_iff {F : Frame} (π : P12) (N : ConclK F) (x : T12 × F.E.Str) {a : Fmt.M1.Stage}
    {rest : List Fmt.M1.Stage} {G0 : Group} {Ly : GroupLayout} {D : Plain}
    (h : Fixes π x.1 a rest G0 Ly D) : QN π N x ↔ N x a rest G0 Ly D := by
  constructor
  · rintro ⟨a', rest', G0', Ly', D', h', hN⟩
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := fixes_one π x.1 h h'
    exact hN
  · exact fun hN => ⟨a, rest, G0, Ly, D, h, hN⟩

/-- **The form bites wherever the promise can be met while N is false.** -/
theorem yesAll_failsAt {W : Type} (F : Frame) (π : P12) (N : ConclK F)
    (on : T12 × F.E.Str → Prop) (p : Piece (ckP .two) F T12 Unit W) (x : T12 × F.E.Str)
    (hon : on x) {a : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {G0 : Group} {Ly : GroupLayout}
    {D : Plain} (hF : Fixes π x.1 a rest G0 Ly D) (hN : ¬ N x a rest G0 Ly D)
    (hyes : ∀ τ, ∃ b, p.ior.red.out x τ = some b) (hs : Small p.err) :
    ¬ p.ior.red.Leads on (fun x _ => QN π N x) p.err := by
  intro h
  refine not_doomed_false _ _ hs (Doomed.mono _ _ (fun τ hτ => ?_) (h x hon))
  obtain ⟨b, hb'⟩ := hyes τ
  exact hN ((qn_iff π N x hF).1 (hτ b hb'))

theorem yesAll_failsRecAt {W : Type} (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (p : Piece (ckP .two) F T12 Unit W)
    (x : T12 × F.E.Str) (h1 : FirstOpens π num no base x.1) (h2 : PayRec π x.1)
    {a : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {G0 : Group} {Ly : GroupLayout} {D : Plain}
    (hF : Fixes π x.1 a rest G0 Ly D) (hN : ¬ NTuple F π no rad rd x a rest G0 Ly D)
    (hyes : ∀ τ, ∃ b, p.ior.red.out x τ = some b) (hs : Small p.err) :
    ¬ p.ior.red.Leads (fun x => FirstOpens π num no base x.1 ∧ PayRec π x.1)
      (fun x _ => QN π (NTuple F π no rad rd) x) p.err :=
  yesAll_failsAt F π _ _ p x ⟨h1, h2⟩ hF hN hyes hs

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.fixes_one
#print axioms VerifiableInference.Desc.K12.Coin.qn_iff
#print axioms VerifiableInference.Desc.K12.Coin.yesAll_failsAt
#print axioms VerifiableInference.Desc.K12.Coin.yesAll_failsRecAt
