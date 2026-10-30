-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/GameHeldChecks.lean: **THE GAME's FORM AT THE PIECE THAT A DESCRIPTION HOLDS,
TRIED AGAINST THE TWO SILLY VERIFIERS.** Definitions, statements and proofs.

GameHeld.lean and GameAlike.lean state the game over the pair of the instance's public part and a
chain's state, behind two doors. The trial against the verifier that says yes to all and the one
that says no to all stood at the record's own forms alone (GameChecks.lean, GameZChecks.lean).
  `GameAtHeld` | `GameAtHeldO`: the form, as a sentence on ANY piece over P × S, at any type of
    claims. `k12_has_held` | `k12_has_heldO`: `k12_game_alike` | `k12_game_alikeO` say just this.
  `yesAll_not_held`: first arm: a piece with small errors that puts out at every transcript from a
    statement whose door in gives a record WITHOUT THE GROUP has not the form.
  `yesAll_not_heldO`: second arm: the like at a statement whose door in gives tOx (ChecksAtO.lean):
    a record WITH the group, at which the promise holds and "one tuple for all rows" is false.
  `yesAll_moves`: a third tooth, of this form alone: a piece that puts out with the public part
    turned has not the form.
  `noAll_has_held` | `noAll_has_heldO`: **A PIECE THAT NEVER PUTS OUT HAS THE FORM.**
Limits. Nothing on soundness. That the form is not idle at the true block (it puts out somewhere
inside the promise) is not shown: `K12GameLiveO` (GameChecks.lean) is stated, not proved.

-/
import Johnson.Desc.K12.Coin.GameAlike
import Johnson.Desc.K12.Coin.GameZChecks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.Member (piO)
open H2K.Pin (NTuple)
open H2K.Pub (PayPub johOk batV0)
open H2K.First (batOneOk)

section
variable {P S Cl' W : Type} (enter : S → Except String T12) (leave : S → T12 → Except String S)
  (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ)
  (base : ℕ) (p : Piece (ckP .two) F (P × S) Cl' W)

/-- What a yes must give, at the held seat. -/
def HeldQ (a b : (P × S) × F.E.Str) : Prop :=
  (∃ t t', enter a.1.2 = .ok t ∧ leave a.1.2 t' = .ok b.1.2 ∧
    QN π (NTuple F π no rad rd) (t, a.2)) ∧ b.1 = (a.1.1, b.1.2)

/-- **The form, first arm.** -/
def GameAtHeld : Prop :=
  p.ior.red.Leads (fun a => ∀ t, enter a.1.2 = .ok t → FirstOpens π num no base t)
    (HeldQ enter leave F π no rad rd) p.err

/-- **The form, second arm.** -/
def GameAtHeldO : Prop :=
  p.ior.red.Leads (fun a => ∀ t, enter a.1.2 = .ok t → FirstOpensOwn π num no base t)
    (HeldQ enter leave F π no rad rd) p.err

/-- **Yes to all, first arm.** -/
theorem yesAll_not_held (dB : RDT) (x : (P × S) × F.E.Str) (t : T12) (ht : enter x.1.2 = .ok t)
    (hg : t.st.groups[t.g]? = none) (hyes : ∀ τ, ∃ b, p.ior.red.out x τ = some b)
    (hs : Small p.err) : ¬ GameAtHeld enter leave F π num no rad rd base p := by
  intro h
  refine not_doomed_false _ _ hs (Doomed.mono _ _ (fun τ hτ => ?_) (h x fun t' ht' => ?_))
  · obtain ⟨b, hb⟩ := hyes τ
    obtain ⟨⟨t', _, e1, _, q⟩, _⟩ := hτ b hb
    obtain rfl : t = t' := Except.ok.inj (ht.symm.trans e1)
    exact qn_no_group π _ (t, x.2) hg q
  · obtain rfl : t = t' := Except.ok.inj (ht.symm.trans ht')
    exact (promN_no_group F π num no rad rd base dB 0 (NTuple F π no rad rd) (t, x.2) hg).1

/-- **A piece that turns the public part has not the form**, either arm's promise being met. -/
theorem yesAll_moves (on : (P × S) × F.E.Str → Prop) (x : (P × S) × F.E.Str) (hon : on x)
    (hyes : ∀ τ, ∃ b, p.ior.red.out x τ = some b ∧ b.1.1 ≠ x.1.1) (hs : Small p.err) :
    ¬ p.ior.red.Leads on (HeldQ enter leave F π no rad rd) p.err := by
  intro h
  refine not_doomed_false _ _ hs (Doomed.mono _ _ (fun τ hτ => ?_) (h x hon))
  obtain ⟨b, hb, hne⟩ := hyes τ
  have e : b.1 = (x.1.1, b.1.2) := (hτ b hb).2
  have e' : b.1.1 = (x.1.1, b.1.2).1 := congrArg Prod.fst e
  exact hne e'

/-- **No to all.** -/
theorem noAll_has_held (hno : ∀ a τ, p.ior.red.out a τ = none) :
    GameAtHeld enter leave F π num no rad rd base p :=
  fun a _ => Doomed.of_forall _ _ fun τ b hb => by rw [hno a τ] at hb; cases hb

theorem noAll_has_heldO (hno : ∀ a τ, p.ior.red.out a τ = none) :
    GameAtHeldO enter leave F π num no rad rd base p :=
  fun a _ => Doomed.of_forall _ _ fun τ b hb => by rw [hno a τ] at hb; cases hb

end

/-- **Yes to all, second arm**: at a statement whose door in gives tOx. -/
theorem yesAll_not_heldO {P S Cl' W : Type} (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (F : Frame) (t₁ t₂ : ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ)
    (p : Piece (ckP .two) F (P × S) Cl' W) (x : (P × S) × F.E.Str) (ht : enter x.1.2 = .ok tOx)
    (hyes : ∀ τ, ∃ b, p.ior.red.out x τ = some b) (hs : Small p.err) :
    ¬ GameAtHeldO enter leave F piO (numAt t₁ t₂ 1) (fun z => t₁ + z) rad rd (t₁ + 5) p := by
  intro h
  obtain ⟨a, rest, G0, Ly, D, hF⟩ := fixes_Ox
  refine not_doomed_false _ _ hs (Doomed.mono _ _ (fun τ hτ => ?_) (h x fun t' ht' => ?_))
  · obtain ⟨b, hb⟩ := hyes τ
    obtain ⟨⟨t', _, e1, _, q⟩, _⟩ := hτ b hb
    obtain rfl : tOx = t' := Except.ok.inj (ht.symm.trans e1)
    exact not_ntuple_Ox F _ rad rd x.2 hF ((qn_iff piO _ (tOx, x.2) hF).1 q)
  · obtain rfl : tOx = t' := Except.ok.inj (ht.symm.trans ht')
    exact (promise_Ox t₁ t₂).2.1

/-- The law says just the form, first arm. -/
theorem k12_has_held (P S Cl' : Type) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ)
    (no : ℕ → ℕ) (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT)
    (dt : List RDT) (e : ℕ) (εt : Err (uLT (ckP .two) dt)) (r : Fmt.M1.Stage → ℕ)
    (p : Piece (ckP .two) F (P × S) Cl' W)
    (hb : Alike (held (P := P) ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave)) p.b)
    (h0 : p.back = []) (hbase : p.base = base) (hds : p.ds = dB :: dt)
    (herr : HEq p.err ((e, εt) : Err (uLT (ckP .two) (dB :: dt))))
    (hA : AtPlace F π num L mC mS mW rad base dB dt εt)
    (hr : ∀ s, rad s = r s.st) (hj : johOk π r = true) (hb1 : batOneOk π = true)
    (hle : batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e) :
    GameAtHeld enter leave F π num no rad rd base p :=
  k12_game_alike P S Cl' enter leave F W π num no L mC mS mW rad rd base dB dt e εt r p hb h0
    hbase hds herr hA hr hj hb1 hle

/-- The law says just the form, second arm. -/
theorem k12_has_heldO (P S Cl' : Type) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ)
    (no : ℕ → ℕ) (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT)
    (dt : List RDT) (e v₀ : ℕ) (εt : Err (uLT (ckP .two) dt))
    (p : Piece (ckP .two) F (P × S) Cl' W)
    (hb : Alike (held (P := P) ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave)) p.b)
    (h0 : p.back = []) (hbase : p.base = base) (hds : p.ds = dB :: dt)
    (herr : HEq p.err ((e, εt) : Err (uLT (ckP .two) (dB :: dt))))
    (hA : AtPlaceOwn F π num L mC mS mW rad base dB dt εt)
    (hP : PayPub π rad dB.entry.rows v₀) (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0])
    (hlog : dB.entry.logN ≤ 64) (hle : v₀ * (bsRound .two dB.entry dB.kind).w ≤ e) :
    GameAtHeldO enter leave F π num no rad rd base p :=
  k12_game_alikeO P S Cl' enter leave F W π num no L mC mS mW rad rd base dB dt e v₀ εt p hb h0
    hbase hds herr hA hP h1 hlog hle

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.yesAll_not_held
#print axioms VerifiableInference.Desc.K12.Coin.yesAll_not_heldO
#print axioms VerifiableInference.Desc.K12.Coin.yesAll_moves
#print axioms VerifiableInference.Desc.K12.Coin.noAll_has_held
#print axioms VerifiableInference.Desc.K12.Coin.noAll_has_heldO
#print axioms VerifiableInference.Desc.K12.Coin.k12_has_held
#print axioms VerifiableInference.Desc.K12.Coin.k12_has_heldO
