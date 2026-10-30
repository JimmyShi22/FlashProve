-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/LeadsE.lean: FROM A BLOCK'S LAW WITH ITS EXTRACTOR TO THE PLAIN FORM, ONE WITNESS
CARRIED THROUGH THE CHAIN; and the token followed along the steps. Definitions and five theorems; no
probability of its own: each "has lost" is the premise's.

Why. The plain form of the rule of composition (Johnson/Desc/Plain/: `Leads`:
"whatever the verifier puts out stands in Q to the statement in front") takes one relation Q of a
block's two statements. `keeps_of_goodIn` goes from `Piece.GoodIn` to the plain
form at the languages "there is a witness": THE WITNESS IS THEN QUANTIFIED AFRESH AT EACH BORDER. At
a proof file's first border that says "for SOME token the model says it": nothing of the reply: the
top's tie from the first chain's yes to the request WITH ITS OWN REPLY cannot be met so. But Q may
be any relation of the two statements, and the table of joints' extractor is a function of these two
and the witness behind, of no transcript.

Main names:
  `leadsE_of_goodIn`: **`Piece.GoodIn`, and "where the block puts out b, its extractor's yield is E
    a b w", give `Leads` at Q a b := the promise behind ∧ every witness w behind gives the witness E
    a b w in front.** `leadsE_sure`: what holds for certain of the two statements may stand in Q
    too.
  `QE`, `EachE`, `eachLeadsE`: along a row: `EachGoodIn` and `EachE` give the plain form's
    `EachLeads`.
  `TokStep`: what is sure of a step, on the reply: where none is heard behind, the extractor leaves
    the token; where one is heard in this step, the extractor lays it; what was heard stays.
    `steps_stays`; **`steps_token`: along n + 1 steps every witness at the last statement gives a
    witness at the first; and if no reply is heard at the first statement and t at the last, that
    witness's token is t.**

Silly members. At rep := "nothing is ever heard" `steps_token`'s premise on the last statement
fails: it says nothing. At E := a constant the first clause of Q asks that constant to be a witness
in front. A block that never puts out meets `leadsE_of_goodIn`'s premise on E for nothing, as it
meets `GoodIn`.

Limits: rules. No block is shown to have `EachE` or `TokStep`: for the table's extractor they are
owed by its make; "what was heard of the reply stays" is a fact on each later block's text. It
stands on `Leads`, `EachLeads`, `steps` (Johnson/Desc/Plain/): compiled beside it, their statements read.
Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Plain.FoldChain
import Johnson.Desc.Sound.GoodIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)
open _root_.Iop.Reduction (steps)
open VerifiableInference.Desc.Plain

variable {S Cl W : Type} {C : CK} {F : Frame}

/-! ## 1 One block -/

/-- **From a block's law with its extractor to the plain form, THE WITNESS KEPT**: where the
extractor's yield is a function E of the two neighbouring statements and the witness behind. -/
theorem leadsE_of_goodIn (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop) (E : S × F.E.Str → S × F.E.Str → W → W)
    (hE : ∀ a τ b w, p.ior.red.out a τ = some b → p.ext a τ w = E a b w)
    (h : p.GoodIn on on' R R') :
    p.ior.red.Leads on (fun a b => on' b ∧ ∀ w, R' b w → R a (E a b w)) p.err := fun a ha =>
  Doomed.mono _ _ (fun τ hτ b hb =>
    ⟨(hτ b hb).1, fun w hw => hE a τ b w hb ▸ (hτ b hb).2 w hw⟩) (h a ha)

/-- What holds for certain of a block's two statements may stand in the relation too. -/
theorem leadsE_sure (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop) (E : S × F.E.Str → S × F.E.Str → W → W)
    (Sure : S × F.E.Str → S × F.E.Str → Prop)
    (hE : ∀ a τ b w, p.ior.red.out a τ = some b → p.ext a τ w = E a b w)
    (hS : ∀ a τ b, on a → p.ior.red.out a τ = some b → Sure a b)
    (h : p.GoodIn on on' R R') :
    p.ior.red.Leads on (fun a b => (on' b ∧ ∀ w, R' b w → R a (E a b w)) ∧ Sure a b) p.err :=
  fun a ha => Doomed.mono _ _ (fun τ hτ b hb =>
    ⟨⟨(hτ b hb).1, fun w hw => hE a τ b w hb ▸ (hτ b hb).2 w hw⟩, hS a τ b ha hb⟩) (h a ha)

/-! ## 2 Along a row -/

/-- The relation of block number i's two statements. -/
def QE (on : ℕ → S × F.E.Str → Prop) (R : ℕ → S × F.E.Str → W → Prop)
    (E : ℕ → S × F.E.Str → S × F.E.Str → W → W) (Sure : ℕ → S × F.E.Str → S × F.E.Str → Prop)
    (i : ℕ) (a b : S × F.E.Str) : Prop :=
  (on (i + 1) b ∧ ∀ w, R (i + 1) b w → R i a (E i a b w)) ∧ Sure i a b

/-- Each block's extractor is E; each block's sure facts hold. -/
def EachE (on : ℕ → S × F.E.Str → Prop) (E : ℕ → S × F.E.Str → S × F.E.Str → W → W)
    (Sure : ℕ → S × F.E.Str → S × F.E.Str → Prop) : ℕ → List (Piece C F S Cl W) → Prop
  | _, [] => True
  | i, p :: l =>
    (∀ a τ b w, p.ior.red.out a τ = some b → p.ext a τ w = E i a b w) ∧
      (∀ a τ b, on i a → p.ior.red.out a τ = some b → Sure i a b) ∧ EachE on E Sure (i + 1) l

theorem eachLeadsE (on : ℕ → S × F.E.Str → Prop) (R : ℕ → S × F.E.Str → W → Prop)
    (E : ℕ → S × F.E.Str → S × F.E.Str → W → W)
    (Sure : ℕ → S × F.E.Str → S × F.E.Str → Prop) :
    ∀ (l : List (Piece C F S Cl W)) (i : ℕ), EachGoodIn on R i l → EachE on E Sure i l →
      EachLeads on (QE on R E Sure) i l
  | [], _, _, _ => trivial
  | p :: l, i, h, e =>
    ⟨leadsE_sure p _ _ _ _ (E i) (Sure i) e.1 e.2.1 h.1, fun _ _ _ hq => hq.1.1,
      eachLeadsE on R E Sure l (i + 1) h.2 e.2.2⟩

/-! ## 3 The token along the steps -/

section Token
variable {A Tok : Type} (on : ℕ → A → Prop) (R : ℕ → A → W → Prop) (E : ℕ → A → A → W → W)
  (tok : W → Tok) (rep : A → Option Tok)

/-- What is sure of a step, on the reply. rep a: the reply that the record of a holds, if one was
heard. (keeps) where none is heard behind, the extractor leaves the witness's token; (lays) where
one is heard in this step, the extractor lays it as the token; (stays) what was heard stays. -/
structure TokStep (i : ℕ) (a b : A) : Prop where
  keeps : rep b = none → ∀ w, tok (E i a b w) = tok w
  lays : rep a = none → ∀ t, rep b = some t → ∀ w, tok (E i a b w) = t
  stays : ∀ t, rep a = some t → rep b = some t

/-- The steps' relation, at any type of statements. -/
def QT (i : ℕ) (a b : A) : Prop :=
  (on (i + 1) b ∧ ∀ w, R (i + 1) b w → R i a (E i a b w)) ∧ TokStep E tok rep i a b

theorem steps_stays : ∀ (n i : ℕ) (a c : A) (t : Tok), steps (QT on R E tok rep) i n a c →
    rep a = some t → rep c = some t
  | 0, _, _, _, t, h, e => h.2.stays t e
  | n + 1, i, _, c, t, ⟨_, hb, hc⟩, e => steps_stays n (i + 1) _ c t hc (hb.2.stays t e)

/-- **ONE WITNESS THROUGH THE CHAIN, AND ITS TOKEN**: along n + 1 steps, every witness at the last
statement gives a witness at the first; and if no reply is heard at the first statement and t is
heard at the last, that witness's token is t. -/
theorem steps_token : ∀ (n i : ℕ) (a c : A) (t : Tok), steps (QT on R E tok rep) i n a c →
    rep c = some t → ∀ w, R (i + 1 + n) c w → ∃ w₀, R i a w₀ ∧ (rep a = none → tok w₀ = t)
  | 0, i, a, c, t, h, e, w, hw => ⟨E i a c w, h.1.2 w hw, fun ha => h.2.lays ha t e w⟩
  | n + 1, i, a, c, t, ⟨b, hb, hc⟩, e, w, hw => by
    have e' : i + 1 + (n + 1) = i + 1 + 1 + n := by omega
    obtain ⟨w₁, h₁, ht⟩ := steps_token n (i + 1) b c t hc e w (e' ▸ hw)
    refine ⟨E i a b w₁, hb.1.2 w₁ h₁, fun ha => ?_⟩
    cases hr : rep b with
    | none => rw [hb.2.keeps hr w₁]; exact ht hr
    | some t' =>
      have : rep c = some t' := steps_stays on R E tok rep n (i + 1) b c t' hc hr
      have ett : t' = t := Option.some.inj (this.symm.trans e)
      rw [hb.2.lays ha t' hr w₁, ett]

end Token

end VerifiableInference.Desc.Sound
