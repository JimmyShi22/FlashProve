-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/Leads.lean: the rule of composition in the PLAIN form: no witness, no extractor.

One notion, `Reduction.Leads`, over the library's "the prover has lost" (`Doomed`, Iop/Rbr.lean),
and its rules, each with its proof. No protocol occurs here.

`K.Leads on Q ε`: on every statement a with `on a` the prover has lost, at the start, at the errors
ε, towards: "whenever the verifier puts out b, Q a b". Q is a relation between the statement in
front and the statement behind. What it is meant to hold, for a block of a chain:
    the promise behind is kept  ∧  (the statement behind is true → the statement in front is true)
    ∧  whatever holds of (a, b) for certain (what the block leaves unturned in the record).
Soundness (`Reduction.Sound`, Iop/Compose.lean) is the case on := "a is false", Q := "b is false",
by definition (`sound_iff_leads`).

Why a relation, and not two languages. (1) A promise must be kept at TRUE statements too, else a
claim that is only carried past the block can be lost with it: so "the promise behind" and "true
behind → true in front" stand under ONE "the prover has lost" (`Keeps`). (2) What the file's last
test compares (the token that was heard) is fixed in the middle of a chain, not at its start: two
relations in a row compose to "there is a statement between" (`Leads.seq`), so the conclusion for a
chain speaks of every boundary that the run went through, not of the first alone.

The doors. `Know.toLeads`: every reduction that the library has proved knowledge sound has the plain
form. `Leads.toKnow`, `Leads.toKnowOut`: the plain form gives the library's `Know` at an extractor
that is the verifier's own output read off the transcript: the form that `Links.Knows` |
`Links.KnowsJ` (OnBytes/TypedOracleCompiler/Joined/) ask of a file's chains.

Limits. Nothing on acceptance. Nothing bounds the errors. A condition that holds of nothing, a
relation that holds of all, a verifier that refuses all, an error that is a round's number of
challenges: each makes `Leads` true and empty. No witness is extracted: what is concluded is that a
statement is true.

Nearest kin in the library. `Reduction.Sound` and `Know` (`sound_iff_leads` and `Know.toLeads` say
how). `Leads.seq`: `Sound.seq` (Iop/Compose.lean) and `Know.seq` (Ior/Know.lean), both by
`Doomed.append` (Iop/Rbr.lean), as here. `conseq`, `mono_err`, `of_sure`: `Doomed.mono`,
`Doomed.mono_err` (Iop/Rbr.lean), `Doomed.of_forall` (Iop/Compose.lean). The notions are this file's
own; these tools are thin over the library's.


-/
import Ior.Know
import Ior.KnowColl

set_option autoImplicit false

namespace Iop
namespace Reduction
variable {A B C : Type}

/-- On the statements with `on` the prover has lost, at the start, towards "whatever the verifier
puts out stands in Q to the statement in front". -/
def Leads (K : Reduction A B) (on : A → Prop) (Q : A → B → Prop) (ε : Err K.shape) : Prop :=
  ∀ a, on a → Doomed K.shape ε (fun τ => ∀ b, K.out a τ = some b → Q a b)

/-- The form for a block with a promise: the promise behind is kept, at true and at false
statements, and a true statement behind gives a true statement in front: under one "has lost". -/
def Keeps (K : Reduction A B) (on : A → Prop) (on' : B → Prop) (L : A → Prop) (L' : B → Prop)
    (ε : Err K.shape) : Prop :=
  K.Leads on (fun a b => on' b ∧ (L' b → L a)) ε

section Rules
variable {K : Reduction A B} {on on' : A → Prop} {Q Q' : A → B → Prop} {ε ε' : Err K.shape}

/-- Soundness is the case "false in front, false behind": by definition. -/
theorem sound_iff_leads (LA : A → Prop) (LB : B → Prop) :
    K.Sound LA LB ε ↔ K.Leads (fun a => ¬ LA a) (fun _ b => ¬ LB b) ε := Iff.rfl

/-- Fewer statements; a larger relation, for which the condition, the verifier's own output and the
old relation may be used. So WHATEVER HOLDS FOR CERTAIN OF WHAT THE VERIFIER PUTS OUT MAY BE ADDED
TO Q AT NO COST: this is the frame rule. -/
theorem Leads.conseq (h : K.Leads on Q ε) (ho : ∀ a, on' a → on a)
    (hQ : ∀ a τ b, on' a → K.out a τ = some b → Q a b → Q' a b) : K.Leads on' Q' ε :=
  fun a ha => Doomed.mono _ _ (fun τ hτ b hb => hQ a τ b ha hb (hτ b hb)) (h a (ho a ha))

theorem Leads.mono_err (h : K.Leads on Q ε) (hε : Err.le ε ε') : K.Leads on Q ε' :=
  fun a ha => Doomed.mono_err _ hε (h a ha)

/-- What holds for certain costs nothing. -/
theorem Leads.of_sure (ε : Err K.shape) (h : ∀ a τ b, on a → K.out a τ = some b → Q a b) :
    K.Leads on Q ε :=
  fun a ha => Doomed.of_forall _ _ fun τ b hb => h a τ b ha hb

/-- A proof by cases on the statement in front: the larger error in each round. -/
theorem Leads.by_cases (P : A → Prop) (h : K.Leads (fun a => on a ∧ P a) Q ε)
    (h' : K.Leads (fun a => on a ∧ ¬ P a) Q ε') : K.Leads on Q (Err.max ε ε') := fun a ha => by
  by_cases hP : P a
  · exact Doomed.mono_err _ (Err.le_max_left ε ε') (h a ⟨ha, hP⟩)
  · exact Doomed.mono_err _ (Err.le_max_right ε ε') (h' a ⟨ha, hP⟩)

/-- Two relations at once: the errors add. -/
theorem Leads.and (h : K.Leads on Q ε) (h' : K.Leads on Q' ε') :
    K.Leads on (fun a b => Q a b ∧ Q' a b) (Err.add ε ε') := fun a ha =>
  Doomed.mono _ _ (fun _ hτ b hb => ⟨hτ.1 b hb, hτ.2 b hb⟩) (Doomed.and _ (h a ha) (h' a ha))

end Rules

/-- **Two in a row.** The relations compose: "there is a statement between"; the errors are
appended. The second's condition is owed of what stands in Q₁ to a statement with the first's: so a
promise that Q₁ holds is what the second may lean on. -/
theorem Leads.seq {K₁ : Reduction A B} {K₂ : Reduction B C} {on₁ : A → Prop} {on₂ : B → Prop}
    {Q₁ : A → B → Prop} {Q₂ : B → C → Prop} {ε₁ : Err K₁.shape} {ε₂ : Err K₂.shape}
    (h₁ : K₁.Leads on₁ Q₁ ε₁) (h₂ : K₂.Leads on₂ Q₂ ε₂) (hon : ∀ a b, on₁ a → Q₁ a b → on₂ b) :
    (K₁.seq K₂).Leads on₁ (fun a c => ∃ b, Q₁ a b ∧ Q₂ b c) (Err.app ε₁ ε₂) := by
  intro a ha
  refine Doomed.append K₁.shape K₂.shape ε₁ ε₂ _ (Doomed.mono _ _ ?_ (h₁ a ha))
  intro τ₁ hτ₁
  cases hout : K₁.out a τ₁ with
  | none =>
      refine Doomed.of_forall _ _ fun τ₂ c hc => ?_
      rw [seq_out_app, hout] at hc
      exact absurd hc (by simp)
  | some b =>
      refine Doomed.mono _ _ ?_ (h₂ b (hon a b ha (hτ₁ b hout)))
      intro τ₂ h c hc
      rw [seq_out_app, hout] at hc
      exact ⟨b, hτ₁ b hout, h c hc⟩

/-- Two blocks with promises in a row. -/
theorem Keeps.seq {K₁ : Reduction A B} {K₂ : Reduction B C} {on₁ : A → Prop} {on₂ : B → Prop}
    {on₃ : C → Prop} {L₁ : A → Prop} {L₂ : B → Prop} {L₃ : C → Prop} {ε₁ : Err K₁.shape}
    {ε₂ : Err K₂.shape} (h₁ : K₁.Keeps on₁ on₂ L₁ L₂ ε₁) (h₂ : K₂.Keeps on₂ on₃ L₂ L₃ ε₂) :
    (K₁.seq K₂).Keeps on₁ on₃ L₁ L₃ (Err.app ε₁ ε₂) :=
  (Leads.seq h₁ h₂ fun _ _ _ h => h.1).conseq (fun _ h => h)
    fun _ _ _ _ _ ⟨_, hb, hc⟩ => ⟨hc.1, fun h => hb.2 (hc.2 h)⟩

/-- **A claim that is only carried rides past a block with a promise, at the block's own errors.**
C in front, C' behind; the one premise holds for certain: where the verifier puts out b, C' b gives
C a (for it the promise behind and the block's own statement behind may be used). -/
theorem Keeps.beside {K : Reduction A B} {on : A → Prop} {on' : B → Prop} {L : A → Prop}
    {L' : B → Prop} {ε : Err K.shape} (h : K.Keeps on on' L L' ε) (Cl : A → Prop) (Cl' : B → Prop)
    (hc : ∀ a τ b, on a → K.out a τ = some b → on' b → L' b → Cl' b → Cl a) :
    K.Keeps on on' (fun a => L a ∧ Cl a) (fun b => L' b ∧ Cl' b) ε :=
  Leads.conseq h (fun _ h => h) fun a τ b ha hb hq =>
    ⟨hq.1, fun hl => ⟨hq.2 hl.1, hc a τ b ha hb hq.1 hl.1 hl.2⟩⟩

/-- `Keeps` is two soundness clauses at one list of errors: "outside the promise, or true", and "the
promise is kept". -/
theorem keeps_iff {K : Reduction A B} {on : A → Prop} {on' : B → Prop} {L : A → Prop}
    {L' : B → Prop} {ε : Err K.shape} :
    K.Keeps on on' L L' ε ↔
      K.Sound (fun a => ¬ on a ∨ L a) (fun b => ¬ on' b ∨ L' b) ε ∧
        K.Sound (fun a => ¬ on a) (fun b => ¬ on' b) ε := by
  constructor
  · intro h
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · have hon : on a := by_contra fun hn => ha (Or.inl hn)
      exact Doomed.mono _ _ (fun _ hτ b hb hor =>
        hor.elim (fun hn => hn (hτ b hb).1) fun hl => ha (Or.inr ((hτ b hb).2 hl))) (h a hon)
    · exact Doomed.mono _ _ (fun _ hτ b hb hn => hn (hτ b hb).1) (h a (not_not.mp ha))
  · rintro ⟨h₁, h₂⟩ a ha
    by_cases hL : L a
    · exact Doomed.mono _ _ (fun _ hτ b hb => ⟨not_not.mp (hτ b hb), fun _ => hL⟩)
        (h₂ a (not_not.mpr ha))
    · refine Doomed.mono _ _ (fun _ hτ b hb => ?_) (h₁ a fun hor => hor.elim (fun hn => hn ha) hL)
      have := hτ b hb
      rw [not_or, not_not] at this
      exact ⟨this.1, fun hl => absurd hl this.2⟩

/-! ## The doors to and from the library's knowledge form -/

section Doors
variable {K : Reduction A B} {on : A → Prop} {ε : Err K.shape} {WA WB : Type}

/-- Every reduction that is knowledge sound has the plain form, for the languages of its two
relations, at the same errors. -/
theorem Know.toLeads {RA : A → WA → Prop} {RB : B → WB → Prop} {ext : A → Tr K.shape → WB → WA}
    (h : K.Know on RA RB ext ε) :
    K.Leads on (fun a b => (∃ w, RB b w) → ∃ w, RA a w) ε := fun a ha =>
  Doomed.mono _ _ (fun τ hτ b hb ⟨w, hw⟩ => ⟨ext a τ w, hτ b w hb hw⟩) (h a ha)

/-- What the verifier puts out, read off the transcript and handed to f; d where it refuses. -/
def readOut (K : Reduction A B) (f : A → B → WB → WA) (d : WA) : A → Tr K.shape → WB → WA :=
  fun a τ w => (K.out a τ).elim d fun b => f a b w

/-- **The plain form gives the library's `Know`**, at the extractor that reads the verifier's own
output off the transcript. -/
theorem Leads.toKnow {Q : A → B → Prop} {RA : A → WA → Prop} {RB : B → WB → Prop}
    (h : K.Leads on Q ε) (f : A → B → WB → WA) (d : WA)
    (hf : ∀ a b w, on a → Q a b → RB b w → RA a (f a b w)) :
    K.Know on RA RB (K.readOut f d) ε := fun a ha =>
  Doomed.mono _ _ (fun τ hτ b w hb hw => by
    show RA a ((K.out a τ).elim d fun b => f a b w)
    rw [hb]
    exact hf a b w ha (hτ b hb) hw) (h a ha)

/-- The case that a file's first chain wants: the "witness" in front IS the statement that the chain
hands on; behind, no witness. M a b: what is known of a once the chain has put out b and b is
true. -/
theorem Leads.toKnowOut {LB : B → Prop} {M : A → B → Prop}
    (h : K.Leads on (fun a b => LB b → M a b) ε) (d : B) :
    K.Know on M (fun b (_ : Unit) => LB b) (K.readOut (fun _ b _ => b) d) ε :=
  h.toKnow _ d fun _ _ _ _ hq hw => hq hw

/-- The case without any witness. -/
theorem Leads.toKnowUnit {LA : A → Prop} {LB : B → Prop}
    (h : K.Leads on (fun a b => LB b → LA a) ε) :
    K.Know on (fun a (_ : Unit) => LA a) (fun b (_ : Unit) => LB b) (fun _ _ _ => ()) ε :=
  fun a ha => Doomed.mono _ _ (fun _ hτ b _ hb hw => hτ b hb hw) (h a ha)

end Doors

/-! ## Along a list -/

/-- n + 1 relations in a row, from the number i on. -/
def steps (Q : ℕ → A → A → Prop) : ℕ → ℕ → A → A → Prop
  | i, 0, a, c => Q i a c
  | i, n + 1, a, c => ∃ b, Q i a b ∧ steps Q (i + 1) n b c

end Reduction
end Iop

#print axioms Iop.Reduction.Leads.seq
#print axioms Iop.Reduction.Keeps.beside
#print axioms Iop.Reduction.keeps_iff
#print axioms Iop.Reduction.Leads.toKnow
#print axioms Iop.Reduction.Leads.toKnowOut
