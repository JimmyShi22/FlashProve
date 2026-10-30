-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/Keyed.lean: the plain form WITH A KEY: one "the prover has lost" for ALL the
statements that have one key; and by it the shared chain of a proof file PAID ONCE for a batch.

`K.LeadsK key on Q ε`: for every value k of the key the prover has lost, at the start, at the errors
ε, towards: "for EVERY statement a with key a = k and `on a`: whatever the verifier puts out at a
stands in Q to a". The statements are quantified INSIDE the game: so the challenges that are bad are
a function of the key alone. At key := id it is `Leads` (`leadsK_id`).

What it is for. In a batch the slots' statements in front of the shared chain differ (each carries
its own request's claims) and have one acting part: the shared chain's own record, the stored table.
Under shared verifier messages, where only the shared part speaks, all slots see one transcript. The
library's clause for a batch (`KnowJ`, CompileK/Joined/ExtractKnow.lean) is had AT THE ERRORS ONCE
from a game that is a function of a key (`knowJ_lost`): `LeadsK.toLinkJ` is that door.

  `LeadsK.seq`: two in a row: the key behind the first is a function of the key in front and of the
    transcript.
  `PlainFile.Leads3K`, `PlainFile.knowsJ`: the library's `Links.KnowsJ`, record by record.
  `proofSound_plainJ`: the proof file's hypothesis of the top, in `proofSound_at_links`' own words:
    NO FACTOR maxBatchSize stands at the shared chain's list (`worstMid`).

Limits. Those of Leads.lean and Doors.lean. A BLOCK OF THE SHARED CHAIN WHOSE BAD CHALLENGES HANG ON
WHAT A SLOT CARRIES (not on the key) HAS NOT THIS FORM: it pays once for each slot: no rule for the
sum of the two is here. THAT THE SLOTS OF A BATCH HAVE ONE KEY is `key₁`: what the first chain hands
on has a key that is a function of the record and the external word alone: a premise: at a
description it says that the shared chain's first record reads nothing of a request.

Nearest kin in the library. `knowJ_lost` (CompileK/Joined/ExtractKnow.lean), which `LeadsK.toLinkJ`
calls.


-/
import Johnson.Desc.Plain.Doors
import OnBytes.TypedOracleCompiler.Joined.MidLinks
import OnBytes.TypedOracleCompiler.Joined.LinkJKit

set_option autoImplicit false

namespace Iop
namespace Reduction
variable {A B C κ κ₂ κ₃ : Type}

/-- One game for all the statements with one key. -/
def LeadsK (K : Reduction A B) (key : A → κ) (on : A → Prop) (Q : A → B → Prop)
    (ε : Err K.shape) : Prop :=
  ∀ k, Doomed K.shape ε (fun τ => ∀ a, key a = k → on a → ∀ b, K.out a τ = some b → Q a b)

section Rules
variable {K : Reduction A B} {key : A → κ} {on on' : A → Prop} {Q Q' : A → B → Prop}
  {ε ε' : Err K.shape}

/-- It gives the form without a key. -/
theorem LeadsK.leads (h : K.LeadsK key on Q ε) : K.Leads on Q ε := fun a ha =>
  Doomed.mono _ _ (fun _ hτ b hb => hτ a rfl ha b hb) (h (key a))

/-- At the key "the statement itself" the two forms are one. -/
theorem leadsK_id : K.LeadsK id on Q ε ↔ K.Leads on Q ε :=
  ⟨LeadsK.leads, fun h k => by
    by_cases hk : on k
    · exact Doomed.mono _ _ (fun _ hτ a ha _ b hb => by
        obtain rfl : a = k := ha
        exact hτ b hb) (h k hk)
    · exact Doomed.of_forall _ _ fun _ a ha ho => by
        obtain rfl : a = k := ha
        exact absurd ho hk⟩

/-- A key that tells more: a weaker clause. -/
theorem LeadsK.finer (h : K.LeadsK key on Q ε) (key' : A → κ₂) (f : κ₂ → κ)
    (hf : ∀ a, key a = f (key' a)) : K.LeadsK key' on Q ε := fun k =>
  Doomed.mono _ _ (fun _ hτ a ha => hτ a (by rw [hf, ha])) (h (f k))

theorem LeadsK.conseq (h : K.LeadsK key on Q ε) (ho : ∀ a, on' a → on a)
    (hQ : ∀ a τ b, on' a → K.out a τ = some b → Q a b → Q' a b) : K.LeadsK key on' Q' ε :=
  fun k => Doomed.mono _ _
    (fun τ hτ a hk ha b hb => hQ a τ b ha hb (hτ a hk (ho a ha) b hb)) (h k)

theorem LeadsK.mono_err (h : K.LeadsK key on Q ε) (hε : Err.le ε ε') : K.LeadsK key on Q ε' :=
  fun k => Doomed.mono_err _ hε (h k)

theorem LeadsK.of_sure (key : A → κ) (ε : Err K.shape)
    (h : ∀ a τ b, on a → K.out a τ = some b → Q a b) : K.LeadsK key on Q ε :=
  fun _ => Doomed.of_forall _ _ fun τ a _ ha b hb => h a τ b ha hb

end Rules

/-- **Two in a row, with keys.** g: the key behind the first, from the key in front of it and its
transcript. -/
theorem LeadsK.seq {K₁ : Reduction A B} {K₂ : Reduction B C} {key₁ : A → κ} {key₂ : B → κ₂}
    {on₁ : A → Prop} {on₂ : B → Prop} {Q₁ : A → B → Prop} {Q₂ : B → C → Prop}
    {ε₁ : Err K₁.shape} {ε₂ : Err K₂.shape} (h₁ : K₁.LeadsK key₁ on₁ Q₁ ε₁)
    (h₂ : K₂.LeadsK key₂ on₂ Q₂ ε₂) (hon : ∀ a b, on₁ a → Q₁ a b → on₂ b)
    (g : κ → Tr K₁.shape → κ₂) (law : ∀ a τ b, K₁.out a τ = some b → key₂ b = g (key₁ a) τ) :
    (K₁.seq K₂).LeadsK key₁ on₁ (fun a c => ∃ b, Q₁ a b ∧ Q₂ b c) (Err.app ε₁ ε₂) := by
  intro k
  refine Doomed.append K₁.shape K₂.shape ε₁ ε₂ _ (Doomed.mono _ _ ?_ (h₁ k))
  intro τ₁ hτ₁
  refine Doomed.mono _ _ ?_ (h₂ (g k τ₁))
  intro τ₂ hτ₂ a hk ha c hc
  rw [seq_out_app] at hc
  obtain ⟨b, hb, hbc⟩ := Option.bind_eq_some_iff.1 hc
  have hq := hτ₁ a hk ha b hb
  exact ⟨b, hq, hτ₂ b (by rw [law a τ₁ b hb, hk]) (hon a b ha hq) c hbc⟩

end Reduction
end Iop

namespace TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)
open _root_.CompileK.Joined (KnowJ knowJ_lost allKind_const)
open scoped ENNReal

/-- **The door: the errors once.** Under shared verifier messages, where only the shared part
speaks. -/
theorem LeadsK.toLinkJ {A B κ κ₂ WA WB : Type} {K : Reduction A B} {key : A → κ} {on : A → Prop}
    {Q : A → B → Prop} {ε : Err K.shape} (h : K.LeadsK key on Q ε) (N : ℕ) {key₂ : B → κ₂}
    {RA : A → WA → Prop} {RB : B → WB → Prop} (ext : A → Tr K.shape → WB → WA)
    (hf : ∀ a τ b w, K.out a τ = some b → (on a → Q a b) → RB b w → RA a (ext a τ w))
    (g : κ → Tr K.shape → κ₂) (law : ∀ a τ b, K.out a τ = some b → key₂ b = g (key a) τ) :
    LinkJ K (RoundSplits.const (RAnn.ofShared .sh) K.shape) N key key₂ (fun _ => True) RA RB ext ε :=
  ⟨knowJ_lost K N key
      (fun k τ => ∀ a, key a = k → on a → ∀ b, K.out a τ = some b → Q a b)
      (fun a _ => h (key a))
      (fun a τ b w _ hl hb hw => hf a τ b w hb (fun ha => hl a rfl ha b hb) hw),
    adm_of_tr g law⟩

namespace PlainFile
variable {G : Chains} {Y : Type} {E : ExtSpec} (P : PlainFile G (Y × E.Str)) {κ₁ κ₂ : Type}

/-- **The three premises, the shared chain's with a key.** -/
structure Leads3K (k₁ : P.A₁ → κ₁) : Prop where
  l₁ : P.K₁.Leads P.on₀ (fun a b => P.on₁ b ∧ (P.L₁ b → P.M a b)) P.ε₁
  l₂ : P.K₂.LeadsK k₁ P.on₁ (fun b c => P.on₂ c ∧ (P.L₂ c → P.L₁ b)) P.ε₂
  l₃ : P.K₃.Leads P.on₂ (fun c _ => P.L₂ c) P.ε₃

theorem Leads3K.leads3 {k₁ : P.A₁ → κ₁} (h : P.Leads3K k₁) : P.Leads3 := ⟨h.l₁, h.l₂.leads, h.l₃⟩

/-- **The library's list with keys**, with the instance read through f (so: record by record). -/
theorem knowsJ {Y' : Type} (f : Y' → Y) (N : ℕ) {k₁ : P.A₁ → κ₁} {k₂ : P.A₂ → κ₂}
    (h : P.Leads3K k₁) (hJ : G.aJ = RAnn.ofShared .sh G.rJ)
    (F₁ : E.Str → κ₁)
    (key₁ : ∀ (a : Y' × E.Str) τ b, P.out₁ (f a.1, a.2) τ = some b → k₁ b = F₁ a.2)
    (g₂ : κ₁ → Tr G.c₂ → κ₂) (key₂ : ∀ b τ c, P.out₂ b τ = some c → k₂ c = g₂ (k₁ b) τ) :
    (P.links.comap f).KnowsJ N k₁ k₂ where
  l₁ := LinkJ.ofLocal (allKind_const (fun _ => rfl) G.c₁) N
    (fun a ha => (P.knows h.leads3).know₁ (f a.1, a.2) ha) F₁
    fun a τ b hb => key₁ a τ b hb
  l₂ := by
    have hA : G.A₂ = RoundSplits.const (RAnn.ofShared .sh) G.c₂ := by
      show (G.aJ, RoundSplits.const (RAnn.ofShared .sh) G.s₂) = _
      rw [hJ]
      rfl
    have := LeadsK.toLinkJ (K := P.K₂) h.l₂ N (key₂ := k₂)
      (RA := fun b (_ : Unit) => P.on₁ b → P.L₁ b) (RB := fun c (_ : Unit) => P.on₂ c → P.L₂ c)
      (fun _ _ _ => ()) (fun b _ c _ _ hq hw hb => (hq hb).2 (hw (hq hb).1)) g₂ key₂
    rw [← hA] at this
    exact this
  l₃ := LinkJ.ofLocal (allKind_const (fun _ => rfl) G.c₃) N (P.knows h.leads3).know₃
    (fun _ => ()) fun _ _ _ _ => rfl
  hands₁ := fun _ _ _ _ _ => trivial
  hands₂ := fun _ _ _ _ _ => trivial

end PlainFile

section At
variable {I X Wn : Type} (L : HolographicProtocol I X) {G : Chains}

/-- **The proof file's hypothesis of the top, from the plain form, the shared chain paid once.** -/
theorem proofSound_plainJ (D : Desc G (X × L.Rec) (oneExternalString L.wordLength L.Symbol)) (hB : L.onlineBatch = D.batch)
    (Rno : I → X → Wn → Prop) (w₀ : Wn) (P : PlainFile G ((X × L.Rec) × (oneExternalString L.wordLength L.Symbol).Str))
    {κ₁ κ₂ : Type} {k₁ : P.A₁ → κ₁} {k₂ : P.A₂ → κ₂}
    (hl : L.late = none) (h : P.Leads3K k₁) (hJ : G.aJ = RAnn.ofShared .sh G.rJ)
    (F₁ : L.Rec → (oneExternalString L.wordLength L.Symbol).Str → κ₁)
    (key₁ : ∀ x rec y τ b, P.out₁ ((x, rec), y) τ = some b → k₁ b = F₁ rec y)
    (g₂ : κ₁ → Tr G.c₂ → κ₂) (key₂ : ∀ b τ c, P.out₂ b τ = some c → k₂ c = g₂ (k₁ b) τ)
    (decides : ∀ x rec y (τ : Tr G.sh), D.accept (x, rec) y τ = true →
      (P.links.all.out ((L.early x, rec), y) τ).isSome = true)
    (ties : ∀ x rec y (τ : Tr G.sh) b, D.accept (x, rec) y τ = true →
      P.out₁ ((L.early x, rec), y) (Tr.fst (s := G.c₁) (t := G.c₂ ++ G.c₃) τ) = some b →
      (P.on₀ ((L.early x, rec), y) → P.M ((L.early x, rec), y) b) → L.relB Rno rec x y w₀)
    {εs : ℝ≥0∞} (worst : P.links.worstMid ≤ εs) :
    ∃ (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn)
      (ε : Err L.onlineBatch.loc.shape), Err.Below ε εs ∧
      ∀ rec, (L.batAt rec).SndBKT L.maxBatchSize L.early L.late (L.relB Rno rec)
        (fun x y τ => wit (x, rec) y τ) ε :=
  proofSound_at_links L D Rno (fun _ => w₀) hB hl
    (fun rec => P.knowsJ (fun x : X => (x, rec)) L.maxBatchSize h hJ (F₁ rec)
      (fun a τ b hb => key₁ a.1 rec a.2 τ b hb) g₂ key₂) decides
    (fun x rec y τ hacc hR => by
      obtain ⟨b, hb⟩ := P.first_of_all _ τ (decides x rec y τ hacc)
      refine ties x rec y τ b hacc hb fun ho => ?_
      have := hR ho
      rwa [P.ext_eq _ τ b hb] at this) worst

end At

end TypedOracleCompiler.Joined

#print axioms Iop.Reduction.LeadsK.seq
#print axioms Iop.Reduction.leadsK_id
#print axioms TypedOracleCompiler.Joined.LeadsK.toLinkJ
#print axioms TypedOracleCompiler.Joined.PlainFile.knowsJ
#print axioms TypedOracleCompiler.Joined.proofSound_plainJ
