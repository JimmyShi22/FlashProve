-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/Doors.lean: from the plain form for a file's three chains to the two hypotheses
of the top, IN THEIR OWN WORDS: the conclusions of `keySound_plain` and `proofSound_plain` are, to
the letter, those of the library's `keySound_at` and `proofSound_at`
(OnBytes/TypedOracleCompiler/Joined/TwoChains.lean), which are `CompilerSoundnessConditionStatements.keySound` and `CompilerSoundnessConditionStatements.proofSound`
(Johnson/Top/InnerCompiledVerifier.lean) at an interface L.

  `PlainFile G A`: three chains' decisions as functions to what they hand on; a condition in front
    of each; the statement L₁ | L₂ that is claimed between them; M a b: WHAT IS KNOWN OF THE FILE's
    STATEMENT a ONCE THE FIRST CHAIN HAS HANDED ON b AND b IS TRUE; three lists of errors.
  `PlainFile.Leads3`: the three premises, one a chain, each a `Reduction.Leads`. A promise at a
    border of two chains may be lost at the earlier chain's cost: it is not asked for certain.
  `PlainFile.links`, `PlainFile.knows`: the library's `Links` and `Links.Knows` at it. The one
    extractor with content is the first chain's own output, read off the transcript.

THE ASKED TOKEN, okStart, THE LAST TEST. `ties` in `proofSound_plain` is handed: the file's yes AT
THE INSTANCE x ITSELF; the statement b that the first chain handed on AT THE EARLY PART of x, on the
very transcript; and "on₀ → M": so whatever the file's decision tests of x itself (the test on the
instance; the last test, which compares what was heard with what is asked) can be spent there, and
`on₀` is paid from the file's yes, not owed at instances that the verifier refuses.

Limits. No witness is extracted: the witness map is constant (w₀). At the two sizes' frame a witness
has the type Unit. The index (the weights) is not extracted here or by any chain: it is `L.decodeIndex y
rec`, the decoder of the external word, inside `relB`. The shared chain's errors count maxBatchSize times
(`worst`): the road by keys (`Links.KnowsJ`) is not taken in this file.

Nearest kin in the library. `PlainFile`'s K₁ K₂ K₃ have the text of `TypedOracleCompiler.Joined.Links.K₁`,
`K₂`, `K₃` (OnBytes/TypedOracleCompiler/Joined/Top.lean) over another record. `keySound_plain` is a corollary of
`keySound_at`.


-/
import Johnson.Desc.Plain.Leads
import OnBytes.TypedOracleCompiler.Joined.TwoChains

set_option autoImplicit false

namespace TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)
open scoped ENNReal

/-- A file's three chains, in the plain form. -/
structure PlainFile (G : Chains) (A : Type) where
  A₁ : Type
  A₂ : Type
  out₁ : A → Tr G.c₁ → Option A₁
  out₂ : A₁ → Tr G.c₂ → Option A₂
  out₃ : A₂ → Tr G.c₃ → Option Unit
  on₀ : A → Prop
  on₁ : A₁ → Prop
  on₂ : A₂ → Prop
  /-- what is known of a once the first chain has handed on b and b is true -/
  M : A → A₁ → Prop
  L₁ : A₁ → Prop
  L₂ : A₂ → Prop
  ε₁ : Err G.c₁
  ε₂ : Err G.c₂
  ε₃ : Err G.c₃
  d : A₁

namespace PlainFile
variable {G : Chains} {A : Type} (P : PlainFile G A)

@[reducible] def K₁ : Reduction A P.A₁ := ⟨G.c₁, P.out₁⟩
@[reducible] def K₂ : Reduction P.A₁ P.A₂ := ⟨G.c₂, P.out₂⟩
@[reducible] def K₃ : Reduction P.A₂ Unit := ⟨G.c₃, P.out₃⟩

/-- **The three premises.** -/
structure Leads3 : Prop where
  l₁ : P.K₁.Leads P.on₀ (fun a b => P.on₁ b ∧ (P.L₁ b → P.M a b)) P.ε₁
  l₂ : P.K₂.Leads P.on₁ (fun b c => P.on₂ c ∧ (P.L₂ c → P.L₁ b)) P.ε₂
  l₃ : P.K₃.Leads P.on₂ (fun c _ => P.L₂ c) P.ε₃

/-- The library's list at it. Behind the first chain the conditions are "all", and a relation is
"inside the promise → true". -/
def links : Links G A where
  A₁ := P.A₁
  A₂ := P.A₂
  W₀ := P.A₁
  W₁ := Unit
  W₂ := Unit
  out₁ := P.out₁
  out₂ := P.out₂
  out₃ := P.out₃
  on₀ := P.on₀
  on₁ := fun _ => True
  on₂ := fun _ => True
  R₀ := P.M
  R₁ := fun b _ => P.on₁ b → P.L₁ b
  R₂ := fun c _ => P.on₂ c → P.L₂ c
  e₁ := P.K₁.readOut (fun _ b _ => b) P.d
  e₂ := fun _ _ _ => ()
  e₃ := fun _ _ _ => ()
  ε₁ := P.ε₁
  ε₂ := P.ε₂
  ε₃ := P.ε₃
  d₀ := P.d
  d₁ := ()

theorem knows (h : P.Leads3) : P.links.Knows where
  know₁ := h.l₁.toKnow (RB := fun b (_ : Unit) => P.on₁ b → P.L₁ b) _ P.d
    fun _ _ _ _ hq hw => hq.2 (hw hq.1)
  know₂ := fun b _ => by
    by_cases hb : P.on₁ b
    · exact Doomed.mono _ _ (fun _ hτ c _ hc hw _ => (hτ c hc).2 (hw (hτ c hc).1)) (h.l₂ b hb)
    · exact Doomed.of_forall _ _ fun _ _ _ _ _ hb' => absurd hb' hb
  know₃ := fun c _ => by
    by_cases hc : P.on₂ c
    · exact Doomed.mono _ _ (fun _ hτ u _ hu _ _ => hτ u hu) (h.l₃ c hc)
    · exact Doomed.of_forall _ _ fun _ _ _ _ _ hc' => absurd hc' hc
  hands₁ := fun _ _ _ _ _ => trivial
  hands₂ := fun _ _ _ _ _ => trivial

/-- The composed extractor's value is what the first chain handed on. -/
theorem ext_eq (a : A) (τ : Tr P.links.all.shape) (b : P.A₁)
    (hb : P.out₁ a (Tr.fst (s := G.c₁) τ) = some b) : P.links.ext a τ () = b := by
  unfold Links.ext Reduction.extSeq
  split
  · show (P.out₁ a (Tr.fst (s := G.c₁) τ)).elim P.d (fun b'' => b'') = b
    rw [hb]
    rfl
  · rename_i hn
    exact absurd (hb.symm.trans hn) (by simp)

/-- Where the three in a row put out, the first has handed on. -/
theorem first_of_all (a : A) (τ : Tr P.links.all.shape) (h : (P.links.all.out a τ).isSome = true) :
    ∃ b, P.out₁ a (Tr.fst (s := G.c₁) τ) = some b := by
  cases hb : P.out₁ a (Tr.fst (s := G.c₁) τ) with
  | some b => exact ⟨b, rfl⟩
  | none =>
    have : P.links.all.out a τ = none := by
      show (P.out₁ a (Tr.fst (s := G.c₁) τ)).bind _ = none
      rw [hb]
      rfl
    rw [this] at h
    cases h

end PlainFile

section At
variable {I X Wn : Type} (L : HolographicProtocol I X) {G : Chains}

/-- **The key file's hypothesis of the top, from the plain form.** -/
theorem keySound_plain (D : Desc G L.Rec (oneExternalString L.wordLength L.Symbol)) (aT : RoundSplits L.offline.shape)
    (hT : L.offline = D.proto) (ha : HEq aT G.ann) (P : PlainFile G (L.Rec × (oneExternalString L.wordLength L.Symbol).Str))
    (laws : G.Laws) (h : P.Leads3)
    (decides : ∀ x y (τ : Tr G.sh), D.accept x y τ = true →
      (P.links.all.out (x, y) τ).isSome = true)
    (ties : ∀ rec y, (P.on₀ (rec, y) → ∃ b, P.M (rec, y) b) →
      L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none) (dT : ℕ) {εs : ℝ≥0∞}
    (worst : P.links.worst (2 ^ dT) ≤ εs) :
    ∃ ε : Err L.offline.shape, Err.Below (Err.timesShared (2 ^ dT) aT ε) εs ∧
      L.offline.Sound (fun rec y => L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none) ε :=
  keySound_at L D aT hT ha laws (P.knows h) decides ties dT worst

/-- **The proof file's hypothesis of the top, from the plain form.** -/
theorem proofSound_plain (D : Desc G (X × L.Rec) (oneExternalString L.wordLength L.Symbol)) (hB : L.onlineBatch = D.batch)
    (Rno : I → X → Wn → Prop) (w₀ : Wn) (P : PlainFile G ((X × L.Rec) × (oneExternalString L.wordLength L.Symbol).Str))
    (hl : L.late = none) (laws : G.Laws) (h : P.Leads3)
    (decides : ∀ x rec y (τ : Tr G.sh), D.accept (x, rec) y τ = true →
      (P.links.all.out ((L.early x, rec), y) τ).isSome = true)
    (ties : ∀ x rec y (τ : Tr G.sh) b, D.accept (x, rec) y τ = true →
      P.out₁ ((L.early x, rec), y) (Tr.fst (s := G.c₁) (t := G.c₂ ++ G.c₃) τ) = some b →
      (P.on₀ ((L.early x, rec), y) → P.M ((L.early x, rec), y) b) → L.relB Rno rec x y w₀)
    {εs : ℝ≥0∞} (worst : P.links.worst L.maxBatchSize ≤ εs) :
    ∃ (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn)
      (ε : Err L.onlineBatch.loc.shape), Err.Below ε εs ∧
      ∀ rec, (L.batAt rec).SndBKT L.maxBatchSize L.early L.late (L.relB Rno rec)
        (fun x y τ => wit (x, rec) y τ) ε :=
  proofSound_at L D hB Rno (fun _ => w₀) hl laws (P.knows h) decides
    (fun x rec y τ hacc hR => by
      obtain ⟨b, hb⟩ := P.first_of_all _ τ (decides x rec y τ hacc)
      refine ties x rec y τ b hacc hb fun ho => ?_
      have := hR ho
      rwa [P.ext_eq _ τ b hb] at this) worst

end At

end TypedOracleCompiler.Joined

#print axioms TypedOracleCompiler.Joined.PlainFile.knows
#print axioms TypedOracleCompiler.Joined.keySound_plain
#print axioms TypedOracleCompiler.Joined.proofSound_plain
