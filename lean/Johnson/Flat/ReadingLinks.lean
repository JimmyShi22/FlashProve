-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ReadingLinks.lean: the reading's law (Johnson/Flat/ReadingLaw.lean) feeds the landed
road by links to the proof file's hypothesis on soundness: its clauses chain₁, chain₂, chain₃ pay
the three premises f₁, f₂, f₃ of `linksBack_knowsJ` (OnBytes/TypedOracleCompiler/Joined/LinksBack.lean), and the
call is made. And what a kind owes for the reading of its stretch, with "the maps read every round"
in it.

Why. `CompilerSoundnessConditionStatements.proofSound` (Johnson/Top/InnerCompiledVerifier.lean) asks knowledge soundness in the form for
batches. The landed road to it goes by the file's three chains: each chain a typed reduction read
over the chain's written rounds (`linksBack`), with the list `Links.KnowsJ` from the typed
reductions' clauses and from maps whose written counts bear the typed ones. `ReadingLaw.sound` does
not feed that hypothesis. This file shows which part of that road the law pays, and which it leaves.
And the law is free at maps that skip every round (`readingLaw_skips`): so a kind's law that is
stated beside the reading of its stretch must ask that no round be skipped.

Definitions, statements and proofs.
  `Maps.ReadsAll`: no round is skipped. `Maps.not_readsAll_skips`: the maps that skip every round of
    a stretch that has a round do not read all. `Maps.ReadsAll.app`.
  `Maps.Reading M δ εs`: WHAT A KIND OWES FOR THE READING OF ITS STRETCH: `Maps.OK`,
    `Maps.ReadsAll`, `Maps.Held εs δ`. `Maps.Reading.app`: two stretches behind each other.
    `readingLaw_of_readings`: the law from the three chains' bundles.
  `chainMap₁`, `chainMap₂`, `chainMap₃`; `chainErr₁`, `chainErr₂`, `chainErr₃`: a chain's maps and
    written counts behind its silent round (the front round, the joining round, the seam), which is
    skipped and bears the count 0: over `G.c₁`, `G.c₂`, `G.c₃` (Compile/Joined/Types.lean), G the
    file's rounds `chainsOf`.
  `ReadingLaw.feeds`: under the law the three maps' written counts bear the typed ones (the shared
    chain's taken N times), and are shares of at most εs.
  `ReadingLaw.knowsJ`: THE CALL: `Links.KnowsJ N` of the description `linksBack` made of three typed
    reductions and these maps, from the law and seven of the road's other premises, handed on as
    they are: know₁, l₂, know₃, law₁, hg, hands₁, hands₂ (the eighth, hJ, holds of `chainsOf` by
    unfolding). The second chain's typed link l₂ is asked at the counts `Err.times N δ₂`.

Limits: THE ROAD IS NOT WALKED TO ITS END: from `Links.KnowsJ` to `CompilerSoundnessConditionStatements.proofSound` the landed
`proofSound_at_links` (OnBytes/TypedOracleCompiler/Joined/MidLinks.lean) asks more (that the file's verifier's yes
gives the links' outputs; the ties of the relations): not called here. THE SEVEN PREMISES OF
`ReadingLaw.knowsJ` ARE PREMISES: the typed clauses of the three chains above all: shown of no file.
`knowsJ` HAS NO CONTROL: the seven can be met together at reductions that never return (there law₁,
hands₁ and hands₂ are empty); no instance with a reduction that returns is laid. It spends the law's
halves on `Fits` alone, which follow from `Maps.OK`: εs and the three bounds of `feeds` are spent
nowhere yet (`CompilerSoundnessConditionStatements.proofSound`'s own bound on the counts is where). Whether a typed link for N
slots has the counts `Err.times N δ₂` of a link for one slot is not shown: l₂ is asked at these
counts. The maps do not read the statement, the key or the external string: `linksBack` allows that,
these do not. `Maps.ReadsAll` IS NEEDED BY NO PROOF HERE: it stands in `Maps.Reading` so that
whoever states a kind's law beside that bundle cannot pay with maps that read nothing;
`readingLaw_of`, `feeds` and `knowsJ` hold without it. It speaks of the written rounds ds of the
file's data, not of the rounds that a kind's text declares: that these are the same is not stated
here. Whether a whole chain of a real file can be read without a skip is not known here. No map is
made here, at any data.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.ReadingLaw
import OnBytes.TypedOracleCompiler.Joined.LinksBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace OnBytes.Flat
open Iop Prob _root_.Run _root_.Run.PQ OnBytes.Maker OnBytes.Slice TypedOracleCompiler.Joined

namespace Maps

/-- No round is skipped: every written round of the stretch is read as a typed round. -/
def ReadsAll : {ds : List RDT} → {s' : Shape} → Maps ds s' → Prop
  | _, _, .nil => True
  | _, _, .step _ rest => rest.ReadsAll
  | _, _, .skip _ _ => False

/-- Maps that skip every round of a stretch that has a round do not read all. -/
theorem not_readsAll_skips (d : RDT) (ds : List RDT) : ¬ (skips (d :: ds)).ReadsAll :=
  fun h => h

/-- Two stretches behind each other are read wholly if each is. -/
theorem ReadsAll.app : ∀ {ds es : List RDT} {s' t' : Shape} {M : Maps ds s'} {N : Maps es t'},
    M.ReadsAll → N.ReadsAll → (M.app N).ReadsAll
  | _, _, _, _, .nil, _, _, hN => hN
  | _, _, _, _, .step _ rest, _, hM, hN => ReadsAll.app (M := rest) hM hN
  | _, _, _, _, .skip _ _, _, hM, _ => hM.elim

/-- **What a kind owes for the reading of its stretch**: its maps are as asked, READ EVERY ROUND,
and the typed counts are held at εs. A kind's law is meant to be stated beside this bundle. -/
structure Reading {ds : List RDT} {s' : Shape} (M : Maps ds s') (δ : Err s') (εs : ℝ≥0∞) :
    Prop where
  ok : M.OK
  reads : M.ReadsAll
  held : M.Held εs δ

/-- Two kinds' stretches behind each other. -/
theorem Reading.app {ds es : List RDT} {s' t' : Shape} {M : Maps ds s'} {N : Maps es t'}
    {δ : Err s'} {η : Err t'} {εs : ℝ≥0∞} (hM : M.Reading δ εs) (hN : N.Reading η εs) :
    (M.app N).Reading (Err.app δ η) εs :=
  ⟨OK.app hM.ok hN.ok, ReadsAll.app hM.reads hN.reads, Held.app hM.held hN.held⟩

end Maps

section
variable (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3) {s₁' s₂' s₃' : Shape}
  (M₁ : Maps D.ds₁ s₁') (M₂ : Maps D.ds₂ s₂') (M₃ : Maps D.ds₃ s₃')

/-- The first chain's maps behind the front round. -/
def chainMap₁ : CarryS (chainsOf (ckP .two) D tF tJ t3).c₁ s₁' := .skip fun _ _ => M₁.carry

/-- The shared chain's maps behind the joining round. -/
def chainMap₂ : CarryS (chainsOf (ckP .two) D tF tJ t3).c₂ s₂' := .skip fun _ _ => M₂.carry

/-- The last chain's maps behind the seam. -/
def chainMap₃ : CarryS (chainsOf (ckP .two) D tF tJ t3).c₃ s₃' := .skip fun _ _ => M₃.carry

/-- The written counts: 0 at the silent round. -/
def chainErr₁ (δ : Err s₁') : Err (chainsOf (ckP .two) D tF tJ t3).c₁ := (0, M₁.err δ)

def chainErr₂ (δ : Err s₂') : Err (chainsOf (ckP .two) D tF tJ t3).c₂ := (0, M₂.err δ)

def chainErr₃ (δ : Err s₃') : Err (chainsOf (ckP .two) D tF tJ t3).c₃ := (0, M₃.err δ)

variable {M₁ M₂ M₃} {δ₁ : Err s₁'} {δ₂ : Err s₂'} {δ₃ : Err s₃'} {εs : ℝ≥0∞} {N : ℕ}

/-- **The reading's law from the three chains' bundles**, the shared chain's at N times its typed
counts. Here no round of the three chains is skipped. -/
theorem readingLaw_of_readings (h₁ : M₁.Reading δ₁ εs) (h₂ : M₂.Reading (Err.times N δ₂) εs)
    (h₃ : M₃.Reading δ₃ εs) : ReadingLaw D tF tJ t3 M₁ M₂ M₃ δ₁ δ₂ δ₃ εs N :=
  readingLaw_of D tF tJ t3 h₁.ok h₂.ok h₃.ok h₁.held h₂.held h₃.held

/-- **The law's three clauses on the chains, in the road's form**: the written counts bear the typed
ones, the shared chain's taken N times, and are shares of at most εs. -/
theorem ReadingLaw.feeds (R : ReadingLaw D tF tJ t3 M₁ M₂ M₃ δ₁ δ₂ δ₃ εs N) :
    ((chainMap₁ D tF tJ t3 M₁).Fits δ₁ (chainErr₁ D tF tJ t3 M₁ δ₁) ∧
      (chainMap₂ D tF tJ t3 M₂).Fits (Err.times N δ₂)
        (chainErr₂ D tF tJ t3 M₂ (Err.times N δ₂)) ∧
      (chainMap₃ D tF tJ t3 M₃).Fits δ₃ (chainErr₃ D tF tJ t3 M₃ δ₃)) ∧
    (Err.Below (chainErr₁ D tF tJ t3 M₁ δ₁) εs ∧
      Err.Below (chainErr₂ D tF tJ t3 M₂ (Err.times N δ₂)) εs ∧
      Err.Below (chainErr₃ D tF tJ t3 M₃ δ₃) εs) :=
  ⟨⟨fun _ _ => R.chain₁.1, fun _ _ => R.chain₂.1, fun _ _ => R.chain₃.1⟩,
    ⟨by rw [Nat.cast_zero]; exact zero_le _, R.chain₁.2⟩,
    ⟨by rw [Nat.cast_zero]; exact zero_le _, R.chain₂.2⟩,
    ⟨by rw [Nat.cast_zero]; exact zero_le _, R.chain₃.2⟩⟩

/-- **The call**: the list for the statements of a batch, of the description made of three typed
reductions (given by their outputs over s₁', s₂', s₃') read over the file's written rounds by these
maps. The law pays f₁, f₂, f₃; hJ holds of `chainsOf` by unfolding; the seven other premises are the
road's own, handed on. -/
theorem ReadingLaw.knowsJ (R : ReadingLaw D tF tJ t3 M₁ M₂ M₃ δ₁ δ₂ δ₃ εs N)
    {Y : Type} {E : ExtSpec} {X₁ X₂ X₃ A₁ A₂ W₀ W₁ W₂ κ κ' κ₂ : Type}
    (out₁ : X₁ → Tr s₁' → Option A₁) (out₂ : X₂ → Tr s₂' → Option A₂)
    (out₃ : X₃ → Tr s₃' → Option Unit) (k₁ : A₁ → κ) (a₁ : Y × E.Str → X₁) (a₂ : A₁ → X₂)
    (a₃ : A₂ → X₃) (on₀ : X₁ → Prop) (on₁ : X₂ → Prop) (on₂ : X₃ → Prop) (R₀ : X₁ → W₀ → Prop)
    (R₁ : X₂ → W₁ → Prop) (R₂ : X₃ → W₂ → Prop) (e₁ : X₁ → Tr s₁' → W₁ → W₀)
    (e₂ : X₂ → Tr s₂' → W₂ → W₁) (e₃ : X₃ → Tr s₃' → Unit → W₂) (t₁ : Tr s₁') (t₂ : Tr s₂')
    (t₃ : Tr s₃') (d₀ : W₀) (d₁ : W₁) (key' : X₂ → κ') (k₂ : A₂ → κ₂)
    (know₁ : (⟨s₁', out₁⟩ : Reduction X₁ A₁).Know on₀ R₀ (fun b w => R₁ (a₂ b) w) e₁ δ₁)
    (l₂ : LinkJ (⟨s₂', out₂⟩ : Reduction X₂ A₂) (shA s₂') N key' k₂ on₁ R₁
      (fun b w => R₂ (a₃ b) w) e₂ (Err.times N δ₂))
    (know₃ : (⟨s₃', out₃⟩ : Reduction X₃ Unit).Know on₂ R₂ (fun _ _ => True) e₃ δ₃)
    (g₁ : E.Str → κ)
    (law₁ : ∀ a τ b, (backS (⟨s₁', out₁⟩ : Reduction X₁ A₁)
      (fun _ : Y × E.Str => chainMap₁ D tF tJ t3 M₁) a₁).out a τ = some b → k₁ b = g₁ a.2)
    (g : κ → κ') (hg : ∀ a, key' (a₂ a) = g (k₁ a))
    (hands₁ : ∀ a τ b, on₀ (a₁ a) → (backS (⟨s₁', out₁⟩ : Reduction X₁ A₁)
      (fun _ : Y × E.Str => chainMap₁ D tF tJ t3 M₁) a₁).out a τ = some b → on₁ (a₂ b))
    (hands₂ : ∀ a τ b, on₁ (a₂ a) → (backS (⟨s₂', out₂⟩ : Reduction X₂ A₂)
      (fun _ : A₁ => chainMap₂ D tF tJ t3 M₂) a₂).out a τ = some b → on₂ (a₃ b)) :
    (linksBack (G := chainsOf (ckP .two) D tF tJ t3) (⟨s₁', out₁⟩ : Reduction X₁ A₁)
      (⟨s₂', out₂⟩ : Reduction X₂ A₂) (⟨s₃', out₃⟩ : Reduction X₃ Unit)
      (fun _ : Y × E.Str => chainMap₁ D tF tJ t3 M₁) k₁ (fun _ : κ => chainMap₂ D tF tJ t3 M₂)
      (fun _ : A₂ => chainMap₃ D tF tJ t3 M₃) a₁ a₂ a₃ on₀ on₁ on₂ R₀ R₁ R₂ e₁ e₂ e₃
      (chainErr₁ D tF tJ t3 M₁ δ₁) (chainErr₂ D tF tJ t3 M₂ (Err.times N δ₂))
      (chainErr₃ D tF tJ t3 M₃ δ₃) t₁ t₂ t₃ d₀ d₁).KnowsJ N k₁ k₂ :=
  linksBack_knowsJ t₁ t₂ t₃ d₀ d₁ rfl know₁ l₂ know₃ (fun _ => (R.feeds D tF tJ t3).1.1)
    (fun _ => (R.feeds D tF tJ t3).1.2.1) (fun _ => (R.feeds D tF tJ t3).1.2.2) g₁ law₁ g hg hands₁
    hands₂

end

end OnBytes.Flat

#print axioms OnBytes.Flat.Maps.ReadsAll.app
#print axioms OnBytes.Flat.Maps.Reading.app
#print axioms OnBytes.Flat.readingLaw_of_readings
#print axioms OnBytes.Flat.ReadingLaw.feeds
#print axioms OnBytes.Flat.ReadingLaw.knowsJ
