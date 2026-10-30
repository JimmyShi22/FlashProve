-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FramePromiseRides.lean: THREE CLAUSES OF THE PROMISE GO FORWARD OVER A STEP OF
THE FRAME THAT TURNS THE VERIFIER's STATE ("cleared"), AT THE COMPOSED MEANING (`mgAll 𝔇 Mg`,
Johnson/Desc/Sound/MgAll.lean): "the committed table decodes", "every leaf is shown",
"no collision": the fields `decodes`, `shown`, `noColl` of `LettersRide` (FrameTied.lean), to the
letter.

What is said.
  `DecRides 𝔇 rel`: THE PREMISE ON 𝔇.decT: where the decoder of the committed table answers at the
    state in front, it answers at the state behind (that the two answers are one is not asked).
  `decodes_rides`, `decRides_of_field`, `decodes_iff`: **the field `decodes` IS that premise**: each
    gives the other: so no weaker premise serves.
  `shown_rides`: "shown" reads no state and no parameter that does: no premise but "the tree lies
    below base".
  `SeedRides 𝔇 rel base In`: THE PREMISE ON 𝔇.smp: at a member of 𝔇.ms in a tree below base, where
    the reader of the OOD samples answers in front, it answers behind WITH THE SAME SEED (the
    answers to the sample may differ: "no collision" reads the seed alone). It may spend "no mark"
    and what is known in front.
  `noColl_rides`: "no collision" goes forward under it.
  `LowAt N O base`: every tenant whose pin is open behind sits in a tree below base.
  `FrontGives 𝔇 Mg N O In`: what is known in front gives the two clauses in front, at the tenants
    whose pin is open behind. `frontGives_at`: at the ties' own `FrontAt` it follows from: every
    tenant whose pin is open behind has its pin open in front.
  `shown_field`, `noColl_field`: the two fields, to the letter.
  `decRides_of_kept`, `seedRides_of_kept`: both premises from `ReadKept` (FrameFieldsBack.lean).
  `not_decRides_pile`: `DecRides` can fail over an accepting step that turns the pile alone.
  `three_cleared`, `three_clear_row`: **the three fields at the yes of every "cleared", and of the
    "cleared" of a row of `framesOf`.**

Limits. `DecRides`, `SeedRides` are premises on parameters that are letters: owed by
whoever fills 𝔇; THAT ANY REAL FILLING HAS THEM IS NOT SHOWN HERE. `SeedRides` is weaker than "the
reader answers alike"; that it is the weakest is not shown. `LowAt` and the premise of
`frontGives_at` are facts on the plan's numbers and the table: owed. No soundness statement.

-/
import Johnson.Top.H0.Walk.FrameFieldsBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Strs Place)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers sampledIn openSets start)
open VerifiableInference.Desc.First.Pend (pendingRowO)

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (VerifiableInference.Desc.Wit (CellsQ rows cols) Tok MsgT))

/-! ### "the committed table decodes" -/

/-- **The premise on 𝔇.decT**: where it answers in front, it answers behind. -/
def DecRides (rel : S → S → Prop) : Prop :=
  ∀ p s t c, rel s t → (𝔇.decT c (p, s)).isSome = true → (𝔇.decT c (p, t)).isSome = true

/-- The field `decodes` of `LettersRide`, to the letter. -/
theorem decodes_rides {rel : S → S → Prop} (base : Nat) (hd : DecRides 𝔇 rel) :
    ∀ p s t y y', rel s t → Stays base y y' → (mgAll 𝔇 Mg).decodes (p, s) y →
      (mgAll 𝔇 Mg).decodes (p, t) y' := by
  intro p s t y y' hr hy h
  rw [mgAll_decodes] at h ⊢
  show (𝔇.decT y'.cell (p, t)).isSome = true
  rw [show y'.cell = y.cell from funext hy.1]
  exact hd p s t _ hr h

/-- And back: the field gives the premise. -/
theorem decRides_of_field {rel : S → S → Prop} (base : Nat)
    (h : ∀ p s t y y', rel s t → Stays base y y' → (mgAll 𝔇 Mg).decodes (p, s) y →
      (mgAll 𝔇 Mg).decodes (p, t) y') : DecRides 𝔇 rel := by
  intro p s t c hr hc
  have h1 := h p s t ⟨c, fun _ _ => []⟩ ⟨c, fun _ _ => []⟩ hr (Stays.refl _ _)
    (by rw [mgAll_decodes]; exact hc)
  rw [mgAll_decodes] at h1
  exact h1

/-- **The field `decodes` is the premise.** -/
theorem decodes_iff (rel : S → S → Prop) (base : Nat) :
    (∀ p s t y y', rel s t → Stays base y y' → (mgAll 𝔇 Mg).decodes (p, s) y →
      (mgAll 𝔇 Mg).decodes (p, t) y') ↔ DecRides 𝔇 rel :=
  ⟨decRides_of_field 𝔇 Mg base, decodes_rides 𝔇 Mg base⟩

/-! ### "every leaf is shown", "no collision" -/

theorem shown_rides {base j t : Nat} {y y' : Strs} (hj : j < base) (hy : Stays base y y')
    (h : (mgAll 𝔇 Mg).shown j t y) : (mgAll 𝔇 Mg).shown j t y' := by
  rw [mgAll_shown] at h ⊢
  exact shownJT_col 𝔇.cs 𝔇.G 𝔇.ms j t y y' (fun x => hy.2 j x hj) h

/-- **The premise on 𝔇.smp**: the same seed behind. -/
def SeedRides (rel : S → S → Prop) (base : Nat) (In : P × S → Strs → Prop) : Prop :=
  ∀ p s t y, rel s t → s.failed = none → In (p, s) y → ∀ x ∈ 𝔇.ms, (x.1.seat x.2).1 < base →
    ∀ z, 𝔇.smp (p, s) x.1 x.2 = some z → ∃ z', 𝔇.smp (p, t) x.1 x.2 = some z' ∧ z'.1 = z.1

theorem noColl_rides {base j k : Nat} {p : P} {s t : S} {y y' : Strs} (hj : j < base)
    (hy : Stays base y y')
    (hs : ∀ x ∈ 𝔇.ms, (x.1.seat x.2).1 < base → ∀ z, 𝔇.smp (p, s) x.1 x.2 = some z →
      ∃ z', 𝔇.smp (p, t) x.1 x.2 = some z' ∧ z'.1 = z.1)
    (h : (mgAll 𝔇 Mg).noColl j k (p, s) y) : (mgAll 𝔇 Mg).noColl j k (p, t) y' := by
  rw [mgAll_noColl] at h ⊢
  have h1 := noCollJT_col 𝔇.cs 𝔇.G 𝔇.smp 𝔇.ms j k (p, s) y y' (fun x => hy.2 j x hj) h
  intro x hx hsit
  obtain ⟨z, hz, h2, h3⟩ := h1 x hx hsit
  have hs' : x.1.seat x.2 = (j, k) := hsit
  obtain ⟨z', hz', e⟩ := hs x hx (by rw [hs']; exact hj) z hz
  exact ⟨z', hz', h2, by rw [e]; exact h3⟩

/-- Every tenant whose pin is open behind sits in a tree below base. -/
def LowAt (N : Numbers) (O : List Item) (base : Nat) : Prop := ∀ x ∈ sampledIn N O, x.1 < base

/-- What is known in front gives the two clauses in front, at the tenants whose pin is open behind.
-/
def FrontGives (N : Numbers) (O : List Item) (In : P × S → Strs → Prop) : Prop :=
  ∀ p s y x, s.failed = none → In (p, s) y → x ∈ sampledIn N O →
    (mgAll 𝔇 Mg).shown x.1 x.2 y ∧ (mgAll 𝔇 Mg).noColl x.1 x.2 (p, s) y

/-- At the ties' own `FrontAt`: from "no pin opens over the step". -/
theorem frontGives_at (N : Numbers) (links : List ModelPart) (ps : List Place) (k : Nat)
    (hsub : ∀ x ∈ sampledIn N ((openSets links ps (start links))[k + 1]?.getD []),
      x ∈ sampledIn N ((openSets links ps (start links))[k]?.getD [])) :
    FrontGives 𝔇 Mg N ((openSets links ps (start links))[k + 1]?.getD [])
      (FrontAt N (mgAll 𝔇 Mg) links ps k) := by
  intro p s y x hf hI hx
  obtain ⟨-, h | ⟨-, -, h, -⟩⟩ := hI
  · exact absurd hf h
  · exact h x (hsub x hx)

/-- The field `shown` of `LettersRide`, to the letter. -/
theorem shown_field {N : Numbers} {O : List Item} {rel : S → S → Prop} {base : Nat}
    {In : P × S → Strs → Prop} (hl : LowAt N O base) (hF : FrontGives 𝔇 Mg N O In) :
    ∀ p s t y y' x, rel s t → Stays base y y' → s.failed = none → In (p, s) y →
      x ∈ sampledIn N O → (mgAll 𝔇 Mg).shown x.1 x.2 y' :=
  fun p s _ y _ x _ hy hf hI hx => shown_rides 𝔇 Mg (hl x hx) hy (hF p s y x hf hI hx).1

/-- The field `noColl` of `LettersRide`, to the letter. -/
theorem noColl_field {N : Numbers} {O : List Item} {rel : S → S → Prop} {base : Nat}
    {In : P × S → Strs → Prop} (hl : LowAt N O base) (hF : FrontGives 𝔇 Mg N O In)
    (hs : SeedRides 𝔇 rel base In) :
    ∀ p s t y y' x, rel s t → Stays base y y' → s.failed = none → In (p, s) y →
      x ∈ sampledIn N O → (mgAll 𝔇 Mg).noColl x.1 x.2 (p, t) y' :=
  fun p s t y _ x hr hy hf hI hx =>
    noColl_rides 𝔇 Mg (hl x hx) hy (hs p s t y hr hf hI) (hF p s y x hf hI hx).2

/-! ### the two premises from `ReadKept`; a case where the first fails -/

theorem decRides_of_kept {rel : S → S → Prop} (hrel : ∀ s t, rel s t → Kept s t) (base : Nat)
    (H : ReadKept 𝔇 base) : DecRides 𝔇 rel := fun p s t c hr h => by
  rw [← H.dec p s t c (hrel s t hr)]
  exact h

theorem seedRides_of_kept {rel : S → S → Prop} (hrel : ∀ s t, rel s t → Kept s t) (base : Nat)
    (In : P × S → Strs → Prop) (H : ReadKept 𝔇 base) : SeedRides 𝔇 rel base In :=
  fun p s t _ hr _ _ x hx hl z hz =>
    ⟨z, by rw [← H.smp p s t (hrel s t hr) x hx hl]; exact hz, rfl⟩

/-- **`DecRides` can fail**: at a decoder that answers only while the pile is empty, over a relation
that lets the pile grow. -/
theorem not_decRides_pile (p : P) (s₀ : S) (r : TensorRow) (M : CellsQ rows cols) :
    ¬ DecRides { 𝔇 with decT := fun _ a => if a.2.out.pending = [] then some M else none }
      (fun s t => t.out.pending = s.out.pending ++ [r]) := fun H => by
  have h1 := H p { s₀ with out := { s₀.out with pending := [] } }
    { s₀ with out := { s₀.out with pending := [r] } } (fun _ => none) rfl (by simp)
  simp at h1

/-! ### at «cleared» -/

/-- **The three fields at the yes of an accepting "cleared".** -/
theorem three_cleared (L : LinkPub) (counts : S → Except String Unit)
    (left : S → Option WsForkOut) (lay : WsLay) (lin : Params.LinShape) (N : Numbers)
    (O : List Item) (base : Nat) (In : P × S → Strs → Prop) (H : ReadKept 𝔇 base)
    (hl : LowAt N O base) (hF : FrontGives 𝔇 Mg N O In) :
    (∀ p s t y y',
        Yes (clearWith L counts left fun im w n os => pendingRowO lay im w n lin os) s t →
        Stays base y y' → (mgAll 𝔇 Mg).decodes (p, s) y → (mgAll 𝔇 Mg).decodes (p, t) y') ∧
      (∀ p s t y y' x,
        Yes (clearWith L counts left fun im w n os => pendingRowO lay im w n lin os) s t →
        Stays base y y' → s.failed = none → In (p, s) y → x ∈ sampledIn N O →
        (mgAll 𝔇 Mg).shown x.1 x.2 y') ∧
      ∀ p s t y y' x,
        Yes (clearWith L counts left fun im w n os => pendingRowO lay im w n lin os) s t →
        Stays base y y' → s.failed = none → In (p, s) y → x ∈ sampledIn N O →
        (mgAll 𝔇 Mg).noColl x.1 x.2 (p, t) y' :=
  have hk : ∀ s t, Yes (clearWith L counts left
      fun im w n os => pendingRowO lay im w n lin os) s t → Kept s t :=
    fun s t h => kept_cleared L counts left lay lin s t h
  ⟨decodes_rides 𝔇 Mg base (decRides_of_kept 𝔇 hk base H), shown_field 𝔇 Mg hl hF,
    noColl_field 𝔇 Mg hl hF (seedRides_of_kept 𝔇 hk base In H)⟩

/-- **At the "cleared" of a row of the frame's own list.** -/
theorem three_clear_row {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List Seat.LinkFrame} {f : Seat.LinkFrame} {l : Nat}
    (h : Seat.framesOf built first W = .ok fs) (hf : fs[l]? = some f) (N : Numbers)
    (O : List Item) (base : Nat) (In : P × S → Strs → Prop) (H : ReadKept 𝔇 base)
    (hl : LowAt N O base) (hF : FrontGives 𝔇 Mg N O In) :
    (∀ p s t y y', Yes f.clear s t → Stays base y y' → (mgAll 𝔇 Mg).decodes (p, s) y →
        (mgAll 𝔇 Mg).decodes (p, t) y') ∧
      (∀ p s t y y' x, Yes f.clear s t → Stays base y y' → s.failed = none → In (p, s) y →
        x ∈ sampledIn N O → (mgAll 𝔇 Mg).shown x.1 x.2 y') ∧
      ∀ p s t y y' x, Yes f.clear s t → Stays base y y' → s.failed = none → In (p, s) y →
        x ∈ sampledIn N O → (mgAll 𝔇 Mg).noColl x.1 x.2 (p, t) y' := by
  obtain ⟨L, counts, left, e⟩ : ∃ L counts left,
      f.clear = clearWith L counts left (Seat.rowOf W first) := by
    rcases Seat.framesOf_arms h hf with ⟨Y, -, -, e⟩ | ⟨-, Y, hp, Q, -, -, -, -, -, -, e⟩ |
      ⟨-, Y, hp, Q, -, -, -, -, -, -, e⟩ | ⟨-, Y, hp, Q, -, -, -, -, -, -, e⟩
    · subst e
      exact ⟨_, _, _, rfl⟩
    · exact ⟨_, _, _, e⟩
    · exact ⟨_, _, _, e⟩
    · exact ⟨_, _, _, e⟩
  rw [e]
  exact three_cleared 𝔇 Mg L counts left W.layers.wsLay first.lin N O base In H hl hF

end

#print axioms decodes_iff
#print axioms shown_rides
#print axioms noColl_rides
#print axioms frontGives_at
#print axioms shown_field
#print axioms noColl_field
#print axioms decRides_of_kept
#print axioms seedRides_of_kept
#print axioms not_decRides_pile
#print axioms three_cleared
#print axioms three_clear_row

end Johnson.Desc.First.Walk.Tied
