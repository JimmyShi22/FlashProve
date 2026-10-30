-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KindPaysOfALot.lean: what the rule at the muted rows takes of one kind (KindPays,
Johnson/T3/OwedOfKinds.lean), at the sides that E2E/TheSides.lean builds, from a hand-in at the kind's
own rows. General in the kind.

  good_of_narrower   Good at an On and a bound gives Good at any narrower On and bound
  block_of_seated    a list that is seated stands at a block of that chain
  find_name          in a list of lots with distinct names, the search for a member's name finds it
  Narrows, narrows_of_bare   a list's letters narrow the row's On and bound; letters that leave it whole do
  kindPays_of_rows   at any rows R and letters Ls: three hand-ins, one a chain, at the rows of the kind,
                     at the row's own On and bound, give KindPays at theSides
  rows_of_overlay    at the rows that overlaySlots lays: a row whose place is of the kind is a row of one
                     of the kind's own lots, where every other lot of the filling lays no side of it
  kindPays_of_lot    the two together, at a filling's lots: a hand-in at the rows of the kind's own
                     lots, and one at the rows of the kind in the lists of the two other chains

A hand-in speaks of the row as the kind lays it. A list's letters may narrow On and the bound, and no
more. This proves no kind's rows good.

  overlayRow_mem, kindPays_of_kindRows   the same at the rows that KindRows lays, on all three chains, at
                     any description: the form at which G stands (E2E/TheG.lean)

Limits. kindPays_of_lot's shared and second are lists given by the caller, and a hand-in at them is
asked of those lists; at KindRows the cover premises say that a side of the kind has a kind's row. KindPays holds of a kind with no row, for want of rows: that
every block has a row is asked elsewhere. A letter On that holds nowhere meets Narrows and leaves exact
asked nowhere; a bound that holds nowhere leaves exact and fresh so: what On and the bound meet in a run
is the rule's other premises.
No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import E2E.TheSides
import Johnson.T3.OwedOfKinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.TheSides
open ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription KindName Place)
open VerifiableInference.Compilation (KindPays)

/-- **Good at an On and a bound gives Good at any narrower On and bound**: they stand only in front of
the fields exact and fresh. -/
theorem good_of_narrower {S Cl V W Y Pb : Type} {pre : List (Nat × Nat × List Fmt.DeclaredRound)}
    {φ : Face V W Pb} {σ : Side S Cl V W Y Pb} {Bk : ProverCoinCounts} {ord : List Place} {chain firstTree : Nat}
    {A B : Coins Bk → S → Mid W Y → Env → Prop}
    {On On' : (u : Member V W Y Pb) → CsAll u.part.carries → Mid W Y → Before → Prop}
    {bud bud' : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop}
    (g : Good pre φ σ Bk ord chain firstTree A B On bud)
    (hOn : ∀ u ca m front, On' u ca m front → On u ca m front)
    (hbud : ∀ n ds asks, bud' n ds asks → bud n ds asks) :
    Good pre φ σ Bk ord chain firstTree A B On' bud' :=
  { fits := g.fits
    plays := g.plays
    acc := g.acc
    exact := fun u hu ca m front ds asks ho hs hop hd hb hh hst =>
      g.exact u hu ca m front ds asks (hOn u ca m front ho) hs hop hd (hbud _ _ _ hb) hh hst
    fresh := fun u hu p sp ca m ds asks hd hb hst =>
      g.fresh u hu p sp ca m ds asks hd (hbud _ _ _ hb) hst }

/-- A list that is seated stands at a block of that chain. -/
theorem block_of_seated {S Cl V W Y Pb : Type} {bs : List (Block S Cl)} {a : Place}
    {row : List (Part V W Y × Sim Pb)} {fs : List (Fall S)} {σ : Side S Cl V W Y Pb}
    (h : Side.seated bs a row fs = some σ) : ∃ b ∈ bs, b.place = a := by
  unfold Side.seated at h
  obtain ⟨b, hb, -⟩ := Option.map_eq_some_iff.1 h
  exact ⟨b, List.mem_of_find?_eq_some hb,
    eq_of_beq (List.find?_some (p := fun b : Block S Cl => b.place == a) hb)⟩

/-- In a list of lots with distinct names, the search for a member's name finds that member. -/
theorem find_name {V W Y Pb : Type} : ∀ {mine : List (SLot V W Y Pb)},
    (mine.map (·.name)).Nodup → ∀ {s : SLot V W Y Pb}, s ∈ mine →
      (mine.find? fun t => t.name == s.name) = some s
  | [], _, _, h => by cases h
  | t :: l, hn, s, h => by
    obtain ⟨h1, h2⟩ := List.nodup_cons.1 hn
    rcases List.mem_cons.1 h with rfl | h
    · exact List.find?_cons_of_pos (by simp)
    · have hne : (t.name == s.name) = false := by
        apply beq_eq_false_iff_ne.2
        intro e
        exact h1 (List.mem_map.2 ⟨s, h, e.symm⟩)
      rw [List.find?_cons_of_neg (by simp [hne])]
      exact find_name h2 h

section Rows
variable {Xi W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}

/-- **A list's letters narrow the row's On and bound.** -/
def Narrows {S Cl V W Y Pb : Type} (L : Lettered Bk S Cl V W Y Pb) (u : Unlettered V W Y Pb) : Prop :=
  (∀ v ca m front, L.On v ca m front → u.On v ca m front) ∧
    ∀ n ds asks, L.bud n ds asks → u.bud n ds asks

/-- Letters that leave a row whole narrow nothing. At the letters that say nothing and at the letters of
the threads that is by definition. -/
theorem narrows_of_bare {S Cl V W Y Pb : Type} {L : Lettered Bk S Cl V W Y Pb}
    {u : Unlettered V W Y Pb} (h : L.bare = u) : Narrows L u := by
  subst h
  exact ⟨fun _ _ _ _ x => x, fun _ _ _ x => x⟩

/-- **The premise of the rule at one kind, from three hand-ins.** CONDITIONAL: at each row of the kind
that is seated in its chain: the hand-in, at the row's own On and bound, and letters that narrow them. -/
theorem kindPays_of_rows (Ls : Letters F Bk W₀ Rc Ky Tr X₀ X) (R : Rows W₀ Rc Xi Ky Tr X₀ X)
    (f₁ : List (Fall F.S₁)) (f₂ : List (Fall F.S₂)) (f₃ : List (Fall F.S₃)) (κ : KindName)
    (hand₁ : ∀ u ∈ R.first, u.place.kind = κ → ∀ σ, Side.seated F.first.blocksInOrder u.place u.row f₁ = some σ →
      Narrows (Ls.first u) u ∧
      ∃ A' B', Good (preOf 0 0 (earlierOf F 0) F.first.blocksInOrder u.place) .own σ Bk (orderOf F) 0 0 A' B'
        u.On u.bud)
    (hand₂ : ∀ u ∈ R.shared, u.place.kind = κ → ∀ σ, Side.seated F.shared.blocksInOrder u.place u.row f₂ = some σ →
      Narrows (Ls.shared u) u ∧
      ∃ A' B', Good (preOf 1 0 (earlierOf F 1) F.shared.blocksInOrder u.place) .shared σ Bk (orderOf F) 1 0 A' B'
        u.On u.bud)
    (hand₃ : ∀ u ∈ R.second, u.place.kind = κ → ∀ σ, Side.seated F.second.blocksInOrder u.place u.row f₃ = some σ →
      Narrows (Ls.second u) u ∧
      ∃ A' B', Good (preOf 2 F.lastChainFirstTreeNumber (earlierOf F 2) F.second.blocksInOrder u.place) .own σ Bk (orderOf F) 2
        F.lastChainFirstTreeNumber A' B' u.On u.bud) :
    KindPays (theSides F Ls R f₁ f₂ f₃) κ := by
  refine ⟨fun L hL hk σ hσ => ?_, fun L hL hk σ hσ => ?_, fun L hL hk σ hσ => ?_⟩
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hL
    obtain ⟨ep, er⟩ := Ls.keeps₁ u
    have hs : Side.seated F.first.blocksInOrder u.place u.row f₁ = some σ := by
      rw [← ep, ← er]
      exact hσ
    obtain ⟨⟨nO, nb⟩, A', B', g⟩ := hand₁ u hu (ep ▸ hk) σ hs
    rw [ep]
    exact ⟨A', B', good_of_narrower g nO nb⟩
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hL
    obtain ⟨ep, er⟩ := Ls.keeps₂ u
    have hs : Side.seated F.shared.blocksInOrder u.place u.row f₂ = some σ := by
      rw [← ep, ← er]
      exact hσ
    obtain ⟨⟨nO, nb⟩, A', B', g⟩ := hand₂ u hu (ep ▸ hk) σ hs
    rw [ep]
    exact ⟨A', B', good_of_narrower g nO nb⟩
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hL
    obtain ⟨ep, er⟩ := Ls.keeps₃ u
    have hs : Side.seated F.second.blocksInOrder u.place u.row f₃ = some σ := by
      rw [← ep, ← er]
      exact hσ
    obtain ⟨⟨nO, nb⟩, A', B', g⟩ := hand₃ u hu (ep ▸ hk) σ hs
    rw [ep]
    exact ⟨A', B', good_of_narrower g nO nb⟩

end Rows

section Overlay
variable {V W Y Pb : Type}

/-- **At the rows that the overlay lays, a row of the kind is a row of one of the kind's own lots.**
CONDITIONAL: hm: the lots laid over have the filling's halves; hAlone: each lot of the filling either
bears the name of a lot of ls, or lays no side of the kind; ls: lots among those laid over, with
distinct names there. -/
theorem rows_of_overlay {Z : ProofFile.Pub} {Gr : ProofFile.Ground} {lots : List (HLot V W Y)}
    {mine ls : List (SLot V W Y Pb)} (apart : (mine.map (·.name)).Nodup) (hls : ∀ l ∈ ls, l ∈ mine)
    (hm : ∀ L ∈ lots, ∀ s, (mine.find? fun s => s.name == L.name) = some s →
      (s.rows Z Gr).map (·.half) = L.halves Z Gr)
    {κ : KindName}
    (hAlone : ∀ M ∈ lots, (∃ l ∈ ls, l.name = M.name) ∨ ∀ x ∈ M.halves Z Gr, x.place.kind ≠ κ) :
    ∀ u ∈ rowsOfLots Z Gr (lots.map (overlayLot mine)), u.place.kind = κ →
      ∃ l ∈ ls, u ∈ l.rows Z Gr := by
  intro u hu hk
  obtain ⟨sl, hsl, hus⟩ := List.mem_flatMap.1 hu
  obtain ⟨M, hM, rfl⟩ := List.mem_map.1 hsl
  rcases hAlone M hM with ⟨l, hl, en⟩ | hno
  · have hf := find_name apart (hls l hl)
    rw [en] at hf
    have he : overlayLot mine M = l := by
      unfold overlayLot
      rw [hf]
    rw [he] at hus
    exact ⟨l, hl, hus⟩
  · have hh := overlay_half (Z := Z) (Gr := Gr) (hm M hM)
    have hmem : u.half ∈ M.halves Z Gr := by
      rw [← hh]
      exact List.mem_map_of_mem hus
    exact absurd hk (hno _ hmem)

end Overlay

section Lot
variable {W₀ Rc X₀ X : Type}

/-- **The premise of the rule at one kind, at the sides built from a filling's lots, from a hand-in at
the kind's own lots ls and at the rows of the two other chains.** CONDITIONAL: hls, hAlone as at
rows_of_overlay; hand₁ at each row of the kind of a lot of ls that is seated; hand₂, hand₃ at the rows
of the kind in the given lists. -/
theorem kindPays_of_lot {P : OnlineProverParts W₀ Rc Cells X₀ X} {A : OnlineProverWithDescription W₀ Rc Cells X₀ X}
    (mine : List (SLot (Local W₀ Rc ProofFile.Inst Cells) (Local W₀ Rc ProofFile.Inst Cells) X ProofFile.Inst))
    (named : ∀ s ∈ mine, P.lots.any (fun L => L.name == s.name) = true)
    (apart : (mine.map (·.name)).Nodup)
    (hm : ∀ L ∈ P.lots, ∀ s, (mine.find? fun s => s.name == L.name) = some s →
      (s.rows A.Z A.G).map (·.half) = L.halves A.Z A.G)
    (shared : List (Unlettered Empty (Common W₀ Rc OnBytes.TableKey) X₀ OnBytes.TableKey))
    (hs : shared.map (·.half) = P.shared A.Z A.G)
    (second : List (Unlettered (Local W₀ Rc ProofFile.Inst Cells) (Local W₀ Rc ProofFile.Inst Cells) X ProofFile.Inst))
    (h₃ : second.map (·.half) = P.second A.Z A.G)
    (Ls : Letters A.F A.B W₀ Rc OnBytes.TableKey Cells X₀ X)
    (f₁ : List (Fall A.F.S₁)) (f₂ : List (Fall A.F.S₂)) (f₃ : List (Fall A.F.S₃)) (κ : KindName)
    (ls : List (SLot (Local W₀ Rc ProofFile.Inst Cells) (Local W₀ Rc ProofFile.Inst Cells) X ProofFile.Inst))
    (hls : ∀ l ∈ ls, l ∈ mine)
    (hAlone : ∀ M ∈ P.lots, (∃ l ∈ ls, l.name = M.name) ∨
      ∀ x ∈ M.halves A.Z A.G, x.place.kind ≠ κ)
    (hand₁ : ∀ l ∈ ls, ∀ u ∈ l.rows A.Z A.G, u.place.kind = κ → ∀ σ,
      Side.seated A.F.first.blocksInOrder u.place u.row f₁ = some σ →
      Narrows (Ls.first u) u ∧
      ∃ A' B', Good (preOf 0 0 (earlierOf A.F 0) A.F.first.blocksInOrder u.place) .own σ A.B (orderOf A.F) 0 0
        A' B' u.On u.bud)
    (hand₂ : ∀ u ∈ shared, u.place.kind = κ → ∀ σ,
      Side.seated A.F.shared.blocksInOrder u.place u.row f₂ = some σ →
      Narrows (Ls.shared u) u ∧
      ∃ A' B', Good (preOf 1 0 (earlierOf A.F 1) A.F.shared.blocksInOrder u.place) .shared σ A.B (orderOf A.F) 1
        0 A' B' u.On u.bud)
    (hand₃ : ∀ u ∈ second, u.place.kind = κ → ∀ σ,
      Side.seated A.F.second.blocksInOrder u.place u.row f₃ = some σ →
      Narrows (Ls.second u) u ∧
      ∃ A' B', Good (preOf 2 A.F.lastChainFirstTreeNumber (earlierOf A.F 2) A.F.second.blocksInOrder u.place) .own σ A.B
        (orderOf A.F) 2 A.F.lastChainFirstTreeNumber A' B' u.On u.bud) :
    KindPays (theSides A.F Ls
      (overlaySlots P A.Z A.G mine named apart hm shared hs second h₃).rows f₁ f₂ f₃) κ := by
  have hr := rows_of_overlay (Z := A.Z) (Gr := A.G) apart hls hm hAlone
  refine kindPays_of_rows Ls _ f₁ f₂ f₃ κ (fun u hu hk σ hσ => ?_) hand₂ hand₃
  obtain ⟨l, hl, hul⟩ := hr u hu hk
  exact hand₁ l hl u hul hk σ hσ

end Lot

section KindRowsLaid
variable {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {Z : ProofFile.Pub} {Gr : ProofFile.Ground}

/-- A row that overlayRow lays at a side at whose place some row of the list stands is of that list. -/
theorem overlayRow_mem {V W Y Pb : Type} {mine : List (Unlettered V W Y Pb)} {h : Placed V W Y}
    (hc : mine.any (fun r => r.place == h.place) = true) : overlayRow mine h ∈ mine := by
  unfold overlayRow
  cases hf : mine.find? fun r => r.place == h.place with
  | some r => exact List.mem_of_find?_eq_some hf
  | none =>
    obtain ⟨q, hq, hp⟩ := List.any_eq_true.1 hc
    exact absurd hp (List.find?_eq_none.1 hf q hq)

/-- **The premise of the rule at one kind, at the rows that the kinds lay, at any description and
letters.** CONDITIONAL: hls, hAlone as at rows_of_overlay, at the first chain; cover₂, cover₃: each side
of the kind in the two other chains has a row of the kinds at its place; hand₁, hand₂, hand₃ at the rows
of the kind. -/
theorem kindPays_of_kindRows {F : FileDescription ProofFile.Inst} {Bk : ProverCoinCounts} (K : KindRows P Z Gr)
    (Ls : Letters F Bk W₀ Rc OnBytes.TableKey Tr X₀ X)
    (f₁ : List (Fall F.S₁)) (f₂ : List (Fall F.S₂)) (f₃ : List (Fall F.S₃)) (κ : KindName)
    (ls : List (SLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst))
    (hls : ∀ l ∈ ls, l ∈ K.lots)
    (hAlone : ∀ M ∈ P.lots, (∃ l ∈ ls, l.name = M.name) ∨ ∀ x ∈ M.halves Z Gr, x.place.kind ≠ κ)
    (cover₂ : ∀ h ∈ P.shared Z Gr, h.place.kind = κ →
      K.shared.any (fun r => r.place == h.place) = true)
    (cover₃ : ∀ h ∈ P.second Z Gr, h.place.kind = κ →
      K.second.any (fun r => r.place == h.place) = true)
    (hand₁ : ∀ l ∈ ls, ∀ u ∈ l.rows Z Gr, u.place.kind = κ → ∀ σ,
      Side.seated F.first.blocksInOrder u.place u.row f₁ = some σ →
      Narrows (Ls.first u) u ∧
      ∃ A' B', Good (preOf 0 0 (earlierOf F 0) F.first.blocksInOrder u.place) .own σ Bk (orderOf F) 0 0 A' B'
        u.On u.bud)
    (hand₂ : ∀ u ∈ K.shared, u.place.kind = κ → ∀ σ,
      Side.seated F.shared.blocksInOrder u.place u.row f₂ = some σ →
      Narrows (Ls.shared u) u ∧
      ∃ A' B', Good (preOf 1 0 (earlierOf F 1) F.shared.blocksInOrder u.place) .shared σ Bk (orderOf F) 1 0 A' B'
        u.On u.bud)
    (hand₃ : ∀ u ∈ K.second, u.place.kind = κ → ∀ σ,
      Side.seated F.second.blocksInOrder u.place u.row f₃ = some σ →
      Narrows (Ls.second u) u ∧
      ∃ A' B', Good (preOf 2 F.lastChainFirstTreeNumber (earlierOf F 2) F.second.blocksInOrder u.place) .own σ Bk (orderOf F) 2
        F.lastChainFirstTreeNumber A' B' u.On u.bud) :
    KindPays (theSides F Ls K.slots.rows f₁ f₂ f₃) κ := by
  have hr := rows_of_overlay (Z := Z) (Gr := Gr) K.apart hls K.lots_fit hAlone
  refine kindPays_of_rows Ls _ f₁ f₂ f₃ κ (fun u hu hk σ hσ => ?_) (fun u hu hk σ hσ => ?_)
    (fun u hu hk σ hσ => ?_)
  · obtain ⟨l, hl, hul⟩ := hr u hu hk
    exact hand₁ l hl u hul hk σ hσ
  · obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hu
    rcases overlayRow_cases K.shared h with e | e
    · exact hand₂ _ e hk σ hσ
    · have hp : h.place.kind = κ := by
        rw [e] at hk
        exact hk
      exact hand₂ _ (overlayRow_mem (cover₂ h hh hp)) hk σ hσ
  · obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hu
    rcases overlayRow_cases K.second h with e | e
    · exact hand₃ _ e hk σ hσ
    · have hp : h.place.kind = κ := by
        rw [e] at hk
        exact hk
      exact hand₃ _ (overlayRow_mem (cover₃ h hh hp)) hk σ hσ

end KindRowsLaid

end AtPublicFiles.TheSides

#print axioms AtPublicFiles.TheSides.good_of_narrower
#print axioms AtPublicFiles.TheSides.block_of_seated
#print axioms AtPublicFiles.TheSides.find_name
#print axioms AtPublicFiles.TheSides.Narrows
#print axioms AtPublicFiles.TheSides.narrows_of_bare
#print axioms AtPublicFiles.TheSides.kindPays_of_rows
#print axioms AtPublicFiles.TheSides.rows_of_overlay
#print axioms AtPublicFiles.TheSides.kindPays_of_lot
#print axioms AtPublicFiles.TheSides.overlayRow_mem
#print axioms AtPublicFiles.TheSides.kindPays_of_kindRows
