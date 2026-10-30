-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineRunsRows.lean: general tools for `BlockPlays` (E2E/OfflineRunsForm.lean): the sub-protocols without a
prover's side; a list of parts each of which plays at every state; and `BlocksPlay` from the sub-protocols
that have a prover's side alone. General in the description, the book and the prover.

  `blockPlays_bare`      a sub-protocol without a prover's side plays, whatever the state
  `PartPlays`            a part, at declared rounds: at every name, address, coin, list of as many challenges as it
                         has moves, and every state, `play` on its steps returns
  `RowPartsPlay`         the same of each part of a list, at its own stretch of the declared rounds
  `rowPartsPlay_of_members`   from the members as the frame cuts them (`membersOf`)
  `play_row_of_parts`    then `play` on the list's steps returns
  `blockPlays_of_parts`  so the sub-protocol at whose place that list stands plays, whatever the state
  `HalvesPlay`, `blocksPlay_of_halves`   `BlocksPlay` from `BlockPlays` at the sub-protocols that have a prover's side

`PartPlays` asks a part to play at EVERY state: a part that reads what was heard in front and errs where it is
short does not meet it; such a part's sub-protocol is paid from `MidForm` directly. Nothing on any property.
-/
import E2E.OfflineRunsForm
import Johnson.Desc.ProofFile.Honest.Small.SaysYesOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open VerifiableInference.Desc

section Chain
variable {S Cl V W Y Pb : Type}

/-- **A sub-protocol without a prover's side plays.** -/
theorem blockPlays_bare {φ : Face V W Pb} {Bk : ProverCoinCounts} {chain : Nat} {hs : List (Placed V W Y)}
    {b : Block S Cl} (hf : (hs.find? fun g => g.place == b.place) = none) (Pre : Mid W Y → Prop) :
    BlockPlays φ Bk chain hs b Pre := by
  intro k m ds l _ hd _ hl
  have ho := (chainSteps_rows [b] hs l hl).1 b List.mem_cons_self
  obtain rfl := steps_one_none hf hl
  exact play_bare_ok (bareSteps (W := W) (Y := Y) b) ds m
    (fun s' hs' => by
      obtain ⟨r, -, rfl⟩ := List.mem_map.1 hs'
      exact ⟨rfl, rfl, rfl⟩)
    (by
      rw [drawsFit_length _ _ hd]
      simp [bareSteps, ho])

/-- **A part plays at every state**, at the declared rounds rs. -/
def PartPlays (p : Part V W Y) (rs : List (Fmt.DeclaredRound × List Oracle)) : Prop :=
  ∀ (nm : String) (a : Addr) (v : Option V) (c : p.Coins) (ds : List Fmt.Drawn) (back : List Fmt.RoundView)
    (m : Mid W Y), ds.length = p.moves.length → ∃ y, play (p.steps nm a rs v c) ds back m = .ok y

/-- Each part of a list plays at every state, at its own stretch of the declared rounds. -/
def RowPartsPlay : List (Part V W Y) → List (Fmt.DeclaredRound × List Oracle) → Prop
  | [], _ => True
  | p :: ps, rs => PartPlays p (rs.take p.moves.length) ∧ RowPartsPlay ps (rs.drop p.moves.length)

/-- From the members as the frame cuts them. -/
theorem rowPartsPlay_of_members : ∀ (row : List (Part V W Y × Sim Pb)) (j : Nat)
    (rs : List (Fmt.DeclaredRound × List Oracle)),
    (∀ u ∈ membersOf row j rs, PartPlays u.part u.rounds) → RowPartsPlay (row.map (·.1)) rs
  | [], _, _, _ => trivial
  | x :: row, j, rs, h =>
    ⟨h ⟨j, rs.take x.1.moves.length, x.1, x.2⟩ List.mem_cons_self,
      rowPartsPlay_of_members row (j + 1) (rs.drop x.1.moves.length)
        fun u hu => h u (List.mem_cons_of_mem _ hu)⟩

/-- **Then `play` on the list's steps returns**, at as many challenges as the list has moves. -/
theorem play_row_of_parts (name : String) (a : Place) (v : Option V) :
    ∀ (ps : List (Part V W Y)) (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle))
      (c : RowCoins ps) (ds : List Fmt.Drawn) (m : Mid W Y), RowPartsPlay ps rs →
      ds.length = (ps.map (·.moves.length)).sum →
      ∃ y, play (rowSteps name a v ps j rs c) ds [] m = .ok y
  | [], _, _, _, ds, m, _, hl => by
    have e : ds = [] := List.eq_nil_of_length_eq_zero hl
    subst e
    exact ⟨([], m), rfl⟩
  | p :: ps, j, rs, c, ds, m, h, hl => by
    have hl' : ds.length = p.moves.length + (ps.map (·.moves.length)).sum := hl
    obtain ⟨y₁, hy₁⟩ := h.1 name ⟨a, j⟩ v c.1 (ds.take p.moves.length) [] m
      (by rw [List.length_take]; omega)
    obtain ⟨z, hz⟩ := play_row_of_parts name a v ps (j + 1) (rs.drop p.moves.length) c.2
      (ds.drop p.moves.length) y₁.2 h.2 (by rw [List.length_drop]; omega)
    refine ⟨(y₁.1 ++ z.1, z.2), ?_⟩
    show play (p.steps name ⟨a, j⟩ (rs.take p.moves.length) v c.1 ++
      rowSteps name a v ps (j + 1) (rs.drop p.moves.length) c.2) ds [] m = _
    rw [← List.take_append_drop p.moves.length ds,
      play_append _ _ _ _ _ _ (Small.play_lengths _ _ _ _ _ hy₁), hy₁]
    show (play _ _ (List.drop _ []) y₁.2).map _ = _
    rw [List.drop_nil, hz]
    rfl

/-- **The sub-protocol at whose place such a list stands plays**, whatever the state. -/
theorem blockPlays_of_parts {φ : Face V W Pb} {Bk : ProverCoinCounts} {chain : Nat} {hs : List (Placed V W Y)}
    {b : Block S Cl} {g : Placed V W Y} (hf : (hs.find? fun g => g.place == b.place) = some g)
    (h : RowPartsPlay g.parts (b.rounds.zip b.oracles)) (Pre : Mid W Y → Prop) :
    BlockPlays φ Bk chain hs b Pre := by
  intro k m ds l _ hd _ hl
  obtain ⟨-, hr⟩ := Small.member_lengths hf hl
  obtain ⟨c, -, rfl⟩ := steps_one_half hf hl
  refine play_row_of_parts b.name b.place _ g.parts 0 _ c ds m h ?_
  rw [drawsFit_length _ _ hd, ← hr]
  unfold Placed.rounds
  rw [foldl_moves, Nat.zero_add]

end Chain

section File
variable {Xi W₀ Rc Ky Tr X₀ X : Type}

/-- **`BlockPlays` at the sub-protocols that have a prover's side.** -/
structure HalvesPlay (F : FileDescription Xi) (Bk : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    (own : Local W₀ Rc Xi Tr) (common : Common W₀ Rc Ky) : Prop where
  first : ∀ j b g, F.first.blocksInOrder[j]? = some b →
    (H.first.find? fun g => g.place == b.place) = some g →
    BlockPlays .own Bk 0 H.first b (MidForm startNone (roundsIn F.first.blocksInOrder j) own)
  shared : ∀ j b g, F.shared.blocksInOrder[j]? = some b →
    (H.shared.find? fun g => g.place == b.place) = some g →
    BlockPlays .shared Bk 1 H.shared b (MidForm startNone (roundsIn F.shared.blocksInOrder j) common)
  second : ∀ j b g, F.second.blocksInOrder[j]? = some b →
    (H.second.find? fun g => g.place == b.place) = some g →
    BlockPlays .own Bk 2 H.second b (MidForm (startThird F) (roundsIn F.second.blocksInOrder j) own)

/-- **It gives `BlocksPlay`**: the others play by themselves. -/
theorem blocksPlay_of_halves {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {own : Local W₀ Rc Xi Tr} {common : Common W₀ Rc Ky} (h : HalvesPlay F Bk H own common) :
    BlocksPlay F Bk H own common where
  first := fun j b hb => by
    cases hf : H.first.find? fun g => g.place == b.place with
    | none => exact blockPlays_bare hf _
    | some g => exact h.first j b g hb hf
  shared := fun j b hb => by
    cases hf : H.shared.find? fun g => g.place == b.place with
    | none => exact blockPlays_bare hf _
    | some g => exact h.shared j b g hb hf
  second := fun j b hb => by
    cases hf : H.second.find? fun g => g.place == b.place with
    | none => exact blockPlays_bare hf _
    | some g => exact h.second j b g hb hf

end File

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.blockPlays_bare
#print axioms AtPublicFiles.OfflineRows.rowPartsPlay_of_members
#print axioms AtPublicFiles.OfflineRows.play_row_of_parts
#print axioms AtPublicFiles.OfflineRows.blockPlays_of_parts
#print axioms AtPublicFiles.OfflineRows.blocksPlay_of_halves
