-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/Quiet.lean proves `ExactMember` (Honest/Small/Field.lean: the
field `exact` of `Good`, Honest/Side.lean, without its hypothesis on the opened columns; it gives
that field at every `pre`) at one member, `quietPart n` (n rounds in which the prover sends nothing)
beside `quietSim a n` (Honest/ForKinds.lean), conditional on the one premise hrs: the member's
rounds rs are n rounds, each of which states no item but roots and no oracle message. It is
bookkeeping, not a theorem on a coin or an input. It is not a statement on a whole row, on a run of
the protocol or on a quiet part into which a stop has been laid. It is for every caller whose rounds
meet the premise.

  `quietPart_exact_lift`: at the part written at any types and seated by `Part.lift`, at every see,
     wit, get and set (the four together: the lens)
  `quietPart_exact`: at the bare part (not lifted), at all types at which there is a face
  the rest: the lemmas on the way: a round in which nothing is sent, as the fold meets it; such
     rounds played; what they show

The face, the side, chain, firstTree, On, bud, the member's number j, its rounds rs and the
simulator's address a are variables; the member is written out.

What is sampled: on the part's side `Cs ⟨0, 0⟩ × CsAll []`; on the simulator's `Cs ⟨0, 0⟩`: one
point each. Fixed: ca, m, front, ds, asks. Both distributions are the point mass at n rounds that
show no item and no column: two constants are compared: the theorem's whole content is that the part
is not at fault and that the numbers of rounds agree. Of the six premises of `ExactMember`
`drawsFit` alone is used, and of it only that ds is as long as rs; the five others stand in the text
and are not used.

The frame's terms that are used here (part, side, row, member, face, coin, run, book, fold and the
like): the head of Honest/Small/Field.lean. All names stand in the namespace ProofFile.Honest.Small: a
caller opens it.

Limits. Without hrs the equation fails: at a round that states a scalar the part is at fault and
shows the one symbol, and its simulator does not; at fewer or more rounds than n the numbers of
rounds differ, or the fold refuses (Honest/Small/Toy.lean). That a description's rounds state this
shape is the caller's to show: this file shows it of none.
hrs is wider than "nothing is sent". It lets through a round whose entry counts roots, or has
left-over bytes, with no oracle message. The part lays no table there, and what a part shows never
holds a root: the equation is true there, of a prover that sends no oracle message where the plan
counts a root. `Block.shaped`, which the plan's test asks, refuses the first (`roots_of_shaped`,
Honest/Small/Field.lean), the format's `Round.ok` (Fmt/Rules8.lean) the second; `Good` refuses
neither: the plan's test is owed beside this theorem, and for the left-over bytes whatever leads
from the description to `Round.ok`.
hrs reads neither `DeclaredRound.stored` nor `DeclaredRound.opens` nor the work bits. A quiet round may draw
positions at which trees and stored tables are opened: these columns are accounted for at the
sender's part and in `Before.stored`, not here; a nonce is accounted for nowhere at the level of the
views, at which `Good` stands.
What the part hands on is not in the equation. "At every set" is no word on the lens: at each of its
rounds the seated part lays set x (get x) on what is handed on; what a later part then shows is that
part's own `exact`.
n = 0 is in, and idle: the book's tests refuse a part without a round. Nothing is claimed on any
property of the protocol: not soundness, completeness, binding, hiding or any other.
-/
import Johnson.Desc.ProofFile.Honest.Law.ToyLaw
import Johnson.Desc.ProofFile.Honest.Law.ToyPlay
import Johnson.Desc.ProofFile.Honest.Law.Along
import Johnson.Desc.ProofFile.Honest.Small.Field
import Johnson.Desc.ProofFile.Honest.Small.Lift

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Small
open VerifiableInference.Desc (Place Oracle)

variable {S Cl V W X Pb V' W' Y : Type}

/-! ## 1 Rounds in which nothing is sent -/

/-- Binding any option to the function that always yields `none` gives `none`. `bindNone` in
Honest/Small/Scalars.lean is the same statement: neither file imports the other. -/
theorem bind_to_none {α β : Type} (o : Option α) :
    (o.bind fun _ => (none : Option β)) = none := by
  cases o <;> rfl

/-- A round in which nothing is sent, as the fold meets it: no stop stops; the move says the empty
message, wherever the run stands; the round states that shape. -/
def QuietStep (s : Step W X) : Prop :=
  (∀ f o, s.bad f o = none) ∧ (∀ f o, s.hid f o = none) ∧
    (∃ mv, s.move = some mv ∧ ∀ sn st, mv.say () sn st = .ok ⟨[], []⟩) ∧
    (⟨[], []⟩ : Sending).fits s.decl s.oracles = true

/-- Such rounds are played, at as many challenges; each shows no item and has no table. -/
theorem play_quietSteps : ∀ (ss : List (Step W X)) (ds : List Fmt.Drawn) (m : Mid W X),
    (∀ s ∈ ss, QuietStep s) → ss.length = ds.length →
    ∃ y, play ss ds [] m = .ok y ∧ y.1.length = ss.length ∧
      ∀ p ∈ y.1, p.vals = [] ∧ p.tables = []
  | [], [], m, _, _ => ⟨([], m), play_nil m, rfl, fun _ h => absurd h (List.not_mem_nil)⟩
  | s :: ss, d :: ds, m, h, hl => by
    obtain ⟨hb, hh, ⟨mv, hmv, hz⟩, hf⟩ := h s (List.mem_cons_self)
    obtain ⟨y, hy, hlen, hp⟩ := play_quietSteps ss ds (m.after mv [] d)
      (fun t ht => h t (List.mem_cons_of_mem _ ht)) (by
        simp only [List.length_cons] at hl
        omega)
    refine ⟨(playedOf s ⟨[], []⟩ d :: y.1, y.2), ?_, ?_, ?_⟩
    · rw [play_step hb hh hmv (hz _ _) hf]
      show (play ss ds [] (m.after mv [] d)).map _ = _
      rw [hy]
      rfl
    · show y.1.length + 1 = ss.length + 1
      rw [hlen]
    · intro p hp'
      rcases List.mem_cons.1 hp' with rfl | h'
      · exact ⟨rfl, rfl⟩
      · exact hp p h'
  | [], _ :: _, _, _, hl => by simp at hl
  | _ :: _, [], _, _, hl => by simp at hl

/-- A function that takes one value b at all members of a list, whatever their numbers, mapped over
the numbered list, gives b as many times as the list is long. -/
theorem map_zipIdx_const {α β : Type} (F : α × Nat → β) (b : β) : ∀ (l : List α) (k : Nat),
    (∀ x, x.1 ∈ l → F x = b) → (l.zipIdx k).map F = List.replicate l.length b
  | [], _, _ => rfl
  | a :: l, k, h => by
    rw [List.zipIdx_cons, List.map_cons, h (a, k) (List.mem_cons_self),
      map_zipIdx_const F b l (k + 1) fun x hx => h x (List.mem_cons_of_mem _ hx)]
    rfl

/-- What such rounds show, whatever positions are asked. -/
theorem shownOf_quiet (ps : List Played) (asks : List (List (List Nat)))
    (h : ∀ p ∈ ps, p.vals = [] ∧ p.tables = []) :
    shownOf ps asks = List.replicate ps.length ⟨[], []⟩ := by
  unfold shownOf
  refine map_zipIdx_const _ _ ps 0 fun x hx => ?_
  obtain ⟨hv, ht⟩ := h x.1 hx
  simp only [hv, ht]
  rfl

/-- The first component of a member of the numbered list is a member of the list. -/
theorem mem_zipIdx_fst {α : Type} : ∀ (l : List α) (k : Nat) (x : α × Nat),
    x ∈ l.zipIdx k → x.1 ∈ l
  | [], _, _, h => by simp at h
  | a :: l, k, x, h => by
    rw [List.zipIdx_cons] at h
    rcases List.mem_cons.1 h with rfl | h'
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_zipIdx_fst l (k + 1) x h')

/-- The premise hrs, taken apart. -/
theorem stated_quiet {rs : List (Fmt.DeclaredRound × List Oracle)} {n : Nat}
    (hrs : statedOf rs = List.replicate n ([], [])) :
    rs.length = n ∧ ∀ r ∈ rs, r.1.items.filter (· != .root) = [] ∧ r.2 = [] := by
  refine ⟨?_, fun r hr => ?_⟩
  · have := congrArg List.length hrs
    simpa [statedOf] using this
  · have h1 : (r.1.items.filter (· != .root), r.2) ∈ statedOf rs :=
      List.mem_map_of_mem (f := fun r : Fmt.DeclaredRound × List Oracle =>
        (r.1.items.filter (· != .root), r.2)) hr
    rw [hrs] at h1
    have h2 := List.eq_of_mem_replicate h1
    exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩

/-! ## 2 What the part shows -/

/-- Conditional on hrs and on `drawsFit`: the part, seated at whatever lens, shows n rounds without
an item or a column: at all coins, wherever the run stands. -/
theorem shows_quiet (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (j n : Nat)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (a : Addr)
    (see : V → V') (wit : W → W') (get : X → Y) (set : X → Y → X)
    (hrs : statedOf rs = List.replicate n ([], []))
    (c : ((quietPart n : Part V' W' Y).lift see wit get set).Coins) (m : Mid W X)
    (ds : List Fmt.Drawn) (asks : List (List (List Nat)))
    (hd : drawsFit (rs.map (·.1)) ds = true) :
    σ.shows φ ⟨j, rs, (quietPart n : Part V' W' Y).lift see wit get set, quietSim a n⟩ c m ds asks =
      some (List.replicate n ⟨[], []⟩) := by
  obtain ⟨hn, hr⟩ := stated_quiet hrs
  have hl : ds.length = rs.length := by
    have := drawsFit_length _ _ hd
    simpa using this
  have hlen : (((quietPart n : Part V' W' Y).lift see wit get set).steps σ.block.name
      ⟨σ.block.place, j⟩ rs (φ.sees m.st.input) c).length = n := by
    simp [Part.steps, Part.lift, quietPart, hn]
  obtain ⟨y, hy, hyl, hp⟩ := play_quietSteps
    (((quietPart n : Part V' W' Y).lift see wit get set).steps σ.block.name ⟨σ.block.place, j⟩ rs
      (φ.sees m.st.input) c) ds m (by
      intro s hs
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hs
      have hx1 := mem_zipIdx_fst _ _ _ hx
      obtain ⟨x1, x2⟩ := x
      obtain ⟨r, mv⟩ := x1
      obtain ⟨hr1, hmv⟩ := List.of_mem_zip hx1
      obtain ⟨mv₀, hmv₀, rfl⟩ := List.mem_map.1 hmv
      have hmv' := List.eq_of_mem_replicate hmv₀
      subst hmv'
      obtain ⟨h1, h2⟩ := hr r hr1
      refine ⟨fun _ _ => rfl, fun _ _ => bind_to_none _, ⟨_, rfl, fun _ _ => rfl⟩, ?_⟩
      show (⟨[], []⟩ : Sending).fits r.1 r.2 = true
      unfold Sending.fits
      rw [h1, h2]
      rfl) (by rw [hlen, hl, hn])
  unfold Side.shows
  show ((play (((quietPart n : Part V' W' Y).lift see wit get set).steps σ.block.name
    ⟨σ.block.place, j⟩ rs (φ.sees m.st.input) c) ds [] m).toOption.map
      fun y => shownOf y.1 asks) = _
  rw [hy]
  show some (shownOf y.1 asks) = _
  rw [shownOf_quiet y.1 asks hp, hyl, hlen]

/-! ## 3 `ExactMember` -/

/-- Conditional on hrs. **`ExactMember` at n rounds in which nothing is sent, the part seated by
`Part.lift` at whatever see, wit, get and set.** -/
theorem quietPart_exact_lift (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (chain firstTree : Nat)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
    (j n : Nat) (rs : List (Fmt.DeclaredRound × List Oracle)) (a : Addr)
    (see : V → V') (wit : W → W') (get : X → Y) (set : X → Y → X)
    (hrs : statedOf rs = List.replicate n ([], [])) :
    ExactMember φ σ chain firstTree On bud
      ⟨j, rs, (quietPart n : Part V' W' Y).lift see wit get set, quietSim a n⟩ := by
  intro ca m front ds asks _ _ hd _ _ _
  exact map_unif_point (some (List.replicate n ⟨[], []⟩)) _ _
    (fun c => shows_quiet φ σ j n rs a see wit get set hrs (c.1, c.2, ca) m ds asks hd)
    (fun _ => rfl)

/-- Conditional on hrs. **`ExactMember` at n rounds in which nothing is sent: the bare part.** -/
theorem quietPart_exact (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (chain firstTree : Nat)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
    (j n : Nat) (rs : List (Fmt.DeclaredRound × List Oracle)) (a : Addr)
    (hrs : statedOf rs = List.replicate n ([], [])) :
    ExactMember φ σ chain firstTree On bud ⟨j, rs, quietPart n, quietSim a n⟩ := by
  have h := quietPart_exact_lift φ σ chain firstTree On bud j n rs a (V' := V) (W' := W) (Y := X)
    id id id (fun x _ => x) hrs
  rw [quietPart_lift] at h
  exact h

end ProofFile.Honest.Small

#print axioms ProofFile.Honest.Small.bind_to_none
#print axioms ProofFile.Honest.Small.play_quietSteps
#print axioms ProofFile.Honest.Small.map_zipIdx_const
#print axioms ProofFile.Honest.Small.shownOf_quiet
#print axioms ProofFile.Honest.Small.mem_zipIdx_fst
#print axioms ProofFile.Honest.Small.stated_quiet
#print axioms ProofFile.Honest.Small.shows_quiet
#print axioms ProofFile.Honest.Small.quietPart_exact_lift
#print axioms ProofFile.Honest.Small.quietPart_exact
