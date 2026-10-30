-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Parts/OwnedPlays.lean: the honest side of the kind "lookup" (K3):
THE ROW WITH A LETTER FOR THE OWNERS OF ITS STRETCHES (Honest/K3/RowOwned.lean) PLAYS AS THE ROW OF
Honest/K3/Row.lean DOES: at every letter the two seated rows yield THE SAME LIST OF STEPS, at coins
that hold the same field elements. So every law on the play of Honest/K3/Row.lean's row that holds
at all
coins holds of the owned row. Definitions and theorems.

  `reHand`            what one part is handed of coins, laid into another part's type: no cast
  `Twin p q`          the two parts stop alike, and say and hand on the same at such coins; what is
                      spent is the same field elements
  `steps_twin`        twins have the same steps
  `twin_sum`, `twin_quiet`, `twin_lift`, `twin_part`   the masked sumcheck's part under two pairs of
                      names; a stage that sends nothing; a seated part; a stage's part at two
                      letters
  `reRow`, `rowSteps_twin`, `rowSpent_twin`   a row of twins
  `plainOf`           the owned seated row's coins as coins of Honest/K3/Row.lean's seated row
  `steps_owned`, `placed_owned`, `spent_owned`   **the bridge**

Why it holds. A stretch's name enters the type of a part's coins, which reads the counts alone, and
the book's lending; the part's moves read their coins through two lists of field elements and the
names not at all (`sumPart_coins`, Honest/K3/Law/SumFits.lean).

Limits. On the play alone: the book's lending, which does read the names, is another file's. Nothing
on any property.

-/
import Johnson.Desc.ProofFile.Honest.K3.RowOwned
import Johnson.Desc.ProofFile.Honest.K3.Law.RowSeated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Parts
open VerifiableInference.Desc (Block Place Oracle)
open ProofFile.Honest.K3.Law

variable {V V' W W' X Y : Type}

/-! ## 1 Twins -/

/-- What one part is handed of coins, laid into another part's type: coin by coin of the extension
field; no cast. -/
def reHand (p q : Part V W X) (c : p.Coins) : q.Coins :=
  (fillCs q.takes (readCs c.1), fillRuns q.spends (readRuns p.spends c.2.1),
    fillRuns q.carries (readRuns p.carries c.2.2))

/-- **The two parts stop alike, and say and hand on the same at coins that hold the same field
elements; what is spent is the same.** -/
structure Twin (p q : Part V W X) : Prop where
  bad : p.bad = q.bad
  hid : p.hid = q.hid
  same : ∀ c, SameSays c (reHand p q c) p.moves q.moves
  spent : ∀ c, csAllE q.spends (reHand p q c).2.1 = csAllE p.spends c.2.1

/-- A list zipped with moves, numbered, reads the moves through what they say and hand on alone. -/
theorem zip_says {α β γ δ : Type} (φ : β → γ) (g : α → γ → Nat → δ) (rs : List α) (ms : List β) :
    (rs.zip ms).zipIdx.map (fun r => g r.1.1 (φ r.1.2) r.2) =
      (rs.zip (ms.map φ)).zipIdx.map fun r => g r.1.1 r.1.2 r.2 := by
  rw [List.zip_map_right, List.zipIdx_map, List.map_map]
  rfl

/-- **Twins have the same steps.** CONDITIONAL ON `Twin`. -/
theorem steps_twin {p q : Part V W X} (h : Twin p q) (name : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (v : Option V) (c : p.Coins) :
    p.steps name a rs v c = q.steps name a rs v (reHand p q c) := by
  have hl : p.moves.length = q.moves.length := by
    have e := congrArg List.length (h.same c)
    rwa [List.length_map, List.length_map] at e
  unfold Part.steps
  rw [h.bad, h.hid, hl]
  have e1 := zip_says (fun mv : Move p.Coins W X => (mv.say c, mv.hand))
    (fun (r : Fmt.DeclaredRound × List Oracle) (y : _ × _) (n : Nat) =>
      (⟨name, a, r.1, r.2, q.bad, fun f o => v.bind fun w => q.hid w f o, n,
        n + 1 == q.moves.length, some ⟨fun _ => y.1, y.2⟩⟩ : Step W X)) rs p.moves
  have e2 := zip_says (fun mv : Move q.Coins W X => (mv.say (reHand p q c), mv.hand))
    (fun (r : Fmt.DeclaredRound × List Oracle) (y : _ × _) (n : Nat) =>
      (⟨name, a, r.1, r.2, q.bad, fun f o => v.bind fun w => q.hid w f o, n,
        n + 1 == q.moves.length, some ⟨fun _ => y.1, y.2⟩⟩ : Step W X)) rs q.moves
  refine e1.trans (Eq.trans ?_ e2.symm)
  rw [show p.moves.map (fun mv => (mv.say c, mv.hand)) =
    q.moves.map (fun mv => (mv.say (reHand p q c), mv.hand)) from h.same c]

/-! ## 2 The lookup's parts -/

/-- The masked sumcheck's part under two pairs of names. -/
theorem twin_sum (n e n' e' : String) (J : SumJob W X) :
    Twin (sumPart (V := V) n e J) (sumPart (V := V) n' e' J) := by
  refine ⟨rfl, rfl, fun c => sumPart_coins n e n' e' J c _ ?_ ?_, fun c => ?_⟩
  · exact (coinsE_fill c.2.1.1 rfl).symm
  · obtain ⟨⟨lead, vs, ends⟩, points, ld, round, inY, endsF⟩ := J
    cases ends with
    | none => rfl
    | some x => exact (coinsE_fill (d' := ⟨0, x.n⟩) c.2.1.2.1 rfl).symm
  · refine csAllE_fill _ _ c.2.1 ?_
    obtain ⟨⟨lead, vs, ends⟩, points, ld, round, inY, endsF⟩ := J
    cases ends <;> rfl

/-- A stage that sends nothing. -/
theorem twin_quiet : Twin (quiet : Part V W Unit) quiet := ⟨rfl, rfl, fun _ => rfl, fun _ => rfl⟩

/-- A seated part. CONDITIONAL ON `Twin` of the parts that are seated. -/
theorem twin_lift (see : V → V') (wit : W → W') (get : X → Y) (set : X → Y → X)
    {p q : Part V' W' Y} (h : Twin p q) :
    Twin (p.lift see wit get set) (q.lift see wit get set) := by
  refine ⟨h.bad, by show (fun v => p.hid (see v)) = fun v => q.hid (see v); rw [h.hid],
    fun c => ?_, h.spent⟩
  have e := h.same c
  unfold SameSays at e ⊢
  have e' := congrArg (List.map fun (y : (Seen → State W' Y → Except String Sending) ×
      (State W' Y → Y)) =>
    ((fun (s : Seen) (t : State W X) => y.1 s (t.narrow wit get)),
      fun (t : State W X) => set t.own (y.2 (t.narrow wit get)))) e
  rw [List.map_map, List.map_map] at e'
  show (p.moves.map (Move.lift wit get set)).map _ = (q.moves.map (Move.lift wit get set)).map _
  rw [List.map_map, List.map_map]
  exact e'

/-- A stage's part at two letters for the owners. -/
theorem twin_part (o o' : Owners) (R : Reads) (J : LookJobs W) (a : At) (s : Stage) (i : Nat) :
    Twin (partOfOwned (V := V) o R J a s i) (partOfOwned (V := V) o' R J a s i) := by
  unfold partOfOwned
  cases s.call a.face with
  | none => exact twin_quiet
  | some k => exact twin_sum _ _ _ _ _

/-! ## 3 Rows -/

section
variable {α : Type}

/-- A row's coins, part by part, laid into another row's type. f, f': the two rows' parts, of one
list; g: the seat. -/
def reRow (f f' : α → Part V' W' Y) (g : Part V' W' Y → Part V W X) :
    (l : List α) → RowCoins ((l.map f).map g) → RowCoins ((l.map f').map g)
  | [], _ => ()
  | x :: l, c =>
    let c' : (g (f x)).Coins × RowCoins ((l.map f).map g) := c
    (reHand (g (f x)) (g (f' x)) c'.1, reRow f f' g l c'.2)

/-- **A row of twins has the same steps.** CONDITIONAL ON `Twin`, part by part. -/
theorem rowSteps_twin (f f' : α → Part V' W' Y) (g : Part V' W' Y → Part V W X)
    (h : ∀ x, Twin (g (f x)) (g (f' x))) (name : String) (a : Place) (v : Option V) :
    ∀ (l : List α) (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle))
      (c : RowCoins ((l.map f).map g)),
      rowSteps name a v ((l.map f).map g) j rs c =
        rowSteps name a v ((l.map f').map g) j rs (reRow f f' g l c)
  | [], _, _, _ => rfl
  | x :: l, j, rs, c => by
    let c' : (g (f x)).Coins × RowCoins ((l.map f).map g) := c
    have hl : (g (f x)).moves.length = (g (f' x)).moves.length := by
      have e := congrArg List.length ((h x).same c'.1)
      rwa [List.length_map, List.length_map] at e
    show (g (f x)).steps name ⟨a, j⟩ (rs.take (g (f x)).moves.length) v c'.1 ++
        rowSteps name a v ((l.map f).map g) (j + 1) (rs.drop (g (f x)).moves.length) c'.2 =
      (g (f' x)).steps name ⟨a, j⟩ (rs.take (g (f' x)).moves.length) v
          (reHand (g (f x)) (g (f' x)) c'.1) ++
        rowSteps name a v ((l.map f').map g) (j + 1) (rs.drop (g (f' x)).moves.length)
          (reRow f f' g l c'.2)
    rw [steps_twin (h x), rowSteps_twin f f' g h name a v l, hl]

/-- What a row of twins spends is the same field elements. CONDITIONAL ON `Twin`, part by part. -/
theorem rowSpent_twin (f f' : α → Part V' W' Y) (g : Part V' W' Y → Part V W X)
    (h : ∀ x, Twin (g (f x)) (g (f' x))) :
    ∀ (l : List α) (c : RowCoins ((l.map f).map g)),
      rowSpent ((l.map f').map g) (reRow f f' g l c) = rowSpent ((l.map f).map g) c
  | [], _ => rfl
  | x :: l, c => by
    let c' : (g (f x)).Coins × RowCoins ((l.map f).map g) := c
    show csAllE (g (f' x)).spends (reHand (g (f x)) (g (f' x)) c'.1).2.1 ::
        rowSpent ((l.map f').map g) (reRow f f' g l c'.2) =
      csAllE (g (f x)).spends c'.1.2.1 :: rowSpent ((l.map f).map g) c'.2
    rw [(h x).spent, rowSpent_twin f f' g h l]

end

/-! ## 4 The bridge -/

section
variable {V₁ W₁ X₁ : Type}

/-- The seated row's coins at one letter for the owners, as its coins at another. -/
def reOwned (o o' : Owners) (R : Reads) (J : LookJobs W) (wit : W₁ → W) (a : At)
    (c : RowCoins (proverSideOfLookupInChain (V₁ := V₁) (X₁ := X₁) o R J wit a).parts) :
    RowCoins (proverSideOfLookupInChain (V₁ := V₁) (X₁ := X₁) o' R J wit a).parts :=
  reRow (fun x : Stage × Nat => partOfOwned (V := Unit) o R J a x.1 x.2)
    (fun x => partOfOwned (V := Unit) o' R J a x.1 x.2)
    (Part.lift (fun _ => ()) wit (fun _ => ()) fun x _ => x) (stages a.face).zipIdx c

/-- **The owned seated row's coins as coins of Honest/K3/Row.lean's seated row.** -/
def plainOf (o : Owners) (R : Reads) (J : LookJobs W) (wit : W₁ → W) (a : At)
    (c : RowCoins (proverSideOfLookupInChain (V₁ := V₁) (X₁ := X₁) o R J wit a).parts) :
    RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) R J wit a).parts :=
  reOwned o oneOwner R J wit a c

/-- **THE BRIDGE: the two seated rows yield the same list of steps.** No premise. -/
theorem steps_owned (o : Owners) (R : Reads) (J : LookJobs W) (wit : W₁ → W) (a : At)
    (name : String) (p : Place) (v : Option V₁) (j : Nat)
    (rs : List (Fmt.DeclaredRound × List Oracle))
    (c : RowCoins (proverSideOfLookupInChain (V₁ := V₁) (X₁ := X₁) o R J wit a).parts) :
    rowSteps name p v (proverSideOfLookupInChain o R J wit a).parts j rs c =
      rowSteps name p v (proverSideOfLookupInChainAtOneOwner R J wit a).parts j rs (plainOf o R J wit a c) :=
  rowSteps_twin (fun x : Stage × Nat => partOfOwned (V := Unit) o R J a x.1 x.2)
    (fun x => partOfOwned (V := Unit) oneOwner R J a x.1 x.2)
    (Part.lift (fun _ => ()) wit (fun _ => ()) fun x _ => x)
    (fun x => twin_lift _ _ _ _ (twin_part o oneOwner R J a x.1 x.2)) name p v
    (stages a.face).zipIdx j rs c

/-- The same at a sub-protocol's rounds. -/
theorem placed_owned {S Cl : Type} (o : Owners) (R : Reads) (J : LookJobs W) (wit : W₁ → W) (a : At)
    (b : Block S Cl) (v : Option V₁)
    (c : RowCoins (proverSideOfLookupInChain (V₁ := V₁) (X₁ := X₁) o R J wit a).parts) :
    (proverSideOfLookupInChain o R J wit a).steps b v c =
      (proverSideOfLookupInChainAtOneOwner R J wit a).steps b v (plainOf o R J wit a c) :=
  steps_owned o R J wit a b.name b.place v 0 _ c

/-- What is spent is the same field elements, part by part, stretch by stretch. -/
theorem spent_owned (o : Owners) (R : Reads) (J : LookJobs W) (wit : W₁ → W) (a : At)
    (c : RowCoins (proverSideOfLookupInChain (V₁ := V₁) (X₁ := X₁) o R J wit a).parts) :
    rowSpent _ (plainOf o R J wit a c) = rowSpent _ c :=
  rowSpent_twin (fun x : Stage × Nat => partOfOwned (V := Unit) o R J a x.1 x.2)
    (fun x => partOfOwned (V := Unit) oneOwner R J a x.1 x.2)
    (Part.lift (fun _ => ()) wit (fun _ => ()) fun x _ => x)
    (fun x => twin_lift _ _ _ _ (twin_part o oneOwner R J a x.1 x.2)) (stages a.face).zipIdx c

end

#print axioms ProofFile.Honest.K3.Parts.zip_says
#print axioms ProofFile.Honest.K3.Parts.steps_twin
#print axioms ProofFile.Honest.K3.Parts.twin_sum
#print axioms ProofFile.Honest.K3.Parts.twin_quiet
#print axioms ProofFile.Honest.K3.Parts.twin_lift
#print axioms ProofFile.Honest.K3.Parts.twin_part
#print axioms ProofFile.Honest.K3.Parts.rowSteps_twin
#print axioms ProofFile.Honest.K3.Parts.rowSpent_twin
#print axioms ProofFile.Honest.K3.Parts.steps_owned
#print axioms ProofFile.Honest.K3.Parts.placed_owned
#print axioms ProofFile.Honest.K3.Parts.spent_owned

end ProofFile.Honest.K3.Parts
