-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
One file of the set of files on the key file's table of joints (Johnson/Desc/Key/KeyBorders.lean).
Johnson/Desc/Key/KeyQuiet.lean: the table of joints of the key file: how a row's law and the frames give the step of the relation and of the promise across one block: general in the row; and from it the nine empty rows whole, from named facts on the readers.
  mem_step_of_rest · mem_step_of_out   what is open behind a block: what was open and is not closed; what it opens
  relAt_back      **proved**, general in the meaning: the claim's half of any row: the relation behind (at the open set that the table computes) gives the relation in front, from: the row's own law at its items (outs and ctx behind ⟹ ins in front) · the frames (an item
                  that is open and not closed rides) · the row's ctx is open and not closed
  Rides O         the frames' facts, guarded by what is open: for each sort of item of O just the readers that it reads agree at the state in front (s) and behind (s')
  holds_rides     **proved**: under Rides O every item of O of the nine sorts that KeyMeaning.meaning₁ fills (plain) rides
  emptyRow_back   **proved**: an empty row's claim's half: the relation at O behind ⟹ the relation at O in front
  rngRows_back    **proved**: rng.0.rows' row, its claim's half, whole: at any row with its ins, outs and ctx: the relation behind ⟹ the relation in front, from KeyLaws.RowsLaidFacts (the five facts) and the frames' facts for what rides
  onAt_fwd        (general in the promise's last letter «free», in front and behind: that is where ties that are no Bool stand; freeAt_fwd: its clause on the stored table rides) **proved**: the promise's half of any row that turns no PIN: the promise in front, the book-keeping's step (a named fact: shape in front ⟹ shape' behind) and the reading's letters unturned ⟹ the promise behind
The oracles in front (y) and behind (y') are two: the rule's strings behind a block are what its stage leaves: the stored table and every tree sent in front pass unturned (Johnson/Desc/Sound/StringsStay.lean), a tree not yet sent need not: StrsStay O y y': the
stored table's cells are the same · the committed word of every message whose pin is open in O is the same. The items that KeyMeaning fills read no string.
What is not here: that any block has the facts (equations on its state: other files' to show) · the book-keeping's step itself · a row that opens or closes a pin (the sendings; the tests) · an error term: these are blocks without a round.
No Mathlib. Nothing on soundness.
-/
import Johnson.Desc.Key.KeyFrames
import Johnson.Desc.Key.KeyOff

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key
open OnBytes

theorem mem_step_of_rest (O : List KItem) (r : KRow) (i : KItem) (hi : i ∈ O) (hn : i ∉ r.ins) : i ∈ stepOpen O r := by
  simp only [stepOpen, List.mem_append, List.mem_filter]
  exact Or.inl ⟨hi, by simp [hn]⟩

theorem mem_step_of_out (O : List KItem) (r : KRow) (i : KItem) (ho : i ∈ r.outs) : i ∈ stepOpen O r := by
  simp only [stepOpen, List.mem_append, List.mem_filter]
  by_cases hc : i ∈ O ∧ (!r.ins.contains i) = true
  · exact Or.inl hc
  · refine Or.inr ⟨ho, ?_⟩
    simp only [Bool.not_eq_true', List.contains_eq_mem, List.mem_filter, decide_eq_false_iff_not]
    exact fun ⟨h1, h2⟩ => hc ⟨h1, by simp [h2]⟩

section
variable {XI P S Cells M Smp Rec : Type} (F : FileDescription XI) (G : Reading (P × S) Cells M Smp Rec) (at_ : Where) (Mg : KMeaning P S (Wit Cells Unit M))

/-- **The claim's half of any row.** a: the record in front; a': behind. -/
theorem relAt_back (r : KRow) (O : List KItem) (a a' : P × S) (y y' : Strs) (w : Wit Cells Unit M)
    (hctx : ∀ i ∈ r.ctx, i ∈ O ∧ i ∉ r.ins)
    (law : (∀ i ∈ r.outs ++ r.ctx, i.holds F G at_ Mg a' y' w) → ∀ i ∈ r.ins, i.holds F G at_ Mg a y w)
    (ride : ∀ i ∈ O, i ∉ r.ins → i.holds F G at_ Mg a' y' w → i.holds F G at_ Mg a y w)
    (h : relAt F G at_ Mg (stepOpen O r) a' y' w) : relAt F G at_ Mg O a y w := by
  intro i hi
  by_cases hin : i ∈ r.ins
  · refine law (fun j hj => ?_) i hin
    rcases List.mem_append.1 hj with ho | hc
    · exact h j (mem_step_of_out O r j ho)
    · exact h j (mem_step_of_rest O r j (hctx j hc).1 (hctx j hc).2)
  · exact ride i hi hin (h i (mem_step_of_rest O r i hi hin))

end

section
variable {XI P S Cells M Smp Rec : Type} (F : FileDescription XI) (G : Reading (P × S) Cells M Smp Rec) (at_ : Where)

/-- **What passes a block unturned of the oracles**, as far as the items of O read them. y: in front; y': behind. -/
structure StrsStay (O : List KItem) (y y' : Strs) : Prop where
  cell : y'.cell = y.cell
  word : ∀ k ∈ pinned O, wordOf F y' (at_ k).1 (at_ k).2 = wordOf F y (at_ k).1 (at_ k).2

theorem mem_pinned (O : List KItem) (k : Nat) (h : KItem.pin k ∈ O) : k ∈ pinned O :=
  List.mem_filterMap.2 ⟨.pin k, h, rfl⟩

theorem member_congr (o : Oracle) (j t : Nat) (y y' : Strs) (z : Smp) (m : M) (hw : wordOf F y' j t = wordOf F y j t) :
    Member F G o j t y' z m ↔ Member F G o j t y z m := by
  unfold Member
  rw [hw]

theorem rides_pin2 (j t : Nat) (a a' : P × S) (y y' : Strs) (w : Wit Cells Unit M) (H : SamePins G a a') (hw : wordOf F y' j t = wordOf F y j t)
    (hu : PIN F G j t a' y' w) : PIN F G j t a y w := by
  obtain ⟨o, z, h1, h2, h3⟩ := hu
  exact ⟨o, z, h1, (H.smp j t).trans h2, (member_congr F G o j t y y' z _ hw).1 h3⟩

/-- rides_pin2 with the samples' agreement asked AT THE ONE SEAT (for a block that lays or strikes a sample elsewhere: a sending; KeyPins.holds_pin_back says the like). -/
theorem rides_pin2_at (j t : Nat) (a a' : P × S) (y y' : Strs) (w : Wit Cells Unit M) (e : G.smp a' j t = G.smp a j t) (hw : wordOf F y' j t = wordOf F y j t)
    (hu : PIN F G j t a' y' w) : PIN F G j t a y w := by
  obtain ⟨o, z, h1, h2, h3⟩ := hu
  exact ⟨o, z, h1, e.symm.trans h2, (member_congr F G o j t y y' z _ hw).1 h3⟩

/-- rides_pinT2 from the record's agreement alone (KeyPins.holds_pinT_back says the like). -/
theorem rides_pinT2_at (a a' : P × S) (y y' : Strs) (w : Wit Cells Unit M) (e : G.recOf a' = G.recOf a) (hc : y'.cell = y.cell) (hu : PINW G a' y' w) : PINW G a y w := by
  obtain ⟨r, h1, h2⟩ := hu
  exact ⟨r, e.symm.trans h1, hc ▸ h2⟩

theorem rides_pinT2 (a a' : P × S) (y y' : Strs) (w : Wit Cells Unit M) (H : SamePins G a a') (hc : y'.cell = y.cell) (hu : PINW G a' y' w) : PINW G a y w := by
  obtain ⟨r, h1, h2⟩ := hu
  exact ⟨r, H.recOf.trans h1, hc ▸ h2⟩

end

/-- The nine sorts of item that KeyMeaning.meaning₁ fills, or that read the reading alone. -/
def plain : KItem → Bool
  | .unmarked | .pinT | .inRange _ | .pin _ | .srow _ | .rows _ | .kclaims _ | .grows | .pile => true
  | _ => false

section
variable {XI P S Cells M Smp Rec : Type} (F : FileDescription XI) (G : Reading (P × S) Cells M Smp Rec) (at_ : Where)
  (K : KPlan) (R : KRead Cells M) (X : KReaders S)
  (near : Nat → P × S → Strs → Prop) (forms worth other : Nat → String → P × S → Strs → Wit Cells Unit M → Prop)

/-- **The frames' facts, guarded by what is open.** -/
structure Rides (O : List KItem) (p : P) (s s' : S) : Prop where
  marked : X.marked s = X.marked s'
  pins : SamePins G (p, s) (p, s')
  stmt : (∃ i ∈ O, (match i with | .srow _ | .rows _ | .grows => true | _ => false) = true) → SameStmt X s s'
  rows : ∀ l, KItem.rows l ∈ O → X.rowsAt s l = X.rowsAt s' l
  keys : ∀ l, KItem.kclaims l ∈ O → X.keysAt s l = X.keysAt s' l
  pile : KItem.pile ∈ O → X.pile s = X.pile s'
  grp : KItem.grows ∈ O → X.grpB s = X.grpB s' ∧
    ∀ (g : Nat) (G' : OnBytes.Group), (X.st s').groups[g]? = some G' → ∃ G₀ : OnBytes.Group, (X.st s).groups[g]? = some G₀ ∧ G₀.rows = G'.rows

local notation "Mg" => meaning₁ K R X near forms worth other

/-- **Every plain item of O rides.** -/
theorem holds_rides (O : List KItem) (p : P) (s s' : S) (y y' : Strs) (w : Wit Cells Unit M) (H : Rides G X O p s s') (Hy : StrsStay F at_ O y y') (i : KItem) (hi : i ∈ O) (hp : plain i = true)
    (hu : i.holds F G at_ (Mg) (p, s') y' w) : i.holds F G at_ (Mg) (p, s) y w := by
  cases i with
  | unmarked => exact rides_unmarked K R X near forms worth other p s s' H.marked hu
  | pinT => exact rides_pinT2 G (p, s) (p, s') y y' w H.pins Hy.cell hu
  | inRange l => exact hu
  | pin k => exact rides_pin2 F G _ _ (p, s) (p, s') y y' w H.pins (Hy.word k (mem_pinned O k hi)) hu
  | near k => simp [plain] at hp
  | srow k => exact rides_srow K R X near forms worth other k p s s' y w (H.stmt ⟨_, hi, rfl⟩) hu
  | forms l r => simp [plain] at hp
  | worth l x => simp [plain] at hp
  | rows l => exact rides_rows K R X near forms worth other l p s s' y w (H.stmt ⟨_, hi, rfl⟩) (H.rows l hi) hu
  | kclaims l => exact rides_kclaims K R X near forms worth other l p s s' y w (H.keys l hi) hu
  | grows => exact rides_grows K R X near forms worth other p s s' y w (H.stmt ⟨_, hi, rfl⟩) (H.grp hi).1 (H.grp hi).2 hu
  | pile => exact rides_pile K R X near forms worth other p s s' y w (H.pile hi) hu
  | claim c n => simp [plain] at hp

/-- **An empty row's claim's half.** -/
theorem emptyRow_back (O : List KItem) (hO : ∀ i ∈ O, plain i = true) (p : P) (s s' : S) (y y' : Strs) (w : Wit Cells Unit M) (H : Rides G X O p s s') (Hy : StrsStay F at_ O y y')
    (h : relAt F G at_ (Mg) O (p, s') y' w) : relAt F G at_ (Mg) O (p, s) y w :=
  fun i hi => holds_rides F G at_ K R X near forms worth other O p s s' y y' w H Hy i hi (hO i hi) (h i hi)

/-- **rng.0.rows' row: its claim's half.** r: the table's row there (rows₁ n at 2 + 6 n): said by its three lists. -/
theorem rngRows_back (n : Nat) (r : KRow) (hins : r.ins = (List.range n).map KItem.rows ++ [.srow 1]) (houts : r.outs = [.grows]) (hctx : r.ctx = [.pin 1])
    (O : List KItem) (hO : ∀ i ∈ O, plain i = true) (hpin : KItem.pin 1 ∈ O) (p : P) (s s' : S) (y y' : Strs) (w : Wit Cells Unit M)
    (Hf : RowsLaidFacts K X n s s') (Hr : Rides G X (O.filter fun i => !r.ins.contains i) p s s') (Hy : StrsStay F at_ (O.filter fun i => !r.ins.contains i) y y')
    (h : relAt F G at_ (Mg) (stepOpen O r) (p, s') y' w) : relAt F G at_ (Mg) O (p, s) y w := by
  refine relAt_back F G at_ (Mg) r O (p, s) (p, s') y y' w ?_ ?_ ?_ h
  · intro i hi
    rw [hctx] at hi
    have e : i = .pin 1 := by simpa using hi
    subst e
    refine ⟨hpin, ?_⟩
    rw [hins]
    simp
  · intro hb i hi
    have hg : (Mg).grows (p, s') y' w := hb .grows (by rw [houts]; simp)
    obtain ⟨h1, h2⟩ := rngRows_tie K R X near forms worth other n p s s' y w Hf hg
    rw [hins] at hi
    rcases List.mem_append.1 hi with ha | hb'
    · obtain ⟨l, hl, e⟩ := List.mem_map.1 ha
      subst e
      exact h1 l (List.mem_range.1 hl)
    · have e : i = .srow 1 := by simpa using hb'
      subst e
      exact h2
  · intro i hi hn hu
    exact holds_rides F G at_ K R X near forms worth other _ p s s' y y' w Hr Hy i (List.mem_filter.2 ⟨hi, by simp [hn]⟩) (hO i hi) hu

/-- **The promise's half of a row that turns no pin.** shape | shape': the book-keeping in front | behind. -/
theorem onAt_fwd (shape shape' : S → Bool) (free free' : P × S → Strs → Prop) (O O' : List KItem) (hpin : pinned O' = pinned O) (p : P) (s s' : S) (y y' : Strs)
    (hm : X.marked s = X.marked s') (hP : SamePins G (p, s) (p, s')) (Hy : StrsStay F at_ O y y') (hfree : free (p, s) y → free' (p, s') y') (step : shape s = true → shape' s' = true)
    (h : onAt F G at_ (Mg) shape free O (p, s) y) : onAt F G at_ (Mg) shape' free' O' (p, s') y' := by
  cases h with
  | inl hn => exact Or.inl fun hu => hn (hm.trans hu)
  | inr hr =>
    obtain ⟨h1, h2, h3, h4⟩ := hr
    refine Or.inr ⟨step h1, ?_, hfree h3, ?_⟩
    · rw [hpin]
      have e : (fun k => hasSmp G (at_ k).1 (at_ k).2 (p, s')) = fun k => hasSmp G (at_ k).1 (at_ k).2 (p, s) :=
        funext fun k => by simp only [hasSmp, hP.smp]
      rw [e]; exact h2
    · intro k hk o z ho hz m m' hm1 hm2
      rw [hpin] at hk
      exact h4 k hk o z ho ((hP.smp _ _).trans hz) m m' ((member_congr F G o _ _ y y' z m (Hy.word k hk)).1 hm1) ((member_congr F G o _ _ y y' z m' (Hy.word k hk)).1 hm2)

/-- The promise's clause on the stored table rides where the reading's letters and the cells do. -/
theorem freeAt_fwd (coll : Strs → Rec → Prop) (p : P) (s s' : S) (y y' : Strs) (hP : SamePins G (p, s) (p, s')) (hcoll : ∀ r, coll y' r → coll y r)
    (h : FreeAt G coll (p, s) y) : FreeAt G coll (p, s') y' := by
  obtain ⟨r, hr1, hr2⟩ := h
  exact ⟨r, hP.recOf.symm.trans hr1, fun hc => hr2 (hcoll r hc)⟩

end

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.relAt_back
#print axioms VerifiableInference.Desc.Key.holds_rides
#print axioms VerifiableInference.Desc.Key.emptyRow_back
#print axioms VerifiableInference.Desc.Key.rngRows_back
#print axioms VerifiableInference.Desc.Key.onAt_fwd

-- the table's own row at 2 + 6 n has these three lists: due «true», at two and at three lookups
#eval [2, 3].all fun n => ((VerifiableInference.Desc.Key.rows₁ n)[2 + 6 * n]?).any fun r =>
  decide (r.ins = (List.range n).map VerifiableInference.Desc.Key.KItem.rows ++ [.srow 1]) && decide (r.outs = [.grows]) && decide (r.ctx = [.pin 1])
-- every item that is open at a border in front of an empty row, or in front of rng.0.rows, is plain: due «true»
#eval (((VerifiableInference.Desc.Key.openSets (VerifiableInference.Desc.Key.rows₁ 2) (VerifiableInference.Desc.Key.start₁ 2)).zipIdx.filter fun x => [2, 3, 6, 7, 8, 9, 12, 13, 14, 18].contains x.2).all fun x => x.1.all VerifiableInference.Desc.Key.plain)
-- control: at the border between K3 and the layer not: due «false»
#eval (((VerifiableInference.Desc.Key.openSets (VerifiableInference.Desc.Key.rows₁ 2) (VerifiableInference.Desc.Key.start₁ 2))[5]?).any fun O => O.all VerifiableInference.Desc.Key.plain)
