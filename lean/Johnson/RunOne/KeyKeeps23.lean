-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyKeeps23.lean, OVER KeyRows23At.lean (THIS FILE HOLDS WHAT IS GENERAL IN THE BLOCK (held_same · same_keeps · CellOnly · freeAt_rides · the rides · keeps₂_01 | keeps₂_1112 | keeps₃_12 | keeps₃_34) AND IMPORTS NO KeyCut23; WHAT UNFOLDS THE SEATED BLOCKS' TEXTS (front₂_same … end₃_keeps) LIES IN KeyKeepsAt23.lean: so the wraps stand over whichever text of the key file's description's blocks lies beneath) («shown» rides by the word at the seat; fits | mask₁ | maskU | maskW ride with the record) («order» rides with the record) («reads» rides: it is on letters alone) (AT 3.3 THE END's YES IS SPENT: end₃_yes: it is fin₃, which the last border's book-keeping holds) (the fence on the rows' content rides with the record) (Free₂ | Free₃ ride field by field: the record does not turn; the open sets' pins do not turn) (the last chain's book-keeping stands in the promise's own slot and reads the own record; AT 3.1 THE BOOK-KEEPING's STEP 1 → 2 IS THE BLOCK's OWN YES) (the ties ride with the record; AT 3.1 THE BLOCK's YES IS SPENT: the promise behind it holds the sources' test). THE PLAIN ROAD's LAW OF A BLOCK («Keeps», Johnson/Desc/Plain/Leads.lean; what Plain/FoldChain.lean's EachKeeps asks block by block) FOR THE FOUR BLOCKS OF THE KEY FILE's SHARED AND LAST CHAIN THAT HAND THE RECORD ON AS IT IS:
the shared chain's front (2.0) · the end of chain 2 (2.11) · the taken trees' sources (3.1) · the end of chain 3 (3.3): at the table's own promises and claims on₂ | L₂ | on₃ | L₃ (KeyRows23At.lean), at ANY list of errors: what holds for certain costs nothing.
  held_same          a piece's block, as the maker holds it (the test «below the prime» in front; lifted to the rule's record), hands on what it was handed wherever the description's block does
  same_keeps         PROVED, general in the meaning, the book-keeping and the promise's free clause: a block that hands the record on as it is keeps a border whose open set does not turn: FROM: the pinned messages' trees lie below the piece's base · the book-keeping's step ·
                     the free clause rides along the strings · every open item rides back along the strings
  rides₃ (rides₂: in KeyWrap23.lean)    PROVED: at the open sets of these four borders every item rides back: none but pinT and the pins reads a string
  front₂_keeps · end₂_keeps · sources₃_keeps · end₃_keeps   PROVED, in KeyKeepsAt23.lean: the four laws, for a piece that holds the block
WHAT IS OWED BESIDE: that the pinned messages' trees lie below the piece's base (the tiling's numbers and the letter at_) · coll reads the stored table's cells alone (CellOnly).
EMPTY WHERE: the promise in front holds of nothing; the block refuses all. The two ends DO test (nothing is left untested): their yes is not used here: a law of a block that hands the record on needs none.
Limits. Four of sixteen blocks. No error term is spent. Nothing on soundness.

-/
import Johnson.RunOne.KeySeams23
import Johnson.Desc.Key.KeyKeeps
import Johnson.Desc.Plain.PaidKeeps


set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK)
open _root_.Iop (Reduction)

/-- As the maker holds a description's block. -/
abbrev heldB {P σ Cl : Type} (b : Block σ Cl) : Block (P × σ) Cl := Block.lift Prod.snd (fun t s => (t.1, s)) (below b)

theorem held_same {P σ Cl : Type} (b : Block σ Cl) (h : ∀ s rs gs s', b.decide s rs gs = .ok s' → s' = s)
    (a : P × σ) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (a' : P × σ) (hd : (heldB b : Block (P × σ) Cl).decide a rs gs = .ok a') : a' = a := by
  have hd' : ((if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then b.decide a.2 rs gs else .error "a word is not below the prime").map fun s => (a.1, s)) = .ok a' := hd
  split at hd'
  · cases hb : b.decide a.2 rs gs with
    | error e => rw [hb] at hd'; cases hd'
    | ok s' =>
      rw [hb] at hd'
      have e : (a.1, s') = a' := Except.ok.inj hd'
      rw [← e, h _ _ _ _ hb]
  · cases hd'

section
variable {XI P S Cells M Smp Rec Cl W : Type} {C : CK} (F : FileDescription XI) (Fr : Frame) (G : Reading (P × S) Cells M Smp Rec) (at_ : Where)
  (Mg : KMeaning P S (Wit Cells Unit M))

/-- **A block that hands the record on as it is, at a border whose open set does not turn.** -/
theorem same_keeps (pc : Piece C Fr (P × S) Cl W) (shape shape' : S → Bool) (free free' : P × S → Strs → Prop) (O : List KItem)
    (hbase : ∀ k ∈ pinned O, (at_ k).1 < pc.base)
    (hid : ∀ a rs gs b, pc.b.decide a rs gs = .ok b → b = a)
    (hshape : ∀ a : P × S, (∃ rs gs, pc.b.decide a rs gs = .ok a) → shape a.2 = true → shape' a.2 = true)
    (hfree : ∀ a y y', (∃ rs gs, pc.b.decide a rs gs = .ok a) → StrsStay F at_ O y y' → free a y → free' a y')
    (hitems : ∀ i ∈ O, ∀ a y y' w, StrsStay F at_ O y y' → i.holds F G at_ Mg a y' w → i.holds F G at_ Mg a y w) :
    pc.ior.red.Keeps (fun x => onAt F G at_ Mg shape free O x.1 (strsOf Fr x.2)) (fun x => onAt F G at_ Mg shape' free' O x.1 (strsOf Fr x.2))
      (fun x => ∃ w, relAt F G at_ Mg O x.1 (strsOf Fr x.2) w) (fun x => ∃ w, relAt F G at_ Mg O x.1 (strsOf Fr x.2) w) pc.err :=
  Reduction.Leads.of_sure (K := pc.ior.red) pc.err fun a τ b ha hb => by
    have hd := piece_decides_at pc a τ b hb
    have e : b.1 = a.1 := hid _ _ _ _ hd
    rw [e] at hd
    have Hy := strsStay_of_out F Fr at_ pc O hbase a b τ hb
    refine ⟨?_, fun ⟨w, hw⟩ => ⟨w, fun i hi => hitems i hi a.1 _ _ w Hy (e ▸ hw i hi)⟩⟩
    show onAt F G at_ Mg shape' free' O b.1 (strsOf Fr b.2)
    rw [e]
    cases ha with
    | inl hn => exact Or.inl hn
    | inr hr =>
      obtain ⟨h1, h2, h3, h4⟩ := hr
      refine Or.inr ⟨hshape _ ⟨_, _, hd⟩ h1, h2, hfree _ _ _ ⟨_, _, hd⟩ Hy h3, fun k hk o z ho hz m m' hm hm' => ?_⟩
      exact h4 k hk o z ho hz m m' ((member_congr F G o _ _ _ _ z m (Hy.word k hk)).1 hm) ((member_congr F G o _ _ _ _ z m' (Hy.word k hk)).1 hm')

end

/-- A letter on the strings that reads the stored table's cells alone. -/
def CellOnly {α : Type} (f : Strs → α → Prop) : Prop := ∀ y y' x, y'.cell = y.cell → (f y' x ↔ f y x)

section
variable {XI Cells M Smp Rec Cl W : Type} {C : CK} (F : FileDescription XI) (Fr₂ Fr₃ : Frame)
  (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (G₃ : Reading (P₃ × St₃) Cells M Smp Rec) (at_ : Where)
  (S : LinShape) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad a : Nat) (idx : List Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (src : St₃ → Bool) (off₂ off₃ : Nat → Nat) (t₁ : Nat)

theorem freeAt_rides {A : Type} (G : Reading A Cells M Smp Rec) (hc : CellOnly coll) (z : A) (y y' : Strs) (h : y'.cell = y.cell)
    (hf : ∃ r, G.recOf z = some r ∧ ¬ coll y r) : ∃ r, G.recOf z = some r ∧ ¬ coll y' r := by
  obtain ⟨r, h1, h2⟩ := hf
  exact ⟨r, h1, fun h3 => h2 ((hc y y' r h).1 h3)⟩

/-- At the shared chain's first border every open item rides back along the strings. -/
theorem rides₂_seam (i : KItem) (hi : i ∈ seam) (z : P₂ × St₂) (y y' : Strs) (w : Wit Cells Unit M) (Hy : StrsStay F at_ seam y y')
    (hu : i.holds F G₂ at_ (meaning₂ S K₁ R enc rad) z y' w) : i.holds F G₂ at_ (meaning₂ S K₁ R enc rad) z y w := by
  have hi' := hi
  simp only [seam, List.mem_cons, List.mem_nil_iff, or_false] at hi'
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hu
  · exact rides_pinT2 G₂ z z y y' w ⟨fun _ _ => rfl, rfl⟩ Hy.cell hu
  · exact rides_pin2 F G₂ _ _ z z y y' w ⟨fun _ _ => rfl, rfl⟩ (Hy.word 0 (by decide)) hu
  · exact hu
  · exact hu
  · exact rides_pin2 F G₂ _ _ z z y y' w ⟨fun _ _ => rfl, rfl⟩ (Hy.word 2 (by decide)) hu
  · exact hu

/-- At its last border. -/
theorem rides₂_end (i : KItem) (hi : i ∈ end₂) (z : P₂ × St₂) (y y' : Strs) (w : Wit Cells Unit M) (Hy : StrsStay F at_ end₂ y y')
    (hu : i.holds F G₂ at_ (meaning₂ S K₁ R enc rad) z y' w) : i.holds F G₂ at_ (meaning₂ S K₁ R enc rad) z y w := by
  have hi' := hi
  simp only [end₂, List.mem_cons, List.mem_nil_iff, or_false] at hi'
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hu
  · exact rides_pin2 F G₂ _ _ z z y y' w ⟨fun _ _ => rfl, rfl⟩ (Hy.word 0 (by decide)) hu
  · exact hu
  · exact rides_pin2 F G₂ _ _ z z y y' w ⟨fun _ _ => rfl, rfl⟩ (Hy.word 2 (by decide)) hu
  · exact hu
  · simpa [KItem.holds, meaning₂, claim₂] using hu
  · exact rides_pin2 F G₂ _ _ z z y y' w ⟨fun _ _ => rfl, rfl⟩ (Hy.word 4 (by decide)) hu
  · exact hu
  · simpa [KItem.holds, meaning₂, claim₂] using hu

/-- On the last chain no item but a pin reads a string. -/
theorem rides₃ (O : List KItem) (hT : KItem.pinT ∉ O) (i : KItem) (hi : i ∈ O) (z : P₃ × St₃) (y y' : Strs) (w : Wit Cells Unit M) (Hy : StrsStay F at_ O y y')
    (hu : i.holds F G₃ at_ (meaning₃ S K₁ R) z y' w) : i.holds F G₃ at_ (meaning₃ S K₁ R) z y w := by
  cases i with
  | pinT => exact absurd hi hT
  | pin k => exact rides_pin2 F G₃ _ _ z z y y' w ⟨fun _ _ => rfl, rfl⟩ (Hy.word k (mem_pinned O k hi)) hu
  | _ => exact hu

theorem open₂_1 : open₂ 1 = seam := by decide
theorem open₂_11 : open₂ 11 = end₂ := by decide
theorem open₃_12 : open₃ 2 = open₃ 1 := by decide
theorem open₃_3 : open₃ 3 = [.unmarked] := by decide
theorem pinT_open₃_1 : KItem.pinT ∉ open₃ 1 := by decide

theorem shape₂_01 (d : St₂) : LKFU.Shape23.shape₂ S a 1 d = LKFU.Shape23.shape₂ S a 0 d := rfl
theorem shape₂_1112 (d : St₂) : LKFU.Shape23.shape₂ S a 12 d = LKFU.Shape23.shape₂ S a 11 d := rfl
theorem shape₃_12 (n g t : Nat) (s : St₃) : LKFU.Shape23.shape₃ S a n g t idx 2 s = LKFU.Shape23.shape₃ S a n g t idx 1 s := rfl
theorem shape₃_34 (n g t : Nat) (s : St₃) : LKFU.Shape23.shape₃ S a n g t idx 4 s = LKFU.Shape23.shape₃ S a n g t idx 3 s := rfl

/-- **A block of the shared chain that hands the record on, between the borders 0 and 1.** -/
theorem keeps₂_01 (pc : Piece C Fr₂ (P₂ × St₂) Cl W) (hid : ∀ z rs gs z', pc.b.decide z rs gs = .ok z' → z' = z)
    (hbase : ∀ k ∈ pinned seam, (at_ k).1 < pc.base) (hc : CellOnly coll) :
    pc.ior.red.Keeps (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 0) (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 1)
      (L₂ F Fr₂ G₂ at_ S K₁ R enc rad 0) (L₂ F Fr₂ G₂ at_ S K₁ R enc rad 1) pc.err := by
  have h := same_keeps F Fr₂ G₂ at_ (meaning₂ S K₁ R enc rad) pc (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 0 d)) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 1 d))
    (Free₂ F G₂ at_ S K₁ R coll last₁ off₂ 0) (Free₂ F G₂ at_ S K₁ R coll last₁ off₂ 1) seam hbase hid (fun _ _ hs => hs)
    (fun z y y' _ Hy hf => { hf with
      record := freeAt_rides coll G₂ hc z y y' Hy.cell hf.record
      lay := fun h3 => absurd h3 (by decide)
      placed := by rw [open₂_1, ← open₂_first]; exact hf.placed
      samples := by rw [open₂_1, ← open₂_first]; exact hf.samples
      rowsIn := fun h2 => absurd h2 (by decide)
      linOk := fun h2 => absurd h2 (by decide)
      seatU := fun h2 => absurd h2 (by decide)
      seatOmega := fun h2 => absurd h2 (by decide)
      shown := fun j hj => by
        rw [open₂_1] at hj
        exact shownAt_ride F at_ j y y' (Hy.word j hj) (hf.shown j (by rw [open₂_first]; exact hj))
      maskU := fun h2 => absurd h2 (by decide) })
    (fun i hi z y y' w Hy hu => rides₂_seam F G₂ at_ S K₁ R enc rad i hi z y y' w Hy hu)
  unfold on₂ L₂ R₂
  rw [open₂_first, open₂_1]
  exact h

/-- **Between the borders 11 and 12.** -/
theorem keeps₂_1112 (pc : Piece C Fr₂ (P₂ × St₂) Cl W) (hid : ∀ z rs gs z', pc.b.decide z rs gs = .ok z' → z' = z)
    (hbase : ∀ k ∈ pinned end₂, (at_ k).1 < pc.base) (hc : CellOnly coll) :
    pc.ior.red.Keeps (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 11) (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 12)
      (L₂ F Fr₂ G₂ at_ S K₁ R enc rad 11) (L₂ F Fr₂ G₂ at_ S K₁ R enc rad 12) pc.err := by
  have h := same_keeps F Fr₂ G₂ at_ (meaning₂ S K₁ R enc rad) pc (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 11 d)) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 12 d))
    (Free₂ F G₂ at_ S K₁ R coll last₁ off₂ 11) (Free₂ F G₂ at_ S K₁ R coll last₁ off₂ 12) end₂ hbase hid (fun _ _ hs => hs)
    (fun z y y' _ Hy hf => { hf with
      record := freeAt_rides coll G₂ hc z y y' Hy.cell hf.record
      lay := fun _ => hf.lay (by decide)
      placed := by rw [open₂_last, ← open₂_11]; exact hf.placed
      samples := by rw [open₂_last, ← open₂_11]; exact hf.samples
      rowsIn := fun _ => hf.rowsIn (by decide)
      linOk := fun _ => hf.linOk (by decide)
      seatU := fun _ => hf.seatU (by decide)
      seatOmega := fun _ => hf.seatOmega (by decide)
      shown := fun j hj => by
        rw [open₂_last] at hj
        exact shownAt_ride F at_ j y y' (Hy.word j hj) (hf.shown j (by rw [open₂_11]; exact hj))
      maskU := fun _ => hf.maskU (by decide) })
    (fun i hi z y y' w Hy hu => rides₂_end F G₂ at_ S K₁ R enc rad i hi z y y' w Hy hu)
  unfold on₂ L₂ R₂
  rw [open₂_11, open₂_last]
  exact h

/-- **A block of the last chain that hands the record on, between the borders 1 and 2.** -/
theorem keeps₃_12 (pc : Piece C Fr₃ (P₃ × St₃) Cl W) (hid : ∀ z rs gs z', pc.b.decide z rs gs = .ok z' → z' = z)
    (hsrc : ∀ z rs gs, pc.b.decide z rs gs = .ok z → src z.2 = true)
    (hbase : ∀ k ∈ pinned (open₃ 1), (at_ k).1 < pc.base) (hc : CellOnly coll) :
    pc.ior.red.Keeps (on₃ F Fr₃ G₃ at_ S K₁ R a idx coll src off₂ off₃ t₁ 1) (on₃ F Fr₃ G₃ at_ S K₁ R a idx coll src off₂ off₃ t₁ 2) (L₃ F Fr₃ G₃ at_ S K₁ R 1) (L₃ F Fr₃ G₃ at_ S K₁ R 2) pc.err := by
  have h := same_keeps F Fr₃ G₃ at_ (meaning₃ S K₁ R) pc (shapeB₃ S K₁ a idx src t₁ 1) (shapeB₃ S K₁ a idx src t₁ 2) (Free₃ F G₃ at_ S K₁ R coll off₂ off₃ 1) (Free₃ F G₃ at_ S K₁ R coll off₂ off₃ 2) (open₃ 1) hbase hid
    (fun z hy hs => by
      obtain ⟨rs, gs, hd⟩ := hy
      have h2 := hsrc z rs gs hd
      simp only [shapeB₃, Bool.and_eq_true] at hs ⊢
      exact ⟨⟨⟨⟨⟨hs.1.1.1.1.1, hs.1.1.1.1.2⟩, hs.1.1.1.2⟩, rfl⟩, by rw [h2]; rfl⟩, rfl⟩)
    (fun z y y' _ Hy hf =>
      { record := freeAt_rides coll G₃ hc z y y' Hy.cell hf.record
        arr := hf.arr
        reads := hf.reads
        placed := fun _ => hf.placed (by decide)
        omega₀ := fun h0 => absurd h0 (by decide)
        omega := fun _ _ => hf.omega (by decide) (by decide)
        in₀ := fun h0 => absurd h0 (by decide)
        inOwn := fun _ => hf.inOwn (by decide)
        inOmega := fun _ _ => hf.inOmega (by decide) (by decide)
        order := hf.order
        order₀ := fun h0 => absurd h0 (by decide)
        shown := fun j hj => by
          rw [open₃_12] at hj
          exact shownAt_ride F at_ j y y' (Hy.word j hj) (hf.shown j hj)
        maskW := hf.maskW
        lin₀ := fun h0 => absurd h0 (by decide)
        seatW := fun h0 => absurd h0 (by decide)
        seatOmega₀ := fun h0 => absurd h0 (by decide) })
    (fun i hi z y y' w Hy hu => rides₃ F G₃ at_ S K₁ R (open₃ 1) pinT_open₃_1 i hi z y y' w Hy hu)
  unfold on₃ L₃ R₃
  rw [open₃_12]
  exact h

/-- **Between the borders 3 and 4.** -/
theorem keeps₃_34 (pc : Piece C Fr₃ (P₃ × St₃) Cl W) (hid : ∀ z rs gs z', pc.b.decide z rs gs = .ok z' → z' = z)
    (hfin : ∀ z rs gs, pc.b.decide z rs gs = .ok z → VerifiableInference.Desc.Third.fin₃ z.2 = true) (hc : CellOnly coll) :
    pc.ior.red.Keeps (on₃ F Fr₃ G₃ at_ S K₁ R a idx coll src off₂ off₃ t₁ 3) (on₃ F Fr₃ G₃ at_ S K₁ R a idx coll src off₂ off₃ t₁ 4) (L₃ F Fr₃ G₃ at_ S K₁ R 3) (L₃ F Fr₃ G₃ at_ S K₁ R 4) pc.err := by
  have h := same_keeps F Fr₃ G₃ at_ (meaning₃ S K₁ R) pc (shapeB₃ S K₁ a idx src t₁ 3) (shapeB₃ S K₁ a idx src t₁ 4) (Free₃ F G₃ at_ S K₁ R coll off₂ off₃ 3) (Free₃ F G₃ at_ S K₁ R coll off₂ off₃ 4) [.unmarked] (fun k hk => (List.not_mem_nil (show k ∈ [] from hk)).elim) hid
    (fun z hy hs => by
      obtain ⟨rs, gs, hd⟩ := hy
      have h4 := hfin z rs gs hd
      simp only [shapeB₃, Bool.and_eq_true] at hs ⊢
      exact ⟨⟨⟨⟨⟨hs.1.1.1.1.1, hs.1.1.1.1.2⟩, hs.1.1.1.2⟩, rfl⟩, rfl⟩, by rw [h4]; rfl⟩)
    (fun z y y' _ Hy hf =>
      { record := freeAt_rides coll G₃ hc z y y' Hy.cell hf.record
        arr := hf.arr
        reads := hf.reads
        placed := fun h0 => absurd h0 (by decide)
        omega₀ := fun h0 => absurd h0 (by decide)
        omega := fun _ h0 => absurd h0 (by decide)
        in₀ := fun h0 => absurd h0 (by decide)
        inOwn := fun h0 => absurd h0 (by decide)
        inOmega := fun _ h0 => absurd h0 (by decide)
        order := hf.order
        order₀ := fun h0 => absurd h0 (by decide)
        shown := fun j hj => by
          rw [open₃_last] at hj
          simp [pinned] at hj
        maskW := hf.maskW
        lin₀ := fun h0 => absurd h0 (by decide)
        seatW := fun h0 => absurd h0 (by decide)
        seatOmega₀ := fun h0 => absurd h0 (by decide) })
    (fun i hi z y y' w Hy hu => rides₃ F G₃ at_ S K₁ R [.unmarked] (by decide) i hi z y y' w Hy hu)
  unfold on₃ L₃ R₃
  rw [open₃_3, open₃_last]
  exact h

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.same_keeps
#print axioms Johnson.RunOne.KeyRows23.keeps₂_01
#print axioms Johnson.RunOne.KeyRows23.keeps₂_1112
#print axioms Johnson.RunOne.KeyRows23.keeps₃_12
#print axioms Johnson.RunOne.KeyRows23.keeps₃_34
#print axioms Johnson.RunOne.KeyRows23.held_same
