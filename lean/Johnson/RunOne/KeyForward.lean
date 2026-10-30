-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyForward.lean: The key file, the shared chain: THE PROMISE's FORWARD HALVES OF THE ROWS 2.1 (LIN point) · 2.4 (LOC) · 2.7 (LIN zeta): the three rows of K14 that draw.
These three and no others. THE CHANCE's HALVES ARE IN OTHER FILES; THE JOINING OF THE TWO HALVES INTO Keeps IS IN THE TABLES' FILES.

OBJECT. No text's constant: two records tied by a structure of plain facts (PointLaid | LocLaid | ZetaLaid: Johnson/Desc/Key/Laid/DrawsDef.lean) and the tables' shape₂ · Free₂ · meaning₂ · open₂ at the borders 1 | 2, 4 | 5, 7 | 8. AT THE DESCRIPTION's OWN BLOCKS: half₂₁_at_desc | half₂₄_at_desc | half₂₇_at_desc: blocks number 1, 4, 7 of (Key.descriptionFromSource X N P).shared.blocksInOrder; fwd₂₁ | fwd₂₄ | fwd₂₇: at «held» of these.
USER. keeps₂_of_halves' (Johnson/RunOne/KeyHalves23.lean), at k := 1 | 4 | 7: fwd₂₁ | fwd₂₄ | fwd₂₇ HAVE THE FORM OF ITS PREMISE «fwd», at pc.b := B, B = held ‹the description's block›: at one y, WITHOUT THE RELATION's WAY BACK. THAT THEY MEET IT HAS BEEN TRIED BEFORE LEAN: a sheet that is not in this library hands each to its joining as «fwd».
LETTERS. F G₂ at_ K₁ R enc rad a coll last₁ off₂: free. S: at the plain rows p.S | S; at the description: the sized key's shape.

THE CAUTION. UNTIL A MEMBER IS SHOWN, EVERY LAW OVER THESE TABLES THAT HAS PIN AS AN ITEM OR NoColl IN ITS PROMISE MAY BE TRUE AND EMPTY AT THE REAL PROTOCOL, AND COUNTS AS CLOSING NOTHING. These halves speak of the promise alone; they are of the form «a yes and the promise in front give the promise behind»: where the promise in front is never met, or the block never says yes, they say nothing.
IS IT EMPTY HERE? NOT SHOWN EITHER WAY BY A THEOREM. A MEMBER WAS SOUGHT IN PRINTS THAT ARE NOT IN THIS REPOSITORY: that the three blocks say yes: one print (over other base files than these; both stored key files, made-up weights): «WALK chain 2: 13 states; stopped: none» · the Bools of the promise (shape₂) at the honest walk's states: sheets over another ground, in no print over these base files · OF onAt … k WITH ITS LETTERS (G₂ · coll · PIN's hasSmp and NoColl): NO MEMBER IS SHOWN.

WHAT IS TAKEN FROM OTHERS, BY NAME: PinsStay G₂ at_ l (z, d) (z, d') (l the open pins: [0, 2] | [0, 2, 3] | [0, 2, 3, 4, 5]): WHOSE: whoever fills the reading: that it gives one sample at these seats and one record of the stored table in front of and behind the block. AT THE DESCRIPTION's BLOCKS IT IS ASKED UNDER THE PLAIN FACTS AND THE PROMISE IN FRONT, not at every pair of records: so that it can be met at a true reading.

WHAT IS EARNED. 2.1: two groups, numbered 0 and 1, empty, not begun · the point has kCol coordinates (the format's test on the round) · Free₂.linOk (the block's own test) · rowsIn (out of «in order»). 2.4: as many rows of the kind «generator» on G_u as the shape has columns. 2.7: the last point has kRow coordinates.

Limits. Each shape₂_… opens shape₂'s list of eighteen clauses by their places: a clause more turns these proofs. Keeps is not stated here. NOTHING ON CHANCE. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.RunOne.KeyRow23
import Johnson.RunOne.KeyRow28
import Johnson.RunOne.KeyCut23
import Johnson.RunOne.KeyWrap23
import Johnson.Desc.Key.Laid.Draws
import Johnson.Desc.Key.Laid.AtBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (FirstState)
open Desc.Plain (Par)
open VerifiableInference.Desc.Plain (held_decide)
open VerifiableInference.Desc.Sound (held)

theorem pinned₂_1 : pinned (open₂ 1) = [0, 2] := by decide
theorem pinned₂_2 : pinned (open₂ 2) = [0, 2] := by decide
theorem pinned₂_5 : pinned (open₂ 5) = [0, 2, 3] := by decide
theorem pinned₂_7 : pinned (open₂ 7) = [0, 2, 3, 4, 5] := by decide

/-! ## The book-keeping, forward -/

theorem shape₂_12 (p : Par) (a : Nat) (d d' : St₂) {r : Fmt.RoundView} (P : PointLaid p d d' r)
    (hl : (_root_.Desc.K14.drawn r).length = p.S.kCol)
    (h : LKFU.Shape23.ok (LKFU.Shape23.shape₂ p.S a 1 d) = true) : LKFU.Shape23.ok (LKFU.Shape23.shape₂ p.S a 2 d') = true := by
  simp only [LKFU.Shape23.ok, LKFU.Shape23.shape₂, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h ⊢
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18⟩ := h
  have el := P.loc
  have eb := P.book
  have er := P.roots
  have eo := P.oracles
  have eg := P.groups
  have g0 : d.st.groups = #[] := Array.eq_empty_of_size_eq_zero (by simpa using c3)
  rw [g0] at eg
  have s0 : d.st.groups.size = 0 := by rw [g0]; rfl
  refine ⟨c1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [eo] using c2
  · simp [eg]
  · simpa [eb, er] using c4
  · simpa [eo, eb] using c5
  · simpa [el] using hl
  · simp [el, s0]
  · simpa [el] using c8
  · simp
  · simpa [el] using c10
  · simp
  · simpa [el] using c12
  · simp [LKFU.Shape23.grpIs, LKFU.Shape23.plainRows, LKFU.Shape23.genRows, eg]
  · simp [LKFU.Shape23.grpIs, LKFU.Shape23.plainRows, LKFU.Shape23.genRows, eg]
  · simp
  · simp
  · simp
  · simpa [eb, er] using c18

theorem shape₂_45 (p : Par) (a : Nat) (d d' : St₂) {r : Fmt.RoundView} {GU : OnBytes.Group} {rows : List OnBytes.Row} (P : LocLaid p d d' r GU rows)
    (hl : rows.length = p.S.fold.columns)
    (h : LKFU.Shape23.ok (LKFU.Shape23.shape₂ p.S a 4 d) = true) : LKFU.Shape23.ok (LKFU.Shape23.shape₂ p.S a 5 d') = true := by
  simp only [LKFU.Shape23.ok, LKFU.Shape23.shape₂, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h ⊢
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18⟩ := h
  have el := P.loc
  have eb := P.book
  have er := P.roots
  have eo := P.oracles
  have eg := P.groups
  have n7 : d.loc.gU = 0 ∧ d.loc.gOmega = 1 := by simpa using c7
  have g13 : LKFU.Shape23.grpIs d.st 0 [0] p.S.fold.index.answers 0 false = true := by simpa using c13
  have g14 : LKFU.Shape23.grpIs d.st 1 [] 0 0 false = true := by simpa using c14
  have jU := P.gU
  have jU' := P.gU'
  rw [n7.1] at jU jU'
  have g14' : LKFU.Shape23.grpIs d'.st 1 [] 0 0 false = true := by
    rw [grpIs_same d.st d'.st 1 _ _ _ _ (P.other 1 (by rw [n7.1]; decide))]
    exact g14
  have hgen : (rows.filter (·.kind == .generator)).length = rows.length := by
    rw [List.filter_eq_self.2 fun x hx => by rw [P.kinds x hx]; rfl]
  have hpl : (rows.filter (·.kind == .plain)).length = 0 := by
    rw [List.filter_eq_nil_iff.2 fun x hx => by rw [P.kinds x hx]; decide]
    rfl
  have g13' : LKFU.Shape23.grpIs d'.st 0 [0] p.S.fold.index.answers p.S.fold.columns false = true := by
    unfold LKFU.Shape23.grpIs at g13 ⊢
    rw [jU] at g13
    rw [jU']
    simp only [Bool.and_eq_true, beq_iff_eq] at g13 ⊢
    obtain ⟨⟨⟨⟨m1, m2⟩, m3⟩, m4⟩, m5⟩ := g13
    refine ⟨⟨⟨⟨m1, ?_⟩, ?_⟩, ?_⟩, m5⟩
    · unfold LKFU.Shape23.plainRows at m2 ⊢
      simp only [Array.toList_append, List.filter_append, List.length_append, m2, hpl]
      simp
    · unfold LKFU.Shape23.genRows at m3 ⊢
      simp only [Array.toList_append, List.filter_append, List.length_append, m3, hgen, hl]
      simp
    · simp only [Array.size_append, List.size_toArray, m4, hl]
      omega
  refine ⟨c1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [eo] using c2
  · simpa [eg] using c3
  · simpa [eb, er] using c4
  · simpa [eo, eb] using c5
  · simpa [el] using c6
  · simpa [el] using c7
  · simpa [el] using c8
  · simpa [LKFU.Shape23.msgIs, eo] using c9
  · simpa [el] using c10
  · simp
  · simpa [el] using c12
  · simpa using g13'
  · simpa using g14'
  · simp
  · simp
  · simp
  · simpa [eb, er] using c18

theorem shape₂_78 (S : LinShape) (a : Nat) (d d' : St₂) {r : Fmt.RoundView} (P : ZetaLaid d d' r)
    (hl : (_root_.Desc.K14.drawn r).length = S.kRow)
    (h : LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 7 d) = true) : LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 8 d') = true := by
  rw [P.is]
  simp only [LKFU.Shape23.ok, LKFU.Shape23.shape₂, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h ⊢
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18⟩ := h
  refine ⟨c1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using c2
  · simpa using c3
  · simpa using c4
  · simpa using c5
  · simpa using c6
  · simpa using c7
  · simpa using c8
  · simpa using c9
  · simpa using c10
  · simpa using c11
  · simpa using hl
  · simpa using c13
  · simpa using c14
  · simpa using c15
  · simp
  · simp
  · simpa using c18

section
variable {XI Cells M Smp Rec : Type} (F : FileDescription XI)
  (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (at_ : Where)
  (p : Par) (S : LinShape) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad a : Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (off₂ : Nat → Nat)

/-! ## The promise's last letter, forward -/

theorem free₂_12 (z : P₂) (d d' : St₂) (y : Strs) {r : Fmt.RoundView} (P : PointLaid p d d' r)
    (hp : PinsStay G₂ at_ [0, 2] (z, d) (z, d'))
    (hf : Free₂ F G₂ at_ p.S K₁ R coll last₁ off₂ 1 (z, d) y) : Free₂ F G₂ at_ p.S K₁ R coll last₁ off₂ 2 (z, d') y :=
  have hord : Means.InOrder d'.st := P.order hf.order
  { hf with
    record := hp.freeAt coll y hf.record
    key := by
      show d'.loc.key = _
      rw [P.loc]
      exact hf.key
    codes := by
      show d'.st.codes = _
      rw [P.codes]
      exact hf.codes
    lay := fun h3 => absurd h3 (by decide)
    placed := by
      show Placed (plan₂ p.S).orc (fun o => d'.book.place[o]?) off₂ at_ ((pinned (open₂ 2)).filter (3 ≤ ·))
      rw [P.book, pinned₂_2, ← pinned₂_1]
      exact hf.placed
    samples := fun _ _ o _ => sampleIn_of_order hord o
    rowsIn := fun _ => ⟨openIn_of_order hord _, openIn_of_order hord _⟩
    order := hord
    linOk := fun _ => by
      show OnBytes.linOk d'.st.codes p.S = true
      rw [P.codes]
      exact P.lin
    seatU := fun h3 => absurd h3 (by decide)
    seatOmega := fun h6 => absurd h6 (by decide)
    shown := fun j hj => hf.shown j (by rw [pinned₂_1]; rw [pinned₂_2] at hj; exact hj)
    maskU := fun h3 => absurd h3 (by decide) }

theorem free₂_45 (z : P₂) (d d' : St₂) (y : Strs) {r : Fmt.RoundView} {GU : OnBytes.Group} {rows : List OnBytes.Row} (P : LocLaid p d d' r GU rows)
    (hp : PinsStay G₂ at_ [0, 2, 3] (z, d) (z, d'))
    (hf : Free₂ F G₂ at_ S K₁ R coll last₁ off₂ 4 (z, d) y) : Free₂ F G₂ at_ S K₁ R coll last₁ off₂ 5 (z, d') y :=
  have hord : Means.InOrder d'.st := P.order hf.order
  { hf with
    record := hp.freeAt coll y hf.record
    key := by
      show d'.loc.key = _
      rw [P.loc]
      exact hf.key
    codes := by
      show d'.st.codes = _
      rw [P.codes]
      exact hf.codes
    lay := fun _ => by
      show d'.loc.oU.lay = vectorLay d'.st.codes S.fold.u S.fold.rowsHigh
      rw [P.loc, P.codes]
      exact hf.lay (by decide)
    placed := by
      show Placed (plan₂ S).orc (fun o => d'.book.place[o]?) off₂ at_ ((pinned (open₂ 5)).filter (3 ≤ ·))
      rw [P.book, pinned₂_5, ← pinned₂_4]
      exact hf.placed
    samples := fun _ _ o _ => sampleIn_of_order hord o
    rowsIn := fun _ => ⟨openIn_of_order hord _, openIn_of_order hord _⟩
    order := hord
    linOk := fun _ => by
      show OnBytes.linOk d'.st.codes S = true
      rw [P.codes]
      exact hf.linOk (by decide)
    seatU := fun _ => by
      show (d'.st.oracles[0]?).any (·.shape == S.fold.u) = true
      rw [P.oracles]
      exact hf.seatU (by decide)
    seatOmega := fun h6 => absurd h6 (by decide)
    shown := fun j hj => hf.shown j (by rw [pinned₂_4]; rw [pinned₂_5] at hj; exact hj)
    maskU := fun _ => by
      show MaskWith (fun i => d'.book.place[i]?) 0 1
      rw [P.book]
      exact hf.maskU (by decide) }

theorem free₂_78 (z : P₂) (d d' : St₂) (y : Strs) {r : Fmt.RoundView} (P : ZetaLaid d d' r)
    (hp : PinsStay G₂ at_ [0, 2, 3, 4, 5] (z, d) (z, d'))
    (hf : Free₂ F G₂ at_ S K₁ R coll last₁ off₂ 7 (z, d) y) : Free₂ F G₂ at_ S K₁ R coll last₁ off₂ 8 (z, d') y :=
  have est : d'.st = d.st := by rw [P.is]
  have ebk : d'.book = d.book := by rw [P.is]
  have epsi : d'.loc.psiSh = d.loc.psiSh := by rw [P.is]
  have ekey : d'.loc.key = d.loc.key := by rw [P.is]
  have eou : d'.loc.oU = d.loc.oU := by rw [P.is]
  have hord : Means.InOrder d'.st := by rw [est]; exact hf.order
  { hf with
    record := hp.freeAt coll y hf.record
    key := by
      show d'.loc.key = _
      rw [ekey]
      exact hf.key
    codes := by
      show d'.st.codes = _
      rw [est]
      exact hf.codes
    lay := fun _ => by
      show d'.loc.oU.lay = vectorLay d'.st.codes S.fold.u S.fold.rowsHigh
      rw [eou, est]
      exact hf.lay (by decide)
    placed := by
      show Placed (plan₂ S).orc (fun o => d'.book.place[o]?) off₂ at_ ((pinned (open₂ 8)).filter (3 ≤ ·))
      rw [ebk, pinned₂_8, ← pinned₂_7]
      exact hf.placed
    samples := fun _ _ o _ => sampleIn_of_order hord o
    rowsIn := fun _ => ⟨openIn_of_order hord _, openIn_of_order hord _⟩
    order := hord
    linOk := fun _ => by
      show OnBytes.linOk d'.st.codes S = true
      rw [est]
      exact hf.linOk (by decide)
    seatU := fun _ => by
      show (d'.st.oracles[0]?).any (·.shape == S.fold.u) = true
      rw [est]
      exact hf.seatU (by decide)
    seatOmega := fun _ => by
      show (d'.st.oracles[2]?).any (·.shape == S.omega) = true
      rw [est]
      exact hf.seatOmega (by decide)
    shown := fun j hj => hf.shown j (by rw [pinned₂_7]; rw [pinned₂_8] at hj; exact hj)
    maskU := fun _ => by
      show MaskWith (fun i => d'.book.place[i]?) 0 1
      rw [ebk]
      exact hf.maskU (by decide) }

/-! ## The three halves, at two records -/

/-- **ROW 2.1, THE PROMISE's FORWARD HALF.** -/
theorem half₂₁ (z : P₂) (d d' : St₂) (y : Strs) {r : Fmt.RoundView} (P : PointLaid p d d' r) (hl : (_root_.Desc.K14.drawn r).length = p.S.kCol)
    (hp : PinsStay G₂ at_ [0, 2] (z, d) (z, d'))
    (hon : onAt F G₂ at_ (meaning₂ p.S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ p.S a 1 d)) (Free₂ F G₂ at_ p.S K₁ R coll last₁ off₂ 1) (open₂ 1) (z, d) y) :
    onAt F G₂ at_ (meaning₂ p.S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ p.S a 2 d)) (Free₂ F G₂ at_ p.S K₁ R coll last₁ off₂ 2) (open₂ 2) (z, d') y :=
  hp.onAt F (meaning₂ p.S K₁ R enc rad) _ _ _ _ (open₂ 1) (open₂ 2) y pinned₂_1 pinned₂_2 trivial
    (fun hsh => shape₂_12 p a d d' P hl hsh) (fun _ h3 => free₂_12 F G₂ at_ p K₁ R coll last₁ off₂ z d d' y P hp h3) hon

/-- **ROW 2.4, THE PROMISE's FORWARD HALF.** -/
theorem half₂₄ (z : P₂) (d d' : St₂) (y : Strs) {r : Fmt.RoundView} {GU : OnBytes.Group} {rows : List OnBytes.Row} (P : LocLaid p d d' r GU rows)
    (hl : rows.length = p.S.fold.columns) (hp : PinsStay G₂ at_ [0, 2, 3] (z, d) (z, d'))
    (hon : onAt F G₂ at_ (meaning₂ p.S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ p.S a 4 d)) (Free₂ F G₂ at_ p.S K₁ R coll last₁ off₂ 4) (open₂ 4) (z, d) y) :
    onAt F G₂ at_ (meaning₂ p.S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ p.S a 5 d)) (Free₂ F G₂ at_ p.S K₁ R coll last₁ off₂ 5) (open₂ 5) (z, d') y :=
  hp.onAt F (meaning₂ p.S K₁ R enc rad) _ _ _ _ (open₂ 4) (open₂ 5) y pinned₂_4 pinned₂_5 trivial
    (fun hsh => shape₂_45 p a d d' P hl hsh) (fun _ h3 => free₂_45 F G₂ at_ p p.S K₁ R coll last₁ off₂ z d d' y P hp h3) hon

/-- **ROW 2.7, THE PROMISE's FORWARD HALF.** -/
theorem half₂₇ (z : P₂) (d d' : St₂) (y : Strs) {r : Fmt.RoundView} (P : ZetaLaid d d' r) (hl : (_root_.Desc.K14.drawn r).length = S.kRow)
    (hp : PinsStay G₂ at_ [0, 2, 3, 4, 5] (z, d) (z, d'))
    (hon : onAt F G₂ at_ (meaning₂ S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 7 d)) (Free₂ F G₂ at_ S K₁ R coll last₁ off₂ 7) (open₂ 7) (z, d) y) :
    onAt F G₂ at_ (meaning₂ S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 8 d)) (Free₂ F G₂ at_ S K₁ R coll last₁ off₂ 8) (open₂ 8) (z, d') y :=
  hp.onAt F (meaning₂ S K₁ R enc rad) _ _ _ _ (open₂ 7) (open₂ 8) y pinned₂_7 pinned₂_8 trivial
    (fun hsh => shape₂_78 S a d d' P hl hsh) (fun _ h3 => free₂_78 F G₂ at_ S K₁ R coll last₁ off₂ z d d' y P hp h3) hon

end

/-! ## The three halves, at the description's own blocks -/

section
variable {XI Cells M Smp Rec : Type} (F : FileDescription XI)
  (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (at_ : Where)
  (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad a : Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (off₂ : Nat → Nat)
  (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
  (b1 b2 b3 b4 b5 b6 b7 b8 : Block _root_.Desc.K14.St Unit)
  (h : _root_.Desc.K14.blocks (p14At X P) = some [b1, b2, b3, b4, b5, b6, b7, b8])
include h

theorem shared_1 : (descriptionFromSource X N P).shared.blocksInOrder[1]? = some (seat b1) := by
  rw [shared_at_blocks X N P _ h]
  rfl

theorem shared_4 : (descriptionFromSource X N P).shared.blocksInOrder[4]? = some (seat b4) := by
  rw [shared_at_blocks X N P _ h]
  rfl

theorem shared_7 : (descriptionFromSource X N P).shared.blocksInOrder[7]? = some (seat b7) := by
  rw [shared_at_blocks X N P _ h]
  rfl

/-- **ROW 2.1's forward half at the description's block "LIN point".** -/
theorem half₂₁_at_desc (hS : (p14At X P).S.sharedSplitNeeded = true)
    (b : Block _root_.Desc.K14.St Claim) (hb : (descriptionFromSource X N P).shared.blocksInOrder[1]? = some b)
    (hP : ∀ (z : P₂) (d d' : St₂) (r : Fmt.RoundView) (y : Strs), PointLaid (p14At X P).par d d' r →
      onAt F G₂ at_ (meaning₂ (p14At X P).S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ (p14At X P).S a 1 d)) (Free₂ F G₂ at_ (p14At X P).S K₁ R coll last₁ off₂ 1) (open₂ 1) (z, d) y →
      PinsStay G₂ at_ [0, 2] (z, d) (z, d')) :
    ∀ (z : P₂) (d : St₂) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (d' : St₂) (y : Strs),
      roundsFit b.rounds rs = true → b.decide d (rs.map noDigest) gs = .ok d' →
      onAt F G₂ at_ (meaning₂ (p14At X P).S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ (p14At X P).S a 1 d)) (Free₂ F G₂ at_ (p14At X P).S K₁ R coll last₁ off₂ 1) (open₂ 1) (z, d) y →
      onAt F G₂ at_ (meaning₂ (p14At X P).S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ (p14At X P).S a 2 d)) (Free₂ F G₂ at_ (p14At X P).S K₁ R coll last₁ off₂ 2) (open₂ 2) (z, d') y := by
  have e : b = seat b1 := Option.some.inj (hb.symm.trans (shared_1 X N P b1 b2 b3 b4 b5 b6 b7 b8 h))
  subst e
  intro z d rs gs d' y hf hd hon
  obtain ⟨r, L, hl⟩ := point_at_blocks _ b1 b2 b3 b4 b5 b6 b7 b8 h hS d rs gs d' hf hd
  exact half₂₁ F G₂ at_ (p14At X P).par K₁ R enc rad a coll last₁ off₂ z d d' y L hl (hP z d d' r y L hon) hon

/-- **ROW 2.4's forward half at the description's block "LOC".** -/
theorem half₂₄_at_desc (b : Block _root_.Desc.K14.St Claim) (hb : (descriptionFromSource X N P).shared.blocksInOrder[4]? = some b)
    (hP : ∀ (z : P₂) (d d' : St₂) (r : Fmt.RoundView) (GU : OnBytes.Group) (rows : List OnBytes.Row) (y : Strs),
      LocLaid (p14At X P).par d d' r GU rows →
      onAt F G₂ at_ (meaning₂ (p14At X P).S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ (p14At X P).S a 4 d)) (Free₂ F G₂ at_ (p14At X P).S K₁ R coll last₁ off₂ 4) (open₂ 4) (z, d) y →
      PinsStay G₂ at_ [0, 2, 3] (z, d) (z, d')) :
    ∀ (z : P₂) (d : St₂) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (d' : St₂) (y : Strs),
      roundsFit b.rounds rs = true → b.decide d (rs.map noDigest) gs = .ok d' →
      onAt F G₂ at_ (meaning₂ (p14At X P).S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ (p14At X P).S a 4 d)) (Free₂ F G₂ at_ (p14At X P).S K₁ R coll last₁ off₂ 4) (open₂ 4) (z, d) y →
      onAt F G₂ at_ (meaning₂ (p14At X P).S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ (p14At X P).S a 5 d)) (Free₂ F G₂ at_ (p14At X P).S K₁ R coll last₁ off₂ 5) (open₂ 5) (z, d') y := by
  have e : b = seat b4 := Option.some.inj (hb.symm.trans (shared_4 X N P b1 b2 b3 b4 b5 b6 b7 b8 h))
  subst e
  intro z d rs gs d' y hf hd hon
  obtain ⟨r, GU, rows, L, hl⟩ := loc_at_blocks _ b1 b2 b3 b4 b5 b6 b7 b8 h d rs gs d' hf hd
  exact half₂₄ F G₂ at_ (p14At X P).par K₁ R enc rad a coll last₁ off₂ z d d' y L hl (hP z d d' r GU rows y L hon) hon

/-- **ROW 2.7's forward half at the description's block "LIN zeta".** -/
theorem half₂₇_at_desc (b : Block _root_.Desc.K14.St Claim) (hb : (descriptionFromSource X N P).shared.blocksInOrder[7]? = some b)
    (hP : ∀ (z : P₂) (d d' : St₂) (r : Fmt.RoundView) (y : Strs), ZetaLaid d d' r →
      onAt F G₂ at_ (meaning₂ (p14At X P).S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ (p14At X P).S a 7 d)) (Free₂ F G₂ at_ (p14At X P).S K₁ R coll last₁ off₂ 7) (open₂ 7) (z, d) y →
      PinsStay G₂ at_ [0, 2, 3, 4, 5] (z, d) (z, d')) :
    ∀ (z : P₂) (d : St₂) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (d' : St₂) (y : Strs),
      roundsFit b.rounds rs = true → b.decide d (rs.map noDigest) gs = .ok d' →
      onAt F G₂ at_ (meaning₂ (p14At X P).S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ (p14At X P).S a 7 d)) (Free₂ F G₂ at_ (p14At X P).S K₁ R coll last₁ off₂ 7) (open₂ 7) (z, d) y →
      onAt F G₂ at_ (meaning₂ (p14At X P).S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ (p14At X P).S a 8 d)) (Free₂ F G₂ at_ (p14At X P).S K₁ R coll last₁ off₂ 8) (open₂ 8) (z, d') y := by
  have e : b = seat b7 := Option.some.inj (hb.symm.trans (shared_7 X N P b1 b2 b3 b4 b5 b6 b7 b8 h))
  subst e
  intro z d rs gs d' y hf hd hon
  obtain ⟨r, L, hl⟩ := zeta_at_blocks _ b1 b2 b3 b4 b5 b6 b7 b8 h d rs gs d' hf hd
  exact half₂₇ F G₂ at_ (p14At X P).S K₁ R enc rad a coll last₁ off₂ z d d' y L hl (hP z d d' r y L hon) hon

/-! ## The same, at the block as a piece holds it: TO THE LETTER OF THE PREMISE «fwd»
OF keeps₂_of_halves' (Johnson/RunOne/KeyHalves23.lean), at pc.b := B -/

/-- **2.1: «fwd» of keeps₂_of_halves' at k := 1.** -/
theorem fwd₂₁ (hS : (p14At X P).S.sharedSplitNeeded = true)
    (b : Block _root_.Desc.K14.St Claim) (hb : (descriptionFromSource X N P).shared.blocksInOrder[1]? = some b)
    (B : Block (P₂ × St₂) Claim) (hB : B = held b)
    (hP : ∀ (z : P₂) (d d' : St₂) (r : Fmt.RoundView) (y : Strs), PointLaid (p14At X P).par d d' r →
      onAt F G₂ at_ (meaning₂ (p14At X P).S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ (p14At X P).S a 1 d)) (Free₂ F G₂ at_ (p14At X P).S K₁ R coll last₁ off₂ 1) (open₂ 1) (z, d) y →
      PinsStay G₂ at_ [0, 2] (z, d) (z, d')) :
    ∀ z rs gs z' y, roundsFit B.rounds rs = true → B.decide z (rs.map noDigest) gs = .ok z' →
      onAt F G₂ at_ (meaning₂ (p14At X P).S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ (p14At X P).S a 1 d)) (Free₂ F G₂ at_ (p14At X P).S K₁ R coll last₁ off₂ 1) (open₂ 1) z y →
      onAt F G₂ at_ (meaning₂ (p14At X P).S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ (p14At X P).S a 2 d)) (Free₂ F G₂ at_ (p14At X P).S K₁ R coll last₁ off₂ 2) (open₂ 2) z' y := by
  subst hB
  intro z rs gs z' y hf hd hon
  obtain ⟨e1, e2⟩ := held_decide b z _ gs z' hd
  have ez : z' = (z.1, z'.2) := Prod.ext e1 rfl
  rw [ez]
  exact half₂₁_at_desc F G₂ at_ K₁ R enc rad a coll last₁ off₂ X N P b1 b2 b3 b4 b5 b6 b7 b8 h hS b hb hP
    z.1 z.2 rs gs z'.2 y hf e2 hon

/-- **2.4: «fwd» of keeps₂_of_halves' at k := 4.** -/
theorem fwd₂₄ (b : Block _root_.Desc.K14.St Claim) (hb : (descriptionFromSource X N P).shared.blocksInOrder[4]? = some b)
    (B : Block (P₂ × St₂) Claim) (hB : B = held b)
    (hP : ∀ (z : P₂) (d d' : St₂) (r : Fmt.RoundView) (GU : OnBytes.Group) (rows : List OnBytes.Row) (y : Strs),
      LocLaid (p14At X P).par d d' r GU rows →
      onAt F G₂ at_ (meaning₂ (p14At X P).S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ (p14At X P).S a 4 d)) (Free₂ F G₂ at_ (p14At X P).S K₁ R coll last₁ off₂ 4) (open₂ 4) (z, d) y →
      PinsStay G₂ at_ [0, 2, 3] (z, d) (z, d')) :
    ∀ z rs gs z' y, roundsFit B.rounds rs = true → B.decide z (rs.map noDigest) gs = .ok z' →
      onAt F G₂ at_ (meaning₂ (p14At X P).S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ (p14At X P).S a 4 d)) (Free₂ F G₂ at_ (p14At X P).S K₁ R coll last₁ off₂ 4) (open₂ 4) z y →
      onAt F G₂ at_ (meaning₂ (p14At X P).S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ (p14At X P).S a 5 d)) (Free₂ F G₂ at_ (p14At X P).S K₁ R coll last₁ off₂ 5) (open₂ 5) z' y := by
  subst hB
  intro z rs gs z' y hf hd hon
  obtain ⟨e1, e2⟩ := held_decide b z _ gs z' hd
  have ez : z' = (z.1, z'.2) := Prod.ext e1 rfl
  rw [ez]
  exact half₂₄_at_desc F G₂ at_ K₁ R enc rad a coll last₁ off₂ X N P b1 b2 b3 b4 b5 b6 b7 b8 h b hb hP
    z.1 z.2 rs gs z'.2 y hf e2 hon

/-- **2.7: «fwd» of keeps₂_of_halves' at k := 7.** -/
theorem fwd₂₇ (b : Block _root_.Desc.K14.St Claim) (hb : (descriptionFromSource X N P).shared.blocksInOrder[7]? = some b)
    (B : Block (P₂ × St₂) Claim) (hB : B = held b)
    (hP : ∀ (z : P₂) (d d' : St₂) (r : Fmt.RoundView) (y : Strs), ZetaLaid d d' r →
      onAt F G₂ at_ (meaning₂ (p14At X P).S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ (p14At X P).S a 7 d)) (Free₂ F G₂ at_ (p14At X P).S K₁ R coll last₁ off₂ 7) (open₂ 7) (z, d) y →
      PinsStay G₂ at_ [0, 2, 3, 4, 5] (z, d) (z, d')) :
    ∀ z rs gs z' y, roundsFit B.rounds rs = true → B.decide z (rs.map noDigest) gs = .ok z' →
      onAt F G₂ at_ (meaning₂ (p14At X P).S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ (p14At X P).S a 7 d)) (Free₂ F G₂ at_ (p14At X P).S K₁ R coll last₁ off₂ 7) (open₂ 7) z y →
      onAt F G₂ at_ (meaning₂ (p14At X P).S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ (p14At X P).S a 8 d)) (Free₂ F G₂ at_ (p14At X P).S K₁ R coll last₁ off₂ 8) (open₂ 8) z' y := by
  subst hB
  intro z rs gs z' y hf hd hon
  obtain ⟨e1, e2⟩ := held_decide b z _ gs z' hd
  have ez : z' = (z.1, z'.2) := Prod.ext e1 rfl
  rw [ez]
  exact half₂₇_at_desc F G₂ at_ K₁ R enc rad a coll last₁ off₂ X N P b1 b2 b3 b4 b5 b6 b7 b8 h b hb hP
    z.1 z.2 rs gs z'.2 y hf e2 hon

end

end Johnson.RunOne.KeyRows23
