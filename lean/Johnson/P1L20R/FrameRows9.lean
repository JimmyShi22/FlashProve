-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/FrameRows9.lean:
FrameLeft9 (FrameJoin9.lean) at N := Dm.N and Hold := holdAt Dm, from eight premises
(FrameParams9), by lemmas of other files that were written for its fields; and closed facts on what
is open at the borders behind the link's frame's 51 sub-protocols.

  restB_full, rest_front, rest_laid0, rest_laid, rest_clear   the items that are open at the border
                    behind each of the 51, the parts of the segments' relations apart: by Lean's
                    kernel: behind the front and "laid" 0: unmarked, pinW, pile; behind "laid" l
                    (1 <= l): these
                    with pinI, carry (l - 1), pinKept (l - 1); behind "cleared" l: these with pinI,
                    carry l, pinKept l. For whoever pays carryLaid or carryClear: with open_mem they
                    turn "carry m is open there" into m = l - 1 or m = l
  fourPartsB_full, four_parts   the parts of a segment's relation that are open at these borders
                    are among four: idn, lookCalls, rider, small
  open_fit          so the three facts that FrameItemsOpen.lean asks of every open item
  not_heard         and what FrameHeadOpen.lean asks: the part lookCallsHeard is open at none
  sampled_same      the tenants whose pin is open are the same at the two borders of each of the 51
  no_carry_front    no item "carry m" is open behind the front
  InAt9             what a payer has in hand of the statement in front: no mark, the promise, Kn k
  FrameParams9      THE PREMISES THAT ARE LEFT, eight fields
  clear_kept        an accepting "cleared" of a row of the frame's value is a member of Kept
  frameLeft9_of     FrameLeft9 Dm.N Dm Z T (holdAt Dm) Kn from FrameParams9
  frameOwes9_of     so FrameOwesR there, with frameOwes9's two premises on E and Dm.N

What is called of other files: Johnson/Top/H0/Walk/FramePromiseRides.lean (decodes, shown,
noColl), FrameStringsRide.lean (the same three at one state), FrameItemsOpen.lean (items),
FramePileWo.lean (pile, wo), Johnson/Desc/SmpRowsLay.lean (held).

Limits. FrameParams9 is shown at nothing here. Its fields read, beside Dm: the bases of T's pieces
(kept, low, the five on carry and head) and Z (d1; the rows of framesOf). X and Z.p.X, Dm.links and
the written list, headLink X and 24 are tied by nothing here. Where Dm.decT never answers the
promise is false everywhere and most fields hold trivially; so do carryLaid and carryClear where
Dm.cr1 is constant: the ties then say nothing. Where Kn k never holds the five fields on carry and
head hold trivially, and the debt moves whole to GivesIn (FrameSitsR.lean). No soundness statement.

-/
import Johnson.P1L20R.FrameJoin9
import Johnson.Top.H0.Walk.FrameItemsOpen
import Johnson.Top.H0.Walk.FramePileWo
import Johnson.Desc.SmpRowsLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block Chain FileDescription Place KindName Strs smpHeld Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Pub Part Meaning Numbers sampledIn openSets start
  flatPlacesOf openSets_succ sampledIn_step)
open Johnson.Desc.First.Walk (layFront)
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)

/-- Is the item a part of a segment's relation? -/
def isConstrB : Item → Bool
  | .constr _ _ => true
  | _ => false

/-- What is open at border k, the parts of the segments' relations apart. -/
def restAt (k : ℕ) : List Item := (openL9 k).filter fun i => !isConstrB i

/-- A test with code: what is open at the border behind each of the 51, these parts apart. -/
def restB : Bool :=
  (restAt 1 == [.unmarked, .pinW, .pile]) && (restAt 2 == [.unmarked, .pinW, .pile]) &&
  ((List.range 24).all fun j =>
    restAt (14 * (j + 1) + 1 + 1) == [.unmarked, .pinW, .pile, .pinI, .carry j, .pinKept j]) &&
  (List.range 25).all fun l =>
    restAt (clearIx l + 1) == [.unmarked, .pinW, .pile, .pinI, .carry l, .pinKept l]

set_option maxRecDepth 1000000 in
theorem restB_full : restB = true := by decide +kernel

theorem rest_front : restAt 1 = [.unmarked, .pinW, .pile] := by
  have h := restB_full
  unfold restB at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h.1.1.1

theorem rest_laid0 : restAt 2 = [.unmarked, .pinW, .pile] := by
  have h := restB_full
  unfold restB at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h.1.1.2

theorem rest_laid {j : ℕ} (hj : j < 24) :
    restAt (14 * (j + 1) + 1 + 1) = [.unmarked, .pinW, .pile, .pinI, .carry j, .pinKept j] := by
  have h := restB_full
  unfold restB at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h.1.2 j hj

theorem rest_clear {l : ℕ} (hl : l < 25) :
    restAt (clearIx l + 1) = [.unmarked, .pinW, .pile, .pinI, .carry l, .pinKept l] := by
  have h := restB_full
  unfold restB at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h.2 l hl

/-- A test with code: the list has each of the 51 borders, and the parts of a segment's relation
that are open there are among four. -/
def fourPartsB : Bool :=
  behind51.all fun k =>
    ((openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[k]?).isSome &&
    (openL9 k).all fun i =>
      match i with
      | .constr _ p => p == Part.idn || p == Part.lookCalls || p == Part.rider || p == Part.small
      | _ => true

set_option maxRecDepth 1000000 in
theorem fourPartsB_full : fourPartsB = true := by decide +kernel

/-- The border behind one of the 51 numbers is one of behind51. -/
theorem succ_mem {k : ℕ} (hk : k ∈ our51) : k + 1 ∈ behind51 := by
  unfold our51 at hk
  unfold behind51
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map, List.mem_range] at hk ⊢
  rcases hk with rfl | ⟨l, hl, rfl⟩ | ⟨l, hl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨l, hl, rfl⟩)
  · exact Or.inr (Or.inr ⟨l, hl, rfl⟩)

/-- **The parts that are open behind one of the 51 are among four.** -/
theorem four_parts {k m : ℕ} {p : Part} (hk : k ∈ our51) (hi : openP9 (k + 1) (.constr m p)) :
    p = Part.idn ∨ p = Part.lookCalls ∨ p = Part.rider ∨ p = Part.small := by
  have hb := succ_mem hk
  have hm : Item.constr m p ∈ openL9 (k + 1) := open_mem (behind51_le hb) hi
  have h0 := List.all_eq_true.1 fourPartsB_full (k + 1) hb
  simp only [Bool.and_eq_true] at h0
  have h := List.all_eq_true.1 h0.2 _ hm
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((h | h) | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

/-- The part lookCallsHeard (the head's keys, at the reply that has been heard) is open behind none
of the 51. -/
theorem not_heard {k m : ℕ} (hk : k ∈ our51) : ¬ openP9 (k + 1) (.constr m .lookCallsHeard) := by
  intro h
  rcases four_parts hk h with e | e | e | e <;> cases e

/-- **The three facts on every item that is open behind one of the 51.** -/
theorem open_fit {N : Numbers} {k base : ℕ} (hk : k ∈ our51)
    (hl : LowAt N (openL9 (k + 1)) base) :
    ∀ i, openP9 (k + 1) i →
      i.part = none ∧ notOwn ownDigits i ∧ lowItem N (fun j => j < base) i := by
  intro i hi
  have hb := succ_mem hk
  have hm : i ∈ openL9 (k + 1) := open_mem (behind51_le hb) hi
  refine ⟨open_partless hb hi, ?_, lowItem_of_lowAt hl hm⟩
  cases i with
  | constr m p =>
    show ownDigits m p = false
    unfold ownDigits
    rcases four_parts hk hi with rfl | rfl | rfl | rfl <;> rfl
  | _ => trivial

/-- **The tenants whose pin is open are the same at the two borders of each of the 51.** -/
theorem sampled_same (N : Numbers) {k : ℕ} (hk : k ∈ our51) :
    sampledIn N (openL9 (k + 1)) = sampledIn N (openL9 k) := by
  obtain ⟨pk, hp, _, _⟩ := idle_at hk
  show sampledIn N ((openSets linksFull (flatPlacesOf linksFull true)
    (start linksFull))[k + 1]?.getD []) = _
  rw [openSets_succ linksFull (flatPlacesOf linksFull true) (start linksFull) k pk hp]
  exact sampledIn_step N _ _ (quiet_at hk hp)

theorem low_succ {N : Numbers} {k base : ℕ} (hk : k ∈ our51) (hl : LowAt N (openL9 k) base) :
    LowAt N (openL9 (k + 1)) base := fun x hx => hl x (by rw [← sampled_same N hk]; exact hx)

/-- No item "carry m" is open behind the front. -/
theorem no_carry_front (m : ℕ) : ¬ openP9 1 (.carry m) := by
  intro h
  have hm : Item.carry m ∈ openL9 1 := open_mem (behind51_le (succ_mem mem_our_front)) h
  have hr : Item.carry m ∈ restAt 1 := List.mem_filter.2 ⟨hm, rfl⟩
  rw [rest_front] at hr
  simp at hr

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {C : CK} {D : WholeD} {all : List LeftT}
  {X₁ X₂ Xi Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  {T : ThreeAt C D all
    (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
    X₁ X₂ (Wit (CellsQ rows cols) Tok MsgT)}

/-- **What a payer has in hand of the statement in front of number k**: it bears no mark, it meets
the table's promise at border k, and Kn k. -/
abbrev InAt9 (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR X)
    (Kn : ℕ → ProofFile.InstPub × S → Strs → Prop) (k : ℕ) : ProofFile.InstPub × S → Strs → Prop :=
  fun a y => a.2.failed = none ∧ InK Dm.N (mgAll Dm mgBase) Kn k a y

/-- **THE PREMISES THAT ARE LEFT.** -/
structure FrameParams9 (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR X) (Z : ProofFile.Pub)
    (T : ThreeAt C D all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ (Wit (CellsQ rows cols) Tok MsgT))
    (Kn : ℕ → ProofFile.InstPub × S → Strs → Prop) : Prop where
  /-- three parameters read of the verifier's state nothing but what "cleared" keeps -/
  kept : ∀ l, l < 25 → ∀ q, (T.p₁ :: T.l₁)[clearIx l]? = some q → ReadKept Dm q.base
  /-- the tenants whose pin is open in front of each of the 51 sit in trees below the piece's base
  -/
  low : ∀ k, k ∈ our51 → ∀ q, (T.p₁ :: T.l₁)[k]? = some q → LowAt Dm.N (openL9 k) q.base
  /-- the parameter's layout, shape of a claim and numbers of claims are the plan's -/
  d1 : D1Fits Dm.d1 Z.p.built.links Z.p.X.layers.wsLay Z.first.lin
  /-- the carried word's sentence goes back over "laid", where its item is open behind -/
  carryLaid : ∀ l, l < 25 → ∀ q, (T.p₁ :: T.l₁)[14 * l + 1]? = some q →
    CarryOpen Dm (openP9 (14 * l + 1 + 1))
      (StepRel (Yes (layFront l)) q.base (InAt9 Dm Kn (14 * l + 1)))
  /-- the carried word's sentence goes back over "cleared", where its item is open behind -/
  carryClear : ∀ l, l < 25 → ∀ fs f,
    Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs →
    fs[l]? = some f → ∀ q, (T.p₁ :: T.l₁)[clearIx l]? = some q →
    CarryOpen Dm (openP9 (clearIx l + 1)) (StepRel (Yes f.clear) q.base (InAt9 Dm Kn (clearIx l)))
  /-- the output head's parts' sentences go back over the front, where their items are open -/
  headFront : ∀ q, (T.p₁ :: T.l₁)[0]? = some q →
    HeadOpen Dm (openP9 1) (StepRel (Yes .ok) q.base (InAt9 Dm Kn 0))
  /-- the like over "laid" -/
  headLaid : ∀ l, l < 25 → ∀ q, (T.p₁ :: T.l₁)[14 * l + 1]? = some q →
    HeadOpen Dm (openP9 (14 * l + 1 + 1))
      (StepRel (Yes (layFront l)) q.base (InAt9 Dm Kn (14 * l + 1)))
  /-- the like over "cleared" -/
  headClear : ∀ l, l < 25 → ∀ fs f,
    Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs →
    fs[l]? = some f → ∀ q, (T.p₁ :: T.l₁)[clearIx l]? = some q →
    HeadOpen Dm (openP9 (clearIx l + 1)) (StepRel (Yes f.clear) q.base (InAt9 Dm Kn (clearIx l)))

/-- An accepting "cleared" of a row of the frame's value is a member of Kept. -/
theorem clear_kept {fs : List Johnson.Desc.First.Walk.Seat.LinkFrame}
    {f : Johnson.Desc.First.Walk.Seat.LinkFrame} {l : ℕ}
    (hfs : Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs)
    (hf : fs[l]? = some f) {s t : S} (h : f.clear s = .ok t) : Kept s t := by
  obtain ⟨_, Xl, counts, left, e, _⟩ :=
    Johnson.Desc.First.Walk.Seat.framesOf_row hfs (List.mem_of_getElem? hf)
  rw [e] at h
  exact kept_cleared Xl counts left _ _ s t h

variable {Dm : MgData Xi ProofFile.InstPub Tok rows cols nR X} {Kn : ℕ → ProofFile.InstPub × S → Strs → Prop}

/-- The three fields that read the strings, at one state. -/
theorem strings3_at (H : FrameParams9 Dm Z T Kn) {k : ℕ} (hk : k ∈ our51)
    {q : Piece C (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) Cl
      (Wit (CellsQ rows cols) Tok MsgT)}
    (hq : (T.p₁ :: T.l₁)[k]? = some q) : Strings3 Dm.N (mgAll Dm mgBase) q.base (openL9 k) where
  decodes := (stringsRide_three Dm mgBase (H.low k hk q hq)).1
  shown := (stringsRide_three Dm mgBase (H.low k hk q hq)).2.1
  noColl := (stringsRide_three Dm mgBase (H.low k hk q hq)).2.2

/-- **FrameLeft9 from FrameParams9.** -/
theorem frameLeft9_of (H : FrameParams9 Dm Z T Kn) :
    FrameLeft9 Dm.N Dm Z T (holdAt Dm) Kn where
  sSame := fun k hk q hq => strings3_at H (same_our hk) hq
  iFront := fun q hq p s t y y' w i hy hst hu hF hop h =>
    items_same_open Dm mgBase Dm.N (openP9 1) (Yes .ok) (fun _ _ e => (Except.ok.inj e).symm)
      q.base (InAt9 Dm Kn 0) (fun m hm => absurd hm (no_carry_front m)) (H.headFront q hq)
      (open_fit mem_our_front (low_succ mem_our_front (H.low 0 mem_our_front q hq)))
      p s t y y' w i hy hst ⟨hu, hF⟩ hop h
  iLaid := fun l hl q hq p s t y y' w i hy hst hu hF hop h =>
    items_same_open Dm mgBase Dm.N (openP9 (14 * l + 1 + 1)) (Yes (layFront l))
      (fun _ _ e => (Johnson.Desc.First.Walk.Law.layFront_ok e).1) q.base
      (InAt9 Dm Kn (14 * l + 1)) (H.carryLaid l hl q hq) (H.headLaid l hl q hq)
      (open_fit (mem_our_laid hl) (low_succ (mem_our_laid hl) (H.low _ (mem_our_laid hl) q hq)))
      p s t y y' w i hy hst ⟨hu, hF⟩ hop h
  heldLay := VerifiableInference.Desc.smpHeld_lay
  cDecodes := fun l hl fs f hfs hf q hq p s t y y' hy hst h =>
    decodes_rides Dm mgBase (rel := fun s t => f.clear s = .ok t) q.base
      (decRides_of_kept Dm (fun s t e => clear_kept hfs hf e) q.base (H.kept l hl q hq))
      p s t y y' hy hst h
  cShown := fun l hl q hq y y' x hst hx h =>
    shown_rides Dm mgBase (H.low _ (mem_our_clear hl) q hq x hx) hst h
  cNoColl := fun l hl fs f hfs hf q hq p s t y y' x hy hst hx h =>
    noColl_rides Dm mgBase (H.low _ (mem_our_clear hl) q hq x hx) hst
      (fun m hm hlow z hz =>
        ⟨z, by rw [← (H.kept l hl q hq).smp p s t (clear_kept hfs hf hy) m hm hlow]; exact hz,
          rfl⟩) h
  cItems := fun l hl fs f hfs hf q hq p s t y y' w i hy hst hu hF hop h =>
    items_clear_row_open Dm mgBase Dm.N (openP9 (clearIx l + 1)) hfs hf q.base
      (InAt9 Dm Kn (clearIx l)) (H.kept l hl q hq) (H.carryClear l hl fs f hfs hf q hq)
      (H.headClear l hl fs f hfs hf q hq)
      (open_fit (mem_our_clear hl) (low_succ (mem_our_clear hl) (H.low _ (mem_our_clear hl) q hq)))
      p s t y y' w i hy hst ⟨hu, hF⟩ hop h
  wo := fun l _ X' hX' _ a y w h => hold_gives_wo Dm mgBase H.d1 l X' hX' a y w h
  holdBack := fun l _ fs f hfs hf p s t w r hy h =>
    hold_back Dm p (leavesReader_frame hfs (List.mem_of_getElem? hf) hy) w r h
  pile := frameOwes_pile Dm mgBase

/-- **So FrameOwesR at the composed meaning.** -/
theorem frameOwes9_of (H : FrameParams9 Dm Z T Kn)
    (E : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → Wit (CellsQ rows cols) Tok MsgT →
      Wit (CellsQ rows cols) Tok MsgT)
    (hE : (∀ a b w, E 0 a b w = w) ∧ (∀ l, l < 25 → ∀ a b w, E (14 * l + 1) a b w = w) ∧
      ∀ l, l < 25 → ∀ a b w, E (clearIx l) a b w = w)
    (hN : NoneBetween Dm.N (flatPlacesOf linksFull true) 0 ∧
      (∀ l, l < 25 → NoneBetween Dm.N (flatPlacesOf linksFull true) (14 * l + 1)) ∧
      ∀ l, l < 25 → NoneBetween Dm.N (flatPlacesOf linksFull true) (clearIx l)) :
    FrameOwesR (T := T) Dm.N (mgAll Dm mgBase) Z E (holdAt Dm)
      (InK Dm.N (mgAll Dm mgBase) Kn) :=
  frameOwes9 (frameLeft9_of H) E hE hN

end

end P1L20

#print axioms P1L20.restB_full
#print axioms P1L20.fourPartsB_full
#print axioms P1L20.not_heard
#print axioms P1L20.open_fit
#print axioms P1L20.no_carry_front
#print axioms P1L20.frameLeft9_of
#print axioms P1L20.frameOwes9_of
