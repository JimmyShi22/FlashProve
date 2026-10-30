-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/FrameJoin9.lean: what the link's
frame's 51 sub-protocols still owe at the composed meaning mgAll Dm mgBase, as ONE STRUCTURE, a
field a debt (FrameLeft9), and the theorem that its fields give FrameOwesR (FrameSitsR.lean) there.

What is known in front. LettersRide asks every field but "decodes" at a statement that bears no mark
and meets In; here In := InK: the table's promise at the border in front (FrontAt) AND Kn k: a
family of letters for what a condition on reached states gives there. Of FrameLeft9's fields the
three on "items" have that fence; the eight others are asked, and can be paid, with no fence. At a
marked statement the promise says nothing but "decodes"; at an unmarked one it says of the state's
book of trees three sizes alone: a sentence that reads the strings through that book needs more.

  quietB_full, quiet_at   the table's row at each of the 51 places closes and opens no class of rows
                    and no pin: by Lean's kernel
  qBehindB_full, q_behind9   at the border behind a "cleared" the open public items (those tied to
                    open items apart) are at most "no reply is heard yet": by Lean's kernel
  same26            the 26 numbers at which the state is handed on: the front and every "laid"
  InK               what is known in front of number k
  Strings3          the three fields that read the strings, at one state, under Stays
  ride_same9        LettersRide at a step that hands the state on, from Strings3 and the field
                    "items" itself (at the step's own yes)
  FrameLeft9        WHAT IS LEFT, eleven fields: at the 26: Strings3 and "items"; at "cleared":
                    decodes, shown, noColl, items; "writing one message's ledger changes no stored
                    OOD sample"; the three sentences on Hold
  held_clear9       "held" over "cleared"
  ride_clear9       LettersRide at "cleared": "pubP" by mgAll_pubP_said
  frameOwes9        FrameOwesR at mgAll Dm mgBase, from FrameLeft9, "E lays nothing at the 51
                    numbers" and "N's numbers of trees and messages do not move across them"

Limits. FrameLeft9 is shown at nothing here. N and Dm.N, X and Z.p.X, Dm.links and the written list,
headLink X and 24 are tied by nothing here: it can be met at values that do not fit each other, and
then the ties speak of a table and a meaning that do not fit. Where Dm.decT never answers the
promise is false everywhere: most fields then hold trivially and the ties say nothing. No soundness
statement.

-/
import Johnson.P1L20R.FrameAt9
import Johnson.P1L20R.FrameSitsR
import Johnson.Top.H0.Walk.FrameRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block Chain FileDescription Place KindName Strs smpHeld Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers start openSets pubSets rowOf
  flatPlacesOf quietRow sampledIn openSets_succ sampledIn_step pubSets_succ)
open Johnson.Desc.First.Walk (layFront clearWith LinkPub)
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)

/-- A test with code: the table's row at each of the 51 places is a quiet one. -/
def quietB : Bool :=
  our51.all fun k =>
    match (flatPlacesOf linksFull true)[k]? with
    | some p => quietRow (rowOf linksFull p)
    | none => false

set_option maxRecDepth 1000000 in
theorem quietB_full : quietB = true := by decide +kernel

theorem quiet_at {k : ℕ} (hk : k ∈ our51) {p : Place}
    (hp : (flatPlacesOf linksFull true)[k]? = some p) : quietRow (rowOf linksFull p) = true := by
  have h := List.all_eq_true.1 quietB_full k hk
  rw [hp] at h
  exact h

/-- A test with code: the list has a border behind each "cleared", and the public items that are
open there are at most "no reply is heard yet". -/
def qBehindB : Bool :=
  (List.range 25).all fun l =>
    ((pubSets mgMore linksFull (flatPlacesOf linksFull true))[clearIx l + 1]?).isSome &&
    ((pubSets mgMore linksFull (flatPlacesOf linksFull true))[clearIx l + 1]?.getD []).all fun q =>
      q == Pub.unheard

set_option maxRecDepth 1000000 in
theorem qBehindB_full : qBehindB = true := by decide +kernel

/-- The 26 numbers at which the state is handed on: the front and every "laid". -/
def same26 : List ℕ := 0 :: (List.range 25).map fun l => 14 * l + 1

theorem same_front : 0 ∈ same26 := List.mem_cons_self

theorem same_laid {l : ℕ} (hl : l < 25) : 14 * l + 1 ∈ same26 :=
  List.mem_cons_of_mem _ (List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩)

theorem same_our {k : ℕ} (hk : k ∈ same26) : k ∈ our51 := by
  unfold same26 at hk
  unfold our51
  rcases List.mem_cons.1 hk with rfl | h
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_append_left _ h)

theorem mem_our_front : 0 ∈ our51 := List.mem_cons_self

theorem mem_our_laid {l : ℕ} (hl : l < 25) : 14 * l + 1 ∈ our51 :=
  List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩))

theorem mem_our_clear {l : ℕ} (hl : l < 25) : clearIx l ∈ our51 :=
  List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩))

/-- The items that are open at border k, as the promise reads them. -/
abbrev openL9 (k : ℕ) : List Item :=
  (openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[k]?.getD []

/-- The items that are open at border k, as the relation reads them. -/
abbrev openP9 (k : ℕ) : Item → Prop :=
  openAfter (insQ linksFull (flatPlacesOf linksFull true))
    (outsQ linksFull (flatPlacesOf linksFull true)) (· ∈ start linksFull) k

/-- **What is known in front of number k**: the table's promise there, and Kn k. -/
abbrev InK {P W : Type} (N : Numbers) (Mg : Meaning P W) (Kn : ℕ → P × S → Strs → Prop) (k : ℕ) :
    P × S → Strs → Prop :=
  fun a y => FrontAt N Mg linksFull (flatPlacesOf linksFull true) k a y ∧ Kn k a y

/-- The three fields that read the strings, at one state. -/
structure Strings3 {P W : Type} (N : Numbers) (Mg : Meaning P W) (base : ℕ) (O : List Item) :
    Prop where
  decodes : ∀ a y y', Stays base y y' → Mg.decodes a y → Mg.decodes a y'
  shown : ∀ x y y', Stays base y y' → x ∈ sampledIn N O → Mg.shown x.1 x.2 y → Mg.shown x.1 x.2 y'
  noColl : ∀ a x y y', Stays base y y' → x ∈ sampledIn N O → Mg.noColl x.1 x.2 a y →
    Mg.noColl x.1 x.2 a y'

/-- **LettersRide at a step that hands the state on.** -/
theorem ride_same9 {P W : Type} {N : Numbers} {Mg : Meaning P W} {Kn : ℕ → P × S → Strs → Prop}
    {k : ℕ} {pk : Place} {base : ℕ} {f : S → Except String S} (hf : ∀ s t, f s = .ok t → t = s)
    (hk : (flatPlacesOf linksFull true)[k]? = some pk)
    (hq : quietRow (rowOf linksFull pk) = true) (ho : (rowOf linksFull pk).outs = [])
    (hm : DoorIdle Mg linksFull pk) (H : Strings3 N Mg base (openL9 k))
    (hI : ∀ p s t y y' w i, Yes f s t → Stays base y y' → s.failed = none → InK N Mg Kn k (p, s) y →
      openP9 (k + 1) i → i.holds N Mg (p, t) y' w → i.holds N Mg (p, s) y w) :
    LettersRide N Mg (Yes f) base (InK N Mg Kn k)
      (openL9 (k + 1)) ((pubSets Mg.more linksFull (flatPlacesOf linksFull true))[k + 1]?.getD [])
      (openP9 (k + 1)) := by
  have eS : sampledIn N (openL9 (k + 1)) = sampledIn N (openL9 k) := by
    show sampledIn N ((openSets linksFull (flatPlacesOf linksFull true)
      (start linksFull))[k + 1]?.getD []) = _
    rw [openSets_succ linksFull (flatPlacesOf linksFull true) (start linksFull) k pk hk]
    exact sampledIn_step N _ _ hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hI⟩
  · intro p s t y y' e hy h
    obtain rfl := hf s t e
    exact H.decodes _ _ _ hy h
  · intro p s t y e hu hF
    obtain rfl := hf s t e
    exact (front_parts hu hF.1).1
  · intro p s t y q e hu hF hx
    obtain rfl := hf s t e
    exact pub_of_kept hk ho hm hu hF.1 hx
  · intro p s t y q e hu hF hx
    obtain rfl := hf s t e
    rw [pubSets_succ Mg.more linksFull (flatPlacesOf linksFull true) k pk hk] at hx
    exact (front_parts hu hF.1).2.2 q (mem_pubStep hm hx)
  · intro p s t y x e hu hF hx
    obtain rfl := hf s t e
    rw [eS] at hx
    exact ((front_parts hu hF.1).2.1 x hx).1
  · intro p s t y y' x e hy hu hF hx
    rw [eS] at hx
    exact H.shown x _ _ hy hx ((front_parts hu hF.1).2.1 x hx).2.1
  · intro p s t y y' x e hy hu hF hx
    obtain rfl := hf s t e
    rw [eS] at hx
    exact H.noColl _ x _ _ hy hx ((front_parts hu hF.1).2.1 x hx).2.2

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR X)

theorem q_behind9 {l : ℕ} (hl : l < 25) {q : Pub}
    (hq : q ∈ (pubSets (mgAll Dm mgBase).more linksFull
      (flatPlacesOf linksFull true))[clearIx l + 1]?.getD []) : q = Pub.unheard := by
  rw [mgAll_more_base] at hq
  have h0 := List.all_eq_true.1 qBehindB_full l (List.mem_range.2 hl)
  simp only [Bool.and_eq_true] at h0
  exact eq_of_beq (List.all_eq_true.1 h0.2 q hq)

/-- **"held" over "cleared"**, from "writing one message's ledger changes no stored OOD sample". -/
theorem held_clear9
    (hLay : ∀ (st : OnBytes.Statement) (o : ℕ) (l' : OnBytes.Ledger) (book : OnBytes.TreeBook)
      (j t : ℕ), smpHeld (VerifiableInference.Desc.K13.Law.layLedger st o l') book j t =
        smpHeld st book j t)
    {Xl : LinkPub} {counts : S → Except String Unit}
    {left : S → Option OnBytes.Model.WsForkOut} {lay : OnBytes.Model.WsLay}
    {lin : OnBytes.Params.LinShape} {s t : S}
    (h : clearWith Xl counts left
      (fun im w n os => VerifiableInference.Desc.First.Pend.pendingRowO lay im w n lin os) s =
        .ok t) (p : ProofFile.InstPub) (j i : ℕ) :
    (mgAll Dm mgBase).held j i (p, t) = (mgAll Dm mgBase).held j i (p, s) := by
  rw [mgAll_held]
  show smpHeld t.st t.book j i = smpHeld s.st s.book j i
  have g := clearedGives Xl counts left lay lin s t h
  rw [g.2.2.2.1]
  cases hv : Xl.fv with
  | false => rw [(g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hv).2]
  | true =>
    obtain ⟨_, _, l', _, _, _, _, hst, _⟩ := cleared_st h hv
    rw [hst, hLay]

end

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {C : CK} {D : WholeD} {all : List LeftT}
  {X₁ X₂ Xi Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  {T : ThreeAt C D all
    (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
    X₁ X₂ (Wit (CellsQ rows cols) Tok MsgT)}

/-- **WHAT IS LEFT OF THE FRAME's DEBTS AT THE COMPOSED MEANING**, a field a debt. -/
structure FrameLeft9 (N : Numbers) (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR X) (Z : ProofFile.Pub)
    (T : ThreeAt C D all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ (Wit (CellsQ rows cols) Tok MsgT))
    (Hold : ProofFile.InstPub × S → Wit (CellsQ rows cols) Tok MsgT → OnBytes.TensorRow → Prop)
    (Kn : ℕ → ProofFile.InstPub × S → Strs → Prop) : Prop where
  /-- the three fields that read the strings, at one state, at the front and at "laid" -/
  sSame : ∀ k, k ∈ same26 → ∀ q, (T.p₁ :: T.l₁)[k]? = some q →
    Strings3 N (mgAll Dm mgBase) q.base (openL9 k)
  /-- "items" at the front -/
  iFront : ∀ q, (T.p₁ :: T.l₁)[0]? = some q → ∀ p s t y y' w i, Yes .ok s t → Stays q.base y y' →
    s.failed = none → InK N (mgAll Dm mgBase) Kn 0 (p, s) y → openP9 1 i →
    i.holds N (mgAll Dm mgBase) (p, t) y' w → i.holds N (mgAll Dm mgBase) (p, s) y w
  /-- "items" at "laid", at the step's own yes -/
  iLaid : ∀ l, l < 25 → ∀ q, (T.p₁ :: T.l₁)[14 * l + 1]? = some q → ∀ p s t y y' w i,
    Yes (layFront l) s t → Stays q.base y y' → s.failed = none →
    InK N (mgAll Dm mgBase) Kn (14 * l + 1) (p, s) y → openP9 (14 * l + 1 + 1) i →
    i.holds N (mgAll Dm mgBase) (p, t) y' w → i.holds N (mgAll Dm mgBase) (p, s) y w
  /-- writing one message's ledger changes no stored OOD sample -/
  heldLay : ∀ (st : OnBytes.Statement) (o : ℕ) (l' : OnBytes.Ledger) (book : OnBytes.TreeBook)
    (j t : ℕ), smpHeld (VerifiableInference.Desc.K13.Law.layLedger st o l') book j t =
      smpHeld st book j t
  /-- "decodes" over "cleared" -/
  cDecodes : ∀ l, l < 25 → ∀ fs f,
    Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs →
    fs[l]? = some f → ∀ q, (T.p₁ :: T.l₁)[clearIx l]? = some q → ∀ p s t y y',
    f.clear s = .ok t → Stays q.base y y' → (mgAll Dm mgBase).decodes (p, s) y →
    (mgAll Dm mgBase).decodes (p, t) y'
  /-- "shown" over "cleared" -/
  cShown : ∀ l, l < 25 → ∀ q, (T.p₁ :: T.l₁)[clearIx l]? = some q → ∀ y y' x,
    Stays q.base y y' → x ∈ sampledIn N (openL9 (clearIx l)) →
    (mgAll Dm mgBase).shown x.1 x.2 y → (mgAll Dm mgBase).shown x.1 x.2 y'
  /-- "no collision" over "cleared" -/
  cNoColl : ∀ l, l < 25 → ∀ fs f,
    Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs →
    fs[l]? = some f → ∀ q, (T.p₁ :: T.l₁)[clearIx l]? = some q → ∀ p s t y y' x,
    f.clear s = .ok t → Stays q.base y y' → x ∈ sampledIn N (openL9 (clearIx l)) →
    (mgAll Dm mgBase).noColl x.1 x.2 (p, s) y → (mgAll Dm mgBase).noColl x.1 x.2 (p, t) y'
  /-- "items" at "cleared" -/
  cItems : ∀ l, l < 25 → ∀ fs f,
    Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs →
    fs[l]? = some f → ∀ q, (T.p₁ :: T.l₁)[clearIx l]? = some q → ∀ p s t y y' w i,
    Yes f.clear s t → Stays q.base y y' → s.failed = none →
    InK N (mgAll Dm mgBase) Kn (clearIx l) (p, s) y → openP9 (clearIx l + 1) i →
    i.holds N (mgAll Dm mgBase) (p, t) y' w → i.holds N (mgAll Dm mgBase) (p, s) y w
  /-- "wo l" follows from Hold of the row that rowAt gives -/
  wo : ∀ l, l < 25 → ∀ X', Z.p.built.links[l]? = some X' → X'.fv = true → ∀ a y w,
    (∀ r, Johnson.Desc.First.Walk.Law.rowAt Z.p.X.layers.wsLay X'.NCL Z.first.lin a.2 = some r →
      Hold a w r) → (mgAll Dm mgBase).wo l a y w
  /-- Hold goes back over "cleared" -/
  holdBack : ∀ l, l < 25 → ∀ fs f,
    Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs →
    fs[l]? = some f → ∀ p s t w r, f.clear s = .ok t → Hold (p, t) w r → Hold (p, s) w r
  /-- "pile" gives Hold of every pending row, where the chain stands between two links -/
  pile : ∀ a y w, a.2.atBetween = true → (mgAll Dm mgBase).pile a y w →
    ∀ r ∈ a.2.out.pending, Hold a w r

variable {N : Numbers} {Dm : MgData Xi ProofFile.InstPub Tok rows cols nR X}
  {Hold : ProofFile.InstPub × S → Wit (CellsQ rows cols) Tok MsgT → OnBytes.TensorRow → Prop}
  {Kn : ℕ → ProofFile.InstPub × S → Strs → Prop}

/-- **LettersRide at "cleared"**, at the composed meaning. -/
theorem ride_clear9 (H : FrameLeft9 N Dm Z T Hold Kn) {l : ℕ} (hl : l < 25)
    {fs : List Johnson.Desc.First.Walk.Seat.LinkFrame} {f : Johnson.Desc.First.Walk.Seat.LinkFrame}
    (hfs : Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs)
    (hf : fs[l]? = some f)
    {q : Piece C (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) Cl
      (Wit (CellsQ rows cols) Tok MsgT)}
    (hq : (T.p₁ :: T.l₁)[clearIx l]? = some q) :
    RideAt N (mgAll Dm mgBase) f.clear q.base (clearIx l)
      (InK N (mgAll Dm mgBase) Kn (clearIx l)) := by
  obtain ⟨_, Xl, counts, left, e, _⟩ :=
    Johnson.Desc.First.Walk.Seat.framesOf_row hfs (List.mem_of_getElem? hf)
  obtain ⟨pk, hk, _, _⟩ := door_idle9 Dm (mem_our_clear hl)
  have eS : sampledIn N (openL9 (clearIx l + 1)) = sampledIn N (openL9 (clearIx l)) := by
    show sampledIn N ((openSets linksFull (flatPlacesOf linksFull true)
      (start linksFull))[clearIx l + 1]?.getD []) = _
    rw [openSets_succ linksFull (flatPlacesOf linksFull true) (start linksFull) (clearIx l) pk hk]
    exact sampledIn_step N _ _ (quiet_at (mem_our_clear hl) hk)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, H.cItems l hl fs f hfs hf q hq⟩
  · intro p s t y y' hy hst h
    exact H.cDecodes l hl fs f hfs hf q hq p s t y y' hy hst h
  · intro p s t y _ hu hF
    exact inOrder9 Dm p s t (front_parts hu hF.1).1
  · intro p s t y x hy hu hF hx
    have hy' : f.clear s = .ok t := hy
    rw [e] at hy'
    exact pub_clear9 Dm hl p s t y x hy' hu hF.1 hx
  · intro p s t y x _ _ _ hx
    rw [q_behind9 Dm hl hx]
    exact mgAll_pubP_said Dm Pub.unheard _ rfl
  · intro p s t y x hy hu hF hx
    have hy' : f.clear s = .ok t := hy
    rw [e] at hy'
    rw [eS] at hx
    rw [held_clear9 Dm H.heldLay hy']
    exact ((front_parts hu hF.1).2.1 x hx).1
  · intro p s t y y' x _ hst hu hF hx
    rw [eS] at hx
    exact H.cShown l hl q hq y y' x hst hx ((front_parts hu hF.1).2.1 x hx).2.1
  · intro p s t y y' x hy hst hu hF hx
    rw [eS] at hx
    exact H.cNoColl l hl fs f hfs hf q hq p s t y y' x hy hst hx
      ((front_parts hu hF.1).2.1 x hx).2.2

/-- **FrameOwesR at the composed meaning.** E: an extractor that lays nothing at the 51 numbers (the
table's own: ext_lays_nothing); N: numbers that do not move across them (off what the sub-protocols
tell: none_between_at, FrameNoneAt.lean). -/
theorem frameOwes9 (H : FrameLeft9 N Dm Z T Hold Kn)
    (E : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → Wit (CellsQ rows cols) Tok MsgT →
      Wit (CellsQ rows cols) Tok MsgT)
    (hE : (∀ a b w, E 0 a b w = w) ∧ (∀ l, l < 25 → ∀ a b w, E (14 * l + 1) a b w = w) ∧
      ∀ l, l < 25 → ∀ a b w, E (clearIx l) a b w = w)
    (hN : NoneBetween N (flatPlacesOf linksFull true) 0 ∧
      (∀ l, l < 25 → NoneBetween N (flatPlacesOf linksFull true) (14 * l + 1)) ∧
      ∀ l, l < 25 → NoneBetween N (flatPlacesOf linksFull true) (clearIx l)) :
    FrameOwesR (T := T) N (mgAll Dm mgBase) Z E Hold (InK N (mgAll Dm mgBase) Kn) where
  eFront := hE.1
  eLaid := hE.2.1
  eClear := hE.2.2
  nFront := hN.1
  nLaid := hN.2.1
  nClear := hN.2.2
  rFront := fun q hq => by
    obtain ⟨pk, hk, hm, ho⟩ := door_idle9 Dm mem_our_front
    exact ride_same9 (fun s t e => (Except.ok.inj e).symm) hk (quiet_at mem_our_front hk) ho
      hm (H.sSame 0 same_front q hq) (H.iFront q hq)
  rLaid := fun l hl q hq => by
    obtain ⟨pk, hk, hm, ho⟩ := door_idle9 Dm (mem_our_laid hl)
    exact ride_same9
      (fun s t e => (Johnson.Desc.First.Walk.Law.layFront_ok e).1) hk
      (quiet_at (mem_our_laid hl) hk) ho hm (H.sSame _ (same_laid hl) q hq) (H.iLaid l hl q hq)
  rClear := fun l hl fs f hfs hf q hq =>
    ⟨ride_clear9 H hl hfs hf hq, fun X' hX' hv =>
      ⟨fun a y w h => H.wo l hl X' hX' hv a y w h,
        fun p s t _ w r hy _ h => H.holdBack l hl fs f hfs hf p s t w r hy h⟩⟩
  pile := H.pile

end

end P1L20

#print axioms P1L20.quietB_full
#print axioms P1L20.qBehindB_full
#print axioms P1L20.ride_same9
#print axioms P1L20.held_clear9
#print axioms P1L20.ride_clear9
#print axioms P1L20.frameOwes9
