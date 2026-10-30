-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/GoAtLaterForms.lean: THREE RIDING
ITEMS OF THE TABLE OF JOINTS (forms m k r, formsT m k r, constr k p) GO BACK OVER A YES OF K1's TWO
SORTS OF LATER BLOCK: where the item's sentence holds of the chain's state behind, it holds of the
state in front, at one witness. AND R1: behind the reads' sending the public item formsIn m k r
holds, from formsInT m k r in front. Statements with their proofs. The letter after
has the type that the runs' forms' layer gives it (by segment).

OBJECT. The blocks: any B with LaterSend P B (Johnson/Desc/K1/Law/PubAtLaterIndex.lean)
and LaterGrows B (here); members of both: laterAt (a link's digits) and IM.k1Reads (a
link's reads with the quiet step behind). The sentences: the fields forms | formsT of
Sound.meaningForms D.cs arr ms D.Rd D.runs St after D.N wt rwB D.ah Mg, at any Mg
(Johnson/Desc/Sound/BordersForms.lean; the composed meaning's are these: mgAll_forms | _formsT);
P5J.constrQAt (Johnson/P5J/MeansQ.lean; mgAll_constr). The Bools: pubAll D base.
USER. The premise hgo of TiedAtLater.lean's block_tied at these three constructors; the
premise hpub of k01_reads_tied (R1). The yes is taken as B.decide x.2 rs gs = .ok x'.2 with
rs.length = 2: TiedAtLater.lean is not imported.
LETTERS. D, arr, ms, St, after, wt, rwB, Mg, base; hd, put, H, headPart, digitsPart, decT.

PROVED HERE.
  LaterGrows B · laterGrows_commitAtS | _laterAt | _joined | _k1Reads: a yes lets the statement
    only grow (Grows, Johnson/Desc/Grows.lean), on any rounds.
  segAt_st · rides_of_part · rides_of_rec: **Rides own a b**
    (Johnson/Desc/Sound/FormsQ.lean) from PartRides, Grows and "the book in front has a place for
    just the statement's messages".
  formsQ_back · formsTQ_back · formsQA_back': one run's sentence goes back.
  aheadIn_there · dataQA_cell_none | _some · cellQA_back: a cell that a form names in front is the
    same off both parts: found at both; ahead at both; or ahead in front and sent behind (hmeet).
  forms_back · formsT_back · go_forms_later · go_formsT_later: **the two items.**
  constr_back · constr_back_one: **the third**: a routing.
  seatAt_mono · entIn_mono · slotIn_mono · affIn_new · formsIn_new · pub_formsIn_new ·
    pub_formsIn_new_later: **R1.**
PREMISES THAT STAY, BY NAME.
  hl          THE READER GIVES ONE ANSWER at both states (an equation; other files' riders
              ask it so): on the letter D.Rd. R1 asks the arrow alone (ReadersStay).
  hin         the tied public item in front: the promise in front holds it.
  hfull       the promise's clause on the book (bookAt's second conjunct).
  hwt         on the letter wt, at the name "weights" alone.
  StatedSame  on the letter St (formsT alone).
  AheadMeets  THE CROSSING, asked only where a run of the item is marked by D.ah: an array that is
              ahead in front and found behind under a new number sits, by the book behind, at the
              seat that the plan's rule gives, with the plan's bits.
  SecondFound R1 alone: each array of the segment's second sending is found behind under a new
              number.
  constr      dec (or: the cells are left, and decT answers alike) · req · headPart · digitsPart:
              ALL FOUR ON LETTERS.
A FIND. AheadMeets and SecondFound both want that THE FRAME's LIST "own" IS NUMBERED AS THE SHAPE's
MESSAGES (own.size = the number of the link's messages of earlier moments, these standing in the
order of the moments): NO CLAUSE OF THE PROMISE SAYS SO, and AheadMeets wants the plan's list
D.N.sent m t IN ORDER, where laterSeatsB holds its members alone.

WHO RIDES WHERE, by a look through Lean at the table's own lists: forms l k r
rides at the digits' places alone; constr at both sorts; formsT RIDES PAST NONE OF THE FIFTY (the
reads' row closes it): go_formsT_later, formsT_back, StatedSame have no user at K1's later places.
IS IT EMPTY HERE? That a block says yes, that a reader with one answer is laid in, that AheadMeets,
SecondFound or StatedSame can be met at the plan's own numbers: not shown.
What is not claimed. Anything on the other riding items. Nothing on soundness, on an honest prover
or on hiding.

-/
import Johnson.Desc.K1.Law.PubAtLaterIndex
import Johnson.Desc.K1.KeepsAtS
import Johnson.Desc.Sound.MgAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S Pub PubData pubAll Meaning)
open VerifiableInference.Desc.Ground (By groundKeeps_grows)
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc.K9 (Read Readers segAt? mergeOf seatAt arrayIn arrayIn_some entIn
  entIn_some maskAt lateOk slotIn affIn formsIn formsInT Ahead aheadOf aheadIn entInA affInA
  formsInA rowBitsOf placeBitsOf rowBits_of placeBits_of atMoment1 entInT affInT maskSeat
  formsInA_of_formsIn)
open VerifiableInference.Desc.Sound (Rides MsgQ dataQ dataQA cellA formsQ formsTQ formsQA Stated
  formsQ_rides formsTQ_rides formsQA_back cell_rides mask_rides slotIn_mask cellA_meets)

variable {Cl Pp : Type}

/-! ## 1 The statement only grows -/

/-- A yes of B, on any rounds, lets the statement only grow. -/
def LaterGrows (B : Block S Cl) : Prop :=
  ∀ s s' rs gs, B.decide s rs gs = .ok s' → Grows s.st s'.st

theorem laterGrows_commitAtS (P : Par) (link moment : Nat) (arrays : Option (List Nat)) :
    LaterGrows (commitAtS P link moment arrays : Block S Cl) :=
  fun s s' rs gs h => Rel.commitAtS_keeps groundKeeps_grows P link moment arrays s rs gs s' h

/-- The first member: a segment's later moment at the plan's numbers (a link's digits). -/
theorem laterGrows_laterAt (q : Params.First) (gp : _root_.Desc.Plain.GPar)
    (link piece moment : Nat)
    (arrays : Option (List Nat)) :
    LaterGrows (laterAt q gp link piece moment arrays : Block S Cl) :=
  laterGrows_commitAtS _ _ _ _

theorem laterGrows_joined (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (nm : String)
    (q : Block S Cl) (hq : QuietP q) :
    LaterGrows (Block.andThen nm (commitAtS P link moment arrays) q) := by
  intro s s' rs gs h
  have h' : ((commitAtS P link moment arrays : Block S Cl).decide s
      (rs.take (commitAtS P link moment arrays : Block S Cl).rounds.length)
      (gs.take (commitAtS P link moment arrays : Block S Cl).openings)).bind (fun s₁ =>
      q.decide s₁ (rs.drop (commitAtS P link moment arrays : Block S Cl).rounds.length)
        (gs.drop (commitAtS P link moment arrays : Block S Cl).openings)) = .ok s' := h
  obtain ⟨s₁, h1, h2⟩ := (bind_ok _ _ _).1 h'
  rw [(hq _ _ _ _ h2).1]
  exact laterGrows_commitAtS P link moment arrays _ _ _ _ h1

/-- The second member: the reads' place's joined block. -/
theorem laterGrows_k1Reads (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : Nat) (X : LinkH) (pr : Nat)
    (reads : Option (List Nat)) : LaterGrows (IM.k1Reads Z G l X pr reads) :=
  laterGrows_joined _ _ _ _ _ _ (quietP_orLoud _ _ _ G l X _)

/-! ## 2 The later part rides on the earlier one -/

theorem segAt_st {s : S} {a : K9.Part} (h : segAt? s = some a) : a.d.st = s.st := by
  unfold segAt? at h
  cases hL : s.link? with
  | none => simp [hL] at h
  | some L =>
    cases hF : s.fork? with
    | none => simp [hL, hF] at h
    | some F =>
      cases ht : s.tl? with
      | none => simp [hL, hF, ht] at h
      | some tl =>
        simp [hL, hF, ht] at h
        subst h
        rfl

/-- **Rides** (FormsQ.lean), from what the tests on forms read of the part (PartRides), a statement
that has only grown, and a book in front that names no message which the statement lacks. -/
theorem rides_of_part {new : List Nat} {a b : K9.Part} (R : PartRides new a b)
    (g : Grows a.d.st b.d.st) (hfull : a.d.book.place.size ≤ a.d.st.oracles.size)
    (own : List (Nat × Nat)) : Rides own a b := by
  refine ⟨R.arrayOf, R.rows, R.there, ?_, R.place, ?_, ?_⟩
  · intro o ho
    have ho' : maskAt a.L.check.frame = some o := ho
    show maskAt b.L.check.frame = some o
    unfold maskAt at ho' ⊢
    obtain ⟨m, hm, hw⟩ := Option.bind_eq_some_iff.1 ho'
    rw [R.shape, R.link, hm]
    exact R.there _ _ _ hw
  · intro o x part hx
    unfold seatAt at hx
    obtain ⟨y, hy, _⟩ := Option.bind_eq_some_iff.1 hx
    have h1 : o < a.d.book.place.size := by
      by_contra hn
      rw [Array.getElem?_eq_none (by omega)] at hy
      cases hy
    have ho : o < a.d.st.oracles.size := by omega
    obtain ⟨X', hX', hg⟩ := g.2.2 o _ (Array.getElem?_eq_getElem ho)
    rw [rowBits_of _ o _ part hX', placeBits_of _ o _ part hX',
      rowBits_of _ o _ part (Array.getElem?_eq_getElem ho),
      placeBits_of _ o _ part (Array.getElem?_eq_getElem ho), hg.1, g.1]
    exact ⟨rfl, rfl⟩
  · intro j _ _
    rw [R.slots.vp, R.slots.mf]
    exact ⟨rfl, rfl⟩

/-- The same of two states of the chain. -/
theorem rides_of_rec {new : List Nat} {s s' : S} (R : RecRides new s s') (g : Grows s.st s'.st)
    (hfull : s.book.place.size = s.st.oracles.size) (own : List (Nat × Nat)) {a : K9.Part}
    (ha : segAt? s = some a) :
    ∃ b, segAt? s' = some b ∧ PartRides new a b ∧ Rides own a b ∧
      b.d.st.codes = a.d.st.codes := by
  obtain ⟨b, hb, hR⟩ := R.seg a ha
  obtain ⟨_, _, _, _, ebk⟩ := segAt_some ha
  have ea := segAt_st ha
  have eb := segAt_st hb
  exact ⟨b, hb, hR, rides_of_part hR (by rw [ea, eb]; exact g)
    (Nat.le_of_eq (by rw [ebk, ea, hfull])) own, by rw [ea, eb]; exact g.1⟩

/-! ## 3 One run's sentence goes back -/

/-- A PREMISE ON THE LETTER St: the stated data agree at both states at what the reader's forms
name (formsTQ_rides, Johnson/Desc/Sound/FormsQ.lean, asks it so). -/
def StatedSame (St : Stated) (Rd : Readers) (own : List (Nat × Nat)) (piece : Nat) (run : String)
    (s s' : S) (rd : Nat × Nat → MsgQ) : Prop :=
  ∀ a b, segAt? s = some a → segAt? s' = some b → ∀ X : Read, Rd.forms piece run s = some X →
    ∀ f ∈ X.forms,
      (∀ x ∈ f.ents.toList, ∀ c : Nat × String, a.L.arrayOf[x.tree]? = some c →
        (St.at1 s' (dataQ own b rd)).cell c.1 c.2 x.row x.idx =
          (St.at1 s (dataQ own a rd)).cell c.1 c.2 x.row x.idx) ∧
      ∀ x ∈ f.slots.toList,
        (St.at1 s' (dataQ own b rd)).mask x.1 = (St.at1 s (dataQ own a rd)).mask x.1

section
variable {new : List Nat} {s s' : S} (R : RecRides new s s') (g : Grows s.st s'.st)
  (hfull : s.book.place.size = s.st.oracles.size) (Rd : Readers) (own : List (Nat × Nat))
  (piece : Nat) (run : String) (rd : Nat × Nat → MsgQ)
  (hl : Rd.forms piece run s' = Rd.forms piece run s)
include R g hfull hl

/-- **"forms" at one run.** -/
theorem formsQ_back (hin : formsIn Rd own piece run s = true)
    (h : formsQ Rd own piece run s' rd) : formsQ Rd own piece run s rd := by
  cases ea : segAt? s with
  | none =>
    unfold formsIn at hin
    rw [ea] at hin
    cases hin
  | some a =>
    obtain ⟨b, hb, _, hr, _⟩ := rides_of_rec R g hfull own ea
    exact formsQ_rides own Rd piece run s s' a b rd ea hb hl hin hr h

/-- **"formsT" at one run.** -/
theorem formsTQ_back (St : Stated) (hin : formsInT Rd own piece run s = true)
    (hat : StatedSame St Rd own piece run s s' rd) (h : formsTQ Rd St own piece run s' rd) :
    formsTQ Rd St own piece run s rd := by
  cases ea : segAt? s with
  | none =>
    unfold formsInT at hin
    rw [ea] at hin
    cases hin
  | some a =>
    obtain ⟨b, hb, _, hr, _⟩ := rides_of_rec R g hfull own ea
    exact formsTQ_rides own Rd St piece run s s' a b rd ea hb hl hin hr (hat a b ea hb) h

end

/-! ## 4 Where a form may name what is ahead -/

section
variable (sent : Nat → List (Nat × Nat)) (own : List (Nat × Nat))

/-- An array whose message is found is not ahead. -/
theorem aheadIn_there (a : K9.Part) (c : Nat × String) (A : Params.ReqArray) (o : Nat)
    (hA : reqArray a.L.check.rows.layout c.1 c.2 = some A)
    (hw : a.L.check.frame.whereIs c.1 A.message = some o) : aheadIn sent own a c = none := by
  have e : aheadOf sent a c = none := by
    unfold aheadOf
    split
    · simp only [hA, Option.bind_some, hw]
    · rfl
  unfold aheadIn
  rw [e]
  rfl

theorem dataQA_cell_none (a : K9.Part) (rd : Nat × Nat → MsgQ) (c : Nat × String)
    (h : aheadIn sent own a c = none) (i j : Nat) :
    (dataQA sent own a rd).cell c.1 c.2 i j = (dataQ own a rd).cell c.1 c.2 i j := by
  show (match aheadIn sent own a c with
    | some q => cellA a.d.st.codes q rd i j
    | none => (dataQ own a rd).cell c.1 c.2 i j) = _
  rw [h]

theorem dataQA_cell_some (a : K9.Part) (rd : Nat × Nat → MsgQ) (c : Nat × String) (q : Ahead)
    (h : aheadIn sent own a c = some q) (i j : Nat) :
    (dataQA sent own a rd).cell c.1 c.2 i j = cellA a.d.st.codes q rd i j := by
  show (match aheadIn sent own a c with
    | some q => cellA a.d.st.codes q rd i j
    | none => (dataQ own a rd).cell c.1 c.2 i j) = _
  rw [h]

/-- **A cell that a form names in front is the same off both parts.** hmeet: THE CROSSING: an array
that is ahead in front and sent behind sits behind at the plan's seat, with the plan's bits. -/
theorem cellQA_back {new : List Nat} {a b : K9.Part} (R : PartRides new a b) (hr : Rides own a b)
    (hcodes : b.d.st.codes = a.d.st.codes) (rd : Nat × Nat → MsgQ)
    (hmeet : ∀ (c : Nat × String) (hh : Ahead) (o : Nat), aheadIn sent own a c = some hh →
      b.L.check.frame.whereIs c.1 hh.A.message = some o → o ∈ new →
      seatAt own b.d.book o = some hh.seat ∧
        b.d.st.rowBits o .main = rowBitsOf hh.shape .main ∧
        b.d.st.placeBits o .main = placeBitsOf a.d.st.codes hh.shape .main)
    (x : Ent) (hx : entInA sent own a x = true) (c : Nat × String)
    (hc : a.L.arrayOf[x.tree]? = some c) :
    (dataQA sent own b rd).cell c.1 c.2 x.row x.idx =
      (dataQA sent own a rd).cell c.1 c.2 x.row x.idx := by
  unfold entInA at hx
  rw [Bool.or_eq_true] at hx
  rcases hx with hx | hx
  · obtain ⟨A, hA⟩ := entIn_some own a x hx
    obtain ⟨c', o, y, hc', hlay, hw, hy⟩ := arrayIn_some own a x.tree A hA
    obtain rfl : c' = c := Option.some.inj (hc'.symm.trans hc)
    rw [dataQA_cell_none sent own b rd c' (aheadIn_there sent own b c' A o
        (by rw [R.rows]; exact hlay) (R.there _ _ _ hw)),
      dataQA_cell_none sent own a rd c' (aheadIn_there sent own a c' A o hlay hw)]
    exact cell_rides own a b rd hr c' A o y hlay hw hy x.row x.idx
  · rw [hc, Option.bind_some] at hx
    cases e2 : aheadIn sent own a c with
    | none =>
      rw [e2] at hx
      cases hx
    | some hh =>
      have e2' := e2
      unfold aheadIn at e2'
      obtain ⟨e3, e4⟩ := Option.filter_eq_some_iff.1 e2'
      rcases aheadOf_rides R sent e3 with e5 | ⟨o, hA, hw, hn⟩
      · have e6 : aheadIn sent own b c = some hh := by
          unfold aheadIn
          exact Option.filter_eq_some_iff.2 ⟨e5, e4⟩
        rw [dataQA_cell_some sent own b rd c hh e6, dataQA_cell_some sent own a rd c hh e2, hcodes]
      · obtain ⟨m1, m2, m3⟩ := hmeet c hh o e2 hw hn
        exact cellA_meets sent own a b rd c hh o e2
          (aheadIn_there sent own b c hh.A o (by rw [R.rows]; exact hA) hw)
          (by rw [R.rows]; exact hA) hw m1 m2 m3 x.row x.idx

/-- **THE CROSSING, of two states of the chain**: A PREMISE. -/
def AheadMeets (new : List Nat) (s s' : S) : Prop :=
  ∀ (a b : K9.Part) (c : Nat × String) (hh : Ahead) (o : Nat), segAt? s = some a →
    segAt? s' = some b → aheadIn sent own a c = some hh →
    b.L.check.frame.whereIs c.1 hh.A.message = some o → o ∈ new →
    seatAt own b.d.book o = some hh.seat ∧
      b.d.st.rowBits o .main = rowBitsOf hh.shape .main ∧
      b.d.st.placeBits o .main = placeBitsOf a.d.st.codes hh.shape .main

/-- **"forms" at one run whose forms may name what is ahead.** -/
theorem formsQA_back' {new : List Nat} {s s' : S} (R : RecRides new s s')
    (g : Grows s.st s'.st) (hfull : s.book.place.size = s.st.oracles.size) (Rd : Readers)
    (piece : Nat) (run : String) (rd : Nat × Nat → MsgQ)
    (hl : Rd.forms piece run s' = Rd.forms piece run s)
    (hin : formsInA Rd sent own piece run s = true) (hmeet : AheadMeets sent own new s s')
    (h : formsQA sent own Rd piece run s' rd) : formsQA sent own Rd piece run s rd := by
  cases ea : segAt? s with
  | none =>
    unfold formsInA at hin
    rw [ea] at hin
    cases hin
  | some a =>
    obtain ⟨b, hb, hR, hr, hcodes⟩ := rides_of_rec R g hfull own ea
    have hall : ∀ X : Read, Rd.forms piece run s = some X → ∀ f ∈ X.forms,
        (∀ x ∈ f.ents.toList, entInA sent own a x = true) ∧
          ∀ x ∈ f.slots.toList, slotIn own (mergeOf s) X.late a x.1 = true := by
      intro X hX f hf
      unfold formsInA at hin
      rw [ea, hX] at hin
      have h' : (lateOk X.late a &&
          X.forms.all fun f => affInA sent own (mergeOf s) X.late a f) = true := hin
      rw [Bool.and_eq_true, List.all_eq_true] at h'
      have h1 := h'.2 f hf
      unfold affInA at h1
      rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h1
      exact h1
    refine formsQA_back sent own Rd piece run s s' a b rd ea hb hl hin hR.arrayOf hr.filled
      ?_ ?_ h
    · intro X hX f hf x hx c hc
      exact cellQA_back sent own hR hr hcodes rd (fun c hh o => hmeet a b c hh o ea hb) x
        ((hall X hX f hf).1 x hx) c hc
    · intro X hX f hf x hx
      obtain ⟨y, hy⟩ := slotIn_mask own (mergeOf s) X.late a x.1 ((hall X hX f hf).2 x hx)
      exact mask_rides own a b rd hr y hy x.1

end

/-! ## 5 The two items "forms" and "formsT" at the runs' forms' layer -/

section
variable (D : PubData) {Cells Tok : Type} (arr : Nat → Nat → Nat) (ms : List Sound.Mem)
  (St : Stated) (after : Nat → S → Except String S)
  (wt : Nat → Pp × S → Strs → Wit Cells Tok Sound.MsgT → Prop) (rwB : Nat → S → Bool)
  (Mg : Meaning Pp (Wit Cells Tok Sound.MsgT)) (base : Pub → Pp × S → Bool)
  {new : List Nat} {x x' : Pp × S} (R : RecRides new x.2 x'.2) (g : Grows x.2.st x'.2.st)
  (hfull : x.2.book.place.size = x.2.st.oracles.size) (m k : Nat) (r : String)
  (hl : ∀ p ∈ D.runs m k r, (D.Rd m).forms p.1 p.2 x'.2 = (D.Rd m).forms p.1 p.2 x.2)
  (y y' : Strs) (w : Wit Cells Tok Sound.MsgT)
  (hwt : r = "weights" → wt m x' y' w → wt m x y w)
include R g hfull hl hwt

/-- **forms m k r goes back.** -/
theorem forms_back (hin : pubAll D base (.formsIn m k r) x = true)
    (hmeet : ∀ p ∈ D.runs m k r, D.ah p.1 p.2 = true →
      AheadMeets (D.N.sent m) (D.N.group m) new x.2 x'.2)
    (h : (Sound.meaningForms D.cs arr ms D.Rd D.runs St after D.N wt rwB D.ah Mg).forms m k r x' y'
      w) :
    (Sound.meaningForms D.cs arr ms D.Rd D.runs St after D.N wt rwB D.ah Mg).forms m k r x y w := by
  rw [pubAll_formsIn, List.all_eq_true] at hin
  show (∀ p ∈ D.runs m k r,
      if D.ah p.1 p.2 = true then
        formsQA (D.N.sent m) (D.N.group m) (D.Rd m) p.1 p.2 x.2 (Sound.seatTab D.cs arr ms w)
      else formsQ (D.Rd m) (D.N.group m) p.1 p.2 x.2 (Sound.seatTab D.cs arr ms w)) ∧
    (r = "weights" → wt m x y w)
  refine ⟨fun p hp => ?_, fun e => hwt e (h.2 e)⟩
  have h1 := h.1 p hp
  have h2 := hin p hp
  by_cases ha : D.ah p.1 p.2 = true
  · rw [if_pos ha] at h1 h2 ⊢
    exact formsQA_back' _ _ R g hfull _ _ _ _ (hl p hp) h2 (hmeet p hp ha) h1
  · rw [if_neg ha] at h1 h2 ⊢
    exact formsQ_back R g hfull _ _ _ _ _ (hl p hp) h2 h1

/-- **formsT m k r goes back.** -/
theorem formsT_back (hin : pubAll D base (.formsInT m k r) x = true)
    (hat : ∀ p ∈ D.runs m k r, StatedSame St (D.Rd m) (D.N.sent m 0) p.1 p.2 x.2 x'.2
      (Sound.seatTab D.cs arr ms w))
    (h : (Sound.meaningForms D.cs arr ms D.Rd D.runs St after D.N wt rwB D.ah Mg).formsT m k r x' y'
      w) :
    (Sound.meaningForms D.cs arr ms D.Rd D.runs St after D.N wt rwB D.ah Mg).formsT m k r x y
      w := by
  rw [pubAll_formsInT, List.all_eq_true] at hin
  show (∀ p ∈ D.runs m k r,
      formsTQ (D.Rd m) St (D.N.sent m 0) p.1 p.2 x.2 (Sound.seatTab D.cs arr ms w)) ∧
    (r = "weights" → wt m x y w)
  exact ⟨fun p hp => formsTQ_back R g hfull _ _ _ _ _ (hl p hp) St (hin p hp) (hat p hp)
    (h.1 p hp), fun e => hwt e (h.2 e)⟩

end

/-! ## 6 The item "constr" at the model's relation's layer -/

section
variable {X : Model.Verify.Public} {W : Type} {rows cols : Nat}

/-- **constr k p goes back**, at any reading H of the witness. ALL FOUR PREMISES ARE ON LETTERS. -/
theorem constr_back (hd : Nat) (put : P5J.TReq → Fin Inst.Model.ppref.V → P5J.TReq)
    (H : P5J.HidAt X Pp W rows cols)
    (headPart : P5J.TPart → Sound.IdxQ → Pp × S → Strs → W → Prop)
    (digitsPart : Nat → Pp × S → Strs → W → Prop) (k : Nat) (p : P5J.TPart) (x x' : Pp × S)
    (y y' : Strs) (w : W) (hdec : H.dec x' y' = H.dec x y) (hreq : H.req x' = H.req x)
    (hhead : ∀ i, headPart p i x' y' w → headPart p i x y w)
    (hdig : digitsPart k x' y' w → digitsPart k x y w)
    (h : P5J.constrQAt hd put H headPart digitsPart k p x' y' w) :
    P5J.constrQAt hd put H headPart digitsPart k p x y w := by
  unfold P5J.constrQAt at h ⊢
  by_cases hp : p = .lookDigits
  · rw [if_pos hp] at h ⊢
    exact hdig h
  · rw [if_neg hp] at h ⊢
    refine ⟨h.1, fun M i hM hi => ?_⟩
    have h1 := h.2 M i (by rw [hdec]; exact hM) hi
    by_cases hk : k = hd
    · rw [if_pos hk] at h1 ⊢
      exact hhead i h1
    · rw [if_neg hk] at h1 ⊢
      rw [hreq] at h1
      exact h1

end

/-- **The same at the composed meaning's one decoder** (mgAll_constr): the strings' cells are left
(the piece's KeptBelow), and the decoder decT answers at the state behind as in front. -/
theorem constr_back_one {X : Model.Verify.Public} {Tok : Type} {rows cols : Nat}
    (decT : (Nat → Option (Nat × List UInt64)) → Pp × S → Option (Sound.CellsQ rows cols))
    (hd : Nat) (put : P5J.TReq → Fin Inst.Model.ppref.V → P5J.TReq)
    (H : P5J.HidAt X Pp (Wit (Sound.CellsQ rows cols) Tok Sound.MsgT) rows cols)
    (headPart : P5J.TPart → Sound.IdxQ → Pp × S → Strs →
      Wit (Sound.CellsQ rows cols) Tok Sound.MsgT → Prop)
    (digitsPart : Nat → Pp × S → Strs → Wit (Sound.CellsQ rows cols) Tok Sound.MsgT → Prop)
    (k : Nat) (p : P5J.TPart) (x x' : Pp × S) (y y' : Strs)
    (w : Wit (Sound.CellsQ rows cols) Tok Sound.MsgT) (hcell : y'.cell = y.cell)
    (hdecT : ∀ c, decT c x' = decT c x) (hreq : H.req x' = H.req x)
    (hhead : ∀ i, headPart p i x' y' w → headPart p i x y w)
    (hdig : digitsPart k x' y' w → digitsPart k x y w)
    (h : P5J.constrQAt hd put (Sound.oneDec decT H) headPart digitsPart k p x' y' w) :
    P5J.constrQAt hd put (Sound.oneDec decT H) headPart digitsPart k p x y w :=
  constr_back hd put (Sound.oneDec decT H) headPart digitsPart k p x x' y y' w
    (show decT y'.cell x' = decT y.cell x by rw [hcell, hdecT]) hreq hhead hdig h

/-! ## 7 R1: "formsIn" is new behind the reads' sending -/

section
variable {own0 own : List (Nat × Nat)} (hsub : ∀ x ∈ own0, x ∈ own)
include hsub

theorem seatAt_mono {book : TreeBook} {o : Nat} {x : Nat × Nat}
    (e : seatAt own0 book o = some x) : seatAt own book o = some x := by
  unfold seatAt at e ⊢
  obtain ⟨y, h1, hy⟩ := Option.bind_eq_some_iff.1 e
  rw [h1, Option.bind_some]
  by_cases hc : own0.contains y = true
  · rw [if_pos hc] at hy
    have h2 : own.contains y = true := by simpa using hsub y (by simpa using hc)
    rw [if_pos h2]
    exact hy
  · rw [if_neg hc] at hy
    cases hy

theorem entIn_mono {a : K9.Part} {x : Ent} (h : entIn own0 a x = true) :
    entIn own a x = true := by
  obtain ⟨A, hA⟩ := entIn_some own0 a x h
  obtain ⟨c, o, z, h1, h2, h3, h4⟩ := arrayIn_some own0 a x.tree A hA
  have e : arrayIn own a x.tree = some A := by
    simp only [arrayIn, h1, h2, h3, seatAt_mono hsub h4, Option.bind_some, Option.map_some]
  unfold entIn at h ⊢
  rw [hA] at h
  rw [e]
  exact h

theorem slotIn_mono (free : Option Nat) (late : List (Nat × E × E)) {a : K9.Part} {j : Nat}
    (h : slotIn own0 free late a j = true) : slotIn own free late a j = true := by
  unfold slotIn at h ⊢
  rw [Bool.and_eq_true, Bool.and_eq_true] at h ⊢
  refine ⟨h.1, ?_, h.2.2⟩
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 h.2.1
  unfold maskSeat at hz ⊢
  obtain ⟨o, ho, hz⟩ := Option.bind_eq_some_iff.1 hz
  rw [ho, Option.bind_some, seatAt_mono hsub hz]
  rfl

end

/-- A PREMISE: each array of the open segment's second sending is found behind, under a new
number. -/
def SecondFound (new : List Nat) (s s' : S) : Prop :=
  ∀ (a b : K9.Part) (c : Nat × String) (A : Params.ReqArray), segAt? s = some a →
    segAt? s' = some b → reqArray a.L.check.rows.layout c.1 c.2 = some A →
    atMoment1 a c A = true → ∃ o ∈ new, b.L.check.frame.whereIs c.1 A.message = some o

/-- A form that, in front, names only what is there at the first sending's seats or is of the second
sending names, behind, only what is there. -/
theorem affIn_new {new : List Nat} {a b : K9.Part} (R : PartRides new a b)
    {own0 own : List (Nat × Nat)} (hsub : ∀ x ∈ own0, x ∈ own) (free : Option Nat)
    (late : List (Nat × E × E)) (hseat : ∀ o ∈ new, (seatAt own b.d.book o).isSome = true)
    (hfound : ∀ (c : Nat × String) (A : Params.ReqArray),
      reqArray a.L.check.rows.layout c.1 c.2 = some A → atMoment1 a c A = true →
      ∃ o ∈ new, b.L.check.frame.whereIs c.1 A.message = some o)
    {f : Aff} (h : affInT own0 free late a f = true) : affIn own free late b f = true := by
  unfold affInT at h
  unfold affIn
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h ⊢
  refine ⟨fun x hx => ?_, fun x hx => slotIn_rides R own free late
    (slotIn_mono hsub free late (h.2 x hx))⟩
  have h1 := h.1 x hx
  unfold entInT at h1
  rw [Bool.or_eq_true] at h1
  rcases h1 with h1 | h1
  · exact entIn_rides R own (entIn_mono hsub h1)
  · cases e1 : a.L.arrayOf[x.tree]? with
    | none =>
      rw [e1] at h1
      cases h1
    | some c =>
      rw [e1] at h1
      cases e2 : reqArray a.L.check.rows.layout c.1 c.2 with
      | none =>
        simp only [e2] at h1
        cases h1
      | some A =>
        simp only [e2, Bool.and_eq_true] at h1
        obtain ⟨o, hn, hw⟩ := hfound c A e2 h1.1
        obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 (hseat o hn)
        have e6 : arrayIn own b x.tree = some A := by
          simp only [arrayIn, R.arrayOf, e1, R.rows, e2, hw, hz, Option.bind_some,
            Option.map_some]
        unfold entIn
        rw [e6, Bool.and_eq_true]
        exact h1.2

/-- **"formsIn" behind, from "formsInT" in front, at one run.** -/
theorem formsIn_new {new : List Nat} {s s' : S} (R : RecRides new s s') (Rd : Readers)
    {own0 own : List (Nat × Nat)} (hsub : ∀ x ∈ own0, x ∈ own) (piece : Nat) (run : String)
    (hRd : ∀ X, Rd.forms piece run s = some X → Rd.forms piece run s' = some X)
    (hseat : ∀ o ∈ new, (seatAt own s'.book o).isSome = true) (hfound : SecondFound new s s')
    (h : formsInT Rd own0 piece run s = true) : formsIn Rd own piece run s' = true := by
  unfold formsInT at h
  unfold formsIn
  cases ea : segAt? s with
  | none =>
    rw [ea] at h
    cases h
  | some a =>
    cases er : Rd.forms piece run s with
    | none =>
      rw [ea, er] at h
      cases h
    | some X =>
      rw [ea, er] at h
      obtain ⟨b, hb, hR⟩ := R.seg a ea
      obtain ⟨_, _, _, _, hbk⟩ := segAt_some hb
      rw [hb, hRd X er, R.merge]
      have h' : (lateOk X.late a &&
          X.forms.all fun f => affInT own0 (mergeOf s) X.late a f) = true := h
      show (lateOk X.late b && X.forms.all fun f => affIn own (mergeOf s) X.late b f) = true
      rw [Bool.and_eq_true, List.all_eq_true] at h' ⊢
      exact ⟨by rw [lateOk_rides hR]; exact h'.1, fun f hf => affIn_new hR hsub _ _
        (by rw [hbk]; exact hseat) (fun c A => hfound a b c A ea hb) (h'.2 f hf)⟩

/-- **R1: formsIn m k r behind, from formsInT m k r in front**, at the composed Bool. -/
theorem pub_formsIn_new (D : PubData) (base : Pub → Pp × S → Bool) {new : List Nat}
    {x x' : Pp × S} (R : RecRides new x.2 x'.2) (m k : Nat) (r : String)
    (hRd : ReadersStay D m k r x.2 x'.2)
    (hseat : ∀ o ∈ new, (seatAt (D.N.group m) x'.2.book o).isSome = true)
    (hfound : SecondFound new x.2 x'.2) (h0 : pubAll D base (.formsInT m k r) x = true) :
    pubAll D base (.formsIn m k r) x' = true := by
  rw [pubAll_formsInT, List.all_eq_true] at h0
  rw [pubAll_formsIn, List.all_eq_true]
  intro p hp
  have hsub : ∀ z ∈ D.N.sent m 0, z ∈ D.N.group m := fun z hz => by
    unfold First.Numbers.group
    exact List.mem_append_left _ (List.mem_append_left _ hz)
  have h1 := formsIn_new R (D.Rd m) hsub p.1 p.2 (hRd p hp) hseat hfound (h0 p hp)
  by_cases ha : D.ah p.1 p.2 = true
  · rw [if_pos ha]
    exact formsInA_of_formsIn _ _ _ _ _ _ h1
  · rw [if_neg ha]
    exact h1

/-! ## 8 Over the block's own yes -/

section
variable {P : Par} {B : Block S Cl} (hB : LaterSend P B) (hG : LaterGrows B) (D : PubData)
  {Cells Tok : Type} (arr : Nat → Nat → Nat) (ms : List Sound.Mem) (St : Stated)
  (after : Nat → S → Except String S) (wt : Nat → Pp × S → Strs → Wit Cells Tok Sound.MsgT → Prop)
  (rwB : Nat → S → Bool) (Mg : Meaning Pp (Wit Cells Tok Sound.MsgT))
  (base : Pub → Pp × S → Bool) (x x' : Pp × S) (rs : List Fmt.RoundView)
  (gs : List (List (Nat × List UInt64))) (h2 : rs.length = 2)
  (h : B.decide x.2 rs gs = .ok x'.2) (hfull : x.2.book.place.size = x.2.st.oracles.size)
  (m k : Nat) (r : String)

include hB hG h2 h hfull in
/-- **G.forms**: the item's sentence goes back over the block's own yes. -/
theorem go_forms_later
    (hl : ∀ p ∈ D.runs m k r, (D.Rd m).forms p.1 p.2 x'.2 = (D.Rd m).forms p.1 p.2 x.2)
    (y y' : Strs) (w : Wit Cells Tok Sound.MsgT) (hwt : r = "weights" → wt m x' y' w → wt m x y w)
    (hin : pubAll D base (.formsIn m k r) x = true)
    (hmeet : ∀ p ∈ D.runs m k r, D.ah p.1 p.2 = true →
      AheadMeets (D.N.sent m) (D.N.group m) (idsOf P x.2.st.oracles.size).toList x.2 x'.2)
    (h0 : (Sound.meaningForms D.cs arr ms D.Rd D.runs St after D.N wt rwB D.ah Mg).forms m k r x'
      y' w) :
    (Sound.meaningForms D.cs arr ms D.Rd D.runs St after D.N wt rwB D.ah Mg).forms m k r x y w :=
  forms_back D arr ms St after wt rwB Mg base (hB _ _ _ _ h2 h).2.1 (hG _ _ _ _ h) hfull m k r hl
    y y' w hwt hin hmeet h0

include hB hG h2 h hfull in
/-- **G.formsT**: the item's sentence goes back over the block's own yes. -/
theorem go_formsT_later
    (hl : ∀ p ∈ D.runs m k r, (D.Rd m).forms p.1 p.2 x'.2 = (D.Rd m).forms p.1 p.2 x.2)
    (y y' : Strs) (w : Wit Cells Tok Sound.MsgT) (hwt : r = "weights" → wt m x' y' w → wt m x y w)
    (hin : pubAll D base (.formsInT m k r) x = true)
    (hat : ∀ p ∈ D.runs m k r, StatedSame St (D.Rd m) (D.N.sent m 0) p.1 p.2 x.2 x'.2
      (Sound.seatTab D.cs arr ms w))
    (h0 : (Sound.meaningForms D.cs arr ms D.Rd D.runs St after D.N wt rwB D.ah Mg).formsT m k r x'
      y' w) :
    (Sound.meaningForms D.cs arr ms D.Rd D.runs St after D.N wt rwB D.ah Mg).formsT m k r x y w :=
  formsT_back D arr ms St after wt rwB Mg base (hB _ _ _ _ h2 h).2.1 (hG _ _ _ _ h) hfull m k r hl
    y y' w hwt hin hat h0

include hB h2 h hfull in
/-- **R1** over the block's own yes, the new messages' seats paid off the promise's clause on the
book and the row's owner's test on the plan (laterSeatsB, unfolded), as at pub_formsIn_later_plan.
-/
theorem pub_formsIn_new_later (hRd : ReadersStay D m k r x.2 x'.2) (t nT : Nat) (ht : t < 3)
    (hT : x.2.book.trees.size = nT)
    (hs : First.sameMembers ((List.range P.sent.size).map fun i =>
      (nT + (layOf P).tree.getD i 0, (layOf P).part.getD i 0)) (D.N.sent m t) = true)
    (hfound : SecondFound (idsOf P x.2.st.oracles.size).toList x.2 x'.2)
    (h0 : pubAll D base (.formsInT m k r) x = true) : pubAll D base (.formsIn m k r) x' = true :=
  pub_formsIn_new D base (hB _ _ _ _ h2 h).2.1 m k r hRd
    (seats_new (hB _ _ _ _ h2 h).2.2 hfull _
      (by rw [hT]; exact seats_in_group D.N P m t nT ht hs)) hfound h0

end

end VerifiableInference.Desc.K1
