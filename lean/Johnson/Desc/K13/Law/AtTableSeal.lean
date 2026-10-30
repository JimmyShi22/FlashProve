-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/AtTableSeal.lean: THE FIRST CHAIN's LAST BLOCK (the seal: First.firstEnd) AT
ITS ROW OF THE TABLE OF JOINTS: THE FIVE TIES. Definitions and statements with their proofs.

Why. The chain of promises (Johnson/Desc/Sound/ChainOfPromises.lean) asks a tie at EVERY block of
the first chain. Without one at the last block the promise at the chain's last border, from
which the shared and the last chain's first promises are got, is earned by no chain of ties. The
table's row there is EMPTY (it closes, opens and reads nothing), and a yes of the block returns THE
RECORD ITSELF (Keeps.chainEnd_same, Johnson/Desc/Tidy/Still.lean). So every Bool of the promise that
reads the record alone is the same Bool; what turns between the two borders is what the TABLE
computes (the place behind is none; the open sets one step on) and the STRINGS.

OBJECT. First.firstEnd piece front, as a chain holds it: any block c with c.UnderR that block; the
general core: any piece whose yes leaves what the table reads of the chain's record.
USER. EachTied | chainOfPromises: seal_tied, firstEnd_tied_seat and firstEnd_tied_lift end in
TiedAt N Mg links ps get k q, to the letter. seal_own | seal_rides: the first two of the four of
SeatLaws (Johnson/Desc/Sound/TiedSeat.lean): joined in
Johnson/Desc/K13/Law/AtTableSealLaws.lean.
LETTERS. The table's own; B: the piece's base.
FIELD. first_chain_knows_means (Johnson/Goal/Skeleton/ProofFile.lean), through chainOfPromises.

Main names:
  SameBelow B y y' · sameBelow_out   the stored table and every tree below B are as they were; a
    piece leaves them so at its base. THE LIKE STANDS ELSEWHERE, under other full names: tree by
    tree: OldKept | oldKept_out (Johnson/Desc/K13/Law/AtTable.lean); on the raw oracles:
    First.Att.P.SameBelow | piece_same_below (Johnson/Desc/First/Att/K05SeamOut.lean); on
    the readings, the sides in the other order: Sound.SameBelow
    (Johnson/Desc/Sound/SharedJointCountLedger.lean, above the shared table): one
    of the four should stay when the tables meet.
  RowSeal     what is asked of the table at (links, ps, k): the place; its row is empty and lays
    nothing; no place behind; the chain is to stand at its end there and no count may wait; no
    public item comes (one may go: that an item is STILL open behind is another test:
    evalLaid_open, Johnson/Desc/K13/Law/LaidToEnd.lean; wSits_fit, AtTableW.lean); by the plan as
    many trees and messages behind as in front.
  FillSeal    what is asked of the table's letters: THEY READ THE STRINGS BELOW B: "decodes";
    "shown" and "no collision" at the sampled tenants that are open; each item that rides goes BACK
    over strings that agree below B. NOTHING ON THE RECORD: it does not turn.
    ("decodes" is asked over SameBelow,
    as the link's frame's StringsRide asks it: Johnson/Desc/K13/Law/AtTableSealStays.lean.)
  sampled_of_open · stepOpen_empty · seal_ins   small facts on the table's text.
  seal_step   the promise one border on, marked or not: onQ_step_held
    (Johnson/Desc/Sound/PromiseRidesQ.lean): CALLED. "The chain stands at its end, none waits" at
    the last border is taken from the promise IN FRONT, not from anything that the seal tests: so
    the promise at the last border says nothing that the one in front did not.
  seal_own    the block's own law at the table's words, at any errors.
  seal_rides  what rides goes back, at one witness.
  seal_tied   **the five ties**, of any piece with the identity for its extractor whose yes leaves
    get's value. The kind's law in it is the idle one (True behind, True for both relations): the
    row asks nothing.
  pieceSeal · seal_piece   the bare block's piece; its yes returns the record.
  firstEnd_tied_seat · firstEnd_tied_lift   **at any such c**: the chain's record is the carried
    record itself; or a part of it.
  RowSeal as a test with code, and members at both lists: Johnson/Desc/K13/Law/AtTableSealRow.lean.
  FillSeal at the table's files' filling by signature: Johnson/Desc/K13/Law/AtTableSealFill.lean.
  Both halves joined, at the table's files' own filling: Johnson/Desc/K13/Law/AtTableSealJoint.lean.
What is not claimed. NO MEMBER OF FillSeal HERE. gt, st, pub are letters: no member. That a
description's first chain's last entry is that block, at place k, with this stretch AND THIS BASE:
not here: base, ds, back, err are free letters of pieceSeal (at a stretch that does not fit the
block the piece never says yes, and all five ties are free). THE EXTRACTOR's OTHER DEBT (EachExtQ,
Johnson/Desc/Sound/BordersFill.lean: the piece's extractor is the table's): seal_extQ
(Johnson/Desc/K13/Law/AtTableSealFill.lean), from RowSeal.lays. At N := the default numbers (0
everywhere) trees and msgs hold by rfl while bookAt is false of every honest record: there the
promise in front is empty at records without a mark. That the piece's base lies above every
sampled tenant's tree and every riding pin's: inside FillSeal's clauses (they are asked at
SameBelow B: false of a letter that reads a tree at or above B). At Mg.decodes := never all is
free. Nothing on the errors. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K13.Law.AtTable
import Johnson.Desc.K13.Law.SitsMade
import Johnson.Desc.Sound.PromiseRidesQ
import Johnson.Desc.ChainEndGoodIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice Iop Run
open OnBytes.Flat OnBytes.Maker
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More)
open VerifiableInference.Desc.Sound (Frame Piece strsOf onQ meansQ relQ insQ outsQ rowQ TiedAt relAt
  openAfter out_seat liftOut onQ_step_held goodIn_of_sure)

/-! ## 1 The strings -/

/-- The stored table, and every tree below B, are as they were. -/
def SameBelow (B : ℕ) (y y' : Strs) : Prop :=
  y'.cell = y.cell ∧ ∀ j, j < B → ∀ x, y'.col j x = y.col j x

/-- A piece leaves the stored table and every tree that was sent in front of its stretch. -/
theorem sameBelow_out {T Cl W : Type} {C : PQ.CK} {F : Frame} (p : Piece C F T Cl W)
    {a b : T × F.E.Str} {τ : Tr (uLT C p.ds)} (h : p.ior.red.out a τ = some b) :
    SameBelow p.base (strsOf F a.2) (strsOf F b.2) := by
  rw [out_imp p h]
  refine ⟨rfl, fun j hj x => ?_⟩
  show (colAt F (p.ior.imp a.2 τ) j x).getD [] = (colAt F a.2 j x).getD []
  rw [old_kept p a.2 τ j x hj]

/-! ## 2 What is asked of the table, and of its letters -/

/-- **What is asked of the table at (links, ps, k).** p: the place of the block. -/
structure RowSeal (N : Numbers) (M : More) (links : List ModelPart) (ps : List Place) (k : ℕ)
    (p : Place) : Prop where
  place : ps[k]? = some p
  /-- the row is empty -/
  ins : (First.rowOf links p).ins = []
  outs : (First.rowOf links p).outs = []
  ctx : (First.rowOf links p).ctx = []
  /-- and its extractor lays nothing: so the table's own extractor is the identity there (extQ_id,
  Johnson/Desc/Sound/BordersFill.lean) -/
  lays : (First.rowOf links p).lays = false
  /-- it is the chain's last block -/
  last : ps[k + 1]? = none
  /-- in front of it the chain is to stand at its end, and no count of rows may wait -/
  stand : First.standAt links p = .mem
  noWait : First.mayWait links p = false
  /-- no public item comes at the block: what is open behind was open in front -/
  pubs : ∀ q ∈ First.pubStep ((First.pubSets M links ps)[k]?.getD []) (First.pubRowM M links p),
    q ∈ (First.pubSets M links ps)[k]?.getD []
  /-- by the plan the block sends nothing -/
  trees : N.treesAt ps[k + 1]? = N.treesAt ps[k]?
  msgs : N.msgsAt ps[k + 1]? = N.msgsAt ps[k]?

/-- **What is asked of the table's letters at the seal**: they read the strings below B. Op: the
items that ride past the block. -/
structure FillSeal {Pp W : Type} (N : Numbers) (Mg : Meaning Pp W) (B : ℕ) (O : List Item)
    (Op : Item → Prop) : Prop where
  decodes : ∀ x y y', SameBelow B y y' → Mg.decodes x y → Mg.decodes x y'
  shown : ∀ t ∈ First.sampledIn N O, ∀ y y', SameBelow B y y' → Mg.shown t.1 t.2 y →
    Mg.shown t.1 t.2 y'
  noColl : ∀ t ∈ First.sampledIn N O, ∀ x y y', SameBelow B y y' → Mg.noColl t.1 t.2 x y →
    Mg.noColl t.1 t.2 x y'
  /-- an item that rides goes back over the strings -/
  back : ∀ i, Op i → ∀ x y y' w, SameBelow B y y' → i.holds N Mg x y' w → i.holds N Mg x y w

/-- Where nothing but "no mark", the stored table's pin, the index masks' pin, W's pin and the one
claim is open, the sampled tenants are the index masks' and W's. -/
theorem sampled_of_open (N : Numbers) (O : List Item)
    (hO : ∀ i ∈ O, i = .unmarked ∨ i = .pinW ∨ i = .pinI ∨ i = .pinV ∨ i = .pileOne) :
    ∀ t ∈ First.sampledIn N O, t = N.index ∨ t = N.w := by
  intro t ht
  obtain ⟨i, hi, hti⟩ := List.mem_flatMap.1 ht
  rcases hO i hi with rfl | rfl | rfl | rfl | rfl
  · exact absurd (show t ∈ ([] : List (ℕ × ℕ)) from hti) List.not_mem_nil
  · exact absurd (show t ∈ ([] : List (ℕ × ℕ)) from hti) List.not_mem_nil
  · exact Or.inl (List.mem_singleton.1 hti)
  · exact Or.inr (List.mem_singleton.1 hti)
  · exact absurd (show t ∈ ([] : List (ℕ × ℕ)) from hti) List.not_mem_nil

/-- An empty row leaves the open set. -/
theorem stepOpen_empty (O : List Item) (r : First.BlockRow) (h1 : r.ins = []) (h2 : r.outs = []) :
    First.stepOpen O r = O := by
  unfold First.stepOpen
  rw [h1, h2]
  simp

section
variable {A Pp Cl W : Type} {C : PQ.CK} {Fr : Frame}

/-- **THE PROMISE ONE BORDER ON**: marked or not: by onQ_step_held. (FillSeal.back is not
spent here: Op may be laid as one likes.) -/
theorem seal_step (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place)
    (get : A → Pp × S) (k : ℕ) (q : Piece C Fr A Cl W) (p : Place) (Op : Item → Prop)
    (hT : RowSeal N Mg.more links ps k p) (hF : FillSeal N Mg q.base (openAt links ps k) Op)
    (hsame : ∀ a τ b, q.ior.red.out a τ = some b → get b.1 = get a.1) (a : A × Fr.E.Str)
    (τ : Tr (uLT C q.ds)) (b : A × Fr.E.Str) (ha : onQ N Mg links ps get k a)
    (hb : q.ior.red.out a τ = some b) : onQ N Mg links ps get (k + 1) b := by
  have e := hsame a τ b hb
  have hy := sameBelow_out q hb
  refine onQ_step_held N Mg links ps get k p hT.place ?_ a b ha ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · unfold First.quietRow
    rw [hT.ins, hT.outs]
    rfl
  · rw [e]; exact id
  · rw [e]; exact hF.decodes _ _ _ hy
  · intro hm' _
    obtain ⟨_, hr⟩ := ha
    obtain ⟨hB, _⟩ := hr.resolve_left (fun h => h hm')
    simp only [Bool.and_eq_true] at hB
    have hs := hB.1.1.1.1.1
    rw [hT.place] at hs
    rw [hT.last, e]
    unfold First.shapeAt at hs ⊢
    simp only [Bool.and_eq_true, hT.stand, hT.noWait, Bool.or_false] at hs ⊢
    exact ⟨hs.1.1, hs.1.2⟩
  · rw [e]; exact fun _ _ => id
  · rw [e]; exact fun _ _ => id
  · rw [e]; exact fun _ _ => id
  · intro _ _ hP
    rw [e, stepOpen_empty _ _ hT.ins hT.outs]
    unfold First.pubHeld at hP ⊢
    refine List.all_eq_true.2 fun x hx => List.all_eq_true.1 hP x ?_
    rcases List.mem_append.1 hx with hx | hx
    · exact List.mem_append_left _ (hT.pubs x hx)
    · exact List.mem_append_right _ hx
  · intro _ _ hbk
    rw [e]
    unfold First.bookAt at hbk ⊢
    rw [hT.trees, hT.msgs]
    exact hbk
  · intro _ _ hPP x hx
    rw [e]
    exact hPP x (hT.pubs x hx)
  · rw [e]; exact fun _ _ _ _ => id
  · intro _ _ x hx h
    rw [e]
    exact ⟨hF.shown x hx _ _ hy h.1, hF.noColl x hx _ _ _ hy h.2⟩

/-- The row closes "no mark" alone, and opens it alone. -/
theorem seal_ins (N : Numbers) (M : More) (links : List ModelPart) (ps : List Place) (k : ℕ) (p : Place)
    (hT : RowSeal N M links ps k p) (i : Item) :
    (insQ links ps k i → i = .unmarked) ∧ outsQ links ps k .unmarked := by
  have hrow : rowQ links ps k = First.rowOf links p := by
    unfold rowQ
    rw [hT.place]
    rfl
  refine ⟨fun hi => ?_, List.mem_append_right _ (List.mem_singleton.2 rfl)⟩
  have hi' : i ∈ (rowQ links ps k).ins ++ (rowQ links ps k).ctx ++ [Item.unmarked] := hi
  rw [hrow, hT.ins, hT.ctx] at hi'
  exact List.mem_singleton.1 hi'

/-- **THE BLOCK's OWN LAW AT THE TABLE's WORDS** (Piece.Own, Johnson/Desc/Sound/Spine.lean), at any
errors: the form in which SeatLaws (Johnson/Desc/Sound/TiedSeat.lean) takes a kind's first debt. -/
theorem seal_own (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place)
    (get : A → Pp × S) (k : ℕ) (q : Piece C Fr A Cl W) (p : Place) (Op : Item → Prop)
    (hT : RowSeal N Mg.more links ps k p) (hF : FillSeal N Mg q.base (openAt links ps k) Op)
    (hsame : ∀ a τ b, q.ior.red.out a τ = some b → get b.1 = get a.1) :
    q.Own (onQ N Mg links ps get k) (onQ N Mg links ps get (k + 1)) (meansQ N Mg get)
      (insQ links ps k) (outsQ links ps k) :=
  goodIn_of_sure q _ _ _ _ fun a τ b ha hb =>
    ⟨seal_step N Mg links ps get k q p Op hT hF hsame a τ b ha hb, fun w hw i hi => by
      obtain rfl := (seal_ins N Mg.more links ps k p hT i).1 hi
      have h := hw .unmarked (seal_ins N Mg.more links ps k p hT .unmarked).2
      unfold meansQ at h ⊢
      rw [hsame a τ b hb] at h
      exact h⟩

/-- **WHAT RIDES**: an item that is open in front and that the row does not close goes back from the
statement behind to the one in front, at one witness. -/
theorem seal_rides (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place)
    (get : A → Pp × S) (k : ℕ) (q : Piece C Fr A Cl W)
    (hF : FillSeal N Mg q.base (openAt links ps k)
      fun i => openAfter (insQ links ps) (outsQ links ps) (· ∈ First.start links) k i ∧
        ¬ insQ links ps k i)
    (hsame : ∀ a τ b, q.ior.red.out a τ = some b → get b.1 = get a.1) (a : A × Fr.E.Str)
    (τ : Tr (uLT C q.ds)) (b : A × Fr.E.Str) (w : W) (i : Item)
    (hb : q.ior.red.out a τ = some b) (hall : relQ N Mg links ps get (k + 1) b w)
    (hi : openAfter (insQ links ps) (outsQ links ps) (· ∈ First.start links) k i)
    (hin : ¬ insQ links ps k i) : meansQ N Mg get i a w := by
  have hw : meansQ (Fr := Fr) N Mg get i b w := hall i (Or.inl ⟨hi, hin⟩)
  unfold meansQ at hw ⊢
  rw [hsame a τ b hb] at hw
  exact hF.back i ⟨hi, hin⟩ _ _ _ w (sameBelow_out q hb) hw

/-- **THE FIVE TIES AT THE SEAL's ROW**, of any piece whose extractor is the identity and whose yes
leaves what the table reads of the chain's record. -/
theorem seal_tied (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place)
    (get : A → Pp × S) (k : ℕ) (q : Piece C Fr A Cl W) (p : Place)
    (hT : RowSeal N Mg.more links ps k p)
    (hF : FillSeal N Mg q.base (openAt links ps k)
      fun i => openAfter (insQ links ps) (outsQ links ps) (· ∈ First.start links) k i ∧
        ¬ insQ links ps k i)
    (hext : ∀ a τ w, q.ext a τ w = w)
    (hsame : ∀ a τ b, q.ior.red.out a τ = some b → get b.1 = get a.1) :
    TiedAt N Mg links ps get k q := by
  refine ⟨fun a => onQ N Mg links ps get k a ∧ (get a.1).2.failed = none, fun _ => True,
    fun _ _ => True, fun _ _ => True,
    goodIn_of_sure q _ _ _ _ fun _ _ _ _ _ => ⟨trivial, fun _ _ => trivial⟩,
    fun a ha hm => ⟨ha, not_not.1 hm⟩,
    fun a τ b ha _ hb _ => seal_step N Mg links ps get k q p _ hT hF hsame a τ b ha hb,
    fun _ _ _ _ _ _ _ _ _ => trivial, ?_, ?_, ?_, ?_⟩
  · -- t4
    intro a τ b w _ hm _ _ _ _ i hi
    obtain rfl := (seal_ins N Mg.more links ps k p hT i).1 hi
    exact not_not.1 hm
  · -- t5
    intro a τ b w i _ _ hb _ hall hi hin
    rw [hext]
    exact seal_rides N Mg links ps get k q hF hsame a τ b w i hb hall hi hin
  · -- a mark stays
    intro a τ b hb hm
    rw [hsame a τ b hb]
    exact hm
  · -- "decodes" rides
    intro a τ b hb hd
    rw [hsame a τ b hb]
    exact hF.decodes _ _ _ (sameBelow_out q hb) hd

end

/-! ## 3 At the block, as a chain holds it -/

section
variable {A Pp Cl W : Type} {C : PQ.CK}

/-- The bare block's piece: the extractor is the identity. -/
def pieceSeal (F : Frame) (piece : ℕ) (front : List (Block S Cl)) (base : ℕ) (ds : List RDT)
    (back : List Fmt.RoundView) (err : Err (uLT C ds)) : Piece C F S Cl W :=
  ⟨First.firstEnd piece front, base, ds, back, fun _ _ w => w, err⟩

/-- A yes of the bare block's piece returns the record. -/
theorem seal_piece (F : Frame) (piece : ℕ) (front : List (Block S Cl)) (base : ℕ) (ds : List RDT)
    (back : List Fmt.RoundView) (err : Err (uLT C ds)) (a : S × F.E.Str) (τ : Tr (uLT C ds))
    (b : S × F.E.Str)
    (hb : (pieceSeal (W := W) F piece front base ds back err).ior.red.out a τ = some b) :
    b.1 = a.1 := by
  obtain ⟨rs, gs, hdec⟩ := piece_ok _ hb
  exact Keeps.chainEnd_same _ _ _ _ _ hdec

/-- **THE FIVE TIES AT THE PIECE THAT HOLDS c**, where the chain's record is the carried record
itself and the public part is one value z. -/
theorem firstEnd_tied_seat (F : Frame) (piece : ℕ) (front : List (Block S Cl)) (base : ℕ)
    (ds : List RDT) (back : List Fmt.RoundView) (err : Err (uLT C ds)) (c : Block S Cl)
    (hc : c.UnderR (First.firstEnd piece front)) (z : Pp) (N : Numbers) (Mg : Meaning Pp W)
    (links : List ModelPart) (ps : List Place) (k : ℕ) (p : Place)
    (hT : RowSeal N Mg.more links ps k p)
    (hF : FillSeal N Mg base (openAt links ps k)
      fun i => openAfter (insQ links ps) (outsQ links ps) (· ∈ First.start links) k i ∧
        ¬ insQ links ps k i) :
    TiedAt N Mg links ps (fun s : S => (z, s)) k
      ((pieceSeal (W := W) F piece front base ds back err).seat c) := by
  refine seal_tied N Mg links ps _ k _ p hT hF (fun _ _ _ => rfl) ?_
  intro a τ b hb
  have e := seal_piece F piece front base ds back err a τ b
    (out_seat (pieceSeal (W := W) F piece front base ds back err) c hc a b τ hb)
  show (z, b.1) = (z, a.1)
  rw [e]

/-- **THE SAME, LIFTED**: the carried record is a part of the chain's record (gt, st: what was laid
is got; what is laid last stays); pub: the table's public part, which laying the part leaves. -/
theorem firstEnd_tied_lift (F : Frame) (piece : ℕ) (front : List (Block S Cl)) (base : ℕ)
    (ds : List RDT) (back : List Fmt.RoundView) (err : Err (uLT C ds)) (c : Block S Cl)
    (hc : c.UnderR (First.firstEnd piece front)) (gt : A → S) (st : A → S → A)
    (h1 : ∀ t s, gt (st t s) = s) (h2 : ∀ t s s', st (st t s) s' = st t s') (pub : A → Pp)
    (hpub : ∀ t s, pub (st t s) = pub t) (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart)
    (ps : List Place) (k : ℕ) (p : Place) (hT : RowSeal N Mg.more links ps k p)
    (hF : FillSeal N Mg base (openAt links ps k)
      fun i => openAfter (insQ links ps) (outsQ links ps) (· ∈ First.start links) k i ∧
        ¬ insQ links ps k i) :
    TiedAt N Mg links ps (fun a : A => (pub a, gt a)) k
      (((pieceSeal (W := W) F piece front base ds back err).seat c).lift gt st) := by
  have hout := liftOut A S Cl W C F gt st
    ((pieceSeal (W := W) F piece front base ds back err).seat c) h1 h2
  refine seal_tied N Mg links ps _ k _ p hT hF (fun _ _ _ => rfl) ?_
  intro a τ b hb
  rw [hout a τ] at hb
  obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb
  have e := seal_piece F piece front base ds back err _ τ b₀
    (out_seat (pieceSeal (W := W) F piece front base ds back err) c hc _ b₀ τ hb₀)
  show (pub (st a.1 b₀.1), gt (st a.1 b₀.1)) = (pub a.1, gt a.1)
  rw [hpub, h1, e]
  rfl

end

end VerifiableInference.Desc.K13.Law
