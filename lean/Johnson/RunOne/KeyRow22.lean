-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyRow22.lean: THE KEY FILE, THE SHARED CHAIN, ROWS 2.2 («send o_u»; border 2 to 3) AND 2.5 («send o_omega»; border 5 to 6): THE PROMISE's FORWARD HALVES, over the key file's tables. Definitions of Prop, statements and proofs.

CUT IN TWO: FIRST ON THE VERIFIER's STATE ALONE, THEN WHOLE.
  Plan22 | Plan25      ON THE PLAN ALONE, each clause by name.
  shape₂_23 | shape₂_56   the book-keeping goes forward: all eighteen clauses; the last («the book is in order») by bookStep_of_seated over SendLaid's «book» and «roots»; at 6 the split's ledger: not shut, with just the free mask entries left.
  tests₂_23 | tests₂_56   Tests₂ (Johnson/RunOne/KeyOn2Parts.lean: sixteen facts on the state; NO STRINGS) GOES FORWARD. EARNED AT 2.2: lay · seatU · placed at 3 · maskU. AT 2.5: seatOmega · placed at 4 and 5.
  tests₂_of_free | free₂_of_tests   Free₂ is Tests₂ with the letters' two facts (arr · reads) and the strings' two (the stored table's OOD sample is there without a collision [the tables' field «record»] · every leaf is shown at every open pin).
  sure22 | sure25      THE PROMISE's HALVES WHOLE: THE PREMISE «yes» OF keeps₂_send2 | keeps₂_send5 (Johnson/RunOne/KeyRows2225.lean) at two states tied by Laid22 | Laid25, with New := «every leaf is shown at the new pins».

OBJECT. Two states d, d' of which Laid22 | Laid25 hold (Johnson/Desc/Key/Laid/Laid2Def.lean), and the tables' own shape₂ S a k · Free₂ … k at k = 2, 3 | 5, 6. What ties them to a text: laid22_of_yes | laid25_of_yes (Johnson/Desc/Key/Laid/Laid2.lean), whose object is K14's own sendAt.
USER. keeps₂_send2 | keeps₂_send5's premise «yes»; the tables' files' fold along the shared chain's history (Tests₂ k ⟹ Tests₂ (k + 1)).
LETTERS. F, G₂, at_, S, K₁, R, a, coll, last₁, off₂, Q: free.

THE CAUTION: UNTIL A MEMBER IS SHOWN, EVERY LAW THAT HAS PIN AS AN ITEM OR NoColl IN ITS PROMISE MAY BE TRUE AND EMPTY AT THE REAL PROTOCOL, AND COUNTS AS CLOSING NOTHING. sure22 | sure25 speak under such a promise. tests₂_23 | tests₂_56 read no pin and no string.
IS IT EMPTY HERE? (1) Tests₂ at every border 0 … 12 was EVALUATED true on the honest walk at two stored key files (synthetic weights; an evaluation, no theorem; the run is not in this library and cannot be repeated from it; at definitions in which shape₂ lacked its last clause). (2) Laid22 | Laid25: the two blocks say yes on that walk, and a yes gives them. (3) Plan22 | Plan25 AT K14's OWN PLACES (parK1 P 2 … | parK1 P 5 …) AT THE REAL SHAPES: EVALUATED BY NOBODY: one tree | a tree each · firstTree = 0 · the mask has no answer · the split has mask rows: until they are, both pairs may be idle there. (4) Of on₂ k as a whole no member is shown by anybody.

WHAT IS LEFT AS A PREMISE OF sure22 | sure25, EACH WITH WHOSE IT IS. Plan22 | Plan25: PUBLIC: (3) · at_ 3 | 4 | 5: the tables' AtOk's clauses (a member is proved: atOk_member) · CellOnly coll: whoever fills coll · hrec: the reading finds the stored table's OOD sample off the instance alone: at the tables' T.h₂ by rfl · StrsStay and «shown at the new pins»: the caller's (the row of a sending hands both).
NO BARE ∀ OVER STATES.
Limits. The way back and the laws with their errors are in other files. A plan without a shared split or without masks ahead is not served. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.RunOne.KeyOn2Parts
import Johnson.RunOne.KeyWrap23
import Johnson.RunOne.KeyBookStep
import Johnson.Desc.Key.Laid.Laid2Def

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key.LaidW (SendLaid SentAt Laid22 Laid25 fresh_left inFrontOf)
open VerifiableInference.Desc.Book (Seated LayFits cnt)
open VerifiableInference.Desc.Sound (bookStep_iff)
open Johnson.RunOne.KeyRows1 (bookStep_of_seated)
open LKFU.Shape23 (ok shape₂ msgIs grpIs)

/-! ## Tools -/

theorem msgIs_sampled (st : Statement) (o a : Nat) (x : OnBytes.Oracle)
    (h : st.oracles[o]? = some x) (h1 : x.sampled = true) (h2 : x.sampleRows.size = a)
    (h3 : x.spentAsMask = false) : msgIs st o (some a) false = true := by
  unfold msgIs
  rw [h]
  simp [h1, h2, h3]

theorem msgIs_plain (st : Statement) (o : Nat) (x : OnBytes.Oracle)
    (h : st.oracles[o]? = some x) (h1 : x.sampled = false) (h2 : x.sampleRows = #[])
    (h3 : x.spentAsMask = false) : msgIs st o none false = true := by
  unfold msgIs
  rw [h]
  simp [h1, h2, h3]

/-- msgIs reads one message. -/
theorem msgIs_congr (st st' : Statement) (o : Nat) (s : Option Nat) (b : Bool)
    (h : st'.oracles[o]? = st.oracles[o]?) : msgIs st' o s b = msgIs st o s b := by
  unfold msgIs
  rw [h]

/-- grpIs reads the groups alone. -/
theorem grpIs_congr (st st' : Statement) (h : st'.groups = st.groups) (g : Nat) (l : List Nat)
    (p q : Nat) (b : Bool) : grpIs st' g l p q b = grpIs st g l p q b := by
  unfold grpIs
  rw [h]

/-- The numbers that a sending of two messages hands back. -/
theorem ids_two (ids : Array Nat) (n0 i0 i1 : Nat)
    (h : ids = (Array.range 2).map (· + n0)) (h0 : ids[0]? = some i0) (h1 : ids[1]? = some i1) :
    i0 = n0 ∧ i1 = n0 + 1 := by
  subst h
  simp at h0 h1
  omega

/-- What goes out with o_u begins with o_u's own notice. -/
theorem withU_first (S : LinShape) (sent : Array OracleNotice)
    (h : _root_.Desc.K14.withU S = some sent) : ∃ n, sent[0]? = some n ∧ n.shape = S.fold.u := by
  unfold _root_.Desc.K14.withU at h
  obtain ⟨r, _, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨⟨S.fold.u, S.fold.leafClass⟩, by simp, rfl⟩

/-- What goes out with o_omega, where a split is needed: o_omega's notice and the split's. -/
theorem withOmega_two (S : LinShape) (h : S.sharedSplitNeeded = true) :
    _root_.Desc.K14.withOmega S =
      #[⟨S.omega, S.omegaLeafClass⟩, ⟨S.sharedSplit, S.sharedSplitLeafClass⟩] := by
  unfold _root_.Desc.K14.withOmega linMessageOmega
  simp [h]

theorem own₂_2 : (pinned (open₂ 2)).filter (3 ≤ ·) = [] := by decide
theorem own₂_3 : (pinned (open₂ 3)).filter (3 ≤ ·) = [3] := by decide
theorem own₂_5 : (pinned (open₂ 5)).filter (3 ≤ ·) = [3] := by decide
theorem own₂_6 : (pinned (open₂ 6)).filter (3 ≤ ·) = [3, 4, 5] := by decide

/-- The book's new clause behind a sending. -/
theorem book_sent (Q : K1.Par) (d d' : St₂) (ids : Array Nat) (A : SentAt Q d d' ids)
    (h0 : Q.gp.firstTree = 0)
    (h : VerifiableInference.Desc.Sound.bookStepB 0 d.book d.roots = true) :
    VerifiableInference.Desc.Sound.bookStepB 0 d'.book d'.roots = true := by
  obtain ⟨lay, hlay, Sd⟩ := A.laid.book
  have hr := A.laid.roots lay hlay
  rw [h0] at Sd
  exact (bookStep_iff 0 d'.book d'.roots).2
    (bookStep_of_seated 0 d.book d'.book _ _ lay _ d.roots d'.roots
      ((bookStep_iff 0 d.book d.roots).1 h) Sd hr)

/-! ## Free₂ is Tests₂ with the letters' two facts and the strings' two -/

section
variable {XI Cells M Smp Rec : Type} (F : FileDescription XI)
  (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (at_ : Where)
  (S : LinShape) (K₁ : KPlan) (R : KRead Cells M) (a : Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (off₂ : Nat → Nat)

theorem tests₂_of_free (k : Nat) (z : P₂ × St₂) (y : Strs)
    (hs : ok (shape₂ S a k z.2) = true) (hf : Free₂ F G₂ at_ S K₁ R coll last₁ off₂ k z y) :
    Tests₂ at_ S K₁ a last₁ off₂ k z :=
  { shape := hs, last := hf.last, eval := hf.eval, placed₁ := hf.placed₁, order₁ := hf.order₁
    key := hf.key, codes := hf.codes, lay := hf.lay, placed := hf.placed, order := hf.order
    linOk := hf.linOk, seatU := hf.seatU, seatOmega := hf.seatOmega, fits := hf.fits
    mask₁ := hf.mask₁, maskU := hf.maskU }

theorem free₂_of_tests (k : Nat) (z : P₂ × St₂) (y : Strs) (T : Tests₂ at_ S K₁ a last₁ off₂ k z)
    (harr : ArrOk G₂ at_ [0, 2, 3, 4, 5]) (hreads : ReadsPinned G₂ at_ R [0, 2, 3, 4, 5])
    (hrec : FreeAt G₂ coll z y) (hshown : ∀ j ∈ pinned (open₂ k), ShownAt F at_ j y) :
    Free₂ F G₂ at_ S K₁ R coll last₁ off₂ k z y :=
  { record := hrec, last := T.last, eval := T.eval, placed₁ := T.placed₁
    in₁ := handedIn_of_order _ _ T.order₁, order₁ := T.order₁, key := T.key, codes := T.codes
    lay := T.lay, arr := harr, reads := hreads, placed := T.placed
    samples := fun _ _ o _ => sampleIn_of_order T.order o
    rowsIn := fun _ => ⟨openIn_of_order T.order _, openIn_of_order T.order _⟩
    order := T.order, linOk := T.linOk, seatU := T.seatU, seatOmega := T.seatOmega
    shown := hshown, fits := T.fits, mask₁ := T.mask₁, maskU := T.maskU }

end

/-! ## Row 2.2: send o_u -/

/-- On the plan alone. -/
structure Plan22 (S : LinShape) (a : Nat) (Q : K1.Par) : Prop where
  isU : _root_.Desc.K14.withU S = some Q.sent
  two : Q.sent.size = 2
  answers : S.fold.u.answers = a
  pos : a ≠ 0
  mask : ∃ n, Q.sent[1]? = some n ∧ n.shape.answers = 0
  tree : ∀ lay, layTrees Q.codes Q.sent = some lay → lay.shapes.size = 1
  first : Q.gp.firstTree = 0

/-- What border 2's book-keeping says of the counts. -/
theorem front₂_2 (S : LinShape) (a : Nat) (d : St₂) (h : ok (shape₂ S a 2 d) = true) :
    d.st.oracles.size = 0 ∧ d.book.trees.size = 0 ∧ d.roots = 0 ∧ d.book.place.size = 0 := by
  simp only [ok, shape₂, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨_, c2, _, c4, c5, _⟩ := h
  have e2 : d.st.oracles.size = 0 := by simpa using c2
  have e4 : d.book.trees.size = 0 ∧ d.roots = 0 := by simpa using c4
  have e5 : d.st.oracles.size = d.book.place.size := by simpa using c5
  exact ⟨e2, e4.1, e4.2, by omega⟩

/-- **shape₂ at 2, and what the block lays, give shape₂ at 3.** -/
theorem shape₂_23 (S : LinShape) (a : Nat) (Q : K1.Par) (d d' : St₂) (PW : Plan22 S a Q)
    (L : Laid22 S Q d d') (h : ok (shape₂ S a 2 d) = true) : ok (shape₂ S a 3 d') = true := by
  obtain ⟨n0, t0, r0, p0⟩ := front₂_2 S a d h
  simp only [ok, shape₂, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h ⊢
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18⟩ := h
  obtain ⟨ids, i0, i1, A, h0, h1, el⟩ := L
  have W := A.laid
  have wsize : d'.st.oracles.size = d.st.oracles.size + Q.sent.size := W.size
  have wgroups : d'.st.groups = d.st.groups := W.groups
  have wplan : d.st.codes = Q.codes := W.plan
  obtain ⟨lay, hlay, Sd⟩ := W.book
  have hlay' : layTrees d.st.codes Q.sent = some lay := hlay
  have hr : d'.roots = d.roots + lay.shapes.size := W.roots lay hlay
  have sdsize : d'.book.trees.size = d.book.trees.size + lay.shapes.size := Sd.size
  have sdcount : d'.book.place.size = d.book.place.size + Q.sent.size := Sd.count
  have t1 : lay.shapes.size = 1 := PW.tree lay (by rw [← wplan]; exact hlay')
  obtain ⟨e0, e1⟩ := ids_two ids d.st.oracles.size i0 i1 (by rw [← PW.two]; exact W.idsAre) h0 h1
  obtain ⟨nu, hnu, su⟩ := withU_first S Q.sent PW.isU
  obtain ⟨x0, hx0, s0, _, sp0, _, sm0⟩ := W.new 0 nu hnu
  obtain ⟨nm, hnm, am⟩ := PW.mask
  obtain ⟨x1, hx1, _, _, sp1, sm1, _⟩ := W.new 1 nm hnm
  have hx0' : d'.st.oracles[0]? = some x0 := by
    have : d'.st.oracles[d.st.oracles.size + 0]? = some x0 := hx0
    rwa [n0] at this
  have hx1' : d'.st.oracles[1]? = some x1 := by
    have : d'.st.oracles[d.st.oracles.size + 1]? = some x1 := hx1
    rwa [n0] at this
  have au : nu.shape.answers ≠ 0 := by rw [su, PW.answers]; exact PW.pos
  have m0 : msgIs d'.st 0 (some a) false = true :=
    msgIs_sampled _ _ _ x0 hx0' (sm0 au).1 (by rw [(sm0 au).2, su, PW.answers]) sp0
  have m1 : msgIs d'.st 1 none false = true :=
    msgIs_plain _ _ x1 hx1' (sm1 am).1 (sm1 am).2 sp1
  have gI := grpIs_congr d.st d'.st wgroups
  refine ⟨c1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [wsize, n0, PW.two]
  · simpa [wgroups] using c3
  · simp [sdsize, hr, t0, r0, t1]
  · simp [wsize, sdcount, n0, p0]
  · simpa [el] using c6
  · simpa [el] using c7
  · simp [el, e0, e1, n0]
  · simp [m0, m1]
  · simpa [el] using c10
  · simp
  · simpa [el] using c12
  · simpa [gI] using c13
  · simpa [gI] using c14
  · simp
  · simp
  · simp
  · exact book_sent Q d d' ids A PW.first c18

section
variable (at_ : Where) (S : LinShape) (K₁ : KPlan) (a : Nat) (last₁ : FirstState → Bool)
  (off₂ : Nat → Nat)

/-- **Tests₂ at 2, and what the block lays, give Tests₂ at 3.** On the verifier's state alone. -/
theorem tests₂_23 (Q : K1.Par) (p : P₂) (d d' : St₂) (PW : Plan22 S a Q) (L : Laid22 S Q d d')
    (at3 : at_ 3 = (off₂ 0, 0)) (T : Tests₂ at_ S K₁ a last₁ off₂ 2 (p, d)) : Tests₂ at_ S K₁ a last₁ off₂ 3 (p, d') := by
  have hs : ok (shape₂ S a 2 d) = true := T.shape
  have hs' := shape₂_23 S a Q d d' PW L hs
  obtain ⟨n0, t0, _, _⟩ := front₂_2 S a d hs
  obtain ⟨ids, i0, i1, A, h0, h1, el⟩ := L
  have W := A.laid
  have wcodes : d'.st.codes = d.st.codes := W.codes
  have wplan : d.st.codes = Q.codes := W.plan
  obtain ⟨lay, hlay, Sd⟩ := W.book
  have hlay' : layTrees d.st.codes Q.sent = some lay := hlay
  have t1 : lay.shapes.size = 1 := PW.tree lay (by rw [← wplan]; exact hlay')
  have hord : Means.InOrder d'.st := A.order T.order
  obtain ⟨nu, hnu, su⟩ := withU_first S Q.sent PW.isU
  obtain ⟨x0, hx0, s0, _⟩ := W.new 0 nu hnu
  have hx0' : d'.st.oracles[0]? = some x0 := by
    have : d'.st.oracles[d.st.oracles.size + 0]? = some x0 := hx0
    rwa [n0] at this
  -- the two new places
  have q0 : d'.book.place[d.st.oracles.size + 0]? =
      some (d.book.trees.size + lay.tree.getD 0 0, lay.part.getD 0 0) :=
    Sd.new 0 (by rw [PW.two]; omega)
  have q1 : d'.book.place[d.st.oracles.size + 1]? =
      some (d.book.trees.size + lay.tree.getD 1 0, lay.part.getD 1 0) :=
    Sd.new 1 (by rw [PW.two]; omega)
  obtain ⟨b1, b2⟩ := Sd.fits 0 (by rw [PW.two]; omega)
  obtain ⟨b3, b4⟩ := Sd.fits 1 (by rw [PW.two]; omega)
  rw [t1] at b1 b3
  have tr0 : lay.tree.getD 0 0 = 0 := by omega
  have tr1 : lay.tree.getD 1 0 = 0 := by omega
  have pa0 : lay.part.getD 0 0 = 0 := b2
  have pa1 : lay.part.getD 1 0 = 1 := by
    rw [b4, tr1]
    show cnt lay.tree 0 0 + (if lay.tree.getD 0 0 = 0 then 1 else 0) = 1
    rw [tr0]
    rfl
  rw [tr0, pa0, n0, t0] at q0
  rw [tr1, pa1, n0, t0] at q1
  exact
  { shape := hs'
    last := T.last
    eval := T.eval
    placed₁ := T.placed₁
    order₁ := T.order₁
    key := by
      show d'.loc.key = _
      rw [el]
      exact T.key
    codes := by
      show d'.st.codes = _
      rw [wcodes]
      exact T.codes
    lay := fun _ => by
      show d'.loc.oU.lay = vectorLay d'.st.codes S.fold.u S.fold.rowsHigh
      rw [el]
    placed := by
      show Placed (plan₂ S).orc (fun o => d'.book.place[o]?) off₂ at_
        ((pinned (open₂ 3)).filter (3 ≤ ·))
      rw [own₂_3]
      intro k hk
      obtain rfl : k = 3 := by simpa using hk
      exact ⟨0, (0, 0), rfl, q0, at3⟩
    order := hord
    linOk := fun _ => by
      show OnBytes.linOk d'.st.codes S = true
      rw [wcodes]
      exact T.linOk (by decide)
    seatU := fun _ => by
      show (d'.st.oracles[0]?).any (·.shape == S.fold.u) = true
      rw [hx0']
      simp [s0, su]
    seatOmega := fun h6 => absurd h6 (by decide)
    fits := T.fits
    mask₁ := T.mask₁
    maskU := fun _ => ⟨0, 0, q0, q1⟩ }

end

/-! ## Row 2.5: send o_omega -/

/-- On the plan alone. -/
structure Plan25 (S : LinShape) (a : Nat) (Q : K1.Par) : Prop where
  isOmega : _root_.Desc.K14.withOmega S = Q.sent
  split : S.sharedSplitNeeded = true
  answers : S.omega.answers = a
  answersSp : S.sharedSplit.answers = a
  pos : a ≠ 0
  /-- the split's message has mask rows: so it has a ledger -/
  rows : 0 < S.sharedSplit.maskRows
  /-- a tree each -/
  trees : ∀ lay, layTrees Q.codes Q.sent = some lay →
    lay.shapes.size = 2 ∧ lay.tree.getD 0 0 = 0 ∧ lay.tree.getD 1 0 = 1
  first : Q.gp.firstTree = 0

/-- What border 5's book-keeping says of the counts. -/
theorem front₂_5 (S : LinShape) (a : Nat) (d : St₂) (h : ok (shape₂ S a 5 d) = true) :
    d.st.oracles.size = 2 ∧ d.book.trees.size = 1 ∧ d.roots = 1 ∧ d.book.place.size = 2 := by
  simp only [ok, shape₂, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨_, c2, _, c4, c5, _⟩ := h
  have e2 : d.st.oracles.size = 2 := by simpa using c2
  have e4 : d.book.trees.size = 1 ∧ d.roots = 1 := by simpa using c4
  have e5 : d.st.oracles.size = d.book.place.size := by simpa using c5
  exact ⟨e2, e4.1, e4.2, by omega⟩

/-- **shape₂ at 5, and what the block lays, give shape₂ at 6.** -/
theorem shape₂_56 (S : LinShape) (a : Nat) (Q : K1.Par) (d d' : St₂) (PW : Plan25 S a Q)
    (L : Laid25 Q d d') (h : ok (shape₂ S a 5 d) = true) : ok (shape₂ S a 6 d') = true := by
  obtain ⟨n0, t0, r0, p0⟩ := front₂_5 S a d h
  simp only [ok, shape₂, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h ⊢
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18⟩ := h
  obtain ⟨ids, i0, i1, A, h0, h1, el⟩ := L
  have W := A.laid
  have wsize : d'.st.oracles.size = d.st.oracles.size + Q.sent.size := W.size
  have wgroups : d'.st.groups = d.st.groups := W.groups
  have wplan : d.st.codes = Q.codes := W.plan
  have wcodes : d'.st.codes = d.st.codes := W.codes
  have wolder : ∀ o, o < d.st.oracles.size → d'.st.oracles[o]? = d.st.oracles[o]? := W.older
  have hsent : Q.sent =
      #[⟨S.omega, S.omegaLeafClass⟩, ⟨S.sharedSplit, S.sharedSplitLeafClass⟩] :=
    PW.isOmega.symm.trans (withOmega_two S PW.split)
  have two : Q.sent.size = 2 := by rw [hsent]; rfl
  have hn2 : Q.sent[0]? = some ⟨S.omega, S.omegaLeafClass⟩ := by rw [hsent]; rfl
  have hn3 : Q.sent[1]? = some ⟨S.sharedSplit, S.sharedSplitLeafClass⟩ := by rw [hsent]; rfl
  obtain ⟨lay, hlay, Sd⟩ := W.book
  have hlay' : layTrees d.st.codes Q.sent = some lay := hlay
  have hr : d'.roots = d.roots + lay.shapes.size := W.roots lay hlay
  have sdsize : d'.book.trees.size = d.book.trees.size + lay.shapes.size := Sd.size
  have sdcount : d'.book.place.size = d.book.place.size + Q.sent.size := Sd.count
  obtain ⟨t2, _, _⟩ := PW.trees lay (by rw [← wplan]; exact hlay')
  obtain ⟨e0, e1⟩ := ids_two ids d.st.oracles.size i0 i1 (by rw [← two]; exact W.idsAre) h0 h1
  obtain ⟨x2, hx2, _, _, sp2, _, sm2⟩ := W.new 0 _ hn2
  obtain ⟨x3, hx3, s3, _, sp3, _, sm3⟩ := W.new 1 _ hn3
  have a2 : S.omega.answers ≠ 0 := by rw [PW.answers]; exact PW.pos
  have a3 : S.sharedSplit.answers ≠ 0 := by rw [PW.answersSp]; exact PW.pos
  obtain ⟨x3', hx3', led⟩ := A.ledger 1 _ hn3 a3
  have hx2' : d'.st.oracles[2]? = some x2 := by
    have : d'.st.oracles[d.st.oracles.size + 0]? = some x2 := hx2
    rwa [n0] at this
  have hx3'' : d'.st.oracles[3]? = some x3 := by
    have : d'.st.oracles[d.st.oracles.size + 1]? = some x3 := hx3
    rwa [n0] at this
  obtain rfl : x3 = x3' := by
    rw [n0] at hx3'
    exact Option.some.inj (hx3''.symm.trans hx3')
  rw [fresh_left Q.codes S.sharedSplit PW.rows] at led
  have m2 : msgIs d'.st 2 (some a) false = true :=
    msgIs_sampled _ _ _ x2 hx2' (sm2 a2).1 (by rw [(sm2 a2).2]; exact PW.answers) sp2
  have m3 : msgIs d'.st 3 (some a) false = true :=
    msgIs_sampled _ _ _ x3 hx3'' (sm3 a3).1 (by rw [(sm3 a3).2]; exact PW.answersSp) sp3
  have o0 : ∀ s b, msgIs d'.st 0 s b = msgIs d.st 0 s b := fun s b =>
    msgIs_congr _ _ _ _ _ (wolder 0 (by omega))
  have o1 : ∀ s b, msgIs d'.st 1 s b = msgIs d.st 1 s b := fun s b =>
    msgIs_congr _ _ _ _ _ (wolder 1 (by omega))
  have gI := grpIs_congr d.st d'.st wgroups
  have hcod : d'.st.codes = Q.codes := wcodes.trans wplan
  refine ⟨c1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [wsize, n0, two]
  · simpa [wgroups] using c3
  · simp [sdsize, hr, t0, r0, t2]
  · simp [wsize, sdcount, n0, p0, two]
  · simpa [el] using c6
  · simpa [el] using c7
  · simpa [el] using c8
  · simpa [o0, o1] using c9
  · simp [el, e0, e1, n0]
  · simp [m2, m3]
  · simpa [el] using c12
  · simpa [gI] using c13
  · simpa [gI] using c14
  · simp [hx3'', led, s3, hcod]
  · simp
  · simp
  · exact book_sent Q d d' ids A PW.first c18

section
variable (at_ : Where) (S : LinShape) (K₁ : KPlan) (a : Nat) (last₁ : FirstState → Bool)
  (off₂ : Nat → Nat)

/-- **Tests₂ at 5, and what the block lays, give Tests₂ at 6.** On the verifier's state alone. -/
theorem tests₂_56 (Q : K1.Par) (p : P₂) (d d' : St₂) (PW : Plan25 S a Q) (L : Laid25 Q d d')
    (at4 : at_ 4 = (off₂ 1, 0)) (at5 : at_ 5 = (off₂ 2, 0)) (T : Tests₂ at_ S K₁ a last₁ off₂ 5 (p, d)) :
    Tests₂ at_ S K₁ a last₁ off₂ 6 (p, d') := by
  have hs : ok (shape₂ S a 5 d) = true := T.shape
  have hs' := shape₂_56 S a Q d d' PW L hs
  obtain ⟨n0, t0, _, p0⟩ := front₂_5 S a d hs
  obtain ⟨ids, i0, i1, A, h0, h1, el⟩ := L
  have W := A.laid
  have wcodes : d'.st.codes = d.st.codes := W.codes
  have wplan : d.st.codes = Q.codes := W.plan
  have wolder : ∀ o, o < d.st.oracles.size → d'.st.oracles[o]? = d.st.oracles[o]? := W.older
  have hsent : Q.sent =
      #[⟨S.omega, S.omegaLeafClass⟩, ⟨S.sharedSplit, S.sharedSplitLeafClass⟩] :=
    PW.isOmega.symm.trans (withOmega_two S PW.split)
  have two : Q.sent.size = 2 := by rw [hsent]; rfl
  have hn2 : Q.sent[0]? = some ⟨S.omega, S.omegaLeafClass⟩ := by rw [hsent]; rfl
  obtain ⟨lay, hlay, Sd⟩ := W.book
  have hlay' : layTrees d.st.codes Q.sent = some lay := hlay
  obtain ⟨_, b0, b1⟩ := PW.trees lay (by rw [← wplan]; exact hlay')
  have hord : Means.InOrder d'.st := A.order T.order
  obtain ⟨x2, hx2, s2, _⟩ := W.new 0 _ hn2
  have hx2' : d'.st.oracles[2]? = some x2 := by
    have : d'.st.oracles[d.st.oracles.size + 0]? = some x2 := hx2
    rwa [n0] at this
  have q0 : d'.book.place[d.st.oracles.size + 0]? =
      some (d.book.trees.size + lay.tree.getD 0 0, lay.part.getD 0 0) :=
    Sd.new 0 (by rw [two]; omega)
  have q1 : d'.book.place[d.st.oracles.size + 1]? =
      some (d.book.trees.size + lay.tree.getD 1 0, lay.part.getD 1 0) :=
    Sd.new 1 (by rw [two]; omega)
  have f0 := (Sd.fits 0 (by rw [two]; omega)).2
  have f1 := (Sd.fits 1 (by rw [two]; omega)).2
  have pa0 : lay.part.getD 0 0 = 0 := f0
  have pa1 : lay.part.getD 1 0 = 0 := by
    rw [f1, b1]
    show cnt lay.tree 1 0 + (if lay.tree.getD 0 0 = 1 then 1 else 0) = 0
    rw [b0]
    rfl
  rw [b0, pa0, n0, t0] at q0
  rw [b1, pa1, n0, t0] at q1
  have splaces : ∀ j, j < d.book.place.size → d'.book.place[j]? = d.book.place[j]? := Sd.places
  exact
  { shape := hs'
    last := T.last
    eval := T.eval
    placed₁ := T.placed₁
    order₁ := T.order₁
    key := by
      show d'.loc.key = _
      rw [el]
      exact T.key
    codes := by
      show d'.st.codes = _
      rw [wcodes]
      exact T.codes
    lay := fun _ => by
      show d'.loc.oU.lay = vectorLay d'.st.codes S.fold.u S.fold.rowsHigh
      rw [el, wcodes]
      exact T.lay (by decide)
    placed := by
      show Placed (plan₂ S).orc (fun o => d'.book.place[o]?) off₂ at_
        ((pinned (open₂ 6)).filter (3 ≤ ·))
      rw [own₂_6]
      intro k hk
      have hp := T.placed
      rw [own₂_5] at hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl
      · obtain ⟨o, t, e1, e2, e3⟩ := hp 3 (by simp)
        have lt := (Array.getElem?_eq_some_iff.1 e2).1
        exact ⟨o, t, e1, (splaces o lt).trans e2, e3⟩
      · exact ⟨2, (1, 0), rfl, q0, at4⟩
      · exact ⟨3, (2, 0), rfl, q1, at5⟩
    order := hord
    linOk := fun _ => by
      show OnBytes.linOk d'.st.codes S = true
      rw [wcodes]
      exact T.linOk (by decide)
    seatU := fun _ => by
      show (d'.st.oracles[0]?).any (·.shape == S.fold.u) = true
      rw [wolder 0 (by omega)]
      exact T.seatU (by decide)
    seatOmega := fun _ => by
      show (d'.st.oracles[2]?).any (·.shape == S.omega) = true
      rw [hx2']
      simp [s2]
    fits := T.fits
    mask₁ := T.mask₁
    maskU := fun _ => by
      obtain ⟨q, pp, m0, m1⟩ := T.maskU (by decide)
      have l0 := (Array.getElem?_eq_some_iff.1 m0).1
      have l1 := (Array.getElem?_eq_some_iff.1 m1).1
      exact ⟨q, pp, (splaces 0 l0).trans m0, (splaces 1 l1).trans m1⟩ }

end

/-! ## The promise's halves, whole -/

section
variable {XI Cells M Smp Rec : Type} (F : FileDescription XI)
  (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (at_ : Where)
  (S : LinShape) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad a : Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (off₂ : Nat → Nat)

theorem pinned₂_3' : pinned (open₂ 3) = pinned (open₂ 2) ++ [3] := by decide
theorem pinned₂_6' : pinned (open₂ 6) = pinned (open₂ 5) ++ [4, 5] := by decide

/-- **ROW 2.2, THE PROMISE's FORWARD HALF.** -/
theorem sure22 (Q : K1.Par) (p : P₂) (d d' : St₂) (y y' : Strs) (PW : Plan22 S a Q)
    (L : Laid22 S Q d d') (at3 : at_ 3 = (off₂ 0, 0)) (hc : CellOnly coll)
    (hrec : G₂.recOf (p, d') = G₂.recOf (p, d)) (Hy : StrsStay F at_ (open₂ 2) y y')
    (hnew : ShownAt F at_ 3 y')
    (hon : onAt F G₂ at_ (meaning₂ S K₁ R enc rad) (fun d => ok (shape₂ S a 2 d))
      (Free₂ F G₂ at_ S K₁ R coll last₁ off₂ 2) (open₂ 2) (p, d) y) :
    ok (shape₂ S a 3 d') = true ∧ Free₂ F G₂ at_ S K₁ R coll last₁ off₂ 3 (p, d') y' := by
  obtain hn | ⟨hs, _, hf, _⟩ := hon
  · exact absurd trivial hn
  have hf' := free₂_strs F G₂ at_ S K₁ R coll last₁ off₂ 2 hc (p, d) y y' Hy hf
  have T := tests₂_23 at_ S K₁ a last₁ off₂ Q p d d' PW L at3
    (tests₂_of_free F G₂ at_ S K₁ R a coll last₁ off₂ 2 (p, d) y' hs hf')
  obtain ⟨r, r1, r2⟩ := hf'.record
  refine ⟨T.shape, free₂_of_tests F G₂ at_ S K₁ R a coll last₁ off₂ 3 (p, d') y' T hf'.arr hf'.reads
    ⟨r, hrec.trans r1, r2⟩ fun j hj => ?_⟩
  rw [pinned₂_3'] at hj
  rcases List.mem_append.1 hj with hj | hj
  · exact hf'.shown j hj
  · obtain rfl : j = 3 := by simpa using hj
    exact hnew

/-- **ROW 2.5, THE PROMISE's FORWARD HALF.** -/
theorem sure25 (Q : K1.Par) (p : P₂) (d d' : St₂) (y y' : Strs) (PW : Plan25 S a Q)
    (L : Laid25 Q d d') (at4 : at_ 4 = (off₂ 1, 0)) (at5 : at_ 5 = (off₂ 2, 0))
    (hc : CellOnly coll) (hrec : G₂.recOf (p, d') = G₂.recOf (p, d))
    (Hy : StrsStay F at_ (open₂ 5) y y') (hnew : ∀ j ∈ [4, 5], ShownAt F at_ j y')
    (hon : onAt F G₂ at_ (meaning₂ S K₁ R enc rad) (fun d => ok (shape₂ S a 5 d))
      (Free₂ F G₂ at_ S K₁ R coll last₁ off₂ 5) (open₂ 5) (p, d) y) :
    ok (shape₂ S a 6 d') = true ∧ Free₂ F G₂ at_ S K₁ R coll last₁ off₂ 6 (p, d') y' := by
  obtain hn | ⟨hs, _, hf, _⟩ := hon
  · exact absurd trivial hn
  have hf' := free₂_strs F G₂ at_ S K₁ R coll last₁ off₂ 5 hc (p, d) y y' Hy hf
  have T := tests₂_56 at_ S K₁ a last₁ off₂ Q p d d' PW L at4 at5
    (tests₂_of_free F G₂ at_ S K₁ R a coll last₁ off₂ 5 (p, d) y' hs hf')
  obtain ⟨r, r1, r2⟩ := hf'.record
  refine ⟨T.shape, free₂_of_tests F G₂ at_ S K₁ R a coll last₁ off₂ 6 (p, d') y' T hf'.arr hf'.reads
    ⟨r, hrec.trans r1, r2⟩ fun j hj => ?_⟩
  rw [pinned₂_6'] at hj
  rcases List.mem_append.1 hj with hj | hj
  · exact hf'.shown j hj
  · exact hnew j hj

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.shape₂_23
#print axioms Johnson.RunOne.KeyRows23.shape₂_56
#print axioms Johnson.RunOne.KeyRows23.tests₂_23
#print axioms Johnson.RunOne.KeyRows23.tests₂_56
#print axioms Johnson.RunOne.KeyRows23.sure22
#print axioms Johnson.RunOne.KeyRows23.sure25
