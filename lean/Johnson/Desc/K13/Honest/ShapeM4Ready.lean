--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/ShapeM4Ready.lean: kind K13's sub-protocol behind W's commitment (`rowsB`):
when its decision accepts, and what the shape of the state behind is: from guards on the shape of
the verifier's state (Johnson/Desc/K13/Honest/ShapeM4.lean) and one named test on values.
Definitions with code, and statements with their proofs.

The form of the laws: premises on the state's shape, and the named tests on values: then the
decision accepts, and the shape behind is a function with code of the shape in front.
Main names:
  `canJoin4`, `has4`, `bits4`, `padAt4`: four readers of the statement's shape; `canJoin4_eq`,
    `has4_eq`, `bits4_eq`, `padAt4_eq`: at a statement's shape they are `canJoinC`
    (Johnson/Desc/K13/Honest/SentC.lean), the library's `Statement.has` and `Statement.tableBits`,
    and the message's list of pad places.
  `ready4L`, `ready4`: **the guards**, as named clauses on the shape: the chain stands at its end; a
    claim is laid; its masks are entries of mask tables; a number is handed on; then ten clauses of
    `sentAtM4L` (SentC.lean), letter for letter, on the shape. W's number is the first of the
    numbers handed on.
  `vals4`: **the one named test on values**: a row has the coefficient 0 at every place of every
    message's pad; where the claim's masks are all entries of mask tables that row is the row
    (Eval).
  `pads4L`, `pads4`: two clauses on the shape that are enough for it: every place of W's pad in the
    main table bears an entry number from 2^(the point's length) on; no place of the claim's masks
    is a place of its message's pad.
  `claim_of_parts`: a claim whose masks are all entries of mask tables is made of the row that the
    library reads off it (`rowOfClaim`, Johnson/Desc/First/State.lean).
  `sent_of_ready`, `pad_of_vals`, `pad_of_pads`: from these to `SentAtM4` (RowsAccept.lean).
  `rowsB_returns`: **the law with the test on values.** `rowsB_returns_shape`: **the law on the
    shape alone.** `atM4_returns_shape`: for the whole sub-protocol at the place of W's commitment:
    that the sub-protocol in front of `rowsB` accepts is a premise, and the guards are asked at the
    shape behind it: it is no law from the shape in front of the place.
WHAT IS ENOUGH AND WHAT IS NEEDED. All is shown to be enough; that any of it is needed is not shown.
The text's own test on pads ("addRow: ON VALUES: no coefficient on a pad",
Johnson/Desc/First/Base/Ground.lean) asks the coefficient at the pads of the own group's members;
`vals4` asks it at every message's pad. The two clauses of `pads4L` read places alone; under them
the coefficient is 0 whatever the elements (`sentAtM4_pad`, Johnson/Desc/K13/Honest/PadFree.lean).
They ask more than the text's test: that one passes wherever the coefficient is 0, these reject
every mask's place on a pad. No state at which they part is exhibited here.
IN THE PROOF FILE's IOP THE SUB-PROTOCOL DOES NOT STAND BARE: every lot's sub-protocol is laid
behind a guard that rejects where the state behind bears a mark of failure (`guardMark`,
Johnson/Desc/ProofFile/Frames1.lean) and behind a guard on the reply (`sameReply`). `Sh4` has no
field for the mark, and no law here says that the mark behind is the mark in front: so for the
guarded sub-protocol `ready4` with `pads4` is short by one flag.

What is not claimed. The converse of any law. That the guards accept at any state of a run. Nothing
on W's commitment itself. "Accepts" is `Block.decide`'s answer `.ok` and no more. Nothing on
soundness or on hiding.

-/
import Johnson.Desc.K13.Honest.ShapeM4
import Johnson.Desc.K13.Honest.RowsAccept
import Johnson.Desc.K13.Honest.SentC
import Johnson.Desc.K13.Honest.PadFree
import Johnson.Desc.K13.Honest.AtM4Accepts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Slice
open OnBytes.Params (LinShape)
open VerifiableInference.Desc.First (S rowOfClaim)
open VerifiableInference.Desc.K13.Law

/-! ## Four readers of the statement's shape -/

/-- The message o can join a group under the codes c and z. -/
def canJoin4 (h : StSh) (c z o : ℕ) : Bool :=
  (h.msgs[o]?).any fun x =>
    x.sampled && (x.shape.mainRows == 0 || x.shape.code == c) &&
      (x.shape.maskRows == 0 || x.shape.maskCode == z)

/-- The message o has that table. -/
def has4 (h : StSh) (o : ℕ) (part : OnBytes.Part) : Bool :=
  match h.msgs[o]? with
  | some x => decide (0 < x.shape.rows part)
  | none => false

/-- The number of bits that index that table. -/
def bits4 (h : StSh) (o : ℕ) (part : OnBytes.Part) : ℕ :=
  match h.msgs[o]? with
  | some x =>
    ceilLog2 (x.shape.rows part) +
      (if x.shape.rows part == 0 then 0
      else match part with
        | .main => (h.codes.base.getD x.shape.code default).logEll
        | .mask => (h.codes.mask.getD x.shape.maskCode default).logEll)
  | none => 0

/-- The places of the message's pad; none where the message is not there. -/
def padAt4 (h : StSh) (o : ℕ) : List (OnBytes.Part × ℕ) := ((h.msgs[o]?).map (·.pad)).getD []

theorem canJoin4_eq (St : Statement) (c z o : ℕ) :
    canJoin4 (stSh St) c z o = canJoinC St c z o := by
  unfold canJoin4 canJoinC
  rw [msgs_at]
  cases St.oracles[o]? <;> rfl

theorem has4_eq (St : Statement) (o : ℕ) (part : OnBytes.Part) :
    has4 (stSh St) o part = St.has o part := by
  unfold has4 Statement.has
  rw [msgs_at]
  cases St.oracles[o]? <;> rfl

theorem bits4_eq (St : Statement) (o : ℕ) (part : OnBytes.Part) :
    bits4 (stSh St) o part = St.tableBits o part := by
  unfold bits4 Statement.tableBits Statement.rowBits Statement.placeBits
  rw [msgs_at]
  cases St.oracles[o]? <;> rfl

theorem padAt4_eq (St : Statement) (o : ℕ) :
    padAt4 (stSh St) o = ((St.oracles[o]?).map (·.pad)).getD [] := by
  unfold padAt4
  rw [msgs_at]
  cases St.oracles[o]? <;> rfl

/-! ## The test -/

/-- **The clauses**, each under a name. c: the claim's shape. w: the first of the numbers handed on.
-/
def ready4L (Sh : LinShape) (c : ClaimSh) (ids : Array ℕ) (h : StSh) (w : ℕ) :
    List (String × Bool) :=
  [("parts: the claim's masks are entries of mask tables",
     c.slots.all fun t => t.2.1 == OnBytes.Part.mask),
   ("first: a number is handed on", (ids[0]?).isSome),
   ("split: where a split is needed, its message is the second, can join and is no other member",
     !Sh.ownSplitNeeded || (ids[1]?).any fun sp =>
       canJoin4 h Sh.w.code Sh.ownMaskCode sp && (sp != w) && c.slots.all fun t => t.1 != sp),
   ("codes: the own group's codes are lawful", Ground.groupOk h.codes Sh.w.code Sh.ownMaskCode),
   ("masks: the messages of the claim's masks can join, and none is W",
     c.slots.all fun t => canJoin4 h Sh.w.code Sh.ownMaskCode t.1 && (t.1 != w)),
   ("joins: W can join", canJoin4 h Sh.w.code Sh.ownMaskCode w),
   ("point: the point has a coordinate for each column variable", c.point == Sh.kCol),
   ("room: W's vector fits its table", decide (Sh.kCol ≤ (linLayW h.codes Sh).bits)),
   ("small: the table has at most 63 index bits", decide ((linLayW h.codes Sh).bits ≤ 63)),
   ("table: W has a main table", has4 h w .main),
   ("bits: W's main table has the layout's index bits",
     bits4 h w .main == (linLayW h.codes Sh).bits),
   ("within: the claim's mask entries lie within their tables",
     c.slots.all fun t => has4 h t.1 .mask && decide (t.2.2 < 2 ^ bits4 h t.1 .mask))]

/-- **Two clauses on pads**, on places alone. -/
def pads4L (Sh : LinShape) (c : ClaimSh) (h : StSh) (w : ℕ) : List (String × Bool) :=
  [("padW: W's pad in the main table lies behind the vector's entries",
     (padAt4 h w).all fun q => q.1 != OnBytes.Part.main ||
       (decide (q.2 < 2 ^ (linLayW h.codes Sh).bits) &&
         decide (2 ^ c.point ≤ (linLayW h.codes Sh).entryAt q.2))),
   ("padM: no place of the claim's masks is a place of its message's pad",
     c.slots.all fun t => !(padAt4 h t.1).contains (OnBytes.Part.mask, t.2.2))]

/-- **The guards on the state's shape.** -/
def ready4 (Sh : LinShape) (h : Sh4) : Bool :=
  h.atEnd && match h.laid with
    | none => false
    | some l => (ready4L Sh l.claim h.ids h.st ((h.ids[0]?).getD noId)).all (·.2)

/-- The two clauses on pads, on the state's shape. -/
def pads4 (Sh : LinShape) (h : Sh4) : Bool :=
  match h.laid with
  | none => false
  | some l => (pads4L Sh l.claim h.st ((h.ids[0]?).getD noId)).all (·.2)

/-- **The one named test on values**: the row that is made, as (Eval) is, of the row that the
library reads off the claim has the coefficient 0 at every place of every message's pad. Where the
claim's masks are all entries of mask tables that is the row (Eval) that the text makes. It reads
field elements of the state: the claim's point and its masks' coefficients. The text asks it at the
own group's members alone. -/
def vals4 (Sh : LinShape) (s : S) : Bool :=
  match s.here with
  | .mem a =>
    match a.lin with
    | some l =>
      (List.range s.st.oracles.size).all fun o =>
        (((s.st.oracles[o]?).map (·.pad)).getD []).all fun q =>
          VerifiableInference.Desc.Own.allZero
            ((evalOf (rowOfClaim l.claim) ((a.ids[0]?).getD noId)
              (linLayW s.st.codes Sh)).coefficient o q.1 q.2)
    | none => false
  | _ => false

/-! ## The guards give all of `SentAtM4` but its clause on pads -/

/-- A claim whose masks are all entries of mask tables is made of that row. -/
theorem claim_of_parts (c : LinClaim) (h : ∀ u ∈ c.masks.toList, u.part = OnBytes.Part.mask) :
    c = memberClaim (rowOfClaim c) := by
  have e : (c.masks.toList.map fun u => ((⟨u.oracle, u.index⟩ : Slot), u.coeff)).map
      (fun m => (⟨m.1.oracle, .mask, m.1.index, m.2⟩ : Single)) = c.masks.toList := by
    rw [List.map_map]
    refine (List.map_congr_left fun u hu => ?_).trans (List.map_id _)
    show (⟨u.oracle, .mask, u.index, u.coeff⟩ : Single) = u
    rw [← h u hu]
  show c = ⟨c.g, c.psi, ((c.masks.toList.map fun u => ((⟨u.oracle, u.index⟩ : Slot), u.coeff)).map
    fun m => (⟨m.1.oracle, .mask, m.1.index, m.2⟩ : Single)).toArray, c.target⟩
  rw [e]

/-- The clause of `SentAtM4` on pads, at the row that the claim is made of. -/
def PadZero (Sh : LinShape) (s : S) (a : First.MemOwn) (l : LinFirst) : Prop :=
  ∀ (o : ℕ) (x : OnBytes.Oracle), s.st.oracles[o]? = some x → ∀ q ∈ x.pad,
    ρg.val ((evalOf (rowOfClaim l.claim) ((a.ids[0]?).getD noId)
      (linLayW s.st.codes Sh)).coefficient o q.1 q.2) = 0

/-- What the shape is where the chain stands at its end. -/
theorem sh4_mem {s : S} {a : First.MemOwn} (hs : s.here = .mem a) :
    sh4 s = ⟨true, a.ids, a.lin.map laidSh, s.rowsOwed, stSh s.st⟩ := by
  unfold sh4
  rw [hs]

/-- Where the guards accept, the chain stands at its end and a claim is laid. -/
theorem laid_of_ready {Sh : LinShape} {s : S} (h : ready4 Sh (sh4 s) = true) :
    ∃ (a : First.MemOwn) (l : LinFirst), s.here = .mem a ∧ a.lin = some l := by
  cases hs : s.here with
  | mem a =>
    rw [sh4_mem hs] at h
    cases hl : a.lin with
    | none =>
      rw [hl] at h
      simp [ready4] at h
    | some l => exact ⟨a, l, rfl, hl⟩
  | between => simp [sh4, hs, ready4] at h
  | lay a => simp [sh4, hs, ready4] at h
  | att a => simp [sh4, hs, ready4] at h
  | head a => simp [sh4, hs, ready4] at h
  | fin a => simp [sh4, hs, ready4] at h

/-- A place of the claim's shape for each mask of the row. -/
theorem slot_of_mask {c : LinClaim} (hp : ∀ u ∈ c.masks.toList, u.part = OnBytes.Part.mask) :
    ∀ t ∈ (rowOfClaim c).masks,
      (t.1.oracle, OnBytes.Part.mask, t.1.index) ∈ (claimSh4 c).slots := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ht
  exact List.mem_map.2 ⟨u, hu, by rw [hp u hu]⟩

/-- **Where the guards accept at the shape of s and (Eval) has no coefficient on a pad, `SentAtM4`
holds at s.** -/
theorem sent_of_ready {Sh : LinShape} {s : S} {a : First.MemOwn} {l : LinFirst}
    (hs : s.here = .mem a) (hl : a.lin = some l) (h : ready4 Sh (sh4 s) = true)
    (hpad : PadZero Sh s a l) :
    l.claim = memberClaim (rowOfClaim l.claim) ∧
      SentAtM4 Sh (rowOfClaim l.claim) a.ids s.st ((a.ids[0]?).getD noId) := by
  rw [sh4_mem hs, hl] at h
  have h' : ((ready4L Sh (claimSh4 l.claim) a.ids (stSh s.st) ((a.ids[0]?).getD noId)).all
      (·.2)) = true := by simpa [ready4] using h
  simp only [ready4L, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    canJoin4_eq, has4_eq, bits4_eq] at h'
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩ := h'
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 p1
  have hw' : (a.ids[0]?).getD noId = w := by rw [hw]; rfl
  have hparts : ∀ u ∈ l.claim.masks.toList, u.part = OnBytes.Part.mask := fun u hu =>
    beq_iff_eq.1 (List.all_eq_true.1 p0 (u.oracle, u.part, u.index)
      (List.mem_map.2 ⟨u, hu, rfl⟩))
  have hslot := slot_of_mask hparts
  refine ⟨claim_of_parts l.claim hparts, by rw [hw']; exact hw, fun hn => ?_, p3,
    fun t ht => ?_, (canJoinC_iff _ _ _ _).1 p5, beq_iff_eq.1 p6, of_decide_eq_true p7,
    of_decide_eq_true p8, p9, beq_iff_eq.1 p10, fun t ht => ?_, hpad⟩
  · rw [hn] at p2
    simp only [Bool.not_true, Bool.false_or] at p2
    cases hi : a.ids[1]? with
    | none =>
      rw [hi] at p2
      simp at p2
    | some sp =>
      rw [hi] at p2
      simp only [Option.any_some, Bool.and_eq_true, bne_iff_ne] at p2
      exact ⟨sp, rfl, (canJoinC_iff _ _ _ _).1 p2.1.1, p2.1.2, fun t ht =>
        bne_iff_ne.1 (List.all_eq_true.1 p2.2 _ (hslot t ht))⟩
  · have q := List.all_eq_true.1 p4 _ (hslot t ht)
    simp only [Bool.and_eq_true, bne_iff_ne] at q
    exact ⟨(canJoinC_iff _ _ _ _).1 q.1, q.2⟩
  · have q := List.all_eq_true.1 p11 _ (hslot t ht)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at q
    exact q

/-! ## The clause on pads: from the test on values, or from the two clauses on places -/

/-- From the named test on values. -/
theorem pad_of_vals {Sh : LinShape} {s : S} {a : First.MemOwn} {l : LinFirst}
    (hs : s.here = .mem a) (hl : a.lin = some l) (h : vals4 Sh s = true) : PadZero Sh s a l := by
  intro o x hx q hq
  unfold vals4 at h
  rw [hs] at h
  simp only [hl, List.all_eq_true, List.mem_range] at h
  have ho : o < s.st.oracles.size := by
    by_contra c
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt c)] at hx
    cases hx
  exact readE_of_isZeroE _ (h o ho q (by rw [hx]; exact hq))

/-- From the guards and the two clauses on places: whatever the field elements. -/
theorem pad_of_pads {Sh : LinShape} {s : S} {a : First.MemOwn} {l : LinFirst}
    (hs : s.here = .mem a) (hl : a.lin = some l) (h : ready4 Sh (sh4 s) = true)
    (hp : pads4 Sh (sh4 s) = true) : PadZero Sh s a l := by
  rw [sh4_mem hs, hl] at h hp
  have h' : ((ready4L Sh (claimSh4 l.claim) a.ids (stSh s.st) ((a.ids[0]?).getD noId)).all
      (·.2)) = true := by simpa [ready4] using h
  have hp' : ((pads4L Sh (claimSh4 l.claim) (stSh s.st) ((a.ids[0]?).getD noId)).all (·.2)) =
      true := hp
  simp only [ready4L, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h'
  obtain ⟨p0, _, _, _, _, _, p6, p7, _⟩ := h'
  simp only [pads4L, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    padAt4_eq] at hp'
  obtain ⟨p12, p13⟩ := hp'
  have hparts : ∀ u ∈ l.claim.masks.toList, u.part = OnBytes.Part.mask := fun u hu =>
    beq_iff_eq.1 (List.all_eq_true.1 p0 (u.oracle, u.part, u.index)
      (List.mem_map.2 ⟨u, hu, rfl⟩))
  have hslot := slot_of_mask hparts
  have hpoint : (rowOfClaim l.claim).psi.length = Sh.kCol := beq_iff_eq.1 p6
  have hroom : Sh.kCol ≤ (linLayW s.st.codes Sh).bits := of_decide_eq_true p7
  refine sentAtM4_pad (by rw [hpoint]; exact hroom) (fun x hx q hq hmain => ?_)
    fun t ht x hx hc => ?_
  · rw [hx] at p12
    have r := List.all_eq_true.1 p12 q hq
    rw [hmain] at r
    simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at r
    exact r
  · have r := List.all_eq_true.1 p13 _ (hslot t ht)
    rw [hx] at r
    simp only [Option.map_some, Option.getD_some, Bool.not_eq_true'] at r
    have r' : x.pad.contains (OnBytes.Part.mask, t.1.index) = true := List.contains_iff_mem.2 hc
    rw [r] at r'
    cases r'

/-! ## The laws -/

variable {Cl : Type}

/-- **The law for `rowsB`, with the test on values**: the guards accept at the shape of s, the named
test on values passes at s: then the decision accepts, and the shape behind is the update of the
shape in front. -/
theorem rowsB_returns {P : Where} {s : S} (h : ready4 P.lin (sh4 s) = true)
    (hv : vals4 P.lin s = true) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    ∃ s', (rowsB (Cl := Cl) atS P).decide s rs gs = .ok s' ∧ sh4 s' = step4 P.lin (sh4 s) := by
  obtain ⟨a, l, hs, hl⟩ := laid_of_ready h
  obtain ⟨hrow, H⟩ := sent_of_ready hs hl h (pad_of_vals hs hl hv)
  obtain ⟨s', _, hd, _⟩ := rowsB_accepts (Cl := Cl) hs hl hrow H rs gs
  exact ⟨s', hd, shape_step4 hd⟩

/-- **The law for `rowsB`, on the shape alone**: the guards and the two clauses on pads accept at
the shape of s: then the decision accepts, whatever the field elements in s, and the shape behind is
the update of the shape in front. -/
theorem rowsB_returns_shape {P : Where} {s : S} (h : ready4 P.lin (sh4 s) = true)
    (hp : pads4 P.lin (sh4 s) = true) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    ∃ s', (rowsB (Cl := Cl) atS P).decide s rs gs = .ok s' ∧ sh4 s' = step4 P.lin (sh4 s) := by
  obtain ⟨a, l, hs, hl⟩ := laid_of_ready h
  obtain ⟨hrow, H⟩ := sent_of_ready hs hl h (pad_of_pads hs hl h hp)
  obtain ⟨s', _, hd, _⟩ := rowsB_accepts (Cl := Cl) hs hl hrow H rs gs
  exact ⟨s', hd, shape_step4 hd⟩

/-- **The law for the whole sub-protocol at the place of W's commitment**, over any sub-protocol b
in front of `rowsB`: that b's decision accepts, from s to s₁, is a premise; the guards and the two
clauses on pads are asked at the shape of s₁. -/
theorem atM4_returns_shape {P : Where} {b : Block S Cl} {s s₁ : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hr : rs.length = b.rounds.length)
    (hg : gs.length = b.openings) (hb : b.decide s rs gs = .ok s₁)
    (h : ready4 P.lin (sh4 s₁) = true) (hp : pads4 P.lin (sh4 s₁) = true) :
    ∃ s', (atM4 P b).decide s rs gs = .ok s' ∧ sh4 s' = step4 P.lin (sh4 s₁) := by
  obtain ⟨a, l, hs, hl⟩ := laid_of_ready h
  obtain ⟨hrow, H⟩ := sent_of_ready hs hl h (pad_of_pads hs hl h hp)
  obtain ⟨s', _, hd, hd', _⟩ := atM4_accepts hr hg hb hs hl hrow H
  exact ⟨s', hd, shape_step4 hd'⟩

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.canJoin4_eq
#print axioms VerifiableInference.Desc.K13.Honest.has4_eq
#print axioms VerifiableInference.Desc.K13.Honest.bits4_eq
#print axioms VerifiableInference.Desc.K13.Honest.padAt4_eq
#print axioms VerifiableInference.Desc.K13.Honest.claim_of_parts
#print axioms VerifiableInference.Desc.K13.Honest.sh4_mem
#print axioms VerifiableInference.Desc.K13.Honest.laid_of_ready
#print axioms VerifiableInference.Desc.K13.Honest.slot_of_mask
#print axioms VerifiableInference.Desc.K13.Honest.sent_of_ready
#print axioms VerifiableInference.Desc.K13.Honest.pad_of_vals
#print axioms VerifiableInference.Desc.K13.Honest.pad_of_pads
#print axioms VerifiableInference.Desc.K13.Honest.rowsB_returns
#print axioms VerifiableInference.Desc.K13.Honest.rowsB_returns_shape
#print axioms VerifiableInference.Desc.K13.Honest.atM4_returns_shape
