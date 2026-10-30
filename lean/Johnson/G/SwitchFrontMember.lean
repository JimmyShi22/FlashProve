-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/G/SwitchFrontMember.lean: the record `FrontAt` (Johnson/Top/H0/K2Hands/TiePaid.lean) HAS A
MEMBER at each written record of a code switch, AT A FRONT MADE HERE OF THE RECORD: eight of its
sixteen clauses test the record's own numbers there, seven hold by how the front is made; THE
SIXTEENTH, `strIs`, IS MET IDLY.

`FrontAt` holds what the join of the code switch's typed chain to its written text asks of the
statement in front. It is a premise of that join. Members of it at made-up
numbers stand outside this library (Johnson/Top/H0/K2Caller/Toy/).
Here the front is made of a written record's own shapes, codes and kept places
(Johnson/Top/H0/K2Caller/Lit.lean), over the frame and the two statements of
Johnson/G/SwitchAtSwitchLit.lean and the samples of Johnson/G/SwitchSampleMember.lean. Definitions,
statements and proofs.
Main names:
  `tenAt`, `rowsC`, `fxAt r`: the made front: the statement in front `stF r`; the carried rows of
    `oldAt` with a claim that says something (one tensor with the main code's index bits as its
    variables, one written-out element for each mask row, the target one); the target `tgtAt r`; as
    further announcements the rest of the sending's sampled messages.
  `frB r`: a test with code on the front, five clauses. `frB_says`. `frB_full`, `frB_small`: Lean's
    kernel says yes at each of the 25 and the 5. `frB_no_last`: a control on its first clause: the
    front of a record with its last sent message struck out has not the shapes of `stB` of the
    whole record.
  `frame_rowsC`: the routine that makes a frame does not read the claim (by rfl).
  `same_at`, `frameIs_at`: the front's statement with the announcements received has the shapes of
    `stB r`; so `K2.frameAt (fxAt r)` IS the frame that the program's routine returns at `stB r`
    (by `K2.frame_congr`, Johnson/Top/H0/K2Hands/FrameOfFront.lean): the clause frameIs.
  `FrontEnd`, `front_member_at`, `front_member_full`, `front_member_small`: there are W, `Fit` and a
    typed claim with held samples such that at EVERY place, record, oracles and string: `StrIs`
    gives `FrontAt`: the other fifteen clauses are paid. OF THESE, EIGHT TEST THE RECORD's OWN
    NUMBERS (its codes, shapes, kept places; the program's frame at them): frameIs, z32, twoOld,
    keptPos, keptRows, ell, next, and of sample the parts on the frame's records, the slots, one
    answer and the two cases. SEVEN HOLD BY HOW THE FRONT AND THE TYPED CLAIM ARE MADE: codes;
    first (`tgtAt`'s shape is defined as the first sent message's: that the PROGRAM's own target
    has that shape is held by an evaluation off this library, at the full size's public files);
    mainVars (the made tensor has that many variables); d0, d1 (one written-out element each: they
    test only that the mask code's messages have an element); target, vector (the typed claim is
    chosen so); and of sample the part on the stored row (made as the program's row at a made
    seed). The call: `frontAt_of_rest` (Johnson/Top/H/SwitchSampleFront.lean).
  `pAt`, `sAt`, `idleB`, `idleB_full`, `idleB_small`, `long_none`: a made place and a made record in
    front WHOSE BOOK OF TREES IS EMPTY: there `K2.longFront` reads nothing at any position.
  `FrontWhole`, `front_whole_at`, `front_whole_full`, `front_whole_small`: so `FrontAt` holds there,
    whole, at all oracles.
  `front_closed_full`, `front_closed_small`: the same, and `SampleEnd`, with the record's promise
    paid (`okFull`, `okSmall`) and at the letters `Letters.plain`: NO PREMISE IS LEFT.
  `held_nonempty`: at these letters' kq there is a held old message wherever the record keeps one
    (24 of the 25: `smpB_no_answers`): the clause sample is not idle there.
Limits: THE FRONT, THE PLACE AND THE RECORD ARE MADE HERE: THEY ARE NO RUN's. `strIs` IS MET IDLY:
it asks of the string only where the front reads the carried rows off the oracles, and at the made
record, with no tree in its book, it reads nothing: SO NOTHING IS SHOWN ON WHETHER `strIs` CAN HOLD
TOGETHER WITH THE OTHER FIFTEEN WHERE IT SAYS SOMETHING. That wants a book of trees with the old
messages' places, and that the stage's long reading can show what `K2.longFront` reads: not
attempted. The carried rows name no fresh mask (`fresh` is no message's number) and no form on a
kept member. The claim, the seed and the answers are poor ones. What is shown: the fifteen do not
shut each other out at the written shapes. Those of SwitchAtSwitchLit.lean and
SwitchSampleMember.lean. `CallerAt` and `YesAt`, the join's two other records, are not treated.
Nothing on soundness.

-/
import Johnson.G.SwitchSampleMember
import Johnson.Top.H.SwitchSampleFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G
open OnBytes OnBytes.Slice Cb Iop IOR Johnson.Pack Johnson.Top.H
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K2Caller VerifiableInference.Desc.First.K2Hands

/-- A tensor with as many variables as the main code's messages have index bits. -/
def tenAt (r : SwRow) : Tensor :=
  { pairs := List.replicate (r.cs.base.getD (codeIx r) default).logEll (oneE, zeroE) }

/-- The carried rows at the front: those of `oldAt`, with a claim that says something: on the main
row's message one tensor with as many variables as the main code's messages have index bits; one
written-out element for each of the two mask rows; the target one. -/
def rowsC (r : SwRow) : SingleRows :=
  { oldAt r with c := { tensors := [tenAt r] }, d := #[#[oneE], #[oneE]], target := oneE }

/-- **A front, made of the record**: the statement in front `stF r`; a frame of the request that
holds nothing but the carried rows; the target `tgtAt r`; as further announcements the sampled
messages of the sending behind g and the kept members' copies. -/
def fxAt (r : SwRow) : _root_.Tw.K2.Front :=
  { st := stF r, f := { shape := default, groups := #[], rows := rowsC r }, own := []
    others := ((r.l.drop (1 + r.kept.length)).map fun x => (⟨x.1, 0⟩ : OracleNotice)).toArray
    T := tgtAt r, plain := 0 }

/-- **The test on the front.** The front's statement with the announcements received has, number by
number, the shapes of `stB r`; the numbers that the sending returns are g's and the copies'; each
message that takes a kept member has a main row; the mask code's messages have an element. -/
def frB (r : SwRow) : Bool :=
  decide ((K2.skelOf (fxAt r)).oracles.toList.map (·.shape) =
    (stB r).oracles.toList.map (·.shape)) &&
  decide ((K2.idsOf (fxAt r)).getD 0 noId = r.lo.length) &&
  decide ((K2.idsOf (fxAt r)).extract 1 (1 + (tgtAt r).kept.size) = anewAt r) &&
  ((tgtAt r).kept.all fun k => decide (0 < k.shape.mainRows)) &&
  decide (1 ≤ (r.cs.mask.getD r.rider.maskCode default).ell)

set_option maxRecDepth 1000000 in
theorem frB_full : (tableFullLit.all frB) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem frB_small : (tableSmallLit.all frB) = true := by decide +kernel

/-- The routine that makes a frame does not read the claim. -/
theorem frame_rowsC (r : SwRow) (S : Statement) (T : SwitchTarget) (g : ℕ) (anew : Array ℕ) :
    switchFrame S (rowsC r) T g anew = switchFrame S (oldAt r) T g anew := rfl

/-- What the test's yes says. -/
theorem frB_says {r : SwRow} (h : frB r = true) :
    (K2.skelOf (fxAt r)).oracles.toList.map (·.shape) = (stB r).oracles.toList.map (·.shape) ∧
    (K2.idsOf (fxAt r)).getD 0 noId = r.lo.length ∧
    (K2.idsOf (fxAt r)).extract 1 (1 + (tgtAt r).kept.size) = anewAt r ∧
    ((tgtAt r).kept.all fun k => decide (0 < k.shape.mainRows)) = true ∧
    1 ≤ (r.cs.mask.getD r.rider.maskCode default).ell := by
  unfold frB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ := h
  exact ⟨a, b, c, d, e⟩

/-- The front's statement with the announcements received has the shapes of `stB r`. -/
theorem same_at {r : SwRow} (h : frB r = true) : K2.SameShapes (stB r) (K2.skelOf (fxAt r)) where
  codes := rfl
  shape := fun o => by
    have e := congrArg (fun l : List OracleShape => l[o]?) (frB_says h).1
    simpa [List.getElem?_map, Array.getElem?_toList] using e

/-- **frameIs**: the frame at the made front is the frame that the routine returns at `stB r`. -/
theorem frameIs_at {r : SwRow} (h : frB r = true) (W : SwitchFrame)
    (hW : switchFrame (stB r) (oldAt r) (tgtAt r) r.lo.length (anewAt r) = some W) :
    K2.frameAt (fxAt r) = some W := by
  obtain ⟨-, h2, h3, -, -⟩ := frB_says h
  show switchFrame (K2.skelOf (fxAt r)) (rowsC r) (tgtAt r) ((K2.idsOf (fxAt r)).getD 0 noId)
    ((K2.idsOf (fxAt r)).extract 1 (1 + (tgtAt r).kept.size)) = some W
  rw [h2, h3, K2.frame_congr (same_at h), frame_rowsC]
  exact hW

/-! ### A place and a record at which the sixteenth clause asks nothing -/

/-- A place's numbers, made here: nothing but the range of the positions is the record's. -/
def pAt (r : SwRow) : K2.P2 :=
  { name := "made", place := default, stands := .finish, grp := 0, firstTree := 0, samples := 1,
    work₁ := 0, roots := 0, seeds := 0, nonZero := 0, work₂ := 0, answers := 0, positions := 0,
    logN := r.g.main.logN, sent := [], read := [] }

/-- A record in front, made here: the bare start at the record's codes: ITS BOOK OF TREES IS
EMPTY. -/
def sAt (r : SwRow) : Rec := S.start r.cs { frame := (fxAt r).f, rows := ⟨default⟩ }

/-- The test: the book behind the sending, made of that empty book, has no place for one of the
messages that hold the carried rows. -/
def idleB (r : SwRow) : Bool :=
  ((K2.bookAt (K2.par9 (pAt r)).firstTree (fxAt r).st (sAt r).book (sAt r).roots
    (_root_.Tw.K2.switchNotices (fxAt r).T (fxAt r).others)).bind fun B =>
      (singleRowsOracles (fxAt r).f.rows).mapM fun o => B.place[o]?).isNone

set_option maxRecDepth 1000000 in
theorem idleB_full : (tableFullLit.all idleB) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem idleB_small : (tableSmallLit.all idleB) = true := by decide +kernel

theorem bind_bind_none {α β γ : Type} (a : Option α) (f : α → Option β) (g : α → β → Option γ)
    (h : (a.bind f).isNone = true) : (a.bind fun x => (f x).bind (g x)) = none := by
  cases a with
  | none => rfl
  | some x =>
    have h' : f x = none := by simpa using h
    show (f x).bind (g x) = none
    rw [h']
    rfl

/-- At that place and record the front reads nothing off the oracles, at any position. -/
theorem long_none {r : SwRow} (h : idleB r = true) (orc : ℕ → ℕ → List UInt64) (q : ℕ) :
    K2.longFront (pAt r) (sAt r) (fxAt r) orc q = none :=
  bind_bind_none _ _ _ h

section
variable (r : SwRow) (H : r.OK) (K : AtOK r) (hS : smpB r = true) (hF : frB r = true) (t₀ : ℕ)
  (oM oZ : Fin r.lo.length → ℕ)
  (kq : Fin r.lo.length → Prop) [DecidablePred kq] {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) (rowsAt r H t₀ oM oZ).G.C.J)
  (Z : Evader GE ((rowsAt r H t₀ oM oZ).G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf r.cs r.lo).sub kq).Msg × Wp)) (t : ℕ)
  (w₀ : ((heldAt r H t₀ oM oZ kq).foldD Sb sl Z A₀).tgt.W)

set_option quotPrecheck false in
local notation "RK" => (rowsAt r H t₀ oM oZ).keep r.kp
set_option quotPrecheck false in
local notation "memR" =>
  slotNum r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀) r.kp (numAt r)
set_option quotPrecheck false in
local notation "rowR" =>
  slotRow r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀) r.kp
set_option quotPrecheck false in
local notation "plR" => slotPl r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀) r.kp
  fun a => plB r (numAt r a)
set_option quotPrecheck false in
local notation "hPr" => heldAt r H t₀ oM oZ kq
set_option quotPrecheck false in
local notation:max "aK " k:max => (⟨⟨k.1.1, k.2.fst⟩, k.2.snd⟩ : {a // r.kp a})

/-- The caller's two maps of names and its data at a frame W with `Fit`. -/
noncomputable abbrev jRec (W : SwitchFrame)
    (Ft : Fit r.cs r.l (stageOf r.g t₀) W (memR) (rowR) (plR)) :=
  iJ (stageOf r.g t₀) W (memR) (rowR) (plR) r.cs r.l Ft.nameJ
noncomputable abbrev qRec (W : SwitchFrame)
    (Ft : Fit r.cs r.l (stageOf r.g t₀) W (memR) (rowR) (plR)) :=
  iQ (stageOf r.g t₀) W (memR) (rowR) r.cs r.l Ft.nameQ
noncomputable abbrev locRec (W : SwitchFrame)
    (Ft : Fit r.cs r.l (stageOf r.g t₀) W (memR) (rowR) (plR)) :=
  (closeSel (hPr) Sb sl Z A₀ r.cs r.l (jRec r H t₀ oM oZ W Ft) (qRec r H t₀ oM oZ W Ft) t w₀).loc

set_option quotPrecheck false in
local notation:max "locR " W:max Ft:max => locRec r H t₀ oM oZ kq Sb sl Z A₀ t w₀ W Ft

/-- **`FrontAt` at the made front, all but `strIs`**, under one name: there are a frame W with `Fit`
and a typed claim with held samples xc such that, at every place p, record sR, oracles orc and
string str of the open word: if str is what the front reads off the oracles (`StrIs`), then
`FrontAt` holds of the front `fxAt r`. -/
def FrontEnd : Prop := ∃ (W : SwitchFrame)
    (Ft : Fit r.cs r.l (stageOf r.g t₀) W (memR) (rowR) (plR))
    (xc : (locR W Ft).Xc × (locR W Ft).hd.Smp),
    ∀ (p : K2.P2) (sR : Rec) (orc : ℕ → ℕ → List UInt64) (str : (locR W Ft).C.ext.Str),
      StrIs (RK) (hPr) Sb sl Z A₀ r.cs r.l (jRec r H t₀ oM oZ W Ft) (qRec r H t₀ oM oZ W Ft) t w₀ p
        sR (fxAt r) orc (coordOf (RK).s (RK).Kp W (fxAt r).f.rows (memR) (rowR)) str →
      FrontAt (RK) (hPr) Sb sl Z A₀ r.cs r.l (jRec r H t₀ oM oZ W Ft) (qRec r H t₀ oM oZ W Ft) t w₀
        W p (memR) (rowR) (plR) (fun k => numAt r (aK k)) (fun _ _ => 0) sR orc xc str (fxAt r)

include K hS hF in
/-- **Fifteen of the sixteen clauses of `FrontAt` are met together at the record's made front.** -/
theorem front_member_at : FrontEnd r H t₀ oM oZ kq Sb sl Z A₀ t w₀ := by
  obtain ⟨W, A⟩ := atSwitch_at r H K t₀ oM oZ
  have hkept : ∀ a : {a // r.kp a}, W.kept[numAt r a]? = some (plB r (numAt r a)) := fun a => by
    rw [kept_of_frame r K W A.frame, List.getElem?_map, List.getElem?_range (numAt_lt r a)]
    rfl
  have hsz : (fxAt r).st.oracles.size = r.lo.length := stF_size r
  have hids : (fun i => (fxAt r).st.oracles.size + i) = fun i => r.lo.length + i := by
    funext i
    rw [hsz]
  obtain ⟨-, -, -, hpos, hz⟩ := frB_says hF
  obtain ⟨f1, f2, -, -, -, -, -, -⟩ := frame_fields _ _ _ _ _ W A.frame
  have e1 : r.cs.base.getD (codeIx r) default = W.code := by
    have f1' : r.cs.base[codeIx r]? = some W.code := f1
    rw [Array.getD_eq_getD_getElem?, f1']
    rfl
  have e2 : r.cs.mask.getD r.rider.maskCode default = W.zk := by
    have f2' : r.cs.mask[r.rider.maskCode]? = some W.zk := f2
    rw [Array.getD_eq_getD_getElem?, f2']
    rfl
  refine ⟨W, A.fit, ((readE (fxAt r).f.rows.target,
    vecOf (RK).s (RK).Kp (fxAt r).f.rows (rowR) (plR)),
    xsRec r H t₀ oM oZ kq Sb sl Z A₀ t w₀ W A.fit), fun p sR orc str hstr => ?_⟩
  refine frontAt_of_rest r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀) r.kp
    (fun a _ => a.2) H.h0 kq (numAt r) Sb sl Z A₀ r.cs r.l W (fun a => plB r (numAt r a)) A.fit t
    w₀ p sR orc (fxAt r) _ str (frameIs_at hF W A.frame) A.z32 ?_ rfl ?_ A.keptRows ?_ A.first
    A.next ?_ ?_ ?_ hstr rfl rfl (numAt_inj r) hkept ?_ ?_ ?_ ?_ ?_
  · -- twoOld
    intro a a' k k' hk hk' ho
    obtain ⟨ha, rfl⟩ := kept_at r K W A.frame a k hk
    obtain ⟨ha', rfl⟩ := kept_at r K W A.frame a' k' hk'
    rw [(smpB_says hS a ha).2.2.2.2.1, (smpB_says hS a' ha').2.2.2.2.1,
      List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ ha'] at ho
    exact (H.nodup.getElem_inj_iff).1 ho
  · -- keptPos
    intro i hi
    have h := Array.all_eq_true.1 hpos i hi
    exact of_decide_eq_true h
  · -- ell
    intro a k hk
    obtain ⟨ha, rfl⟩ := kept_at r K W A.frame a k hk
    have hlt : (plB r a).old < r.lo.length := by
      rw [(smpB_says hS a ha).2.2.2.2.1, List.getD_eq_getElem _ _ ha]
      have hx := H.kept _ (List.getElem_mem ha)
      obtain ⟨x, hx1, -⟩ := Option.map_eq_some_iff.1 hx
      exact (List.getElem?_eq_some_iff.1 hx1).1
    show (r.cs.base.getD ((stF r).oracles.getD (plB r a).old default).shape.code default).ell = _
    rw [← stB_front r _ hlt]
    exact A.ell a _ hk
  · -- mainVars
    intro v hv
    have hv' : v ∈ [tenAt r] := hv
    rw [List.mem_singleton] at hv'
    rw [hv', ← e1]
    show (List.replicate _ _).length = _
    rw [List.length_replicate]
  · -- d0
    show 1 ≤ W.zk.ell
    rw [← e2]
    exact hz
  · -- d1
    show 1 ≤ W.zk.ell
    rw [← e2]
    exact hz
  · -- hrb
    intro a
    rw [(smpB_says hS _ (numAt_lt r a)).2.2.2.2.2, shape_at]
  · -- hSl
    intro a
    rw [hids]
    exact paid_slots A _ _ (hkept a)
  · -- ha
    intro a
    have h := (smpB_says hS _ (numAt_lt r a)).1
    rwa [shape_at] at h
  · -- hc
    intro a
    have h := (smpB_says hS _ (numAt_lt r a)).2.1
    rw [shape_at] at h
    exact h.elim (fun h3 => Or.inl (Or.inr h3)) fun h1 => Or.inr ⟨H.h0 a.1 a.2, h1⟩
  · -- hst
    intro k
    obtain ⟨-, -, hp, hb, ho, -⟩ := smpB_says hS _ (numAt_lt r (aK k))
    rw [shape_at] at hp hb
    rw [numAt_get] at ho
    obtain ⟨row, hrow⟩ := form_of_pad r.cs (r.lo.get k.1.1).1 k.1.1.val seedAt 0 hp
    refine ⟨seedAt, row, zeroE, 1, ?_, ?_, ?_, ?_, rfl, rfl⟩
    · rw [ho]
      exact hrow
    · show ((stF r).oracles.getD (plB r (numAt r (aK k))).old default).sampleRows.toList[0]? = _
      rw [ho, stF_at r _ k.1.1.isLt]
      show some (rowAt r k.1.1.val) = _
      unfold rowAt
      rw [List.getD_eq_getElem _ _ k.1.1.isLt]
      have e : Send.form r.cs (r.lo[k.1.1.val]).1 k.1.1.val seedAt 0 = some row := hrow
      rw [e]
      rfl
    · show _ ≤ (List.replicate 64 zeroE).length
      rw [List.length_replicate]
      exact hb
    · show ((1 : GEˣ) : GE) = readE oneE
      rw [readE_one]
      rfl

/-- **`FrontAt` whole**, under one name: a frame, `Fit`, a typed claim with held samples and a
string at which all sixteen clauses hold of the made front, at the made place and record and all
oracles. -/
def FrontWhole : Prop := ∃ (W : SwitchFrame)
    (Ft : Fit r.cs r.l (stageOf r.g t₀) W (memR) (rowR) (plR))
    (xc : (locR W Ft).Xc × (locR W Ft).hd.Smp) (str : (locR W Ft).C.ext.Str),
    ∀ orc : ℕ → ℕ → List UInt64,
      FrontAt (RK) (hPr) Sb sl Z A₀ r.cs r.l (jRec r H t₀ oM oZ W Ft) (qRec r H t₀ oM oZ W Ft) t w₀
        W (pAt r) (memR) (rowR) (plR) (fun k => numAt r (aK k)) (fun _ _ => 0) (sAt r) orc xc str
        (fxAt r)

include K hS hF in
/-- **`FrontAt` has a member at the record**: fifteen clauses say something; the sixteenth, `strIs`,
is met IDLY: at the made record the front reads nothing off the oracles. -/
theorem front_whole_at (hI : idleB r = true) : FrontWhole r H t₀ oM oZ kq Sb sl Z A₀ t w₀ := by
  obtain ⟨W, Ft, xc, h⟩ := front_member_at r H K hS hF t₀ oM oZ kq Sb sl Z A₀ t w₀
  refine ⟨W, Ft, xc, fun _ _ => 0, fun orc => h (pAt r) (sAt r) orc _ ?_⟩
  intro q seg hq
  rw [long_none hI] at hq
  cases hq

/-- **At each of the 25 written records of the full example.** -/
theorem front_member_full (hr : r ∈ tableFullLit) : FrontEnd r H t₀ oM oZ kq Sb sl Z A₀ t w₀ :=
  front_member_at r H (atB_says (List.all_eq_true.1 atB_full r hr))
    (List.all_eq_true.1 smpB_full r hr) (List.all_eq_true.1 frB_full r hr) t₀ oM oZ kq Sb sl Z A₀ t
    w₀

theorem front_member_small (hr : r ∈ tableSmallLit) : FrontEnd r H t₀ oM oZ kq Sb sl Z A₀ t w₀ :=
  front_member_at r H (atB_says (List.all_eq_true.1 atB_small r hr))
    (List.all_eq_true.1 smpB_small r hr) (List.all_eq_true.1 frB_small r hr) t₀ oM oZ kq Sb sl Z A₀
    t w₀

theorem front_whole_full (hr : r ∈ tableFullLit) : FrontWhole r H t₀ oM oZ kq Sb sl Z A₀ t w₀ :=
  front_whole_at r H (atB_says (List.all_eq_true.1 atB_full r hr))
    (List.all_eq_true.1 smpB_full r hr) (List.all_eq_true.1 frB_full r hr) t₀ oM oZ kq Sb sl Z A₀ t
    w₀ (List.all_eq_true.1 idleB_full r hr)

theorem front_whole_small (hr : r ∈ tableSmallLit) : FrontWhole r H t₀ oM oZ kq Sb sl Z A₀ t w₀ :=
  front_whole_at r H (atB_says (List.all_eq_true.1 atB_small r hr))
    (List.all_eq_true.1 smpB_small r hr) (List.all_eq_true.1 frB_small r hr) t₀ oM oZ kq Sb sl Z A₀
    t w₀ (List.all_eq_true.1 idleB_small r hr)

end

/-! ### With no premise left, at letters that are there -/

/-- The record's promise, paid by the kernel's yes at the table. -/
theorem okFull (r : SwRow) (hr : r ∈ tableFullLit) : r.OK :=
  SwRow.ok_says r (List.all_eq_true.1 tableFullLit_ok r hr)

theorem okSmall (r : SwRow) (hr : r ∈ tableSmallLit) : r.OK :=
  SwRow.ok_says r (List.all_eq_true.1 tableSmallLit_ok r hr)

/-- `FrontWhole` at the letters `Letters.plain` (Johnson/Top/H0/K2Caller/Member.lean). -/
abbrev FrontPlain (r : SwRow) (H : r.OK) (t : ℕ) : Prop :=
  FrontWhole r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ
    (Letters.plain r H).kq (Letters.plain r H).Sb (Letters.plain r H).sl (Letters.plain r H).Z
    (Letters.plain r H).A₀ t (Letters.plain r H).w₀

/-- `SampleEnd` (Johnson/G/SwitchSampleMember.lean) at the same letters. -/
abbrev SamplePlain (r : SwRow) (H : r.OK) (t : ℕ) : Prop :=
  SampleEnd r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ
    (Letters.plain r H).kq (Letters.plain r H).Sb (Letters.plain r H).sl (Letters.plain r H).Z
    (Letters.plain r H).A₀ t (Letters.plain r H).w₀

/-- **`FrontAt` has a member at each of the 25 written records: no premise is left.** -/
theorem front_closed_full (r : SwRow) (hr : r ∈ tableFullLit) (t : ℕ) :
    ∃ H : r.OK, FrontPlain r H t ∧ SamplePlain r H t :=
  ⟨okFull r hr, front_whole_full r (okFull r hr) _ _ _ _ _ _ _ _ t _ hr,
    sample_member_full r (okFull r hr) _ _ _ _ _ _ _ _ t _ hr⟩

theorem front_closed_small (r : SwRow) (hr : r ∈ tableSmallLit) (t : ℕ) :
    ∃ H : r.OK, FrontPlain r H t ∧ SamplePlain r H t :=
  ⟨okSmall r hr, front_whole_small r (okSmall r hr) _ _ _ _ _ _ _ _ t _ hr,
    sample_member_small r (okSmall r hr) _ _ _ _ _ _ _ _ t _ hr⟩

/-- **The clause "sample" is not idle there**: at these letters the messages that stay open are the
kept members (`kqOf`): where the record keeps a message there is a held old message of which the
clause speaks. -/
theorem held_nonempty (r : SwRow) (H : r.OK) (t₀ : ℕ) (oM oZ : Fin r.lo.length → ℕ)
    (hk : r.kept ≠ []) : Nonempty {a // (heldAt r H t₀ oM oZ (kqOf r)).cl a} := by
  have h0 : 0 < r.kept.length := List.length_pos_iff.2 hk
  have hin : r.kept[0] ∈ r.kept := List.getElem_mem h0
  obtain ⟨x, hx1, hx2⟩ := Option.map_eq_some_iff.1 (H.kept _ hin)
  obtain ⟨hl, hx3⟩ := List.getElem?_eq_some_iff.1 hx1
  have hmem : r.mem ⟨r.kept[0], hl⟩ := by
    show (r.lo.get ⟨r.kept[0], hl⟩).1.mainRows ≠ 0
    have : r.lo.get ⟨r.kept[0], hl⟩ = x := hx3
    rw [this]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hx2
    exact hx2.1
  exact ⟨⟨⟨⟨r.kept[0], hl⟩, hin⟩, ⟨hmem, hin⟩⟩⟩

/-! ### The test on the front can say no -/

set_option maxRecDepth 1000000 in
/-- A control: with the last sent message struck out the test on the front says no at each record:
the front's statement with the announcements received no longer has the shapes of `stB` of the
whole record. -/
theorem frB_no_last : (tableFullLit.all fun r =>
    !decide ((K2.skelOf (fxAt { r with l := r.l.dropLast })).oracles.toList.map (·.shape) =
      (stB r).oracles.toList.map (·.shape))) = true := by decide +kernel

end Johnson.G

#print axioms Johnson.G.front_closed_full
#print axioms Johnson.G.front_closed_small
#print axioms Johnson.G.held_nonempty
#print axioms Johnson.G.front_whole_at
#print axioms Johnson.G.front_member_full
#print axioms Johnson.G.front_member_small
#print axioms Johnson.G.front_whole_full
#print axioms Johnson.G.front_whole_small
#print axioms Johnson.G.idleB_full
#print axioms Johnson.G.idleB_small
#print axioms Johnson.G.long_none
#print axioms Johnson.G.frB_no_last

#print axioms Johnson.G.front_member_at
#print axioms Johnson.G.same_at
#print axioms Johnson.G.frameIs_at
#print axioms Johnson.G.frB_full
#print axioms Johnson.G.frB_small
#print axioms Johnson.G.frame_rowsC
