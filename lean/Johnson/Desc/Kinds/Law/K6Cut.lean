-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6Cut.lean: **THE CUT**: THE COMPONENTS THAT K6's RULE READS OFF THE TABLE's
WITNESS, WITH SEGMENT 24's MATRICES CUT TO THE FOUR RANGES IN WHICH THE HEAD's CELLS LIE (namely
Hd.SmallH's four: the parts of hf · hd · hr · the copy of the stream, inside the rows and columns
that the layout and the border give), 0 OUTSIDE: SO THAT (1) K6's HALF OF (pin) ASKS ONLY
THAT THE SYMBOLS OF THESE FOUR MATRICES'
COLUMNS ARE SEATED AT PINNED MEMBERS: payable whether or not segment 24's list names messages that
are sent behind K6 (Law/K6Own24.lean's SeatsIn runs over the whole list) ·
(2) K6's RELATION's UNFENCED "every cell is small" FOLLOWS FROM Hd.SmallH (Hd.cellsH walks
into the neighbour's matrix beyond a matrix's features: at the cut list it meets an entry of a
range, or 0) ·
(3) THE ASSEMBLY AT ONE RECORD ENDS IN **Hd.HeadOrdLB AT THE UNCUT ownQ … w 24**: the
clause on the head of Johnson/Road/HeadL5BL.lean, whole: STATED AND PROVED.
WHOSE. "The head's record reads the entries within the shapes alone" IS ANOTHER FILE's
(Johnson/Goal/Meaning/HidHeadCongr.lean: AgreeH · smallH_congr · headOrd_congr): CALLED, NOT TYPED
AGAIN. "The same symbols in a column: the same cells there" is the library's
(Cb/Pv/Tail/Unique.lean: cellsOf_congr): called.
  InFour · ColFour · cutM · agreeH_cut · cut_small
  THREE LETTERS MORE
      ARE TIED:
  ms0 msR N THE PINNED MEMBERS ARE NO LETTER: the members of the reader's list at the tenants that
      segment 24 sends AT ITS MOMENT 0: the table's item "pin 24 0", WHICH ALONE STANDS IN THE CTX
      OF K6's ROW: a wider list could be had from no item of the table (the list's third office: the
      door).
  Wp.H.ns THE MASK ROW's LENGTH IS NO LETTER: the head's plan's own number ("entries of the link's
      mask row in use", OnBytes/Model/HeadPlan.lean).
  PlanK6 THE CONDITIONS ON THE PUBLIC LETTERS, AS ONE RECORD OF SIX: made:

      THE PUBLIC RECORD Wp IS ONE THAT THE VERIFIER's OWN MAKER publicOf RETURNS: were
          Wp a free record,
      the block reads its shape, frame, border and arrays' numbers, the
      fence "follows" its plan's list of matrices: at a made-up Wp with an empty list every
      condition would be empty · follows: THE SIZES s ARE THE
      PLANS' (Follows Wp s, Johnson/Goal/Meaning/HidPlan.lean): were
      s free beside Wp, at sizes without a matrix every condition would be empty and the
      reading a constant · named | seats: IN A COLUMN OF THE FOUR RANGES ALONE, at segment 24 alone:
      one tenant has the
                 number; the place is seated in the reader's list by a member sent at moment 0,
                     inside its ranges · maskNamed | maskIn: the like for the mask row's entries in
                     use. THE PROOF SPENDS FOUR OF THE SIX: "made" AND "follows" ARE FENCES: they
                         narrow the
                     sentence to the sizes that are meant.
  planK6_NM THE TWO FENCES BITE: under PlanK6 segment 24 has NHf + 4 matrices.
  ownCut_alike · compCut · readsPinnedW_cut · k6OwnCut (THE CALL) · **k06_ord**
THE LETTERS. Under "there is": PlanK6.made's three files (any that the maker takes to Wp). ∀-letters
that no premise reads: G (the frame's description of the files: IT STANDS IN THE ITEM "pins" ALONE
AND IS TIED TO NOTHING: at a G that tells no oracle no witness is pinned, and the law is the promise
alone: A THIRD LETTER THAT EMPTIES THE ITEM, beside smp and decT), the sizes and types. k06_ord:
Hd.NumH | Hd.BorderH (the head's public numbers at the full size, as numerals) are premises beside
FullH: numH_of_layout | borderH_of_layout (Johnson/Road/HeadPlace.lean) give them from the
layouts' return: NOT CALLED HERE.
WHAT IT DOES NOT SAY. THAT THE FOUR MATRICES ARE SENT IN FRONT OF K6: PlanK6 is a record of
conditions on public letters that HAS RUN AT NO PLAN. The planes' matrix (number NHf + 2) IS CUT
AWAY: K6In | K6Out say nothing of planes; were they to, a fifth range would come in. All that
Law/K6Index.lean does not say: public letters tied to no plan; the piece's premises; it does not
join the table; NO MEMBER: AND BY NAME: **smp**: at smp := none the item on both sides has no
witness
and the law is the promise alone (so says Johnson/Desc/Sound/BordersFill.lean's
head, which
also names the filling that is meant, in Johnson/Desc/Sound/Seed.lean): NO FILLING OF smp IS CALLED
HERE. k06_ord's LookCallsAt | RiderAt |
Hd.SmallH are other blocks' laws' conclusions: that those laws end in these sentences at THIS
reading is not shown. "The record is the instance's" · tab = EX (Law/LibTab.lean) · W.hS.digSh = 8 ·
"y = 0 if e < T": premises. No chance in it beyond p.Own's own.
GENERAL IN THE BLOCK: k6OwnCutBy: the call for any block b6, of any type of claims, that meets
Law/K6Steps.lean's record K6Steps Wp b6 on after: p.Own (on) (after) ...; k6OwnCut
is its instance at blockOf, K6On and K6After. (p.b = below
(seatedClaims' value) is false at every piece
of the seated description: there that value stands under the mark's guard, the driver's address and
the guard on the reply. THE ENTRY IS k6OwnCutBy at a block that meets K6Steps: Law/K6Steps.lean's
k6Steps_seated is carried to such a block by whoever shows that its step goes on only where the
seated value's does.)

-/
import Mathlib
import Johnson.Goal.Meaning.HidHeadCongr
import Johnson.Goal.Meaning.HidPlan
import OnBytes.Tie.Pv.Lookup.Ends.FoMadePub
import Johnson.Desc.Kinds.Law.K6Index

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open OnBytes.Road (Mats)
open OnBytes.Model.Verify (borderOf)
open Inst.Model.Layout (kRef hRef)
open VerifiableInference.OnPublicFiles.Flat (GE Holds)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.Sound (Piece Frame Sending Mem MsgT Fenced SmpStays ErrBears kitK
    kitFs
  SeatsNamed namedOnce seatOf)

/-- The column c of the matrix number a is one of the four ranges' columns. -/
def ColFour (h : OnBytes.Model.Head.Shape) (L : OnBytes.Model.Head.HL)
    (b : OnBytes.Model.Head.Border) (a c : Nat) : Prop :=
  (a < h.NHf ∧ c < L.k) ∨ (a = h.NHf ∧ c < L.kD) ∨ (a = h.NHf + 1 ∧ c < L.kR) ∨
    (a = h.NHf + 3 ∧ c < b.kxb)

/-- The entry (matrix a, row r, column c) lies in one of the four ranges of Hd.SmallH. -/
def InFour (h : OnBytes.Model.Head.Shape) (L : OnBytes.Model.Head.HL)
    (b : OnBytes.Model.Head.Border) (a r c : Nat) : Prop :=
  (a < h.NHf ∧ r < L.m ∧ c < L.k) ∨ (a = h.NHf ∧ r < L.mD ∧ c < L.kD) ∨
    (a = h.NHf + 1 ∧ r < L.mR ∧ c < L.kR) ∨ (a = h.NHf + 3 ∧ r < b.mxb ∧ c < b.kxb)

open Classical in
/-- **The list cut to the four ranges.** -/
def cutM (h : OnBytes.Model.Head.Shape) (L : OnBytes.Model.Head.HL) (b : OnBytes.Model.Head.Border)
    (Mh : Mats Int) : Mats Int := fun a r c => if InFour h L b a r c then Mh a r c else 0

namespace Came

theorem colFour_of_in {h : OnBytes.Model.Head.Shape} {L : OnBytes.Model.Head.HL}
    {b : OnBytes.Model.Head.Border} {a r c : Nat} (hin : InFour h L b a r c) : ColFour h L b a c :=
        by
  rcases hin with ⟨h1, _, h3⟩ | ⟨h1, _, h3⟩ | ⟨h1, _, h3⟩ | ⟨h1, _, h3⟩
  · exact Or.inl ⟨h1, h3⟩
  · exact Or.inr (Or.inl ⟨h1, h3⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h1, h3⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h1, h3⟩))

/-- The cut list agrees with the list within the four ranges: by make. -/
theorem agreeH_cut (h : OnBytes.Model.Head.Shape) (L : OnBytes.Model.Head.HL)
    (b : OnBytes.Model.Head.Border) (Mh : Mats Int) : Meaning.AgreeH h L b (cutM h L b Mh) Mh :=
  ⟨fun _ ha _ hr _ hc => if_pos (Or.inl ⟨ha, hr, hc⟩),
    fun _ hr _ hc => if_pos (Or.inr (Or.inl ⟨rfl, hr, hc⟩)),
    fun _ hr _ hc => if_pos (Or.inr (Or.inr (Or.inl ⟨rfl, hr, hc⟩))),
    fun _ hr _ hc => if_pos (Or.inr (Or.inr (Or.inr ⟨rfl, hr, hc⟩)))⟩

/-- **Under SmallH EVERY entry of the cut list is small.** -/
theorem cut_small {h : OnBytes.Model.Head.Shape} {L : OnBytes.Model.Head.HL}
    {b : OnBytes.Model.Head.Border} {Mh : Mats Int} (Sm : OnBytes.Road.Hd.SmallH h L b Mh)
    (a r c : Nat) : (cutM h L b Mh a r c).natAbs < 2 ^ 18 := by
  have key : |cutM h L b Mh a r c| < 2 ^ 18 := by
    unfold cutM
    by_cases hin : InFour h L b a r c
    · rw [if_pos hin]
      rcases hin with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact Sm.1 a h1 r h2 c h3
      · rw [h1]; exact Sm.2.1 r h2 c h3
      · rw [h1]; exact Sm.2.2.1 r h2 c h3
      · rw [h1]; exact Sm.2.2.2 r h2 c h3
    · rw [if_neg hin]
      norm_num
  rw [Int.abs_eq_natAbs] at key
  exact_mod_cast key

end Came

/-- **The pinned members: NO LETTER**: those members of the reader's list that sit at a tenant which
segment 24 sends at its moment 0: the table's item "pin 24 0", which alone stands in the ctx of K6's
row. -/
def ms0 (msR : List Mem) (N : Numbers) : List Mem :=
  msR.filter fun y => Decidable.decide (seatOf y ∈ N.sent 24 0)

variable {rows cols : Nat} (cs : OnBytes.Codes) {Tok : Type} (arr : Nat → Nat → Nat)
  (msR : List Mem) (N : Numbers) (s : Nat → Cb.Pv.Tail.Size)
  (seat : ∀ k, Fin (s k).NM → Nat → Nat → Nat × Nat × Nat) (Wp : OnBytes.Model.Verify.Public)
  (pl : Nat → Nat × Bool × Nat × Nat)

/-- **THE CONDITIONS ON THE PUBLIC LETTERS, AS ONE RECORD.** -/
structure PlanK6 : Prop where
  /-- the public record is one that the verifier's own maker returns: so its fields (the head's
      shape and layout, the head's plan, the layers') are tied to each other by that text -/
  made : ∃ (pol KL : ByteArray) (layout : Option ByteArray),
    OnBytes.Model.Verify.publicOf pol KL layout = .ok Wp
  /-- the sizes are the plans' (the integer model's own sentence): number of matrices, rows,
      columns; one radix, one shift -/
  follows : Meaning.Follows Wp s
  /-- in a column of the four ranges: segment 24's group has just one tenant with the number that
      the seat names -/
  named : ∀ (μ : Fin (s 24).NM) (r c : Nat), r < Alg.symRows ((s 24).m μ) → c < (s 24).k μ →
    ColFour Wp.hS Wp.HLy (borderOf Wp.y) μ.val c → namedOnce arr N 24 (seat 24 μ r c).1 = true
  /-- there: the place is seated in the reader's list, by a member sent at moment 0, inside its
      ranges -/
  seats : ∀ (μ : Fin (s 24).NM) (r c : Nat), r < Alg.symRows ((s 24).m μ) → c < (s 24).k μ →
    ColFour Wp.hS Wp.HLy (borderOf Wp.y) μ.val c →
    InCopy cs arr (ms0 msR N) msR N 24 (seat 24 μ r c).1 false (seat 24 μ r c).2.1
      (seat 24 μ r c).2.2
  /-- the like two for the mask row's entries in use: as many as the head's plan says -/
  maskNamed : ∀ j, j < Wp.H.ns → namedOnce arr N 24 (pl j).1 = true
  maskIn : ∀ j, j < Wp.H.ns →
    InCopy cs arr (ms0 msR N) msR N 24 (pl j).1 (pl j).2.1 (pl j).2.2.1 (pl j).2.2.2

/-- Segment 24's own integers off the witness, cut to the four ranges. -/
def ownCut {Cells : Type} (w : Wit Cells Tok MsgT) : Mats Int :=
  cutM Wp.hS Wp.HLy (borderOf Wp.y) (P5J.ownQ cs arr msR N s seat w 24)

/-- **The components that K6's rule reads, off the table's witness, cut.** -/
def compCut : Wit (Fin rows → Fin cols → GE) Tok MsgT → Pinned :=
  compOf Wp.hS Wp.HLy (borderOf Wp.y) (ownCut cs arr msR N s seat Wp) whOf
    (maskQ cs arr msR N 24 Wp.H.ns pl)

namespace Came

/-- **The cut list reads pinned places alone.** -/
theorem ownCut_alike {Cells : Type} (hP : PlanK6 cs arr msR N s seat Wp pl)
    (w w' : Wit Cells Tok MsgT) (hA : ReadAlike cs arr (ms0 msR N) w w') :
    ownCut cs arr msR N s seat Wp w = ownCut cs arr msR N s seat Wp w' := by
  funext a r c
  unfold ownCut cutM
  by_cases hin : InFour Wp.hS Wp.HLy (borderOf Wp.y) a r c
  · rw [if_pos hin, if_pos hin]
    unfold P5J.ownQ Meaning.ownOf OnBytes.Road.Rows.Norms.mzTot
    beta_reduce
    by_cases h1 : a < (s 24).NM
    · rw [dif_pos h1, dif_pos h1]
      by_cases h2 : c < (s 24).k (⟨a, h1⟩ : Fin (s 24).NM)
      · rw [dif_pos h2, dif_pos h2]
        by_cases h3 : r < (s 24).m (⟨a, h1⟩ : Fin (s 24).NM)
        · rw [dif_pos h3, dif_pos h3]
          refine congrFun (Cb.Pv.Tail.cellsOf_congr (Λ := Cb.Pv.Tail.symL Cb.Gl.E (s 24))
            (μ := ⟨a, h1⟩) (c := ⟨c, h2⟩) fun i' => ?_) ⟨r, h3⟩
          exact readAt_alike cs arr (ms0 msR N) msR N 24 _ w w'
            (hP.named ⟨a, h1⟩ i'.val c i'.isLt h2 (colFour_of_in hin)) hA false _ _
            (hP.seats ⟨a, h1⟩ i'.val c i'.isLt h2 (colFour_of_in hin))
        · rw [dif_neg h3, dif_neg h3]
      · rw [dif_neg h2, dif_neg h2]
    · rw [dif_neg h1, dif_neg h1]
  · rw [if_neg hin, if_neg hin]

/-- **This kind's half of (pin), at the cut: A THEOREM.** -/
theorem readsPinnedW_cut (hP : PlanK6 cs arr msR N s seat Wp pl) :
    ReadsPinnedW cs arr (ms0 msR N)
      (compCut (rows := rows) (cols := cols) (Tok := Tok) cs arr msR N s seat Wp pl) :=
  readsPinnedW_comp cs arr (ms0 msR N) _ _ _ _ whOf _ (ownCut_alike cs arr msR N s seat Wp pl hP)
    (maskQ_alike cs arr (ms0 msR N) msR N 24 Wp.H.ns pl hP.maskNamed hP.maskIn)

/-- **The two fences bite**: under PlanK6 segment 24 has the head's NHf + 4 matrices: sizes without
a
matrix, and a made-up public record with an empty list of matrices, are shut out. -/
theorem planK6_NM (hP : PlanK6 cs arr msR N s seat Wp pl) : (s 24).NM = Wp.hS.NHf + 4 := by
  obtain ⟨pol, KL, layout, hW⟩ := hP.made
  obtain ⟨stream, _, hm, _⟩ := _root_.Fo.Pub.public_mats hW
  rw [hP.follows.NM 24 (by omega)]
  show (Meaning.tlAt Wp 24).mats.size = _
  have e : Meaning.tlAt Wp 24 = Wp.H.tl := by
    unfold Meaning.tlAt
    simp
  rw [e, hm]
  simp [OnBytes.Model.Head.matsH]

/-- **THE CALL, AT THE CUT.** -/
theorem k6OwnCutBy {Xi : Type} (G : FileDescription Xi)
    (smp : S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (decT : (Nat → Option (Nat × List UInt64)) → S → Option (Fin rows → Fin cols → GE))
    (fld : Fmt.Fld) (Fr : Frame)
    {Cl : Type} (p : Piece (_root_.Run.ckP fld) Fr S Cl (Wit (Fin rows → Fin cols → GE) Tok MsgT))
    (b6 : Block S Cl) {on after : S → Prop}
    (hst : K6Steps Wp b6 on after) (hpb : p.b = Sound.below b6)
    (hback : p.back = []) (hext : ∀ a τ w, p.ext a τ w = w)
    (hP : PlanK6 cs arr msR N s seat Wp pl) (hF : Fenced p.base (ms0 msR N))
    (hS : SmpStays cs smp p (ms0 msR N)) (hD : DecTStays decT p)
    (hlog : ∀ d, d ∈ toRDs p.ds → d.entry.logN ≤ 64)
    (hErr : ErrBears (_root_.Run.ckP fld)
      (fun j => kitK (toRDs p.ds) j *
        (priceAt (parOf Wp.hS (workOf Wp)) j * kitFs fld (toRDs p.ds) j)) (toRDs p.ds) 0 p.err) :
    p.Own (fun a => on a.1) (fun b => after b.1)
      (meansW cs G arr smp decT (ms0 msR N) (compCut cs arr msR N s seat Wp pl)
        (base24 cs arr msR N s seat) Wp Fr) InK6 OutK6 :=
  k6OwnWBy cs G arr smp decT (ms0 msR N) _ _ Wp fld Fr p b6 hst hpb hback hext
    (readsPinnedW_cut cs arr msR N s seat Wp pl hP) hF hS hD hlog hErr

/-- The same at the block at the unit type, under K6On, with K6After behind.
    -/
theorem k6OwnCut {Xi : Type} (G : FileDescription Xi)
    (smp : S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (decT : (Nat → Option (Nat × List UInt64)) → S → Option (Fin rows → Fin cols → GE))
    (fld : Fmt.Fld) (Fr : Frame)
    (p : Piece (_root_.Run.ckP fld) Fr S Unit (Wit (Fin rows → Fin cols → GE) Tok MsgT))
    (b6 : Block S Unit) (hb6 : blockOf Wp 24 = some b6) (hpb : p.b = Sound.below b6)
    (hback : p.back = []) (hext : ∀ a τ w, p.ext a τ w = w)
    (hP : PlanK6 cs arr msR N s seat Wp pl) (hF : Fenced p.base (ms0 msR N))
    (hS : SmpStays cs smp p (ms0 msR N)) (hD : DecTStays decT p)
    (hlog : ∀ d, d ∈ toRDs p.ds → d.entry.logN ≤ 64)
    (hErr : ErrBears (_root_.Run.ckP fld)
      (fun j => kitK (toRDs p.ds) j *
        (priceAt (parOf Wp.hS (workOf Wp)) j * kitFs fld (toRDs p.ds) j)) (toRDs p.ds) 0 p.err) :
    p.Own (fun a => K6On Wp a.1) (fun b => K6After Wp b.1)
      (meansW cs G arr smp decT (ms0 msR N) (compCut cs arr msR N s seat Wp pl)
        (base24 cs arr msR N s seat) Wp Fr) InK6 OutK6 :=
  k6OwnCutBy cs arr msR N s seat Wp pl G smp decT fld Fr p b6
    ((k6Steps_blockOf Wp 24 b6 hb6).weaken fun _ h => h.1) hpb hback hext hP hF hS hD hlog hErr

/-- **THE ASSEMBLY AT ONE RECORD ENDS IN HeadOrdLB AT SEGMENT 24's OWN INTEGERS, UNCUT.**
-/
theorem k06_ord (hr0 : rows ≤ hRef) (hc0 : cols ≤ 2 ^ kRef) (s0 : S) (y : Nat)
    (x : Inst.Model.Instance Inst.Model.ppref) (i : Cm.Idx) (tab : Nat → Nat)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (hon : K6On Wp s0)
    (hin : K6In Wp s0 (compCut cs arr msR N s seat Wp pl w))
    (hy : Reply.token (seatAt Wp.hS (readsOf Wp)).toSeat s0 = some y)
    (hlook : LookCallsAt Wp tab s0 y (compCut cs arr msR N s seat Wp pl w).1)
    (hrider : RiderAt Wp s0 y (compCut cs arr msR N s seat Wp pl w).1)
    (hSm : OnBytes.Road.Hd.SmallH Wp.hS Wp.HLy (borderOf Wp.y) (P5J.ownQ cs arr msR N s seat w 24))
    (hF : OnBytes.Road.Hd.FullH Wp.hS) (hNum : OnBytes.Road.Hd.NumH Wp.hS Wp.HLy)
    (hBd : OnBytes.Road.Hd.BorderH (borderOf Wp.y)) (h8 : Wp.hS.digSh = 8) (hr : s0.rowR = x.r)
    (he : s0.rowE = x.e) (htok : ∀ t, t < 1024 → s0.tokv.getD t 0 = x.tok t) (hyx : y = x.y.val)
    (htab : ∀ u, u < 2 ^ 16 → (tab u : Int) = Inst.Model.EX u) (hH : Holds w.cells i)
    (hy0 : x.e < Inst.Model.ppref.T → ((x.y.val : Nat) : ZMod Cb.Gl.p) = 0) :
    OnBytes.Road.Hd.HeadOrdLB Wp.hS Wp.HLy Wp.y (OnBytes.Road.Hd.npOf Wp.hS)
      (OnBytes.Road.Hd.polOf Wp.hS) i.mat x (P5J.ownQ cs arr msR N s seat w 24) := by
  have hC : _root_.Policy.HeadCl (OnBytes.Road.Hd.npOf Wp.hS) (OnBytes.Road.Hd.polOf Wp.hS) i.mat x
      (OnBytes.Road.Hd.cellsH Wp.hS Wp.HLy (borderOf Wp.y) (ownCut cs arr msR N s seat Wp w)) := by
    unfold compCut at hin hlook hrider
    refine k06_whole_own Wp.HLy (borderOf Wp.y) (ownCut cs arr msR N s seat Wp) whOf
      (maskQ cs arr msR N 24 Wp.H.ns pl) Wp s0 y x i.mat tab w hon hin hy hlook hrider ?_ ?_ hF h8
          hr
      he
      htok hyx htab (whOf_holds hr0 hc0 hH)
    · intro m f t
      cases m <;> exact cut_small hSm _ _ _
    · intro f t
      exact cut_small hSm _ _ _
  exact Meaning.headOrd_congr hNum hBd (agreeH_cut _ _ _ _)
    ⟨Meaning.smallH_congr (agreeH_cut _ _ _ _).symm hSm, hC, hy0⟩

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.ownCut_alike
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.planK6_NM
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.k6OwnCutBy
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.k6OwnCut
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.k06_ord
#check @VerifiableInference.Desc.Kinds.Head.Law.Came.k6OwnCut
#check @VerifiableInference.Desc.Kinds.Head.Law.Came.k06_ord
