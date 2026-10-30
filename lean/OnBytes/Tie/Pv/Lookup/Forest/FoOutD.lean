-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lookup/Forest/FoOutD.lean: the share of a lookup of a sub-proof in a run on views:
the record of end values; and its law to the typed block: what the typed block puts out is one
written function of that record. Beside it a Bool test on plain data, for a run that is fed its
rounds from elsewhere.

Definitions with code, statements and proofs.

Why. The typed block forB (OnBytes/Tie/Pv/Lookup/Forest/FoHole.lean) has no test: it hands claims
on. It has no code and is
never run: soundness is proved of it. A run on views needs at a lookup (1) what the lookup hands on,
as a small value, and (2) a law that ties (1) to the typed block's output at the typed transcript
made of the views. For (1): endsOf (Forest/FoEnds.lean), a function on lists over a commutative
ring. For (2): OutAt (Forest/FoOutOf.lean) says of an out-statement, field by field, what it is in
that record: here its right sides are laid together into one term, and the equation is proved.

WHAT STANDS AT A LOOKUP IN A RUN UNDER THE FRAME: THE PLAN's h · FoNums.ok h · WRITTEN ROUNDS ds
THAT MEET specF h · THEN endsOf h lm jLK rs, AND NOTHING ELSE OF THIS FILE.
THE LAWS TO THE TYPED SIDE (lookFitsB_meets; lookOutD_outAt, _claim, _run, _fits; lookEnds_fits; the
three at a view) ALL STAND UNDER FoNums.ok h (a public Bool with code): planF h and specF h are
total in h: at a record that fails it the test below can pass and no law follows. NO Bool ON THE
ROUNDS IS WANTED UNDER THE FRAME: the block has no typed test to which one could be equal, and the
fit lies in the type of the written rounds: at ds that meet the spec every written transcript's
rounds fit (flWsT_fit, Forest/FoPeelKitT.lean; lookFitsB_view).
endsOf's record is short lists, points and scalars: it can be named, handed on and compared field by
field. lookRowsE, lookOutE, lookRowsD, lookOutD HAVE CODE BUT ARE THE LAW's BRIDGE: THEY ARE NOT TO
BE BUILT AT A REAL SIZE. The reason: SRow (Cb/Pv/Lookup/Out/TwV.lean) is sparse by type (a list of a
place and a coefficient), but three rows hold a list over all cells of the planes' matrix: bitsForm
runs over 2 ^ (w + d) cells and stands in rowEnd and in rowBitE; rowNum runs over 2 ^ d rows times n
+ 2 planes. The record holds these three succinctly: for the leaves' row lvEps, lvFin, lvXs, lvDg,
lvInc, leavesA and the point zb0; for the bits' end row bitV, bitBe and the point zb1; rowNum is
public. And a TX (Cb/Ld/LdLkpTree.lean) holds functions (pt : ℕ → E; mf and each row's cf : N → E,
spread by dense and toRow): two such values cannot be compared by a Bool test.

Definitions (namespace Fo); none bears the mark "noncomputable" or, by its text, calls choice:
  "lookFitsB" h rs : Bool (asks decidable equality on K): the rounds' numbers of scalars sent and of
    elements drawn are planF h, and in every round in which specF h asks it no element drawn is 0.
    ITS USE: WHERE ROUNDS ARE CUT OUT OF A VIEW BY OFFSETS, OR LAID BY A HARNESS: there endsOf
    answers at any rs, by silent defaults (headD, getD, take, drop): a record of which no law
    speaks. Not in it: a round's test of work: rs holds no work.
  "lookRowsE" h lm jLK En, "lookOutE" h lm jLK ι st En: the rows and the out-statement AS FUNCTIONS
    OF THE RECORD En ALONE, beside the public h, lm, jLK, the renaming ι and the caller's state st:
    the public numbers are numsF h lm jLK En.theta.
  "lookRowsD" h lm jLK rs, "lookOutD" h lm jLK ι rs st : TX (St₀ × K) K (Option J₀): OutAt's right
    sides, to the letter: they read forN and forTrace beside the record (in rowEnd, rowBitE,
    rowNum). The point, on which OutAt has no equation: fun t => (En.zx ++ En.zy).getD t 0 (over a
    field: Blocks.ofList of that list, by definition).
  "lookOutGl": lookOutD at the challenge field Cb.Gl.E.
Statements:
  "lookFitsB_yes", "lookFitsB_of": lookFitsB h rs = true if and only if meet's two premises hold
    (the sizes; YNonZero). "lookFitsB_meets": under FoNums.ok h its yes gives a typed transcript τ
    with forFl h L Ex τ = rs.
  "lookRowsD_ofEnds", "lookOutD_ofEnds": lookOutD h lm jLK ι rs st = lookOutE h lm jLK ι st (endsOf
    h lm jLK rs), at every rs: SO EQUAL RECORDS GIVE EQUAL TYPED OUTPUTS. By ends_leaves
    (Forest/FoEnds.lean) for the leaves' row, and by unfolding for the bits' end row and the public
    numbers.
  "lookOutD_rows": it has Fo.nRows h rows (Forest/FoOutLen.lean), at every rs.
  "lookOutD_outAt": under FoNums.ok h, at every rs: OutAt at lookOutD (the point's length by
    ends_zx_len, ends_zy_len, Forest/FoJoinOut.lean). "lookOutD_claim": under out_iff_claims'
    premises: at every x with OutAt at the same data the typed out-claim holds if and only if it
    holds at lookOutD. (It carries that one predicate alone.)
  "lookOutD_run": THE ONE EQUATION: under FoNums.ok h and the layout's two laws: at every statement
    a and typed transcript τ: (forB E h L V₀ V₀C).R.red.out a τ = some (lookOutD h lm jLK (placeOf
    mk pl) (forFl h L Ex τ) a.1, a.2).
  "lookOutD_fits", "lookEnds_fits": WHAT THE TEST's YES IS WORTH: under the same, where lookFitsB h
    rs = true: at every a there is a τ with forFl h L Ex τ = rs and (forB …).R.red.out a τ = some
    (lookOutE h lm jLK (placeOf mk pl) a.1 (endsOf h lm jLK rs), a.2). (That τ is by existence: no
    code, not said to be the only one: harmless: lookOutD_run has the equation at every τ.)
  "Fo.Peel.lookOutD_view": AT THE IMAGE OF A FILE's WRITTEN ROUNDS: for written rounds ds that meet
    specF h (MeetsT) and hold no answers (NoAns), at every written transcript τ: (forB GE h L V₀
    V₀C).R.red.out a (M.view τ) = some (lookOutD … ((rvT (ckP .two) ds τ).map (rdRV Reading.gl))
    a.1, a.2), M := mapsT ds _ (specF h) (rkFor h L Ex).R _ (Peel/FoPeelMapsT.lean). Four laws in a
    row: lookOutD_run; (rkFor …).read (Forest/FoPeelForB.lean); mapsT_read; flWsT_view
    (Forest/FoPeelKitT.lean).
  "Fo.Peel.lookEnds_view": THE LAW IN A RUN's TERMS: the same with … = some (lookOutE h lm jLK
    (placeOf mk pl) a.1 (endsOf h lm jLK ((rvT (ckP .two) ds τ).map (rdRV Reading.gl))), a.2).
  "Fo.Peel.lookFitsB_view": at such ds and every τ: lookFitsB h ((rvT …).map (rdRV Reading.gl)) =
    true (flWsT_fit; spec_sizes, Forest/FoMeet.lean; ynz_of_fit, Forest/FoPeelForB.lean). It takes
    the decision of equality on GE as a letter: such a decision has at most one member, so the law
    holds at whichever a run finds.
  WHICH LAW SERVES WHAT. lookOutD_view, lookEnds_view: a law "the run's output at a block is the
    typed block's output at the typed transcript made of the views": under FoNums.ok h, the layout's
    two laws, hM and hA: they stand at Maps.view, which is total: no test of work and no lookFitsB
    among their premises. Who gives hM at a plan: `meets_planT`
    (OnBytes/Tie/Pv/Lookup/Forest/FoPeelT.lean), from the planner's yes and 1 ≤ h.v, for rounds with
    `Plain` whose entries are the plan's; hA, and `Plain` at ds := a stretch of the chain's written
    rounds: by reading alone;
    not spent here. THE OUTPUT IS A TX, A RUN CARRIES THE RECORD: so the next block's law must stand
    at the statement lookOutE … En: none lies yet. lookFitsB: UNDER THE FRAME IT CANNOT SAY NO
    (lookFitsB_view): it guards a run that is fed its rounds from elsewhere: there, under FoNums.ok
    h, lookEnds_fits says what its yes is worth.
  Helpers: "nat_rev_get", "nat_rev_ofFn" (a vector read backwards, as a function on ℕ, is the
    reversed list, 0 beyond), "eqN_revList", "drop_take_rev", "sizes_of_fit", "clK_ptL", "rd_pt"
    (rd_read's sixth clause: the point itself).

How lookOutD_run is proved. hcOut1E (Forest/FoOut.lean) gives four fields. On the point it gives the
equality weights alone. The point itself: the block's out is A.rd of the chain's last state
(allK₀_out, OnBytes/Tie/Pv/Lookup/Shift/ShiftKOut.lean: an equation with no premise); its masked
claim's pt is Blocks.nat of the keys' top point read backwards (clK_pt, Forest/FoState.lean: by
definition): 0 beyond v' + 1; clK_pnt (there; key_pnt, Value/TwKeyEq.lean) has that point's list as
pntTop … of the trace; rd_read's steps (Forest/FoRead.lean) carry it to the flat trace.

KIN. one_out (OnBytes/Tie/Pv/Lookup/Out/TwOutEq.lean): the like equation of ANOTHER block (oneK: its
out is rows alone: the claim on the keys is already a row through kAt: no state, no point): the
pattern. OutIs, hcOut1E, HCout1, rd_read, all_read, outAt_run, LookPubOK.outAt
(Ends/FoLookPub.lean): the out-statement under "there is", field by field, the point by its weights.
rows16, forV (Forest/FoV.lean), r16 (Cb/Pv/Lookup/Forest/FoNat.lean) with ends_r16: lookRowsD is r16
at forN and forTrace. Ends.rows (Forest/FoEnds.lean): the short rows alone. LkAsmH.rd
(Cb/Pv/Lookup/Asm/AsmH.lean): the TX of the typed last state, not of plain data. The other way, a TX
taken apart: outRho, outZx, outZy, outZk (Rider/ForBCalls.lean).
At a view: lookCarryT_read, _none, _fits, _view, _pass (Forest/FoPeelT.lean), lookCarryT_reads
(Peel/FoPeelAtT.lean): on the partial carry (CarryS.tr); mapsT_ok, _view, _read
(Peel/FoPeelMapsT.lean), outs_img (Forest/FoPeelKit.lean), lookImgT_eq (Peel/FoPeelPlace.lean): the
image. By a net on theorems' first lines none of the library's names the block's out at a view.
ynz_of_fit is sizes_of_fit's sister; rfit_of (Forest/FoMeet.lean) is the way there.

forFl IS THE LAW's, NEVER RUN: it reads a typed transcript as plain data and has no code (marked).
In a run rs comes of the view's rounds: that reading is another file's.

What of the claim it touches: the public files: through h : FoNums.Sh (the record of a forest), lm,
jLK, ι, ds: bare letters here, tied to no file, and read. The prompt, the output tokens, the
commitment ID: nothing: st is a letter that is handed through. (The proof file's rounds: through rs
and τ: letters.)

Limits. AT LETTERS: no value of a plan. No entry's value is read here: the out-statement holds FORMS
on entries (ι names the places; mf and the rows' cf weigh the mask entries): nothing here says that
a mask entry is read, or spent once. No law here carries to verify() by itself: that wants the
reading of a view's rounds as rs, and a taker for what is handed on: NOT YET: a map from the
record's short rows, points and factors into the forms in which a run's state keeps its claims. That
endsOf runs in bearable time at a real record is a run's to show (leavesA sums over 2 ^ d rows, tT
over 2 ^ kT for each call). lm and jLK are letters: out_iff_claims asks 5 ≤ lm ≤ h.kT + 5; whence
jLK comes in a run is open. At lookOutGl Lean's line on axioms names Classical.choice, at lookOutD
propext alone: where the choice enters is not known.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoOutOf
import OnBytes.Tie.Pv.Lookup.Forest.FoMeet
import OnBytes.Tie.Pv.Lookup.Forest.FoOutLen
import OnBytes.Tie.Pv.Lookup.Forest.FoState
import OnBytes.Tie.Pv.Lookup.Forest.FoJoinOut
import OnBytes.Tie.Pv.Lookup.Peel.FoPeelMapsT
import OnBytes.Tie.Pv.Lookup.Forest.FoPeelForB
import OnBytes.Tie.Pv.Lookup.Shift.ShiftKOut
import OnBytes.Tie.Pv.Lookup.Value.TwKeyEq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open Iop IOR Cb Cb.Tw Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole TwV Tw3 Tw Cb.Fo Cb.Fo.NumsEq Cb.Fo.Pin

/-! ### The definitions -/

/-- **The rounds' plain data fit**: the plan's sizes, and no 0 drawn where the spec asks it. -/
def lookFitsB {K : Type} [Zero K] [DecidableEq K] (h : FoNums.Sh) (rs : Rounds K) : Bool :=
  decide (rs.map sizeOf = planF h) &&
    (List.range rs.length).all fun i =>
      !((specF h).getD i ⟨0, 0, false⟩).nz || (rs.getD i ([], [])).2.all fun x => decide (x ≠ 0)

/-- The rows, as a function of the record of end values alone (beside the public numbers). -/
def lookRowsE {K : Type} [CommRing K] (h : FoNums.Sh) (lm jLK : ℕ) (En : Ends K) :
    List (SRow Pl K) :=
  En.tieRows.reverse ++
    (En.keyRows.reverse ++ ((En.tabRows.reverse ++
      [⟨hide (numsF h lm jLK En.theta).ledE En.lvDg En.lvXs ++ scale En.lvEps En.lvInc ++
          scale (En.lvEps * En.leavesA) (bitsForm (numsF h lm jLK En.theta) En.zb0.reverse),
          En.lvFin - En.lvEps * 1⟩,
        En.bitU,
        ⟨bitsForm (numsF h lm jLK En.theta) En.zb1.reverse ++
          [((numsF h lm jLK En.theta).ledB.sh 0, En.bitBe)], En.bitV⟩]) ++
      [rowNum (numsF h lm jLK En.theta)]))

/-- **The out-statement, as a function of the record of end values alone.** -/
def lookOutE {K : Type} [CommRing K] {St₀ J₀ : Type} [DecidableEq J₀] (h : FoNums.Sh) (lm jLK : ℕ)
    (ι : Pl → Option J₀) (st : St₀) (En : Ends K) : TX (St₀ × K) K (Option J₀) :=
  ((st, En.theta),
    ⟨fun t => (En.zx ++ En.zy).getD t 0, dense (mapL ι En.cEndF), En.alpha - En.cEndC⟩,
    ((lookRowsE h lm jLK En).map (rowMap ι)).map toRow)

/-- The rows that the lookup puts out, as sparse lists over the plain places. -/
def lookRowsD {K : Type} [CommRing K] (h : FoNums.Sh) (lm jLK : ℕ) (rs : Rounds K) :
    List (SRow Pl K) :=
  (endsOf h lm jLK rs).tieRows.reverse ++
    ((endsOf h lm jLK rs).keyRows.reverse ++ (((endsOf h lm jLK rs).tabRows.reverse ++
      [rowEnd (forN h lm jLK rs) (forTrace h lm jLK rs), (endsOf h lm jLK rs).bitU,
        rowBitE (forN h lm jLK rs) (forTrace h lm jLK rs)]) ++
      [rowNum (forN h lm jLK rs)]))

/-- **What the lookup of a sub-proof puts out, with code.** -/
def lookOutD {K : Type} [CommRing K] {St₀ J₀ : Type} [DecidableEq J₀] (h : FoNums.Sh) (lm jLK : ℕ)
    (ι : Pl → Option J₀) (rs : Rounds K) (st : St₀) : TX (St₀ × K) K (Option J₀) :=
  ((st, (endsOf h lm jLK rs).theta),
    ⟨fun t => ((endsOf h lm jLK rs).zx ++ (endsOf h lm jLK rs).zy).getD t 0,
      dense (mapL ι (endsOf h lm jLK rs).cEndF),
      (endsOf h lm jLK rs).alpha - (endsOf h lm jLK rs).cEndC⟩,
    ((lookRowsD h lm jLK rs).map (rowMap ι)).map toRow)

/-- The same at the challenge field. -/
def lookOutGl {St₀ J₀ : Type} [DecidableEq J₀] (h : FoNums.Sh) (lm jLK : ℕ) (ι : Pl → Option J₀)
    (rs : Rounds Cb.Gl.E) (st : St₀) : TX (St₀ × Cb.Gl.E) Cb.Gl.E (Option J₀) :=
  lookOutD h lm jLK ι rs st

/-! ### The test -/

/-- The test's yes gives meet's two premises. -/
theorem lookFitsB_yes :
  ∀ (K : Type) [Zero K] [DecidableEq K] (h : FoNums.Sh) (rs : Rounds K), lookFitsB h rs = true →
    rs.map sizeOf = planF h ∧ YNonZero h rs := by
  intro K _ _ h rs hf
  unfold lookFitsB at hf
  rw [Bool.and_eq_true] at hf
  refine ⟨of_decide_eq_true hf.1, fun i x hn hx => ?_⟩
  by_cases hi : i < rs.length
  · have h1 := List.all_eq_true.1 hf.2 i (List.mem_range.2 hi)
    rw [hn] at h1
    have h2 : ((rs.getD i ([], [])).2.all fun x => decide (x ≠ 0)) = true := by simpa using h1
    exact of_decide_eq_true (List.all_eq_true.1 h2 x hx)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)] at hx
    cases hx

/-- The way back: meet's two premises give the test's yes. -/
theorem lookFitsB_of {K : Type} [Zero K] [DecidableEq K] (h : FoNums.Sh) (rs : Rounds K)
    (hs : rs.map sizeOf = planF h) (hz : YNonZero h rs) : lookFitsB h rs = true := by
  unfold lookFitsB
  rw [Bool.and_eq_true]
  refine ⟨decide_eq_true hs, List.all_eq_true.2 fun i _ => ?_⟩
  cases hn : ((specF h).getD i ⟨0, 0, false⟩).nz with
  | false => rfl
  | true =>
    show (!true || (rs.getD i ([], [])).2.all fun x => decide (x ≠ 0)) = true
    rw [Bool.not_true, Bool.false_or]
    exact List.all_eq_true.2 fun x hx => decide_eq_true (hz i x hn hx)

/-- Data that fit a spec round for round have its sizes. -/
theorem sizes_of_fit {K : Type} [Zero K] : ∀ {sp : List RSp} {rs : Rounds K},
    List.Forall₂ RFit sp rs → rs.map sizeOf = szs sp
  | _, _, .nil => rfl
  | _, _, .cons h1 h2 => by
    rw [List.map_cons, sizes_of_fit h2]
    unfold sizeOf szs
    rw [h1.1, h1.2.1, List.map_cons]

/-- **Data that fit are the reading of a typed transcript.** -/
theorem lookFitsB_meets :
  ∀ (E : Type) [Field E] [Fintype E] [DecidableEq E] (St₀ J₀ : Type) [Fintype J₀] [DecidableEq J₀]
    (h : FoNums.Sh), FoNums.ok h = true → ∀ (L : Lay E St₀ J₀) (Ex : ExtSpec) (rs : Rounds E),
    lookFitsB h rs = true →
    ∃ τ : Tr (forB E h L V₀ V₀C (Ex := Ex)).R.shape, forFl h L Ex τ = rs := by
  intro E _ _ _ St₀ J₀ _ _ h H L Ex rs hf
  obtain ⟨hs, hz⟩ := lookFitsB_yes E h rs hf
  have hv : 1 ≤ h.v := by
    have := ok_v H
    omega
  exact meet h L Ex rs hv hs hz

/-! ### A function of the record; the number of rows -/

/-- The rows are a function of the record. -/
theorem lookRowsD_ofEnds {K : Type} [CommRing K] (h : FoNums.Sh) (lm jLK : ℕ) (rs : Rounds K) :
    lookRowsD h lm jLK rs = lookRowsE h lm jLK (endsOf h lm jLK rs) := by
  have e : rowBitE (forN h lm jLK rs) (forTrace h lm jLK rs) =
      ⟨bitsForm (forN h lm jLK rs) (endsOf h lm jLK rs).zb1.reverse ++
        [((forN h lm jLK rs).ledB.sh 0, (endsOf h lm jLK rs).bitBe)],
        (endsOf h lm jLK rs).bitV⟩ := by
    unfold endsOf rowBitE
    simp only [List.reverse_reverse]
  unfold lookRowsD lookRowsE
  rw [ends_leaves, e]
  rfl

/-- **Equal records give equal typed outputs**: lookOutD is a function of the record. -/
theorem lookOutD_ofEnds {K : Type} [CommRing K] {St₀ J₀ : Type} [DecidableEq J₀] (h : FoNums.Sh)
    (lm jLK : ℕ) (ι : Pl → Option J₀) (rs : Rounds K) (st : St₀) :
    lookOutD h lm jLK ι rs st = lookOutE h lm jLK ι st (endsOf h lm jLK rs) := by
  unfold lookOutD lookOutE
  rw [lookRowsD_ofEnds]

/-- It has nRows h rows, at every rs. -/
theorem lookOutD_rows {K : Type} [CommRing K] {St₀ J₀ : Type} [DecidableEq J₀] (h : FoNums.Sh)
    (lm jLK : ℕ) (ι : Pl → Option J₀) (rs : Rounds K) (st : St₀) :
    (lookOutD h lm jLK ι rs st).2.2.length = nRows h := by
  have e := ends_rows_len h lm jLK rs
  unfold Ends.rows at e
  show (((lookRowsD h lm jLK rs).map (rowMap ι)).map toRow).length = _
  unfold lookRowsD
  simp only [List.length_map, List.length_append, List.length_reverse, List.length_cons,
    List.length_nil] at e ⊢
  omega

/-! ### OutAt at the value -/

/-- A list read backwards as a vector, then as a function on ℕ: the reversed list, 0 beyond. -/
theorem nat_rev_get {K : Type} [Zero K] (l : List K) :
    (Blocks.nat fun i : Fin l.length => l.get i.rev) = fun t => l.reverse.getD t 0 := by
  funext t
  unfold Blocks.nat
  by_cases h : t < l.length
  · rw [dif_pos h, List.getD_eq_getElem _ _ (by simpa using h), List.getElem_reverse]
    show l.get (Fin.rev ⟨t, h⟩) = _
    rw [List.get_eq_getElem]
    simp only [Fin.val_rev]
    have e : l.length - (t + 1) = l.length - 1 - t := by omega
    simp only [e]
  · rw [dif_neg h, List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt h)]

/-- The library's weights at a reversed list are the flat weights at the list. -/
theorem eqN_revList {E : Type} [Field E] (k : ℕ) (l : List E) (hl : l.length = k) (X : ℕ)
    (hX : X < 2 ^ k) :
    Blocks.eqN k 0 (fun t => l.reverse.getD t 0) X = TwV.eqN l X := by
  have h := eqN_list k l.length hl (fun i => l.get i) X hX
  rw [List.ofFn_get] at h
  rw [← nat_rev_get l]
  exact h

/-- **It has OutAt's five clauses**, at every rs. -/
theorem lookOutD_outAt :
  ∀ (E : Type) [Field E] [Fintype E] (St₀ J₀ : Type) [Fintype J₀] [DecidableEq J₀] (h : FoNums.Sh)
    (lm jLK : ℕ) (ι : Pl → Option J₀) (rs : Rounds E) (st : St₀), FoNums.ok h = true →
    OutAt h lm jLK ι rs st (lookOutD h lm jLK ι rs st) := by
  intro E _ _ St₀ J₀ _ _ h lm jLK ι rs st H
  have hlen : (endsOf h lm jLK rs).zx.length + (endsOf h lm jLK rs).zy.length =
      FoNums.v' h + 1 := by
    rw [ends_zx_len h H, ends_zy_len h H, ← ok_v H]
    rfl
  refine ⟨rfl, rfl, ?_, fun _ => rfl, rfl⟩
  intro X hX
  have e : (endsOf h lm jLK rs).zx ++ (endsOf h lm jLK rs).zy =
      ((endsOf h lm jLK rs).zy.reverse ++ (endsOf h lm jLK rs).zx.reverse).reverse := by
    rw [List.reverse_append, List.reverse_reverse, List.reverse_reverse]
  have hl : ((endsOf h lm jLK rs).zy.reverse ++ (endsOf h lm jLK rs).zx.reverse).length =
      FoNums.v' h + 1 := by
    rw [List.length_append, List.length_reverse, List.length_reverse]
    omega
  show Blocks.eqN (FoNums.v' h + 1) 0
    (fun t => ((endsOf h lm jLK rs).zx ++ (endsOf h lm jLK rs).zy).getD t 0) X = _
  rw [e]
  exact eqN_revList _ _ hl X hX

/-- **The typed out-claim at an out-statement with OutAt is the out-claim at lookOutD.** -/
theorem lookOutD_claim :
  ∀ (E : Type) [Field E] [Fintype E] (St₀ J₀ : Type) [Fintype J₀] [DecidableEq J₀] (h : FoNums.Sh),
    FoNums.ok h = true → ∀ (L : Lay E St₀ J₀) (lm jLK : ℕ), 5 ≤ lm → lm ≤ h.kT + 5 →
    ∀ (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀) (rs : Rounds E) (st : St₀)
      (x : TX (St₀ × E) E (Option J₀)), OutAt h lm jLK (placeOf mk pl) rs st x →
    ∀ (KF : ℕ → AffK (Option J₀) E) (μ₀ : J₀ → E),
    KFokAt h (forK E L st) (fun c => (endsOf h lm jLK rs).zk.getD c []) KF (zext μ₀) →
    ((forA E h L).lk.out id id x (zext μ₀) ↔
      (forA E h L).lk.out id id (lookOutD h lm jLK (placeOf mk pl) rs st) (zext μ₀)) := by
  intro E _ _ St₀ J₀ _ _ h H L lm jLK h5 hlm mk pl rs st x hx KF μ₀ hKF
  exact (out_iff_claims h H L lm jLK h5 hlm mk pl rs st x hx KF μ₀ hKF).trans
    (out_iff_claims h H L lm jLK h5 hlm mk pl rs st _
      (lookOutD_outAt E St₀ J₀ h lm jLK (placeOf mk pl) rs st H) KF μ₀ hKF).symm

/-! ### The one equation -/

/-- A vector read backwards, as a function on ℕ: the reversed list of its entries, 0 beyond. -/
theorem nat_rev_ofFn {K : Type} [Zero K] {k : ℕ} (z : Fin k → K) :
    (Blocks.nat fun i : Fin k => z i.rev) = fun t => (List.ofFn z).reverse.getD t 0 := by
  funext t
  unfold Blocks.nat
  by_cases h : t < k
  · rw [dif_pos h, List.getD_eq_getElem _ _ (by simpa using h), List.getElem_reverse,
      List.getElem_ofFn]
    show z (Fin.rev ⟨t, h⟩) = _
    congr 1
    apply Fin.ext
    simp only [Fin.val_rev, List.length_ofFn]
    omega
  · rw [dif_neg h, List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt h)]

section
variable {E : Type} [Field E] [Fintype E] (Ex : ExtSpec)

/-- The point of the keys' claim, as a function on ℕ, off the trace. -/
theorem clK_ptL (A : LkAsmH E) (st : A.St) (o : A.XB) : (A.clK (A.oldT o)).pt =
    fun t => (pntTop (numsA A st).oK [] (traceOf A o).keys.reverse).reverse.getD t 0 := by
  rw [clK_pt, ← clK_pnt A st o]
  exact nat_rev_ofFn _

/-- rd_read's sixth clause: the point itself. -/
theorem rd_pt {P' : Type} (A : LkAsmH E) (st : A.St) (ι : P' → A.J) (N : Nums P' E)
    (hN : PlacesAre A st ι N) (τ : Tr (A.chnK (SK₀ E Ex)).R.shape) :
    (A.rd (chnV (SV₀ E Ex) A st τ)).2.1.pt =
      fun t => (pntTop N.oK [] (traceOfFlat N (flChn Ex A τ)).keys.reverse).reverse.getD t 0 := by
  have ht : traceOf A (chnV (SV₀ E Ex) A st τ) = traceOfFlat N (flChn Ex A τ) :=
    (state_eq Ex A st (fun _ => Sum.inr 0) τ).trans
      (hN.same (fun M => traceOfFlat M (flChn Ex A τ)) fun _ => rfl)
  have h := clK_ptL A st (chnV (SV₀ E Ex) A st τ)
  rw [ht, hN.same (fun M => M.oK) fun _ => rfl] at h
  exact h

end

/-- The two halves of the point, reversed, are the point reversed. -/
theorem drop_take_rev {α : Type} (l : List α) (k : ℕ) :
    (l.drop k).reverse ++ (l.take k).reverse = l.reverse := by
  rw [← List.reverse_append, List.take_append_drop]

/-- **THE ONE EQUATION: the typed block's output is lookOutD at the transcript read as plain
data.** -/
theorem lookOutD_run :
  ∀ (E : Type) [Field E] [Fintype E] (St₀ J₀ : Type) [Fintype J₀] [DecidableEq J₀] (h : FoNums.Sh),
    FoNums.ok h = true → ∀ (L : Lay E St₀ J₀) (lm jLK : ℕ) (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀),
    (∀ s, L.mkS s = mk (jLK + s)) →
    (∀ t c j, c < h.NC →
      L.bc t c j = pl (FoNums.cellRC h lm (t, c, j)).1 (FoNums.cellRC h lm (t, c, j)).2) →
    ∀ (Ex : ExtSpec) (a : St₀ × Ex.Str) (τ : Tr (forB E h L V₀ V₀C (Ex := Ex)).R.shape),
      (forB E h L V₀ V₀C (Ex := Ex)).R.red.out a τ =
        some (lookOutD h lm jLK (placeOf mk pl) (forFl h L Ex τ) a.1, a.2) := by
  intro E _ _ St₀ J₀ _ _ h H L lm jLK mk pl hmk hbc Ex a τ
  obtain ⟨x, h1, h2, h3, -, h5, h6⟩ := hcOut1E E St₀ J₀ h L lm jLK mk pl H hmk hbc Ex a τ
  have h0 := allK₀_out Ex (forA E h L) (forP E h L) (FoNums.several h) a τ
  have hx : x = _ := (Prod.mk.inj (Option.some.inj (h1.symm.trans h0))).1
  have hθ : Fo.thetaOf h (forFl h L Ex τ) = _ :=
    theta_flAll Ex (forA E h L) (forP E h L) (FoNums.several h) h rfl τ
  have hr : Fo.afterShift h (forFl h L Ex τ) = _ :=
    after_flAll Ex (forA E h L) (forP E h L) (FoNums.several h) h rfl τ
  have hpt : x.2.1.pt = fun t => ((endsOf h lm jLK (forFl h L Ex τ)).zx ++
      (endsOf h lm jLK (forFl h L Ex τ)).zy).getD t 0 := by
    have e : (endsOf h lm jLK (forFl h L Ex τ)).zx ++ (endsOf h lm jLK (forFl h L Ex τ)).zy =
        (pntK (forN h lm jLK (forFl h L Ex τ)) (forTrace h lm jLK (forFl h L Ex τ))).reverse :=
      drop_take_rev _ _
    rw [e, hx]
    unfold forTrace forN pntK
    rw [hθ, hr]
    exact rd_pt Ex ((forP E h L).asmH (forA E h L)) _ (placeOf mk pl) _
      (numsOf_forA E h L lm jLK mk pl (ok_parts H).1.1 hmk hbc a.1 _ _) _
  rw [h1]
  obtain ⟨x1, ⟨pt, mf, tg⟩, rows⟩ := x
  simp only at h2 h3 h5 h6 hpt
  have hmf : mf = dense (mapL (placeOf mk pl) (endsOf h lm jLK (forFl h L Ex τ)).cEndF) :=
    funext h5
  subst h2 h3 hpt hmf h6
  rfl

/-- **The two joined: at data that fit, the value is the typed block's output at a transcript that
reads as these data.** -/
theorem lookOutD_fits :
  ∀ (E : Type) [Field E] [Fintype E] [DecidableEq E] (St₀ J₀ : Type) [Fintype J₀] [DecidableEq J₀]
    (h : FoNums.Sh), FoNums.ok h = true →
    ∀ (L : Lay E St₀ J₀) (lm jLK : ℕ) (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀),
    (∀ s, L.mkS s = mk (jLK + s)) →
    (∀ t c j, c < h.NC →
      L.bc t c j = pl (FoNums.cellRC h lm (t, c, j)).1 (FoNums.cellRC h lm (t, c, j)).2) →
    ∀ (Ex : ExtSpec) (rs : Rounds E), lookFitsB h rs = true → ∀ a : St₀ × Ex.Str,
    ∃ τ : Tr (forB E h L V₀ V₀C (Ex := Ex)).R.shape, forFl h L Ex τ = rs ∧
      (forB E h L V₀ V₀C (Ex := Ex)).R.red.out a τ =
        some (lookOutD h lm jLK (placeOf mk pl) rs a.1, a.2) := by
  intro E _ _ _ St₀ J₀ _ _ h H L lm jLK mk pl hmk hbc Ex rs hf a
  obtain ⟨τ, hτ⟩ := lookFitsB_meets E St₀ J₀ h H L Ex rs hf
  refine ⟨τ, hτ, ?_⟩
  rw [← hτ]
  exact lookOutD_run E St₀ J₀ h H L lm jLK mk pl hmk hbc Ex a τ

/-- **What the test's yes is worth**: at data that fit, the written function of the record is the
typed block's output at a transcript that reads as these data. -/
theorem lookEnds_fits :
  ∀ (E : Type) [Field E] [Fintype E] [DecidableEq E] (St₀ J₀ : Type) [Fintype J₀] [DecidableEq J₀]
    (h : FoNums.Sh), FoNums.ok h = true →
    ∀ (L : Lay E St₀ J₀) (lm jLK : ℕ) (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀),
    (∀ s, L.mkS s = mk (jLK + s)) →
    (∀ t c j, c < h.NC →
      L.bc t c j = pl (FoNums.cellRC h lm (t, c, j)).1 (FoNums.cellRC h lm (t, c, j)).2) →
    ∀ (Ex : ExtSpec) (rs : Rounds E), lookFitsB h rs = true → ∀ a : St₀ × Ex.Str,
    ∃ τ : Tr (forB E h L V₀ V₀C (Ex := Ex)).R.shape, forFl h L Ex τ = rs ∧
      (forB E h L V₀ V₀C (Ex := Ex)).R.red.out a τ =
        some (lookOutE h lm jLK (placeOf mk pl) a.1 (endsOf h lm jLK rs), a.2) := by
  intro E _ _ _ St₀ J₀ _ _ h H L lm jLK mk pl hmk hbc Ex rs hf a
  obtain ⟨τ, hτ, ho⟩ := lookOutD_fits E St₀ J₀ h H L lm jLK mk pl hmk hbc Ex rs hf a
  exact ⟨τ, hτ, by rw [ho, lookOutD_ofEnds]⟩

end Fo

/-! ### At the image of a file's written rounds -/

namespace Fo.Peel
open Iop IOR Prob Cb Cb.LdLkp TWhole TwV Tw Cb.Fo Cb.Fo.NumsEq OnBytes OnBytes.Slice OnBytes.Flat
open OnBytes.Model OnBytes.Maker Run

/-- **At the image of a written transcript the typed block puts out lookOutD at the view's rounds
read in the field.** No test of work, no test of fit: Maps.view is total. -/
theorem lookOutD_view {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀] (h : FoNums.Sh)
    (H : FoNums.ok h = true) (L : Lay GE St₀ J₀) (lm jLK : ℕ) (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀)
    (hmk : ∀ s, L.mkS s = mk (jLK + s))
    (hbc : ∀ t c j, c < h.NC →
      L.bc t c j = pl (FoNums.cellRC h lm (t, c, j)).1 (FoNums.cellRC h lm (t, c, j)).2)
    (Ex : ExtSpec) (ds : List RDT) (hM : List.Forall₂ MeetsT ds (specF h))
    (hA : ∀ d ∈ ds, NoAns d.items) (a : St₀ × Ex.Str) (τ : Tr (uLT (ckP .two) ds)) :
    (forB GE h L V₀ V₀C (Ex := Ex)).R.red.out a
        ((mapsT ds _ (specF h) (rkFor h L Ex).R hM.length_eq).view τ) =
      some (lookOutD h lm jLK (placeOf mk pl) ((rvT (ckP .two) ds τ).map (rdRV Reading.gl)) a.1,
        a.2) := by
  rw [lookOutD_run GE St₀ J₀ h H L lm jLK mk pl hmk hbc Ex a _, ← (rkFor h L Ex).read,
    mapsT_read ds _ (specF h) (rkFor h L Ex).R hM τ, ← flWsT_view ds τ hA]

/-- **THE LAW IN A RUN's TERMS**: the typed block's output at the image is the written function of
the record of end values at the view's rounds read in the field. -/
theorem lookEnds_view {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀] (h : FoNums.Sh)
    (H : FoNums.ok h = true) (L : Lay GE St₀ J₀) (lm jLK : ℕ) (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀)
    (hmk : ∀ s, L.mkS s = mk (jLK + s))
    (hbc : ∀ t c j, c < h.NC →
      L.bc t c j = pl (FoNums.cellRC h lm (t, c, j)).1 (FoNums.cellRC h lm (t, c, j)).2)
    (Ex : ExtSpec) (ds : List RDT) (hM : List.Forall₂ MeetsT ds (specF h))
    (hA : ∀ d ∈ ds, NoAns d.items) (a : St₀ × Ex.Str) (τ : Tr (uLT (ckP .two) ds)) :
    (forB GE h L V₀ V₀C (Ex := Ex)).R.red.out a
        ((mapsT ds _ (specF h) (rkFor h L Ex).R hM.length_eq).view τ) =
      some (lookOutE h lm jLK (placeOf mk pl) a.1
        (endsOf h lm jLK ((rvT (ckP .two) ds τ).map (rdRV Reading.gl))), a.2) := by
  rw [lookOutD_view h H L lm jLK mk pl hmk hbc Ex ds hM hA a τ, lookOutD_ofEnds]

/-- **At a view's rounds that meet the spec the test says yes**: under the frame it cannot say
no. -/
theorem lookFitsB_view [DecidableEq GE] (h : FoNums.Sh) (H : FoNums.ok h = true) (ds : List RDT)
    (hM : List.Forall₂ MeetsT ds (specF h)) (hA : ∀ d ∈ ds, NoAns d.items)
    (τ : Tr (uLT (ckP .two) ds)) :
    lookFitsB h ((rvT (ckP .two) ds τ).map (rdRV Reading.gl)) = true := by
  have hf := flWsT_fit ds (specF h) hM τ
  have hv : 1 ≤ h.v := by
    have := ok_v H
    omega
  rw [flWsT_view ds τ hA]
  exact lookFitsB_of h _ ((sizes_of_fit hf).trans (spec_sizes h hv)) (ynz_of_fit hf)

end Fo.Peel

#print axioms Fo.lookFitsB
#print axioms Fo.lookRowsE
#print axioms Fo.lookOutE
#print axioms Fo.lookRowsD
#print axioms Fo.lookOutD
#print axioms Fo.lookOutGl
#print axioms Fo.lookFitsB_yes
#print axioms Fo.lookFitsB_meets
#print axioms Fo.lookRowsD_ofEnds
#print axioms Fo.lookOutD_ofEnds
#print axioms Fo.lookOutD_rows
#print axioms Fo.nat_rev_get
#print axioms Fo.eqN_revList
#print axioms Fo.lookOutD_outAt
#print axioms Fo.lookOutD_claim
#print axioms Fo.nat_rev_ofFn
#print axioms Fo.clK_ptL
#print axioms Fo.rd_pt
#print axioms Fo.drop_take_rev
#print axioms Fo.lookOutD_run
#print axioms Fo.lookOutD_fits
#print axioms Fo.lookEnds_fits
#print axioms Fo.Peel.lookOutD_view
#print axioms Fo.lookFitsB_of
#print axioms Fo.sizes_of_fit
#print axioms Fo.Peel.lookEnds_view
#print axioms Fo.Peel.lookFitsB_view
