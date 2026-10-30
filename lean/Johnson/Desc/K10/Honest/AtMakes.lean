-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K10/Honest/AtMakes.lean: THE CLOSING OF A SEGMENT (K10): THE JOIN WITH ANOTHER
AUTHOR's LAWS ON THE ROWS' MAKES (Johnson/Desc/First/Shape/Rows.lean, FoldMake.lean, Forms.lean,
Ones.lean): THE ONE NAMED PREMISE OF Johnson/Desc/K10/Honest/AtChain.lean (`FormsBehind`) IS PAID
AT LETTERS THAT ARE A FUNCTION OF THE PLACE's k, THE SHAPE IN FRONT AND THE MAKES OF THE
STATEMENT's ROWS. Lemmas on the verifier's own text; no honest side's frame in them; none of the
library's goals.

  `rowBitsS`, `rowBitsS_eq`, `rowBits_begun`   the number of bits that index a row of a message's
                   table, off the statement's shape; it is the same behind the beginning of a test
                   (the library's `begun_rowBits`, called)
  `batchedS`, `batched_eq`   the make of the batched row, off the rows' makes and the statement's
                   shape: that author's `batchS` at `runRowsS`; where the record names its four,
                   the verifier's batching at the closing returns just where it returns, and the
                   make of what is returned is its value, WHATEVER ELEMENT "BAT" DREW
  `forms_behind`   each yes of the decision: `batchedS` yields some M, and the makes of the forms
                   in the single rows behind are M's: the form on the main table with k variables
                   fixed; the kept forms as they are
  `closeGSM`       THE STEP, A FUNCTION OF THE PLACE's PARAMETERS, THE ROWS' MAKES AND THE SHAPE:
                   `closeGS` at these letters
  `close_carriesM` CARRIES, WITH NO PREMISE BUT THE YES: where the seated term says yes from t to
                   t': `closeGSM` at the makes of t's statement's rows and the shape of t yields
                   the shape of t'
  `forms_turn`     the rows' makes behind: those in front, with the frame's group's list of open
                   rows emptied
  `mainBitsS`, `mainBitsS_eq`, `mainBits_behind`   the number of index bits of a message's main
                   table, off the statement's shape; it is the same behind the closing. NEAR TWINS
                   IN THE LIBRARY, not called: `OnBytes.LayLaw.placeBits_of_shape`,
                   `begun_placeBits` (Johnson/Desc/First/Close/Law/BatOwn.lean);
                   `OnBytes.Means.Extends.tableBits` (Johnson/Desc/Means/Keeps.lean, for a message
                   that is there) with `behind_extends`
                   (Johnson/Desc/First/Close/Law/StBehind.lean); at the statement behind the
                   closing, with no premise on the message's number, one reader's search met none
  `closeValsS`, `closeVals_cut`   THE NAMED TEST `closeValsB`, CUT, where the record names its four
                   and "BAT" drew one element: its half on makes (that author's `foldRowFitsS` at
                   `batchedS`'s value), and that author's one test on values at the batched row
                   (`onesG`)
  `close_returnsM` RETURNS ON MAKES: the guard on the shape, the half on makes, THE ROWS THAT GO
                   INTO THE BATCHING IN ORDER (the library's `OrderRow`), the rounds: the seated
                   term says yes

Limits. THE ROWS' MAKES ARE NO COMPONENT OF `ChainSh` (Johnson/Desc/First/Shape/Chain.lean): so this
is a law of one step on the pair (shape, makes), not on the shape. IN RETURNS ONE PREMISE ON VALUES
IS LEFT: that the rows which go into the batching are in order. IT SUFFICES; IT IS NOT WHAT THE
DECISION TESTS: that is `onesG` at the batched row (`closeVals_cut`); a yes does not give the
premise back (by reading, no theorem: it asks terms on mask tables too, which the test
on the batched row never reads). It is shown here of no state. HOW `close_returnsM` PARTS FROM THIS
FOLDER's ELDER RETURNS (`close_yes_all`, Base.lean; `split_of_base`, Split.lean; the Bool
`closeBaseB`, BaseB.lean; `RowFit.batch_returns`, RowFits.lean): there facts on the kind's own state
that name no challenge; here the cut into makes and one premise on values, on all terms and forms of
these rows. No state is evaluated here (members: Johnson/Desc/K10/Honest/AtPairToy.lean). It stands
over other authors' files (Johnson/Desc/First/Shape/, Johnson/Desc/Ground/Shape/,
Johnson/Desc/K13/Honest/).
Nothing on soundness, completeness or hiding of the protocol.

-/
import Johnson.Desc.K10.Honest.AtChain
import Johnson.Desc.First.Shape.FoldMake
import Johnson.Desc.First.Shape.Forms
import Johnson.Desc.First.Shape.Ones

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.YesFree
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.First.Close
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.Ground.Sh (StSh GrpSh stSh grpSh orc_get grp_get layoutS layoutS_eq)

/-- The number of bits that index a row of a message's table, off the statement's shape. -/
def rowBitsS (a : StSh) (o : Nat) (part : OnBytes.Part) : Nat :=
  match a.oracles[o]? with
  | some x => ceilLog2 (x.shape.rows part)
  | none => 0

theorem rowBitsS_eq (St : Statement) : rowBitsS (stSh St) = St.rowBits := by
  funext o part
  unfold rowBitsS Statement.rowBits
  rw [orc_get]
  cases St.oracles[o]? <;> rfl

/-- The library's own law (`OnBytes.Slice.begun_rowBits`, OnBytes/Slice/BlkStLaws.lean), as an
equation of functions. -/
theorem rowBits_begun (St : Statement) (g : Nat) (G : Group) :
    (Slice.begun St g G).rowBits = St.rowBits := by
  funext o part
  exact Slice.begun_rowBits St g G o part

/-- **The make of the batched row**, off the rows' makes and the statement's shape. -/
def batchedS (fm : FormsSh) (a : StSh) (g : Nat) (G : GrpSh) : Option GroupMk :=
  batchS (rowBitsS a) g (layoutS a G) (runRowsS fm g G.members)

/-- **The verifier's batching at the closing, on makes**: whatever element is handed in. -/
theorem batched_eq {s : Rec} {D : BaseData} (hD : baseData s = some D) (x : E) :
    (Own.batch (D.S1 s) s.frame.group ⟨Own.layoutOf s.st D.G, Slice.runRows s.st D.G⟩ x).map
        groupMk =
      batchedS (formsOf s.st) (stSh s.st) s.frame.group (grpSh D.G) := by
  obtain ⟨_, _, _, hG⟩ := baseData_some hD
  rw [batch_mk]
  unfold batchedS
  rw [rowBitsS_eq, layoutS_eq]
  show batchS (Slice.begun s.st s.frame.group D.G).rowBits _ _
    ((Slice.runRows s.st D.G).toList.map rowMk) = _
  rw [rowBits_begun, runRows_mk s.st s.frame.group D.G hG]
  rfl

/-- **EACH YES OF THE DECISION: THE MAKES OF THE FORMS BEHIND ARE THE BATCHED ROW's MAKE's.** -/
theorem forms_behind {Cl : Type} {P : Par} {s s' : Rec} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : ((kind (Cl := Cl)) P).decide s rs gs = .ok s') :
    ∃ D M, baseData s = some D ∧
      batchedS (formsOf s.st) (stSh s.st) s.frame.group (grpSh D.G) = some M ∧
      formSh s'.frame.rows.c = M.c.fixLow P.k ∧
      (s'.frame.rows.kept.toList.map fun k => (k.oracle, formSh k.c)) = M.kept := by
  obtain ⟨D, hD, rB, rE, rR, t, row, sum, eps, gamma, claim, rfl, _, hrow, _, _, hlen, rfl⟩ :=
    yes_left h
  have hb := batched_eq hD (E.ofTriple t)
  rw [hrow] at hb
  have hm := foldOutput_mk (spent (D.S1 s) D.m) (D.F s) row D.m eps gamma claim
  rw [hlen] at hm
  exact ⟨D, groupMk row, hD, hb.symm, congrArg SingleSh.c hm, congrArg SingleSh.kept hm⟩

/-- **THE STEP ON THE PAIR (MAKES, SHAPE).** -/
def closeGSM (Q : Par) (fm : FormsSh) (a : ChainSh) : Option ChainSh :=
  (a.core.st.groups[a.live.frame.group]?).bind fun G =>
    (batchedS fm a.core.st a.live.frame.group G).bind fun M => closeGS Q (M.c.fixLow Q.k) M.kept a

/-- **CARRIES, WITH NO PREMISE BUT THE YES.** -/
theorem close_carriesM {Q : Par} {same : S → S → Bool} {name : String} {a : Place} {t t' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (IM.seatedAs same (K9.closing (Cl := Unit) Q).retype name a).decide t rs gs = .ok t') :
    closeGSM Q (formsOf t.st) (chainSh t) = some (chainSh t') := by
  obtain ⟨r, hr, ht', _⟩ := seated_inner h
  obtain ⟨D, M, hD, hM, hc, hk⟩ := forms_behind hr
  obtain ⟨_, _, _, hG⟩ := baseData_some hD
  have ho : r.owed = none := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hrr⟩ := close_keeps hr
    rw [hrr]
  have hrec : K9.recOf t' = r := by
    rw [ht']
    obtain ⟨ow, fr, st⟩ := r
    obtain rfl : ow = none := ho
    exact recOf_put t _ _
  have hl : (chainSh t).live.frame = frameSh (K9.recOf t).frame := by
    rw [chainSh_live]
    rfl
  have hcs : (chainSh t).core.st = stSh (K9.recOf t).st := rfl
  unfold closeGSM
  rw [hl, hcs]
  show ((stSh (K9.recOf t).st).groups[(K9.recOf t).frame.group]?).bind _ = _
  rw [grp_get, hG]
  show (batchedS (formsOf (K9.recOf t).st) (stSh (K9.recOf t).st) (K9.recOf t).frame.group
    (grpSh D.G)).bind _ = _
  rw [hM]
  exact close_carriesC h ⟨by rw [hrec]; exact hc, by rw [hrec]; exact hk⟩

/-- **THE ROWS' MAKES BEHIND**: those in front, with the frame's group's list of open rows
emptied. From `K10Turns`: so from each yes of the member. -/
theorem forms_turn {t t' : S} (h : K10Turns t t') :
    formsOf t'.st = { formsOf t.st with
      groups := Ground.Sh.modAt (formsOf t.st).groups (K9.recOf t).frame.group fun _ => [] } := by
  obtain ⟨⟨L, Gq, G, m, rows, _, _, _, _, _, _, k6, k7, k8, hrr⟩, ht'⟩ := h
  have e1 : t'.st = spent (Slice.begun (K9.recOf t).st (K9.recOf t).frame.group G) m := by
    have : t'.st = (K9.recOf t').st := rfl
    rw [this, hrr]
  have b := begin_at (s := K9.recOf t) (List.all_eq_true.2 k7) k6
  obtain ⟨_, _, _, _, hf⟩ := beginRun_forms b
  have sp := spend_forms (spend_at (S := Slice.begun (K9.recOf t).st (K9.recOf t).frame.group G)
    (m := m) (List.all_eq_true.2 k8))
  rw [e1]
  exact sp.trans hf

/-! ## RETURNS: the named test on makes -/

/-- The number of all index bits of a message's main table, off the statement's shape. -/
def mainBitsS (a : StSh) (o : Nat) : Nat :=
  rowBitsS a o .main +
    match a.oracles[o]? with
    | some x =>
      if x.shape.rows .main == 0 then 0 else (a.codes.base.getD x.shape.code default).logEll
    | none => 0

theorem mainBitsS_eq (St : Statement) (o : Nat) : mainBitsS (stSh St) o = St.tableBits o .main := by
  unfold mainBitsS Statement.tableBits Statement.placeBits
  rw [rowBitsS_eq, orc_get]
  cases St.oracles[o]? <;> rfl

/-- Codes and shapes ride past the closing: so do these numbers. -/
theorem mainBits_behind (St : Statement) (g : Nat) (G : Group) (m o : Nat) :
    (spent (Slice.begun St g G) m).tableBits o .main = St.tableBits o .main := by
  have e := behind_shape St g G m o
  have hc : (spent (Slice.begun St g G) m).codes = St.codes := behind_codes _ _ _ _
  unfold Statement.tableBits Statement.rowBits Statement.placeBits
  rw [hc]
  cases h1 : (spent (Slice.begun St g G) m).oracles[o]? with
  | none =>
    cases h2 : St.oracles[o]? with
    | none => rfl
    | some y =>
      rw [h1, h2] at e
      cases e
  | some x =>
    cases h2 : St.oracles[o]? with
    | none =>
      rw [h1, h2] at e
      cases e
    | some y =>
      rw [h1, h2] at e
      have e' : x.shape = y.shape := Option.some.inj e
      simp only [e']

/-- **THE HALF OF THE NAMED TEST THAT IS ON MAKES**: the batching's step on makes yields, and what
it yields fits the fold: that author's `foldRowFitsS`. code, maskCode, k, h: as in `closeG`. -/
def closeValsS (fm : FormsSh) (a : StSh) (code maskCode k h g : Nat) (G : GrpSh) : Bool :=
  match batchedS fm a g G with
  | some M =>
    foldRowFitsS (a.codes.base.getD code default).ell (a.codes.mask.getD maskCode default).ell
      (mainBitsS a)
      (ioppFoldShape { code := code, maskCode := maskCode, k := k, h := h } (layoutS a G)) M
  | none => false

/-- **THE NAMED TEST, CUT**: where the record names its four and "BAT" drew one element t:
`closeValsB` says yes just if its half on makes says yes and the batched row at t passes that
author's one test on values (`onesG`). -/
theorem closeVals_cut {s : Rec} {D : BaseData} (hD : baseData s = some D) {rs : List Fmt.RoundView}
    {t : Fmt.Ext} (ht : batDraw rs = [t]) :
    closeValsB s rs = true ↔
      closeValsS (formsOf s.st) (stSh s.st) s.frame.shape.code s.frame.shape.maskCode D.Gq.k D.Gq.h
        s.frame.group (grpSh D.G) = true ∧
      ∃ row, Own.batch (D.S1 s) s.frame.group ⟨Own.layoutOf s.st D.G, Slice.runRows s.st D.G⟩
        (E.ofTriple t) = some row ∧ onesG row = true := by
  have hb := batched_eq hD (E.ofTriple t)
  unfold closeValsB closeValsS
  rw [hD, ht, ← hb]
  show (match Own.batch (D.S1 s) s.frame.group ⟨Own.layoutOf s.st D.G, Slice.runRows s.st D.G⟩
      (E.ofTriple t) with
    | some row => Own.foldRowFits (spent (D.S1 s) D.m) (D.F s) row
    | none => false) = true ↔ _
  cases hr : Own.batch (D.S1 s) s.frame.group ⟨Own.layoutOf s.st D.G, Slice.runRows s.st D.G⟩
      (E.ofTriple t) with
  | none => exact ⟨fun h => (nomatch h), fun h => (nomatch h.1)⟩
  | some row =>
    show Own.foldRowFits (spent (D.S1 s) D.m) (D.F s) row = true ↔ _
    rw [foldRowFits_split]
    have hc : (spent (D.S1 s) D.m).codes = s.st.codes := behind_codes _ _ _ _
    have htb : (fun o => (spent (D.S1 s) D.m).tableBits o .main) = mainBitsS (stSh s.st) := by
      funext o
      rw [mainBitsS_eq]
      exact mainBits_behind _ _ _ _ _
    rw [hc, htb, Bool.and_eq_true, layoutS_eq]
    exact ⟨fun h => ⟨h.1, row, rfl, h.2⟩,
      fun ⟨h1, r', e, h2⟩ => ⟨h1, by rw [Option.some.inj e]; exact h2⟩⟩

/-- **RETURNS ON MAKES**: where the guard on the shape says yes, the half of the named test on
makes says yes, THE ROWS THAT GO INTO THE BATCHING ARE IN ORDER (the library's `OrderRow`,
OnBytes/Slice/BlkProxOrder.lean: the one premise on values that is left), and the rounds are 2 + k
of the kind's shape: the seated term says yes. -/
theorem close_returnsM {Q : Par} {name : String} {a : Place} {t : S} {D : BaseData}
    (hD : baseData (K9.recOf t) = some D) (hG : closeGB Q (chainSh t) = true)
    (hV : closeValsS (formsOf t.st) (stSh t.st) (K9.recOf t).frame.shape.code
      (K9.recOf t).frame.shape.maskCode D.Gq.k D.Gq.h (K9.recOf t).frame.group (grpSh D.G) = true)
    (hO : ∀ r ∈ (Slice.runRows t.st D.G).toList, OnBytes.Slice.ProxRun.OrderRow r)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (hl : rs.length = 2 + Q.k)
    (hs : ShapedAll rs) :
    ∃ t', (IM.seatedAs ProofFile.sameReply (K9.closing (Cl := Unit) Q).retype name a).decide t rs gs =
      .ok t' := by
  obtain ⟨x, hx⟩ : ∃ x, batDraw rs = [x] := by
    match rs, hs with
    | rB :: _ :: _, ⟨⟨_, ⟨x, hx⟩, _⟩, _⟩ => exact ⟨x, by simp [batDraw, hx]⟩
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hG
  refine close_returnsC hy rs gs hl hs ((closeVals_cut hD hx).2 ⟨hV, ?_⟩)
  have hb := batched_eq hD (E.ofTriple x)
  unfold closeValsS at hV
  cases hr : Own.batch (D.S1 (K9.recOf t)) (K9.recOf t).frame.group
      ⟨Own.layoutOf (K9.recOf t).st D.G, Slice.runRows (K9.recOf t).st D.G⟩ (E.ofTriple x) with
  | none =>
    rw [hr] at hb
    have hb' : batchedS (formsOf t.st) (stSh t.st) (K9.recOf t).frame.group (grpSh D.G) = none :=
      hb.symm
    rw [hb'] at hV
    cases hV
  | some row => exact ⟨row, rfl, batch_ones hO hr⟩

end ProofFile.Honest.K10.YesFree

#print axioms ProofFile.Honest.K10.YesFree.closeVals_cut
#print axioms ProofFile.Honest.K10.YesFree.close_returnsM
#print axioms ProofFile.Honest.K10.YesFree.forms_turn
#print axioms ProofFile.Honest.K10.YesFree.batched_eq
#print axioms ProofFile.Honest.K10.YesFree.forms_behind
#print axioms ProofFile.Honest.K10.YesFree.close_carriesM
