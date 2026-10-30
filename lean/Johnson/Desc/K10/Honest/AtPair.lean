-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K10/Honest/AtPair.lean: THE CLOSING OF A SEGMENT (K10): ONE STEP ON THE PAIR OF THE
FIRST CHAIN's SHAPE AND THE MAKES OF ITS STATEMENT's ROWS (`ChainF`,
Johnson/Desc/First/Shape/ChainF.lean: another author's), WITH BOTH LAWS AT THE VERY BLOCK THAT THE
DESCRIPTION SEATS. Lemmas on the verifier's own text; no honest side's frame in them; none of the
library's goals.

  `closeValsF`, `valsF_eq`   the half of the named test `closeValsB` that is on makes
                   (`closeValsS`, AtMakes.lean), as a Bool on the pair
  `closeGF`        THE STEP: a function of the place's parameters and the pair alone. ITS GUARD
                   HOLDS WHAT THE DECISION TESTS ON SHAPE AND MAKES: `closeValsF`, and
                   `closeGSM`'s own (AtMakes.lean): by five laws together, at the seat's test
                   `ProofFile.sameReply` (`seated_yes_iff`, SeatYes.lean; `closeGB_eq`, AtChain.lean;
                   `closeVals_cut`, AtMakes.lean; `valsF_eq`; `closeGF_isSome`), what a yes asks
                   beyond the guard is the rounds' number and shape, and `onesG` of the batched
                   row; as one sentence that is stated nowhere in this folder. Its value:
                   `closeGSM`'s on the shape; beside it the makes with the live frame's group's
                   list of open rows emptied (`formsBehindF`)
  `closeGF_isSome` it yields just where `closeValsF` and the guard on the shape (`closeGB`,
                   AtChain.lean) say yes
  `forms_turnF`    the makes behind as a function of the shape and the makes in front: in that
                   author's form (`pair_carries`' premise)
  `close_carriesF` CARRIES, WITH NO PREMISE BUT THE YES: where the seated term says yes from t to
                   t': `closeGF Q (chainF t) = some (chainF t')`
  `rowOrderB`, `closeOrdB`, `rowOrder_of`   A TEST WITH CODE ON THE STATE: every tensor among the
                   terms and the forms of each row that goes into the batching passes the
                   library's `Tensor.ok` (of whose four clauses three are on makes and one on
                   values); it gives the library's `OrderRow`, and asks more
    `live_frame`, `yields_gives`, `ord_gives`   three steps on the way
  `closeVals_of`   where the step on the pair yields, `closeOrdB` says yes and "BAT" drew one
                   element: the named test `closeValsB` says yes; no file of this folder calls it
  `close_returnsF` RETURNS: where the step on the pair yields, `closeOrdB` says yes and the rounds
                   are 2 + k of the kind's shape: the seated term says yes
  `closing_atF`    under the library's one head (`P5J.AtMgA`), at each l < 25, at the member's
                   number in the chain's flat list (the library's `LPFK10.ixK10 l`; written out:
                   `number_is`, KeepsSeat.lean): which block it is; what its step asks of the
                   rounds; CARRIES from its decision and from its step; RETURNS

Limits. `closeOrdB` SUFFICES; IT IS NOT WHAT THE DECISION TESTS (AtMakes.lean's Limits): RETURNS
goes one way. WHO PAYS IT: THAT `closeOrdB` SAYS YES AT THE STANDS OF A THREAD IS THIS KIND's
AUTHORS' DEBT (the other authors' "values": `Values`, in the file Thread/Shape.lean named below). It
is shown of no state here.

WHAT IT WOULD BE DRAWN FROM: a fact that rides on the state, "every open row and every sample row
passes `rowOrderB`", laid by each routine that lays a row and kept by the others. AS A WHOLE two
readers' searches of the library met it nowhere. ITS HALF ON FORMS IS IN THE LIBRARY, not called
here: `OnBytes.Means.InOrder` (Johnson/Desc/Means/Order.lean), a fact on the statement, with a law
at the start (`InOrder.start`) and one for each of six effects (`InOrder.withGroup`, `stSent`,
`admitted`, `withMessageInGroup`, `withRow`, `begun`; some under premises of their own); past the closing:
`behind_inOrder` (Johnson/Desc/First/Close/Law/StBehind.lean). By `InOrder.runRows` every row that
goes into the batching then has `RowIn` (Johnson/Desc/Means/Says.lean), whose clause on forms asks
`Form.fits`, which asks `Tensor.ok` of each tensor. THE HALF ON TERMS IS OWED: of a term `RowIn`
asks the place alone. The like as a Bool that is carried: another author's `stTidyB` with
`beginRun_rows_in` (Johnson/Desc/Ground/Shape/Marks.lean, which a tree may lack); and, where no
tensor has a written-out factor, its `stPlainB` with `beginRun_rows_plain`, from which the library's
`orderRow_of_plain` (OnBytes/Slice/BlkProxOrder.lean) gives `OrderRow`, terms and forms, of the rows
that the beginning of a test hands on: what `close_returnsM` (AtMakes.lean) asks of the rows that go
into the batching, not `closeOrdB`; the two lists are one by `begin_at` (Split.lean; under the
ground's clauses for the beginning); no theorem of this folder joins that road to `close_returnsM`.
That `InOrder` holds at a stand in front of a closing is not shown here. For a group's OPEN rows the
description's own ground runs `rowOrderB`'s tests, on terms and on forms, where a row is laid
(`rowL`, Johnson/Desc/First/Base/Ground.lean, with the library's `Own.tensorInOrder_agrees`,
Johnson/Desc/Own/ShapesAgree.lean: one reader's reading): one law there would serve all kinds; the
messages' SAMPLE rows are tested by no routine that the reader met.

THE STEP READS THE MAKES, and the shape behind (the single rows' two fields on forms) hangs on them:
so it is not of that author's form `pairF`, whose step on the shape is handed no make.

NEITHER LAW IS TYPED IN THE OTHER AUTHORS' OWN DEFINITIONS OF "carries" AND "returns"
(Johnson/Desc/ProofFile/Honest/Thread/Shape.lean, which stands over an honest side's frame and which
a tree may lack): there the step yields a refusal with words, here an Option; "returns" asks the
decision at the rounds without their digest (`shapedAll_noDigest`, Step.lean); the place's
parameters stand under "there is" with the two equations that lay them; the shape's reader must be
`chainF`.

`closing_atF` has no member here. THE HEAD IS MET, UNDER FOUR PREMISES ON THE THREE PUBLIC FILES (in
scope; `readFiles` returns; `protocolDataWellFormed` says yes; `At.CondsOwed`), by the library's
`P5J.head_exists_at_name` (Johnson/P5J/HeadExistsAtName.lean); that these four hold at any public
files is not shown here. No state is evaluated here. AT `OnBytes.secondHashFunction` ALONE, IN SCOPE
(`closing_atF`).

It stands over other authors' files (Johnson/Desc/First/Shape/, Johnson/Desc/Ground/Shape/,
Johnson/Desc/K13/Honest/).
Nothing on soundness, completeness or hiding of the protocol.

-/
import Johnson.Desc.K10.Honest.AtMakes
import Johnson.Desc.First.Shape.ChainF

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.YesFree
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.First.Close
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.Ground.Sh (stSh grpSh grp_get)

theorem live_frame (t : S) : (chainSh t).live.frame = frameSh (K9.recOf t).frame := by
  rw [chainSh_live]
  rfl

/-- **The half of the named test that is on makes, as a Bool on the pair.** -/
def closeValsF (x : ChainF) : Bool :=
  match x.1.live.frame.groups[x.1.live.frame.link]?, x.1.core.st.groups[x.1.live.frame.group]? with
  | some Gq, some G =>
    closeValsS x.2 x.1.core.st x.1.live.frame.shape.code x.1.live.frame.shape.maskCode Gq.k Gq.h
      x.1.live.frame.group G
  | _, _ => false

/-- At the pair of a state whose record names its four. -/
theorem valsF_eq {t : S} {D : BaseData} (hD : baseData (K9.recOf t) = some D) :
    closeValsF (chainF t) =
      closeValsS (formsOf t.st) (stSh t.st) (K9.recOf t).frame.shape.code
        (K9.recOf t).frame.shape.maskCode D.Gq.k D.Gq.h (K9.recOf t).frame.group (grpSh D.G) := by
  obtain ⟨_, h2, _, h4⟩ := baseData_some hD
  unfold closeValsF chainF
  have hcs : (chainSh t).core.st = stSh (K9.recOf t).st := rfl
  simp only [live_frame, hcs]
  have e2 : (frameSh (K9.recOf t).frame).groups[(frameSh (K9.recOf t).frame).link]? =
      some D.Gq := h2
  have e4 : (stSh (K9.recOf t).st).groups[(frameSh (K9.recOf t).frame).group]? =
      some (grpSh D.G) := by
    show (stSh (K9.recOf t).st).groups[(K9.recOf t).frame.group]? = _
    rw [grp_get, h4]
    rfl
  rw [e2, e4]
  rfl

/-- The makes behind, off the shape and the makes in front. -/
def formsBehindF (a : ChainSh) (fm : FormsSh) : FormsSh :=
  { fm with groups := Ground.Sh.modAt fm.groups a.live.frame.group fun _ => [] }

/-- **THE STEP ON THE PAIR.** -/
def closeGF (Q : Par) (x : ChainF) : Option ChainF :=
  if closeValsF x then (closeGSM Q x.2 x.1).map (·, formsBehindF x.1 x.2) else none

/-- **It yields just where the two guards say yes.** -/
theorem closeGF_isSome (Q : Par) (x : ChainF) :
    (closeGF Q x).isSome = (closeValsF x && closeGB Q x.1) := by
  unfold closeGF
  cases hv : closeValsF x with
  | false => rfl
  | true =>
    rw [if_pos rfl, Option.isSome_map, Bool.true_and]
    unfold closeValsF at hv
    unfold closeGSM
    split at hv
    · rename_i Gq G _ e4
      rw [e4]
      show ((batchedS x.2 x.1.core.st x.1.live.frame.group G).bind _).isSome = _
      unfold closeValsS at hv
      cases hb : batchedS x.2 x.1.core.st x.1.live.frame.group G with
      | none =>
        rw [hb] at hv
        cases hv
      | some M => exact closeGS_isSome Q _ _ x.1
    · cases hv

/-- **The makes behind, in the other author's form.** -/
theorem forms_turnF {t t' : S} (h : K10Turns t t') :
    formsOf t'.st = formsBehindF (chainSh t) (formsOf t.st) := by
  unfold formsBehindF
  rw [forms_turn h, live_frame]
  rfl

/-- **CARRIES, WITH NO PREMISE BUT THE YES.** -/
theorem close_carriesF {Q : Par} {same : S → S → Bool} {name : String} {a : Place} {t t' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (IM.seatedAs same (K9.closing (Cl := Unit) Q).retype name a).decide t rs gs = .ok t') :
    closeGF Q (chainF t) = some (chainF t') := by
  obtain ⟨r, hr, _, _⟩ := seated_inner h
  obtain ⟨_, hs, h1, h2⟩ := (close_yes_split (Cl := Unit) Q (K9.recOf t) rs gs).1 ⟨r, hr⟩
  obtain ⟨D, hD⟩ : ∃ D, baseData (K9.recOf t) = some D := by
    unfold closeShapeB at h1
    cases hD : baseData (K9.recOf t) with
    | none =>
      rw [hD] at h1
      cases h1
    | some D => exact ⟨D, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, batDraw rs = [x] := by
    match rs, hs with
    | rB :: _ :: _, ⟨⟨_, ⟨x, hx⟩, _⟩, _⟩ => exact ⟨x, by simp [batDraw, hx]⟩
  have hv : closeValsF (chainF t) = true := by
    rw [valsF_eq hD]
    exact ((closeVals_cut hD hx).1 h2).1
  unfold closeGF
  rw [if_pos hv]
  show (closeGSM Q (formsOf t.st) (chainSh t)).map _ = _
  rw [close_carriesM h]
  show some (chainSh t', _) = some (chainSh t', formsOf t'.st)
  rw [forms_turnF (seated_keeps _ _ _ h).1]
  rfl

/-! ## RETURNS -/

/-- Every tensor among a row's terms and forms passes the library's test. -/
def rowOrderB (r : OnBytes.Row) : Bool :=
  (r.terms.toList.all fun t => t.v.ok) && r.forms.toList.all fun f => f.c.tensors.all (·.ok)

theorem rowOrder_of {r : OnBytes.Row} (h : rowOrderB r = true) :
    OnBytes.Slice.ProxRun.OrderRow r := by
  unfold rowOrderB at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  exact ⟨fun t ht => Tensor.inOrder_of_ok _ (h.1 t ht),
    fun f hf v hv => Tensor.inOrder_of_ok _ (List.all_eq_true.1 (h.2 f hf) v hv)⟩

/-- **A TEST WITH CODE ON THE STATE**: each row that goes into the batching at the live frame's
group. Where there is no such group it says yes for nothing: it is spent behind a yield of the
step alone, where the group is there. -/
def closeOrdB (t : S) : Bool :=
  match t.st.groups[(K9.recOf t).frame.group]? with
  | some G => (Slice.runRows t.st G).toList.all rowOrderB
  | none => true

/-- What a yield of the step gives at a state. -/
theorem yields_gives {Q : Par} {t : S} {y : ChainF} (hy : closeGF Q (chainF t) = some y) :
    closeGB Q (chainSh t) = true ∧ ∃ D, baseData (K9.recOf t) = some D ∧
      closeValsS (formsOf t.st) (stSh t.st) (K9.recOf t).frame.shape.code
        (K9.recOf t).frame.shape.maskCode D.Gq.k D.Gq.h (K9.recOf t).frame.group (grpSh D.G) =
          true := by
  have h := closeGF_isSome Q (chainF t)
  rw [hy, Option.isSome_some] at h
  have h' := h.symm
  rw [Bool.and_eq_true] at h'
  obtain ⟨hv, hG⟩ := h'
  have hg := hG
  change closeGB Q (chainSh t) = true at hg
  rw [closeGB_eq, Bool.and_eq_true] at hg
  obtain ⟨D, hD⟩ : ∃ D, baseData (K9.recOf t) = some D := by
    have := hg.2
    unfold closeShapeB at this
    cases hD : baseData (K9.recOf t) with
    | none =>
      rw [hD] at this
      cases this
    | some D => exact ⟨D, rfl⟩
  exact ⟨hG, D, hD, by rw [← valsF_eq hD]; exact hv⟩

theorem ord_gives {t : S} {D : BaseData} (hD : baseData (K9.recOf t) = some D)
    (hO : closeOrdB t = true) :
    ∀ r ∈ (Slice.runRows t.st D.G).toList, OnBytes.Slice.ProxRun.OrderRow r := by
  obtain ⟨_, _, _, h4⟩ := baseData_some hD
  unfold closeOrdB at hO
  have h4' : t.st.groups[(K9.recOf t).frame.group]? = some D.G := h4
  rw [h4'] at hO
  exact fun r hr => rowOrder_of (List.all_eq_true.1 hO r hr)

/-- **THE NAMED TEST, FROM THE STEP's YIELD AND THE TEST ON VALUES.** -/
theorem closeVals_of {Q : Par} {t : S} {y : ChainF} (hy : closeGF Q (chainF t) = some y)
    (hO : closeOrdB t = true) {rs : List Fmt.RoundView} {x : Fmt.Ext} (hx : batDraw rs = [x]) :
    closeValsB (K9.recOf t) rs = true := by
  obtain ⟨_, D, hD, hV⟩ := yields_gives hy
  refine (closeVals_cut hD hx).2 ⟨hV, ?_⟩
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
  | some row => exact ⟨row, rfl, batch_ones (ord_gives hD hO) hr⟩

/-- **RETURNS.** -/
theorem close_returnsF {Q : Par} {name : String} {a : Place} {t : S} {y : ChainF}
    (hy : closeGF Q (chainF t) = some y) (hO : closeOrdB t = true)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (hl : rs.length = 2 + Q.k)
    (hs : ShapedAll rs) :
    ∃ t', (IM.seatedAs ProofFile.sameReply (K9.closing (Cl := Unit) Q).retype name a).decide t rs gs =
      .ok t' := by
  obtain ⟨hG, D, hD, hV⟩ := yields_gives hy
  exact close_returnsM hD hG hV (ord_gives hD hO) rs gs hl hs

/-- **AT THE MEMBER, UNDER THE LIBRARY's ONE HEAD, AT EACH LINK.** -/
theorem closing_atF {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    {x : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    ∃ (p : K9.Where) (Q : Par) (b : Block P5J.TS ProofFile.Cl),
      IM.k9At Zp l = some p ∧ ProofFile.k10Par Zp (ProofFile.k9Stretches Zp) p = some Q ∧
      cF.blocksInOrder[LPFK10.ixK10 l]? = some b ∧
      b = IM.seatedAs ProofFile.sameReply (K9.closing (Cl := Unit) Q).retype b.name
        (IM.cAt l (IM.subAt l) 1 .K10) ∧
      (∀ ft rs cols, b.Fits ft rs cols ↔ rs.length = 2 + Q.k ∧ ShapedAll rs) ∧
      (∀ t t' rs gs, b.decide t rs gs = .ok t' → closeGF Q (chainF t) = some (chainF t')) ∧
      (∀ ft t t' rs cols n, b.step ft t rs cols = .ok (t', n) →
        closeGF Q (chainF t) = some (chainF t')) ∧
      ∀ t y rs gs, closeGF Q (chainF t) = some y → closeOrdB t = true →
        rs.length = 2 + Q.k → ShapedAll rs → ∃ t', b.decide t rs gs = .ok t' := by
  obtain ⟨p, Q, b, hp, hQ, hn, hb, hf, _, _⟩ := closingBlock_at h l hl
  have hc : ∀ t t' rs gs, b.decide t rs gs = .ok t' → closeGF Q (chainF t) = some (chainF t') := by
    intro t t' rs gs hd
    rw [hb] at hd
    exact close_carriesF hd
  refine ⟨p, Q, b, hp, hQ, by rw [number_is]; exact hn, hb, hf, hc,
    fun ft t t' rs cols n hst => hc _ _ _ _ ((step_iff ft b t t' rs cols n).1 hst).2.1,
    fun t y rs gs hy hO h1 h2 => ?_⟩
  rw [hb]
  exact close_returnsF hy hO rs gs h1 h2

end ProofFile.Honest.K10.YesFree

#print axioms ProofFile.Honest.K10.YesFree.closeGF_isSome
#print axioms ProofFile.Honest.K10.YesFree.forms_turnF
#print axioms ProofFile.Honest.K10.YesFree.close_carriesF
#print axioms ProofFile.Honest.K10.YesFree.closeVals_of
#print axioms ProofFile.Honest.K10.YesFree.close_returnsF
#print axioms ProofFile.Honest.K10.YesFree.closing_atF
