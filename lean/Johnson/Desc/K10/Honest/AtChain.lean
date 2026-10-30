-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K10/Honest/AtChain.lean: THE CLOSING OF A SEGMENT (K10): A STEP ON THE SHAPE OF THE
FIRST CHAIN's STATE (`ChainSh`, Johnson/Desc/First/Shape/Chain.lean: another author's) AND TWO
LETTERS, WITH TWO LAWS AT THE VERY BLOCK THAT THE DESCRIPTION SEATS, AT EACH LINK l < 25. IT IS NO
LAW OF ONE STEP ON THE SHAPE UNTIL THE ONE NAMED PREMISE IS PAID AT LETTERS THAT ARE A FUNCTION OF
THE SHAPE IN FRONT (paid, on the pair of the shape and the rows' makes: AtMakes.lean, AtPair.lean).
Lemmas on the verifier's own text; no honest side's frame in them; none of the library's goals.

  `putLiveS`, `chainSh_putLive`   the state's own writing of the live copy of the calls' state,
                   seen through the shape
  `chainSh_putRec`   the chain's laying back of the kind's record (`K9.putRec`) turns, of the
                   shape's components, three: core (its statement), rowsOwed, and ONE OF
                   link | check by case (there the frame of the calls' state)
  `owedS` (`owedS_eq`), `frameBehindS`, `singleS`   the rows owed; the frame behind; the shape of
                   the single rows behind, off the shape in front AND TWO LETTERS: c, the make of
                   the form on the main table; kept, the kept forms in order, each with its oracle
                   message's number and its make
  `closeGS`          THE STEP AT THE SEAT, a function of the place's parameters, the two letters
                   and the shape: no mark; nothing owed; the live frame names the link's shape,
                   the link's group and a mask, and the core's statement has the frame's group;
                   the closing is due; `closeS` (OnShape.lean) yields at the core's statement:
                   then the three components are turned. `closeGS_at`: the same in a state's own
                   letters, where the state has no mark and its record names these four
  `closeGB`          THE GUARD, FREE OF THE TWO LETTERS; `closeGS_isSome`: the step yields just
                   where it says yes; `closeGB_eq` (with `closeGB_none`): at the shape of a state
                   it is: no mark, and the first test of Split.lean at the state's record
  `FormsBehind`      THE ONE NAMED PREMISE: c and kept are the makes of the forms in the single
                   rows of the state behind
    `seated_inner`, `singleSh_of_make`   two steps on the way. THE FIRST HAS A TWIN IN THE LIBRARY,
                   at an address that is not of the kind K7: `LPFK10.seated_yes` with
                   `seated_unmarked` (Johnson/LPFK10R/Sits.lean, SitsAll.lean): not called
  `close_carriesC`   CARRIES: where the seated term (at any test on the seat) says yes from t to
                   t', and `FormsBehind t' c kept`: `closeGS` at the shape of t yields the shape
                   of t'
  `close_returnsC`   RETURNS: where `closeGS` yields at the shape of t, at any c and kept, the
                   rounds are 2 + k of the kind's shape, and THE NAMED TEST `closeValsB` says yes:
                   the seated term, at the seat's own test `ProofFile.sameReply`, says yes
  `closingBlock_at`       under the library's one head (`P5J.AtMgA`), at each l < 25, at the member's
                   number in the chain's flat list: the member b is the seated term; what `b.Fits`
                   is (for the rounds without their digest: `shapedAll_noDigest`, Step.lean);
                   CARRIES, STILL UNDER `FormsBehind`; RETURNS, from the guard

Limits. WHAT A CALLER GAINS BY CARRIES, AND WHAT NOT: all of the shape behind BUT TWO FIELDS, c and
kept, of the live frame's single rows is a written function of the place's parameters and the shape
in front; of these two NOTHING is said: any caller meets `FormsBehind` by reading c and kept off the
state behind. THE PREMISE IS PAID IN AtMakes.lean (`forms_behind`, `close_carriesM`; the emptied
open rows: `forms_turn`) AND AtPair.lean (`close_carriesF`): as a law on the pair of the shape and
the rows' makes, not on the shape alone. `closeValsB` reads the rows' summands and what "BAT" drew:
no function of the shape. The step yields an Option, not a refusal with words. That the other
components stay is by reduction of that author's setters, stated by no lemma; `closeS_ground`
(OnShape.lean) is not lifted to `closeGS`. AT `OnBytes.secondHashFunction` ALONE, IN SCOPE (`closingBlock_at`).
Members of the step and of the two laws at the seated term: Johnson/Desc/K10/Honest/AtChainToy.lean;
`closeGB_none` and `closingBlock_at` have none; that the head can be met, under four premises:
`P5J.head_exists_at_name` (Johnson/P5J/HeadExistsAtName.lean). It stands over other authors' files
(Johnson/Desc/First/Shape/, Johnson/Desc/Ground/Shape/, Johnson/Desc/K13/Honest/).
Nothing on soundness, completeness
or hiding of the protocol.

-/
import Johnson.Desc.K10.Honest.Rows
import Johnson.Desc.K10.Honest.SeatYes
import Johnson.Desc.First.Shape.Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.YesFree
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.First.Close
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.Ground.Sh (StSh CoreSh stSh coreSh)

/-- The writing of the live copy of the calls' state, on the shape: the open link's own, else the
walk's. -/
def putLiveS (a : ChainSh) (c : CheckSh) : ChainSh :=
  match a.link with
  | some L => a.setLink { L with check := c }
  | none => a.setCheck c

theorem chainSh_putLive (s : S) (c : ChainCheck) :
    chainSh (s.putLive c) = putLiveS (chainSh s) (checkSh c) := by
  unfold S.putLive putLiveS
  show _ = (match s.link?.map linkSh with
    | some L => (chainSh s).setLink { L with check := checkSh c }
    | none => (chainSh s).setCheck (checkSh c))
  cases s.link? with
  | none => exact chainSh_check s c
  | some L => exact chainSh_putLink s _

/-- **The laying back of the kind's record, seen through the shape.** -/
theorem chainSh_putRec (t : S) (r : Rec) :
    chainSh (K9.putRec t r) =
      ((putLiveS (chainSh t) { (chainSh t).live with frame := frameSh r.frame }).setCore
        { (chainSh t).core with st := stSh r.st }).setRowsOwed r.owed := by
  have e : K9.putRec t r =
      { (t.putLive { t.live with frame := r.frame }) with st := r.st, rowsOwed := r.owed } := rfl
  obtain ⟨k1, k2, _⟩ := putLive_keeps t { t.live with frame := r.frame }
  have e2 : chainSh { (t.putLive { t.live with frame := r.frame }) with
      st := r.st, rowsOwed := r.owed } =
      ((chainSh (t.putLive { t.live with frame := r.frame })).setCore
        (coreSh ⟨r.st, (t.putLive { t.live with frame := r.frame }).book,
          (t.putLive { t.live with frame := r.frame }).roots⟩)).setRowsOwed r.owed := rfl
  rw [e, e2, k1, k2, chainSh_putLive, chainSh_live]
  rfl

/-- The rows that are still owed a count, off the shape; "some 0" is "none" (`K9.owedOf`). -/
def owedS (a : ChainSh) : Option Nat :=
  match a.rowsOwed with
  | some 0 => none
  | x => x

theorem owedS_eq (t : S) : owedS (chainSh t) = K9.owedOf t := rfl

/-- **The shape of the single rows behind**, off the shape in front and two letters: c, kept. -/
def singleS (Q : Par) (code maskCode k h m : Nat) (a : StSh) (G : Ground.Sh.GrpSh) (c : FormSh)
    (kept : List (Nat × FormSh)) : SingleSh :=
  let Ly := (ioppFoldShape { code := code, maskCode := maskCode, k := k, h := h }
    (Ground.Sh.layoutS a G)).layout
  { code := code, maskCode := maskCode, layout := Ly, gamma := Q.k, masks := 2, fresh := m, c := c
    kept := kept
    d := [(a.codes.mask.getD maskCode default).ell, (a.codes.mask.getD maskCode default).ell]
    keptRows := keptRowsS a Ly }

/-- The frame's shape behind. -/
def frameBehindS (f : FrameSh) (R : SingleSh) : FrameSh :=
  { f with rows := R, mask := none, link := f.link + 1, next := .first }

/-- **THE STEP AT THE SEAT.** -/
def closeGS (Q : Par) (c : FormSh) (kept : List (Nat × FormSh)) (a : ChainSh) : Option ChainSh :=
  if a.marked then none
  else
    match a.live.frame.shape.link[a.live.frame.link]?, a.live.frame.groups[a.live.frame.link]?,
        a.live.frame.mask, a.core.st.groups[a.live.frame.group]? with
    | some L, some Gq, some m, some G =>
      if (owedS a).isNone && decide (a.live.frame.next = .laterOrClose) &&
          a.live.frame.moment == reqMoments L then
        (closeS Q a.live.frame.shape.code a.live.frame.shape.maskCode Gq.k Gq.h a.live.frame.group m
          a.core.st).map fun y =>
          ((putLiveS a { a.live with
            frame := (frameBehindS a.live.frame (singleS Q a.live.frame.shape.code
              a.live.frame.shape.maskCode Gq.k Gq.h m a.core.st G c kept)) }).setCore
            { a.core with st := y }).setRowsOwed none
      else none
    | _, _, _, _ => none

/-- **THE ONE NAMED PREMISE**: c and kept are the makes of the forms in the single rows of the
state t': of the form on the main table; and of the kept forms, in order, each with its oracle
message's number. TWO EQUATIONS, WHICH ANY CALLER MEETS BY TAKING c AND kept OFF t'. What is
really owed is more; it is paid on the pair of the shape and the rows' makes: AtMakes.lean. -/
def FormsBehind (t' : S) (c : FormSh) (kept : List (Nat × FormSh)) : Prop :=
  formSh (K9.recOf t').frame.rows.c = c ∧
    ((K9.recOf t').frame.rows.kept.toList.map fun k => (k.oracle, formSh k.c)) = kept

/-- **THE GUARD, FREE OF THE TWO LETTERS.** -/
def closeGB (Q : Par) (a : ChainSh) : Bool := (closeGS Q ⟨[], []⟩ [] a).isSome

/-- Whether the step yields hangs on neither letter. -/
theorem closeGS_isSome (Q : Par) (c : FormSh) (kept : List (Nat × FormSh)) (a : ChainSh) :
    (closeGS Q c kept a).isSome = closeGB Q a := by
  unfold closeGB closeGS
  split
  · rfl
  · split
    · split
      · rw [Option.isSome_map, Option.isSome_map]
      · rfl
    · rfl

/-- A yes of the seated term gives, inside: a yes of the kind's own decision at the record, laid
back; and no mark in front. -/
theorem seated_inner {Q : Par} {same : S → S → Bool} {name : String} {a : Place} {t t' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (IM.seatedAs same (K9.closing (Cl := Unit) Q).retype name a).decide t rs gs = .ok t') :
    ∃ r, ((kind (Cl := Unit)) Q).decide (K9.recOf t) rs gs = .ok r ∧ t' = K9.putRec t r ∧
      t.failed = none := by
  have hk := seated_keeps _ _ _ h
  have key : ∀ u, (IM.marked (K9.closing (Cl := Unit) Q).retype name).decide t rs gs = .ok u →
      (K9.closing (Cl := Unit) Q).decide t rs gs = .ok u := fun u hu =>
    (ProofFile.Law.guardMark_yes.1
      (show (ProofFile.guardMark (K9.closing (Cl := Unit) Q).retype).decide t rs gs = _ from hu)).1
  have inner : (K9.closing (Cl := Unit) Q).decide t rs gs = .ok t' := by
    unfold IM.seatedAs Block.guarded at h
    simp only at h
    split at h
    · exact key _ h
    · obtain ⟨u, hu, hv⟩ := ok_bind h
      unfold seatSame at hv
      split at hv
      · obtain rfl := Except.ok.inj hv
        exact key _ hu
      · cases hv
  rw [closing_decide] at inner
  cases hr : ((kind (Cl := Unit)) Q).decide (K9.recOf t) rs gs with
  | error e => rw [hr] at inner; cases inner
  | ok r =>
    rw [hr] at inner
    exact ⟨r, rfl, (Except.ok.inj inner).symm, (keeps_unmarked hk).2⟩

/-- The single rows' shape, from their make and the two letters. -/
theorem singleSh_of_make {Q : Par} {s : Rec} {D : BaseData} {R : SingleRows}
    (H : RowsMake Q s D R) {c : FormSh} {kept : List (Nat × FormSh)} (hc : formSh R.c = c)
    (hk : (R.kept.toList.map fun k => (k.oracle, formSh k.c)) = kept) :
    singleSh R = singleS Q s.frame.shape.code s.frame.shape.maskCode D.Gq.k D.Gq.h D.m (stSh s.st)
      (Ground.Sh.grpSh D.G) c kept := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, _⟩ := H
  unfold singleSh singleS
  rw [h1, h2, h3, h4, h5, h6, h7, h8, hc, hk, Ground.Sh.layoutS_eq]
  rfl

/-- The step at the shape of a state, written in the state's own letters. -/
theorem closeGS_at (Q : Par) (c : FormSh) (kept : List (Nat × FormSh)) (t : S) {L : Params.ReqLink}
    {Gq : ReqGroup} {m : Nat} {G : Group} (hm : t.failed = none)
    (h1 : (K9.recOf t).frame.shape.link[(K9.recOf t).frame.link]? = some L)
    (h2 : (K9.recOf t).frame.groups[(K9.recOf t).frame.link]? = some Gq)
    (h3 : (K9.recOf t).frame.mask = some m)
    (h4 : (K9.recOf t).st.groups[(K9.recOf t).frame.group]? = some G) :
    closeGS Q c kept (chainSh t) =
      if (K9.recOf t).owed.isNone && decide ((K9.recOf t).frame.next = .laterOrClose) &&
          (K9.recOf t).frame.moment == reqMoments L then
        (closeS Q (K9.recOf t).frame.shape.code (K9.recOf t).frame.shape.maskCode Gq.k Gq.h
          (K9.recOf t).frame.group m (stSh (K9.recOf t).st)).map fun y =>
          ((putLiveS (chainSh t) { (chainSh t).live with
            frame := (frameBehindS (frameSh (K9.recOf t).frame)
              (singleS Q (K9.recOf t).frame.shape.code (K9.recOf t).frame.shape.maskCode Gq.k Gq.h m
                (stSh (K9.recOf t).st) (Ground.Sh.grpSh G) c kept)) }).setCore
            { (chainSh t).core with st := y }).setRowsOwed none
      else none := by
  have hmk : (chainSh t).marked = false := by
    show t.failed.isSome = false
    rw [hm]
    rfl
  have hl : (chainSh t).live.frame = frameSh (K9.recOf t).frame := by
    rw [chainSh_live]
    rfl
  have hc : (chainSh t).core.st = stSh (K9.recOf t).st := rfl
  have g4 : (stSh (K9.recOf t).st).groups[(K9.recOf t).frame.group]? =
      some (Ground.Sh.grpSh G) := by
    rw [Ground.Sh.grp_get, h4]
    rfl
  unfold closeGS
  rw [hmk, hl, hc, owedS_eq]
  show (match (K9.recOf t).frame.shape.link[(K9.recOf t).frame.link]?,
      (K9.recOf t).frame.groups[(K9.recOf t).frame.link]?, (K9.recOf t).frame.mask,
      (stSh (K9.recOf t).st).groups[(K9.recOf t).frame.group]? with
    | some L, some Gq, some m, some G => _
    | _, _, _, _ => none) = _
  rw [h1, h2, h3, g4]
  rfl

/-- Where the record does not name one of the four, the guard says no. -/
theorem closeGB_none (Q : Par) (t : S)
    (h : (K9.recOf t).frame.shape.link[(K9.recOf t).frame.link]? = none ∨
      (K9.recOf t).frame.groups[(K9.recOf t).frame.link]? = none ∨
      (K9.recOf t).frame.mask = none ∨
      (K9.recOf t).st.groups[(K9.recOf t).frame.group]? = none) :
    closeGB Q (chainSh t) = false := by
  have hl : (chainSh t).live.frame = frameSh (K9.recOf t).frame := by
    rw [chainSh_live]
    rfl
  have hc : (chainSh t).core.st = stSh (K9.recOf t).st := rfl
  unfold closeGB closeGS
  rw [hl, hc]
  split
  · rfl
  · split
    · rename_i L Gq m G e1 e2 e3 e4
      exfalso
      have e1' : (K9.recOf t).frame.shape.link[(K9.recOf t).frame.link]? = some L := e1
      have e2' : (K9.recOf t).frame.groups[(K9.recOf t).frame.link]? = some Gq := e2
      have e3' : (K9.recOf t).frame.mask = some m := e3
      have e4' : (stSh (K9.recOf t).st).groups[(K9.recOf t).frame.group]? = some G := e4
      rcases h with h | h | h | h
      · rw [h] at e1'; cases e1'
      · rw [h] at e2'; cases e2'
      · rw [h] at e3'; cases e3'
      · rw [Ground.Sh.grp_get, h] at e4'; cases e4'
    · rfl

/-- **CARRIES**, under the one named premise: c and kept are the makes of the forms behind. -/
theorem close_carriesC {Q : Par} {same : S → S → Bool} {name : String} {a : Place} {t t' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (IM.seatedAs same (K9.closing (Cl := Unit) Q).retype name a).decide t rs gs = .ok t')
    {c : FormSh} {kept : List (Nat × FormSh)} (hF : FormsBehind t' c kept) :
    closeGS Q c kept (chainSh t) = some (chainSh t') := by
  obtain ⟨hc, hk⟩ := hF
  obtain ⟨r, hr, rfl, hm⟩ := seated_inner h
  obtain ⟨L, Gq, G, m, rows, k0, k1, k2, k3, k4, k5, k6, _, _, hrr⟩ := close_keeps hr
  obtain ⟨Gq', m', j2, j3, hS⟩ := close_carries hr
  obtain rfl : Gq = Gq' := Option.some.inj (k2.symm.trans j2)
  obtain rfl : m = m' := Option.some.inj (k5.symm.trans j3)
  obtain ⟨D, hD, hM⟩ := rows_make hr
  obtain ⟨d1, d2, d3, d4⟩ := baseData_some hD
  obtain rfl : D.Gq = Gq := Option.some.inj (d2.symm.trans k2)
  obtain rfl : D.m = m := Option.some.inj (d3.symm.trans k5)
  obtain rfl : D.G = G := Option.some.inj (d4.symm.trans k6)
  have hrec : K9.recOf (K9.putRec t r) = r := by
    rw [hrr]
    exact recOf_put t _ _
  rw [hrec] at hc hk
  rw [closeGS_at Q c kept t hm k1 k2 k5 k6, k0, k3, k4, hS, chainSh_putRec]
  have hf : frameSh r.frame =
      frameBehindS (frameSh (K9.recOf t).frame) (singleSh r.frame.rows) := by
    rw [hrr]
    rfl
  have ho : r.owed = none := by rw [hrr]
  rw [hf, singleSh_of_make hM hc hk, ho]
  simp

/-- **THE GUARD AT THE SHAPE OF A STATE IS**: no mark, and the first test of Split.lean at the
state's record. -/
theorem closeGB_eq (Q : Par) (t : S) :
    closeGB Q (chainSh t) = (!t.failed.isSome && closeShapeB Q (K9.recOf t)) := by
  cases hm : t.failed with
  | some e =>
    unfold closeGB closeGS
    have : (chainSh t).marked = true := by
      show t.failed.isSome = true
      rw [hm]
      rfl
    rw [this]
    rfl
  | none =>
    rw [closeShapeB_eq]
    cases h1 : (K9.recOf t).frame.shape.link[(K9.recOf t).frame.link]? with
    | none => exact closeGB_none Q t (Or.inl h1)
    | some L =>
      cases h2 : (K9.recOf t).frame.groups[(K9.recOf t).frame.link]? with
      | none => exact closeGB_none Q t (Or.inr (Or.inl h2))
      | some Gq =>
        cases h3 : (K9.recOf t).frame.mask with
        | none => exact closeGB_none Q t (Or.inr (Or.inr (Or.inl h3)))
        | some m =>
          cases h4 : (K9.recOf t).st.groups[(K9.recOf t).frame.group]? with
          | none =>
            rw [closeGB_none Q t (Or.inr (Or.inr (Or.inr h4)))]
            have hg : closeG Q (K9.recOf t).frame.shape.code (K9.recOf t).frame.shape.maskCode Gq.k
                Gq.h (K9.recOf t).frame.group m (stSh (K9.recOf t).st) = false := by
              unfold closeG
              rw [Ground.Sh.grp_get, h4]
              simp
            show false = (!(none : Option String).isSome && (_ && _ && _ && closeG Q
              (K9.recOf t).frame.shape.code (K9.recOf t).frame.shape.maskCode Gq.k Gq.h
              (K9.recOf t).frame.group m (stSh (K9.recOf t).st)))
            rw [hg]
            simp
          | some G =>
            unfold closeGB
            rw [closeGS_at Q _ _ t hm h1 h2 h3 h4]
            show _ = (!(none : Option String).isSome && (((K9.recOf t).owed.isNone &&
              decide ((K9.recOf t).frame.next = .laterOrClose) &&
              (K9.recOf t).frame.moment == reqMoments L) && closeG Q
              (K9.recOf t).frame.shape.code (K9.recOf t).frame.shape.maskCode Gq.k Gq.h
              (K9.recOf t).frame.group m (stSh (K9.recOf t).st)))
            rw [← closeS_isSome]
            split
            · rename_i hc
              rw [hc, Option.isSome_map]
              rfl
            · rename_i hc
              rw [Bool.not_eq_true] at hc
              rw [hc]
              rfl

/-- **RETURNS**, under the named test on the rows and what "BAT" drew. -/
theorem close_returnsC {Q : Par} {name : String} {a : Place} {t : S} {c : FormSh}
    {kept : List (Nat × FormSh)} {y : ChainSh} (hG : closeGS Q c kept (chainSh t) = some y)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (hl : rs.length = 2 + Q.k)
    (hs : ShapedAll rs) (hv : closeValsB (K9.recOf t) rs = true) :
    ∃ t', (IM.seatedAs ProofFile.sameReply (K9.closing (Cl := Unit) Q).retype name a).decide t rs gs =
      .ok t' := by
  have hm : t.failed = none := by
    unfold closeGS at hG
    split at hG
    · cases hG
    · rename_i hmk
      have h1 : (chainSh t).marked = false := by simpa using hmk
      have h2 : t.failed.isSome = false := h1
      simpa using h2
  refine (seated_yes_iff Q name a t rs gs).2 ⟨hm, hl, hs, ?_, hv⟩
  rw [closeShapeB_eq]
  cases h1 : (K9.recOf t).frame.shape.link[(K9.recOf t).frame.link]? with
  | none => exact absurd hv (by unfold closeValsB baseData; rw [h1]; simp)
  | some L =>
    cases h2 : (K9.recOf t).frame.groups[(K9.recOf t).frame.link]? with
    | none => exact absurd hv (by unfold closeValsB baseData; rw [h1, h2]; simp)
    | some Gq =>
      cases h3 : (K9.recOf t).frame.mask with
      | none => exact absurd hv (by unfold closeValsB baseData; rw [h1, h2, h3]; simp)
      | some m =>
        cases h4 : (K9.recOf t).st.groups[(K9.recOf t).frame.group]? with
        | none => exact absurd hv (by unfold closeValsB baseData; rw [h1, h2, h3, h4]; simp)
        | some G =>
          rw [closeGS_at Q c kept t hm h1 h2 h3 h4] at hG
          split at hG
          · rename_i hc
            obtain ⟨z, hz, _⟩ := Option.map_eq_some_iff.1 hG
            have hg := closeS_isSome Q (K9.recOf t).frame.shape.code
              (K9.recOf t).frame.shape.maskCode Gq.k Gq.h (K9.recOf t).frame.group m
              (stSh (K9.recOf t).st)
            rw [hz] at hg
            show (_ && _ && _ && closeG Q (K9.recOf t).frame.shape.code
              (K9.recOf t).frame.shape.maskCode Gq.k Gq.h (K9.recOf t).frame.group m
              (stSh (K9.recOf t).st)) = true
            rw [← hg, hc]
            rfl
          · cases hG

/-- **AT THE MEMBER, UNDER THE LIBRARY's ONE HEAD, AT EACH LINK**: which block it is; what its
step asks of the rounds; CARRIES, STILL UNDER THE ONE NAMED PREMISE; RETURNS, from the guard that
is free of the letters. -/
theorem closingBlock_at {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    {x : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    ∃ (p : K9.Where) (Q : Par) (b : Block S ProofFile.Cl),
      IM.k9At Zp l = some p ∧ ProofFile.k10Par Zp (ProofFile.k9Stretches Zp) p = some Q ∧
      cF.blocksInOrder[14 * l + (if l = 24 then 9 else 7) + 5]? = some b ∧
      b = IM.seatedAs ProofFile.sameReply (K9.closing (Cl := Unit) Q).retype b.name
        (IM.cAt l (IM.subAt l) 1 .K10) ∧
      (∀ ft rs cols, b.Fits ft rs cols ↔ rs.length = 2 + Q.k ∧ ShapedAll rs) ∧
      (∀ t t' rs gs c kept, b.decide t rs gs = .ok t' → FormsBehind t' c kept →
        closeGS Q c kept (chainSh t) = some (chainSh t')) ∧
      ∀ t rs gs, closeGB Q (chainSh t) = true → rs.length = 2 + Q.k →
        ShapedAll rs → closeValsB (K9.recOf t) rs = true → ∃ t', b.decide t rs gs = .ok t' := by
  obtain ⟨Lk, p, Q, b, _, hp, hQ, _, hn, hb, _⟩ := seated_at_headK10 h l hl
  refine ⟨p, Q, b, hp, hQ, hn, hb, fun ft rs cols => ?_, fun t t' rs gs c kept hd hF => ?_,
    fun t rs gs hG h1 h2 h3 => ?_⟩
  · rw [hb]
    exact seated_fits_iff Q _ _ _ ft rs cols
  · rw [hb] at hd
    exact close_carriesC hd hF
  · rw [hb]
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hG
    exact close_returnsC hy rs gs h1 h2 h3

end ProofFile.Honest.K10.YesFree

#print axioms ProofFile.Honest.K10.YesFree.closeGS_isSome
#print axioms ProofFile.Honest.K10.YesFree.closeGB_eq
#print axioms ProofFile.Honest.K10.YesFree.close_carriesC
#print axioms ProofFile.Honest.K10.YesFree.close_returnsC
#print axioms ProofFile.Honest.K10.YesFree.closingBlock_at
#print axioms ProofFile.Honest.K10.YesFree.seated_inner
#print axioms ProofFile.Honest.K10.YesFree.singleSh_of_make
#print axioms ProofFile.Honest.K10.YesFree.chainSh_putLive
#print axioms ProofFile.Honest.K10.YesFree.chainSh_putRec
