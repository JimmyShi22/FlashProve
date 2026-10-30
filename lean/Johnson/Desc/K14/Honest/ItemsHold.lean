--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/ItemsHold.lean: claims on an honest prover's tables that the library's laws
of the linear claim's shared rounds name, read forwards: each holds of the honest words behind the
sub-protocol that, in the library's table of the shared chain, opens it. Each is shown from public
premises, from the run UP TO that sub-protocol, and, of what is shown, FROM WHAT THAT SUB-PROTOCOL
ITSELF SHOWS.

The library's table (Johnson/Desc/Shared/BordersShared.lean: rowS) names, for each sub-protocol, the
claims that it closes, opens and reads. The library reads it backwards, for soundness. The kind's
laws give the claims their forms. WHAT STANDS IN THE STATEMENTS HERE ARE THESE FORMS THEMSELVES, at
words in the witness's stead: no statement names the table, its entries or a filling. That these are
the table's claims at a witness needs that the witness's words are the honest words, and that the
library's reader of o_omega's table is omegaAt: not in this file.

The forms, and where the library lays them:
  OmU, NearAt, RecAll, RowsUL, RowsU, RowsO, FoldAt: the fields omU, nearU, recRow and row of mgI
      (Johnson/Desc/K14/Law/LedgerOne.lean), at the reader uRK of the state (o_u noted as the
      message to come, where it is not sent yet)
  SmpSay: mgI leaves the sample constraints to a letter; SmpSay is the form that meets the law's
      premise on that letter (LedgerOne.lean) and that the library lays there
      (Johnson/Desc/K14/Law/LedgerLetters.lean)
  DotEq: no field of mgI: the form of the request's own claim (Dot)
      (Johnson/Desc/Sound/PointAtFilling.lean)

Main names:
  rowsOn_say, stretch_say, smpSay_of_met   from AllMet to these forms
  Notes, AtU.notes, wOf_notes, sends_of   what the kind notes of the point and of o_u; small tools
  fold_at, omU_at, nearU_at, recRow_at, dot_at   SENTENCES ON THE HONEST WORDS ALONE, from the
                      public premises: they hold whatever is sent. nearU_at asks hTab; recRow_at
                      asks that the key's sizes fit, and OwnAnswers; dot_at asks VIs
  "LIN point"         Public8.omU_behind1, nearU_behind1, recRow_behind1. Of the five claims that
                      the table opens there, these three; (Dot) stands beside as dot_at; the
                      request's own claim on the other vector, and the two claims read as context,
                      are not here
  the two sendings    smp_new: every NEW sample constraint holds, whatever words lie in front, where
                      what THAT sending shows is honest (Johnson/Prover/Send/Says.lean: send_says);
                      Public8.sample_behind2, sample_behind5: o_u's; o_omega's and o_sp's
  "(rec_gamma)", "LOC"   Public8.recG_behind3 (asks OwnAnswers), loc_behind4 (asks OwnColumns):
                      nothing that a sending or "SPLIT" shows is asked; of the columns that "LOC"
                      reads: OwnColumns. With the number of constraints on the group, so that the
                      stretch named is what that sub-protocol has laid
  "LIN zeta"          Public8.fold_behind7: nothing more is asked
  "SPLIT"             split_rows_say; Public8.foldU_behind8, foldOmega_behind8: ask ShownMu alone.
                      With the numbers of constraints

What is assumed, as premises: Public8 and the run up to the sub-protocol
(Johnson/Desc/K14/Honest/RunsTo.lean); what is named above. NO THEOREM HERE ASKS AllMet IN FRONT,
and none asks what an earlier sub-protocol showed. At "LIN point": no message has been sent in front
of the eight (h0): so at the shared chain's first state. At recRow_at and recRow_behind1: THE KEY's
SIZES FIT (hkey): the verifier tests that only later, in "(rec_gamma)". For nearU: hTab: THE
COMMITTED TABLE's COLUMN AT EVERY LOCATION, opened or not, holds the rows' own symbols. For dot: the
other vector is the row weights applied to the rows' matrix (VIs).
What is not claimed. The three claims that a sampled message's table is what its committed word
decodes to (the table's "pin"), neither where they are opened nor where a later entry reads them as
context. That a claim, once it holds, holds behind later sub-protocols for every witness: these are
sentences on one family of words. That a committer's table meets hTab. Nothing on soundness or on
hiding. This is not completeness of the protocol or of a program.

-/
import Johnson.Desc.K14.Honest.ShapesBehind
import Johnson.Desc.K14.Honest.ItemsEach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Means (Words)
open OnBytes.Slice (rdE)
open Johnson.Prover.Send (Rows held shapeAt send_says)
open VerifiableInference.Desc (Grows)
open VerifiableInference.Desc.Ground (ok)
open VerifiableInference.Desc.Own (keyFits)
open VerifiableInference.Desc.K1 (decideSend_iff)
open VerifiableInference.Desc.Key.LaidW (inFrontOf)
open Desc.K14.Law (genK uOf omegaOf eqK rowsOn parK1_sent parU parO OmU NearAt RecAll RowsU RowsUL
  RowsO FoldAt SmpSay uRK uRK_next nearAt_of_rows rowsUL_of_own index_ok_of_linOk DotEq VIs Seated
  placed_of_seated size_grows on4_of_seatedUB onward_laysRec onward_loc laysLocW split_inv
  foldMeansW rowsOn_addRowP_same rowsOn_addRowP_other rowsOn_takeMaskP)

/-! ## From AllMet to the forms in which the kind's laws name rows -/

/-- All rows on a group, as they lie in the state, hold. -/
theorem rowsOn_say {d : St} {m : Words Cb.Gl.E} (h : Means.AllMet rdE d.st m) (g : Nat) :
    Means.AllSay rdE d.st (rowsOn d g) m := by
  unfold rowsOn
  cases hG : d.st.groups[g]? with
  | none =>
    intro r hr
    cases hr
  | some G => exact h.2.rows g G hG

/-- A stretch of a list of rows that hold. -/
theorem stretch_say {T : Statement} {l : List Row} {m : Words Cb.Gl.E}
    (h : Means.AllSay rdE T l m) (i n : Nat) : Means.AllSay rdE T ((l.drop i).take n) m :=
  fun r hr => h r (List.mem_of_mem_drop (List.mem_of_mem_take hr))

/-- A message's sample rows hold, in the library's form SmpSay. -/
theorem smpSay_of_met {d : St} {m : Words Cb.Gl.E} (h : Means.AllMet rdE d.st m) (o : Nat)
    (ho : o < d.st.oracles.size) : SmpSay o d m :=
  ⟨d.st.oracles[o], d.st, Array.getElem?_eq_getElem ho, Grows.refl _,
    h.2.samples o _ (Array.getElem?_eq_getElem ho)⟩

variable {P : P14} {sentU : Array OracleNotice} {layO : TreeLay} {d0 : St} {V : View8}
  {D : States8} {H : Inputs}

/-! ## Sentences on the honest words alone: they hold whatever is sent -/

/-- Of what the kind notes, two fields are as a run from d0 leaves them: the shared point is the one
sampled in the round r1, and o_u is the first new message, in the plan's layout. -/
structure Notes (P : P14) (d0 : St) (r1 : Fmt.RoundView) (l : Lin) : Prop where
  psi : l.psiSh = drawn r1
  u : l.oU = ⟨d0.st.oracles.size, vectorLay P.codes P.par.S.fold.u P.par.S.fold.rowsHigh⟩

/-- The weights read the point alone. -/
theorem wOf_notes {r1 : Fmt.RoundView} {l : Lin} (hl : Notes P d0 r1 l) :
    wOf rdE P.par.S l = wRun P d0 r1 := by
  funext r
  unfold wRun wOf weights gamma
  rw [hl.psi]
  rfl

/-- The numbers of the two sendings' messages, and their shapes: off the public premises. -/
theorem sends_of (hP : PlanFacts P.par P.codes sentU layO) (n0 : Nat) :
    (n0 + (parU P sentU).sent.size ≤ n0 + 2 ∧ 0 < (parU P sentU).sent.size ∧
      shapeAt (parU P sentU) 0 = P.par.S.fold.u) ∧
      0 < (parO P).sent.size ∧ shapeAt (parO P) 0 = P.par.S.omega := by
  obtain ⟨w2, w0, _⟩ := withOmega_two hP.two
  have sU : (parU P sentU).sent = sentU := parK1_sent P 2 _ sentU
  have sO : (parO P).sent = withOmega P.par.S := parK1_sent P 5 _ _
  refine ⟨⟨by rw [sU, hP.goesTwo], by rw [sU, hP.goesTwo]; omega, ?_⟩, by rw [sO, w2]; omega, ?_⟩
  · exact (shapeAt_of_get (parU P sentU) 0 ⟨P.par.S.fold.u, P.par.S.fold.leafClass⟩
      (by rw [sU]; exact withU_zero hP.goes)).1
  · exact (shapeAt_of_get (parO P) 0 ⟨P.par.S.omega, P.par.S.omegaLeafClass⟩
      (by rw [sO]; exact w0)).1

/-- **o_u's table in the honest words holds the rows' fold.** From the public premises alone. -/
theorem fold_at (hP : PlanFacts P.par P.codes sentU layO) (d0 : St) (r1 : Fmt.RoundView) (H : Inputs)
    {l : Lin} (hl : Notes P d0 r1 l) :
    IsFold P.par.S.fold (wOf rdE P.par.S l) H.Rw (uOf l (words2 P sentU d0 r1 H)) := by
  obtain ⟨⟨hle, hsz, hsh⟩, _⟩ := sends_of hP d0.st.oracles.size
  rw [wOf_notes hl]
  exact isFold_chain H.w₀ d0.st.oracles.size (d0.st.oracles.size + 2) (parU P sentU) (parO P)
    (rowsO P d0 r1 H) P.codes P.par.S (wRun P d0 r1) H.Rw H.cU H.cMask l hP.lin hle hsz hsh hl.u

/-- o_omega's table, at the run's number and the plan's layout: the library's omWK
(Johnson/Desc/K14/Law/LedgerOne.lean), read at words. -/
def omegaAt (P : P14) (d0 : St) (m : Words Cb.Gl.E) (y : Nat) : Cb.Gl.E :=
  m (d0.st.oracles.size + 2) .main ((linLayOmega P.codes P.par.S).index y)

/-- **o_omega's table in the honest words is, row by row of the matrix, what o_u's gives at the
point's low part.** From the public premises alone. -/
theorem omU_at (hP : PlanFacts P.par P.codes sentU layO) (d0 : St) (r1 : Fmt.RoundView) (H : Inputs)
    {l : Lin} (hl : Notes P d0 r1 l) (y : Nat) (hy : y < P.par.S.matrixRows) :
    omegaAt P d0 (words2 P sentU d0 r1 H) y = ∑ t ∈ Finset.range (2 ^ P.par.S.kLo),
      eqK ((l.psiSh.take P.par.S.kLo).map rdE.val) t *
        uOf l (words2 P sentU d0 r1 H) (t + 2 ^ P.par.S.kLo * y) := by
  obtain ⟨⟨hle, hsz, hsh⟩, hszO, hshO⟩ := sends_of hP d0.st.oracles.size
  rw [hl.psi]
  exact col_chain H.w₀ d0.st.oracles.size (d0.st.oracles.size + 2) (parU P sentU) (parO P) P.codes
    P.par.S (psiLoRun P r1) (wRun P d0 r1) H.Rw H.cU H.cMask H.cOmega H.cSp
    { l with oOmega := d0.st.oracles.size + 2 } hP.lin hle hsz hsh hl.u hszO hshO rfl y hy

/-- **The code word of o_u's table in the honest words is the fold of the committed table's
columns**, at every radius. tab: the committed table's columns; hTab: at EVERY location, opened or
not, the column holds the rows' own symbols. -/
theorem nearU_at (hP : PlanFacts P.par P.codes sentU layO) (d0 : St) (r1 : Fmt.RoundView) (H : Inputs)
    (d : St) (hl : Notes P d0 r1 d.loc) (hpt : (drawn r1).length = P.par.S.kCol)
    (tab : Nat → List UInt64)
    (hTab : ∀ x < 2 ^ P.par.S.fold.index.code.logN, ∀ r < P.par.S.fold.index.rows,
      rdE.val (ofF ((tab x).toArray.getD r 0)) = genK rdE P.par.S.fold x (H.Rw r)) (e' : Nat) :
    NearAt rdE P.par d (words2 P sentU d0 r1 H) tab e' := by
  have hw : (weights P.par.S d.loc).size = P.par.S.fold.index.rows :=
    weights_size P.par d (by rw [hl.psi]; exact hpt)
  have hF := fold_at hP d0 r1 H hl
  refine nearAt_of_rows rdE P.par d _ tab H.Rw
    (fun x hx r hr => hTab x hx r (by rw [← hw]; exact hr)) (fun j hj => ?_) (fun j hj => ?_) e'
  · rw [hF.onMsg j hj, hw]
    rfl
  · rw [hF.onTail j hj, hw]
    rfl

/-- **The answers of o_u's table in the honest words at the key's seeds are the fold of the key's
answers**, where the key's sizes fit and each answer of the key is its row's own. -/
theorem recRow_at (hP : PlanFacts P.par P.codes sentU layO) (d0 : St) (r1 : Fmt.RoundView) (H : Inputs)
    (d : St) (hl : Notes P d0 r1 d.loc) (hkey : keyFits d.loc.key P.par.S.fold.index = true)
    (hA : OwnAnswers P d.loc.key H) : RecAll rdE P.par d (words2 P sentU d0 r1 H) := by
  intro x hx
  have hfit : d.loc.key.fits P.par.S.fold.index = true := hkey
  simp only [TableKey.fits, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hfit
  have hx' : d.loc.key.seeds[x.2]? = some x.1 := List.mem_zipIdx_iff_getElem?.1 hx
  have hlt : x.2 < P.par.S.fold.index.answers := by
    rw [← hfit.1.2]
    exact (List.getElem?_eq_some_iff.1 hx').1
  have hi := index_ok_of_linOk P.codes P.par.S (linOk_of hP)
  simp only [IndexShape.ok, Bool.and_eq_true, decide_eq_true_eq] at hi
  have hp0 : P.par.S.fold.index.pads < P.par.S.fold.index.code.ell := by tauto
  exact recEq_of_isFold P.par.S.fold (x.1.z.map rdE.val) (rdE.val x.1.beta)
    (fun t => rdE.val (thetaE t)) x.2 (wOf rdE P.par.S d.loc)
    (fun k => rdE.val (d.loc.key.record.getD k zeroE)) (uOf d.loc (words2 P sentU d0 r1 H)) H.Rw
    (fold_at hP d0 r1 H hl) (Nat.le_of_lt hp0) hlt (hA x hx)

/-- **(Dot)'s equation holds at o_omega's table in the honest words**, if the other vector is the
row weights g applied to the rows' matrix. From the public premises alone. -/
theorem dot_at (hP : PlanFacts P.par P.codes sentU layO) (d0 : St) (r1 : Fmt.RoundView) (H : Inputs)
    (hpt : (drawn r1).length = P.par.S.kCol) (g W : Nat → Cb.Gl.E) (hW : VIs P.par.S g H.Rw W) :
    DotEq P.par.S.matrixRows P.par.S.kCol g (omegaAt P d0 (words2 P sentU d0 r1 H))
      ((drawn r1).map rdE.val) W := by
  obtain ⟨_, hszO, hshO⟩ := sends_of hP d0.st.oracles.size
  have hsh := (VerifiableInference.Desc.Own.linFits_iff P.codes P.par.S).1 hP.lin
  have hroom : P.par.S.matrixRows * 2 ^ P.par.S.kLo ≤ P.par.S.fold.index.plain :=
    hsh.1.2.2.2.2.2.1
  have hk : P.par.S.kLo ≤ (drawn r1).length := by
    rw [hpt]
    unfold LinShape.kCol
    omega
  have hg : (gamma P.par.S
      (locU P.par P.codes d0.loc d0.st.groups.size d0.st.oracles.size r1)).length =
      P.par.S.fold.index.v := by
    show ((drawn r1).drop P.par.S.kLo).length = _
    rw [List.length_drop, hpt]
    unfold LinShape.kCol
    omega
  have e := dotEq_honest P.par.S (psiLoRun P r1) (((drawn r1).drop P.par.S.kLo).map rdE.val) g
    (wRun P d0 r1) (uHon P.par.S.fold (wRun P d0 r1) H.Rw) W H.Rw
    (by unfold psiLoRun; rw [List.length_map, List.length_take]; omega)
    (uHon_isFold P.par.S.fold _ H.Rw) (wOf_eq rdE P.par.S _ hg) hroom hW
  have ep : psiLoRun P r1 ++ ((drawn r1).drop P.par.S.kLo).map rdE.val =
      (drawn r1).map rdE.val := by
    unfold psiLoRun
    rw [← List.map_append, List.take_append_drop]
  rw [ep] at e
  unfold DotEq at e ⊢
  rw [← e]
  refine Finset.sum_congr rfl fun y hy => ?_
  have eo : omegaAt P d0 (words2 P sentU d0 r1 H) y =
      omegaHon P.par.S (psiLoRun P r1) (uHon P.par.S.fold (wRun P d0 r1) H.Rw) y :=
    omega_chain H.w₀ d0.st.oracles.size (d0.st.oracles.size + 2) (parU P sentU) (parO P)
      (rowsU P d0 r1 H) P.codes P.par.S (psiLoRun P r1) (uHon P.par.S.fold (wRun P d0 r1) H.Rw)
      H.cOmega H.cSp { d0.loc with oOmega := d0.st.oracles.size + 2 } hP.lin hszO hshO rfl y
      (Finset.mem_range.1 hy)
  rw [eo]

/-! ## Behind "LIN point": from the run up to it -/

/-- Behind "LIN point", read with o_u noted as the message to come, the state notes what the run
does. h0: no message has been sent in front of the eight. -/
theorem Public8.notes1 (S : Public8 P sentU layO d0) (u : To1 P d0 V D)
    (h0 : d0.st.oracles.size = 0) :
    Notes P d0 V.r1 (uRK P.par D.d1).loc ∧ (uRK P.par D.d1).loc.key = d0.loc.key ∧
      D.d1.loc.psiSh = drawn V.r1 := by
  have A := S.at1 u
  have hp : D.d1.loc.psiSh = drawn V.r1 := by rw [A.loc]
  rw [uRK_next P.par D.d1 (by rw [A.size]; exact h0)]
  refine ⟨⟨hp, ?_⟩, A.carried.key, hp⟩
  show (⟨D.d1.st.oracles.size, vectorLay D.d1.st.codes P.par.S.fold.u P.par.S.fold.rowsHigh⟩ :
    FoldedRow) = _
  rw [A.size, A.carried.codes]

/-- **Behind "LIN point": the library's OmU holds of the honest words.** Nothing is asked of the
key. -/
theorem Public8.omU_behind1 (S : Public8 P sentU layO d0) (u : To1 P d0 V D)
    (h0 : d0.st.oracles.size = 0) (H : Inputs) :
    OmU P.par (uRK P.par) (fun w : Words Cb.Gl.E => w) (omegaAt P d0) D.d1
      (words2 P sentU d0 V.r1 H) := by
  obtain ⟨hn, _, hp⟩ := S.notes1 u h0
  intro y hy
  have e := omU_at S.facts d0 V.r1 H hn y hy
  rw [hn.psi, ← hp] at e
  exact e

/-- **Behind "LIN point": the library's NearAt holds of the honest words**, at every radius, under
hTab. Nothing is asked of the key. -/
theorem Public8.nearU_behind1 (S : Public8 P sentU layO d0) (u : To1 P d0 V D)
    (h0 : d0.st.oracles.size = 0) (H : Inputs) (tab : Nat → List UInt64)
    (hTab : ∀ x < 2 ^ P.par.S.fold.index.code.logN, ∀ r < P.par.S.fold.index.rows,
      rdE.val (ofF ((tab x).toArray.getD r 0)) = genK rdE P.par.S.fold x (H.Rw r)) (e' : Nat) :
    NearAt rdE P.par (uRK P.par D.d1) (words2 P sentU d0 V.r1 H) tab e' :=
  nearU_at S.facts d0 V.r1 H _ (S.notes1 u h0).1 u.point tab hTab e'

/-- **Behind "LIN point": the library's RecAll holds of the honest words**, WHERE THE KEY's SIZES
FIT and each answer of the key is its row's own. -/
theorem Public8.recRow_behind1 (S : Public8 P sentU layO d0) (u : To1 P d0 V D)
    (h0 : d0.st.oracles.size = 0) (hkey : keyFits d0.loc.key P.par.S.fold.index = true)
    (hA : OwnAnswers P d0.loc.key H) :
    RecAll rdE P.par (uRK P.par D.d1) (words2 P sentU d0 V.r1 H) := by
  obtain ⟨hn, hk, _⟩ := S.notes1 u h0
  exact recRow_at S.facts d0 V.r1 H _ hn (by rw [hk]; exact hkey) (by rw [hk]; exact hA)

/-! ## The two sendings: the new sample rows, from what that sending itself shows -/

/-- **Every sample row of a message that a sending brings holds of the held words**, whatever words
lie in front, where the OOD answers that this sending shows are the honest ones. -/
theorem smp_new {Q : VerifiableInference.Desc.K1.Par} {note : St → Array Nat → Option St}
    {d d' : St} {ra rb : Fmt.RoundView} {x : DState (Array Nat)} {ids : Array Nat}
    (h : SentTo Q note d d' ra rb x ids) (w : Words Cb.Gl.E) (Vr : ℕ → Rows)
    (ha : rb.vals = answersAt Q d.st ra w Vr) (k : Nat) (hk : k < Q.sent.size) (hk2 : k < 2) :
    ∃ y, d'.st.oracles[d.st.oracles.size + k]? = some y ∧
      Means.AllSay rdE d'.st y.sampleRows.toList (held w d.st.oracles.size Q Vr) := by
  obtain ⟨_, _, e⟩ := (decideSend_iff Q none (inFrontOf d) x ra rb ids).1 h.sent
  obtain ⟨y, hy⟩ : ∃ y, d'.st.oracles[d.st.oracles.size + k]? = some y :=
    ⟨_, Array.getElem?_eq_getElem (by rw [h.size]; omega)⟩
  refine ⟨y, hy, ?_⟩
  rw [h.st] at hy ⊢
  subst e
  exact send_says Q (inFrontOf d) ra rb w Vr ha k y hk hy

/-- **Behind the sending of o_u its sample rows hold of the honest words** (SmpSay), where the OOD
answers that this sending shows are the honest ones. -/
theorem Public8.sample_behind2 (S : Public8 P sentU layO d0) (u : To2 P sentU d0 V D)
    (hU : ShownU P sentU d0 V D H) :
    SmpSay d0.st.oracles.size D.d2 (words2 P sentU d0 V.r1 H) := by
  obtain ⟨⟨_, hsz, _⟩, _⟩ := sends_of S.facts d0.st.oracles.size
  obtain ⟨y, hy, hs⟩ := smp_new u.s2 H.w₀ (rowsU P d0 V.r1 H) hU 0 hsz (by omega)
  rw [(S.at1 u.front).size] at hy hs
  refine ⟨y, D.d2.st, hy, Grows.refl _, fun r hr => ?_⟩
  exact (Means.says_of_words rdE D.d2.st r fun o ho part i =>
    words2_old P sentU d0 V.r1 H o (by rw [(S.at2 u).size] at ho; exact ho) part i).1 (hs r hr)

/-- **Behind the second sending o_omega's and o_sp's sample rows hold of the honest words**
(SmpSay), where the OOD answers that this sending shows are the honest ones. Nothing is asked of
what the first sending showed. -/
theorem Public8.sample_behind5 (S : Public8 P sentU layO d0) (u : To5 P sentU d0 V D)
    (hO : ShownO P sentU d0 V D H) :
    SmpSay (d0.st.oracles.size + 2) D.d5 (words2 P sentU d0 V.r1 H) ∧
      SmpSay (d0.st.oracles.size + 3) D.d5 (words2 P sentU d0 V.r1 H) := by
  obtain ⟨w2, _, _⟩ := withOmega_two S.facts.two
  have sO : (parO P).sent.size = 2 := (congrArg Array.size (parK1_sent P 5 _ _)).trans w2
  obtain ⟨y, hy, hs⟩ := smp_new u.s5 (words1 P sentU d0 V.r1 H) (rowsO P d0 V.r1 H) hO 0
    (by rw [sO]; omega) (by omega)
  obtain ⟨z, hz, ht⟩ := smp_new u.s5 (words1 P sentU d0 V.r1 H) (rowsO P d0 V.r1 H) hO 1
    (by rw [sO]; omega) (by omega)
  rw [(S.at4 u.front).size] at hy hs hz ht
  exact ⟨⟨y, D.d5.st, hy, Grows.refl _, hs⟩, ⟨z, D.d5.st, hz, Grows.refl _, ht⟩⟩

/-! ## "(rec_gamma)" and "LOC": the rows that each has laid, by that row's own law -/

/-- What the kind notes between the two sendings is what Notes asks. -/
theorem AtU.notes {r1 : Fmt.RoundView} {d : St} {mU : List Nat} (A : AtU P d0 r1 d mU) :
    Notes P d0 r1 d.loc :=
  ⟨by rw [A.loc]; rfl, by rw [A.loc]; rfl⟩

/-- **Behind "(rec_gamma)" the rows on o_u's group hold of the honest words** (RowsUL), and they are
just as many as the key has answers a row: so they are the rows that "(rec_gamma)" has laid. Nothing
is asked of what is shown. -/
theorem Public8.recG_behind3 (S : Public8 P sentU layO d0) (u : To3 P sentU d0 V D)
    (hA : OwnAnswers P d0.loc.key H) :
    RowsUL rdE 0 P.par.S.fold.index.answers D.d3 (words2 P sentU d0 V.r1 H) ∧
      (rowsOn D.d3 D.d3.loc.gU).length = P.par.S.fold.index.answers := by
  have A := S.at2 u.front
  obtain ⟨hi, hP2⟩ := on4_of_seatedUB P.par D.d2 (A.stands S.facts)
  obtain ⟨ho, hl⟩ := onward_laysRec P.par D.d2 D.d3 V.rs3 u.k3
  have h0 : rowsOn D.d2 D.d2.loc.gU = [] :=
    List.eq_nil_of_length_eq_zero (S.rows2 u.front (S.keyFits_of u))
  have k := rec_hold rdE P.par D.d2 D.d3 V.rs3 D.d3.st (words2 P sentU d0 V.r1 H) H.Rw u.k3 hi
    (hP2 _ ho.grows) (fold_at S.facts d0 V.r1 H A.notes) (by rw [A.carried.key]; exact hA)
    (by rw [h0]; intro r hr; cases hr)
  rw [← hl] at k
  exact ⟨rowsUL_of_own rdE _ _ _ _ (stretch_say k _ _), S.rows3 u⟩

/-- **Behind "LOC" the rows behind "(rec_gamma)"'s on o_u's group hold of the honest words**
(RowsUL), and they are just as many as locations were sampled: they are the rows that "LOC" has
laid. Nothing that a sending or "SPLIT" shows is asked, nor anything of the key's answers; of the
columns that "LOC" reads: OwnColumns. -/
theorem Public8.loc_behind4 (S : Public8 P sentU layO d0) (u : To4 P sentU d0 V D)
    (hC : OwnColumns P V H) :
    RowsUL rdE P.par.S.fold.index.answers P.par.S.fold.columns D.d4
        (words2 P sentU d0 V.r1 H) ∧
      (rowsOn D.d4 D.d4.loc.gU).length = P.par.S.fold.index.answers + P.par.S.fold.columns := by
  have A := S.at3 u.front
  obtain ⟨hi, hP3⟩ := on4_of_seatedUB P.par D.d3 (A.stands S.facts)
  obtain ⟨ho, hl⟩ := onward_loc P.par D.d3 D.d4 V.r4 V.cols u.k4
  obtain ⟨_, rows, hrows, _, hU, _⟩ := laysLocW P.par D.d3 D.d4 V.r4 V.cols u.k4
  have hs := loc_say rdE P.par D.d3 V.r4 V.cols D.d4.st (words2 P sentU d0 V.r1 H) H.Rw rows hrows
    hi (hP3 _ ho.grows) (fold_at S.facts d0 V.r1 H A.notes)
    (weights_size P.par D.d3 A.carried.psi) hC
  refine ⟨rowsUL_of_own rdE _ _ _ _ fun r hr => ?_, S.rows4 u⟩
  rw [hl, hU, List.drop_left' (S.rows3 u.front)] at hr
  exact hs r (List.mem_of_mem_take hr)

/-! ## "LIN zeta" and "SPLIT" -/

/-- **Behind "LIN zeta" (fold)'s equation holds of the honest words at the point noted** (FoldAt).
It asks nothing of what is shown, and neither premise on the committed table. -/
theorem Public8.fold_behind7 (S : Public8 P sentU layO d0) (u : To7 P sentU d0 V D) (H : Inputs) :
    FoldAt rdE P.par.S D.d7 (words2 P sentU d0 V.r1 H) := by
  obtain ⟨l7, c7⟩ := S.at7 u
  have hn : Notes P d0 V.r1 D.d7.loc := ⟨by rw [l7]; rfl, by rw [l7]; rfl⟩
  have hO : D.d7.loc.oOmega = d0.st.oracles.size + 2 := by rw [l7]; rfl
  refine foldEq_of_col P.par.S _ _ _ _ fun j hj => ?_
  have e := omU_at S.facts d0 V.r1 H hn j hj
  unfold omegaOf
  rw [c7, hO]
  exact e

/-- **The two rows that "SPLIT" lays hold of the honest words**, where the scalar that it is shown
is the honest one. x, y: the rows; each group's list behind is its list in front with the row behind
it. Nothing is asked of what the two sendings showed, nor of the committed table. -/
theorem split_rows_say (hP : PlanFacts P.par P.codes sentU layO)
    {r1 r2a r2b r4 r5a r5b r7 r8 : Fmt.RoundView} {cols : List (Nat × List UInt64)}
    {rs3 rs6 : List Fmt.RoundView} {d1 d2 d3 d4 d5 d6 d7 d8 : St} {x2 x5 : DState (Array Nat)}
    {ids2 ids5 : Array Nat}
    (h : Returned P sentU d0 r1 r2a r2b r4 r5a r5b r7 r8 cols rs3 rs6
      d1 d2 d3 d4 d5 d6 d7 d8 x2 x5 ids2 ids5) (H : Inputs)
    (hmu : r8.vals = [.e (Slice.ofE (muRun P d0 r1 r7 H))]) :
    ∃ x y, rowsOn d8 d7.loc.gOmega = rowsOn d7 d7.loc.gOmega ++ [x] ∧
      rowsOn d8 d7.loc.gU = rowsOn d7 d7.loc.gU ++ [y] ∧
      Means.Says rdE d8.st x (words2 P sentU d0 r1 H) ∧
      Means.Says rdE d8.st y (words2 P sentU d0 r1 H) := by
  have hlin := hP.lin
  obtain ⟨w2, w0, w1⟩ := withOmega_two hP.two
  have sO : (parO P).sent = withOmega P.par.S := parK1_sent P 5 _ _
  have hszO : 1 < (parO P).sent.size := by rw [sO, w2]; omega
  have hshO0 : shapeAt (parO P) 0 = P.par.S.omega :=
    (shapeAt_of_get (parO P) 0 ⟨P.par.S.omega, P.par.S.omegaLeafClass⟩ (by rw [sO]; exact w0)).1
  have hshO1 : shapeAt (parO P) 1 = P.par.S.sharedSplit :=
    (shapeAt_of_get (parO P) 1 ⟨P.par.S.sharedSplit, P.par.S.sharedSplitLeafClass⟩
      (by rw [sO]; exact w1)).1
  have at7 : Seated d7.st P.codes P.par.S d7.loc := by
    obtain ⟨x, hx, hs, _⟩ := h.o7.omega
    obtain ⟨y, hy, hs', _⟩ := h.u7.u
    exact ⟨h.c7, h.o7.apartOU, ⟨x, hx, hs⟩, ⟨y, hy, hs'⟩, by rw [← h.c7]; exact h.u7.lay⟩
  have hP7 : ∀ T, Grows d7.st T →
      Law.Placed T P.par.S d7.loc (linLayOmega d7.st.codes P.par.S) := fun T g => by
    rw [h.c7]
    exact placed_of_seated (at7.grows g) (linOk_of hP)
  have lO7 : d7.loc.oOmega = d0.st.oracles.size + 2 := by rw [h.l7]; rfl
  have lS7 : d7.loc.oSp = d0.st.oracles.size + 2 + 1 := by rw [h.l7]; rfl
  have lZ7 : d7.loc.zFd = drawn r7 := by rw [h.l7]; rfl
  have hn : Notes P d0 r1 d7.loc := ⟨by rw [h.l7]; rfl, by rw [h.l7]; rfl⟩
  obtain ⟨row, x, G, kappa, d₁, d₂, hf, hx, hG, hok, hk, h2, h3⟩ :=
    split_inv P.par d7 d8 r8 hP.two h.k8
  have hne : d7.loc.gOmega ≠ d7.loc.gU := by
    simp only [ok, splitL, List.all_cons, Bool.and_eq_true, bne_iff_ne] at hok
    exact hok.1
  have g1 := VerifiableInference.Desc.Ground.takeMaskP_grows d7 d₁ _ _ hk
  -- (fold)'s own row
  have hrow : Means.Says rdE d₁.st row (words2 P sentU d0 r1 H) :=
    (foldMeansW rdE d₁.st P.par.S d7.loc _ row hf (hP7 _ g1) _).2
      (foldEq_of_col P.par.S _ _ _ _ fun j hj => by
        have e := omU_at hP d0 r1 H hn j hj
        unfold omegaOf
        rw [h.c7, lO7]
        exact e)
  -- the scalar
  have hval : rdE.val (E.ofTriple x) =
      muVal rdE d₁.st row G.members d7.loc.oSp kappa (words2 P sentU d0 r1 H) := by
    obtain ⟨d₁', hk', hA, _⟩ := take_first P.par d7 hP.two h.f8
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hk.symm.trans hk'))
    obtain ⟨GO, hGO, _, _, _, hmem⟩ := h.f8.gO
    obtain rfl : G = GO := Option.some.inj (hG.symm.trans hGO)
    obtain ⟨xS, hxS, hsS, _, hpS⟩ := h.f8.sp
    obtain ⟨ms1, _⟩ := mask_first d7.st d7.loc.oSp xS P.par.S.sharedSplit hxS hsS hpS h.f8.free
    have hx' : x = Slice.ofE (muRun P d0 r1 r7 H) := by
      have e := hx.symm.trans hmu
      simpa using e
    have hsh := (VerifiableInference.Desc.Own.linFits_iff P.codes P.par.S).1 hlin
    have hSp : VerifiableInference.Desc.Own.SplitMessageFits P.par.S.sharedSplit
        P.par.S.sharedMaskCode := by
      rcases hsh.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with e | e
      · rw [hP.two] at e
        cases e
      · exact e
    rw [muVal_formula rdE d₁.st P.par.S d7.loc _ row G.members 0 _ hf (hP7 _ g1)
      (contains_of hmem _ (by simp))
      (not_contains_of hmem _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨Ne.symm h.f8.apartOU, Ne.symm h.f8.apartU⟩))
      (Nat.lt_of_lt_of_le h.f8.sp.lt (size_grows _ _ g1))
      (by
        unfold Means.tableSize
        rw [hA.has_eq, ms1, if_pos rfl]
        exact Nat.two_pow_pos _)]
    rw [h.c7, lZ7, hx']
    have e := mu_chain H.w₀ d0.st.oracles.size (d0.st.oracles.size + 2) (parU P sentU) (parO P)
      (rowsU P d0 r1 H) P.codes P.par.S (psiLoRun P r1) ((drawn r7).map rdE.val)
      (uHon P.par.S.fold (wRun P d0 r1) H.Rw) H.cOmega H.cSp d7.loc hlin hszO hshO0 hshO1 lO7 lS7 0
      (by rw [Nat.zero_mod]; exact Nat.pos_of_ne_zero hSp.2.1)
    refine Eq.trans ?_ e.symm
    show Slice.readE (E.ofTriple (Slice.ofE (muRun P d0 r1 r7 H))) = _
    rw [Slice.readE_ofTriple, Slice.toE_ofE]
    rfl
  obtain ⟨sa, sb⟩ := says_split rdE d₁.st row G.members d7.loc.oSp kappa (E.ofTriple x) _ hval hrow
  refine ⟨_, _, ?_, ?_, (Means.says_addRowP rdE h3 _ _).2 ((Means.says_addRowP rdE h2 _ _).2 sa),
    (Means.says_addRowP rdE h3 _ _).2 ((Means.says_addRowP rdE h2 _ _).2 sb)⟩
  · rw [rowsOn_addRowP_other d₂ d8 _ _ _ h3 hne.symm, rowsOn_addRowP_same d₁ d₂ _ _ h2,
      rowsOn_takeMaskP d7 d₁ _ _ _ hk]
  · rw [rowsOn_addRowP_same d₂ d8 _ _ h3, rowsOn_addRowP_other d₁ d₂ _ _ _ h2 hne,
      rowsOn_takeMaskP d7 d₁ _ _ _ hk]

/-- **Behind "SPLIT" the last row on o_u's group holds of the honest words** (RowsU), where the
scalar shown is the honest one: the list has just one row more than behind "LOC". -/
theorem Public8.foldU_behind8 (S : Public8 P sentU layO d0) (u : To8 P sentU d0 V D)
    (hM : ShownMu P d0 V H) :
    RowsU rdE (P.par.S.fold.index.answers + P.par.S.fold.columns) 1 D.d8
        (words2 P sentU d0 V.r1 H) ∧
      (rowsOn D.d8 D.d8.loc.gU).length =
        P.par.S.fold.index.answers + P.par.S.fold.columns + 1 := by
  obtain ⟨x, y, _, hy, _, sy⟩ := split_rows_say S.facts (S.returned u) H hM
  have hl := (Law.onward_split P.par D.d7 D.d8 V.r8 S.facts.two u.k8).2
  refine ⟨fun r hr => ?_, (S.rows8 u).1⟩
  rw [hl, hy, List.drop_left' (S.rows7 u.front).1] at hr
  obtain rfl : r = y := by simpa using List.mem_of_mem_take hr
  exact sy

/-- **Behind "SPLIT" the one row on o_omega's group holds of the honest words** (RowsO), where the
scalar shown is the honest one. -/
theorem Public8.foldOmega_behind8 (S : Public8 P sentU layO d0) (u : To8 P sentU d0 V D)
    (hM : ShownMu P d0 V H) :
    RowsO rdE 0 1 D.d8 (words2 P sentU d0 V.r1 H) ∧
      (rowsOn D.d8 D.d8.loc.gOmega).length = 1 := by
  obtain ⟨x, y, hx, _, sx, _⟩ := split_rows_say S.facts (S.returned u) H hM
  have hl := (Law.onward_split P.par D.d7 D.d8 V.r8 S.facts.two u.k8).2
  have h0 : rowsOn D.d7 D.d7.loc.gOmega = [] :=
    List.eq_nil_of_length_eq_zero (S.rows7 u.front).2
  refine ⟨fun r hr => ?_, (S.rows8 u).2⟩
  rw [hl, hx, h0] at hr
  obtain rfl : r = x := by simpa using List.mem_of_mem_drop (List.mem_of_mem_take hr)
  exact sx

end Desc.K14.Honest

#print axioms Desc.K14.Honest.rowsOn_say
#print axioms Desc.K14.Honest.stretch_say
#print axioms Desc.K14.Honest.smpSay_of_met
#print axioms Desc.K14.Honest.wOf_notes
#print axioms Desc.K14.Honest.sends_of
#print axioms Desc.K14.Honest.fold_at
#print axioms Desc.K14.Honest.omU_at
#print axioms Desc.K14.Honest.nearU_at
#print axioms Desc.K14.Honest.recRow_at
#print axioms Desc.K14.Honest.dot_at
#print axioms Desc.K14.Honest.Public8.notes1
#print axioms Desc.K14.Honest.Public8.omU_behind1
#print axioms Desc.K14.Honest.Public8.nearU_behind1
#print axioms Desc.K14.Honest.Public8.recRow_behind1
#print axioms Desc.K14.Honest.smp_new
#print axioms Desc.K14.Honest.Public8.sample_behind2
#print axioms Desc.K14.Honest.Public8.sample_behind5
#print axioms Desc.K14.Honest.AtU.notes
#print axioms Desc.K14.Honest.Public8.recG_behind3
#print axioms Desc.K14.Honest.Public8.loc_behind4
#print axioms Desc.K14.Honest.Public8.fold_behind7
#print axioms Desc.K14.Honest.split_rows_say
#print axioms Desc.K14.Honest.Public8.foldU_behind8
#print axioms Desc.K14.Honest.Public8.foldOmega_behind8
