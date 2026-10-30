-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/PointStepBack.lean: THE TIE AT "LIN point": THE STEP BACK FROM (Eval): the
premise s4a of point_leadsB_closed (Johnson/Desc/Sound/PointAtK14Closed.lean), to the letter but
for one premise of s4a's ("no mark": handed and not spent here):
AN INSTANCE, at the table's letters, of kind K13's files' claim_of_eval_held
(Johnson/Desc/K13/Law/StepBackHeld.lean) and vec_of_words (Johnson/Desc/K13/Law/VecWords.lean),
which stand in those files' own terms. One structure, four theorems.
hg IS FENCED BY Oc TOO.
It
stands above the table's files' PointAtK14Closed.lean, and their PointAtK14All.lean calls
it.

OBJECT   the letters of the shared table's tie at "LIN point"; no block's text.
USER     s4a of point_leadsB_closed: through s4a_all (Johnson/Desc/Sound/PointAtK14All.lean).
FIELD    shared_joint_count (Johnson/Goal/Skeleton/ProofFile.lean), through block 1's clause.

WHAT SHAPES THIS FILE: (i) THE WORDS READ WHAT WAS HANDED: rg₁ : P₁ → Wit →
Words GE (not ONE function for all statements inside the promise: the words
that a witness gives go through a record's shapes and seats: at a fixed letter the filling that is
meant has no member, as at the last chain's row 0, one storey lower) · (ii) hvec
IS FENCED BY Oc · (iii) hvec_paid: **hvec IS NO PREMISE** at rg₁ p w := wordsOn (stOf
p) (tabP p w) · vec := vecAt lay₀ ‹W's member's shape›: CLOSED TERMS over two readers (stOf: the
first
chain's statement off what was handed; tabP: the witness's table of a number of that statement): it
is exchanged for WSits: SEVEN PUBLIC FACTS on the handed record against the plan · s4a_all: s4a from
these.

THE FILLING: laid : P₁ → Option EvalAt: a reader, a letter · ev p _ w := there is such a record, and
(Eval) says its claim of rg₁ p w · claimM p _ w := there is such a record, and its row on the matrix
is true of the matrix that the witness's cells hold (matC w.cells) and of rg₁ p w's mask entries.
WHERE THE
READER GIVES NOTHING BOTH ARE FALSE, not free.
  WSits cs arr xW lay₀ stOf tabP p D: the record's statement is the reader's · its codes are the
  plan's · W's number bears a message of W's member's shape · the witness's table at W's number is
  THE ONE ACCESSOR at W's member's shape, number and seat (at tabAt: by unfolding,
  from "W's
    number has W's member's seat") · W's layout is the plan's · the codes' lengths are powers of two
    · the shape's code is in the list.
WHAT IT SPENDS: the promise on the table · Oc (through hOk, hW) · (Eval) · VIs · "what was handed
stays". IDLE: the index masks' pin.
WHAT STAYS OF s4a_all, BY NAME: two equations of letters (hev, hcl) · hOk (Oc holds EvalLaid: the
filling's) · hW (Oc holds WSits: seven public facts: the filling's; NO MEMBER IS SHOWN: each is a
test with code on record and plan but "tab", which is an unfolding) · hg (a definition of gOf) ·
htab (the
tables read the witness's messages and pads alone) · HeldTie (two members are theorems).

Limits. As PointAtK14Closed.lean's. A theorem under premises at free letters can be idle.

-/
import Johnson.Desc.Sound.PointAtK14Closed
import Johnson.Desc.K13.Law.StepBackHeld
import Johnson.Desc.K13.Law.VecWords

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack (sigOf pMain)
open VerifiableInference.Desc (Block Strs Wit FileDescription)
open VerifiableInference.Desc.Sound (Frame Piece onQ₂ promQ actQ shIt ownItem stepPt strsOf
    strsOfAct OcReadsBelow
  pinJT SitsAt decodesOf pinWOf extS wTab MsgT Mem Sending decAtRec decGuard noColl_of_promise
      pinT_extS
  msg_extS_one pad_extS_one toMsgT msgsOf msgs_forth InMsg)
open VerifiableInference.Desc.Shared (NumbersS MeaningS PromMeaning ItemS PromS promsAt)
open VerifiableInference.Desc.K13.Law (EvalAt witOf matBy vecAt vec_of_words)

variable {P₁ Xi Cells Tok : Type} {F : Frame}

/-- Inside the promise on the table, at the guarded decoder: the decoder gives some U, and the cells
that the table's extractor lays at block 1 are held U. -/
theorem held_of_promise (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : Nat → Nat → Nat)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₂ : List Mem) (c₀ : Cells) (N : NumbersS) (split : Bool) (p : Par) (err₂ eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (held : ((ixOf2 p.S.fold err₂ eM rank).Row × Fin p.S.fold.index.code.ell → GE) → Option Cells)
    (s : St) (y : Strs) (w : Wit Cells Tok MsgT) (h : decodesOf (decK p err₂ eM rank held) s y) :
    ∃ U, dcdAt p err₂ eM rank y.cell (recAt p err₂ eM rank s) = some U ∧
      held U = some (extS cs G arr smp₂ ms₂ (decK p err₂ eM rank held) c₀ N split 1 s y w).cells :=
          by
  obtain ⟨hnc, hds⟩ := noColl_of_promise (collAt p err₂ eM rank) (dcdAt p err₂ eM rank) held
    (recAt p err₂ eM rank) s y h
  obtain ⟨U, hU⟩ := Option.isSome_iff_exists.1 hds
  have hpin : decK p err₂ eM rank held y.cell s =
      some (extS cs G arr smp₂ ms₂ (decK p err₂ eM rank held) c₀ N split 1 s y w).cells :=
    pinT_extS cs G arr smp₂ ms₂ (decK p err₂ eM rank held) c₀ N split s y w h
  have e : decK p err₂ eM rank held y.cell s = held U := by
    show decGuard (collAt p err₂ eM rank) (dcdAt p err₂ eM rank) held y.cell (recAt p err₂ eM rank
        s) = held U
    unfold decGuard
    rw [if_neg hnc]
    exact congrArg (fun o => Option.bind o held) hU
  exact ⟨U, hU, e.symm.trans hpin⟩

/-- **The step back from (Eval): the premise s4a of point_leadsB_closed, to the letter.** The words
read what was handed; the tie of the vector is asked inside Oc. -/
theorem s4a_paid (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : Nat → Nat → Nat) (xW : Mem)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₂ : List Mem) (c₀ : Cells) (vec : MsgT → Nat → GE)
    (rg₁ : P₁ → Wit Cells Tok MsgT → Words GE) (P : P14) (b1 : Block St Unit)
    (base : Nat) (d : RDT)
    (ext : (P₁ × St) × F.E.Str → Tr (uLT (ckP .two) [d]) → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
    (err : Err (uLT (ckP .two) [d]))
    (N : NumbersS) (Mg : MeaningS St P₁ (Wit Cells Tok MsgT)) (Pm : PromMeaning St)
    (Oc : P₁ → Strs → Prop) (split : Bool)
    (f : Piece (ckP .two) F (P₁ × St) Unit (Wit Cells Tok MsgT))
    (r : List (Piece (ckP .two) F (P₁ × St) Unit (Wit Cells Tok MsgT)))
    (gOf : P₁ → Nat → GE) (err₂ eM : Nat)
    (rank : ((Fin P.par.S.fold.index.v → Bool) →
      Fin (P.par.S.fold.index.code.r + P.par.S.fold.index.code.ell) → GE) → Nat)
    (held : ((ixOf2 P.par.S.fold err₂ eM rank).Row × Fin P.par.S.fold.index.code.ell → GE) →
      Option Cells)
    (hTP : Pm.tablePromise = decodesOf (decK P.par err₂ eM rank held))
    -- the two letters filled
    (laid : P₁ → Option EvalAt) (matC : Cells → Nat → Nat → GE)
    (hev : Mg.ev = fun p _ w => ∃ D, laid p = some D ∧ OnBytes.Means.Says OnBytes.Model.Reading.gl
        D.st D.r (rg₁ p w))
    (hcl : Mg.claimM = fun p _ w => ∃ D, laid p = some D ∧
      VerifiableInference.Desc.K13.Law.Holds OnBytes.Model.Reading.gl
        (witOf (matBy (nR := P.par.S.matrixRows) P.par.S.kCol (matC w.cells)) (rg₁ p w)) D.row)
    -- the ties
    (hOk : ∀ p y D, Oc p y → laid p = some D → D.Ok P.par.S)
    (hg : ∀ p y' D, Oc p y' → laid p = some D → ∀ y < P.par.S.matrixRows,
      gOf p y = (D.row.g.map fun t => OnBytes.Model.Reading.gl.val (t.entry y)).sum)
    (hvec : ∀ p y D w, Oc p y → laid p = some D → ∀ c < 2 ^ P.par.S.kCol,
      rg₁ p w D.w .main (D.lay.index c) = vec (wTab cs arr xW w) c)
    (hrg : ∀ p (w w' : Wit Cells Tok MsgT), (∀ n, w'.msg n = w.msg n) → (∀ j t, w'.pad j t = w.pad j
        t) →
      rg₁ p w' = rg₁ p w)
    (hH : HeldTie P.par err₂ eM rank held matC) :
    ∀ a τ b w, onQ₂ N Pm Oc split f (liftedPiece b1 base d ext err :: r) 1 a →
      (liftedPiece b1 base d ext err).ior.red.out a τ = some b → ownItem N Mg .ev b w →
      VIs P.par.S (gOf a.1.1) (TabX2 P.par err₂ eM rank (tabOf a.2) a.1.2.loc.key)
        (vec (wTab cs arr xW w)) → ownItem N Mg .pinI b w →
      ownItem N Mg .claimM a (extS cs G arr smp₂ ms₂ (decK P.par err₂ eM rank held) c₀ N split 1
        ((actQ N f (liftedPiece b1 base d ext err :: r) 1).2 a).1 (strsOfAct F ((actQ N f
            (liftedPiece b1 base d ext err :: r) 1).2 a)) w) := by
  intro a τ b w hon hb hE hvi _
  have hK : b.1.1 = a.1.1 := lifted_handed b1 base d ext err a τ b hb
  have h1 : Pm.tablePromise a.1.2 (strsOfAct F ((actQ N f (liftedPiece b1 base d ext err :: r) 1).2
      a)) :=
    hon.1 .tablePromise (by rw [promsAt_one]; exact List.mem_cons_self)
  rw [hTP] at h1
  obtain ⟨U, hU, hheld⟩ := held_of_promise cs G arr smp₂ ms₂ c₀ N split P.par err₂ eM rank held
      a.1.2
    (strsOfAct F ((actQ N f (liftedPiece b1 base d ext err :: r) 1).2 a)) w h1
  rw [tabOf_cells a.2] at hvi
  have hvi' : VIs P.par.S (gOf a.1.1) (TabX2 P.par err₂ eM rank
      (colsOf (strsOfAct F ((actQ N f (liftedPiece b1 base d ext err :: r) 1).2 a)).cell)
          a.1.2.loc.key) (vec (wTab cs arr xW w)) := hvi
  have hE' : Mg.ev b.1.1 (strsOf F b.2) w := hE
  rw [hK, hev] at hE'
  obtain ⟨D, hD, hS⟩ := hE'
  have e1 : rg₁ a.1.1 (extS cs G arr smp₂ ms₂ (decK P.par err₂ eM rank held) c₀ N split 1 a.1.2
      (strsOfAct F ((actQ N f (liftedPiece b1 base d ext err :: r) 1).2 a)) w) = rg₁ a.1.1 w :=
    hrg a.1.1 w _ (fun n => msg_extS_one cs G arr smp₂ ms₂ (decK P.par err₂ eM rank held) c₀ N split
        _ _ w n)
      (fun j t => pad_extS_one cs G arr smp₂ ms₂ (decK P.par err₂ eM rank held) c₀ N split _ _ w j
          t)
  have key := (claim_of_eval_held P.par err₂ eM rank held matC hH _ a.1.2 U hU _ hheld D
    (hOk a.1.1 _ D hon.2 hD) (rg₁ a.1.1 w) (gOf a.1.1) (vec (wTab cs arr xW w)) (hg a.1.1 _ D hon.2
        hD)
    (hvec a.1.1 _ D w hon.2 hD) hvi').1 hS
  rw [← e1] at key
  show Mg.claimM a.1.1 (strsOf F a.2) _
  rw [hcl]
  exact ⟨D, hD, key⟩

/-- **W sits as the plan says**: seven public facts on the handed record against the plan. -/
structure WSits (cs : OnBytes.Codes) (arr : Nat → Nat → Nat) (xW : Mem) (lay₀ : VectorLay)
    (stOf : P₁ → Statement) (tabP : P₁ → Wit Cells Tok MsgT → Nat → MsgT) (p : P₁) (D : EvalAt) :
        Prop where
  st : D.st = stOf p
  codes : D.st.codes = cs
  there : ∃ x, D.st.oracles[D.w]? = some x ∧ x.shape = (xW.1.l.get xW.2).1
  tab : ∀ w, tabP p w D.w = w.tab cs (xW.1.l.get xW.2).1 (arr (xW.1.seat xW.2).1 (xW.1.seat xW.2).2)
    (xW.1.seat xW.2).1 (xW.1.seat xW.2).2
  lay : D.lay = lay₀
  lengths : cs.lengthsOk = true
  code : (xW.1.l.get xW.2).1.code < cs.base.size

/-- **The tie of the vector, paid**: at the words that the tables give at the handed statement, and
the vector read off W's member's table under the plan's layout. -/
theorem hvec_paid (cs : OnBytes.Codes) (arr : Nat → Nat → Nat) (xW : Mem) (lay₀ : VectorLay) (Sh :
    LinShape)
    (stOf : P₁ → Statement) (tabP : P₁ → Wit Cells Tok MsgT → Nat → MsgT) (Oc : P₁ → Strs → Prop)
    (laid : P₁ → Option EvalAt) (hOk : ∀ p y D, Oc p y → laid p = some D → D.Ok Sh)
    (hW : ∀ p y D, Oc p y → laid p = some D → WSits cs arr xW lay₀ stOf tabP p D) :
    ∀ p y D w, Oc p y → laid p = some D → ∀ c < 2 ^ Sh.kCol,
      wordsOn (stOf p) (tabP p w) D.w .main (D.lay.index c) = vecAt lay₀ (xW.1.l.get xW.2).1 (wTab
          cs arr xW w) c := by
  intro p y D w ho hD c hc
  have W := hW p y D ho hD
  obtain ⟨x, hx, hsh⟩ := W.there
  have hM : ∀ row place, row < x.shape.mainRows →
      place < (D.st.codes.base.getD x.shape.code default).ell →
      wTab cs arr xW w false row place = tabP p w D.w false row place := by
    intro row place h1 h2
    rw [W.tab w]
    rw [hsh] at h1
    rw [W.codes, hsh] at h2
    refine (msgs_forth cs xW.1.l xW.1.seat arr w xW.2 false row place ?_).symm
    unfold InMsg
    rw [if_neg (by decide)]
    exact ⟨h1, h2⟩
  have hM0 : ∀ row place, ¬ row < x.shape.mainRows → wTab cs arr xW w false row place = 0 := by
    intro row place hn
    rw [hsh] at hn
    show toMsgT cs xW.1.l xW.2 (msgsOf cs xW.1.l xW.1.seat arr w xW.2) false row place = 0
    unfold toMsgT
    rw [if_neg (by decide), dif_neg (fun h => hn h.1)]
  have key := vec_of_words Sh D (hOk p y D ho hD) (tabP p w) x hx (by rw [W.codes]; exact W.lengths)
    (by rw [W.codes, hsh]; exact W.code) (wTab cs arr xW w) hM hM0 c hc
  rw [W.st, W.lay, hsh] at key
  rw [W.lay]
  exact key

/-- **s4a, with the tie of the vector paid.** -/
theorem s4a_all (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : Nat → Nat → Nat) (xW : Mem)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₂ : List Mem) (c₀ : Cells) (lay₀ : VectorLay)
    (stOf : P₁ → Statement) (tabP : P₁ → Wit Cells Tok MsgT → Nat → MsgT) (P : P14) (b1 : Block St
        Unit)
    (base : Nat) (d : RDT)
    (ext : (P₁ × St) × F.E.Str → Tr (uLT (ckP .two) [d]) → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
    (err : Err (uLT (ckP .two) [d]))
    (N : NumbersS) (Mg : MeaningS St P₁ (Wit Cells Tok MsgT)) (Pm : PromMeaning St)
    (Oc : P₁ → Strs → Prop) (split : Bool)
    (f : Piece (ckP .two) F (P₁ × St) Unit (Wit Cells Tok MsgT))
    (r : List (Piece (ckP .two) F (P₁ × St) Unit (Wit Cells Tok MsgT)))
    (gOf : P₁ → Nat → GE) (err₂ eM : Nat)
    (rank : ((Fin P.par.S.fold.index.v → Bool) →
      Fin (P.par.S.fold.index.code.r + P.par.S.fold.index.code.ell) → GE) → Nat)
    (held : ((ixOf2 P.par.S.fold err₂ eM rank).Row × Fin P.par.S.fold.index.code.ell → GE) →
      Option Cells)
    (hTP : Pm.tablePromise = decodesOf (decK P.par err₂ eM rank held))
    (laid : P₁ → Option EvalAt) (matC : Cells → Nat → Nat → GE)
    (hev : Mg.ev = fun p _ w => ∃ D, laid p = some D ∧
      OnBytes.Means.Says OnBytes.Model.Reading.gl D.st D.r (wordsOn (stOf p) (tabP p w)))
    (hcl : Mg.claimM = fun p _ w => ∃ D, laid p = some D ∧
      VerifiableInference.Desc.K13.Law.Holds OnBytes.Model.Reading.gl
        (witOf (matBy (nR := P.par.S.matrixRows) P.par.S.kCol (matC w.cells)) (wordsOn (stOf p)
            (tabP p w))) D.row)
    (hOk : ∀ p y D, Oc p y → laid p = some D → D.Ok P.par.S)
    (hg : ∀ p y' D, Oc p y' → laid p = some D → ∀ y < P.par.S.matrixRows,
      gOf p y = (D.row.g.map fun t => OnBytes.Model.Reading.gl.val (t.entry y)).sum)
    (hW : ∀ p y D, Oc p y → laid p = some D → WSits cs arr xW lay₀ stOf tabP p D)
    (htab : ∀ p (w w' : Wit Cells Tok MsgT), (∀ n, w'.msg n = w.msg n) → (∀ j t, w'.pad j t = w.pad
        j t) →
      tabP p w' = tabP p w)
    (hH : HeldTie P.par err₂ eM rank held matC) :
    ∀ a τ b w, onQ₂ N Pm Oc split f (liftedPiece b1 base d ext err :: r) 1 a →
      (liftedPiece b1 base d ext err).ior.red.out a τ = some b → ownItem N Mg .ev b w →
      VIs P.par.S (gOf a.1.1) (TabX2 P.par err₂ eM rank (tabOf a.2) a.1.2.loc.key)
        (vecAt lay₀ (xW.1.l.get xW.2).1 (wTab cs arr xW w)) → ownItem N Mg .pinI b w →
      ownItem N Mg .claimM a (extS cs G arr smp₂ ms₂ (decK P.par err₂ eM rank held) c₀ N split 1
        ((actQ N f (liftedPiece b1 base d ext err :: r) 1).2 a).1 (strsOfAct F ((actQ N f
            (liftedPiece b1 base d ext err :: r) 1).2 a)) w) :=
  s4a_paid cs G arr xW smp₂ ms₂ c₀ (vecAt lay₀ (xW.1.l.get xW.2).1) (fun p w => wordsOn (stOf p)
      (tabP p w)) P b1 base d ext err
    N Mg Pm Oc split f r gOf err₂ eM rank held hTP laid matC hev hcl hOk hg
    (hvec_paid cs arr xW lay₀ P.par.S stOf tabP Oc laid hOk hW)
    (fun p w w' h1 h2 => by
      show wordsOn (stOf p) (tabP p w') = wordsOn (stOf p) (tabP p w)
      rw [htab p w w' h1 h2]) hH

end Desc.K14.Law
