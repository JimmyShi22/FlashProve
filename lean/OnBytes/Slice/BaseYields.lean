-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BaseYields.lean: the program's own base case of the proximity test, taken apart on the
view of the two written rounds.

The program is the Lean verifier in OnBytes/. It is made of blocks (OnBytes/Iop/). The last block of
its proximity test, `baseVerify` (OnBytes/Iop/Prox.lean), receives the masking word's target, closes
the round that draws one element, receives two messages and two tails, makes its first named test,
closes the round of positions, reads the opened columns and makes its second named test. A named
test (`Blk.check`, `Blk.checkOnView`) does not stop the run: the first one that fails is noted in
the context's field `failed`. This file says what a run of that block is, in two steps.

 `baseVerify_run`, on words. Let the block run through from a context whose next two rounds are
   the view of two written rounds, and let no named test have failed at the end. Then the first
   round sent one element and drew one; the second sent the two messages and the two tails, of
   their codes' lengths; the equality of words of the first test holds; the columns were read by
   one call of `Blk.readOpened`, whose run is shown; and at every listed position the two
   equalities of words of the second test hold. No named test had failed at the start, and the
   run takes these two rounds and no more.
 `baseVerify_sem`, in the field. The same run gives the library's decision `Cb.LdwAccept` at the
   values of the two written rounds (OnBytes/Slice/BaseEqs.lean: `accept_of_eqs`). This is the
   decision towards whose failure OnBytes/Slice/Base.lean takes the two rounds off.

The case. The masking oracle came in an earlier message, and the block's complex of single rows
(`SingleRows`) is one main row and one mask row, without kept rows.

What is asked, as hypotheses with names.
 `htie`    the symbols that the program has read are those of the word and of the masking word
           (`BaseTie`).
 `hx1`, `hxc`, `hxd`   the claim is the program's claim, read in the field.
 `hcd`, `hC`, `hZ`    the two codes of the program's statement are the stage's.
 `h0`, `g0`, `ha`, `hz`, `hB`   each of the stage's tables has one row; each code has at most 2^32
           positions; the second round draws the stage's number of positions and nothing else.

Main definitions: `BaseTie`.
Main theorems: `recvEsInto_inv`, `recvVectors_inv`, `baseVerify_run`, `baseVerify_sem`.
Not claimed. That the named hypotheses hold. Nothing on the dry run (`Blk.rounds`: all values are
zero, and the run only describes the block's rounds). Nothing on a masking oracle that is received
in the block itself.
-/
import OnBytes.Iop.Prox
import OnBytes.Iop.OpenLaws
import OnBytes.Slice.ProgField
import OnBytes.Slice.ProgCodes
import OnBytes.Slice.BaseEqs
import OnBytes.Slice.BlkRead
import OnBytes.Iop.DotLaws
import Fmt.Rules6Laws

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb _root_.Run

/-! ## Calls that receive elements -/

/-- Nothing changes: a case of `Blk.SameBut`. -/
theorem sameBut_refl (c : Ctx) : Blk.SameBut c c := by
  constructor <;> rfl

/-- What two calls in a row leave as it was. -/
theorem sameBut_trans {a b c : Ctx} (h1 : Blk.SameBut a b) (h2 : Blk.SameBut b c) :
    Blk.SameBut a c := by
  cases h1
  cases h2
  constructor <;> simp_all

/-- One step of the call that receives several elements, as an equation between functions of the
elements already received. -/
theorem recvEsInto_succ_fun (n : ℕ) :
    Blk.recvEsInto (n + 1) = fun acc => Blk.recvE >>= fun x => Blk.recvEsInto n (acc.push x) :=
  rfl

/-- Outside the dry run, the elements that the call receives are the next items of the first pending
round. -/
theorem recvEsInto_inv : ∀ (n : ℕ) (acc out : Array E) (c c' : Ctx) (r : Fmt.RoundView)
    (rest : List Fmt.RoundView), c.ch.dry = false → c.ch.pending = r :: rest →
    (Blk.recvEsInto n acc).Yields c out c' →
    ∃ (xs : List E) (vs : List Fmt.ItemValue), xs.length = n ∧ out = acc ++ xs.toArray ∧
      r.vals = xs.map (fun x => Fmt.ItemValue.e x.triple) ++ vs ∧
      c'.ch.pending = { r with vals := vs } :: rest ∧
      Blk.SameBut c c'
  | 0, acc, out, c, c', r, rest, _, hp, h => by
    obtain ⟨rfl, rfl⟩ := (Blk.yields_pure _ _ _ _).1 h
    exact ⟨[], r.vals, rfl, by simp, rfl, hp, sameBut_refl _⟩
  | n + 1, acc, out, c, c', r, rest, hd, hp, h => by
    rw [congrFun (recvEsInto_succ_fun n) acc] at h
    obtain ⟨x, c1, h1, h2⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨r1, t1, v1, a1, a2, a3, s1⟩ := Blk.recvE_inv x c c1 hd h1
    rw [hp] at a1
    obtain ⟨rfl, rfl⟩ := List.cons.inj a1
    obtain ⟨xs, vs, b1, b2, b3, b4, s2⟩ :=
      recvEsInto_inv n (acc.push x) out c1 c' _ _ (s1.dry.trans hd) a3 h2
    refine ⟨x :: xs, vs, congrArg (· + 1) b1, ?_, ?_, b4, sameBut_trans s1 s2⟩
    · rw [b2]
      simp
    · rw [a2]
      exact congrArg (Fmt.ItemValue.e x.triple :: ·) b3

/-- Outside the dry run, the vectors that the call receives are the next items of the first pending
round. -/
theorem recvVectors_inv : ∀ (ns : List ℕ) (out : List (Array E)) (c c' : Ctx) (r : Fmt.RoundView)
    (rest : List Fmt.RoundView), c.ch.dry = false → c.ch.pending = r :: rest →
    (recvVectors ns).Yields c out c' →
    ∃ (xss : List (List E)) (vs : List Fmt.ItemValue), xss.map List.length = ns ∧
      out = xss.map List.toArray ∧ r.vals = xss.flatten.map (fun x => Fmt.ItemValue.e x.triple) ++ vs ∧
      c'.ch.pending = { r with vals := vs } :: rest ∧ Blk.SameBut c c'
  | [], out, c, c', r, rest, _, hp, h => by
    obtain ⟨rfl, rfl⟩ := (Blk.yields_pure _ _ _ _).1 h
    exact ⟨[], r.vals, rfl, rfl, rfl, hp, sameBut_refl _⟩
  | n :: ns, out, c, c', r, rest, hd, hp, h => by
    unfold recvVectors at h
    obtain ⟨v, c1, h1, h2⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨vs', c2, h3, h4⟩ := (Blk.yields_bind _ _ _ _ _).1 h2
    obtain ⟨rfl, rfl⟩ := (Blk.yields_pure _ _ _ _).1 h4
    obtain ⟨xs, w1, a1, a2, a3, a4, s1⟩ := recvEsInto_inv n #[] v c c1 r rest hd hp h1
    obtain ⟨xss, w2, b1, b2, b3, b4, s2⟩ :=
      recvVectors_inv ns vs' c1 _ _ _ (s1.dry.trans hd) a4 h3
    refine ⟨xs :: xss, w2, ?_, ?_, ?_, b4, sameBut_trans s1 s2⟩
    · rw [List.map_cons, a1, b1]
    · rw [List.map_cons, a2, b2]
      simp
    · have b3' : w1 = xss.flatten.map (fun x => Fmt.ItemValue.e x.triple) ++ w2 := b3
      rw [a3, b3', List.flatten_cons, List.map_append, List.append_assoc]

/-! ## Other calls -/

/-- A round of positions that was closed: it was closed, and the call returns the list made of its
draws. -/
private theorem closedPositions (name : String) (logN : ℕ) (pos : Positions) (more : List E)
    (c c' : Ctx) (h : (Blk.closePositions name logN).Yields c (pos, more) c') :
    ∃ d, (Blk.close name .positions).Yields c d c' ∧ pos = Positions.ofDraws logN d.poss := by
  unfold Blk.closePositions at h
  obtain ⟨d, c1, h1, h2⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨e, c2, h3, h4⟩ := (Blk.yields_bind _ _ _ _ _).1 h2
  obtain ⟨u, c3, h5, h6⟩ := (Blk.yields_bind _ _ _ _ _).1 h4
  obtain ⟨h7, e4⟩ := (Blk.yields_pure _ _ _ _).1 h6
  obtain ⟨_, e3⟩ := (Blk.yields_must _ _ _).1 h5
  have e2 : c2 = c1 := by
    unfold Blk.Yields Blk.outcome Blk.lastEntry at h3
    cases hl : c1.ch.last with
    | none =>
      rw [hl] at h3
      cases h3
    | some e' =>
      rw [hl] at h3
      exact (congrArg Prod.snd (Option.some.inj h3)).symm
  rw [e4, e3, e2]
  exact ⟨d, h1, congrArg Prod.fst h7⟩

/-- A named test changes nothing but the record of failed tests. -/
theorem check_frame (name : String) (b : Bool) (c c' : Ctx)
    (h : (Blk.check name b).Yields c () c') : c'.ch = c.ch ∧ c'.st = c.st ∧ c'.book = c.book := by
  unfold Blk.Yields Blk.outcome Blk.check at h
  split at h
  · cases Option.some.inj h
    exact ⟨rfl, rfl, rfl⟩
  · cases Option.some.inj h
    exact ⟨rfl, rfl, rfl⟩

/-- A list of lists with two given lengths has two members. -/
theorem two_of_lengths {xss : List (List E)} {a b : ℕ} (h : xss.map List.length = [a, b]) :
    ∃ x y, xss = [x, y] ∧ x.length = a ∧ y.length = b := by
  match xss, h with
  | [x, y], h =>
    have h1 := List.cons.inj h
    exact ⟨x, y, rfl, h1.1, (List.cons.inj h1.2).1⟩

/-- The elements among items that are all elements. -/
theorem sentOf_map_e : ∀ l : List E,
    Fmt.M1.sentOf (l.map fun x => Fmt.ItemValue.e x.triple) = l.map E.triple
  | [] => rfl
  | x :: l => congrArg (x.triple :: ·) (sentOf_map_e l)

/-! ## The run of the base case -/

/-- What a run of the program's base case on the view of the two written rounds gives if no named
test has failed at its end: what each round sent and drew, the equalities of both tests, and the
call that read the columns. The case: the masking oracle came in an earlier message, and the complex
is one main row and one mask row, without kept rows. -/
theorem baseVerify_run (R : SingleRows) (star lc : ℕ) (dL dB : PQ.RD) (mL : (wRound dL).Msg)
    (cL : (wRound dL).Chal) (mB : (wRound dB).Msg) (cB : (wRound dB).Chal) (rest : List Fmt.RoundView)
    (c c' : Ctx) (hd : c.ch.dry = false)
    (hp : c.ch.pending = PQ.rvSL (ckP .two) [dL, dB] (mL, cL, mB, cB, ()) ++ rest)
    (hm : R.masks = 1) (hk : R.keptRows = 0)
    (h : (baseVerify R (some star) lc).Yields c () c') (hf : c'.failed = none) :
    ∃ (code : Code) (tauS lam : E) (xs0 xs1 ys0 ys1 : List E) (c1 a : Ctx)
      (opened : Array (Array Column)) (y : Array E) (stars : Array Column),
      c.st.codes.base[R.code]? = some code ∧ baseShapeOk c.st R star = true ∧
      sentW dL mL = [tauS.triple] ∧ (rvOf dL mL cL).els = [lam.triple] ∧
      sentW dB mB = (xs0 ++ xs1 ++ (ys0 ++ ys1)).map E.triple ∧ xs0.length = code.ell ∧
      xs1.length = (c.st.codes.mask.getD R.maskCode default).ell ∧ ys0.length = code.r ∧
      ys1.length = (c.st.codes.mask.getD R.maskCode default).r ∧
      (R.c.fits (ceilLog2 code.ell) && R.d.size == 1 &&
        R.d.all fun x => x.size == (c.st.codes.mask.getD R.maskCode default).ell) = true ∧
      addE (R.c.dot (ceilLog2 code.ell) xs0.toArray) (inner (R.d.getD 0 #[]) xs1.toArray) =
        maddE tauS lam R.target ∧
      (Blk.readOpened ((singleRowsOracles R).push star)
        (Positions.ofDraws code.logN (rvOf dB mB cB).poss)).Yields a opened c' ∧
      a.ch.pending = rest ∧ a.ch.opened = c.ch.opened ∧ a.book = c.book ∧ a.ch.dry = false ∧
      (Blk.spendAsMask star).Yields c () c1 ∧ a.st = c1.st ∧ a.ch.firstTree = c.ch.firstTree ∧
      c.failed = none ∧ c'.ch.pending = rest ∧
      singleRowsSymbols R opened
        (Positions.ofDraws code.logN (rvOf dB mB cB).poss).all.size = some y ∧
      opened.back? = some stars ∧
      ∀ i, i < (Positions.ofDraws code.logN (rvOf dB mB cB).poss).all.size →
        symbolAt code ((Positions.ofDraws code.logN (rvOf dB mB cB).poss).all.getD i 0)
            xs0.toArray ys0.toArray =
          maddE ((stars.getD i {}).main.getD 0 zeroE) lam (y.getD (i * 2 + 0) zeroE) ∧
        symbolAt (c.st.codes.mask.getD R.maskCode default)
            (shortPosition (c.st.codes.mask.getD R.maskCode default).logN
              ((Positions.ofDraws code.logN (rvOf dB mB cB).poss).all.getD i 0))
            xs1.toArray ys1.toArray =
          maddE ((stars.getD i {}).mask.getD 0 zeroE) lam (y.getD (i * 2 + 1) zeroE) := by
  have hrows : R.rows = 2 := by
    unfold SingleRows.rows
    omega
  unfold baseVerify at h
  rw [hrows, hm] at h
  obtain ⟨S0, x1, h1, g1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨code, x2, h2, g2⟩ := (Blk.yields_bind _ _ _ _ _).1 g1
  obtain ⟨star', x3, h3, g3⟩ := (Blk.yields_bind _ _ _ _ _).1 g2
  obtain ⟨S, x4, h4, g4⟩ := (Blk.yields_bind _ _ _ _ _).1 g3
  obtain ⟨u5, x5, h5, g5⟩ := (Blk.yields_bind _ _ _ _ _).1 g4
  obtain ⟨u6, x6, h6, g6⟩ := (Blk.yields_bind _ _ _ _ _).1 g5
  obtain ⟨tauS, x7, h7, g7⟩ := (Blk.yields_bind _ _ _ _ _).1 g6
  obtain ⟨lam, x8, h8, g8⟩ := (Blk.yields_bind _ _ _ _ _).1 g7
  obtain ⟨u9, x9, h9, g9⟩ := (Blk.yields_bind _ _ _ _ _).1 g8
  obtain ⟨m, x10, h10, g10⟩ := (Blk.yields_bind _ _ _ _ _).1 g9
  obtain ⟨r, x11, h11, g11⟩ := (Blk.yields_bind _ _ _ _ _).1 g10
  obtain ⟨u12, x12, h12, g12⟩ := (Blk.yields_bind _ _ _ _ _).1 g11
  obtain ⟨left, x13, h13, g13⟩ := (Blk.yields_bind _ _ _ _ _).1 g12
  obtain ⟨u14, x14, h14, g14⟩ := (Blk.yields_bind _ _ _ _ _).1 g13
  obtain ⟨u15, x15, h15, g15⟩ := (Blk.yields_bind _ _ _ _ _).1 g14
  obtain ⟨u16, x16, h16, g16⟩ := (Blk.yields_bind _ _ _ _ _).1 g15
  obtain ⟨⟨pos, more⟩, x17, h17, g17⟩ := (Blk.yields_bind _ _ _ _ _).1 g16
  obtain ⟨u18, x18, h18, g18⟩ := (Blk.yields_bind _ _ _ _ _).1 g17
  obtain ⟨opened, x19, h19, g19⟩ := (Blk.yields_bind _ _ _ _ _).1 g18
  obtain ⟨y, x20, h20, g20⟩ := (Blk.yields_bind _ _ _ _ _).1 g19
  obtain ⟨stars, x21, h21, h22⟩ := (Blk.yields_bind _ _ _ _ _).1 g20
  clear h g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20
  -- the public head
  obtain ⟨eS0, ex1⟩ := (Blk.yields_statement _ _ _).1 h1
  subst x1 S0
  obtain ⟨hcode, ex2⟩ := (Blk.yields_get _ _ _ _).1 h2
  subst x2
  obtain ⟨est, ex3⟩ := (Blk.yields_pure _ _ _ _).1 h3
  subst x3 star'
  obtain ⟨eS, ex4⟩ := (Blk.yields_statement _ _ _).1 h4
  subst x4 S
  obtain ⟨hshape, ex5⟩ := (Blk.yields_must _ _ _).1 h5
  subst x5
  have ex6 := Blk.spendAsMask_inv star c x6 h6
  have hch6 : x6.ch = c.ch := by rw [ex6]
  have hbk6 : x6.book = c.book := by rw [ex6]
  have hfl6 : x6.failed = c.failed := by rw [ex6]
  have hd6 : x6.ch.dry = false := by rw [hch6]; exact hd
  clear ex6 h1 h2 h3 h4 h5
  -- the first round
  have hp' : c.ch.pending =
      ⟨PQ.PlainOf.gots dL.items (GPlain.old (b := dL.entry.work) mL.2),
        (ckP .two).dr dL.entry dL.kind (GChal.old (b := dL.entry.work) cL)⟩ ::
      ⟨PQ.PlainOf.gots dB.items (GPlain.old (b := dB.entry.work) mB.2),
        (ckP .two).dr dB.entry dB.kind (GChal.old (b := dB.entry.work) cB)⟩ :: rest := hp
  obtain ⟨r1, t1, v1, a1, a2, a3, s7⟩ := Blk.recvE_inv tauS x6 x7 hd6 h7
  rw [hch6, hp'] at a1
  obtain ⟨er1, et1⟩ := List.cons.inj a1
  subst er1 et1
  have hd7 : x7.ch.dry = false := s7.dry.trans hd6
  obtain ⟨d8, h8', hel⟩ := Blk.closeOne_inv _ _ _ lam x7 x8 h8
  obtain ⟨e8, es8, r8, t8, _, _, _, b4, b5, b6, _, _, _, b10, _, _, b13, b14, b15, b16, b17,
    _, b19, _⟩ :=
    Blk.close_inv _ _ _ d8 x7 x8 hd7 h8'
  rw [a3] at b4
  obtain ⟨er8, et8⟩ := List.cons.inj b4
  subst er8 et8
  have hv1 : v1 = [] := b5
  subst hv1
  have a2' : PQ.PlainOf.gots dL.items (GPlain.old (b := dL.entry.work) mL.2) =
      [Fmt.ItemValue.e tauS.triple] := a2
  have hsL : sentW dL mL = [tauS.triple] := by
    unfold sentW
    rw [a2']
    rfl
  have helL : (rvOf dL mL cL).els = [lam.triple] := by
    rw [b6] at hel
    exact hel
  obtain ⟨_, ex9⟩ := (Blk.yields_must _ _ _).1 h9
  subst x9
  -- the second round's message
  obtain ⟨xss, w1, c1, c2, c3, c4, s10⟩ := recvVectors_inv _ m x8 x10 _ _ b16 b10 h10
  obtain ⟨xs0, xs1, rfl, hx0, hx1⟩ := two_of_lengths c1
  have hd10 : x10.ch.dry = false := s10.dry.trans b16
  obtain ⟨yss, w2, f1, f2, f3, f4, s11⟩ := recvVectors_inv _ r x10 x11 _ _ hd10 c4 h11
  obtain ⟨ys0, ys1, rfl, hy0, hy1⟩ := two_of_lengths f1
  have hd11 : x11.ch.dry = false := s11.dry.trans hd10
  subst c2 f2
  obtain ⟨hfit, ex12⟩ := (Blk.yields_testOnView _ _ _ hd11).1 h12
  subst x12
  obtain ⟨hleft, ex13⟩ := (Blk.yields_onView _ _ _ _ _ hd11).1 h13
  subst x13
  have n14 := Blk.yields_note _ _ _ _ h14
  have n15 := Blk.yields_note _ _ _ _ h15
  have hch15 : x15.ch = x11.ch := n15.ch.trans n14.ch
  obtain ⟨k1, k2, k3⟩ := check_frame _ _ _ _ h16
  have hd15 : x15.ch.dry = false := by rw [hch15]; exact hd11
  have hd16 : x16.ch.dry = false := by rw [k1]; exact hd15
  -- the second round is closed
  obtain ⟨d17, h17', hpos⟩ := closedPositions _ _ _ _ _ _ h17
  obtain ⟨e17, es17, r17, t17, _, _, _, g4, g5, g6, _, _, _, g10, _, _, g13, g14, g15, g16, g17,
    _, g19, _⟩ :=
    Blk.close_inv _ _ _ d17 x16 x17 hd16 h17'
  rw [k1, hch15, f4] at g4
  obtain ⟨er17, et17⟩ := List.cons.inj g4
  subst er17 et17
  have hw2 : w2 = [] := g5
  subst hw2
  obtain ⟨_, ex18⟩ := (Blk.yields_must _ _ _).1 h18
  subst x18
  obtain ⟨_, _, _, _, _, _, _, fr, _⟩ := Blk.readOpened_inv _ _ _ _ _ g16 h19
  have q1 := fr.failed
  have q2 := fr.dry
  obtain ⟨hy, ex20⟩ := (Blk.yields_get _ _ _ _).1 h20
  subst x20
  obtain ⟨hstars, ex21⟩ := (Blk.yields_get _ _ _ _).1 h21
  subst x21
  have hd19 : x19.ch.dry = false := q2.trans g16
  obtain ⟨hall, ec'⟩ := Blk.yields_checkOnView _ _ _ _ hd19 h22 hf
  subst c'
  -- no named test has failed, so the first one held
  have hf16 : x16.failed = none := by rw [← g15, ← q1]; exact hf
  obtain ⟨hlin, ex16⟩ := Blk.yields_check _ _ _ _ hd15 h16 hf16
  subst x16
  -- what was read, in the statement's words
  have hposE : pos = Positions.ofDraws code.logN (rvOf dB mB cB).poss := by
    rw [hpos, g6]
    rfl
  subst hposE
  have hsB : sentW dB mB = (xs0 ++ xs1 ++ (ys0 ++ ys1)).map E.triple := by
    have c3' : PQ.PlainOf.gots dB.items (GPlain.old (b := dB.entry.work) mB.2) =
        (xs0 ++ xs1).map (fun x => Fmt.ItemValue.e x.triple) ++ w1 := by
      have e0 : [xs0, xs1].flatten = xs0 ++ xs1 := by simp
      rw [← e0]
      exact c3
    have f3' : w1 = (ys0 ++ ys1).map (fun x => Fmt.ItemValue.e x.triple) := by
      have e0 : [ys0, ys1].flatten = ys0 ++ ys1 := by simp
      rw [← e0, ← List.append_nil (List.map (fun x : E => Fmt.ItemValue.e x.triple) [ys0, ys1].flatten)]
      exact f3
    unfold sentW
    rw [c3', f3', ← List.map_append, sentOf_map_e]
  have hlin' : addE (R.c.dot (ceilLog2 code.ell) xs0.toArray)
      (inner (R.d.getD 0 #[]) xs1.toArray) = maddE tauS lam R.target := by
    have e0 := beq_iff_eq.1 hlin
    rw [hleft] at e0
    exact e0
  have hop : x17.ch.opened = c.ch.opened := by
    rw [g17, hch15, s11.opened, s10.opened, b17, s7.opened, hch6]
  have hbk : x17.book = c.book := by
    rw [g14, n15.book, n14.book, s11.book, s10.book, b14, s7.book, hbk6]
  have hst : x17.st = x6.st := by
    rw [g13, n15.st, n14.st, s11.st, s10.st, b13, s7.st]
  have hft : x17.ch.firstTree = c.ch.firstTree := by
    rw [g19, hch15, s11.firstTree, s10.firstTree, b19, s7.firstTree, hch6]
  have hfc : c.failed = none := by
    rw [← hfl6, ← s7.failed, ← b15, ← s10.failed, ← s11.failed, ← n14.failed, ← n15.failed]
    exact hf16
  have hpe : x19.ch.pending = rest := fr.pending.trans g10
  refine ⟨code, tauS, lam, xs0, xs1, ys0, ys1, x6, x17, opened, y, stars, hcode, hshape, hsL, helL,
    hsB, hx0, hx1, hy0, hy1, hfit, hlin', h19, g10, hop, hbk, g16, h6, hst, hft, hfc, hpe, hy,
    hstars, ?_⟩
  intro i hi
  have q3 := (List.all_eq_true.1 hall) i (List.mem_range.2 hi)
  have q4 := (List.all_eq_true.1 q3) 0 (by decide)
  have q5 := (List.all_eq_true.1 q3) 1 (by decide)
  exact ⟨beq_iff_eq.1 q4, beq_iff_eq.1 q5⟩

/-! ## The run, read in the field -/

/-- A list that is joined of four is cut into the four at their lengths. -/
theorem cut_four {α : Type} (a b c d : List α) :
    (a ++ b ++ (c ++ d)).take a.length = a ∧
      ((a ++ b ++ (c ++ d)).drop a.length).take b.length = b ∧
      ((a ++ b ++ (c ++ d)).drop (a.length + b.length)).take c.length = c ∧
      (a ++ b ++ (c ++ d)).drop (a.length + b.length + c.length) = d := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.append_assoc, List.take_left']
    rfl
  · rw [List.append_assoc, List.drop_left', List.take_left'] <;> rfl
  · rw [← List.length_append, List.drop_left', List.take_left'] <;> rfl
  · rw [← List.length_append, ← List.append_assoc, ← List.length_append, List.drop_left']
    rfl

/-- A drawn position is in the list by which trees are opened. -/
theorem ofDraws_index (logN : ℕ) (draws : List ℕ) (x : ℕ) (hx : x ∈ draws) :
    ∃ k, k < (Positions.ofDraws logN draws).all.size ∧
      (Positions.ofDraws logN draws).all.getD k 0 = x := by
  obtain ⟨k, hk, e⟩ := List.mem_iff_getElem.1 ((Fmt.listOf_mem draws x).2 hx)
  refine ⟨k, ?_, ?_⟩
  · show k < (listOfT draws).toArray.size
    rw [listOfT_eq, List.size_toArray]
    exact hk
  · show (listOfT draws).toArray.getD k 0 = x
    rw [listOfT_eq, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_eq_getElem hk,
      Option.getD_some]
    exact e

/-- What is asked of the symbols that the program has read at the listed positions: they are
those of the word f and of the masking word g. y holds, for each listed position in turn, the main
row's symbol and the mask row's; stars holds the masking oracle's columns. -/
def BaseTie (s : Sg) (f g : s.cIn.Word) (pos : Positions) (y : Array E) (stars : Array Column) :
    Prop :=
  ∀ (i : ℕ) (_ : i < pos.all.size) (hx : pos.all.getD i 0 < 2 ^ s.C.a),
    readV y (i * 2 + 0) = f (.inl ⟨pos.all.getD i 0, hx⟩) (fun _ => false, ()) ∧
    readV y (i * 2 + 1) = f (.inr ⟨pos.all.getD i 0, hx⟩) (fun _ => false, ()) ∧
    readV (stars.getD i {}).main 0 = g (.inl ⟨pos.all.getD i 0, hx⟩) (fun _ => false, ()) ∧
    readV (stars.getD i {}).mask 0 = g (.inr ⟨pos.all.getD i 0, hx⟩) (fun _ => false, ())

/-- If the program's base case runs through and no named test fails, the library's decision holds at
the values of the two written rounds as they are read in the field. The head of this file says what
each named hypothesis asks. -/
theorem baseVerify_sem (s : Sg) (h0 : s.h = 0) (g0 : s.g = 0) (ha : s.C.a ≤ 32)
    (hz : s.Z.a ≤ 32) (R : SingleRows) (star lc : ℕ) (dL dB : PQ.RD) (mL : (wRound dL).Msg)
    (cL : (wRound dL).Chal) (mB : (wRound dB).Msg) (cB : (wRound dB).Chal) (rest : List Fmt.RoundView)
    (c c' : Ctx) (hd : c.ch.dry = false)
    (hp : c.ch.pending = PQ.rvSL (ckP .two) [dL, dB] (mL, cL, mB, cB, ()) ++ rest)
    (hm : R.masks = 1) (hk : R.keptRows = 0)
    (h : (baseVerify R (some star) lc).Yields c () c') (hf : c'.failed = none) {nB : ℕ}
    (hB : SendsDraws dB nB 0 s.t s.C.a) (cd : Code) (hcd : c.st.codes.base[R.code]? = some cd)
    (hC : codeOf cd = s.C) (hZ : codeOf (c.st.codes.mask.getD R.maskCode default) = s.Z)
    (x : GE × (s.cIn.J → GE)) (f g : s.cIn.Word) (hx1 : x.1 = readE R.target)
    (hxc : ∀ j : Fin s.C.l, x.2 (.inl (fun _ => false, j)) = readE (R.c.entry j.val))
    (hxd : ∀ j : Fin s.Z.l, x.2 (.inr (fun _ => false, j)) = readV (R.d.getD 0 #[]) j.val)
    (htie : ∀ c1 a opened y stars,
      (Blk.readOpened ((singleRowsOracles R).push star)
        (Positions.ofDraws cd.logN (rvOf dB mB cB).poss)).Yields a opened c' →
      a.ch.dry = false → a.ch.opened = c.ch.opened → a.book = c.book →
      a.ch.firstTree = c.ch.firstTree → (Blk.spendAsMask star).Yields c () c1 → a.st = c1.st →
      singleRowsSymbols R opened
        (Positions.ofDraws cd.logN (rvOf dB mB cB).poss).all.size = some y →
      opened.back? = some stars →
      BaseTie s f g (Positions.ofDraws cd.logN (rvOf dB mB cB).poss) y stars) :
    LdwAccept (ldCw s.cIn) (ldForm (Slf.idf (E := GE) (J := s.cIn.J)) x) x.1 (s.cIn.T f)
      (s.cIn.T g) (lst (sentW dL mL) 0) (gOne _ (valsOf dL cL)) (shownW s (sentW dB mB))
      (gPos s.C.a s.t _ (valsOf dB cB)) := by
  obtain ⟨code, tauS, lam, xs0, xs1, ys0, ys1, c1, a, opened, y, stars, hcode, hshp, hsL, helL, hsB,
    hx0, hx1', hy0, hy1, hfit, hlin, hrd, _, hop, hbk, hda, hsp, hst, hft, _, _, hy, hstars,
    hall⟩ :=
    baseVerify_run R star lc dL dB mL cL mB cB rest c c' hd hp hm hk h hf
  obtain rfl : cd = code := Option.some.inj (hcd.symm.trans hcode)
  have tie := htie c1 a opened y stars hrd hda hop hbk hft hsp hst hy hstars
  -- the program's product of the form and a vector
  have hdot : ∀ v : Array E, readE (R.c.dot (ceilLog2 cd.ell) v) =
      ∑ i ∈ Finset.range (2 ^ ceilLog2 cd.ell), readE (R.c.entry i) * readV v i := by
    have hf1 : R.c.fits (ceilLog2 cd.ell) = true := by
      simp only [Bool.and_eq_true] at hfit
      exact hfit.1.1
    exact fun v => Form.dot_val rdE R.c _ (Form.vars_of_fits R.c _ hf1) v
  -- the sizes
  have lC : cd.ell = s.C.l := congrArg Fmt.M1.Code.l hC
  have rC : cd.r = s.C.r := congrArg Fmt.M1.Code.r hC
  have aC : cd.logN = s.C.a := congrArg Fmt.M1.Code.a hC
  have lZ : (c.st.codes.mask.getD R.maskCode default).ell = s.Z.l := congrArg Fmt.M1.Code.l hZ
  have rZ : (c.st.codes.mask.getD R.maskCode default).r = s.Z.r := congrArg Fmt.M1.Code.r hZ
  have aZ : (c.st.codes.mask.getD R.maskCode default).logN = s.Z.a := congrArg Fmt.M1.Code.a hZ
  -- the values of the two rounds
  have hu : lst (sentW dL mL) 0 = readE tauS := by
    rw [hsL]
    rfl
  have hμ : gOne _ (valsOf dL cL) = readE lam := gOne_of_els dL mL cL helL
  have hms : shownW s (sentW dB mB) =
      shownOf s (readL xs0) (readL xs1) (readL ys0) (readL ys1) := by
    obtain ⟨k1, k2, k3, k4⟩ := cut_four (xs0.map E.triple) (xs1.map E.triple) (ys0.map E.triple)
      (ys1.map E.triple)
    simp only [List.length_map] at k1 k2 k3 k4
    have e1 : ∀ l : List E, readL l = lst (l.map E.triple) := fun l => funext (readL_eq_lst l)
    unfold shownW
    rw [hsB, List.map_append, List.map_append, List.map_append, ← lC, ← lZ, ← rC, ← hx0, ← hx1',
      ← hy0, k1, k2, k3, k4, e1, e1, e1, e1]
    rfl
  rw [hu, hμ, hms]
  -- the two equations at a drawn position
  have key : ∀ i : Fin s.t,
      polyV s.C (gPos s.C.a s.t _ (valsOf dB cB) i).val (readL xs0) (readL ys0) =
        g (.inl (gPos s.C.a s.t _ (valsOf dB cB) i)) (fun _ => false, ()) +
          readE lam * f (.inl (gPos s.C.a s.t _ (valsOf dB cB) i)) (fun _ => false, ()) ∧
      polyV s.Z (posIn s.Z (gPos s.C.a s.t _ (valsOf dB cB) i)).val (readL xs1) (readL ys1) =
        g (.inr (gPos s.C.a s.t _ (valsOf dB cB) i)) (fun _ => false, ()) +
          readE lam * f (.inr (gPos s.C.a s.t _ (valsOf dB cB) i)) (fun _ => false, ()) := by
    intro i
    have hlt : i.val < (rvOf dB mB cB).poss.length := by
      rw [hB.poss_length]
      exact i.isLt
    have hmem : (gPos s.C.a s.t _ (valsOf dB cB) i).val ∈ (rvOf dB mB cB).poss := by
      rw [hB.gPos_val mB cB i, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt,
        Option.getD_some]
      exact List.getElem_mem hlt
    obtain ⟨k, hk', ek⟩ := ofDraws_index cd.logN _ _ hmem
    have hxlt : (Positions.ofDraws cd.logN (rvOf dB mB cB).poss).all.getD k 0 < 2 ^ s.C.a := by
      rw [ek]
      exact (gPos s.C.a s.t _ (valsOf dB cB) i).isLt
    obtain ⟨t1, t2, t3, t4⟩ := tie k hk' hxlt
    obtain ⟨m1, m2⟩ := hall k hk'
    have hX : (⟨(Positions.ofDraws cd.logN (rvOf dB mB cB).poss).all.getD k 0, hxlt⟩ : s.Ps) =
        gPos s.C.a s.t _ (valsOf dB cB) i := Fin.ext ek
    rw [hX] at t1 t2 t3 t4
    have e1 := congrArg readE m1
    have e2 := congrArg readE m2
    have t1' : readE (y.getD (k * 2 + 0) zeroE) = _ := t1
    have t2' : readE (y.getD (k * 2 + 1) zeroE) = _ := t2
    have t3' : readE ((stars.getD k {}).main.getD 0 zeroE) = _ := t3
    have t4' : readE ((stars.getD k {}).mask.getD 0 zeroE) = _ := t4
    have e3 : ∀ l : List E, lst (l.map E.triple) = readL l := fun l =>
      (funext (readL_eq_lst l)).symm
    rw [readE_symbolAt cd _ (by rw [aC]; exact ha) (by rw [aC]; exact hxlt), readE_maddE, t3', t1',
      ek, hC, symV_eq_polyV, List.toList_toArray, List.toList_toArray, e3, e3] at e1
    rw [readE_symbolAt _ _ (by rw [aZ]; exact hz)
        (show shortPosition _ _ < _ from Nat.mod_lt _ (Nat.two_pow_pos _)), readE_maddE, t4',
      t2', ek, hZ, aZ, symV_eq_polyV, List.toList_toArray, List.toList_toArray, e3, e3] at e2
    exact ⟨e1, e2⟩
  refine accept_of_eqs s h0 g0 x f g _ _ _ _ _ _ _ ?_ (fun i => (key i).1) fun i => (key i).2
  -- the linear equation
  have e0 := congrArg readE hlin
  rw [readE_add, readE_maddE, hdot, readE_inner _ _ s.Z.l
    (le_trans (min_le_right _ _) (by rw [List.size_toArray, hx1', lZ]))] at e0
  rw [hx1, ← e0]
  congr 1
  · have hle : s.C.l ≤ 2 ^ ceilLog2 cd.ell := by
      rw [← lC]
      exact le_two_pow_ceilLog2 cd.ell
    rw [← Finset.sum_subset (Finset.range_subset_range.2 hle) fun i _ hi => by
        rw [readV_toArray, readL_of_le xs0 i (by
          rw [hx0, lC]
          exact Nat.le_of_not_lt fun hlt => hi (Finset.mem_range.2 hlt)), mul_zero],
      ← Fin.sum_univ_eq_sum_range (fun i => readE (R.c.entry i) * readV xs0.toArray i) s.C.l]
    exact Finset.sum_congr rfl fun j _ => by rw [hxc j, readV_toArray xs0]
  · rw [← Fin.sum_univ_eq_sum_range
      (fun i => readV (R.d.getD 0 #[]) i * readV xs1.toArray i) s.Z.l]
    exact Finset.sum_congr rfl fun j _ => by rw [hxd j, readV_toArray xs1]

end OnBytes.Slice

#print axioms OnBytes.Slice.recvVectors_inv
#print axioms OnBytes.Slice.baseVerify_run
#print axioms OnBytes.Slice.baseVerify_sem
#print axioms OnBytes.Slice.sameBut_refl
#print axioms OnBytes.Slice.sameBut_trans
#print axioms OnBytes.Slice.recvEsInto_succ_fun
#print axioms OnBytes.Slice.recvEsInto_inv
#print axioms OnBytes.Slice.closedPositions
#print axioms OnBytes.Slice.check_frame
#print axioms OnBytes.Slice.two_of_lengths
#print axioms OnBytes.Slice.sentOf_map_e
#print axioms OnBytes.Slice.cut_four
#print axioms OnBytes.Slice.ofDraws_index
