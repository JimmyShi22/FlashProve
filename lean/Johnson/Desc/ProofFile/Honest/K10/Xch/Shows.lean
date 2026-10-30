-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Xch/Shows.lean: the closing of a segment (K10): the rounds that the honest prover's
part plays show, read in the field, the hiding polynomial's sum and the honest round polynomials, under the premises
named below. These are two premises (hσ, hR) of `carryExact_from_front` (Johnson/Desc/K10/Honest/CarryWords.lean).
Fifteen lemmas alone.

Words.
  a round, read       `sentOf` and `drawnOf` (Johnson/Prover/Link/FormFold.lean) return the elements that a round
                      shows as sent and the element that it drew, as records of three words (`OnBytes.E`). `readE`
                      (OnBytes/Slice/ProgField.lean) reads such a record as an element of the extension field. Two
                      records may read as one element
  the rounds          the closing has 2 + k rounds: rB ("BAT", nothing is sent), rE ("FOLD epsilon", one element) and
                      the k rounds rR ("FOLD round", two elements each). Of the kind's shape: `ShapedAll`
                      (Johnson/Desc/K10/Honest/YesFree.lean): they show just so many elements, and each drew one
                      element, no position and no matrix entry
  `Shows k rR q γ`    (Johnson/Prover/Link/FoldHolds.lean) the k rounds rR send what reads as the constant and
                      quadratic coefficients of q, and drew what reads as the point γ
  the data            a value A of `FoldAsk` (Honest/K10/Job.lean): the batched row written out (c, d), the group's
                      two tables (m, mu), the kept forms' value (keptV), and a run: the 2 k + 1 coefficients of the
                      hiding polynomial. `foldWords` (Honest/K10/Words.lean) makes of them the word for "FOLD epsilon"
                      (`sigma`, by `foldSigmaE`) and the two words for a "FOLD round" (`round`, by `foldRoundE`).
                      `askZero` (the data, made with 0 for each member of the run), `askWith` (these data with a run
                      laid in) and `saysAt` (what round i of the part says): Honest/K10/SimSent.lean
  the stage           `stageB D s` (Johnson/Desc/K10/Honest/LeftClaim.lean), written with the data D of the facts
                      `CloseBase` (Johnson/Desc/K10/Honest/Base.lean) at the record s

Why the field. The part lays each word x as the field's element `toE x.triple` (`sayE`, Honest/Sum.lean), and a view
shows an element as the three words below the prime that represent it (`Said.got`, Honest/Frame.lean). So what a
played round shows reads as x reads. That it is x, word for word, would need each of x's three words to be below the
prime, which no lemma called here says. `tables_law` and `ask_law` (Honest/K10/AskLaw.lean) and `rounds_show`
(Johnson/Prover/Link/FoldWordsShows.lean) ask equality of words of what is sent: what `plays_is` (SimSent.lean) says
of the played rounds does not give that. `Shows` reads a round through `readE` alone: sections 2 and 3 carry
`rounds_show` over to rounds that read alike.

What is proved.
  `map_eq_of_get`     on lists: equal images member by member give equal images
  **`shows_alike`**   `Shows` passes between two lists of rounds whose elements sent (the first two) and drawn read
                      alike
  `exact_rounds`      for any function f and any rounds there are rounds that drew the same and show f's very words,
                      round i at what the rounds in front of it drew
  `shows_of_read`     so: if `Shows k X q γ` holds at all such X (hS), and rR sends what reads as f's words read (hq),
                      then `Shows k rR q γ`
  **`close_shows`**   the step inside the proof of `tables_law`, as a statement. Premises. H: `CloseBase P s D`. nk,
                      nh, nl, nz: the stage st has the group's two numbers of row variables and its two codes' message
                      lengths. hrow: the batching returns row at the element x. hlen: rR are st.h + st.g rounds. hq:
                      they send `foldRoundE`'s words at the row written out, the tables `closeMain` and `closeMask` of
                      the entries mw, zw, `closeKept`'s word and the coefficients w. Conclusion: they show the honest
                      round polynomials `foldQK` at the tables of `askWords mw zw`, at the point that they drew
  **`close_shows_read`**
                      the same where hq is asked read in the field
  `head_one`, `drawn_one`, `drawnE_take`
                      at rounds that drew one element each, `drawnE` (Honest/Sum.lean) of the challenges is `drawnOf`
                      of the rounds
  `says_sigma`, `says_round`
                      the items of `saysAt` at round 1 and at round j + 2, as a view shows them
  **`sent_at_ask`**   rounds rB, rE, rR of the kind's shape (hsh) whose challenges are d0, d1, gs (hd) and whose items
                      are `saysAt J o u d1 gs`'s (hv), with gs as many as `J.pub.par.k` (hk): rE sends what reads as
                      `foldWords.sigma`'s word, and rR's i-th round what reads as `foldWords.round`'s two words, at
                      `askWith J o u`. o and u are variables: it holds at o = none too; there `askWith` is `bareAsk`
                      (Honest/K10/Sim.lean): empty tables and the run
  `askZero_of_base`   `askZero`'s value, written out, under the premises of `ask_of_base` (AskLaw.lean)
  **`shows_at_ask`**  Premises. H. hlen: the main code's message length is 2 ^ logEll. hh: the job's h is the frame's
                      group's. Those of `sent_at_ask` at o = some A. hrow, at what rB drew. hc, hdd, hm, hmu, hV: A's
                      five fields are the row written out, `closeMain`, `closeMask` and `closeKept` at mw, zw. hT: the
                      tables of the words are those of `askWords mw zw`. Conclusion: hσ and hR of
                      `carryExact_from_front` at these words, at W the coefficients of the run u (`coefU` of
                      `uOfBook`) and γ the point that rR drew (`ptK` of `lst`)
  **`shows_at_moved`**
                      the same from the prover's side of a thread's step (hM: `Thread.Moved`,
                      Honest/Thread/Pays.lean), by `moved_close_of` (Honest/K10/Xch/Coins.lean): the rounds as played
                      are rB, rE, rR (hrs); c is what `closeCoins` returns (hcc); `askZero` at the state before the
                      block, at what rB drew and at c's carried runs is some A (hA); u is the run that c spends. hr,
                      ho: the block's rounds and oracle messages are those of `closeRounds` at the job's numbers. hp:
                      the first of the thread's sides at the block's place has the one part
                      `closePart (foldShellT true J foldWords)`. hf: the challenges fit the block's rounds

By what. `sigma_readsE`, `rounds_show` (FoldWordsShows.lean); `sent_written`, `sent_written_one` (FoldHolds.lean);
`base_row`, `read_closeKept`, `vecG_written`, `vecIn_tables`, `sigma_cast`, `round_cast`, `ask_of_base` (AskLaw.lean);
`stageB_k`, `stageB_z` (LeftClaim.lean); `get_of_range` (Honest/K10/Fast/Says.lean). The proof of `close_shows` is the
text of the end of `tables_law`'s. A shorter road to `close_shows_read` is not taken: the proof of `rounds_show`
itself goes through `shows_of_parts` (FoldWordsShows.lean), which asks in the field. In front of `shows_at_ask` six
names are marked irreducible to the end of the section, so that Lean does not unfold them while it compares terms:
that changes no statement, and the kernel reads no such mark.

Limits. Every premise named above is a premise: none is proved here of any record, job, thread or run. `CloseBase`,
hlen (of `shows_at_ask`) and hh are shown of no honest run. That `askZero` returns data, and that the data's fields
are these (hA, hc, hdd, hm, hmu, hV): `askZero_of_base` has it where `J.stAt` returns the record's own statement and
group, `J.rows` returns rows and `rowsFit` says yes, at a challenge of the form ⟨[t], [], [], none⟩: all premises; at
a job whose `stAt` returns another statement nothing is said here. Where `askZero` is none, `sent_at_ask` still holds,
and `shows_at_ask` and `shows_at_moved` say nothing. hT ties the words to the entries of which the part's tables are
made: it is shown of no witness. That a fresh table pairs with W (the premise hP of `carryExact_from_front`) is not
spoken of. mw, zw, words and u are variables. Where hM is false `shows_at_moved` holds vacuously. Nothing is shown of
a run of the protocol. No property of the protocol is claimed: nothing is said on its soundness, completeness, binding
or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Xch.Coins
import Johnson.Desc.ProofFile.Honest.K10.AskLaw
import Johnson.Desc.K10.Honest.LeftClaim

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (E zeroE GroupRow)
open OnBytes.Means (Words)
open OnBytes.Slice (readE GE Sg vecG ptK lst runRows toE ofE)
open Johnson.Prover.Link (keptVal FoldSizes sentOf drawnOf Shows foldQK coefU uOfBook foldSigmaE foldRoundE
  sigma_readsE rounds_show sent_written sent_written_one)
open H2K.ClaimSays (msgOf)
open ProofFile.Honest.K10.Values (keptLen)
open ProofFile.Honest.K10.YesFree (BaseData CloseBase ShapedAll)
open ProofFile.Honest.K10.LeftIs (stageB stageB_k stageB_z)
open VerifiableInference VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par Rec)
open Cb (RIdx HPt hMu sVars)

/-! ## 1 Lists -/

/-- Two lists of one length whose members at each number have the same image under g have the same image under g. -/
theorem map_eq_of_get {α β : Type} (g : α → β) : ∀ (l l' : List α), l.length = l'.length →
    (∀ i (h₁ : i < l.length) (h₂ : i < l'.length), g l[i] = g l'[i]) → l.map g = l'.map g
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => by cases hl
  | _ :: _, [], hl, _ => by cases hl
  | a :: l, b :: l', hl, h => by
      have h0 : g a = g b := h 0 (Nat.succ_pos _) (Nat.succ_pos _)
      have ht : l.map g = l'.map g := map_eq_of_get g l l' (Nat.succ.inj hl) fun i h₁ h₂ =>
        h (i + 1) (Nat.succ_lt_succ h₁) (Nat.succ_lt_succ h₂)
      show g a :: l.map g = g b :: l'.map g
      rw [h0, ht]

/-! ## 2 `Shows` reads a round in the field alone -/

/-- **`Shows` passes between two lists of rounds that read alike**: whose first and second elements sent, and whose
elements drawn, read in the field, are the same. -/
theorem shows_alike : ∀ (k : ℕ) (rs rs' : List Fmt.RoundView) (q : RIdx (sVars GE 2 k) → GE) (γ : HPt (sVars GE 2 k)),
    rs.map (fun r => readE ((sentOf r).getD 0 zeroE)) = rs'.map (fun r => readE ((sentOf r).getD 0 zeroE)) →
    rs.map (fun r => readE ((sentOf r).getD 1 zeroE)) = rs'.map (fun r => readE ((sentOf r).getD 1 zeroE)) →
    rs.map (fun r => readE (drawnOf r)) = rs'.map (fun r => readE (drawnOf r)) →
    Shows k rs q γ → Shows k rs' q γ
  | 0, [], [], _, _, _, _, _, h => h
  | 0, [], _ :: _, _, _, e, _, _, _ => by cases e
  | 0, _ :: _, _, _, _, _, _, _, h => h.elim
  | _ + 1, [], _, _, _, _, _, _, h => h.elim
  | _ + 1, _ :: _, [], _, _, e, _, _, _ => by cases e
  | k + 1, r :: rs, r' :: rs', q, γ, e0, e1, e2, h => by
      obtain ⟨h0, h2, hg, hr⟩ := h
      rw [List.map_cons, List.map_cons] at e0 e1 e2
      obtain ⟨a0, b0⟩ := List.cons.inj e0
      obtain ⟨a1, b1⟩ := List.cons.inj e1
      obtain ⟨a2, b2⟩ := List.cons.inj e2
      exact ⟨a0.symm.trans h0, a1.symm.trans h2, a2.symm.trans hg,
        shows_alike k rs rs' _ γ.2 b0 b1 b2 hr⟩

/-- **Beside any rounds there are rounds that drew the same and show f's very words**: round number i shows the two
elements that f makes of pre and of what the rounds in front of it drew. -/
theorem exact_rounds (f : List E → E × E) : ∀ (rs : List Fmt.RoundView) (pre : List E),
    ∃ X : List Fmt.RoundView, X.map drawnOf = rs.map drawnOf ∧
      ∀ i (h : i < X.length), (sentOf X[i]).getD 0 zeroE = (f (pre ++ (X.take i).map drawnOf)).1 ∧
        (sentOf X[i]).getD 1 zeroE = (f (pre ++ (X.take i).map drawnOf)).2
  | [], _ => ⟨[], rfl, fun i h => absurd h (Nat.not_lt_zero i)⟩
  | r :: rs, pre => by
      obtain ⟨X, hd, hX⟩ := exact_rounds f rs (pre ++ [drawnOf r])
      refine ⟨⟨[.e (f pre).1.triple, .e (f pre).2.triple], r.drawn⟩ :: X, congrArg (drawnOf r :: ·) hd,
        fun i h => ?_⟩
      cases i with
      | zero =>
        refine ⟨?_, ?_⟩
        · show (f pre).1 = (f (pre ++ [])).1
          rw [List.append_nil]
        · show (f pre).2 = (f (pre ++ [])).2
          rw [List.append_nil]
      | succ j =>
        have e := hX j (Nat.lt_of_succ_lt_succ h)
        rw [List.append_assoc] at e
        exact e

/-- **From words to the field.** Let q and γ be such that `Shows` holds at every list of rounds that drew what rR drew
and shows f's very words (hS). If rR shows elements that read, in the field, as f's words read (hq), `Shows` holds at
rR. -/
theorem shows_of_read {k : ℕ} (f : List E → E × E) (rR : List Fmt.RoundView) (q : RIdx (sVars GE 2 k) → GE)
    (γ : HPt (sVars GE 2 k))
    (hS : ∀ X : List Fmt.RoundView, X.map drawnOf = rR.map drawnOf →
      (∀ i (h : i < X.length), (sentOf X[i]).getD 0 zeroE = (f ((X.take i).map drawnOf)).1 ∧
        (sentOf X[i]).getD 1 zeroE = (f ((X.take i).map drawnOf)).2) → Shows k X q γ)
    (hq : ∀ i (h : i < rR.length),
      readE ((sentOf rR[i]).getD 0 zeroE) = readE (f ((rR.take i).map drawnOf)).1 ∧
        readE ((sentOf rR[i]).getD 1 zeroE) = readE (f ((rR.take i).map drawnOf)).2) :
    Shows k rR q γ := by
  obtain ⟨X, hd, hX⟩ := exact_rounds f rR []
  have hX' : ∀ i (h : i < X.length), (sentOf X[i]).getD 0 zeroE = (f ((X.take i).map drawnOf)).1 ∧
      (sentOf X[i]).getD 1 zeroE = (f ((X.take i).map drawnOf)).2 := fun i h => hX i h
  have hl : X.length = rR.length := by
    have e := congrArg List.length hd
    rw [List.length_map, List.length_map] at e
    exact e
  have hT : ∀ i, (X.take i).map drawnOf = (rR.take i).map drawnOf := fun i => by
    rw [List.map_take, List.map_take, hd]
  refine shows_alike k X rR q γ ?_ ?_ ?_ (hS X hd hX')
  · exact map_eq_of_get _ X rR hl fun i h₁ h₂ =>
      (congrArg readE (hX' i h₁).1).trans
        ((congrArg (fun l => readE (f l).1) (hT i)).trans (hq i h₂).1.symm)
  · exact map_eq_of_get _ X rR hl fun i h₁ h₂ =>
      (congrArg readE (hX' i h₁).2).trans
        ((congrArg (fun l => readE (f l).2) (hT i)).trans (hq i h₂).2.symm)
  · have e := congrArg (List.map readE) hd
    rw [List.map_map, List.map_map] at e
    exact e

/-! ## 3 The rounds "FOLD round" show the honest round polynomials -/

/-- **Rounds that show `foldRoundE`'s words show the honest round polynomials**, at tables made of given entries mw, zw:
the step inside the proof of `tables_law` (Honest/K10/AskLaw.lean), as a statement. x: what "BAT" drew. eps: what "FOLD
epsilon" drew. -/
theorem close_shows {P : Par} {s : Rec} {D : BaseData} (H : CloseBase P s D) (st : Sg)
    (nk : D.Gq.k = st.h + st.g) (nh : D.Gq.h = st.h)
    (nl : 2 ^ (Own.layoutOf s.st D.G).logEll = st.C.l)
    (nz : 2 ^ (Own.layoutOf s.st D.G).logEllZk = st.Z.l) (mw zw : Nat → Nat → E) (x eps : E)
    (rR : List Fmt.RoundView) (hlen : rR.length = st.h + st.g) (w : Fin (2 * (st.h + st.g) + 1) → E) {row : GroupRow}
    (hrow : Own.batch (D.S1 s) s.frame.group ⟨Own.layoutOf s.st D.G, runRows s.st D.G⟩ x = some row)
    (hq : ∀ i (h : i < rR.length),
      (sentOf rR[i]).getD 0 zeroE = (foldRoundE (st.h + st.g) st.h
          (row.c.writeOut ((Own.layoutOf s.st D.G).k + (Own.layoutOf s.st D.G).logEll)) row.d
          (closeMain (D.S1 s) (Own.layoutOf s.st D.G) mw)
          (closeMask (D.S1 s) (Own.layoutOf s.st D.G) zw) (closeKept (D.S1 s) row.kept mw) w
          eps ((rR.take i).map drawnOf)).1 ∧
        (sentOf rR[i]).getD 1 zeroE = (foldRoundE (st.h + st.g) st.h
          (row.c.writeOut ((Own.layoutOf s.st D.G).k + (Own.layoutOf s.st D.G).logEll)) row.d
          (closeMain (D.S1 s) (Own.layoutOf s.st D.G) mw)
          (closeMask (D.S1 s) (Own.layoutOf s.st D.G) zw) (closeKept (D.S1 s) row.kept mw) w
          eps ((rR.take i).map drawnOf)).2) :
    Shows (st.h + st.g) rR
      (foldQK st (vecG st row)
        (msgOf st (OnBytes.Means.tablesOf (D.S1 s) (Own.layoutOf s.st D.G) (askWords mw zw)))
        (coefU (st.h + st.g) (uOfBook (st.h + st.g) fun i => (w i).triple)) (readE eps)
        (keptVal (keptLen (D.S1 s))
          (OnBytes.Means.tablesOf (D.S1 s) (Own.layoutOf s.st D.G) (askWords mw zw)).kept row.kept)
        (ptK (st.h + st.g) (lst ((rR.map drawnOf).map (·.triple)))))
      (ptK (st.h + st.g) (lst ((rR.map drawnOf).map (·.triple)))) := by
  have hk : (Own.layoutOf s.st D.G).k = st.h + st.g := H.kh.1.trans nk
  have hh : (Own.layoutOf s.st D.G).h = st.h := H.kh.2.trans nh
  obtain ⟨f1, f2, f3⟩ := base_row H hrow
  have hV : keptVal (keptLen (D.S1 s))
      (OnBytes.Means.tablesOf (D.S1 s) (Own.layoutOf s.st D.G) (askWords mw zw)).kept row.kept =
      readE (closeKept (D.S1 s) row.kept mw) := by
    rw [read_closeKept]
    unfold keptVal
    refine congrArg List.sum (List.map_congr_left fun f hf => ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    show _ * (OnBytes.keptWeight (K := GE) (Own.layoutOf s.st D.G) f.oracle * readE (mw f.oracle i)) = _
    rw [f3 f hf, one_mul]
  have hsz : FoldSizes (st.h + st.g) st.h st.C.l st.Z.l
      ((row.c.writeOut ((Own.layoutOf s.st D.G).k + (Own.layoutOf s.st D.G).logEll)).map (·.triple))
      (row.d.map (·.triple))
      ((closeMain (D.S1 s) (Own.layoutOf s.st D.G) mw).map (·.triple))
      ((closeMask (D.S1 s) (Own.layoutOf s.st D.G) zw).map (·.triple)) := by
    have hv : ∀ v ∈ row.c.tensors,
        v.vars = (Own.layoutOf s.st D.G).k + (Own.layoutOf s.st D.G).logEll := fun v h =>
      (((Own.formFits_iff _ _).1 f1).1 v h).1
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Array.size_map, (OnBytes.Form.writeOut_val OnBytes.Slice.rdE row.c _ hv 0 (Nat.two_pow_pos _)).1, hk,
        pow_add, nl]
    · unfold closeMain
      rw [Array.size_map, Array.size_ofFn, hk, pow_add, nl]
    · rw [Array.size_map, f2, hh, pow_add, nz]
    · unfold closeMask
      rw [Array.size_map, Array.size_ofFn, hh, pow_add, nz]
  rw [vecG_written st (Own.layoutOf s.st D.G) row hk nl f1,
    ← vecIn_tables st (D.S1 s) (Own.layoutOf s.st D.G) mw zw hk hh nl nz, hV]
  exact rounds_show st _ _ _ _ _ w eps hsz rR hlen hq

/-- **The same from rounds that show elements which read, in the field, as `foldRoundE`'s words read.** -/
theorem close_shows_read {P : Par} {s : Rec} {D : BaseData} (H : CloseBase P s D) (st : Sg)
    (nk : D.Gq.k = st.h + st.g) (nh : D.Gq.h = st.h)
    (nl : 2 ^ (Own.layoutOf s.st D.G).logEll = st.C.l)
    (nz : 2 ^ (Own.layoutOf s.st D.G).logEllZk = st.Z.l) (mw zw : Nat → Nat → E) (x eps : E)
    (rR : List Fmt.RoundView) (hlen : rR.length = st.h + st.g) (w : Fin (2 * (st.h + st.g) + 1) → E) {row : GroupRow}
    (hrow : Own.batch (D.S1 s) s.frame.group ⟨Own.layoutOf s.st D.G, runRows s.st D.G⟩ x = some row)
    (hq : ∀ i (h : i < rR.length),
      readE ((sentOf rR[i]).getD 0 zeroE) = readE (foldRoundE (st.h + st.g) st.h
          (row.c.writeOut ((Own.layoutOf s.st D.G).k + (Own.layoutOf s.st D.G).logEll)) row.d
          (closeMain (D.S1 s) (Own.layoutOf s.st D.G) mw)
          (closeMask (D.S1 s) (Own.layoutOf s.st D.G) zw) (closeKept (D.S1 s) row.kept mw) w
          eps ((rR.take i).map drawnOf)).1 ∧
        readE ((sentOf rR[i]).getD 1 zeroE) = readE (foldRoundE (st.h + st.g) st.h
          (row.c.writeOut ((Own.layoutOf s.st D.G).k + (Own.layoutOf s.st D.G).logEll)) row.d
          (closeMain (D.S1 s) (Own.layoutOf s.st D.G) mw)
          (closeMask (D.S1 s) (Own.layoutOf s.st D.G) zw) (closeKept (D.S1 s) row.kept mw) w
          eps ((rR.take i).map drawnOf)).2) :
    Shows (st.h + st.g) rR
      (foldQK st (vecG st row)
        (msgOf st (OnBytes.Means.tablesOf (D.S1 s) (Own.layoutOf s.st D.G) (askWords mw zw)))
        (coefU (st.h + st.g) (uOfBook (st.h + st.g) fun i => (w i).triple)) (readE eps)
        (keptVal (keptLen (D.S1 s))
          (OnBytes.Means.tablesOf (D.S1 s) (Own.layoutOf s.st D.G) (askWords mw zw)).kept row.kept)
        (ptK (st.h + st.g) (lst ((rR.map drawnOf).map (·.triple)))))
      (ptK (st.h + st.g) (lst ((rR.map drawnOf).map (·.triple)))) := by
  refine shows_of_read (fun gs => foldRoundE (st.h + st.g) st.h
          (row.c.writeOut ((Own.layoutOf s.st D.G).k + (Own.layoutOf s.st D.G).logEll)) row.d
          (closeMain (D.S1 s) (Own.layoutOf s.st D.G) mw)
          (closeMask (D.S1 s) (Own.layoutOf s.st D.G) zw) (closeKept (D.S1 s) row.kept mw) w
          eps gs) rR _ _ (fun X hd hX => ?_) hq
  have hl : X.length = st.h + st.g := by
    have e := congrArg List.length hd
    rw [List.length_map, List.length_map] at e
    exact e.trans hlen
  have e := close_shows H st nk nh nl nz mw zw x eps X hl w hrow hX
  rw [hd] at e
  exact e

/-! ## 4 What the part's rounds send, read in the field -/

/-- At a list of one triple of words, the first by `head?` (0 for none) spells the element that the first by `headD`
spells. -/
theorem head_one (l : List Fmt.Ext) (t : Fmt.Ext) (h : l = [t]) :
    (l.head?.map E.ofTriple).getD zeroE = E.ofTriple (l.headD (0, 0, 0)) := by
  subst h
  rfl

/-- At a round that drew one element, `drawnE`'s reading of the challenge is `drawnOf`'s of the round. -/
theorem drawn_one (r : Fmt.RoundView) (h : ∃ t, r.drawn.elems = [t]) :
    (r.drawn.elems.head?.map E.ofTriple).getD zeroE = drawnOf r := by
  obtain ⟨t, ht⟩ := h
  exact head_one _ t ht

/-- At rounds that drew one element each, `drawnE` of the first i challenges is `drawnOf` of the first i rounds. -/
theorem drawnE_take : ∀ (rs : List Fmt.RoundView) (i : Nat), (∀ r ∈ rs, ∃ t, r.drawn.elems = [t]) →
    drawnE ((rs.map (·.drawn)).take i) = (rs.take i).map drawnOf
  | _, 0, _ => rfl
  | [], _ + 1, _ => rfl
  | r :: rs, i + 1, h => by
      show (r.drawn.elems.head?.map E.ofTriple).getD zeroE :: drawnE ((rs.map (·.drawn)).take i) =
        drawnOf r :: (rs.take i).map drawnOf
      rw [drawnE_take rs i fun q hq => h q (List.mem_cons_of_mem _ hq), drawn_one r (h r List.mem_cons_self)]

variable {W : Type}

/-- What round 1 of the part ("FOLD epsilon") says, as a view shows it. -/
theorem says_sigma (J : CloseJob W) (o : Option FoldAsk) (u : Fin (2 * J.pub.par.k + 1) → E) (d1 : Fmt.Drawn)
    (gs : List Fmt.Drawn) : (saysAt J o u d1 gs 1).vals.map Said.got =
      [.e (ofE (toE (foldWords.sigma (askWith J o u)).triple))] := rfl

/-- What round j + 2 of the part (the j-th "FOLD round", from 0) says, as a view shows it. -/
theorem says_round (J : CloseJob W) (o : Option FoldAsk) (u : Fin (2 * J.pub.par.k + 1) → E) (d1 : Fmt.Drawn)
    (gs : List Fmt.Drawn) (j : Nat) : (saysAt J o u d1 gs (j + 2)).vals.map Said.got =
      [.e (ofE (toE (foldWords.round (askWith J o u) ((drawnE (d1 :: gs.take j)).headD zeroE)
          ((drawnE (d1 :: gs.take j)).drop 1)).1.triple)),
        .e (ofE (toE (foldWords.round (askWith J o u) ((drawnE (d1 :: gs.take j)).headD zeroE)
          ((drawnE (d1 :: gs.take j)).drop 1)).2.triple))] := rfl

/-- **What rounds that show `saysAt`'s items send, read in the field**: "FOLD epsilon" sends what reads as
`foldWords.sigma`'s word, and the i-th "FOLD round" what reads as `foldWords.round`'s two words, at the data
`askWith J o u`, at what "FOLD epsilon" drew and what the rounds "FOLD round" in front drew. o and u are variables. -/
theorem sent_at_ask (J : CloseJob W) (o : Option FoldAsk) (u : Fin (2 * J.pub.par.k + 1) → E)
    (d0 d1 : Fmt.Drawn) (gs : List Fmt.Drawn) (rB rE : Fmt.RoundView) (rR : List Fmt.RoundView)
    (hk : gs.length = J.pub.par.k) (hsh : ShapedAll (rB :: rE :: rR))
    (hd : (rB :: rE :: rR).map (·.drawn) = d0 :: d1 :: gs)
    (hv : (rB :: rE :: rR).map (·.vals) = (List.range (2 + J.pub.par.k)).map fun i =>
      (saysAt J o u d1 gs i).vals.map Said.got) :
    readE ((sentOf rE).getD 0 zeroE) = readE (foldWords.sigma (askWith J o u)) ∧
      ∀ i (h : i < rR.length),
        readE ((sentOf rR[i]).getD 0 zeroE) =
            readE (foldWords.round (askWith J o u) (drawnOf rE) ((rR.take i).map drawnOf)).1 ∧
          readE ((sentOf rR[i]).getD 1 zeroE) =
            readE (foldWords.round (askWith J o u) (drawnOf rE) ((rR.take i).map drawnOf)).2 := by
  obtain ⟨-, sE, sR⟩ := hsh
  have hd' : rB.drawn :: rE.drawn :: rR.map (·.drawn) = d0 :: d1 :: gs := hd
  obtain ⟨-, hd2⟩ := List.cons.inj hd'
  obtain ⟨e1, eg⟩ := List.cons.inj hd2
  subst e1
  subst eg
  rw [List.length_map] at hk
  constructor
  · have h1 := get_of_range (rB :: rE :: rR) (fun r => r.vals) _ _ hv 1 (by omega)
    rw [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some, says_sigma] at h1
    exact sent_written_one rE _ (Option.some.inj h1)
  · intro i h
    have h2 := get_of_range (rB :: rE :: rR) (fun r => r.vals) _ _ hv (i + 2) (by omega)
    rw [List.getElem?_cons_succ, List.getElem?_cons_succ, List.getElem?_eq_getElem h, Option.map_some,
      says_round] at h2
    have eH : (drawnE (rE.drawn :: (rR.map (·.drawn)).take i)).headD zeroE = drawnOf rE := drawn_one rE sE.2.1
    have eT : (drawnE (rE.drawn :: (rR.map (·.drawn)).take i)).drop 1 = (rR.take i).map drawnOf :=
      drawnE_take rR i fun r hr => (sR r hr).2.1
    rw [eH, eT] at h2
    exact sent_written rR[i] _ _ (Option.some.inj h2)

/-! ## 5 The closing's data, by value -/

/-- **`askZero`'s value under the facts on the record in front**: `ask_of_base` (Honest/K10/AskLaw.lean) at the run of
zeros. -/
theorem askZero_of_base (J : CloseJob W) {s : Rec} {D : BaseData} (H : CloseBase J.pub.par s D)
    (hh : J.pub.par.h = D.Gq.h) (w : W) (sn : Seen) (front : List Fmt.Drawn) (t : Fmt.Ext)
    (hst : J.stAt w sn front = .ok (s.st, s.frame.group)) (ca : CsAll (closeCarries J.pub)) (R : GroupData)
    (hr : J.rows w front ca = .ok R) (hf : rowsFit s.st D.G R = true) :
    ∃ row, Own.batch (D.S1 s) s.frame.group ⟨Own.layoutOf s.st D.G, runRows s.st D.G⟩
        (E.ofTriple t) = some row ∧
      askZero J w sn front ⟨[t], [], [], none⟩ ca = some
        { k := J.pub.par.k, h := J.pub.par.h
          c := row.c.writeOut ((Own.layoutOf s.st D.G).k + (Own.layoutOf s.st D.G).logEll)
          d := row.d
          m := closeMain (D.S1 s) (Own.layoutOf s.st D.G) fun o =>
            wordAt (D.S1 s) R.base.ell (rowsAt D.G R (·.main)) o .main
          mu := closeMask (D.S1 s) (Own.layoutOf s.st D.G) fun o =>
            wordAt (D.S1 s) R.zk.ell (rowsAt D.G R (·.mask)) o .mask
          keptV := closeKept (D.S1 s) row.kept fun o =>
            wordAt (D.S1 s) R.base.ell (rowsAt D.G R (·.main)) o .main
          w := fun _ => zeroE } := by
  obtain ⟨row, hrow, e⟩ := ask_of_base J H hh w sn front t hst (fun _ => zeroE) ca R hr hf
  refine ⟨row, hrow, ?_⟩
  unfold askZero
  rw [e]
  rfl

/-! ## 6 The two premises on the rounds, at the stage of `CloseBase` -/

section Top
attribute [local irreducible] foldSigmaE foldRoundE closeMain closeMask closeKept OnBytes.Form.writeOut

/-- **Rounds that show `saysAt`'s items at data A show the hiding polynomial's sum and the honest round polynomials**,
at the stage `stageB D s`, at the coefficients of the run u and at the point that the rounds drew; at any words whose
tables are those of the entries mw, zw of which A's two tables are made. -/
theorem shows_at_ask (J : CloseJob W) {s : Rec} {D : BaseData} (H : CloseBase J.pub.par s D)
    (hlen : 2 ^ (Own.layoutOf s.st D.G).logEll = ((D.S1 s).codes.base.getD s.frame.shape.code default).ell)
    (hh : J.pub.par.h = D.Gq.h) (mw zw : Nat → Nat → E) (A : FoldAsk) (u : Fin (2 * J.pub.par.k + 1) → E)
    (d0 d1 : Fmt.Drawn) (gs : List Fmt.Drawn) (rB rE : Fmt.RoundView) (rR : List Fmt.RoundView)
    (hk : gs.length = J.pub.par.k) (hsh : ShapedAll (rB :: rE :: rR))
    (hd : (rB :: rE :: rR).map (·.drawn) = d0 :: d1 :: gs)
    (hv : (rB :: rE :: rR).map (·.vals) = (List.range (2 + J.pub.par.k)).map fun i =>
      (saysAt J (some A) u d1 gs i).vals.map Said.got) {row : GroupRow}
    (hrow : Own.batch (D.S1 s) s.frame.group ⟨Own.layoutOf s.st D.G, runRows s.st D.G⟩ (drawnOf rB) = some row)
    (hc : A.c = row.c.writeOut ((Own.layoutOf s.st D.G).k + (Own.layoutOf s.st D.G).logEll)) (hdd : A.d = row.d)
    (hm : A.m = closeMain (D.S1 s) (Own.layoutOf s.st D.G) mw)
    (hmu : A.mu = closeMask (D.S1 s) (Own.layoutOf s.st D.G) zw)
    (hV : A.keptV = closeKept (D.S1 s) row.kept mw) (words : Words GE)
    (hT : OnBytes.Means.tablesOf (D.S1 s) (Own.layoutOf s.st D.G) words =
      OnBytes.Means.tablesOf (D.S1 s) (Own.layoutOf s.st D.G) (askWords mw zw)) :
    readE ((sentOf rE).getD 0 zeroE) = hMu (sVars GE 2 ((stageB D s).h + (stageB D s).g))
        (coefU ((stageB D s).h + (stageB D s).g) (uOfBook ((stageB D s).h + (stageB D s).g) fun i =>
          (u (Fin.cast (by rw [H.stretch, stageB_k H]) i)).triple)) ∧
    Shows ((stageB D s).h + (stageB D s).g) rR
      (foldQK (stageB D s) (vecG (stageB D s) row)
        (msgOf (stageB D s) (OnBytes.Means.tablesOf (D.S1 s) (Own.layoutOf s.st D.G) words))
        (coefU ((stageB D s).h + (stageB D s).g) (uOfBook ((stageB D s).h + (stageB D s).g) fun i =>
          (u (Fin.cast (by rw [H.stretch, stageB_k H]) i)).triple)) (readE (drawnOf rE))
        (keptVal (keptLen (D.S1 s)) (OnBytes.Means.tablesOf (D.S1 s) (Own.layoutOf s.st D.G) words).kept row.kept)
        (ptK ((stageB D s).h + (stageB D s).g) (lst ((rR.map drawnOf).map (·.triple)))))
      (ptK ((stageB D s).h + (stageB D s).g) (lst ((rR.map drawnOf).map (·.triple)))) := by
  have ek : J.pub.par.k = (stageB D s).h + (stageB D s).g := H.stretch.trans (stageB_k H)
  have eh : J.pub.par.h = (stageB D s).h := hh
  have hl : rR.length = (stageB D s).h + (stageB D s).g := by
    have e := congrArg List.length hd
    simp only [List.length_map, List.length_cons] at e
    omega
  obtain ⟨pσ, pR⟩ := sent_at_ask J (some A) u d0 d1 gs rB rE rR hk hsh hd hv
  constructor
  · have e0 : foldWords.sigma (askWith J (some A) u) = foldSigmaE J.pub.par.k u := rfl
    rw [pσ, e0, sigma_cast ek u]
    exact sigma_readsE _ _
  · rw [hT]
    refine close_shows_read H (stageB D s) (stageB_k H) rfl hlen (stageB_z H) mw zw (drawnOf rB) (drawnOf rE) rR hl
      (fun i => u (Fin.cast (by rw [H.stretch, stageB_k H]) i)) hrow fun i h => ?_
    obtain ⟨q1, q2⟩ := pR i h
    have e0 : foldWords.round (askWith J (some A) u) (drawnOf rE) ((rR.take i).map drawnOf) =
        foldRoundE J.pub.par.k J.pub.par.h A.c A.d A.m A.mu A.keptV u (drawnOf rE)
          ((rR.take i).map drawnOf) := rfl
    have e1 := round_cast ek J.pub.par.h A.c A.d A.m A.mu A.keptV u (drawnOf rE) ((rR.take i).map drawnOf)
    have e2 := e1.trans (by rw [eh])
    rw [e0, e2, hc, hdd, hm, hmu, hV] at q1 q2
    exact ⟨q1, q2⟩

end Top

/-! ## 7 At a thread -/

/-- **The same from the prover's side of the closing's step**: where the rounds as played are rB, rE and rR, the part's
coins are c, and `askZero`, at the state of the prover's run before the block, at what rB drew and at c's carried runs,
returns data A: the two premises on the rounds hold at the run that c spends. -/
theorem shows_at_moved {V X Pb S' Cl : Type} {Bk : ProverCoinCounts} (T : Thread Bk S' Cl V W X Pb) (J : CloseJob W)
    (blk : Block S' Cl) (hr : blk.rounds = (closeRounds J.pub.par).map (·.1))
    (ho : blk.oracles = (closeRounds J.pub.par).map (·.2))
    (hp : ∃ g, (T.hs.find? fun h => h.place == blk.place) = some g ∧
      g.parts = [closePart (foldShellT true J foldWords)])
    (k : Coins Bk) (m : Mid W X) (En : Env) (ds : List Fmt.Drawn) (y : List Played × Mid W X) (cols : List OpenedColumn)
    (hf : drawsFit blk.rounds ds = true) (hM : T.Moved blk k m En ds y cols)
    (c : (closePart (V := V) (X := X) (foldShellT true J foldWords)).Coins)
    (hcc : closeCoins (V := V) (X := X) Bk (Bk.rowsOf T.chain) (k.look T.chain) blk.place J = .ok c)
    {s : Rec} {D : BaseData} (H : CloseBase J.pub.par s D)
    (hlen : 2 ^ (Own.layoutOf s.st D.G).logEll = ((D.S1 s).codes.base.getD s.frame.shape.code default).ell)
    (hh : J.pub.par.h = D.Gq.h) (mw zw : Nat → Nat → E) (A : FoldAsk) (rB rE : Fmt.RoundView) (rR : List Fmt.RoundView)
    (hrs : roundsOf y.1 = rB :: rE :: rR) (hsh : ShapedAll (rB :: rE :: rR))
    (hA : askZero J m.st.input m.shown m.st.heard rB.drawn (handSnd c).2.2 = some A) {row : GroupRow}
    (hrow : Own.batch (D.S1 s) s.frame.group ⟨Own.layoutOf s.st D.G, runRows s.st D.G⟩ (drawnOf rB) = some row)
    (hc : A.c = row.c.writeOut ((Own.layoutOf s.st D.G).k + (Own.layoutOf s.st D.G).logEll)) (hdd : A.d = row.d)
    (hm : A.m = closeMain (D.S1 s) (Own.layoutOf s.st D.G) mw)
    (hmu : A.mu = closeMask (D.S1 s) (Own.layoutOf s.st D.G) zw)
    (hV : A.keptV = closeKept (D.S1 s) row.kept mw) (words : Words GE)
    (hT : OnBytes.Means.tablesOf (D.S1 s) (Own.layoutOf s.st D.G) words =
      OnBytes.Means.tablesOf (D.S1 s) (Own.layoutOf s.st D.G) (askWords mw zw)) :
    readE ((sentOf rE).getD 0 zeroE) = hMu (sVars GE 2 ((stageB D s).h + (stageB D s).g))
        (coefU ((stageB D s).h + (stageB D s).g) (uOfBook ((stageB D s).h + (stageB D s).g) fun i =>
          (spentRun J (handSnd c) (Fin.cast (by rw [H.stretch, stageB_k H]) i)).triple)) ∧
    Shows ((stageB D s).h + (stageB D s).g) rR
      (foldQK (stageB D s) (vecG (stageB D s) row)
        (msgOf (stageB D s) (OnBytes.Means.tablesOf (D.S1 s) (Own.layoutOf s.st D.G) words))
        (coefU ((stageB D s).h + (stageB D s).g) (uOfBook ((stageB D s).h + (stageB D s).g) fun i =>
          (spentRun J (handSnd c) (Fin.cast (by rw [H.stretch, stageB_k H]) i)).triple)) (readE (drawnOf rE))
        (keptVal (keptLen (D.S1 s)) (OnBytes.Means.tablesOf (D.S1 s) (Own.layoutOf s.st D.G) words).kept row.kept)
        (ptK ((stageB D s).h + (stageB D s).g) (lst ((rR.map drawnOf).map (·.triple)))))
      (ptK ((stageB D s).h + (stageB D s).g) (lst ((rR.map drawnOf).map (·.triple)))) := by
  obtain ⟨d0, d1, gs, rfl, hk, -, hdr, hvl⟩ := moved_close_of T J blk hr ho hp k m En ds y cols hf hM c hcc
  rw [hrs] at hdr hvl
  have hdr' : rB.drawn :: (rE :: rR).map (·.drawn) = d0 :: d1 :: gs := hdr
  have e0 : rB.drawn = d0 := (List.cons.inj hdr').1
  subst e0
  rw [hA] at hvl
  exact shows_at_ask J H hlen hh mw zw A (spentRun J (handSnd c)) rB.drawn d1 gs rB rE rR hk hsh hdr hvl hrow hc hdd
    hm hmu hV words hT

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.map_eq_of_get
#print axioms ProofFile.Honest.K10.shows_alike
#print axioms ProofFile.Honest.K10.exact_rounds
#print axioms ProofFile.Honest.K10.shows_of_read
#print axioms ProofFile.Honest.K10.close_shows
#print axioms ProofFile.Honest.K10.close_shows_read
#print axioms ProofFile.Honest.K10.head_one
#print axioms ProofFile.Honest.K10.drawn_one
#print axioms ProofFile.Honest.K10.drawnE_take
#print axioms ProofFile.Honest.K10.says_sigma
#print axioms ProofFile.Honest.K10.says_round
#print axioms ProofFile.Honest.K10.sent_at_ask
#print axioms ProofFile.Honest.K10.askZero_of_base
#print axioms ProofFile.Honest.K10.shows_at_ask
#print axioms ProofFile.Honest.K10.shows_at_moved
