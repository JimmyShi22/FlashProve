-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Shape/SwitchInShapeOwn.lean: `door_facts` and `switchIn_shape`
(SwitchInShape.lean in this folder) for a proximity test whose first fold sends its own fresh table.
Two theorems; no definition.

What it is. `SwitchIn` (Johnson/Prover/Link/FormBehindAny.lean) is what the library's laws on the
later stages ask of the state in front of a switch. SwitchInShape.lean proves it at the first stage
where the fresh table has come earlier. Its head says why that proof does not serve the other case:
the clause `roots` says that the state's count of roots is `p.nums.free + j`, and a fold that sends
its own table counts one root more. Here the same clauses are proved in that case, with the count as
it is.

Main names.
  `door_facts_own`: what the door's tests give where no message is named as the mask on entry:
  `TestFrontOwn` (Johnson/Desc/K12/Honest/OwnFoldFirst.lean) in the place of `TestFront`; the rest
  as in `door_facts`.
  `switchIn_shape_own`: `SwitchIn q 0 …` at the term's state after the first fold, at ANY place q
  whose number `free` is `p.nums.free + 1`. Of the nine clauses of `SwitchIn` only `roots` reads the
  place.

By what. The proofs are those of `door_facts` and `switchIn_shape`, with the fellows for this case:
`testFrontOwn_of` (TestDoor.lean), `bat5_yes_own` (OwnFoldDoor.lean), `foldFrontOwn_first`
(OwnFoldFirst.lean), `fold5_yes_own` and `front_entered` (OwnFoldLaws.lean). The state after the
fold is `foldTOwn` (OwnFold.lean): `foldT` at `enteredT`, the state with the new table entered,
which counts one root more.

Over what it stands. `SwitchIn` is read as in FormBehindAny.lean, whose sixth clause
is `dense : DenseForm rows.c`. With `plain : PlainForm rows.c` there the proof would not fit.
The proof here lays `DenseForm`, the weaker of the two: as typed it fits `dense` alone.

Limits.
- `switchIn_shape_own` is a helper, and its letter q is meant for one place and for no other that we
  know: the renumbered place `renumP p` (Johnson/Desc/ProofFile/Honest/K12/Own/Renumber.lean), a
  term of comparison. At that place the first fold's own mask tree is left out of the lists. So
  nothing that is drawn there may be quoted of stage 0, of all the test's trees, or of any count or
  budget over them. No file's plan that we know of has these numbers.
- Conditionals. Nothing here shows that the hypotheses can be met in this case: `A` (`TermAsks`)
  above all.
- Every row taken in is asked to be a `PlainRow`, as in the other statements for this case. There is
  no "dense" twin.
- The state on entry is a letter of the statement. It is not shown to be the verifier's.
- `switchIn_shape` also gives the form of the statement after the fold. That conjunct is left out
  here: no caller asks it.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.Shape.SwitchInShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Sh
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.K12

/-- What the door's tests give, where no message is named as the mask on entry: the first fold sends
its own fresh table. G: the group under test. row: the batched row. x: the element at which
`Bat.combine` returns that row. -/
theorem door_facts_own {p : P12} {a next : Fmt.M1.Stage} {t₀ : T12} {i nn : ℕ × ℕ}
    {dB : Fmt.Drawn}
    (h : doorB p a next (((laidOf p).take 1).map (·.1)) i nn (testSh t₀) = true)
    (hm : t₀.mask = none) (ht : stTidyB t₀.st = true)
    (hpl : ∀ G, t₀.st.groups[t₀.g]? = some G → ∀ r ∈ (runRows t₀.st G).toList, PlainRow r)
    (hv : claimsB t₀ = true) (hB : batCut (((laidOf p).take 1).map (·.1)) = true)
    (fB : roundsFit (((laidOf p).take 1).map (·.1)) [⟨[], dB⟩] = true) :
    ∃ G row x, TestFrontOwn p a next t₀ G i nn ∧
      Bat.combine (begun t₀.st t₀.g G) t₀.g ⟨Means.layoutOf t₀.st G, runRows t₀.st G⟩ x =
        some row ∧
      tBat p t₀ dB = batT t₀ G row ∧ p.nums.free = t₀.roots := by
  unfold doorB at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have h4' : (match t₀.mask with
    | some id => cameB a (testSh t₀).core t₀.g i id
    | none => (testSh t₀).core.st.oracles.length == (testSh t₀).core.book.place.length) = true := h4
  rw [hm] at h4'
  obtain ⟨G, H⟩ := testFrontOwn_of h1 hm (by simpa using h4') ht hpl
  obtain ⟨row, hr, hb⟩ := bat5_yes_own H _ (batOwes_of h2 H.group) hB [⟨[], dB⟩] fB
  exact ⟨G, row, _, H, hr, getD_of_ok hb, (frontOwes_of h3 hv H.group).roots⟩

/-- **`SwitchIn` at the first stage, where the first fold sends its own fresh table**, under the
hypotheses of `first_of_shape_own` and `hrC`, at any place q that counts one root more in front of
the test's own trees than p. The state is the term's state after the first fold (`t1At`), at p. rC:
the round whose sampled positions the clause `range` of `SwitchIn` speaks of. -/
theorem switchIn_shape_own (p : P12) (K : BCoins) (rest : List Fmt.M1.Stage) (a next : Fmt.M1.Stage)
    (o : ℕ) (t₀ : T12) (P : PS) (D : ℕ → Fmt.Drawn) (dB : Fmt.Drawn) (Dp : Plain)
    (c : ℕ → ℕ → List UInt64) (i : ℕ × ℕ) (n : IoppStage) (dS dC : Fmt.DeclaredRound)
    (h : doorB p a next (((laidOf p).take 1).map (·.1)) i (n.code, n.maskCode) (testSh t₀) = true)
    (hm : t₀.mask = none) (ht : stTidyB t₀.st = true)
    (hpl : ∀ G, t₀.st.groups[t₀.g]? = some G → ∀ r ∈ (runRows t₀.st G).toList, PlainRow r)
    (hv : claimsB t₀ = true)
    (Pl : SwitchPub p t₀.st.codes 0 a next rest.isEmpty ⟨i.1, i.2, a.k, a.h⟩ n dS dC)
    (hB : batCut (((laidOf p).take 1).map (·.1)) = true)
    (hF : foldCutOwn a.k (((laidS p).take (1 + a.k)).map (·.1)) = true)
    (fB : roundsFit (((laidOf p).take 1).map (·.1)) [⟨[], dB⟩] = true)
    (A : TermAsks p K rest a next o (tBat p t₀ dB) P D Dp c ⟨i.1, i.2, a.k, a.h⟩ dS dC)
    (rC : Fmt.RoundView) (hrC : rC.drawn.poss = (D (o + 2 + ((sgOf a).h + (sgOf a).g))).poss)
    (q : P12) (hq : q.nums.free = p.nums.free + 1) :
    ∃ rows, SwitchIn q 0 a next n (tBat p t₀ dB).st.groups.size
        (t1At p K 0 a (laidS p) o (tBat p t₀ dB) P D) rows rC := by
  obtain ⟨G, row, x, H, hr, eB, hroots⟩ := door_facts_own h hm ht hpl hv hB fB
  rw [eB] at A ⊢
  have F' := foldFrontOwn_first H x row hr
  have F := front_entered F'
  have hfold := fold5_yes_own F' hF (rfAt K 0 a o (batT t₀ G row) P D) A.fitF
  have e1 : t1At p K 0 a (laidS p) o (batT t₀ G row) P D = _ := getD_of_ok hfold
  obtain ⟨rE, rR, hrs, hR⟩ := rounds_split (length_of_foldCutOwn hF) A.fitF
  obtain ⟨places, Pb⟩ := readPub_sh (A.pub _ _ (by rw [e1]; rfl))
  rw [e1] at Pb ⊢
  rw [hrs] at Pb ⊢
  have hcodes : (batT t₀ G row).st.codes = t₀.st.codes := batT_codes t₀ G row
  have hrow : foldRowOk
      (spent (withOwn (batT t₀ G row).st
        (ioppFoldShape ⟨i.1, i.2, a.k, a.h⟩ (Means.layoutOf t₀.st G)))
        (batT t₀ G row).st.oracles.size)
      (ioppFoldShape ⟨i.1, i.2, a.k, a.h⟩ (Means.layoutOf t₀.st G)) row = true :=
    (Own.foldRowFits_agrees _ _ _).trans ((foldRowFits_spent _ _ _ _).trans F.rowFits)
  have hlen : (rR.map drawnOf).length = a.k := by rw [List.length_map]; exact hR
  have hplain : DenseForm row.c :=
    combine_dense _ _ _ _ _ (fun r h => denseRow_of_plain (H.plain r h)) hr
  have hord : Means.InOrder (withOwn (batT t₀ G row).st
      (ioppFoldShape ⟨i.1, i.2, a.k, a.h⟩ (Means.layoutOf t₀.st G))) := by
    rw [withOwn_sent]
    exact (H.order.begun t₀.g G H.group).stSent _
  obtain ⟨cd, hcd, ecd⟩ := Pl.codes.base
  refine ⟨_, ⟨rfl, ?_,
    inOrder_foldT (enteredT p (batT t₀ G row)
        (ioppFoldShape ⟨i.1, i.2, a.k, a.h⟩ (Means.layoutOf t₀.st G))) row (Means.layoutOf t₀.st G)
      ⟨i.1, i.2, a.k, a.h⟩ (n.code, n.maskCode) (batT t₀ G row).st.oracles.size (rE :: rR) hord,
    ?_, ?_,
    denseForm_foldOutput _ _ row (batT t₀ G row).st.oracles.size _ _ _ hplain, ?_,
    by rw [hrC]; exact A.range, oldIn_of_pub Pb⟩⟩
  · show ((batT t₀ G row).st.groups.push _)[(batT t₀ G row).st.groups.size]? = _
    rw [Array.getElem?_push_size]
  · show t₀.roots + 1 = q.nums.free + 0
    rw [hq, hroots]
  · have Pl' : SwitchPub p (batT t₀ G row).st.codes 0 a next rest.isEmpty ⟨i.1, i.2, a.k, a.h⟩ n dS
        dC := by
      rw [hcodes]
      exact Pl
    exact foldedFit_pure (batT t₀ G row).st.codes (sgOf a) (sgOf next) ⟨i.1, i.2, a.k, a.h⟩
      Pl'.codes n.code n.maskCode Pl'.zk Pl'.codeN Pl'.zkN Pl'.small
      (withOwn (batT t₀ G row).st (ioppFoldShape ⟨i.1, i.2, a.k, a.h⟩ (Means.layoutOf t₀.st G)))
      (spent (withOwn (batT t₀ G row).st
        (ioppFoldShape ⟨i.1, i.2, a.k, a.h⟩ (Means.layoutOf t₀.st G)))
        (batT t₀ G row).st.oracles.size) row (Means.layoutOf t₀.st G)
      (batT t₀ G row).st.oracles.size (drawnOf rE)
      (claimOf rR (maddE ((sentOf rE).getD 0 zeroE) (drawnOf rE) row.target)) (rR.map drawnOf) rfl
      rfl
      (H2K.Pin.combine_noKept0 _ _ _ _ _ hr fun k => H.noKept k) (fun k _ => H.noKept k)
      (hlen.trans Pl.codes.k) ((Own.foldShapeFits_agrees _ _).trans F.shape) hrow
  · have h1 := cfits_foldOutput
      (spent (withOwn (batT t₀ G row).st
        (ioppFoldShape ⟨i.1, i.2, a.k, a.h⟩ (Means.layoutOf t₀.st G)))
        (batT t₀ G row).st.oracles.size)
      (ioppFoldShape ⟨i.1, i.2, a.k, a.h⟩ (Means.layoutOf t₀.st G)) row
      (batT t₀ G row).st.oracles.size (drawnOf rE)
      (rR.map drawnOf) (claimOf rR (maddE ((sentOf rE).getD 0 zeroE) (drawnOf rE) row.target)) hlen
      hrow
    have e : ((spent (withOwn (batT t₀ G row).st
        (ioppFoldShape ⟨i.1, i.2, a.k, a.h⟩ (Means.layoutOf t₀.st G)))
        (batT t₀ G row).st.oracles.size).codes.base.getD
        (ioppFoldShape ⟨i.1, i.2, a.k, a.h⟩ (Means.layoutOf t₀.st G)).code default).ell =
        (sgOf a).C.l := by
      show ((batT t₀ G row).st.codes.base.getD i.1 default).ell = _
      rw [hcodes, Array.getD_eq_getD_getElem?, hcd]
      exact congrArg (·.l) ecd
    rw [e] at h1
    exact h1

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.door_facts_own
#print axioms ProofFile.Honest.Sh.switchIn_shape_own
