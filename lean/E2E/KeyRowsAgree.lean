-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
THE DEBT IS MOVED INTO NAMED PREMISES, NOT PAID.
E2E/KeyRowsAgree.lean: the rows of «send o_u» in the two texts agree where a column or an answer reads
them, tails included: `RowsAgree` (Johnson/Desc/ProofFile/Honest/K14/TieDefs.lean) at the half's rows and
the honest rows `rowsU`.

Why. The tables that the half sends are made of its rows in this kind's text (`Laid`); the witness's words
are `rowsU`'s. `sentTables_tie` makes the tables of one from the other, under `RowsAgree`.

Main names.
  `rowsAgree_u`: under the premises of `rowsU_read`.

What it says and does not. At `main`, the fold of the committed rows in two texts: this has teeth. At every
coin, tail, pad, mask, the honest rows are defined as what the sender reads off its own coins: there
it says that two texts number the coins alike. At the first mask it holds by construction, by
`readFresh`'s definition, and says nothing of the packing.

NOT IN FRONT OF A LAW OVER COINS: `rowsAgree_u` bears this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground: `hRw`, `hcU`, `hcM` tie `H` to the input's rows and to `cs`,
`hp` ties `r1` to `h`: of the first kind; its callers lay `H` := `holds2`, `a` := `witOf`, `cs` := the run's coins
that the book lends, by `coins_msg`. None of these is the term that the committer makes. None: the bar
is flat.

Nothing on soundness, completeness, hiding or binding.

-/
import Johnson.Desc.ProofFile.Honest.K14.TieColumns
import Johnson.Desc.ProofFile.Honest.K14.SendingsRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyRowsAgree
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (E zeroE)
open OnBytes.Slice (rdE)
open _root_.Desc.K14 (P14 St)
open _root_.Desc.K14.Honest (Inputs rowsU vecMain ownPadPlaces u_coded)
open Johnson.Prover.Send (Rows shapeAt)

/-- **The two texts' rows of «send o_u» agree.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem rowsAgree_u (Q : P14) (d0 : St) (r1 : Fmt.RoundView) (H : Inputs) (a : Ask) (h : List Fmt.Drawn)
    (cs : Array E) (hsz : (jobU ⟨Q, 0⟩).Q.sent.size ≤ 2)
    (hs0 : ((jobU ⟨Q, 0⟩).Q.sent.getD 0 default).shape = Q.par.S.fold.u)
    (hV : VecShape Q.codes Q.par.S.fold.u)
    (hno : ((jobU ⟨Q, 0⟩).Q.sent.getD 1 default).shape.mainRows = 0)
    (hp : elems (heardFrom ({ input := a, heard := h, own := () } : State Ask Unit) 0 1) =
      _root_.Desc.K14.drawn r1)
    (hpt : (_root_.Desc.K14.drawn r1).length = Q.par.S.kCol)
    (hRw : ∀ r k, H.Rw r k = rdE.val (a.rows r k))
    (hcU : H.cU = readCoins Q.codes Q.par.S.fold.u (msgCoins (jobU ⟨Q, 0⟩) cs 0))
    (hcM : H.cMask = match Q.S.testU.head? with
      | some s => readFresh Q.codes ((jobU ⟨Q, 0⟩).Q.sent.getD 1 default).shape
          (msgCoins (jobU ⟨Q, 0⟩) cs 1) s.k s.h
      | none => readCoins Q.codes ((jobU ⟨Q, 0⟩).Q.sent.getD 1 default).shape
          (msgCoins (jobU ⟨Q, 0⟩) cs 1)) :
    RowsAgree (jobU ⟨Q, 0⟩).Q ((jobU ⟨Q, 0⟩).rows { input := a, heard := h, own := () } cs)
      (rowsU Q d0 r1 H) := by
  have two : ∀ k, k < (jobU ⟨Q, 0⟩).Q.sent.size → k = 0 ∨ k = 1 := by
    intro k hk
    omega
  have noMask : ((jobU ⟨Q, 0⟩).Q.sent.getD 0 default).shape.maskRows = 0 := by
    rw [hs0]
    exact hV.noMask
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k hk hne
    rcases two k hk with rfl | rfl
    · show ((jobU ⟨Q, 0⟩).Q.sent.getD 0 default).shape.mainDeg = 3
      rw [hs0]
      exact hV.overE
    · exact absurd hno hne
  · intro k hk r hr j _
    rcases two k hk with rfl | rfl
    · have hr' : r < ((jobU ⟨Q, 0⟩).Q.sent.getD 0 default).shape.mainRows := hr
      rw [hs0] at hr'
      have e := laid_main_reads Q.codes Q.par.S.fold.u Q.S.fold.rowsHigh
        (_root_.Desc.K14.Honest.uAtE Q.S (elems (heardFrom
        ({ input := a, heard := h, own := () } : State Ask Unit) 0 1)) a.rows)
        (msgCoins (jobU ⟨Q, 0⟩) cs 0) hV.noMask hV.main hV.overE hV.room r j
        (lt_of_lt_of_le hr' (OnBytes.Slice.le_two_pow_ceilLog2 _))
      have hv : (fun n => rdE.val ((_root_.Desc.K14.Honest.uAtE Q.S (elems (heardFrom
        ({ input := a, heard := h, own := () } : State Ask Unit) 0 1)) a.rows) n)) =
          _root_.Desc.K14.Honest.uHon Q.par.S.fold (_root_.Desc.K14.Honest.wRun Q d0 r1) H.Rw :=
        funext fun n => by
          rw [hp]
          exact u_coded Q d0 r1 H a.rows hpt (fun r _ k => hRw r k) n
      rw [hv] at e
      show _ = rdE.val ((laid Q.codes ((jobU ⟨Q, 0⟩).Q.sent.getD 0 default).shape
        (_root_.Desc.K14.Honest.uAtE Q.S (elems (heardFrom
        ({ input := a, heard := h, own := () } : State Ask Unit) 0 1)) a.rows)
        (msgCoins (jobU ⟨Q, 0⟩) cs 0) (.plain Q.S.fold.rowsHigh)).main r j)
      rw [hs0, e, ← hcU]
      rfl
    · have hr' : r < ((jobU ⟨Q, 0⟩).Q.sent.getD 1 default).shape.mainRows := hr
      rw [hno] at hr'
      exact absurd hr' (Nat.not_lt_zero _)
  · intro k hk r hr q _
    rcases two k hk with rfl | rfl
    · show H.cU.tail r q = rdE.val ((laid Q.codes ((jobU ⟨Q, 0⟩).Q.sent.getD 0 default).shape
        (_root_.Desc.K14.Honest.uAtE Q.S (elems (heardFrom
        ({ input := a, heard := h, own := () } : State Ask Unit) 0 1)) a.rows)
        (msgCoins (jobU ⟨Q, 0⟩) cs 0) (.plain Q.S.fold.rowsHigh)).mainTail r q)
      rw [hs0, hcU]
      rfl
    · have hr' : r < ((jobU ⟨Q, 0⟩).Q.sent.getD 1 default).shape.mainRows := hr
      rw [hno] at hr'
      exact absurd hr' (Nat.not_lt_zero _)
  · intro k hk r hr j _
    rcases two k hk with rfl | rfl
    · have hr' : r < ((jobU ⟨Q, 0⟩).Q.sent.getD 0 default).shape.maskRows := hr
      rw [noMask] at hr'
      exact absurd hr' (Nat.not_lt_zero _)
    · show H.cMask.mask r j = _
      cases ht : Q.S.testU.head? with
      | some s =>
        rw [ht] at hcM
        have hL : (jobU ⟨Q, 0⟩).rows { input := a, heard := h, own := () } cs 1 =
            laid Q.codes ((jobU ⟨Q, 0⟩).Q.sent.getD 1 default).shape
              (_root_.Desc.K14.Honest.uAtE Q.S (elems (heardFrom
        ({ input := a, heard := h, own := () } : State Ask Unit) 0 1)) a.rows)
              (msgCoins (jobU ⟨Q, 0⟩) cs 1) (.fresh s.k s.h) := by
          show laid _ _ _ _ (match Q.S.testU.head? with
            | some s => MsgSort.fresh s.k s.h
            | none => MsgSort.plain false) = _
          rw [ht]
          rfl
        rw [hL, hcM]
        rfl
      | none =>
        rw [ht] at hcM
        have hL : (jobU ⟨Q, 0⟩).rows { input := a, heard := h, own := () } cs 1 =
            laid Q.codes ((jobU ⟨Q, 0⟩).Q.sent.getD 1 default).shape
              (_root_.Desc.K14.Honest.uAtE Q.S (elems (heardFrom
        ({ input := a, heard := h, own := () } : State Ask Unit) 0 1)) a.rows)
              (msgCoins (jobU ⟨Q, 0⟩) cs 1) (.plain false) := by
          show laid _ _ _ _ (match Q.S.testU.head? with
            | some s => MsgSort.fresh s.k s.h
            | none => MsgSort.plain false) = _
          rw [ht]
          rfl
        rw [hL, hcM]
        rfl
  · intro k hk r hr q _
    rcases two k hk with rfl | rfl
    · have hr' : r < ((jobU ⟨Q, 0⟩).Q.sent.getD 0 default).shape.maskRows := hr
      rw [noMask] at hr'
      exact absurd hr' (Nat.not_lt_zero _)
    · show H.cMask.maskTail r q = _
      cases ht : Q.S.testU.head? with
      | some s =>
        rw [ht] at hcM
        have hL : (jobU ⟨Q, 0⟩).rows { input := a, heard := h, own := () } cs 1 =
            laid Q.codes ((jobU ⟨Q, 0⟩).Q.sent.getD 1 default).shape
              (_root_.Desc.K14.Honest.uAtE Q.S (elems (heardFrom
        ({ input := a, heard := h, own := () } : State Ask Unit) 0 1)) a.rows)
              (msgCoins (jobU ⟨Q, 0⟩) cs 1) (.fresh s.k s.h) := by
          show laid _ _ _ _ (match Q.S.testU.head? with
            | some s => MsgSort.fresh s.k s.h
            | none => MsgSort.plain false) = _
          rw [ht]
          rfl
        rw [hL, hcM]
        rfl
      | none =>
        rw [ht] at hcM
        have hL : (jobU ⟨Q, 0⟩).rows { input := a, heard := h, own := () } cs 1 =
            laid Q.codes ((jobU ⟨Q, 0⟩).Q.sent.getD 1 default).shape
              (_root_.Desc.K14.Honest.uAtE Q.S (elems (heardFrom
        ({ input := a, heard := h, own := () } : State Ask Unit) 0 1)) a.rows)
              (msgCoins (jobU ⟨Q, 0⟩) cs 1) (.plain false) := by
          show laid _ _ _ _ (match Q.S.testU.head? with
            | some s => MsgSort.fresh s.k s.h
            | none => MsgSort.plain false) = _
          rw [ht]
          rfl
        rw [hL, hcM]
        rfl

end AtPublicFiles.KeyRowsAgree

#print axioms AtPublicFiles.KeyRowsAgree.rowsAgree_u
