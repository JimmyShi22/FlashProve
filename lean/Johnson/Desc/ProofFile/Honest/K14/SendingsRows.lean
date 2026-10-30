-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SendingsRows.lean: the tables that the two sendings' parts make
with code READ, at every index, as the tables of the honest rows at a run's first round (rowsU,
rowsO: Johnson/Desc/K14/Honest/ChainHolds.lean), where what the prover holds is what the parts read
off their input and their coins, and under the premises on the shapes and on the point that are
named below. Two definitions, and five statements with their proofs.

  plain_read      a message that carries a vector and has no mask row: both tables
  coins_read      a message of mask rows alone, every entry a coin: both tables
  fresh_read      a fold's fresh table: both tables
  VecShape, msgCoins   what the laws on a message that carries a vector ask of its shape; a
                  message's coins off the part's coins
  rowsU_read      **"send o_u"**: at each of its messages, at every index
  rowsO_read      **"send o_omega"**: the like

What is assumed. On the shapes: o_u and o_omega have no mask row, a main row, entries of the
extension field, and no more OOD answers than their code's message length (VecShape); the first mask
and o_sp have no main row; each sending has at most two messages; the first has the named shape, and
so has the second of "send o_omega"; of the second of "send o_u" no more is asked than that it has
no main row. On what is held (H): its rows are the input's rows, read; the random values of o_u,
o_omega and o_sp are those messages' coins, read (readCoins, Honest/K14/SendingsTables.lean); THE
FIRST MASK's HAVE TWO CASES (premise hcM of rowsU_read): where the proximity test on G_u has a first
stage they are readFresh's (the same file), else readCoins's. The point that the parts hear is the
first round's, and has its planned number of coordinates: both main statements stand at the jobs
⟨Q, 0⟩ alone, where the point is heard as the challenge number 0.
Limits. AT A FOLD's FRESH TABLE what is held is, by readFresh's definition, the part's own mask rows
and tails, read, the packing by freshRow included: its entries are not the coins, read. So for the
first mask in that case the premise already holds the conclusion: fresh_read's equation holds there
by construction and says nothing on how the coefficients are packed. Met by a default value in
silence: "their code's message length" is `(codes.base.getD s.code default).ell`: the default code's
at a code's number beyond the array; msgCoins returns 0 beyond the end of the part's coins.
What is not claimed. Nothing on a verifier's decision, on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.SendingsTables
import Johnson.Desc.K14.Honest.RowsCoded

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (E zeroE Codes OracleShape OracleNotice)
open OnBytes.Slice (rdE)
open Desc.K14 (P14 St)
open Desc.K14.Honest (MsgCoins vecRows coinRows Inputs rowsU rowsO u_coded omega_coded)
open Johnson.Prover.Send (Rows shapeAt)

/-- A message that carries a vector and has no mask row: both tables, read; where it has a main row,
main rows over the extension field and no more OOD answers than the code's message length, the data
is the vector, read (hv), and the random values are the coins, read (hc). -/
theorem plain_read (codes : Codes) (sent : Array OracleNotice) (L : Nat → Laid) (k : Nat)
    (high : Bool) (v cs : Nat → E) (data : Nat → Cb.Gl.E) (c : MsgCoins)
    (hL : L k = laid codes (sent.getD k default).shape v cs (.plain high))
    (hz : (sent.getD k default).shape.maskRows = 0) (hm : 0 < (sent.getD k default).shape.mainRows)
    (hdeg : (sent.getD k default).shape.mainDeg = 3)
    (hlen : (sent.getD k default).shape.answers ≤
      (codes.base.getD (sent.getD k default).shape.code default).ell)
    (hv : ∀ n, rdE.val (v n) = data n) (hc : c = readCoins codes (sent.getD k default).shape cs)
    (part : OnBytes.Part) (i : Nat) :
    rdE.val (wordsOf sent L k part i) =
      (vecRows codes (sent.getD k default).shape high data c).word (sent.getD k default).shape part
        i := by
  have e : (fun n => rdE.val (v n)) = data := funext hv
  subst hc
  cases part with
  | main => rw [word_main_reads codes sent L k high v cs hL hz hm hdeg hlen i, e]
  | mask => exact word_mask_reads codes sent L k high v cs data hL i

/-- A message of mask rows alone (hno: no main row), every entry a coin: both tables, read; where
the random values are the coins, read (hc). -/
theorem coins_read (codes : Codes) (sent : Array OracleNotice) (L : Nat → Laid) (k : Nat)
    (high : Bool) (v cs : Nat → E) (c : MsgCoins)
    (hL : L k = laid codes (sent.getD k default).shape v cs (.plain high))
    (hno : (sent.getD k default).shape.mainRows = 0)
    (hc : c = readCoins codes (sent.getD k default).shape cs) (part : OnBytes.Part) (i : Nat) :
    rdE.val (wordsOf sent L k part i) = (coinRows c).word (sent.getD k default).shape part i := by
  subst hc
  cases part with
  | main =>
    show rdE.val (if _ < (sent.getD k default).shape.mainRows then _ else zeroE) =
      (if _ < (sent.getD k default).shape.mainRows then _ else 0)
    rw [hno, if_neg (Nat.not_lt_zero _), if_neg (Nat.not_lt_zero _), rdE.zero]
  | mask => exact word_mask_reads codes sent L k high v cs (fun _ => 0) hL i

/-- A fold's fresh table: both tables, read; where it has no main row (hno) and the random values
are readFresh's (hc). readFresh is the part's own rows, read: so at the mask table the equation
holds by construction and says nothing on the packing. -/
theorem fresh_read (codes : Codes) (sent : Array OracleNotice) (L : Nat → Laid) (n : Nat)
    (v cs : Nat → E) (k h : Nat) (c : MsgCoins)
    (hL : L n = laid codes (sent.getD n default).shape v cs (.fresh k h))
    (hno : (sent.getD n default).shape.mainRows = 0)
    (hc : c = readFresh codes (sent.getD n default).shape cs k h) (part : OnBytes.Part)
    (i : Nat) :
    rdE.val (wordsOf sent L n part i) = (coinRows c).word (sent.getD n default).shape part i := by
  subst hc
  cases part with
  | main =>
    show rdE.val (if _ < (sent.getD n default).shape.mainRows then _ else zeroE) =
      (if _ < (sent.getD n default).shape.mainRows then _ else 0)
    rw [hno, if_neg (Nat.not_lt_zero _), if_neg (Nat.not_lt_zero _), rdE.zero]
  | mask => exact word_fresh_reads codes sent L n v cs k h hL i

/-- What the laws on a message that carries a vector ask of its shape. -/
structure VecShape (codes : Codes) (s : OracleShape) : Prop where
  noMask : s.maskRows = 0
  main : 0 < s.mainRows
  overE : s.mainDeg = 3
  room : s.answers ≤ (codes.base.getD s.code default).ell

/-- The coins of the message number n of a job, from the message's first on, off the part's coins; 0
beyond the end of the part's coins (`getD … zeroE`). The same text as the function inside
SendJob.rows (Honest/K14/Sendings.lean), under a name. -/
def msgCoins (J : SendJob) (cs : Array E) (n i : Nat) : E :=
  cs.getD (offsetOf J.Q.codes J.Q.sent J.sort n + i) zeroE

/-- **"send o_u": under the head's premises on the shapes, on the point and on what is held, the
coded tables read as the honest rows' tables**, at each of its messages, at every index. The first
mask's random values (hcM) are readFresh's where the test on G_u has a first stage, else
readCoins's. -/
theorem rowsU_read (Q : P14) (d0 : St) (r1 : Fmt.RoundView) (H : Inputs) (a : Ask) (h : List Fmt.Drawn)
    (cs : Array E) (hsz : (jobU ⟨Q, 0⟩).Q.sent.size ≤ 2)
    (hs0 : ((jobU ⟨Q, 0⟩).Q.sent.getD 0 default).shape = Q.par.S.fold.u)
    (hV : VecShape Q.codes Q.par.S.fold.u)
    (hno : ((jobU ⟨Q, 0⟩).Q.sent.getD 1 default).shape.mainRows = 0)
    (hp : elems (heardFrom ({ input := a, heard := h, own := () } : State Ask Unit) 0 1) =
      Desc.K14.drawn r1)
    (hpt : (Desc.K14.drawn r1).length = Q.par.S.kCol)
    (hRw : ∀ r k, H.Rw r k = rdE.val (a.rows r k))
    (hcU : H.cU = readCoins Q.codes Q.par.S.fold.u (msgCoins (jobU ⟨Q, 0⟩) cs 0))
    (hcM : H.cMask = match Q.S.testU.head? with
      | some s => readFresh Q.codes ((jobU ⟨Q, 0⟩).Q.sent.getD 1 default).shape
          (msgCoins (jobU ⟨Q, 0⟩) cs 1) s.k s.h
      | none => readCoins Q.codes ((jobU ⟨Q, 0⟩).Q.sent.getD 1 default).shape
          (msgCoins (jobU ⟨Q, 0⟩) cs 1))
    (k : Nat) (hk : k < (jobU ⟨Q, 0⟩).Q.sent.size) (part : OnBytes.Part) (i : Nat) :
    rdE.val (wordsOf (jobU ⟨Q, 0⟩).Q.sent
        ((jobU ⟨Q, 0⟩).rows { input := a, heard := h, own := () } cs) k part i) =
      (rowsU Q d0 r1 H k).word (shapeAt (jobU ⟨Q, 0⟩).Q k) part i := by
  have hk2 : k = 0 ∨ k = 1 := by omega
  rcases hk2 with rfl | rfl
  · have e := plain_read Q.codes (jobU ⟨Q, 0⟩).Q.sent
      ((jobU ⟨Q, 0⟩).rows { input := a, heard := h, own := () } cs) 0 Q.S.fold.rowsHigh
      (Desc.K14.Honest.uAtE Q.S (elems (heardFrom
        ({ input := a, heard := h, own := () } : State Ask Unit) 0 1)) a.rows)
      (msgCoins (jobU ⟨Q, 0⟩) cs 0)
      (Desc.K14.Honest.uHon Q.par.S.fold (Desc.K14.Honest.wRun Q d0 r1) H.Rw) H.cU rfl
      (by rw [hs0]; exact hV.noMask) (by rw [hs0]; exact hV.main) (by rw [hs0]; exact hV.overE)
      (by rw [hs0]; exact hV.room)
      (fun n => by rw [hp]; exact u_coded Q d0 r1 H a.rows hpt (fun r _ k => hRw r k) n)
      (by rw [hs0]; exact hcU) part i
    rw [hs0] at e
    rw [e]
    show _ = (rowsU Q d0 r1 H 0).word ((jobU ⟨Q, 0⟩).Q.sent.getD 0 default).shape part i
    rw [hs0]
    rfl
  · cases ht : Q.S.testU.head? with
    | some s =>
      rw [ht] at hcM
      have hL : (jobU ⟨Q, 0⟩).rows { input := a, heard := h, own := () } cs 1 =
          laid Q.codes ((jobU ⟨Q, 0⟩).Q.sent.getD 1 default).shape
            (Desc.K14.Honest.uAtE Q.S (elems (heardFrom
              ({ input := a, heard := h, own := () } : State Ask Unit) 0 1)) a.rows)
            (msgCoins (jobU ⟨Q, 0⟩) cs 1) (.fresh s.k s.h) := by
        show laid _ _ _ _ (match Q.S.testU.head? with
          | some s => MsgSort.fresh s.k s.h
          | none => MsgSort.plain false) = _
        rw [ht]
        rfl
      exact fresh_read Q.codes (jobU ⟨Q, 0⟩).Q.sent _ 1 _ _ s.k s.h H.cMask hL hno hcM part i
    | none =>
      rw [ht] at hcM
      have hL : (jobU ⟨Q, 0⟩).rows { input := a, heard := h, own := () } cs 1 =
          laid Q.codes ((jobU ⟨Q, 0⟩).Q.sent.getD 1 default).shape
            (Desc.K14.Honest.uAtE Q.S (elems (heardFrom
              ({ input := a, heard := h, own := () } : State Ask Unit) 0 1)) a.rows)
            (msgCoins (jobU ⟨Q, 0⟩) cs 1) (.plain false) := by
        show laid _ _ _ _ (match Q.S.testU.head? with
          | some s => MsgSort.fresh s.k s.h
          | none => MsgSort.plain false) = _
        rw [ht]
        rfl
      exact coins_read Q.codes (jobU ⟨Q, 0⟩).Q.sent _ 1 false _ _ H.cMask hL hno hcM part i

/-- **"send o_omega": under the head's premises on the shapes, on the point and on what is held, the
coded tables read as the honest rows' tables**, at each of its messages, at every index. -/
theorem rowsO_read (Q : P14) (d0 : St) (r1 : Fmt.RoundView) (H : Inputs) (a : Ask) (h : List Fmt.Drawn)
    (cs : Array E) (hsz : (jobOmega ⟨Q, 0⟩).Q.sent.size ≤ 2)
    (hs0 : ((jobOmega ⟨Q, 0⟩).Q.sent.getD 0 default).shape = Q.par.S.omega)
    (hs1 : ((jobOmega ⟨Q, 0⟩).Q.sent.getD 1 default).shape = Q.par.S.sharedSplit)
    (hV : VecShape Q.codes Q.par.S.omega) (hno : Q.par.S.sharedSplit.mainRows = 0)
    (hp : elems (heardFrom ({ input := a, heard := h, own := () } : State Ask Unit) 0 1) =
      Desc.K14.drawn r1)
    (hpt : (Desc.K14.drawn r1).length = Q.par.S.kCol)
    (hRw : ∀ r k, H.Rw r k = rdE.val (a.rows r k))
    (hcO : H.cOmega = readCoins Q.codes Q.par.S.omega (msgCoins (jobOmega ⟨Q, 0⟩) cs 0))
    (hcS : H.cSp = readCoins Q.codes Q.par.S.sharedSplit (msgCoins (jobOmega ⟨Q, 0⟩) cs 1))
    (k : Nat) (hk : k < (jobOmega ⟨Q, 0⟩).Q.sent.size) (part : OnBytes.Part) (i : Nat) :
    rdE.val (wordsOf (jobOmega ⟨Q, 0⟩).Q.sent
        ((jobOmega ⟨Q, 0⟩).rows { input := a, heard := h, own := () } cs) k part i) =
      (rowsO Q d0 r1 H k).word (shapeAt (jobOmega ⟨Q, 0⟩).Q k) part i := by
  have hk2 : k = 0 ∨ k = 1 := by omega
  rcases hk2 with rfl | rfl
  · have e := plain_read Q.codes (jobOmega ⟨Q, 0⟩).Q.sent
      ((jobOmega ⟨Q, 0⟩).rows { input := a, heard := h, own := () } cs) 0 Q.S.omegaRowsHigh
      (Desc.K14.Honest.omegaAtE Q.S (elems (heardFrom
        ({ input := a, heard := h, own := () } : State Ask Unit) 0 1)) a.rows)
      (msgCoins (jobOmega ⟨Q, 0⟩) cs 0)
      (Desc.K14.Honest.omegaHon Q.par.S (Desc.K14.Honest.psiLoRun Q r1)
        (Desc.K14.Honest.uHon Q.par.S.fold (Desc.K14.Honest.wRun Q d0 r1) H.Rw)) H.cOmega rfl
      (by rw [hs0]; exact hV.noMask) (by rw [hs0]; exact hV.main) (by rw [hs0]; exact hV.overE)
      (by rw [hs0]; exact hV.room)
      (fun n => by rw [hp]; exact omega_coded Q d0 r1 H a.rows hpt (fun r _ k => hRw r k) n)
      (by rw [hs0]; exact hcO) part i
    rw [hs0] at e
    rw [e]
    show _ = (rowsO Q d0 r1 H 0).word ((jobOmega ⟨Q, 0⟩).Q.sent.getD 0 default).shape part i
    rw [hs0]
    rfl
  · exact coins_read Q.codes (jobOmega ⟨Q, 0⟩).Q.sent _ 1 Q.S.omegaRowsHigh
      (Desc.K14.Honest.omegaAtE Q.S (elems (heardFrom
        ({ input := a, heard := h, own := () } : State Ask Unit) 0 1)) a.rows)
      (msgCoins (jobOmega ⟨Q, 0⟩) cs 1) H.cSp rfl (by rw [hs1]; exact hno)
      (by rw [hs1]; exact hcS) part i

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.plain_read
#print axioms ProofFile.Honest.K14.coins_read
#print axioms ProofFile.Honest.K14.fresh_read
#print axioms ProofFile.Honest.K14.rowsU_read
#print axioms ProofFile.Honest.K14.rowsO_read
