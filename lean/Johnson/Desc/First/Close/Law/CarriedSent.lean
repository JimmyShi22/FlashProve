-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/CarriedSent.lean (kind K10; for the code switching's law behind it):
THE ROWS THAT A CLOSING LAYS INTO THE FRAME NAME MESSAGES THAT THE STATEMENT HOLDS, OFF THE
CLOSING's OWN YES. Statements and proofs.

Why. The next code switching opens the oracle messages `singleRowsOracles f.rows`
(OnBytes/Iop/Fold.lean: the carried layout's members, and the fresh mask where the rows have two
mask rows). A law in other files spends "each of these numbers is below the number of the
statement's messages". It is made by K10's closing and by nobody else.
  `out_oracles`: at `foldOutput S' F row m eps gs claim` these messages are F.layout's members and
    then m.
  `closing_sent`: closing P S g mask rs = .ok (out, S') gives: every o among `singleRowsOracles out`
    is below S'.oracles.size.
  `closeFrame_sent`: the like at a yes of `closeFrame`, of x.1.rows and x.2.
  `k10_sent`: at a yes of the decision of `K9.closing Q` from s to s': every o among
    `singleRowsOracles s'.live.frame.rows` is below s'.st.oracles.size: of the LIVE copy of the
    frame, into which K10 writes.
By: the closing's own two tests "K10.shape" (every member of the layout is there) and "K10.maskfits"
(the fresh mask is there), read off the yes by `closing_iff`, `fold_iff` (CloseMeans.lean, beside
this file) and opened by `foldShapeFits_iff`, `foldMaskFits_iff` (Johnson/Desc/Own/FoldMean.lean);
`fold_st` (StBehind.lean): the statement behind has as many messages.
Limits. THE STATE RIGHT BEHIND THE CLOSING ALONE: that the frame's rows stay and the statement's
messages do not grow fewer up to the next code switching is a walk's. In the statement's own number
of messages, not in the book's number of places: that the two are one is another fact. Nothing on
soundness.

-/
import Johnson.Desc.First.Close.Law.CloseMeans
import Johnson.Desc.First.Close.Law.StBehind
import Johnson.Desc.First.Close.Law.LensAt
import Johnson.Desc.First.Close.Law.Leaves
import Johnson.Desc.Own.FoldMean

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (recOf putRec)

/-- The messages that the fold's new statement has opened. -/
theorem out_oracles (S' : Statement) (F : FoldShape) (row : GroupRow) (m : ℕ) (eps : E)
    (gs : List E) (claim : E) :
    singleRowsOracles (foldOutput S' F row m eps gs claim) = F.layout.members.push m := rfl

/-- **THE CARRIED ROWS NAME MESSAGES THAT THE STATEMENT BEHIND HOLDS.** -/
theorem closing_sent {P : Plan} {T T' : Statement} {g : ℕ} {mask : Option ℕ}
    {rs : List Fmt.RoundView} {out : SingleRows} (h : closing P T g mask rs = .ok (out, T')) :
    ∀ o ∈ singleRowsOracles out, o < T'.oracles.size := by
  obtain ⟨eB, es, rB, rs', -, -, m, -, row, L, S1, -, -, hF⟩ :=
    (closing_iff P T g mask rs out T').1 h
  have hst := fold_st ((fold_iff _ _ _ _ _ _ _ _).2 hF)
  obtain ⟨-, -, -, -, -, -, -, -, hshape, hmask, -, d2, -, sum, eps, -, -, gamma, claim, -, rfl,
    -⟩ := hF
  have hsz : T'.oracles.size = S1.oracles.size := by
    rw [hst]
    show (S1.oracles.modify m _).size = _
    rw [Array.size_modify]
  obtain ⟨c, zk, -, -, -, -, -, -, -, -, -, hall, -⟩ := (Own.foldShapeFits_iff _ _).1 hshape
  obtain ⟨x, hx, -⟩ := (Own.foldMaskFits_iff _ _ _).1 hmask
  intro o ho
  rw [out_oracles, Array.mem_push] at ho
  rw [hsz]
  rcases ho with ho | rfl
  · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 ho
    obtain ⟨y, hy, -⟩ := hall i hi
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some] at hy
    exact (Array.getElem?_eq_some_iff.1 hy).1
  · exact (Array.getElem?_eq_some_iff.1 hx).1

/-- At a yes of the frame's closing of a link. -/
theorem closeFrame_sent {owed : Option ℕ} {f : ReqFrame} {T : Statement} {es : List Fmt.Entry}
    {rs : List Fmt.RoundView} {x : ReqFrame × Statement} (h : closeFrame owed f T es rs = .ok x) :
    ∀ o ∈ singleRowsOracles x.1.rows, o < x.2.oracles.size := by
  obtain ⟨-, Lk, -, Gf, -, -, rows, hc, e⟩ := (closeFrame_iff owed f T es rs x.1 x.2).1 h
  rw [e]
  exact closing_sent ((closing_iff _ _ _ _ _ _ _).2 hc)

/-- **At a yes of K10's decision: of the live copy of the frame.** -/
theorem k10_sent {Cl : Type} (Q : Par) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64)))
    (h : (VerifiableInference.Desc.K9.closing (Cl := Cl) Q).decide s rs gs = .ok s') :
    ∀ o ∈ singleRowsOracles s'.live.frame.rows, o < s'.st.oracles.size := by
  obtain ⟨x, hx, rfl⟩ := closing_writes Q s s' rs gs h
  have e1 : (putRec s ⟨none, x.1, x.2⟩).live.frame = x.1 := (recOf_putRec s ⟨none, x.1, x.2⟩).1
  have e2 : (putRec s ⟨none, x.1, x.2⟩).st = x.2 := (recOf_putRec s ⟨none, x.1, x.2⟩).2
  rw [e1, e2]
  exact closeFrame_sent hx

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.closing_sent
#print axioms VerifiableInference.Desc.First.Close.closeFrame_sent
#print axioms VerifiableInference.Desc.First.Close.k10_sent
