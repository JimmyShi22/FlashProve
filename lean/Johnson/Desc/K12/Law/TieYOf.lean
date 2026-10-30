-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/TieYOf.lean: the word of the law's own group holds each member's word as sent
at the seat that the yes of `siteL` gives; so a sampled member without a candidate leaves few draws
at which the batched claim has a witness near that very word. Statements and proofs.

The law's own group is `gpG` (Johnson/Desc/K12/Law/FirstOkLaw.lean), read off the members' written
oracles. Neither `gpG` nor `gpOk` is changed for it. There is no new mathematics.
Main names:
  `depth_of_L`, `layOf`: the clause "depth" out of the yes of `siteL`; the law's own record of where
    a member's symbols stand (the field lay of `gpP`).
  `tie_gpG`: (siteOf D.st.codes a m e0 (oM D.L j) (oZ D.L j) hs).Tie (upW (strOf … (layOf m) (dM j)
    (os j))) ((gpG h rd).word fun i => ((gpG h rd).mb i).ofOrc ((gpP h rd dM dF).lay i) (dM i) (os
    i)), by `tie_of_gp` (Johnson/Desc/K12/Law/TieRoad.lean) at r := r': the seats' equations and the
    main rows' values by rfl; the mask rows' values by "depth" (the two moduli 2 ^ (the tree's
    depth) and 2 ^ aOf are one number). There "depth" is spent: without it the equation is false of
    a general oracle.
  `few_draws_gpG`: with `few_draws_of_noCand1`: cnt (BadDraws (sgOf a) e S' g L rows (that word)) ≤
    (sgOf a).lstJ e · (rows.size − 1).
Read with the law: outside `BadDraws`, at the row that the batching returns, "∀ w, ¬ (sgOf a).RIn e
(stmG (sgOf a) row, y) w": the premise hno of `k12_lemma` (Johnson/Desc/K12/Law/K12Lemma.lean), at y
:= this word and e := c.rad.
Limits:
(1) That the word here is `yOf` of Johnson/Desc/K12/Law/K12Lemma.lean: an equation by rfl has been
compiled, with this file beneath it, in a file YOfIs.lean that is not in this library. The letters,
by the text of `yOf`: h := good_of_ok p a row D hok; dM i := (W0 (D.mems.get i).t).1; dF := (W0
D.fresh.t).1; os i := (W0 (D.mems.get i).t).2.
(2) hS is a premise here. `few_draws_made` (Johnson/Desc/K12/Law/TieMade.lean) pays it
(`answers_of_says_g`, with `RowsBlank` of this word from `rowsBlank_law`) at the row { Send.form …
with target := the answer }; that the record's sample row is that row at some seed is a premise
there.
(3) `strOf` (Johnson/Desc/K12/Law/StrOf.lean) is our own definition of "the word as sent".
(4) The yes of `siteL` is held by runs alone (it has said yes at every member of the proximity tests
of the two example proofs).
(5) It is a count of values θ, with no game.
(6) Members without a sample: nothing.
(7) As in the files on the batching's converse under Johnson/Desc/Means, which lie beneath: nothing
on who draws the batching's element, or when, or on how its readings are spread over the field.
No soundness is claimed, and nothing is said on hiding.
Lemmas called (none runs in a context of `verify-on-bytes`): `tie_of_gp`, `upW_strOf`,
`few_draws_of_noCand1`, `numbered_gpG`; the library's `Gp.Numbered.apart`
(OnBytes/Slice/KeyPlaces.lean).
No sorry, no axiom of ours; each theorem has its premises; what the main ones rest on is printed at
the file's end.

-/
import Johnson.Desc.K12.Law.StrOf
import Johnson.Desc.K12.Law.RowsBlankGp

set_option autoImplicit false
namespace H2K.Pin
open Cb Cb.Ood Iop Prob OnBytes OnBytes.Slice OnBytes.Slice.ProxRun Johnson.Pack
open OnBytes.Means H2K.ClaimSays
open VerifiableInference.Desc VerifiableInference.Desc.K12
open _root_.Run
open H2K.First (Seat1 Plain gpL gpG gpP good_of_ok oM oZ skM skZ Good)
open H2K.Pub (sgOf)

/-- The clause "depth" out of siteL's yes. -/
theorem depth_of_L {K : OnBytes.Codes} {a : Fmt.M1.Stage} {m : Seat1} (h : ok (siteL K a m) = true)
    :
    m.tsh.logN = aOf K m.sh := by
  simp only [siteL, ok, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at h
  exact h.2.2.2.2.2

/-- Where a member's symbols stand in a column of its tree: the law's own record (gpP's lay). -/
def layOf (m : Seat1) : OnBytes.Slice.Lay := ⟨m.sh.mainDeg == 1, skM m.tsh m.part, skZ m.tsh m.part⟩

/-- The law's word holds, at the seat that siteL's yes gives, the member's word as sent. h, rd:
the letters of the law's own group gpG. dM i, os i: the written round that sent member i's tree, and
its written oracle. By the text of K12Lemma.lean's yOf, read, not compiled here, the word is the
term to which yOf unfolds at h := good_of_ok p a row D hok · dM i := (W0 (D.mems.get i).t).1 · dF :=
(W0 D.fresh.t).1 · os i := (W0 (D.mems.get i).t).2. j: a member. hs: the six clauses' yes at it.
Then that word holds, at the seat siteOf of the format that the member's own shape gives, the string
strOf read off the same written oracle at the law's own record of where the symbols stand. -/
theorem tie_gpG {F : ℕ} {a : Fmt.M1.Stage} {row : GroupRow} {D : Plain} (h : Good F a row D)
    (rd : ℕ → ℕ) (dM : Fin D.mems.length → PQ.RD) (dF : PQ.RD) (os : ∀ i, (wRound (dM i)).Orc)
    (j : Fin D.mems.length) (e0 : ℕ) (hs : ok (siteL D.st.codes a (D.mems.get j)) = true) :
    (siteOf D.st.codes a (D.mems.get j) e0 (oM D.L j.val) (oZ D.L j.val) hs).Tie
      ((portOmZ D.st.codes (D.mems.get j).sh e0).upW
        (strOf D.st.codes (D.mems.get j).sh e0 (layOf (D.mems.get j)) (dM j) (os j)))
      ((gpG h rd).word fun i => ((gpG h rd).mb i).ofOrc ((gpP h rd dM dF).lay i) (dM i) (os i)) :=
          by
  rw [upW_strOf _ _ _ _ _ _ rfl]
  refine tie_of_gp (gpG h rd) (numbered_gpG h rd).apart _ j _ _ (fun x r' => ⟨r', rfl, rfl⟩)
    (fun x r' => ⟨r', rfl, ?_⟩)
  show symW _ _ (x.val % 2 ^ (D.mems.get j).tsh.logN) _ =
    symW _ _ (x.val % 2 ^ aOf D.st.codes (D.mems.get j).sh) _
  rw [depth_of_L hs]
  rfl

/-- The road joined at the law's word: a sampled member without a candidate ⇒ but for few values
of the drawn element the batched claim has no witness within the radius of the law's own word. The
member j of the law's group; hs: siteL's yes at it; e: the first stage's radius, with the library's
StageJ (johOk's yes gives it); e0: the member's radius, which e fits in leaves; the batching's test
combineAt at the statement S' behind, with the layout's four numbers; r: a batched row with hS for
the witnesses within e (Johnson/Desc/K12/Law/TieMade.lean pays it from the member's sample row); no
candidate for the member's word as sent (strOf off its written oracle) at the sample smp. -/
theorem few_draws_gpG {F : ℕ} {a : Fmt.M1.Stage} {row : GroupRow} {D : Plain} (h : Good F a row D)
    (rd : ℕ → ℕ) (dM : Fin D.mems.length → PQ.RD) (dF : PQ.RD) (os : ∀ i, (wRound (dM i)).Orc)
    (j : Fin D.mems.length) (e0 : ℕ) (hs : ok (siteL D.st.codes a (D.mems.get j)) = true)
    (smp : (portOmZ D.st.codes (D.mems.get j).sh e0).Smp) (e : ℕ) (hJ : (sgOf a).StageJ e)
    (hfit : e < (e0 + 1) * 2 ^ ((sgOf a).C.a - aOf D.st.codes (D.mems.get j).sh))
    (S' : Statement) (g : Nat) (L : GroupLayout) (rows : Array Row)
    (ht : combineAt S' g ⟨L, rows⟩ = true) (hk : L.k = (sgOf a).h + (sgOf a).g)
    (hh : L.h = (sgOf a).h) (hl : 2 ^ L.logEll = (sgOf a).C.l) (hz : 2 ^ L.logEllZk = (sgOf a).Z.l)
    (r : Row) (hr : r ∈ rows.toList)
    (hS : ∀ w : (sgOf a).cIn.N.Wit, offCnt (Ex := (sgOf a).cIn.ext)
        ((gpG h rd).word fun i => ((gpG h rd).mb i).ofOrc ((gpP h rd dM dF).lay i) (dM i) (os i))
        ((sgOf a).cIn.N.enc w.1 w.2) ≤ e →
      Says rdE S' r (H2K.ClaimSays.wordsOf S' L (tabOf (sgOf a) w.1)) →
      (portOmZ D.st.codes (D.mems.get j).sh e0).Z.val smp.1 (fun x => w.1
        ((siteOf D.st.codes a (D.mems.get j) e0 (oM D.L j.val) (oZ D.L j.val) hs).atJ x)) = smp.2)
    (hno : ∀ m, ¬ (portOmZ D.st.codes (D.mems.get j).sh e0).Cand
      (strOf D.st.codes (D.mems.get j).sh e0 (layOf (D.mems.get j)) (dM j) (os j)) smp m) :
    cnt (BadDraws (sgOf a) e S' g L rows
      ((gpG h rd).word fun i => ((gpG h rd).mb i).ofOrc ((gpP h rd dM dF).lay i) (dM i) (os i))) ≤
      (sgOf a).lstJ e * (rows.size - 1) :=
  few_draws_of_noCand1 D.st.codes (D.mems.get j).sh e0 _ _ smp e hJ hfit _
    (tie_gpG h rd dM dF os j e0 hs) S' g L rows ht hk hh hl hz r hr hS hno

end H2K.Pin

#print axioms H2K.Pin.tie_gpG
#print axioms H2K.Pin.few_draws_gpG
