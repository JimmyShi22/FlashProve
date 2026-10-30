-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/TieMade.lean: "a sampled member without a candidate leaves few bad draws", at
the record behind the batching: one statement, one layout, and the premise hS paid. Statements and
proofs.

`few_draws_gpG` (Johnson/Desc/K12/Law/TieYOf.lean) had two layouts and two statements that nothing
tied (the seat by D.L and D.st.codes; the rows, the words and the bad draws by letters L and S') and
took hS as a premise. Here S' := t.st and L := the layout that passes, tied to the plain data D by
`Made` (how `gpOf` makes it). There is no new mathematics.
Main names:
  `codes_made`: `Made p t a L D` gives t.st.codes = D.st.codes, in both arms of the mask (where the
    fold brings its own mask D.st lies behind its entering: D.st ≠ t.st there; what is received
    turns no code).
  `few_draws_made`: from `Good`, `Made`, the yes of `siteL` at the member j, `StageJ` at e, e
    fitting e0 in leaves, `combineAt t.st g ⟨L, rows⟩`, the layout's four numbers, the member's
    sample row { row0 with target := tt } ∈ rows with row0 := Send.form D.st.codes sh id seed 0, the
    point at least as long as the cube, the factor the unit β, one answer, `CaseE ∨ CaseF`, the two
    powers of two, and no candidate for `strOf` (the word as sent off the member's written oracle)
    at the sample ((the seed's point read, β), the answer read): cnt (BadDraws (sgOf a) e t.st g L
    rows (the law's word)) ≤ (sgOf a).lstJ e · (rows.size − 1).
Every premise, sorted. Booleans that have been evaluated at the proximity tests of the two example
proofs: `Good` (`gpOk`), `siteL` (`siteOk`), `StageJ` (`johOk`), `combineAt`, the four numbers; and
one answer, the case, the powers of two, "the record's sample row is that of `Send.form` at a seed
read back, the target apart", the seed's length, β ≠ 0 (`sampleOk`). By a lemma: `Made` (`made_of`
at the value of `gpOf`); that a member's sample row stands in `runRows` (`sample_mem_runRows`,
Johnson/Desc/K12/Law/SampleAt.lean: at the statement in front of the batching). Arithmetic on a
letter: hfit. The case's own: hno.
Limits:
(1) What the yes of `sampleOk` gives is not typed here: it is `sample_of_L`
(Johnson/Desc/K12/Law/SampleLaw.lean).
(2) rows := runRows S G at the statement in front, x.sampleRows at the statement behind: the closing
of ledgers turns neither. Not typed here: see Johnson/Desc/K12/Law/TieFront.lean.
(3) `strOf` is our own definition of "the word as sent": that it is the reading of the strings in
Johnson/Desc/Sound/ is not shown.
(4) It is a count of values θ of the drawn element, with no game.
(5) One member a call.
(6) Members without a sample: nothing.
(7) As in the files on the batching's converse under Johnson/Desc/Means, which lie beneath: nothing
on who draws the batching's element, or when, or on how its readings are spread over the field.
No soundness is claimed, and nothing is said on hiding.
Lemmas called (none runs in a context of `verify-on-bytes`): `combineAt_gives`
(Johnson/Desc/Means/TestsLaw.lean), `layout_eq`, `layFacts` (Johnson/Desc/Means/Layout.lean);
`few_draws_gpG`, `answers_of_says_g`, `rowsBlank_law`, `shapes_back`, `shapesKeep_made`,
`find_of_nodup`, `recvP_ok`.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the
file's end.

-/
import Johnson.Desc.K12.Law.TieYOf
import Johnson.Desc.K12.Law.FormTake

set_option autoImplicit false
namespace H2K.Pin
open Cb Cb.Ood Iop Prob OnBytes OnBytes.Slice OnBytes.Slice.ProxRun Johnson.Pack
open OnBytes.Means H2K.ClaimSays
open VerifiableInference.Desc VerifiableInference.Desc.K12
open _root_.Run
open H2K.First (Seat1 Plain gpL gpG gpP good_of_ok oM oZ skM skZ Good Made entered)
open H2K.Pub (sgOf)

/-- The plain data's statement has the record's codes: in both arms of the mask. -/
theorem codes_made {p : P12} {t : T12} {a : Fmt.M1.Stage} {L : GroupLayout} {D : Plain}
    (hm : Made p t a L D) : t.st.codes = D.st.codes := by
  obtain ⟨cu, _, he⟩ := hm.ent
  unfold entered at he
  split at he
  · have e : t.st = D.st := congrArg (fun x => x.2.1) (Option.some.inj he)
    rw [← e]
  · obtain ⟨x, hx, he⟩ := Option.bind_eq_some_iff.1 he
    obtain ⟨id, _, he⟩ := Option.map_eq_some_iff.1 he
    have e : x.2.st = D.st := congrArg (fun x => x.2.1) he
    rw [← e]
    obtain ⟨ids, d1⟩ := x
    obtain ⟨lay, _, _, _, rfl⟩ := H2K.Sw.recvP_ok hx
    rfl

/-- The road at the record behind the batching, hS paid: p, t, a, L, D: the place, the record
behind the batching, the first stage, the layout that passes, gpOf's plain data (Made); h: gpOk's
clauses (Good). j: a member; hs: siteL's yes at it. e: the first stage's radius with the library's
StageJ; e0: the member's radius, which e fits in leaves. rows: the rows that the batching takes,
with its test combineAt at the record's statement and the layout's four numbers. The member's sample
row: { row0 with target := tt }, row0 := Send.form at the plain data's codes, the member's shape and
number and a seed whose point has at least the cube's coordinates and whose factor is the unit β; it
stands among the rows. The case: the member's word as sent (strOf off its written oracle) has no
candidate at that sample. Then the values of the drawn element at which the batched claim has a
witness within e of the law's own word are at most lstJ e · (rows.size − 1). -/
theorem few_draws_made {F : ℕ} {a : Fmt.M1.Stage} {row : GroupRow} {D : Plain} {p : P12} {t : T12}
    {L : GroupLayout} (h : Good F a row D) (hm : Made p t a L D)
    (rd : ℕ → ℕ) (dM : Fin D.mems.length → PQ.RD) (dF : PQ.RD) (os : ∀ i, (wRound (dM i)).Orc)
    (j : Fin D.mems.length) (e0 : ℕ) (hs : ok (siteL D.st.codes a (D.mems.get j)) = true)
    (e : ℕ) (hJ : (sgOf a).StageJ e)
    (hfit : e < (e0 + 1) * 2 ^ ((sgOf a).C.a - aOf D.st.codes (D.mems.get j).sh))
    (g : Nat) (rows : Array Row) (ht : combineAt t.st g ⟨L, rows⟩ = true)
    (hk : L.k = (sgOf a).h + (sgOf a).g) (hh : L.h = (sgOf a).h)
    (hl : 2 ^ L.logEll = (sgOf a).C.l) (hz : 2 ^ L.logEllZk = (sgOf a).Z.l)
    (seed : SampleSeed) (row0 : Row)
    (hform : Send.form D.st.codes (D.mems.get j).sh (D.mems.get j).id seed 0 = some row0) (tt : E)
    (hr : { row0 with target := tt } ∈ rows.toList) (h1 : (D.mems.get j).sh.answers = 1)
    (hc : CaseE (D.mems.get j).sh ∨ CaseF (D.mems.get j).sh)
    (hzl : bitsZ D.st.codes (D.mems.get j).sh ≤ seed.z.length) (β : GEˣ)
    (hβ : (β : GE) = readE seed.beta)
    (hlM : 0 < (D.mems.get j).sh.mainRows →
      2 ^ ceilLog2 (pMain D.st.codes (D.mems.get j).sh).ell = (pMain D.st.codes (D.mems.get
          j).sh).ell)
    (hlZ : 0 < (D.mems.get j).sh.maskRows →
      2 ^ ceilLog2 (pMask D.st.codes (D.mems.get j).sh).ell = (pMask D.st.codes (D.mems.get
          j).sh).ell)
    (hno : ∀ m, ¬ (portOmZ D.st.codes (D.mems.get j).sh e0).Cand
      (strOf D.st.codes (D.mems.get j).sh e0 (layOf (D.mems.get j)) (dM j) (os j))
      ((readP (bitsZ D.st.codes (D.mems.get j).sh) seed.z, β), fun _ => readE tt) m) :
    cnt (BadDraws (sgOf a) e t.st g L rows
      ((gpG h rd).word fun i => ((gpG h rd).mb i).ofOrc ((gpP h rd dM dF).lay i) (dM i) (os i))) ≤
      (sgOf a).lstJ e * (rows.size - 1) := by
  obtain ⟨G', hG, hL', hOk, _⟩ := combineAt_gives ht
  have hL : t.st.layout g = some L := hL'
  have hLm : L.members = G'.members := by
    have e' := layout_eq t.st g G' hG
    rw [hL] at e'
    rw [Option.some.inj e']
    rfl
  obtain ⟨x, hx, ex⟩ := shapes_back hm t.st (shapesKeep_made hm) (by rw [hLm]; exact hOk.there) j
  have hfind := find_of_nodup (by rw [hLm]; exact hOk.nodup) (hm.mem j).1
  have hy := rowsBlank_law h hm rd g G' hG hL hOk hk hh
    (fun i => ((gpG h rd).mb i).ofOrc ((gpP h rd dM dF).lay i) (dM i) (os i))
  have hF := layFacts hG hL hOk
  have hcs := codes_made hm
  have hLD := hm.lay
  subst hLD
  refine few_draws_gpG h rd dM dF os j e0 hs _ e hJ hfit t.st g D.L rows ht hk hh hl hz _ hr
    (fun w hn hS => ?_) hno
  exact answers_of_says_g hJ.sized e hJ.joh.1 t.st G' D.L hF _ hy (D.mems.get j).id j.val x hx
    D.st.codes hcs _ ex e0 _ (oM D.L j.val) (oZ D.L j.val) (fun _ => rfl) (fun _ => rfl) (h.roomM j)
    (h.roomZ j) hfind (h.kept _)
    (fun h0 => by
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (h.firstM j h0)
      unfold oM
      rw [hv]
      rfl)
    (fun h0 => by
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (h.firstZ j h0)
      unfold oZ
      rw [hv]
      rfl)
    hk hh seed row0 hform tt h1 hc hzl β hβ hlM hlZ w hn hS

end H2K.Pin

#print axioms H2K.Pin.codes_made
#print axioms H2K.Pin.few_draws_made
