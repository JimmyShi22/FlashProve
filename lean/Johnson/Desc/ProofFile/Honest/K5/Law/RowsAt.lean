-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/RowsAt.lean: CONDITIONAL: the rows that the verifier makes of
an attention segment's masked sumchecks, at the ledger behind the kind's hearing: each is worth 0.
Definitions of propositions, and statements with their proofs. The reading is the library's own
(`Reading.gl`); the world is any.

What is joined. Honest/K5/Law/Along.lean draws, from the kind's hearing, each sumcheck's own hearing
with its ledgers. Honest/K5/Law/Rows.lean and RowKey.lean say what one sumcheck's row is worth where
the rounds heard are the honest part's. The verifier's text for the rows is `leftP`
(Johnson/Desc/First/Att/LeftP.lean), taken apart by `LeftIs`
(Johnson/Desc/First/Att/K5LeftAll.lean).

EVERY STATEMENT IS CONDITIONAL: on `HonestSum`, one for each sumcheck, which gathers what the honest
side owes. NOTHING HERE SHOWS THAT IT CAN BE MET. Two links that it needs at a member of a run are
not in this file: that the rounds which the kind's decision is handed are the rounds played, as they
are (`honestSum_heard`, Honest/K5/Law/RowsK5.lean, conditional); and at which numbers the scalars
that the hearing takes lie (`laid_of_hear`, Johnson/Desc/K5/Honest/Law/Numbers.lean, conditional).
Its clauses, and who is meant to show each:
  part q of the row is a sumcheck at the job's call        by the row's text
  the summand is tame, and has the call's end values        whoever lays the summand
  the challenges pass the call's test; played alone, the part says the stretch of part q
                                                            whoever shows what the row plays
  the world has the hiding polynomial's coins under the sumcheck's own slots
                                                            whoever ties the mask row to the coins
  the start form is worth the summand's total               whoever states the sumcheck's start
  the summand's terms and weights are the verifier's (`GoodProducts`, `GoodKey`)
                                                            whoever reads the weights
Main names:
  `HonestSum`, `GoodProducts`, `GoodKey`   the premises' forms, for one sumcheck
  `left_zero`, `leftKey_zero`              one row is worth 0
  `RowsPay`                                the premises' forms, for all, at the verifier's weights
  `RowsZero`, `rows_zero`                  **every row is worth 0**

Limits. Nothing on the other claims of the kind. Nothing is claimed on soundness, completeness or
hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Along
import Johnson.Desc.ProofFile.Honest.K5.Law.Rows
import Johnson.Desc.ProofFile.Honest.K5.Law.RowKey
import Johnson.Desc.First.Att.K5LeftAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open OnBytes.Model (Reading Aff Fork World)
open OnBytes.Slice (GE)
open VerifiableInference.Desc.Part (MaskedSum.Heard)
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call ownSlots)
open VerifiableInference.Desc.First.Att.P (Geo UnitG Heard Left LeftIs left leftKey chal scoreW
  weights inner wDivision wBelow wOn wAtIndex wCells batched)
open ProofFile.Honest.SumLaw (SumCoins alone frontOf drawsOk hidingCoin)
open H2K5.Honest (Summand K5In pairsOf shapes iSE iVM iVD iSF iSD iHB keyVars sdOf sdDs)

/-- **The honest side of one masked sumcheck**, against the rounds rs that the kind heard and a
world Wd. q: the sumcheck's number among the row's parts. C, vs, e, hh: its start form, variables,
ends, and what the hearing holds of it. Good: a further clause on the summand. It says that there
are a job made of a summand, coins, a state and challenges such that: part q of the row is a
sumcheck at the job's call; the summand is tame and has the call's number of end values; the
challenges pass the call's test; PLAYED ALONE, THE PART SAYS JUST THE STRETCH OF PART q; the world
has the hiding polynomial's coins under the sumcheck's own slots; the start form is worth the
summand's total; and the further clause. What the part is handed as seen (seen) stands under the
"there are" too: the witness that honestSum_at (Honest/K5/Law/AtMember.lean) lays is m.shown with
rounds laid behind; nothing that is laid beside it there reads its field `opened`. It is a
definition: a premise's form. Nothing is claimed of it. -/
def HonestSum (x : OnBytes.Params.AttentionRounds) (rs : List Fmt.RoundView) (Wd : World GE) (q : Nat)
    (C : Aff) (vs : List Var) (e : Ends) (hh : MaskedSum.Heard) (Good : Summand → Prop) : Prop :=
  ∃ (V W X : Type) (name endName : String) (k : Call) (lead : W → Front X → List E)
    (S : W → Front X → Summand) (c : SumCoins name endName (jobOf k lead S)) (t : State W X)
    (seen : Seen) (dr : List Fmt.Drawn) (ds : List Nat),
    (shapes x)[q]? = some (.sum k) ∧ vs = ds.map Var.plain ∧
    (S t.input (frontOf t seen)).Tame Reading.gl ds e.dY ∧
    (S t.input (frontOf t seen)).ends = e.n ∧ drawsOk k dr = true ∧
    alone (sumPart (V := V) name endName (jobOf k lead S)) c t seen dr =
      some ((rs.drop (H2K5.Honest.firstOf x q)).take (vs.length + 3)) ∧
    (∀ i, i < ownSlots k.all → Wd.slot (hh.first + i) = hidingCoin c i) ∧
    C.value Reading.gl Wd = Reading.gl.val (S t.input (frontOf t seen)).total ∧
    Good (S t.input (frontOf t seen))

/-- The further clause at a sumcheck of products: at the challenges heard the summand's terms are
weighted products, as many as half the end values; the verifier's weights Wt are as many and read
alike. -/
def GoodProducts (e : Ends) (hh : MaskedSum.Heard) (Wt : Array E) (S : Summand) : Prop :=
  ∃ (np : Nat) (Wo : Array E), e.n = 2 * np ∧ S.terms (hh.r.take S.vars) = pairsOf np Wo ∧
    Wt.size = np ∧
    ∀ b, b < np → Reading.gl.val (Wt.getD b zeroE) = Reading.gl.val (Wo.getD b zeroE)

/-- The further clause at the sumcheck on the key at the index: the summand is that sumcheck's text
at the verifier's own letters rho and om'; the call has its numbers. -/
def GoodKey (g : Geo) (vs : List Var) (e : Ends) (rho om' : Array E) (S : Summand) : Prop :=
  (∃ w' : K5In, S = sdOf g w' rho om') ∧ vs = (sdDs g).map Var.plain ∧ e.dY = g.lt + 1 ∧
    e.n = g.Lam + g.NP * g.lt

/-- **The row that the verifier makes of a sumcheck of products, at the ledger behind the kind's
hearing, is worth 0.** CONDITIONAL on: the sumcheck was heard so (`SumHeardAt`); the honest side's
clauses (`HonestSum` with `GoodProducts`); the verifier's `left` returns. -/
theorem left_zero {x : OnBytes.Params.AttentionRounds} {rs : List Fmt.RoundView} {G : Fork}
    {Wd : World GE} {q : Nat} {C : Aff} {vs : List Var} {e : Ends} {hh : MaskedSum.Heard}
    {Wt : Array E} {f : Aff} (H : SumHeardAt x rs G q C vs e hh)
    (P : HonestSum x rs Wd q C vs e hh (GoodProducts e hh Wt)) (hf : left G hh Wt = some f) :
    f.value Reading.gl Wd = 0 := by
  obtain ⟨lead0, F', G', hq', hh', hz, hl⟩ := H
  obtain ⟨V, W, X, name, endName, k, lead, S, c, t, seen, dr, ds, hq, hvs, hT, hn, hd, ha, hm, hσ,
    np, Wo, hen, ht, hsz, hW⟩ := P
  obtain rfl : k = ⟨lead0, vs, some e⟩ := by
    rw [hq'] at hq
    injection hq with h1
    injection h1 with h2
    exact h2.symm
  exact row_zero_left (V := V) name endName _ ds e lead S c t seen dr _ C F' G' G hh Wd np Wo Wt f
    hvs rfl hT hd ha hh' hm hσ hf ht hsz hW hn hen hz hl

/-- **The like of the sumcheck on the key at the index.** CONDITIONAL likewise. Of `HonestSum` the
clauses on the variables, on tameness and on the number of end values are not spent here: `GoodKey`
names the summand, of which they are known. -/
theorem leftKey_zero {x : OnBytes.Params.AttentionRounds} {rs : List Fmt.RoundView} {G : Fork}
    {Wd : World GE} {q : Nat} {C : Aff} {vs : List Var} {e : Ends} {hh : MaskedSum.Heard}
    {g : Geo} {rho om' : Array E} {f : Aff} (H : SumHeardAt x rs G q C vs e hh)
    (P : HonestSum x rs Wd q C vs e hh (GoodKey g vs e rho om'))
    (hf : leftKey g G hh rho om' = some f) : f.value Reading.gl Wd = 0 := by
  obtain ⟨lead0, F', G', hq', hh', hz, hl⟩ := H
  obtain ⟨V, W, X, name, endName, k, lead, S, c, t, seen, dr, ds, hq, -, -, -, hd, ha, hm, hσ,
    ⟨w', hS⟩, hvs, hdY, hen⟩ := P
  obtain rfl : k = ⟨lead0, vs, some e⟩ := by
    rw [hq'] at hq
    injection hq with h1
    injection h1 with h2
    exact h2.symm
  exact row_zero_leftKey (V := V) name endName _ e lead S c t seen dr _ C F' G' G hh Wd g w' rho om'
    f hS hvs rfl hdY hen hd ha hh' hm hσ hf hz hl

/-- Two lists that are related member by member, at a number. -/
theorem RowsAt.forall₂_at {α β : Type} {R : α → β → Prop} : ∀ {l₁ : List α} {l₂ : List β},
    List.Forall₂ R l₁ l₂ → ∀ (n : Nat) (b : β), l₂[n]? = some b → ∃ a, l₁[n]? = some a ∧ R a b
  | _, _, .nil, n, b, h => by simp at h
  | _, _, .cons h1 _, 0, b, h => by
    rw [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact ⟨_, rfl, h1⟩
  | _, _, .cons _ t, n + 1, b, h => by
    rw [List.getElem?_cons_succ] at h
    obtain ⟨a, ha, hr⟩ := RowsAt.forall₂_at t n b h
    exact ⟨a, by rw [List.getElem?_cons_succ]; exact ha, hr⟩

/-- **The honest side of all the kind's masked sumchecks**, each at the weights that the verifier's
text lays (Johnson/Desc/First/Att/K5LeftAll.lean). It is a definition: a premise's form. At a
softmax-table unit it holds, inside `GoodProducts`, that the plan's number of pairs of maps is the
number of the verifier's weights: a tie between the plan's numbers and the verifier's shape. At the
three sumchecks of the division and the value product it is handed what the verifier's text has
tested: the pieces' weights are as many as the shape's pairs. -/
structure RowsPay (x : OnBytes.Params.AttentionRounds) (rs : List Fmt.RoundView) (Wd : World GE) (g : Geo)
    (zk : Array (Array E)) (hd : Heard) : Prop where
  score : ∀ (i : Nat) (u : Nat × Nat) (o : Nat × MaskedSum.Heard) (ug : UnitG) (Wt : Array E),
    x.score[i]? = some u → hd.scores[i]? = some o → g.scores[i]? = some ug →
    scoreW g ug (zk.getD ug.call #[]) (chal o.2) = some Wt →
    HonestSum x rs Wd i (.slot (o.1 + 6)) (prodVs u.1) (prodEnds u.2) o.2
      (GoodProducts (prodEnds u.2) o.2 Wt)
  division : ∀ wl : UnitG, g.single .wl = some wl →
    (weights wl (zk.getD wl.call #[])).size = g.NP →
    HonestSum x rs Wd (iSE x) (.slot (hd.five + 1)) (prodVs x.e) (prodEnds x.pairs) hd.division
      (GoodProducts (prodEnds x.pairs) hd.division
        (wDivision g (weights wl (zk.getD wl.call #[])) (inner wl (zk.getD wl.call #[])) hd))
  below : ∀ wl : UnitG, g.single .wl = some wl →
    (weights wl (zk.getD wl.call #[])).size = g.NP →
    HonestSum x rs Wd (iVM x) (.slot hd.values) (prodVs x.valueM) (prodEnds x.pairs) hd.below
      (GoodProducts (prodEnds x.pairs) hd.below
        (wBelow g (weights wl (zk.getD wl.call #[])) (inner wl (zk.getD wl.call #[])) hd))
  on : ∀ wl : UnitG, g.single .wl = some wl →
    (weights wl (zk.getD wl.call #[])).size = g.NP →
    HonestSum x rs Wd (iVD x) (.slot (hd.values + 1)) (prodVs x.valueD) (prodEnds x.pairs) hd.on
      (GoodProducts (prodEnds x.pairs) hd.on
        (wOn g (weights wl (zk.getD wl.call #[])) (inner wl (zk.getD wl.call #[])) hd))
  atIndex : HonestSum x rs Wd (iSF x) (batched x.pairs hd.om hd.maxima 1 0) (prodVs x.attained)
    (prodEnds x.pairs) hd.atIndex (GoodProducts (prodEnds x.pairs) hd.atIndex (wAtIndex g hd))
  key : HonestSum x rs Wd (iSD x) (batched x.pairs hd.om' hd.atIndex.sEnd 2 1) (keyVars x)
    (keyEnds x) hd.key (GoodKey g (keyVars x) (keyEnds x) (chal hd.atIndex) hd.om')
  cells : HonestSum x rs Wd (iHB x) (.ofConst zeroE) (prodVs x.bits) (prodEnds x.pairs) hd.cells
    (GoodProducts (prodEnds x.pairs) hd.cells (wCells g hd))

/-- Every row is worth 0. -/
structure RowsZero (Wd : World GE) (l : Left) : Prop where
  scores : ∀ (n : Nat) (f : Aff), l.scores[n]? = some f → f.value Reading.gl Wd = 0
  division : l.division.value Reading.gl Wd = 0
  below : l.below.value Reading.gl Wd = 0
  on : l.on.value Reading.gl Wd = 0
  atIndex : l.atIndex.value Reading.gl Wd = 0
  key : l.key.value Reading.gl Wd = 0
  cells : l.cells.value Reading.gl Wd = 0

/-- **Every row that the verifier makes of the kind's masked sumchecks is worth 0.** CONDITIONAL on:
each sumcheck was heard as `Along` says; the verifier's text for the rows has returned them, at the
ledger behind the hearing (`LeftIs`); the honest side's clauses (`RowsPay`). -/
theorem rows_zero {x : OnBytes.Params.AttentionRounds} {rs : List Fmt.RoundView} {G : Fork}
    {Wd : World GE} {g : Geo} {zk : Array (Array E)} {hd : Heard} {l : Left}
    (A : Along x rs G hd) (L : LeftIs g zk hd G l) (P : RowsPay x rs Wd g zk hd) :
    RowsZero Wd l := by
  obtain ⟨wl, hwl, hsz, _, b1, b2, b3, b4, b5, b6⟩ := L.rest
  refine ⟨fun n f hf => ?_, left_zero A.division (P.division wl hwl hsz) b1,
    left_zero A.below (P.below wl hwl hsz) b2, left_zero A.on (P.on wl hwl hsz) b3,
    left_zero A.atIndex P.atIndex b4, leftKey_zero A.key P.key b5, left_zero A.cells P.cells b6⟩
  obtain ⟨⟨ug, o⟩, hz, Wt, hW, hl⟩ :=
    RowsAt.forall₂_at L.scores n f (by rw [Array.getElem?_toList]; exact hf)
  rw [Array.toList_zip, List.getElem?_zip_eq_some] at hz
  have hug : g.scores[n]? = some ug := hz.1
  have ho : hd.scores[n]? = some o := by
    rw [← Array.getElem?_toList]
    exact hz.2
  have hn : n < x.score.length := by
    rw [← A.units]
    exact (Array.getElem?_eq_some_iff.1 ho).1
  exact left_zero (A.score n _ o (List.getElem?_eq_getElem hn) ho)
    (P.score n _ o ug Wt (List.getElem?_eq_getElem hn) ho hug hW) hl

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.left_zero
#print axioms ProofFile.Honest.K5.leftKey_zero
#print axioms ProofFile.Honest.K5.RowsAt.forall₂_at
#print axioms ProofFile.Honest.K5.rows_zero
