-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/TotalJoin.lean: THE HEART OF THE JOIN FOR THE ITEM "totalB": THE SEALED LIBRARY's
EQUATION ON STATES, CALLED AT A LINK. Statements and proofs ON THE VERIFIER's TEXT, under `SealLaw`
(Honest/K9/TotalFront.lean); no prover is in this file, and no goal is stated.
  `moves_ok`       under `SealLaw`: each of the link's two moves (add what the gatherer returns; the runs behind)
      meets the library's `MoveOk`: as the library's own `joinAsks_of_runs` proves it
      (Johnson/Desc/First/Link/Law/LinkJoinRuns.lean)
  **`one_sum`**      under `SealLaw`, at a yes of the batching's step at s with s' behind, where what is fixed at s
      meets the promise Ok, and the link's runs behind return t at s': the round has drawn one element x, and AT EVERY
      y the ledger's one equation at t, read at t, IS the polynomial of the runs' terms, off what is fixed at s, at x:
      the library's `value_at` (Johnson/Desc/First/Batch/Law/Row3Tools.lean) and `terms_link`, called
  `termsRuns_zero`, `termsAt_zero`   where every coefficient of every run's terms is 0, so is every coefficient of the
      runs' terms in a row; and a polynomial whose coefficients are all 0 is worth 0
  **`one_zero`**     so: where, at one y, every entry's terms have the coefficient 0 at every number n: the one
      equation at t, read at t at that y, is worth 0
`data_same`      under `SealLaw`: over the batching's step and the runs behind, K9's part is there at t, and the
witness's data at t ARE those at the part a AT s: the library's `tab_of_rb`, `tabAt_quiet`, `dataAt_door`, `data_at`,
called (the book: `LinkShare.two`, `hbook2_of_share`)
**`totalQ_front`**   THE VALUE HALF OF THE ITEM, FROM THE STATE IN FRONT: under `SealLaw`, at a yes of the batching's
step at s with s' behind, Ok at what is fixed at s, and the runs behind returning t: where every entry's terms, off
what is fixed at s, at the witness's data AT s, have the coefficient 0: the library's `totalQ own t rd`
`termsBack_append`   beside these, on the named sentences and under no `SealLaw`: `TermsBack`
(Honest/K9/TotalFront.lean) at two lists of terms in a row, from `TermsBack` at each: called by
Honest/K9/TotalItems.lean
No member. `totalQ_front` is called by Honest/K9/TotalAfter.lean's two joins.
WHAT IS NOT CLAIMED. `SealLaw` at any link. Ok at any state. That any coefficient is 0. That the runs behind return.
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.TotalFront
import Johnson.Desc.First.Batch.Law.Row3Tools
import Johnson.Desc.First.Batch.Law.OnAFree
import Johnson.Desc.First.Batch.Law.MovesBlock
import Johnson.Desc.First.Link.Law.LinkExps
import Johnson.Desc.First.Link.Law.LinkJoinRuns
import Johnson.Desc.First.Link.Law.LettersAt
import Johnson.Desc.First.Link.Law.SortShare
import Johnson.Desc.First.Batch.Law.JoinTable
import Johnson.Desc.First.Batch.Law.AtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First

variable {α : Type} {sub : First.ModelPart} {l : ℕ} {Lk : Link S Claim} {p : Desc.K9.Where} {φ : S → α}
  {Ok : α × Option K9L.Pub9 → Prop} {nU : Array ℕ} {u : HTailF2}
  {π : α → Option HTailF2 × Option (Array HFun)}
  {tmOf : ℕ × String → ℕ → α × Option K9L.Pub9 → K9L.Bound Cb.Gl.E → List (ℕ × Cb.Gl.E)}
  {lenOf : ℕ × String → α × Option K9L.Pub9 → ℕ}

/-- The link's two moves meet the library's premise on a move. -/
theorem moves_ok (A : SealLaw sub l Lk p φ Ok nU u π tmOf lenOf) :
    ∀ m ∈ LinkJoin.moves₁ Lk (LinkJoin.rlOf Lk tmOf lenOf) ++ LinkJoin.moves₂ (α := α) Lk,
      K9L.MoveOk Reading.gl Desc.K9.atS (K9L.O9 φ Ok (LinkJoin.FullAt nU)) (K9L.Fx9 φ Ok) m := by
  have HF := K9L.fitsM_atS (K := Cb.Gl.E) φ A.runs.hφ Ok (LinkJoin.FullAt nU) p
  intro m hm
  rcases List.mem_append.1 hm with hm | hm
  · obtain rfl := List.mem_singleton.1 hm
    exact JoinAtBlocks.claimsInBy_addOk Reading.gl Desc.K9.atS (K9L.O9 φ Ok (LinkJoin.FullAt nU)) (K9L.Fx9 φ Ok) p HF
      Lk.each Lk.hear Lk.order _ (LinkJoin.rlOf_runs Lk tmOf lenOf)
      (LinkJoin.rlOf_runOk Reading.gl Desc.K9.atS _ _ Lk tmOf lenOf (by rw [A.seg.order]; exact A.runs.hpay))
  · obtain rfl := List.mem_singleton.1 hm
    exact ⟨JoinAtBlocks.runBehind_quietOk Desc.K9.atS (K9L.O9 φ Ok (LinkJoin.FullAt nU)) (K9L.Fx9 φ Ok) p HF Lk
      (by rw [A.seg.orderAfter]; exact A.runs.hquiet), fun _ _ _ => rfl, fun _ => rfl⟩

/-- **The one sum.** -/
theorem one_sum (A : SealLaw sub l Lk p φ Ok nU u π tmOf lenOf) (ft : ℕ) (s s' t : S) (rs : List Fmt.RoundView)
    (cols : List Desc.OpenedColumn) (k : ℕ)
    (hs : (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).step ft s rs cols = .ok (s', k))
    (hOk : Ok (K9L.fixed9 φ s)) (ht : Lk.runBehind s' = .ok t) :
    ∃ r x, rs = [r] ∧ r.drawn.elems = [x] ∧ ∀ y, K9L.oneK Desc.K9.atS Reading.gl t t y =
      Desc.termsAt Cb.Gl.E (K9L.termsRuns (K9L.fixed9 φ s) y (LinkJoin.rlOf Lk tmOf lenOf) 0)
        (Reading.gl.val (E.ofTriple x)) := by
  have HF := K9L.fitsM_atS (K := Cb.Gl.E) φ A.runs.hφ Ok (LinkJoin.FullAt nU) p
  have hon := K9L.yes_onA p _ _ A.share.hb₁ ft s rs cols s' k hs
  obtain ⟨r, x, a, o, cls, hr, hx, ha, ho, hy⟩ := A.share.hb₁ ft s rs cols s' k hs
  refine ⟨r, x, hr, hx, fun y => ?_⟩
  have hy2 : K9L.MovesYes Desc.K9.atS
      ((LinkJoin.moves₁ Lk (LinkJoin.rlOf Lk tmOf lenOf) ++ LinkJoin.moves₂ (α := α) Lk).map (·.move))
      (Desc.K9.atS.set s { a with owed := o.owed, L := o.L, F := o.F }) t (cls ++ []) :=
    K9L.movesYes_append Desc.K9.atS _ _ _ s' t cls [] hy ⟨t, [], [], ⟨ht, rfl⟩, ⟨rfl, rfl⟩, rfl⟩
  have h := K9L.value_at Reading.gl Desc.K9.atS (K9L.O9 φ Ok (LinkJoin.FullAt nU)) (K9L.Fx9 φ Ok) p HF _
    (moves_ok A) A.full.hend s t a o x _ ⟨hon, hOk⟩ ha ho hy2 y
  rw [h]
  show Desc.termsAt Cb.Gl.E (K9L.termsOf (K9L.fixed9 φ s) y _ 0) _ = _
  rw [LinkJoin.terms_link]

/-- Where every run's terms have the coefficient 0, so have the runs' terms in a row. -/
theorem termsRuns_zero {T P K : Type} [Zero K] (q : P) (y : K9L.Bound K) :
    ∀ (rl : List (K9L.TermedRun T P K)) (n : ℕ), (∀ r ∈ rl, ∀ n, ∀ c ∈ r.tm n q y, c.2 = 0) →
      ∀ c ∈ K9L.termsRuns q y rl n, c.2 = 0
  | [], _, _, c, hc => by simp [K9L.termsRuns] at hc
  | r :: rl, n, h, c, hc => by
    unfold K9L.termsRuns at hc
    rcases List.mem_append.1 hc with hc | hc
    · exact h r List.mem_cons_self n c hc
    · exact termsRuns_zero q y rl _ (fun r' hr' => h r' (List.mem_cons_of_mem _ hr')) c hc

/-- A polynomial whose coefficients are all 0 is worth 0. -/
theorem termsAt_zero {K : Type} [Field K] (t : List (ℕ × K)) (x : K) (h : ∀ c ∈ t, c.2 = 0) :
    Desc.termsAt K t x = 0 := by
  unfold Desc.termsAt
  refine List.sum_eq_zero fun z hz => ?_
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hz
  rw [h c hc, mul_zero]

/-- **The one equation at t is worth 0 wherever every entry's terms have the coefficient 0.** -/
theorem one_zero (A : SealLaw sub l Lk p φ Ok nU u π tmOf lenOf) (ft : ℕ) (s s' t : S) (rs : List Fmt.RoundView)
    (cols : List Desc.OpenedColumn) (k : ℕ)
    (hs : (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).step ft s rs cols = .ok (s', k))
    (hOk : Ok (K9L.fixed9 φ s)) (ht : Lk.runBehind s' = .ok t) (y : K9L.Bound Cb.Gl.E)
    (hz : ∀ o ∈ Lk.order, ∀ n, ∀ c ∈ tmOf o n (K9L.fixed9 φ s) y, c.2 = 0) :
    K9L.oneK Desc.K9.atS Reading.gl t t y = 0 := by
  obtain ⟨r, x, _, _, h⟩ := one_sum A ft s s' t rs cols k hs hOk ht
  rw [h y]
  refine termsAt_zero _ _ (termsRuns_zero _ y _ 0 fun r' hr' n c hc => ?_)
  obtain ⟨o, ho, _, e1, _⟩ := LinkJoin.mem_rlOf hr'
  rw [e1] at hc
  exact hz o ho n c hc

/-- **The witness's data at t are those at s**: over the batching's step and the runs behind. a: K9's part at s. -/
theorem data_same (A : SealLaw sub l Lk p φ Ok nU u π tmOf lenOf) (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → Sound.MsgQ)
    (ft : ℕ) (s s' t : S) (rs : List Fmt.RoundView) (cols : List Desc.OpenedColumn) (k : ℕ)
    (hs : (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).step ft s rs cols = .ok (s', k))
    (ht : Lk.runBehind s' = .ok t) (a : Desc.K9.Part) (ha : Desc.K9.atS.get? s = some a) :
    (Desc.K9.atS.get? t).isSome = true ∧
      K9L.dataAt Desc.K9.atS t (K9L.tabAt own rd t) = Sound.dataQ own a rd := by
  have lens : ∀ (e : S) (x : Desc.K9.Part), (Desc.K9.atS.get? e).isSome = true →
      ∃ a', Desc.K9.atS.get? (Desc.K9.atS.set e x) = some a' ∧ a'.L = x.L ∧ a'.d.st = x.d.st := fun e x h => by
    obtain ⟨a', e0, _, e2, e3⟩ := K9L.atS_reads e x h
    exact ⟨a', e0, e2, e3⟩
  obtain ⟨p1, p2⟩ := LinkJoin.parts_batch Lk p A.share.hb₁ ft s rs cols s' k hs
  have hRb := (A.share.two.1 ft s rs cols s' k hs).1
  have t1 := LinkJoin.tab_of_rb own rd s s' hRb p1 p2
  have d1 := (K9L.drawMoves_door Desc.K9.atS lens p _ _ A.share.hb₁ (fun m hm => by
    obtain rfl := List.mem_singleton.1 hm
    exact JoinAtBlocks.claimsInBy_door Desc.K9.atS Lk.each Lk.hear Lk.order fun r hr => by
      rw [← LinkJoin.rlOf_runs Lk tmOf lenOf] at hr
      obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
      exact LinkJoin.rlOf_door Desc.K9.atS Lk tmOf lenOf (by rw [A.seg.order]; exact A.runs.hpayd) r' hr')
    ft s rs cols s' k hs).2
  have hy2 : K9L.MovesYes Desc.K9.atS [K9L.Move.quiet Lk.runBehind] s' t [] :=
    ⟨t, [], [], ⟨ht, rfl⟩, ⟨rfl, rfl⟩, rfl⟩
  obtain ⟨t2, d2⟩ := K9L.tabAt_quiet own rd [K9L.Move.quiet Lk.runBehind]
    (fun m hm => by
      obtain rfl := List.mem_singleton.1 hm
      exact JoinAtBlocks.runBehind_door Desc.K9.atS Lk (by rw [A.seg.orderAfter]; exact A.runs.hquietd))
    (LinkJoin.hbook2_of_share (α := α) A.share) s' t [] p2 hy2
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 p2
  obtain ⟨c, hc, _, _⟩ := d2 b hb
  refine ⟨by rw [hc]; rfl, ?_⟩
  rw [t2, t1, K9L.dataAt_door Desc.K9.atS s' t d2 p2, K9L.dataAt_door Desc.K9.atS s s' d1 p1]
  exact K9L.data_at own rd s a ha

/-- **THE VALUE HALF OF THE ITEM, FROM THE STATE IN FRONT**: where every entry's terms, off what is fixed at s, at the
witness's data AT s, have the coefficient 0: the library's `totalQ own t rd`. -/
theorem totalQ_front (A : SealLaw sub l Lk p φ Ok nU u π tmOf lenOf) (own : List (ℕ × ℕ))
    (rd : ℕ × ℕ → Sound.MsgQ) (ft : ℕ) (s s' t : S) (rs : List Fmt.RoundView) (cols : List Desc.OpenedColumn) (k : ℕ)
    (hs : (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).step ft s rs cols = .ok (s', k))
    (hOk : Ok (K9L.fixed9 φ s)) (ht : Lk.runBehind s' = .ok t) (a : Desc.K9.Part)
    (ha : Desc.K9.atS.get? s = some a)
    (hz : ∀ o ∈ Lk.order, ∀ n, ∀ c ∈ tmOf o n (K9L.fixed9 φ s) (Sound.dataQ own a rd), c.2 = 0) :
    Sound.totalQ own t rd := by
  obtain ⟨hp, hd⟩ := data_same A own rd ft s s' t rs cols k hs ht a ha
  refine (K9L.total_iff own rd t).2 ⟨hp, ?_⟩
  rw [hd]
  exact one_zero A ft s s' t rs cols k hs hOk ht _ hz

/-- `TermsBack` at two lists of terms in a row, from `TermsBack` at each. -/
theorem termsBack_append {V W X Pb : Type} {Bk : ProverCoinCounts} {T : Thread Bk S Claim V W X Pb} {b : ℕ}
    {own : List (ℕ × ℕ)} {rdW : T.Wt → ℕ × ℕ → Sound.MsgQ}
    (tm₁ tm₂ : ℕ → α × Option K9L.Pub9 → K9L.Bound Cb.Gl.E → List (ℕ × Cb.Gl.E)) (Front₁ Front₂ : S → T.Wt → Prop)
    (h₁ : TermsBack Lk p φ Ok T b own rdW tm₁ Front₁) (h₂ : TermsBack Lk p φ Ok T b own rdW tm₂ Front₂) :
    TermsBack Lk p φ Ok T b own rdW (fun n q y => tm₁ n q y ++ tm₂ n q y) (fun s v => Front₁ s v ∧ Front₂ s v) := by
  intro κ s m En ds y cols s' x z G St a v ha hOk hF n c hc
  rcases List.mem_append.1 hc with hc | hc
  · exact h₁ κ s m En ds y cols s' x z G St a v ha hOk hF.1 n c hc
  · exact h₂ κ s m En ds y cols s' x z G St a v ha hOk hF.2 n c hc

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.termsBack_append
#print axioms ProofFile.Honest.K9.data_same
#print axioms ProofFile.Honest.K9.totalQ_front
#print axioms ProofFile.Honest.K9.moves_ok
#print axioms ProofFile.Honest.K9.one_sum
#print axioms ProofFile.Honest.K9.termsRuns_zero
#print axioms ProofFile.Honest.K9.termsAt_zero
#print axioms ProofFile.Honest.K9.one_zero
