-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/BehindAtM3.lean: kind K13, the members' batching: WHAT A CHAIN's
THREAD ASKS BEHIND A MEMBER's STEP (`Behind`, Honest/Thread/Pays.lean), AT THE FIRST CHAIN's THREAD
(`Letters.thread`, Honest/Thread/First.lean) AND THE KIND's MEMBER. Statements with their proofs,
general in the thread's parameters.

`Behind` has three clauses, each asked wherever the thread holds in front and the member's own step
has accepted, from s to s'. THE FORM: no named test on values has failed, and the library's own
promise `onAt` holds at the border behind, at the honest parameters: THAT IS TEXT, AND IS SHOWN
HERE, by `onAt_behind` (Johnson/Desc/K13/Honest/PromiseBehind.lean). `rides` and `keeps` are fields
of the parameters without text: THEY ARE PREMISES HERE, asked under the member's accepted step, at
its own s' and at where the prover's run stands behind it: the two clauses of `Behind` themselves.

The road. `Behind` has the member's accepted step in hand: so the state in front passed the kind's
guards and the state behind is `withClaim` (`k13_from_yes`, FromStep.lean of this folder): NO
PREMISE "the thread in front gives the guards" IS ASKED, no half of the prover's and no coin.
Main names:
  `pubM3_honest`: what the promise's step reads of the meaning is not among the five fields that the
    honest parameters turn.
  `form_behind`: **the thread's form at the border behind, from the form in front**, at `withClaim`,
    at every row and announcement.
  `k13_thread_form_behind`: **the first clause of `Behind`**: from the form in front and the
    member's accepted step: the form behind, at the step's own s'.
  `k13_thread_behind`: **`Behind L.thread b`**, its second and third clause being premises.
    Seated.lean of this folder shows these two from an equation on each of the two fields.
  `k13_thread_form`: the state behind the step by the other road, forth from the guards (beside
    `AtK13`, the tie of the member to `atM3`, the challenges' fit and the step): it serves where
    the guards are at hand and the tie back is not.

The premises of `k13_thread_behind`. On the member: it returns only where `atM3 P` does, with the
same state (hback: the field `back` of `MemberIs`, ShapeAtM3.lean of this folder). On the table: the
library's `RowM3` (Johnson/Desc/K13/Law/AtTable.lean: a test with code gives it, but for two
equations on the plan's numbers); no public item is open in front of the place. On the meaning:
`PubM3`. OF THESE NONE FIXES A COIN, A SENT VALUE OR WHAT A LATER SUB-PROTOCOL RETURNS. `rides` and
`keeps`, as told above: WHAT THESE TWO FIX HANGS ON THE TEXT THAT IS LAID INTO THE FIELDS: a `rides`
that carries "the reply that the state holds is the one that the instance asks about" speaks of one
sent value, which is public.

Words. Thread, border, member, half, parameters: Honest/Thread/Thr.lean's head tells them. The table
of joints, its items and its promise: Johnson/Desc/First/Borders.lean's.

What is not claimed. That any of these premises holds at the library's own parameters:
BehindAtM3At.lean of this folder has what is shown there. That `rides` and `keeps` have a text that
the member's step meets. `Exchange`: the items that the row owes. That a thread holds at any run, or
that the step accepts. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K13.AtThread
import Johnson.Desc.ProofFile.Honest.K13.FromStep
import Johnson.Desc.ProofFile.Honest.Thread.First
import Johnson.Desc.K13.Honest.PromiseBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open VerifiableInference.Desc (Block Place OpenedColumn Strs)
open VerifiableInference.Desc.First (S Meaning Numbers onAt openSets pubSets start)
open VerifiableInference.Desc.Ground (takeMasksP)
open VerifiableInference.Desc.K13 (Where battRounds atM3 St)
open VerifiableInference.Desc.K13.Law (dOf RowM3)
open VerifiableInference.Desc.K13.Honest (withClaim PubM3 onAt_behind)
open ProofFile.Honest.FirstThread (Letters honest noStrs)

/-! ## 1 The state behind the member's step, forth from the guards -/

section
variable {Bk : ProverCoinCounts} {Cl Cl' W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {weights : W₀ → Weights} {pile : PileOf Xi} {P : Where}

/-- **Behind the member's step**: the state is `withClaim` at what the verifier's taking returns;
the prover's input is as it was. -/
theorem k13_thread_form (h : AtK13 T b weights pile P) {blk : Block S Cl}
    (hb : T.bs[b]? = some blk) {k : Coins Bk} {s s' : S} {m : Mid (Local W₀ Rc Xi Tr) X} {En : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hdec : ∀ rs gs t', (atM3 (Cl := Cl') P).decide s rs gs = .ok t' →
      blk.decide s rs gs = .ok t')
    (hd : drawsFit blk.rounds ds = true) (hG : K13Guards P s)
    (hS : T.Stepped blk k s m En ds y cols s') :
    ∃ t msg row, takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol) = some t ∧
      s' = withClaim s t.2.st msg row ∧ y.2.st.input = m.st.input := by
  obtain ⟨⟨⟨l, hl, hy⟩, hc⟩, hst⟩ := hS
  obtain ⟨c, -, rfl⟩ := chainSteps_one (h.half blk hb) hl
  obtain ⟨⟨f, hfin⟩, hreply, hcount, hfit, hw, hform, ⟨t, ht⟩, hlin, ⟨msg, hmsg⟩⟩ := hG
  obtain ⟨p, row, hp, hc', hst'⟩ := k13_step_any weights pile P blk (h.rounds blk hb)
    (h.oracles blk hb) _ c m ds (by rw [← h.rounds blk hb]; exact hd) hdec hfin hreply hcount hfit
    hw hform ht hlin hmsg T.chain T.ft (En.add y.1).stored (En.add y.1).tree
  have ey := Except.ok.inj (hy.symm.trans hp)
  have ec : cols = [] := Except.ok.inj (hc.symm.trans hc')
  have e1 : y.1 = p := congrArg Prod.fst ey
  have e2 : y.2.st.input = m.st.input := by rw [ey]
  rw [e1, ec] at hst
  exact ⟨t, msg, row, ht, congrArg Prod.fst (Except.ok.inj (hst.symm.trans hst')), e2⟩

end

/-! ## 2 The honest parameters -/

/-- What the promise's step reads of the meaning is not among the five fields that the honest
parameters turn. -/
theorem pubM3_honest {Pp Wt : Type} {P : Where} {N : Numbers} {Mg : Meaning Pp Wt}
    (h : PubM3 P N Mg) (ans : Nat → Nat → Pp × S → Strs → Wt → Prop)
    (test : Nat → S → Option String) : PubM3 P N (honest Mg ans test) :=
  ⟨h.frontOk, h.frontOkP, h.indexIs, h.indexThere, h.held, h.inOrder⟩

/-! ## 3 The form behind; `Behind` -/

variable {Bk : ProverCoinCounts} {Cl Cl' W₀ Rc Xi Tr X Pp Cells Tok M : Type}
  (L : Letters Bk Cl W₀ Rc Xi Tr X Pp Cells Tok M)

/-- **The thread's form at the border behind the kind's place, from the form in front.** m': where
the prover's run stands behind: its input is as it was. The row and the announcement are any. -/
theorem form_behind {b : Nat} {P : Where} (hT : RowM3 L.N L.MgP.more L.links L.ps b)
    (hF : PubM3 P L.N L.MgP) (hQ : ((pubSets L.MgP.more L.links L.ps)[b]?).getD [] = [])
    {k : Coins Bk} {s : S} {m m' : Mid (Local W₀ Rc Xi Tr) X} (hm : m'.st.input = m.st.input)
    {n : Nat} {t : List Nat × St} (msg : Array OracleNotice) (row : TensorRow)
    (ht : takeMasksP (dOf s) s.out.indexMasks n = some t)
    (hlin : linOk s.st.codes P.lin = true) (h : L.thread.Form b k s m) :
    L.thread.Form (b + 1) k (withClaim s t.2.st msg row) m' := by
  obtain ⟨h1, h2⟩ := h
  have hf : s.failed = none := Option.isNone_iff_eq_none.1 h1
  have h2' : onAt L.N L.mgP L.links L.ps[b]? (((openSets L.links L.ps (start L.links))[b]?).getD [])
      (((pubSets L.mgP.more L.links L.ps)[b]?).getD []) (L.pubOf m.st.input.x, s) noStrs := h2
  refine ⟨h1, ?_⟩
  show onAt L.N L.mgP L.links L.ps[b + 1]?
    (((openSets L.links L.ps (start L.links))[b + 1]?).getD [])
    (((pubSets L.mgP.more L.links L.ps)[b + 1]?).getD [])
    (L.pubOf m'.st.input.x, withClaim s t.2.st msg row) noStrs
  rw [hm]
  exact onAt_behind L.N L.mgP L.links L.ps b P hT (pubM3_honest hF L.ans L.test) _ s noStrs noStrs
    msg row ht hlin hf (fun _ => trivial) (fun _ => trivial) (fun _ => trivial)
    (fun q hq => by
      have hq' : q ∈ ((pubSets L.MgP.more L.links L.ps)[b]?).getD [] := hq
      rw [hQ] at hq'
      cases hq')
    (fun q hq => by
      have hq' : q ∈ ((pubSets L.MgP.more L.links L.ps)[b]?).getD [] := hq
      rw [hQ] at hq'
      cases hq') h2'

/-- **The first clause of `Behind`**: from the thread's form in front and the member's accepted
step: the form behind, at the step's own s'. hback: the member returns only where the kind's own
sub-protocol does, with the same state. -/
theorem k13_thread_form_behind {b : Nat} {P : Where} (hT : RowM3 L.N L.MgP.more L.links L.ps b)
    (hF : PubM3 P L.N L.MgP) (hQ : ((pubSets L.MgP.more L.links L.ps)[b]?).getD [] = [])
    {blk : Block S Cl} {k : Coins Bk} {s s' : S} {m : Mid (Local W₀ Rc Xi Tr) X} {En : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hback : ∀ rs gs t', blk.decide s rs gs = .ok t' →
      (atM3 (Cl := Cl') P).decide s rs gs = .ok t')
    (h : L.thread.Form b k s m) (hS : L.thread.Stepped blk k s m En ds y cols s') :
    L.thread.Form (b + 1) k s' y.2 := by
  obtain ⟨hG, t, msg, row, ht, -, rfl, e2⟩ := k13_from_yes (Cl' := Cl') hback hS
  exact form_behind L hT hF hQ e2 msg row ht hG.lin h

/-- **`Behind` at the kind's member of the first chain's thread.** hrides, hkeeps: the two clauses
that have no text, as `Behind` asks them: under the thread in front and the member's accepted step.
-/
theorem k13_thread_behind {b : Nat} {P : Where} (hT : RowM3 L.N L.MgP.more L.links L.ps b)
    (hF : PubM3 P L.N L.MgP) (hQ : ((pubSets L.MgP.more L.links L.ps)[b]?).getD [] = [])
    (hback : ∀ blk, L.thread.bs[b]? = some blk → ∀ s rs gs t', blk.decide s rs gs = .ok t' →
      (atM3 (Cl := Cl') P).decide s rs gs = .ok t')
    (hrides : ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m En ds y cols s',
      Thr L.thread b k s m En → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m En ds y cols s' → L.rides (b + 1) y.2.st.input s')
    (hkeeps : ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m En ds y cols s',
      Thr L.thread b k s m En → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m En ds y cols s' → L.keeps b s s') : Behind L.thread b := by
  intro blk hb k s m En ds y cols s' hThr hd hS
  exact ⟨k13_thread_form_behind (Cl' := Cl') L hT hF hQ (hback blk hb s) hThr.2.2.1 hS,
    hrides blk hb k s m En ds y cols s' hThr hd hS, hkeeps blk hb k s m En ds y cols s' hThr hd hS⟩

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_thread_form
#print axioms ProofFile.Honest.K13.pubM3_honest
#print axioms ProofFile.Honest.K13.form_behind
#print axioms ProofFile.Honest.K13.k13_thread_form_behind
#print axioms ProofFile.Honest.K13.k13_thread_behind
