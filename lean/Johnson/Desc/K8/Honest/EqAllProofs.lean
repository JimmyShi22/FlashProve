-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/EqAllProofs.lean: THE SMALLNESS TEST: the proof of the statement of
Johnson/Desc/K8/Honest/EqAllReturns.lean: the whole list "K8.equations" returns, under premises on
numbers, flags, marks and lengths and three tests on values. Lemmas; none of the library's goals.

By the library's cut of the text (`eqAll_split`, `eqRest`:
Johnson/Desc/First/TailClaims/EquationsTotal.lean), the laws `eqKeys_returns` and `eqCounts_returns`
(Johnson/Desc/First/TailClaims/), `eqTail_returns` (Johnson/Desc/K8/Honest/EqTailProofs.lean), and
two of the library's laws from a yes: `tame_counts` (the ledger turns on the side alone) and
`eqWeights_spec` (what the sums are).
  `open_paid`, `side_paid`   marking an owed claim as added leaves the slots, and all but the side
  `markLoop_congr`, `markRead_moved`, `marksOf_moved`   the marks do not read the two fields that
                     the first four claims lay
  `tailReady_moved`   the seventeen premises behind the first four claims, from those in front
  `live_of_cols`      where no column's weight is 0, no sum that the weights' step lays is
  `eqAll_returns`
The limits are those of Johnson/Desc/K8/Honest/EqAllReturns.lean.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.EqAllReturns
import Johnson.Desc.K8.Honest.EqTailProofs
import Johnson.Desc.First.TailClaims.EquationsForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law (St Ret OnlySide idxOk keysClaim countsClaims
  eqAll_split eqRest eqKeys_returns eqCounts_returns tame_counts eqWeights_spec)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.First.Look (laidDigits padKeyDigits)
open OnBytes.Tie.Pv.Tail.Port (readsList gamAt getD_map_range)

/-! ## Marking an owed claim as added -/

theorem open_paid {p : Psc} {F : Fork} (h : D6.Ret.Open p F) (i : Nat) :
    D6.Ret.Open p (F.paid i) :=
  ⟨h.noRow, h.started, h.sizes, h.some, h.pos, h.sized, h.fits, h.own⟩

theorem side_paid (F : Fork) (i : Nat) : OnlySide F (F.paid i) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Behind the first four claims -/

theorem markLoop_congr {a b : HTailF2} (Fn : HFun) (sg t0 : Nat)
    (h : ∀ c, a.tabAt Fn c sg = b.tabAt Fn c sg) : ∀ (count c : Nat) (m : Array Bool),
      a.markLoop Fn sg t0 count c m = b.markLoop Fn sg t0 count c m
  | 0, _, _ => by
    unfold HTailF2.markLoop
    rfl
  | count + 1, c, m => by
    unfold HTailF2.markLoop
    rw [h c]
    cases b.tabAt Fn c sg with
    | none => rfl
    | some pos =>
      dsimp only
      rw [markLoop_congr Fn sg t0 h count]

theorem markRead_moved (tl : HTailF2) (j : Option Nat) (bf : E) (Fn : HFun) (sg : Nat)
    (rd : Array (Array Bool)) :
    ({ tl with joinObj9 := j, bitFactor9 := bf } : HTailF2).markRead Fn sg rd =
      tl.markRead Fn sg rd := by
  unfold HTailF2.markRead
  dsimp only
  exact congrArg _ (markLoop_congr (a := { tl with joinObj9 := j, bitFactor9 := bf }) (b := tl)
    Fn sg _ (fun _ => rfl) _ _ _)

theorem marksOf_moved (tl : HTailF2) (j : Option Nat) (bf : E) (funs : Array HFun) :
    marksOf ({ tl with joinObj9 := j, bitFactor9 := bf } : HTailF2) funs = marksOf tl funs := by
  have e : (fun (rd : Array (Array Bool)) (x : HFun × Nat) =>
      ({ tl with joinObj9 := j, bitFactor9 := bf } : HTailF2).markRead x.1 x.2 rd) =
      fun rd x => tl.markRead x.1 x.2 rd := by
    funext rd x
    exact markRead_moved tl j bf _ _ _
  show (readsList tl funs).foldlM _ (noMarks tl) = _
  rw [e]
  rfl

/-- The seventeen premises behind the first four claims, from those in front. -/
theorem tailReady_moved {before front : Nat} {tl : HTailF2} {funs : Array HFun} {F G : Fork}
    {cs : Array Claim} {rd : Array (Array Bool)} {s1 s3 : Nat} (hS : OnlySide F G)
    (j : Option Nat) (bf : E) (h : TailReady before front tl funs F cs rd s1 s3) :
    TailReady before front { tl with joinObj9 := j, bitFactor9 := bf } funs G cs rd s1 s3 := by
  have hc : ∀ tU, colsOf G tU = colsOf F tU := fun tU => by
    unfold colsOf
    rw [hS.trees]
  refine ⟨h.four, by rw [hS.drawn]; exact h.drawn, by rw [hS.plan]; exact h.plan, h.one, h.fresh,
    h.fits, h.table, fun x hx => ?_, (marksOf_moved tl j bf funs).trans h.marks, h.allSet,
    h.inList, h.tile1, h.tile3, by rw [hS.trees]; exact h.kinds, by rw [hS.trees]; exact h.sum,
    h.count, h.apart⟩
  obtain ⟨tU, r⟩ := h.reads x hx
  exact ⟨tU, r.unit, by rw [hc]; exact r.cols, r.mat, r.len, r.seg, by rw [hc]; exact r.row⟩

/-- Where no column's weight at the batching element is 0, no sum that the weights' step lays is the
element 0. -/
theorem live_of_cols {tl tl' : HTailF2} {front : Nat} {s s' : St}
    (hW : eqWeights tl front s = .ok (tl', s')) (x : HFun × Nat) (hx : x.1.mat < tl.NM)
    (h : ∀ c, c < (tl.mats.getD x.1.mat {}).k →
      isZeroE (foldColumn tl.cfF ((tl.cfFirst.getD x.1.mat 0 + c) * tl.tau) tl.tau
        (powers s.1.theta tl.tau)) = false) : LiveAt tl' x := by
  obtain ⟨hP, e1, hgam⟩ := eqWeights_spec tl tl' front s s' hW
  have hNM : tl'.NM = tl.NM := congrArg (·.NM) e1
  have hmats : tl'.mats = tl.mats := congrArg (·.mats) e1
  have hcf : tl'.cfF = tl.cfF := congrArg (·.cfF) e1
  have hfi : tl'.cfFirst = tl.cfFirst := congrArg (·.cfFirst) e1
  have htau : tl'.tau = tl.tau := congrArg (·.tau) e1
  intro c hc
  rw [(hgam x.1.mat (by rw [hNM]; exact hx)).2]
  unfold gamAt
  rw [getD_map_range _ _ _ _ hc, hP.vp, hcf, hfi, htau]
  exact h c (by rw [← hmats]; exact hc)

/-! ## The whole -/

theorem eqAll_returns : Spec.eqAll_returns := by
  intro front tl funs F cs g rd s1 s3 h hheld hzero hlive
  rw [eqAll_split]
  refine Ret.bind (Ret.mustAs _ (by simp [h.closed.1, h.closed.2])
    (Q := fun _ s₁ => s₁ = (F, cs)) rfl) ?_
  rintro _ _ rfl
  refine Ret.bind (Ret.mustAs _ hheld (Q := fun _ s₁ => s₁ = (F, cs)) rfl) ?_
  rintro _ _ rfl
  refine Ret.bind (Ret.ask _ rfl (Q := fun b s₁ =>
    b = (F.LS.extract tl.slotA tl.slotB).all isZeroE ∧ s₁ = (F, cs)) ⟨rfl, rfl⟩) ?_
  rintro _ _ ⟨rfl, rfl⟩
  refine Ret.bind (Ret.testAs _ hzero (Q := fun _ s₁ => s₁ = (F, cs)) rfl) ?_
  rintro _ _ rfl
  refine Ret.bind (Ret.get _ h.heard (Q := fun a s₁ => g = a ∧ s₁ = (F, cs)) ⟨rfl, rfl⟩) ?_
  rintro _ _ ⟨rfl, rfl⟩
  refine Ret.bind (Ret.mustAs _ (by rw [h.rows]; simp) (Q := fun _ s₁ => s₁ = (F, cs)) rfl) ?_
  rintro _ _ rfl
  unfold eqRest
  refine Ret.bind (Ret.claims (Q := fun n s₁ => n = front + cs.size ∧ s₁ = (F, cs)) ⟨rfl, rfl⟩) ?_
  rintro _ _ ⟨rfl, rfl⟩
  refine Ret.bind (eqKeys_returns h.heard h.key h.idx h.laid front F cs) ?_
  rintro _ _ ⟨rfl, c0, rfl, hc0⟩
  refine Ret.bind (Ret.also
    (eqCounts_returns (tl := { tl with joinObj9 := some (front + cs.size) }) (g := g) h.heard
      (open_paid h.leaves g.owedJoin) front (cs.push c0))
    fun a s' e => tame_counts _ front _ s' a e) ?_
  rintro _ ⟨G, c4⟩ ⟨⟨⟨bf, rfl⟩, hled, hsh⟩, hside, new, hnew⟩
  dsimp only at hled hsh hside hnew
  subst hnew
  have hS : OnlySide F G := (side_paid F g.owedJoin).trans hside
  have hnewSh : new.map claimSh = countsClaims tl g := by
    rw [Array.toList_append, List.map_append] at hsh
    exact List.append_cancel_left hsh
  have hlen : (cs.push c0 ++ new.toArray).size = cs.size + 4 := by
    have := congrArg List.length hnewSh
    simp only [List.length_map] at this
    have h3 : (countsClaims tl g).length = 3 := rfl
    simp only [Array.size_append, Array.size_push, List.size_toArray]
    omega
  refine Ret.mono (eqTail_returns (front + cs.size) front _ funs G _ rd s1 s3
    (tailReady_moved (tl := tl) hS (some (front + cs.size)) bf (h.tail _ hlen))
    fun tl' hW x hx => ?_) ?_
  · obtain ⟨_, r⟩ := (h.tail _ hlen).reads x hx
    refine live_of_cols hW x r.mat fun c hc => ?_
    show isZeroE (foldColumn tl.cfF _ tl.tau (powers G.theta tl.tau)) = false
    rw [hS.theta]
    exact hlive x hx c hc
  · rintro _ _ ⟨tl', ties, reads, hL, rfl, rfl, hT, hR⟩
    refine ⟨bf, tl', c0 :: new, ties, reads, hL, ?_, hS, hled, ?_, ?_, hT, hR⟩
    · rw [hlen, hS.trees]
      rfl
    · apply Array.toList_inj.1
      simp
    · rw [List.map_cons, hc0, hnewSh]

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.eqAll_returns
#print axioms VerifiableInference.Desc.First.K8.Honest.tailReady_moved
#print axioms VerifiableInference.Desc.First.K8.Honest.live_of_cols
#print axioms VerifiableInference.Desc.First.K8.Honest.open_paid
