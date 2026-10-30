-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/DrawAtBatch.lean: THE SMALLNESS TEST: AT EVERY STATE THAT THE FIRST CHAIN's OWN BLOCKS
REACH IN FRONT OF A SEGMENT's BATCHING, AT ALL 25 SEGMENTS: THE DRAWN MATRIX's ENTRIES ARE 1, -1 OR
0; EACH MATRIX's FIRST COLUMN IS THE SUM OF THE NUMBERS OF COLUMNS IN FRONT; THERE ARE 128
COMBINATIONS: THREE OF THE FOUR FIELDS OF `TieFront` (Johnson/Desc/K8/Honest/TieWords.lean). UNDER
THE SCOPE, THE FILES READ AND IM.Open. Definitions and lemmas; none of the library's goals. No
prover stands in them; nothing on completeness, soundness or hiding. Why. The draw's decision lays
whatever entries its round shows; that these are -1, 0 or 1 is tested by the frame, in the block's
step (roundsFit, Johnson/Desc/Block.lean): so the fact is had of a reached state, not of a
decision's yes.

  `drawView`, `keeps4_draw`   the five fields read; the lookup on the digits lays none of them
  `DrawnOk tl`, `drawnOk_view`, `tieFront_of_drawn`   the last two fields of `TieFront`; they read
      the view alone; `TieFront` from them, "128 combinations" and its bound on the matrices' rows
  `getD_trit`   an entry of a list of such entries, or the default 0
  `range_take_sum`   a walk over the first numbers against the sum of a list's front
  **`means_drawn`**   behind a yes of the draw's step: fit_iff
      (Johnson/Desc/First/K8/LawRoundFit.lean): what the frame's test gives at the draw's round;
      MeansAtS (HearMeans.lean), firstColumns_aux (Law.lean), putTl_tl (LawAtS.lean)
  `drawn_of_view`   from the reading to the data
  `view_back`   the blocks between the draw and the batching leave every reading that the lookup
      on the digits does not lay: P1K8S.staysAt_open (Johnson/P1K8R/WideAtSeat.lean),
      LinkJoin.reach_leaves (Johnson/Desc/First/Link/Law/ReachLeaves.lean)
  **`drawn_at_batch`**   P1K8S.sitsAt_open (Johnson/P1K8R/OrderAtSeat.lean): the law of the draw's
      block's step; reach_pred (Johnson/Road/K4/FunsThirdReached.lean); LinkJoin.read_of_tl
      (PlannedAtDraw.lean); IM.k8_tau_128 (Johnson/K8Q14R/TauAt.lean)
Limits. Nothing on the second field of `TieFront` (each (m + 2) / 3 is at most 2^64). Nothing on
whether any state is reached.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P1K8R.OrderAtSeat
import Johnson.P1K8R.WideAtSeat
import Johnson.Desc.K8.Honest.TieWords
import Johnson.Desc.First.K8.Law
import Johnson.Desc.First.K8.LawAtS
import Johnson.Desc.First.K8.LawRoundFit
import Johnson.Desc.First.Link.Law.PlannedAtDraw
import Johnson.Desc.First.Link.Law.ReachLeaves
import Johnson.K8Q14R.TauAt
import Johnson.Road.K4.FunsThirdReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.First.K8.Honest
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Road.K4 (reach_pred)

/-- What the draw of the smallness test's matrix lays, and three planned fields. -/
def drawView (tl : HTailF2) := (tl.cfF, tl.cfFirst, tl.NM, tl.mats, tl.tau)

/-- The lookup on the digits lays none of the five. -/
theorem keeps4_draw : Keeps4 drawView := fun _ _ _ _ _ => rfl

/-- **The last two fields of `TieFront`** (Johnson/Desc/K8/Honest/TieWords.lean): the drawn matrix's
entries are 1, -1 or 0; each matrix's first column is the sum of the numbers of columns in front. -/
def DrawnOk (tl : HTailF2) : Prop :=
  (∀ j, tl.cfF.getD j 0 = 1 ∨ tl.cfF.getD j 0 = -1 ∨ tl.cfF.getD j 0 = 0) ∧
  ∀ mu, mu < tl.NM → tl.cfFirst.getD mu 0 =
    (List.range mu).foldl (fun n nu => n + (tl.mats.getD nu {}).k) 0

theorem drawnOk_view {a b : HTailF2} (h : drawView a = drawView b) (k : DrawnOk b) : DrawnOk a := by
  simp only [drawView, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, -⟩ := h
  unfold DrawnOk
  rw [h1, h2, h3, h4]
  exact k

/-- `TieFront` from "128 combinations", its bound on the matrices' rows and `DrawnOk`. -/
theorem tieFront_of_drawn {tl : HTailF2} (h1 : tl.tau = 128)
    (h2 : ∀ nu, nu < tl.NM → ((tl.mats.getD nu {}).m + 2) / 3 ≤ 2 ^ 64) (k : DrawnOk tl) :
    TieFront tl := ⟨by rw [h1]; norm_num, h2, k.1, k.2⟩

/-- An entry of such a list, or the default 0. -/
theorem getD_trit (l : List Int) (h : ∀ t ∈ l, t = -1 ∨ t = 0 ∨ t = 1) (j : ℕ) :
    l.toArray.getD j 0 = 1 ∨ l.toArray.getD j 0 = -1 ∨ l.toArray.getD j 0 = 0 := by
  by_cases hj : j < l.length
  · have e : l.toArray.getD j 0 = l[j] := by simp [Array.getD_eq_getD_getElem?, hj]
    rw [e]
    rcases h _ (List.getElem_mem hj) with q | q | q
    · exact Or.inr (Or.inl q)
    · exact Or.inr (Or.inr q)
    · exact Or.inl q
  · have e : l.toArray.getD j 0 = 0 := by
      simp [Array.getD_eq_getD_getElem?, List.getElem?_eq_none (Nat.le_of_not_lt hj)]
    exact Or.inr (Or.inr e)

/-- A walk over the first numbers that adds f is the sum of a list's front, where f reads the
list. The like over Finset.range: sum_take (Johnson/Desc/First/K8/Law.lean). -/
theorem range_take_sum (l : List ℕ) (f : ℕ → ℕ) (hf : ∀ i, i < l.length → f i = l.getD i 0) :
    ∀ mu, mu ≤ l.length → (List.range mu).foldl (fun n nu => n + f nu) 0 = (l.take mu).sum := by
  intro mu
  induction mu with
  | zero =>
    intro _
    simp
  | succ m ih =>
    intro h
    have hm : m < l.length := h
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih (by omega), hf m hm,
      List.take_add_one, List.sum_append]
    simp [List.getD_eq_getElem?_getD, hm]

/-- **Behind a yes of the draw's step the data hold `DrawnOk`.** The three lines that read
firstColumns_aux are those of the proof of firstColumns_get (Johnson/Desc/First/K8/Law.lean), which
ends in the typed side's sum. -/
theorem means_drawn {p : K8.Par} {st st' : S} {r : Fmt.RoundView}
    (hf : roundsFit [K8.round p] [r] = true) (hm : MeansAtS p st r st') :
    ∃ tl, st'.tl? = some tl ∧ DrawnOk tl ∧ tl.tau = p.tau := by
  obtain ⟨tl, ht, -, -, -, hN, hk, -, hT, -, e⟩ := hm
  refine ⟨{ tl with cfF := r.drawn.trits.toArray, cfFirst := firstColumns p }, ?_,
    ⟨fun j => getD_trit _ ((fit_iff p r).1 hf).2.2.2.2 j, fun mu hmu => ?_⟩, hT⟩
  · rw [e]
    exact putTl_tl st tl _ ht
  · have hmu' : mu < p.ks.length := by
      rw [← hN]
      exact hmu
    have key := (firstColumns_aux p.ks #[0] (by simp)).2.2 mu hmu'.le
    have e0 : (#[0] : Array Nat).size - 1 + mu = mu := by simp
    rw [e0] at key
    show (firstColumns p).getD mu 0 =
      (List.range mu).foldl (fun n nu => n + (tl.mats.getD nu {}).k) 0
    have hs : ∀ i, i < p.ks.length → (tl.mats.getD i {}).k = p.ks.getD i 0 := by
      intro i hi
      rw [← hk] at hi ⊢
      have hi' : i < tl.mats.size := by simpa using hi
      simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, hi']
    rw [range_take_sum p.ks (fun nu => (tl.mats.getD nu {}).k) hs mu hmu'.le]
    unfold firstColumns
    rw [key]
    simp

/-- From the reading to the data. -/
theorem drawn_of_view {s : S} {tlP : HTailF2} (hv : readTl drawView s = some (drawView tlP))
    (k : DrawnOk tlP) : ∃ tl, s.tl? = some tl ∧ DrawnOk tl ∧ tl.tau = tlP.tau := by
  unfold readTl at hv
  cases hts : s.tl? with
  | none =>
    rw [hts] at hv
    exact absurd hv (by simp)
  | some tl =>
    rw [hts] at hv
    exact ⟨tl, rfl, drawnOk_view (Option.some.inj hv) k,
      congrArg (·.2.2.2.2) (Option.some.inj hv)⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Q : Type} {start : Q → S}

/-- From the batching's border back to the border behind the draw: the blocks between leave the five
fields: P1K8S.staysAt_open (Johnson/P1K8R/WideAtSeat.lean) in LinkJoin.reach_leaves
(Johnson/Desc/First/Link/Law/ReachLeaves.lean), as LinkJoin.stretch_leaves (PlannedToBatch.lean)
calls it. -/
theorem view_back (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {x : ℕ × ℕ × ℕ}
    (hx : x ∈ P1K8S.stretches) {z : Q} {s : S}
    (h : Reach 0 c.blocksInOrder start (14 * x.1 + x.2.1 + 3 + x.2.2) (z, s)) :
    ∃ t, Reach 0 c.blocksInOrder start (14 * x.1 + x.2.1 + 3) (z, t) ∧
      readTl drawView s = readTl drawView t :=
  LinkJoin.reach_leaves 0 c.blocksInOrder start (readTl drawView) (14 * x.1 + x.2.1 + 3) x.2.2
    (fun j _ h2 b hb => (P1K8S.staysAt_open hS hR O x hx).2 (j - (14 * x.1 + x.2.1 + 3))
      (by omega) b
      (by
        rw [show 14 * x.1 + x.2.1 + 3 + (j - (14 * x.1 + x.2.1 + 3)) = j by omega]
        exact hb) _ drawView keeps4_draw) (z, s) h

/-- **AT EVERY STATE REACHED IN FRONT OF A SEGMENT's BATCHING THE DATA HOLD `DrawnOk`, AND 128
COMBINATIONS**, at all 25 segments: back over the blocks that leave the five fields, then one step
back over the draw's block, whose step holds the frame's test. -/
theorem drawn_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25) {z : Q}
    {s : S} (h : Reach 0 c.blocksInOrder start (14 * l + (if l = 24 then 11 else 9)) (z, s)) :
    ∃ tl, s.tl? = some tl ∧ DrawnOk tl ∧ tl.tau = 128 := by
  have hx : (l, (if l = 24 then 5 else 4), (if l = 24 then 3 else 2)) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  have hp : (l, if l = 24 then 5 else 4) ∈ P1K8S.places :=
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  obtain ⟨Lk, b8, Xl, -, -, hf8, hXl, -, -, -, hstep⟩ := P1K8S.sitsAt_open hS hR O _ hp
  have e : 14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2) =
      14 * l + (if l = 24 then 11 else 9) := by
    split_ifs <;> omega
  rw [← e] at h
  obtain ⟨s₇, h7, e7⟩ := view_back hS hR O hx h
  obtain ⟨z', s₆, t₇, b, e', -, hb, R, cs, -, hst⟩ :=
    reach_pred (k := 14 * l + (if l = 24 then 5 else 4) + 2) h7
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e'
  obtain rfl : b8 = b := Option.some.inj (hf8.symm.trans hb)
  obtain ⟨r, -, hfit, hm, -, -⟩ := (hstep 0 _ _ _ _ _).1 hst
  obtain ⟨tl₇, ht, D, hT⟩ := means_drawn hfit hm
  obtain ⟨tl, hs, D', e''⟩ := drawn_of_view (e7.trans (LinkJoin.read_of_tl ht)) D
  exact ⟨tl, hs, D', e''.trans (hT.trans (IM.k8_tau_128 hS hR O (by omega) hXl))⟩

end

end P1K8

#print axioms P1K8.keeps4_draw
#print axioms P1K8.drawnOk_view
#print axioms P1K8.tieFront_of_drawn
#print axioms P1K8.getD_trit
#print axioms P1K8.range_take_sum
#print axioms P1K8.means_drawn
#print axioms P1K8.drawn_of_view
#print axioms P1K8.view_back
#print axioms P1K8.drawn_at_batch
