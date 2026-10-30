-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/FoldAtHeadSeg.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE: IN FRONT OF
THE OUTPUT HEAD's SEGMENT's BATCHING THE MATRIX IS COUNTED AS DRAWN ONCE (tl.foldDrawn = 1): IN THE
GOALS' SCOPE, THE FILES READ, UNDER AN OPENING OF THE DESCRIPTION AND ITS TEST ON ITS PLAN, AT EVERY
STATE THAT THE FIRST CHAIN's OWN BLOCKS REACH AT 347, FROM WHATEVER START. THAT ANY SUCH STATE IS
REACHED IS NOT SHOWN. Lemmas; none of the library's goals.

  `seatDigits_fold` what the seat of the lookup on the digits lays counts one drawing more
  `fold_behind_digits` behind a yes of the seated lookup on the digits: c.tl?.map (·.foldDrawn) =
                   s.tl?.map (·.foldDrawn + 1)
  **`fold_at_head_seg`** the scope · the files read · the opening · its test on its plan · Reach 0
                   c.blocksInOrder start 347 (z, s) ⊢ ∃ tl, s.tl? = some tl ∧ tl.foldDrawn = 1
HOW. FOUR BLOCKS BACK FROM 347. The head's segment's blocks that hear are K7, K2, K3, K6, K1, K8,
K1, K3, K11 (`kindsBeforeBatching`, Johnson/Desc/First/Driver/Chain.lean), at 338 and on. The merge, at 346,
leaves the test's data: the library's P1K8S.merge_leaves (Johnson/P1K8R/WideAtSeat.lean) · the
lookup on the digits, at 345, counts one more: `fold_behind_digits` · K1's sending of the digits, at
344, leaves the test's data: P1K8S.digits_leave (the same file) · behind a yes of the draw's block,
at 343, the count is 0: `fold0_of_step` (KeepsFold.lean) at the seat that P1K8S.sitsAt_of_alone
(Johnson/P1K8R/Sits.lean) gives off IM.k8_of_head. K1's other sending, at 342, which lays the test's
data anew at the head's segment, stands in front of the draw: the road does not cross it.
WRITTEN A FURTHER TIME: `seatDigits_fold` and `fold_behind_digits` are the proofs of
`seatDigits_slot` and `slot_behind_digits` (SlotAtReach.lean) at another field, without the ledger's
sizes. KIN, NOT CALLED (files that the library may not hold): the same count as a rider on a thread:
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/LaysFold.lean lays "foldDrawn = 1" behind the lookup's
member, under "foldDrawn = 0" in front; Johnson/Desc/ProofFile/Honest/K8/LaysFoldAt.lean lays that 0
at 343. Here no rider is wanted. Nearer kin at a step, under
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/: `digits_put` (StateBehind.lean) writes the seat's put
out whole; `form_tl` and `digits_tl_site` (DigitsTlKept.lean) have the end of `fold_behind_digits`,
and more, behind a step of the same member; they stand over that folder's own sites.
No option is raised, no instance taken away. TACTICS THAT SEARCH: `simp [a list]` on eight lines ·
`simp only [a list]` on one · a bare `simp` on one, on a sum of two ifs · `omega` on five lines, on
numbers of segments alone.
Limits. NOTHING SAYS THAT ANY STATE IS REACHED AT 347: where none is, all is idle. THE HEAD's
SEGMENT ALONE. IN SCOPE ALONE: the full size; the first chain; at OnBytes.secondHashFunction. No prover stands
in it.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.K8.Honest.SlotAtReach
import Johnson.Desc.K8.Honest.LeftAtReach
import Johnson.Desc.K8.Honest.KeepsFold
import Johnson.P1K8R.WideAtSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.OnPublicFiles (decide_left_some theStated_yes_digits)
open VerifiableInference.Desc.LinkJoin (quietAt_tl piece_digits)
open Johnson.Desc.First.Walk.Tied (Reach StepYes stepYes_decide)
open OnBytes.Road.K4 (reach_pred)

/-- What the seat of the lookup on the digits lays counts one drawing more. -/
theorem seatDigits_fold {Cl : Type} (claim : Aff → Cl) (s : S) (g : Forest.Heard) (G : Fork)
    (hf : ((K3.seatDigits claim).fork s).isSome = true) :
    (((K3.seatDigits claim).put s g G).tl?.map (·.foldDrawn)) =
      s.tl?.map (·.foldDrawn + 1) := by
  simp only [K3.seatDigits] at hf ⊢
  cases hh : s.here with
  | between => simp [S.fork?, hh] at hf
  | fin _ => simp [S.fork?, hh] at hf
  | mem _ => simp [S.fork?, hh] at hf
  | lay a => simp [S.tl?, S.fork?, S.putTl, S.putFork, hh]
  | att a => simp [S.tl?, S.fork?, S.putTl, S.putFork, hh]
  | head a =>
    cases ho : a.opened with
    | false => simp [S.fork?, hh, ho] at hf
    | true => simp [S.tl?, S.fork?, S.putTl, S.putFork, hh, ho]

/-- **Behind a yes of the seated lookup on the digits one drawing more is counted.** -/
theorem fold_behind_digits {Cl : Type} (claim : Aff → Cl) (readers : ℕ → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) (B : Block S Cl)
    (h : K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true) (i : ℕ)
    (hi : a.link = some i) (hpc : a.piece = K3.pieceAt X i true) (s c : S)
    (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) (hd : B.decide s rs gs = .ok c) :
    c.tl?.map (·.foldDrawn) = s.tl?.map (·.foldDrawn + 1) := by
  obtain ⟨P', sent, laid, n, gs', s', hP, hyes, hstep⟩ :=
    theStated_yes_digits claim readers X codes shape a B h hOk i hi hpc s c rs gs hd
  cases hsh : P'.shape with
  | none =>
    exfalso
    obtain ⟨_, x, _, _, hx, _⟩ := VerifiableInference.OnPublicFiles.decide_ok (K3.seatDigits claim)
      a.piece laid sent P' [] s s' _ gs' hyes
    unfold K3.hear at hx
    simp [hsh] at hx
  | some hh =>
    obtain ⟨F₁, y, hF₁, hn, e, hE⟩ := decide_left_some (K3.seatDigits claim) a.piece laid sent P' []
      (K3.seatDigits_reads claim) hh hsh Reading.gl 5 s s' _ gs' hyes
    have hsome : ((K3.seatDigits claim).fork s).isSome = true := by
      rw [hF₁]
      rfl
    have hb : s'.tl?.map (·.foldDrawn) = s.tl?.map (·.foldDrawn + 1) := by
      rw [e]
      exact seatDigits_fold claim _ _ _ hsome
    rcases hstep with rfl | ⟨f, hf, hfs⟩
    · exact hb
    · rw [quietAt_tl X i f hf s' c hfs]
      exact hb

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **IN FRONT OF THE HEAD's SEGMENT's BATCHING THE MATRIX IS COUNTED AS DRAWN ONCE.** -/
theorem fold_at_head_seg {Q : Type} {start : Q → S} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {z : Q} {s : S} (h : Reach 0 c.blocksInOrder start 347 (z, s)) :
    ∃ tl, s.tl? = some tl ∧ tl.foldDrawn = 1 := by
  have hp := blocks_planOk O hOk
  -- the merge, at 346
  have h7 : Reach 0 c.blocksInOrder start (346 + 1) (z, s) := h
  obtain ⟨z6, s6, t7, b6, e7, r6, hb6, hy6⟩ := reach_pred h7
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e7
  obtain ⟨bm, hbm, Lm⟩ := P1K8S.merge_leaves hS hR O
  have hbm' : c.blocksInOrder[346]? = some bm := hbm
  obtain rfl : bm = b6 := Option.some.inj (hbm'.symm.trans hb6)
  obtain ⟨rs6, gs6, hd6⟩ := stepYes_decide hy6
  have k6 : s.tl? = s6.tl? := Lm s6 rs6 gs6 s hd6
  -- the lookup on the digits, at 345
  have h6 : Reach 0 c.blocksInOrder start (345 + 1) (z, s6) := r6
  obtain ⟨z5, s5, t6, b5, e6, r5, hb5, hy5⟩ := reach_pred h6
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e6
  obtain ⟨Lk, b, b', e1, e2, e3, e4⟩ := IM.k3_of hS hR O 24 (by omega) true
  have hf : c.blocksInOrder[14 * 24 + IM.k3Ix 24 true + 2]? = some b := by
    rw [← IM.flatIx_scope hS hR O (by omega : 24 ≤ 24) (IM.k3Ix 24 true)]
    exact IM.hear_at_flat e1 e2
  have hf' : c.blocksInOrder[345]? = some b := hf
  obtain rfl : b = b5 := Option.some.inj (hf'.symm.trans hb5)
  obtain ⟨rs5, gs5, hd5⟩ := stepYes_decide hy5
  have hd5' := ((IM.yes_alone e4 (fun h => nomatch h) s5 _ rs5 gs5).1 hd5).1
  have hOk' : b'.planOk = true := by
    rw [← IM.alone_planOk e4]
    exact hp b (List.mem_of_getElem? hf)
  have h7p : 7 ≤ (IM.k3Place 24 true).piece := by
    show 7 ≤ (if true = true then 6 else 1) + (if 24 = 24 then 1 else 0) + 1
    simp
  have hpc := piece_digits _ _ _ _ _ _ b' e3 24 rfl h7p
  have k5 := fold_behind_digits _ _ _ _ _ _ b' e3 hOk' 24 rfl hpc s5 _ rs5 gs5 hd5'
  -- K1's sending of the digits, at 344
  have h5 : Reach 0 c.blocksInOrder start (344 + 1) (z, s5) := r5
  obtain ⟨z4, s4, t5, b4, e5, r4, hb4, hy4⟩ := reach_pred h5
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e5
  obtain ⟨bd, hbd, Ld⟩ := P1K8S.digits_leave hS hR O (l := 24) (by omega) .head
    (IM.subs_scope hS hR O 24 (by omega)) 6 rfl (Or.inr rfl)
  have hbd' : c.blocksInOrder[344]? = some bd := hbd
  obtain rfl : bd = b4 := Option.some.inj (hbd'.symm.trans hb4)
  obtain ⟨rs4, gs4, hd4⟩ := stepYes_decide hy4
  have k4 : s5.tl? = s4.tl? := Ld s4 rs4 gs4 s5 hd4
  -- the draw, at 343
  have h4 : Reach 0 c.blocksInOrder start (343 + 1) (z, s4) := r4
  obtain ⟨z3, s3, t4, b3, e4', r3, hb3, hy3⟩ := reach_pred h4
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e4'
  obtain ⟨Lk8, b8, Xl, f1, f2, f3, f4, -⟩ := IM.k8_of_head hS hR O
  obtain ⟨Lk8', b8', Xl', -, -, g3, -, -, hs8, -⟩ :=
    P1K8S.sitsAt_of_alone f1 f2 (IM.flatIx_scope hS hR O (by omega) 5) f3 f4
  have g3' : c.blocksInOrder[343]? = some b8' := g3
  obtain rfl : b8' = b3 := Option.some.inj (g3'.symm.trans hb3)
  obtain ⟨tl4, ht4, hz4⟩ := fold0_of_step hs8 hy3
  -- together
  rw [k4, ht4] at k5
  rw [← k6] at k5
  cases ht : s.tl? with
  | none =>
    rw [ht] at k5
    cases k5
  | some tl =>
    rw [ht] at k5
    refine ⟨tl, rfl, ?_⟩
    have e : tl.foldDrawn = tl4.foldDrawn + 1 := Option.some.inj k5
    rw [hz4] at e
    exact e

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.seatDigits_fold
#print axioms VerifiableInference.Desc.First.K8.Honest.fold_behind_digits
#print axioms VerifiableInference.Desc.First.K8.Honest.fold_at_head_seg
