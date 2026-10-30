-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/GatherYes.lean: WHAT A KIND's RUN OF CLAIMS FINDS OF THE LEDGER WHEN IT IS CALLED
INSIDE THE BATCHING, WHAT K9's TEST BEHIND A RUN ASKS, AND WHEN THE GATHERER RETURNS. Statements and proofs ON THE
VERIFIER's TEXT; no prover is in this file, and no goal is stated.

  `ran_kept`        along the thread of the runs (`Ran`, Honest/K9/GatherFold.lean): if every named run keeps the
                    ledger's core (`RunKeeps`), each run ran at a state at which the core is the one with which the
                    gathering began
  `LedgerAtRun x a'`, `kept_finds`   **WHAT A RUN FINDS**, behind a yes of the draw at x and such runs: chi is x and is
                    marked as drawn · the plan's number of claims is not 0 · every coefficient on a slot is the word
                    0 · no claim is counted · no number is marked
  `window_zero`     so on every window of slots the coefficients are all 0, in the form in which the list
                    "K8.equations" asks it ("internal-f-tail-slot", TailClaims/Equations.lean)
  `each_owner`      **K9's TEST BEHIND A RUN** (`K9.eachAtS`): behind a run that is an owner of the smallness test's
                    window and is not the first of its stretch it asks NOTHING: it says yes whatever the list is
  `each_k8`         so behind "K8.equations", at all three sorts of segment
  `each_other`      behind a run that is no owner of the window: a yes is: no claim of the list names a slot of the
                    window
  `each_first`      behind the FIRST run of the window's stretch (the lookup on the digits' "objects"): a yes is: the
                    list has as many claims as that lookup has equations of its own. These three are all the cases at
                    a state that holds the smallness test's data (a run is no owner, the stretch's first, or
                    another of it: by hand; no theorem says so); `each_noTl`: where it holds none, nothing is asked
  `step_yes`, `gather_returns`   **THE GATHERER RETURNS** where a family I i n u ("in front of entry number i of the
                    order, with n claims made so far, the state u is as it should be") holds at (0, 0, its state)
                    and, at each entry i, from I i n u: the named run returns at n and u, K9's test behind it says
                    yes, and I (i + 1) (n + the list's length) holds behind. BY THE PLACE, because a real run cannot
                    run twice (it lays its hiding values, and a second value under a slot is refused); WITH THE
                    NUMBER, because a run may write the number into the state
  `runUnder_of_under`, `RunUnder.share`   FOR THE COUNT's PREMISES, which say "if the run returns": from the seal's
                    `LinkJoin.Under`, which a seated link's ties yield, to `RunUnder`; a kind's sentence on its own
                    run's list passes to the run in the description's list
  `guardedRun`, `guarded_claims`, `guardedRun_under`, `guardedRun_yes`   A BLOCK UNDER THE DRIVER's GUARD ON THE SEAT
                    (`Block.guarded`) states each of its runs WRAPPED (`guarded_claims`: by `rfl`). `gather_returns`
                    asks that the run IN THE LIST returns: so, where the list's blocks stand under that guard (by the
                    seal's `Link.guarded` the hearing blocks do; that the proof file's description lays it is read,
                    not shown), a kind that shows "my own run returns" ALSO OWES that the guard's test passes behind
                    it (`guardedRun_yes`)

WHAT IS NOT CLAIMED. That any kind's run keeps the core or returns, or that the guard's test passes behind it. Whether
other wraps than `Block.guarded` stand on the real list's runs. (That the description's own `Link.each` is `K9.eachAtS`
at the segment's sort: the sealed `IM.k9_of`; handed on as `SeatedFree.each`, Honest/K9/AtSeatAll.lean.) Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K9.GatherFold
import Johnson.Desc.First.Batch.EachAtS
import Johnson.Desc.First.Batch.Law.SumsMeans
import Johnson.Desc.First.Link.Law.Under
import Johnson.Desc.SeatGuard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Claim claimsInBy claimsInStep named)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (atS eachAtS cutAt SegSort)

/-- Along the thread every run ran at a state with the core with which the gathering began. -/
theorem ran_kept (bs : List (Block S Claim)) (order : List (Nat × String))
    (hk : ∀ o ∈ order, ∀ run, claimsRunOf bs o = some run → RunKeeps run) (n : Nat) (t : S)
    (ls : List (List Claim)) (e : S) (h : Ran bs order n t ls e) :
    List.Forall₂ (fun o l => ∃ run n u z, claimsRunOf bs o = some run ∧ Kept t u ∧ run n u = .ok z ∧ z.1 = l)
      order ls ∧ Kept t e :=
  ran_inv bs (fun u => Kept t u) order n t ls e
    (fun o ho run hr n u z hI hz => hI.trans (hk o ho run hr n u z hz)) (Kept.refl t) h

/-- **What a run finds of the ledger.** x: the drawn chi; a': K9's part of the state at which the run is called. -/
structure LedgerAtRun (x : E) (a' : VerifiableInference.Desc.K9.Part) : Prop where
  chi : a'.F.theta = x
  drawn : a'.F.thetaDrawnF = true
  planned : a'.F.planClaimsF ≠ 0
  empty : ∀ j, a'.F.LS.getD j zeroE = zeroE
  sized : a'.F.LS.size = a'.F.ns
  count : a'.F.nClaim = 0
  marks : a'.F.kapMapF = Array.replicate a'.F.planClaimsF false

/-- Behind a yes of the draw, at every state that has kept the core. -/
theorem kept_finds (a a₁ : VerifiableInference.Desc.K9.Part) (x : E) (hl : DrawLeaves a a₁ x) (t u : S)
    (ht : atS.get? t = some a₁) (hk : Kept t u) : ∃ a', atS.get? u = some a' ∧ LedgerAtRun x a' := by
  obtain ⟨a', ha', c⟩ := hk a₁ ht
  exact ⟨a', ha',
    { chi := by rw [c.theta, hl.chi]
      drawn := by rw [c.drawn, hl.drawn]
      planned := by rw [c.plan, hl.plan]; exact hl.planned
      empty := fun j => by rw [c.LS]; exact hl.empty j
      sized := by rw [c.LS, c.ns, hl.sized]
      count := by rw [c.count, hl.count]
      marks := by rw [c.marks, hl.marks, c.plan, hl.plan] }⟩

/-- On every window the coefficients are all 0. -/
theorem window_zero (LS : Array E) (h : ∀ j, LS.getD j zeroE = zeroE) (lo hi : Nat) :
    (LS.extract lo hi).all isZeroE = true := by
  rw [Array.all_eq_true]
  intro i hi'
  have hsz : lo + i < LS.size := by
    have := hi'
    simp only [Array.size_extract] at this
    omega
  have e : (LS.extract lo hi)[i] = LS[lo + i] := by simp
  have z := h (lo + i)
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hsz] at z
  rw [e]
  have z' : LS[lo + i] = zeroE := z
  rw [z']
  rfl

/-- **Behind an owner of the window that is not the first of its stretch K9's test asks nothing.** -/
theorem each_owner (k : SegSort) (run : Nat × String) (cls : List Claim) (s : S)
    (ho : run ∈ cutAt k 1) (hh : (cutAt k 1).head? ≠ some run) : eachAtS k run cls s = .ok () := by
  unfold eachAtS
  rw [VerifiableInference.Desc.K9L.eachRun_iff]
  constructor
  · rw [VerifiableInference.Desc.K9L.windowsOk_iff]
    intro w hw hn
    unfold VerifiableInference.Desc.K9.k8Window at hw
    cases htl : s.tl? with
    | none => rw [htl] at hw; exact nomatch hw
    | some tl =>
      rw [htl] at hw
      have e : w = ⟨cutAt k 1, tl.slotA, tl.slotB⟩ := by simpa using hw
      rw [e] at hn
      exact absurd ho hn
  · intro d hd
    unfold VerifiableInference.Desc.K9.dueAtS at hd
    have hf : ((cutAt k 1).head? == some run) = false := by simpa using hh
    rw [hf] at hd
    exact nomatch hd

/-- The entry of the order at which "K8.equations" stands, by the sort of segment. -/
def k8Entry : SegSort → Nat × String
  | .layers => (4, "K8.equations")
  | .attention => (4, "K8.equations")
  | .head => (5, "K8.equations")

/-- **Behind "K8.equations" K9's test asks nothing**, at all three sorts of segment. -/
theorem each_k8 (k : SegSort) (cls : List Claim) (s : S) : eachAtS k (k8Entry k) cls s = .ok () :=
  each_owner k (k8Entry k) cls s (by cases k <;> decide) (by cases k <;> decide)

/-- Behind a run that is no owner, and not that first one: no claim of the list names a slot of the window. -/
theorem each_other (k : SegSort) (run : Nat × String) (cls : List Claim) (s : S) (tl : HTailF2)
    (htl : s.tl? = some tl) (hn : run ∉ cutAt k 1) :
    eachAtS k run cls s = .ok () ↔
      ∀ cl ∈ cls, ∀ x ∈ cl.form.slots, ¬ (tl.slotA ≤ x.1 ∧ x.1 < tl.slotB) := by
  have hh : ((cutAt k 1).head? == some run) = false := by
    cases hc : cutAt k 1 with
    | nil => rfl
    | cons a l =>
      have : a ≠ run := fun e => hn (by rw [hc, e]; exact List.mem_cons_self)
      simpa using this
  unfold eachAtS
  rw [VerifiableInference.Desc.K9L.eachRun_iff, VerifiableInference.Desc.K9L.windowsOk_iff]
  unfold VerifiableInference.Desc.K9.k8Window VerifiableInference.Desc.K9.dueAtS
  rw [htl, hh]
  constructor
  · rintro ⟨h, _⟩
    exact h ⟨cutAt k 1, tl.slotA, tl.slotB⟩ (by simp) hn
  · intro h
    refine ⟨fun w hw _ => ?_, fun d hd => nomatch hd⟩
    have e : w = ⟨cutAt k 1, tl.slotA, tl.slotB⟩ := by simpa using hw
    rw [e]
    exact h

/-- **Behind the first run of the window's stretch** (the lookup on the digits' "objects"): K9's one due number: the
list has as many claims as that lookup has equations of its own. -/
theorem each_first (k : SegSort) (run : Nat × String) (cls : List Claim) (s : S) (tl : HTailF2)
    (htl : s.tl? = some tl) (hh : (cutAt k 1).head? = some run) :
    eachAtS k run cls s = .ok () ↔ cls.length = VerifiableInference.Desc.First.TailClaims.lookRows tl := by
  have ho : run ∈ cutAt k 1 := List.mem_of_mem_head? hh
  have hb : ((cutAt k 1).head? == some run) = true := by rw [hh]; simp
  unfold eachAtS
  rw [VerifiableInference.Desc.K9L.eachRun_iff, VerifiableInference.Desc.K9L.windowsOk_iff]
  unfold VerifiableInference.Desc.K9.k8Window VerifiableInference.Desc.K9.dueAtS
  rw [htl, hb]
  constructor
  · rintro ⟨_, h⟩
    exact h _ rfl
  · intro h
    refine ⟨fun w hw hn => ?_, fun d hd => ?_⟩
    · have e : w = ⟨cutAt k 1, tl.slotA, tl.slotB⟩ := by simpa using hw
      rw [e] at hn
      exact absurd ho hn
    · have e : d = ("K9.lookup-rows-counted", VerifiableInference.Desc.First.TailClaims.lookRows tl) :=
        (Option.some.inj hd).symm
      rw [e]
      exact h

/-- Where the state holds no data of the smallness test, K9's test behind a run asks nothing. -/
theorem each_noTl (k : SegSort) (run : Nat × String) (cls : List Claim) (s : S) (htl : s.tl? = none) :
    eachAtS k run cls s = .ok () := by
  unfold eachAtS
  rw [VerifiableInference.Desc.K9L.eachRun_iff, VerifiableInference.Desc.K9L.windowsOk_iff]
  unfold VerifiableInference.Desc.K9.k8Window VerifiableInference.Desc.K9.dueAtS
  rw [htl]
  refine ⟨fun w hw => (nomatch hw), fun d hd => ?_⟩
  by_cases hb : ((cutAt k 1).head? == some run) = true
  · rw [if_pos hb] at hd; exact nomatch hd
  · rw [if_neg hb] at hd; exact nomatch hd

/-- One step of the gatherer says yes. -/
theorem step_yes (each : Nat × String → List Claim → S → Except String Unit) (bs : List (Block S Claim))
    (x : List Claim × S) (o : Nat × String) (run : ClaimsRun) (z : List Claim × S)
    (hr : claimsRunOf bs o = some run) (hz : run x.1.length x.2 = .ok z) (he : each o z.1 z.2 = .ok ()) :
    claimsInStep each bs x o = .ok (x.1 ++ z.1, z.2) := by
  unfold claimsInStep
  have hn : named (o.2 ++ ": no such run") ((bs[o.1]?).bind fun b => b.claims.lookup o.2) = .ok run := by
    have : ((bs[o.1]?).bind fun b => b.claims.lookup o.2) = some run := hr
    rw [this]
    rfl
  rw [hn]
  simp only [Except.bind, hz, he]

/-- The fold returns, from any place, list and state. I i n u: "in front of entry number i of the order, with n claims
made so far, the state u is as it should be". -/
theorem fold_returns (each : Nat × String → List Claim → S → Except String Unit) (bs : List (Block S Claim))
    (I : Nat → Nat → S → Prop) : ∀ (order : List (Nat × String)) (i : Nat) (x : List Claim × S),
    I i x.1.length x.2 →
    (∀ j o, order[j]? = some o → ∀ n u, I (i + j) n u → ∃ run z, claimsRunOf bs o = some run ∧
      run n u = .ok z ∧ each o z.1 z.2 = .ok () ∧ I (i + j + 1) (n + z.1.length) z.2) →
    ∃ y, order.foldl (gatherStep each bs) (.ok x) = .ok y ∧ I (i + order.length) y.1.length y.2
  | [], i, x, hI, _ => ⟨x, rfl, hI⟩
  | o :: l, i, x, hI, h => by
    obtain ⟨run, z, hr, hz, he, hI'⟩ := h 0 o rfl x.1.length x.2 hI
    have hI2 : I (i + 1) (x.1 ++ z.1, z.2).1.length (x.1 ++ z.1, z.2).2 := by
      show I (i + 1) (x.1 ++ z.1).length z.2
      rw [List.length_append]
      exact hI'
    obtain ⟨y, hy, hIy⟩ := fold_returns each bs I l (i + 1) (x.1 ++ z.1, z.2) hI2 (by
      intro j o' hj n u hu
      have e1 : i + 1 + j = i + (j + 1) := by omega
      rw [e1] at hu
      have := h (j + 1) o' (by simpa using hj) n u hu
      rw [e1]
      exact this)
    refine ⟨y, ?_, ?_⟩
    · rw [List.foldl_cons]
      have hs : gatherStep each bs (.ok x) o = .ok (x.1 ++ z.1, z.2) := step_yes each bs x o run z hr hz he
      rw [hs]
      exact hy
    · have e2 : i + (o :: l).length = i + 1 + l.length := by rw [List.length_cons]; omega
      rw [e2]
      exact hIy

/-- **The gatherer returns.** -/
theorem gather_returns (each : Nat × String → List Claim → S → Except String Unit)
    (bs : List (Block S Claim)) (order : List (Nat × String)) (I : Nat → Nat → S → Prop) (t : S)
    (hI : I 0 0 t)
    (h : ∀ j o, order[j]? = some o → ∀ n u, I j n u → ∃ run z, claimsRunOf bs o = some run ∧
      run n u = .ok z ∧ each o z.1 z.2 = .ok () ∧ I (j + 1) (n + z.1.length) z.2) :
    ∃ y, claimsInBy each bs order t = .ok y ∧ I order.length y.1.length y.2 := by
  obtain ⟨y, hy, hIy⟩ := fold_returns each bs I order 0 ([], t) hI (by
    intro j o hj n u hu
    rw [Nat.zero_add] at hu ⊢
    exact h j o hj n u hu)
  rw [Nat.zero_add] at hIy
  exact ⟨y, hy, hIy⟩

/-- The seal's "every yes of run is a yes of r, with the same return" (`LinkJoin.Under`), which the ties of a seated
link yield, is `RunUnder`. -/
theorem runUnder_of_under {run' run : ClaimsRun} (h : VerifiableInference.Desc.LinkJoin.Under run' run) :
    RunUnder run' run := fun n t z hz => h n t z.1 z.2 hz

/-- A run as the driver's guard on the seat wraps it (`Block.guarded`, Johnson/Desc/SeatGuard.lean: its text for a
block's runs of claims). -/
def guardedRun (same : S → S → Bool) (run : ClaimsRun) : ClaimsRun :=
  fun n t => (run n t).bind fun y => (VerifiableInference.Desc.seatSame same t y.2).map fun _ => y

/-- The runs of a block under the guard are the block's own runs, each wrapped so. -/
theorem guarded_claims (same : S → S → Bool) (but : VerifiableInference.Desc.Place → Bool) (b : Block S Claim) :
    (b.guarded same but).claims = b.claims.map fun c => (c.1, guardedRun same c.2) := rfl

/-- The wrapped run only refuses more. -/
theorem guardedRun_under (same : S → S → Bool) (run : ClaimsRun) : RunUnder (guardedRun same run) run := by
  intro n t z h
  unfold guardedRun at h
  obtain ⟨y, hy, h⟩ := bind_ok h
  cases hs : VerifiableInference.Desc.seatSame same t y.2 with
  | error m => rw [hs] at h; exact nomatch h
  | ok s' =>
    rw [hs] at h
    have e : y = z := Except.ok.inj h
    rw [← e]
    exact hy

/-- **THE OTHER WAY, WHICH `gather_returns` WANTS OF THE RUN IN THE LIST**: the wrapped run returns where the kind's own
run returns AND the guard's test passes: the seat is behind the run as it was in front. -/
theorem guardedRun_yes (same : S → S → Bool) (run : ClaimsRun) (n : Nat) (t : S) (z : List Claim × S)
    (h : run n t = .ok z) (hs : same t z.2 = true) : guardedRun same run n t = .ok z := by
  unfold guardedRun VerifiableInference.Desc.seatSame
  rw [h]
  show (Except.map (fun _ => z) (if same t z.2 = true then Except.ok z.2 else _)) = _
  rw [if_pos hs]
  rfl

/-- A kind's sentence on what its OWN run lays passes to a run that only refuses more: so to the run that stands in
the description's list. In this form stand the three shares of `slotsLive_of_inv`. -/
theorem RunUnder.share {run' run : ClaimsRun} (hu : RunUnder run' run) (I : S → Prop) (P : List Claim → Prop)
    (h : ∀ m u z, I u → run m u = .ok z → P z.1) : ∀ m u z, I u → run' m u = .ok z → P z.1 :=
  fun m u z hI hz => h m u z hI (hu m u z hz)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.ran_kept
#print axioms ProofFile.Honest.K9.kept_finds
#print axioms ProofFile.Honest.K9.window_zero
#print axioms ProofFile.Honest.K9.each_owner
#print axioms ProofFile.Honest.K9.each_k8
#print axioms ProofFile.Honest.K9.each_other
#print axioms ProofFile.Honest.K9.each_first
#print axioms ProofFile.Honest.K9.each_noTl
#print axioms ProofFile.Honest.K9.runUnder_of_under
#print axioms ProofFile.Honest.K9.RunUnder.share
#print axioms ProofFile.Honest.K9.guarded_claims
#print axioms ProofFile.Honest.K9.guardedRun_under
#print axioms ProofFile.Honest.K9.guardedRun_yes
#print axioms ProofFile.Honest.K9.step_yes
#print axioms ProofFile.Honest.K9.gather_returns
#print axioms ProofFile.Honest.K9.LedgerAtRun
#print axioms ProofFile.Honest.K9.k8Entry
#print axioms ProofFile.Honest.K9.fold_returns
#print axioms ProofFile.Honest.K9.guardedRun
