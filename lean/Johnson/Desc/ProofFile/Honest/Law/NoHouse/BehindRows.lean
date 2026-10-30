-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/BehindRows.lean: lemmas that prove `behindLeaves`
(Honest/Law/NoHouse/BehindKeeps.lean), the fourth conjunct of `keepsBehind`, for the step after a
segment's batching (`Link.runBehind`, Johnson/Desc/Block.lean). That step first runs the link's
tests, which return no state, and then the runs that the link's second order names. The library's
order names three: "K8.lsTail", in a layers' segment "free-slot", and "K8.tests". The first writes
one field of the range proof's state. The second puts the ledger back unchanged. The third writes
virtual rows of the ledger's arrays. None of them writes the link's context.

The library has lemmas on these runs for every relation that is reflexive and that all eight known
runs keep (`RunRests`, Johnson/Desc/First/Link/Law/RunRel.lean; `after_rests_layers` and its two
neighbours, AfterRests.lean). `behindLeaves` is not such a relation, since the five runs that add
claims do change the ledger. So the lemmas of section 3 repeat the library's three with hypotheses
on the other three runs alone.

  1  `putTl_reads`, `putFork_reads`   what the three readers return after a write
  2  `rows_onRow`, `rows_coef`, `rows_lsTail`, `rows_tests`, `rows_free`   the three runs
  3  `rows_layers`, `rows_attention`, `rows_head`   every run of a link's second order
  4  `rows_runBehind`   the step
  5  `rows_share_head`   every link of the library's description of the whole protocol, where the
     link stands at its sort (`hseg`)

Limits.
  * Section 3 takes as hypotheses that a link's own runs return only what the three model runs
    return (`UnderAfter`). Section 4 takes section 3's conclusion (`AL`). Section 5 takes section
    3's hypotheses from the library's lemmas `ties_layers_mg`, `ties_att_mg` and `ties_head_mg`
    (Johnson/LPFK9R/SortTiesAtMg.lean).
  * Nothing is said on whether the step accepts.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.BehindKeeps
import Johnson.Desc.First.Link.Law.AfterRests
import Johnson.LPFK9R.SortTiesAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open OnBytes.Model (Fork HTree HRow HTailF2)
open VerifiableInference.Desc (Chain Link Claim)
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.First.TailClaims (coefBody)
open VerifiableInference.Desc.First.TailClaims.Law (coefBody_inv)
open VerifiableInference.Desc.K9L (k8LsTail k8Tests k8LsTail_ok k8Tests_ok)
open VerifiableInference.Desc.K4Run (k4_freeSlot_wrote)
open OnBytes.Desc.First.K4 (blockAtC Wrote)
open VerifiableInference.Desc.LinkJoin (AtAfter SegAt UnderAfter order_at after_layers
  after_attention after_head relAfter_under holds_runBehind)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-! ## 1 What the three readers return after a write -/

/-- After the range proof's state is written, where there is one. -/
theorem putTl_reads (e : S) (tl tl' : HTailF2) (ht : e.tl? = some tl) :
    (e.putTl tl').link? = e.link? ∧ (e.putTl tl').tl? = some tl' ∧
      (e.putTl tl').fork? = e.fork? := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := e
  cases here with
  | lay x => exact ⟨rfl, rfl, rfl⟩
  | att x => exact ⟨rfl, rfl, rfl⟩
  | head x =>
    by_cases ho : x.opened = true
    · simp [S.putTl, S.link?, S.tl?, S.fork?, ho]
    · simp [S.tl?, ho] at ht
  | between => simp [S.tl?] at ht
  | fin x => simp [S.tl?] at ht
  | mem x => simp [S.tl?] at ht

/-- After the ledger is written, where there is one. -/
theorem putFork_reads (e : S) (F G : Fork) (hf : e.fork? = some F) :
    (e.putFork G).link? = e.link? ∧ (e.putFork G).tl? = e.tl? ∧
      (e.putFork G).fork? = some G := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := e
  cases here with
  | lay x => exact ⟨rfl, rfl, rfl⟩
  | att x => exact ⟨rfl, rfl, rfl⟩
  | head x =>
    by_cases ho : x.opened = true
    · simp [S.putFork, S.link?, S.tl?, S.fork?, ho]
    · simp [S.fork?, ho] at hf
  | between => simp [S.fork?] at hf
  | fin x => simp [S.fork?] at hf
  | mem x => simp [S.fork?] at hf

/-! ## 2 The three runs -/

/-- A change of one virtual row. -/
theorem rows_onRow (F r : Fork) (t' r' : Nat) (f : HRow → HRow) (h : rowsAlone F r) :
    rowsAlone F (HTailF2.onRow r t' r' f) := by
  obtain ⟨ts, rfl, e⟩ := h
  refine ⟨ts.modify t' fun X => { X with rows := X.rows.modify r' f }, rfl, ?_⟩
  rw [← e]
  exact OnBytes.Model.map_modify_same (fun X : HTree => { X with rows := #[] })
    (fun X => { X with rows := X.rows.modify r' f }) (fun _ => rfl) ts t'

/-- Setting the weights changes virtual rows alone. -/
theorem rows_coef (tl : HTailF2) (g : OnBytes.Model.Forest.Heard) (F : Fork) :
    rowsAlone F (coefBody tl g F) :=
  coefBody_inv (rowsAlone F) (fun r t' r' f h => rows_onRow F r t' r' f h) tl g F
    (rowsAlone_refl F)

/-- The run "K8.lsTail". -/
theorem rows_lsTail (e e₁ : S) (h : k8LsTail e = .ok e₁) : behindLeaves e e₁ := by
  obtain ⟨F, tl, hF, ht, rfl⟩ := k8LsTail_ok e e₁ h
  obtain ⟨a1, a2, a3⟩ := putTl_reads e tl { tl with lsTail := F.LS.extract tl.slotA tl.slotB } ht
  refine ⟨a1, fun tl0 h0 => ?_, fun F0 h0 => ⟨F0, a3.trans h0, rowsAlone_refl F0⟩⟩
  obtain rfl := Option.some.inj (ht.symm.trans h0)
  exact ⟨_, a2⟩

/-- The run "K8.tests". -/
theorem rows_tests (nU : Array Nat) (e e₁ : S) (h : k8Tests nU e = .ok e₁) :
    behindLeaves e e₁ := by
  obtain ⟨F, tl, g, hF, ht, -, -, -, rfl⟩ := k8Tests_ok nU e e₁ h
  obtain ⟨a1, a2, a3⟩ := putTl_reads e tl tl ht
  obtain ⟨b1, b2, b3⟩ := putFork_reads (e.putTl tl) F (coefBody tl g F) (a3.trans hF)
  refine ⟨b1.trans a1, fun tl0 h0 => ?_, fun F0 h0 => ?_⟩
  · obtain rfl := Option.some.inj (ht.symm.trans h0)
    exact ⟨tl.lsTail, b2.trans a2⟩
  · obtain rfl := Option.some.inj (hF.symm.trans h0)
    exact ⟨_, b3, rows_coef tl g F⟩

/-- The run "free-slot" of a layers' segment. -/
theorem rows_free (e e₁ : S) (a : LayOwn) (h : Wrote e a a.F e₁) : behindLeaves e e₁ := by
  obtain ⟨h1, rfl⟩ := h
  refine ⟨?_, fun tl0 h0 => ⟨tl0.lsTail, ?_⟩, fun F0 h0 => ⟨F0, ?_, rowsAlone_refl F0⟩⟩
  · simp [S.link?, h1]
  · simpa [S.tl?, h1] using h0
  · simpa [S.fork?, h1] using h0

/-! ## 3 Every run of a link's second order -/

theorem rows_layers {l : Nat} {L : Link S Claim} (hL : SegAt l .layers L)
    {p : OnBytes.Desc.First.K4.Par} {nU : Array Nat}
    (tLs : ∀ run, AtAfter L (4, "K8.lsTail") run → UnderAfter run k8LsTail)
    (tFree : ∀ run, AtAfter L (2, "free-slot") run →
      ∃ r, (blockAtC p).after.lookup "free-slot" = some r ∧ UnderAfter run r)
    (tTests : ∀ run, AtAfter L (4, "K8.tests") run → UnderAfter run (k8Tests nU)) :
    ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ → behindLeaves e e₁ := by
  rw [(order_at hL).2, after_layers]
  refine ⟨fun run h => relAfter_under (tLs run h) rows_lsTail, fun run h e e₁ hr => ?_,
    fun run h => relAfter_under (tTests run h) (rows_tests nU)⟩
  obtain ⟨r, h0, hu⟩ := tFree run h
  obtain ⟨a, hw⟩ := k4_freeSlot_wrote h0 (hu e e₁ hr)
  exact rows_free e e₁ a hw

theorem rows_attention {l : Nat} {L : Link S Claim} (hL : SegAt l .attention L)
    {nU : Array Nat} (tLs : ∀ run, AtAfter L (4, "K8.lsTail") run → UnderAfter run k8LsTail)
    (tTests : ∀ run, AtAfter L (4, "K8.tests") run → UnderAfter run (k8Tests nU)) :
    ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ → behindLeaves e e₁ := by
  rw [(order_at hL).2, after_attention]
  exact ⟨fun run h => relAfter_under (tLs run h) rows_lsTail,
    fun run h => relAfter_under (tTests run h) (rows_tests nU)⟩

theorem rows_head {l : Nat} {L : Link S Claim} (hL : SegAt l .head L) {nU : Array Nat}
    (tLs : ∀ run, AtAfter L (5, "K8.lsTail") run → UnderAfter run k8LsTail)
    (tTests : ∀ run, AtAfter L (5, "K8.tests") run → UnderAfter run (k8Tests nU)) :
    ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ → behindLeaves e e₁ := by
  rw [(order_at hL).2, after_head]
  exact ⟨fun run h => relAfter_under (tLs run h) rows_lsTail,
    fun run h => relAfter_under (tTests run h) (rows_tests nU)⟩

/-! ## 4 The step -/

/-- If every run of the link's second order satisfies `behindLeaves`, so does the step. -/
theorem rows_runBehind (Lk : Link S Claim)
    (AL : ∀ o ∈ Lk.orderAfter, ∀ run, AtAfter Lk o run → ∀ e e₁, run e = .ok e₁ →
      behindLeaves e e₁) (s s' : S) (h : Lk.runBehind s = .ok s') : behindLeaves s s' :=
  holds_runBehind (fun e => behindLeaves s e) Lk
    (fun o ho run hl e e₁ hr hx => behindLeaves_trans hx (AL o ho run hl e e₁ hr)) s s' h
    (behindLeaves_refl s)

/-! ## 5 Every link of the library's description -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem rows_share_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : Nat} (hm : m < 25)
    {Lk : Link S Claim} (hlk : h.𝔇.lk m = some Lk) (hseg : SegAt m (IM.subAt m) Lk) :
    ∀ o ∈ Lk.orderAfter, ∀ run, AtAfter Lk o run → ∀ e e₁, run e = .ok e₁ →
      behindLeaves e e₁ := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  cases hs : IM.subAt m with
  | layers =>
    obtain ⟨p4, X, -, -, T⟩ := LPFK9.ties_layers_mg h O m hm hs Lk hlk
    rw [hs] at hseg
    exact rows_layers hseg T.tLs T.tFree T.tTests
  | attention =>
    obtain ⟨Xl, A, X, -, -, -, -, T⟩ := LPFK9.ties_att_mg h O m hm hs Lk hlk
    rw [hs] at hseg
    exact rows_attention hseg T.tLs T.tTests
  | head =>
    obtain ⟨iU3, X, -, -, T⟩ := LPFK9.ties_head_mg h O m hm hs Lk hlk
    rw [hs] at hseg
    exact rows_head hseg T.tLs T.tTests

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.putTl_reads
#print axioms ProofFile.Honest.FirstThread.putFork_reads
#print axioms ProofFile.Honest.FirstThread.rows_onRow
#print axioms ProofFile.Honest.FirstThread.rows_coef
#print axioms ProofFile.Honest.FirstThread.rows_lsTail
#print axioms ProofFile.Honest.FirstThread.rows_tests
#print axioms ProofFile.Honest.FirstThread.rows_free
#print axioms ProofFile.Honest.FirstThread.rows_layers
#print axioms ProofFile.Honest.FirstThread.rows_attention
#print axioms ProofFile.Honest.FirstThread.rows_head
#print axioms ProofFile.Honest.FirstThread.rows_runBehind
#print axioms ProofFile.Honest.FirstThread.rows_share_head
