-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/RowFormSeat.lean: AT EACH OF THE 25 LINKS OF THE PROOF FILE's FIRST CHAIN, IN
THE GOALS' SCOPE AND WHERE THE THREE PUBLIC FILES ARE READ: IF THE STEP "BEHIND THE BATCHING"
(`Link.runBehind`, Johnson/Desc/Block.lean) RETURNS A STATE sE FROM A STATE sB AT WHICH
`FrontOfTests` HOLDS (RowFormTested.lean), THEN sE HAS A LEDGER F₁, AND THE TEST ON VALUES `termsV`
(Johnson/Desc/First/Batch/Shape/DoorParts.lean) ACCEPTS AT THE COPY OF F₁ WHOSE FIELD doorShutF IS
SET TO true. One definition, two theorems; the proofs combine theorems of the library with
RowFormTested.lean; nothing is evaluated.

Purpose. RowFormTested.lean has this conclusion behind the run "K8.tests" alone. Inside the step
"behind the batching" two joins are owed: from the state before the step to the state before that
run, and from the state behind that run to the state behind the step. Here both are made.

How. The library has, at each of the 25 links in scope, the link's order behind the batching written
out: "K8.lsTail", then a stretch mid, then "K8.tests", last; the runs that the link's list holds
under the two names stand under those of K8.whole p; and each run of mid leaves the smallness test's
record and the list of tables (`K8At`, `k08_scope`, Johnson/TocK8R/AtSeat.lean). In
Johnson/Desc/First/TailClaims/ it says what the two runs do to the state (`sits_lsTail`,
`sits_tests`, K8Sits.lean), how the record, the ledger and the list of tables are read, also behind
a writing of the first two (`partOf_some`, K8SitsBetween.lean; `part_set`, K8SitsMeet.lean), and how
a row of runs is cut (`afterIn_cons`, `afterIn_keeps`, K8SitsLink.lean). mid is empty but at the
twelve layers' links, where it is the one run "free-slot", which leaves the ledger too
(`freeSlot_field`, K8SitsBetween.lean). "K8.lsTail" writes one field of the record, which
FrontOfTests does not read (`testsFront_lsTail`, RowFormTested.lean).

Main names.
* `LeavesLedger bs o`: the run at the entry o does not change the ledger.
* **`termsV_at_link`**: at a link Lk with K8At, where each run of mid leaves the ledger:
  Lk.runBehind sB = .ok sE and FrontOfTests sB give F₁ with sE.fork? = some F₁ and termsV L { F₁
  with doorShutF := true } = true at every L.
* **`termsV_scope`**: in scope (VerifierAndGoals.InScope P = true), where the files are read (VerifierAndGoals.readFiles
  P = .ok pp), at an opening O (`IM.Open`, Johnson/IMR/SeatOpen.lean): at each l < 25 the chain's
  link number l is such a link.

Limits. IMPLICATIONS, FROM A RETURN OF THE STEP. termsV IS EVALUATED AT A COPY OF THE LEDGER, with
doorShutF set to true: whether F₁ itself has that field set, and where such a copy is what a test
reads, is not said here. NOTHING HERE SHOWS FrontOfTests AT ANY STATE. It asks, of the state's
ledger and record, where the state has both (`TestsFront`, RowFormTested.lean): each tree of the
ledger that the record's index U names has R = 1 if it is of the kind table; the record is `Powered`
at the ledger's element theta; each row of the ledger is `RowClean`. No example in Lean shows that
the premises can hold together. termsV_scope is stated at the hash OnBytes.secondHashFunction alone, and at the
letters of an opening, not under the library's hypothesis P5J.AtMgA. That the block with this step
stands in the chain's flat list before the closing's blocks is `Link.blocksInOrder`'s text
(Johnson/Desc/Block.lean): not used here; nothing is said of a state that a run reaches. Of the
tests on values only termsV is treated. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.RowFormTested
import Johnson.TocK8R.AtSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open Inst.Model
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName Claim claimsInBy afterIn)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching orderOf orderAfterOf)
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open VerifiableInference.Desc.K9.Shape (termsV)
open ProofFile (Cl)
open IM
open TocK8 (K8At afterIn_of_behind k08_scope ixOf preOf postOf midOf)

/-! ## 1 At a link -/

/-- The run that the list bs holds at the entry o of an order behind the batching does not change
the ledger (S.fork?). The like of the library's AfterLeaves (Johnson/TocK8R/AtSeat.lean), which
speaks of the smallness test's record and the list of tables. -/
def LeavesLedger (bs : List (Block S Cl)) (o : ℕ × String) : Prop :=
  ∀ run, ((bs[o.1]?).bind fun b => b.after.lookup o.2) = some run →
    ∀ e e₁, run e = .ok e₁ → e₁.fork? = e.fork?

/-- **AT A LINK WITH THE LIBRARY's K8At**: if Lk.runBehind sB = .ok sE, FrontOfTests holds at sB,
and each run between "K8.lsTail" and "K8.tests" leaves the ledger, then sE has a ledger F₁, and
termsV accepts, at every L, at the copy of F₁ whose field doorShutF is set to true. -/
theorem termsV_at_link {Lk : Link S Cl} {p : VerifiableInference.Desc.First.K8.ParW} {i : ℕ}
    {pre post mid : List (ℕ × String)} (K : K8At Lk p i pre post mid)
    (hF : ∀ o ∈ mid, LeavesLedger Lk.hear o)
    (sB sE : S) (h2 : Lk.runBehind sB = .ok sE) (hf : FrontOfTests sB) :
    ∃ F₁, sE.fork? = some F₁ ∧ ∀ L, termsV L { F₁ with doorShutF := true } = true := by
  have ha := afterIn_of_behind h2
  rw [K.after] at ha
  obtain ⟨rL', s₁, hlL, hrL, ha'⟩ := afterIn_cons ha
  obtain ⟨s₂, -, hkeep, ha''⟩ :=
    afterIn_keeps (fun s : S => (k8Field s, s.fork?)) mid [(i, "K8.tests")] s₁ sE
      (fun o ho run hl e e₁ hr =>
        Prod.ext (K.hmid o ho run hl e e₁ hr) (hF o ho run hl e e₁ hr)) ha'
  obtain ⟨rT', s₃, hlT, hrT, hend⟩ := afterIn_cons ha''
  obtain rfl : s₃ = sE := Except.ok.inj hend
  obtain ⟨rL, mL, uL⟩ := K.hL rL' hlL
  obtain ⟨rT, mT, uT⟩ := K.hT rT' hlT
  obtain ⟨q, hq, rfl⟩ := (sits_lsTail p rL mL sB s₁).1 (uL _ _ hrL)
  obtain ⟨q₂, Fc, hq₂, ht, rfl⟩ := (sits_tests p rT mT s₂ _).1 (uT _ _ hrT)
  obtain ⟨b1, b2, -⟩ := partOf_some.1 hq
  obtain ⟨c1, c2, -⟩ := partOf_some.1 (part_set hq
    { q with tl := { q.tl with lsTail := q.F.LS.extract q.tl.slotA q.tl.slotB } })
  obtain ⟨d1, d2, -⟩ := partOf_some.1 hq₂
  obtain ⟨k1, k2⟩ := Prod.mk.inj hkeep
  have k3 := (Prod.mk.inj k1).1
  have e1 : q₂.tl = { q.tl with lsTail := q.F.LS.extract q.tl.slotA q.tl.slotB } :=
    Option.some.inj (d1.symm.trans (k3.trans c1))
  have e2 : q₂.F = q.F := Option.some.inj (d2.symm.trans (k2.trans c2))
  rw [e1, e2] at ht
  obtain ⟨-, g2, -⟩ := partOf_some.1 (part_set hq₂ { q₂ with F := Fc })
  exact ⟨Fc, g2, termsV_of_testsP ht (testsFront_lsTail (hf q.F q.tl b2 b1) _)⟩

/-! ## 2 All 25 links, in scope -/

/-- **IN THE GOALS' SCOPE, WHERE THE THREE PUBLIC FILES ARE READ, AT AN OPENING O AT THE HASH
OnBytes.secondHashFunction**: for each l < 25 the chain c
has a link number l, and termsV_at_link's conclusion holds at it: from Lk.runBehind sB = .ok sE and
FrontOfTests sB. -/
theorem termsV_scope {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ l < 25, ∃ Lk : Link S Cl, c.links[l]? = some Lk ∧
      ∀ sB sE : S, Lk.runBehind sB = .ok sE → FrontOfTests sB →
        ∃ F₁, sE.fork? = some F₁ ∧ ∀ L, termsV L { F₁ with doorShutF := true } = true := by
  intro l hl
  obtain ⟨Lk, Xl, e, -, K, -⟩ := k08_scope hS hR O l hl
  refine ⟨Lk, e, fun sB sE h2 hf => termsV_at_link K ?_ sB sE h2 hf⟩
  intro o ho run hlk e₀ e₁ hr
  by_cases h24 : l = 24
  · subst h24
    exact nomatch ho
  · by_cases he : l % 2 = 0
    · have ej : 2 * (l / 2) = l := by omega
      have hs : subAt l = .layers := by
        rw [← ej]
        exact subAt_layers (l / 2) (by omega)
      rw [hs] at ho
      obtain rfl := List.mem_singleton.1 ho
      obtain ⟨L4, b4, x, e4, hb4, -, la4, -⟩ := k4_of hS hR O (l / 2) (by omega)
      rw [ej] at e4
      obtain rfl : Lk = L4 := Option.some.inj (e.symm.trans e4)
      rw [show ((2, "free-slot") : ℕ × String).1 = 2 from rfl, hb4] at hlk
      obtain ⟨r', hl', -, hy⟩ := after_yes la4 hlk
      exact (freeSlot_field (p := { x.2 with k3Runs := true }) hl' ((hy e₀ e₁).1 hr).1).2
    · have ej : 2 * (l / 2) + 1 = l := by omega
      have hs : subAt l = .attention := by
        rw [← ej]
        exact subAt_attention (l / 2)
      rw [hs] at ho
      exact nomatch ho

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.termsV_at_link
#print axioms Johnson.AtFull.Shape.termsV_scope
