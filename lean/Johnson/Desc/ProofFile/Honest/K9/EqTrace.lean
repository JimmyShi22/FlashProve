-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/EqTrace.lean: WHAT A STATE THAT IS REACHED IN FRONT OF THE SUB-PROTOCOL "THE ONE
EQUATION" HOLDS, BY THE YESES OF THE TWO SUB-PROTOCOLS IN FRONT OF IT: the batching, and the step "behind the batching".
At each of the 25 segments of the first chain, under the library's hypothesis `AtMgA`; whoever plays.

"Reached" (`Reach`) is: handed on from a first state by accepting steps of the chain's own sub-protocols; which first
states are allowed is a variable here (`start`). Two steps
back stands a state s₂ in front of the batching. The batching's yes says: the draw's tests accepted at the part a that is
read at s₂; the runs of claims ran; their claims were added, which left a ledger G. The next step's yes says: the
segment's tests behind the adding accepted, and the weights of the virtual rows were laid.

  `normOwed`, `owedOf_eq`, `part_all`, `used_of_part`, `set_link`   small lemmas on the reading of a part of the state
  `counted_of_counts`     the segment's counts hold: so as many claims were added as the public parameters count
  `BehindBoth p n s a x G tl g`   THE FACTS, as one structure:
      ready: the draw's tests accepted at a · link: the book-keeping at s is a's with the slots in use told and the mark
      "the draw has run" · fork, tail: the ledger at s is G with the rows' weights laid; the smallness test's record
      is tl · used: the slots in use are told at s · owed: the count of rows owed is the batching's entry's · ns, plan:
      G has a's numbers of slots and of planned claims · count: G has counted n claims · coefs, marks: G has a
      coefficient for each slot and a mark for each planned claim · marked: each counted claim bears its mark · frame:
      but for the values of the weights on columns, G's arrays are a's with the draw's filling (`t2FillL`)
  **`eq_trace`**          l < 25, s reached at 14 l + `IM.nAt l` + 4: there are the seated segment's letters Lk, p, w and a,
      x, G, tl, g with `BehindBoth p w.2.1 s a x G tl g`, and a state s₂ reached at 14 l + `IM.nAt l` + 2 at which a is read

Limits. Of a reached state: that anything is reached is not proved here. The full size and the hash function `secondHashFunction` alone:
the hypothesis's. This file proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.EqBehind
import Johnson.Desc.ProofFile.Honest.K9.EqAdd
import Johnson.Desc.ProofFile.Honest.K9.BatAtHead
import Johnson.Desc.ProofFile.Honest.K9.AtHead
import Johnson.Desc.ProofFile.Honest.K9.FromYes
import Johnson.Desc.First.Link.Law.UsedStays
import Johnson.Desc.First.Batch.Shape.DoorAtS
import Johnson.Road.K4.FunsThirdReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims (coefBody)
open VerifiableInference.Desc.LinkJoin (FieldRests usedSome rests_usedSome usedSome_set rests_owed)
open VerifiableInference.Desc.K9.Shape (part_reads)
open Johnson.Desc.First.Walk.Tied (Reach StepYes stepYes_decide)
open OnBytes.Road.K4 (reach_pred)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-- A count of no rows is no count. -/
def normOwed : Option ℕ → Option ℕ
  | some 0 => none
  | x => x

theorem owedOf_eq (s : S) : Desc.K9.owedOf s = normOwed s.rowsOwed := by
  unfold Desc.K9.owedOf normOwed
  rcases s.rowsOwed with _ | _ | _ <;> rfl

theorem normOwed_twice (o : Option ℕ) : normOwed (normOwed o) = normOwed o := by
  rcases o with _ | _ | _ <;> rfl

/-- A part that is read, written out. -/
theorem part_all {s : S} {P : Desc.K9.Part} (h : Desc.K9.atS.get? s = some P) :
    ∃ tl u, s.link? = some P.L ∧ s.fork? = some P.F ∧ s.tl? = some tl ∧ Desc.K9.usedOf s = some u ∧
      P.owed = Desc.K9.owedOf s ∧ P.used = u ∧ P.laid = Desc.K9.laidOf tl ∧
      P.d = { st := s.st, book := s.book, roots := s.roots, opened := [], loc := () } := by
  have h' : (do
    let L ← s.link?
    let F ← s.fork?
    let tl ← s.tl?
    let used ← Desc.K9.usedOf s
    pure ({ owed := Desc.K9.owedOf s, used := used, laid := Desc.K9.laidOf tl, L := L, F := F,
            d := { st := s.st, book := s.book, roots := s.roots, opened := [], loc := () } } :
      Desc.K9.Part) : Option Desc.K9.Part) = some P := h
  cases hL : s.link? with
  | none => rw [hL] at h'; exact nomatch h'
  | some L =>
    cases hF : s.fork? with
    | none => rw [hL, hF] at h'; exact nomatch h'
    | some F =>
      cases ht : s.tl? with
      | none => rw [hL, hF, ht] at h'; exact nomatch h'
      | some tl =>
        cases hu : Desc.K9.usedOf s with
        | none => rw [hL, hF, ht, hu] at h'; exact nomatch h'
        | some u =>
          rw [hL, hF, ht, hu] at h'
          obtain rfl := Option.some.inj h'
          exact ⟨tl, u, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- And the other way. -/
theorem part_of_all {s : S} {L : LinkCtx} {F : Fork} {tl : HTailF2} (hL : s.link? = some L) (hF : s.fork? = some F)
    (ht : s.tl? = some tl) (hu : usedSome s = true) :
    ∃ u, Desc.K9.atS.get? s = some
      ({ owed := Desc.K9.owedOf s, used := u, laid := Desc.K9.laidOf tl, L := L, F := F,
         d := { st := s.st, book := s.book, roots := s.roots, opened := [], loc := () } } : Desc.K9.Part) := by
  obtain ⟨u, hu'⟩ := Option.isSome_iff_exists.1 hu
  refine ⟨u, ?_⟩
  show (do
    let L ← s.link?
    let F ← s.fork?
    let tl ← s.tl?
    let used ← Desc.K9.usedOf s
    pure ({ owed := Desc.K9.owedOf s, used := used, laid := Desc.K9.laidOf tl, L := L, F := F,
            d := { st := s.st, book := s.book, roots := s.roots, opened := [], loc := () } } :
      Desc.K9.Part) : Option Desc.K9.Part) = _
  rw [hL, hF, ht, hu']
  rfl

theorem used_of_part {s : S} {P : Desc.K9.Part} (h : Desc.K9.atS.get? s = some P) : usedSome s = true := by
  obtain ⟨_, u, -, -, -, hu, -⟩ := part_all h
  unfold usedSome
  rw [hu]
  rfl

/-- Behind the laying of a part the book-keeping is the one that was laid. -/
theorem set_link (s : S) (a q : Desc.K9.Part) (ha : Desc.K9.atS.get? s = some a) :
    (Desc.K9.atS.set s q).link? = some q.L := by
  obtain ⟨a₁, h1, -, h3⟩ := get_set s a q ha
  rw [(part_reads h1).1, h3]

/-- The segment's counts hold: so as many claims were added as the public parameters count. -/
theorem counted_of_counts (k : Desc.K9.SegSort) (n : ℕ) (s : S)
    (h : Desc.K9.countsHold (Desc.K9.countsAt k n) s = .ok ()) : Desc.K9.claimsCounted n s = true := by
  unfold Desc.K9.countsHold at h
  cases k <;>
    · unfold Desc.K9.countsAt at h
      simp only [List.forM_cons] at h
      obtain ⟨_, h1, -⟩ := (Desc.K9.Shape.ans_bind _ _ _).1 h
      exact (Desc.K9.Shape.need_ok _ _ _).1 h1

/-- **The facts.** n: the number of claims that the public parameters count. a: the part that is read in front of the
batching. x: the element drawn. G: the ledger behind the adding. -/
structure BehindBoth (p : Desc.K9.Where) (n : ℕ) (s : S) (a : Desc.K9.Part) (x : E) (G : Fork) (tl : HTailF2)
    (g : Forest.Heard) : Prop where
  ready : drawReady a = true
  link : s.link? = some (drawnPart p a x).L
  fork : s.fork? = some (coefBody tl g G)
  tail : s.tl? = some tl
  used : usedSome s = true
  owed : Desc.K9.owedOf s = normOwed (some p.rows)
  ns : G.ns = a.F.ns
  plan : G.planClaimsF = a.F.planClaimsF
  count : G.nClaim = n
  coefs : G.LS.size = a.F.ns
  marks : G.kapMapF.size = a.F.planClaimsF
  marked : Marked G
  frame : treesFrame G.trees = treesFrame (t2FillL a.F a.L.list).trees

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Two steps back from a state that is reached in front of "the one equation".** -/
theorem eq_trace (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) (hl : l < 25) {Q : Type} {start : Q → TS}
    {pub : Q} {s : TS} (hr : Reach 0 cF.blocksInOrder start (14 * l + IM.nAt l + 4) (pub, s)) :
    ∃ Lk p w s₂ a χ G tl g, SeatedFree cF Zp l (IM.nAt l) Lk p w ∧
      Reach 0 cF.blocksInOrder start (14 * l + IM.nAt l + 2) (pub, s₂) ∧ Desc.K9.atS.get? s₂ = some a ∧
      BehindBoth p w.2.1 s a χ G tl g := by
  obtain ⟨Lk, p, w, Sd₀⟩ := seated_at_head h l hl
  have Sd : SeatedFree cF Zp l (IM.nAt l) Lk p w := Sd₀
  obtain ⟨z1, s₁, s', b1, e1, hr1, hb1, hy1⟩ := reach_pred (k := 14 * l + IM.nAt l + 3) hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e1
  obtain ⟨z2, s₂, s'', b2, e2, hr2, hb2, hy2⟩ := reach_pred (k := 14 * l + IM.nAt l + 2) hr1
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e2
  obtain ⟨bb, hbb, -, hdec⟩ := Sd.behind
  obtain rfl : bb = b1 := Option.some.inj (hbb.symm.trans hb1)
  obtain rfl : Lk.batch (claimsInBy Lk.each Lk.hear Lk.order) = b2 := Option.some.inj (Sd.batching.symm.trans hb2)
  obtain ⟨rs1, gs1, hd1⟩ := stepYes_decide hy1
  rw [hdec] at hd1
  obtain ⟨R, c, -, hstep⟩ := hy2
  obtain ⟨r0, tr, -, -, -, y, G, hB, -, -⟩ := behind_of_step Sd 0 s₂ s₁ R c c.length hstep
  obtain ⟨t₁, hdraw, hg, he⟩ := gathered_split p _ s₂ _ y hB.gathered
  obtain ⟨a, ha, hready⟩ := (draw_iff p s₂ _).1 ⟨t₁, hdraw⟩
  have et := draw_is p s₂ t₁ _ a ha hdraw
  obtain ⟨a₁, h1, hl1⟩ := draw_facts p s₂ t₁ _ a ha hdraw
  obtain ⟨a', ha', hcore⟩ := Sd.keeps t₁ y.1 y.2.2 a₁ hg h1
  obtain rfl : a' = y.2.1 := Option.some.inj (ha'.symm.trans he)
  -- every reading that rests is kept by the runs of claims
  have gk : ∀ {γ : Type} (f : S → γ), FieldRests f → f y.1 = f t₁ := by
    intro γ f Rf
    obtain ⟨ls, -, hran⟩ := gather_ran Lk.each Lk.hear Lk.order t₁ (y.2.2, y.1) hg
    refine (ran_inv Lk.hear (fun u => f u = f t₁) Lk.order 0 t₁ ls y.1
      (fun o ho run hrun n t z hI hz => ?_) rfl hran).2
    obtain ⟨j, hj⟩ := List.getElem?_of_mem ho
    exact (rests_at_head h hl Sd f Rf j o run hj hrun n t z hz).trans hI
  -- and by the step behind the batching
  have bk : ∀ {γ : Type} (f : S → γ), FieldRests f → f s = f s₁ := fun f Rf =>
    (behind_at_head h l hl Lk Sd.link f Rf s₁ s hd1).1
  obtain ⟨-, F1, tl1, g, hF1, -, -, htlE, hFE⟩ := behind_at_head h l hl Lk Sd.link S.link? rests_link s₁ s hd1
  obtain rfl : F1 = G := Option.some.inj (hF1.symm.trans hB.ledger)
  obtain ⟨aL, aM⟩ := addList_leaves _ _ _ hB.added
  -- the tests behind the adding
  have htests : Lk.tests s₁ = .ok () := by
    unfold Link.runBehind at hd1
    split at hd1
    · rename_i u hu
      exact hu
    · exact nomatch hd1
  have hcount := counted_of_counts _ _ _ ((Sd.tests s₁).1 htests).2.2
  refine ⟨Lk, p, w, s₂, a, E.ofTriple tr, F1, _, g, Sd, hr2, ha,
    { ready := hready, link := ?_, fork := hFE, tail := htlE, used := ?_, owed := ?_, ns := ?_, plan := ?_,
      count := ?_, coefs := ?_, marks := ?_, marked := ?_, frame := ?_ }⟩
  · rw [bk S.link? rests_link, hB.state, set_link y.1 y.2.1 _ he]
    have e3 : y.1.link? = some y.2.1.L := (part_reads he).1
    have e4 : y.1.link? = t₁.link? := gk S.link? rests_link
    rw [et, set_link s₂ a _ ha] at e4
    exact e3.symm.trans e4
  · rw [bk usedSome rests_usedSome, hB.state, usedSome_set]
    exact used_of_part he
  · obtain ⟨_, _, -, -, -, -, ho, -⟩ := part_all he
    have o2 : Desc.K9.owedOf s₁ = normOwed y.2.1.owed := by rw [hB.state, owedOf_eq]; rfl
    have o5 : Desc.K9.owedOf t₁ = normOwed (some p.rows) := by rw [et, owedOf_eq]; rfl
    rw [bk Desc.K9.owedOf rests_owed, o2, ho, gk Desc.K9.owedOf rests_owed, o5, normOwed_twice]
  · rw [aL.ns, hcore.ns, hl1.ns]
  · rw [hB.all.plan, hcore.plan, hl1.plan]
  · unfold Desc.K9.claimsCounted at hcount
    rw [hB.ledger] at hcount
    exact beq_iff_eq.1 hcount
  · rw [aL.coefs, hcore.LS, hl1.sized, hl1.ns]
  · rw [aL.marks, hcore.marks, hl1.marks, Array.size_replicate]
  · refine aM fun i hi => ?_
    rw [hcore.count, hl1.count] at hi
    exact absurd hi (Nat.not_lt_zero i)
  · rw [hB.all.frame, hcore.frame, hl1.trees]

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.owedOf_eq
#print axioms ProofFile.Honest.K9.part_all
#print axioms ProofFile.Honest.K9.part_of_all
#print axioms ProofFile.Honest.K9.used_of_part
#print axioms ProofFile.Honest.K9.set_link
#print axioms ProofFile.Honest.K9.counted_of_counts
#print axioms ProofFile.Honest.K9.eq_trace
