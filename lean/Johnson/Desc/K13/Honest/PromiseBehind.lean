-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Honest/PromiseBehind.lean: kind K13, the members' batching: THE PROMISE OF THE
FIRST CHAIN's TABLE OF JOINTS (`onAt`, Johnson/Desc/First/Borders.lean) GOES FROM THE BORDER IN
FRONT OF THE KIND's PLACE TO THE BORDER BEHIND IT, at the state that the joined sub-protocol leaves
(`withClaim`, Johnson/Desc/K13/Honest/SubProtocols.lean). A definition; statements with their
proofs. On plain states; general in the table's parameters.

Where it comes from. The library has this step: it is the second of the five ties inside `k13_tied`
(Johnson/Desc/K13/Law/AtTable.lean), stated there of a piece and of its oracles. Here the same
argument is said of `onAt` itself and of two states, so that it can be called where no piece is at
hand. What is asked of the table is the library's own `RowM3`.

What the state behind differs in: the statement (of which the ledgers alone turn: `takeMasks_same`,
Johnson/Desc/K13/Law/PinDec.lean), the count of rows that waits (none), and where the chain stands
(at its end, with W's message announced and one claim).
Main names:
  `PubM3 P N Mg`: what the step reads of the meaning's parameters: six clauses. Five in the words of
    `FillsK13C` (Johnson/Desc/K13/Law/FillsK13C.lean): what Mg says at the public items "frontOk",
    "indexIs", "indexThere"; that it says nothing more at the first; what "held" says at the index
    masks' tenant (a tree and a place in it). The sixth is no field there: "in order" reads the
    public part alone. `pubM3_of_fills`: from `FillsK13C` and that sixth clause.
  `frontOkC_withClaim`: **the public item that the kind makes**: behind, the claim is made of a row
    and W's vector fits its table.
  `shapeAt_withClaim`, `bookAt_withClaim`, `index_withClaim`, `smpHeld_withClaim`: clause by clause.
  `onAt_behind`: **the promise behind, from the promise in front**, AT EVERY ROW AND EVERY
    ANNOUNCEMENT: the promise behind reads neither.

The premises of `onAt_behind`. On the table: `RowM3`. On the meaning: `PubM3`; that "decodes",
"shown" and "no collision" go from the one state and oracles to the other (three premises; where
these parameters are true outright they are idle); that a public item which is open in front goes on
(two premises; idle where none is open in front). On the state in front: no mark of failure; the
taking of mask entries returns; the shape of the test on the committed table is lawful.

What is not claimed. That the premises on the table or on the meaning hold at any parameters. That a
sub-protocol of an IOP as written in Lean leaves this state. Nothing on the items that are open at
the two borders. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Law.AtTable
import Johnson.Desc.K13.Law.FillsK13C
import Johnson.Desc.K13.Law.FillK13Laws
import Johnson.Desc.K13.Law.SigHeld
import Johnson.Desc.K13.Law.M3Fits
import Johnson.Desc.K13.Law.IndexKept
import Johnson.Desc.K13.Honest.SubProtocols

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes
open VerifiableInference.Desc (Place Strs smpHeld)
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers onAt)
open VerifiableInference.Desc.Ground (takeMasksP)
open VerifiableInference.Desc.K13.Law

/-! ## 1 What the step reads of the meaning -/

/-- **What the promise's step at the kind's place reads of the meaning's parameters.** -/
structure PubM3 {Pp W : Type} (P : Where) (N : Numbers) (Mg : Meaning Pp W) : Prop where
  /-- the public item that comes at the place is the kind's own test -/
  frontOk : ∀ x, Mg.pub .frontOk x = frontOkC P x.2
  /-- and it says nothing beside that test -/
  frontOkP : ∀ x, Mg.pubP .frontOk x
  /-- the two public items that are tied to the index masks' pin -/
  indexIs : ∀ x, Mg.pub .indexIs x = indexIsC N.indexNo x.2
  indexThere : ∀ x, Mg.pub .indexThere x = indexThereC x.2
  /-- the state holds the sample at the index masks' tenant (a tree and a place in it) -/
  held : ∀ x, Mg.held N.index.1 N.index.2 x = smpHeld x.2.st x.2.book N.index.1 N.index.2
  /-- "in order" reads the public part alone -/
  inOrder : ∀ p s s', Mg.inOrder (p, s) = Mg.inOrder (p, s')

/-- From the library's own structure on the meaning's parameters. -/
theorem pubM3_of_fills {Pp Xi Cells Tok : Type} {nR : ℕ} {P : Where} {N : Numbers}
    {Mg : Meaning Pp (Desc.Wit Cells Tok Sound.MsgT)} {cs : Codes} {arr : ℕ → ℕ → ℕ}
    {mat : Cells → Fin nR → (Fin P.lin.kCol → Bool) → OnBytes.Slice.GE} {G : FileDescription Xi}
    {smp : Pp × S → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((Johnson.Pack.sigOf cs s.l).om i).Smp}
    {ms : List Sound.Mem} {decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells}
    (h : FillsK13C P N Mg cs arr mat G smp ms decT)
    (hin : ∀ p s s', Mg.inOrder (p, s) = Mg.inOrder (p, s')) : PubM3 P N Mg :=
  ⟨h.frontOk, fun x => h.quiet .frontOk (by simp [quietC]) x, h.indexIs, h.indexThere, h.held, hin⟩

/-! ## 2 Clause by clause, at the state behind -/

/-- **The public item that the kind makes.** -/
theorem frontOkC_withClaim {P : Where} (s : S) (st : Statement) (msg : Array OracleNotice)
    (row : TensorRow) (hc : st.codes = s.st.codes) (hlin : linOk s.st.codes P.lin = true) :
    frontOkC P (withClaim s st msg row) = true := by
  show (claimMadeB (memberClaim row) &&
    decide (P.lin.kCol ≤ (linLayW st.codes P.lin).bits)) = true
  rw [hc, (claimMade_iff _).2 ⟨row, rfl⟩, decide_eq_true (fits_of_linOk hlin)]
  rfl

/-- The table's book-keeping: the chain stands at its end, no count of rows waits, no segment is
open. p: the place of the next sub-protocol, or none. -/
theorem shapeAt_withClaim (s : S) (st : Statement) (msg : Array OracleNotice) (row : TensorRow)
    (links : List ModelPart) (p : Option Place)
    (hp : ∀ p', p = some p' → First.standAt links p' = .mem) :
    First.shapeAt links p (withClaim s st msg row) = true := by
  cases p with
  | none => simp [First.shapeAt, First.standOf, S.noneWaits]
  | some p' => simp [First.shapeAt, First.standOf, S.noneWaits, S.link?, hp p' rfl]

/-- Where the book stands. -/
theorem bookAt_withClaim (N : Numbers) (s : S) (st : Statement) (msg : Array OracleNotice)
    (row : TensorRow) (hs : SameAll s.st st) (p p' : Option Place)
    (hT : N.treesAt p' = N.treesAt p) (hM : N.msgsAt p' = N.msgsAt p)
    (h : First.bookAt N p s = true) : First.bookAt N p' (withClaim s st msg row) = true := by
  unfold First.bookAt at h ⊢
  show (s.book.trees.size == N.treesAt p' && s.book.place.size == st.oracles.size &&
    st.oracles.size == N.msgsAt p') = true
  rw [sameAll_size hs, hT, hM]
  exact h

/-- The two public items that are tied to the index masks' pin. -/
theorem index_withClaim (s : S) (st : Statement) (msg : Array OracleNotice) (row : TensorRow)
    (hs : SameAll s.st st) : IndexKept s (withClaim s st msg row) :=
  indexKept_of rfl (le_of_eq (sameAll_size hs).symm) fun _ _ h => h

/-- The sample at a tenant: the tree number j, the place t in it. -/
theorem smpHeld_withClaim (s : S) (st : Statement) (msg : Array OracleNotice) (row : TensorRow)
    (hs : SameAll s.st st) (j t : ℕ) :
    smpHeld (withClaim s st msg row).st (withClaim s st msg row).book j t =
      smpHeld s.st s.book j t := by
  show smpHeld st s.book j t = smpHeld s.st s.book j t
  unfold smpHeld
  rw [smpSeed_same hs]

/-! ## 3 The promise behind -/

/-- **The promise behind the kind's place, from the promise in front.** k: the number of the kind's
sub-protocol in the list of places. n: how many mask entries are taken. The row and the announcement
are any. -/
theorem onAt_behind {Pp W : Type} (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart)
    (ps : List Place) (k : ℕ) (P : Where) (hT : RowM3 N Mg.more links ps k) (hF : PubM3 P N Mg)
    (p : Pp) (s : S) (y y' : Strs) {n : ℕ} {t : List ℕ × St} (msg : Array OracleNotice)
    (row : TensorRow) (ht : takeMasksP (dOf s) s.out.indexMasks n = some t)
    (hlin : linOk s.st.codes P.lin = true) (hm : s.failed = none)
    (hdec : Mg.decodes (p, s) y → Mg.decodes (p, withClaim s t.2.st msg row) y')
    (hsh : Mg.shown N.index.1 N.index.2 y → Mg.shown N.index.1 N.index.2 y')
    (hnc : Mg.noColl N.index.1 N.index.2 (p, s) y →
      Mg.noColl N.index.1 N.index.2 (p, withClaim s t.2.st msg row) y')
    (hride : ∀ q ∈ (First.pubSets Mg.more links ps)[k]?.getD [], Mg.pub q (p, s) = true →
      Mg.pub q (p, withClaim s t.2.st msg row) = true)
    (hrideP : ∀ q ∈ (First.pubSets Mg.more links ps)[k]?.getD [], Mg.pubP q (p, s) →
      Mg.pubP q (p, withClaim s t.2.st msg row))
    (ha : onAt N Mg links ps[k]? (openAt links ps k)
      ((First.pubSets Mg.more links ps)[k]?.getD []) (p, s) y) :
    onAt N Mg links ps[k + 1]? (openAt links ps (k + 1))
      ((First.pubSets Mg.more links ps)[k + 1]?.getD []) (p, withClaim s t.2.st msg row) y' := by
  have hs : SameAll s.st t.2.st := takeMasks_same ht
  obtain ⟨hd, hr⟩ := ha
  obtain ⟨hB, hS, hA, hPP⟩ := hr.resolve_left fun h => h hm
  simp only [Bool.and_eq_true] at hB
  have hall := List.all_eq_true.1 hB.1.2
  have hi : N.index ∈ First.sampledIn N (openAt links ps k) := idx_of_pin N hT.pinIn
  have hmem : ∀ q, q = Pub.indexIs ∨ q = Pub.indexThere →
      q ∈ First.pubOfItems (openAt links ps k) := fun q hq =>
    List.mem_flatMap.2 ⟨.pinI, hT.pinIn, by rcases hq with rfl | rfl <;> simp⟩
  have hii := hall _ (List.mem_append_right _ (hmem _ (Or.inl rfl)))
  have hit := hall _ (List.mem_append_right _ (hmem _ (Or.inr rfl)))
  have hK := index_withClaim s t.2.st msg row hs
  refine ⟨hdec hd, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
  · simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨shapeAt_withClaim s _ msg row links _ hT.next, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · unfold First.rowsHeld
      rw [hT.noRows]
      rfl
    · unfold First.membersHeld
      rw [hT.noRows]
      rfl
    · rw [← hF.inOrder p s]
      exact hB.1.1.2
    · refine List.all_eq_true.2 fun x hx => ?_
      rcases List.mem_append.1 hx with hx | hx
      · rcases hT.pubs x hx with rfl | hx'
        · rw [hF.frontOk]
          exact frontOkC_withClaim s _ msg row hs.1 hlin
        · exact hride x hx' (hall _ (List.mem_append_left _ hx'))
      · rcases hT.tied x hx with rfl | rfl
        · rw [hF.indexIs] at hii ⊢
          exact hK.1 _ hii
        · rw [hF.indexThere] at hit ⊢
          exact hK.2.1 hit
    · exact bookAt_withClaim N s _ msg row hs _ _ hT.trees hT.msgs hB.2
  · refine List.all_eq_true.2 fun x hx => ?_
    rw [hT.idxOnly x hx, hF.held, smpHeld_withClaim s _ msg row hs, ← hF.held (p, s)]
    exact List.all_eq_true.1 hS _ hi
  · intro x hx
    rw [hT.idxOnly x hx]
    exact ⟨hsh (hA _ hi).1, hnc (hA _ hi).2⟩
  · intro x hx
    rcases hT.pubs x hx with rfl | hx'
    · exact hF.frontOkP _
    · exact hrideP x hx' (hPP x hx')

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.pubM3_of_fills
#print axioms VerifiableInference.Desc.K13.Honest.frontOkC_withClaim
#print axioms VerifiableInference.Desc.K13.Honest.shapeAt_withClaim
#print axioms VerifiableInference.Desc.K13.Honest.bookAt_withClaim
#print axioms VerifiableInference.Desc.K13.Honest.index_withClaim
#print axioms VerifiableInference.Desc.K13.Honest.smpHeld_withClaim
#print axioms VerifiableInference.Desc.K13.Honest.onAt_behind
