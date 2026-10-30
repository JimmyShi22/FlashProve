-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/ReadsK13.lean: THE PROOF OF THE STATEMENT THAT
Johnson/Desc/K13/Law/OwedReadsK13.lean WRITES AS OWED: inside the promise in front of block number
k, at a verifier's state without a mark, kind K13's layer's sentence at "every pending row holds"
and at "the one claim holds" reads of the witness the index masks' tenant's message, that tenant's
pad and the cells alone. Statements with their proofs; and the premise on the table as a test with
code.
Main names:
  `readsK13_sub`: what the layer says that it reads is among what the table books for the item
    (`Item.reads`, Johnson/Desc/First/Borders.lean), at every item.
  `no_rows`: where "nothing is sent yet" is open and the border is not the chain's end: inside the
    promise, without a mark, no row is on the table.
  `rows_read`: where the index masks' pin and the four public items are open: inside the promise,
    without a mark: "all rows on the table are true" has one truth value at two witnesses that
    agree on the three components: `reads_rows` (Johnson/Desc/K13/Law/ReaderByBook.lean), its eight
    tests out of the promise (`promise_index`, `seat_in_hand`) and the plan (`below_of_plan`).
  `readsK13_ok`: **the owed statement.**
  `readsOkAt_k13`: so `ReadsOkAtQ`'s own clause (Johnson/Desc/Sound/BordersSidesOn.lean) holds at
    the two items, with what the table books in the place of `readsK13`.
  `borderK13B`, `borderK13_of`: `BorderK13` as a test with code; where it says yes the premise
    holds.
  `bordersK13B`: the test at every border of a list at which one of the two items is open: FOR A RUN
    OR THE KERNEL, at the written lists and the filling of the table's door that is handed in.
What is not claimed. The statement's premises: `FillsK13`, `PlanM3`, what Mg says at "nothing is
sent yet", `BorderK13` (a fact on closed lists: `bordersK13B` is evaluated at no list in this file).
Nothing on the other items.
Nothing on soundness.
Words. "Block": a sub-protocol of the IOP as it is written in Lean. "The plan": the list of rounds
with each round's error bound, and the numbers made of it. "The verifier's state": what the verifier
carries from one sub-protocol to the next. "The promise": the condition on the public side at a
border between two sub-protocols.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.OwedReadsK13
import Johnson.Desc.K13.Law.PileReadsOut
import Johnson.Desc.K13.Law.IndexSeatAtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers Comp)
open VerifiableInference.Desc.Sound (MsgT Sending Mem Frame onQ meansQ sameQ insQ outsQ openAfter)
open VerifiableInference.Desc.K12.Door (msgShapesB bookInOrderB seatsCarriedB toTree)

/-- What the layer says that it reads is among what the table books. -/
theorem readsK13_sub (arr : ℕ → ℕ → ℕ) (N : Numbers) (links : List ModelPart) (i : Item) (c : Comp)
    (h : c ∈ readsK13 arr N i) : c ∈ i.reads arr N links := by
  cases i <;> simp [readsK13] at h <;>
    simp [Item.reads, Item.tenants, h]

section
variable {A Pp W : Type} {Fr : Frame}

/-- **Where nothing is sent yet no row is on the table.** -/
theorem no_rows (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place)
    (get : A → Pp × S) (k : ℕ) (hNS : ∀ x, Mg.pub .noneSent x = noneSentC N x.2)
    (hns : Pub.noneSent ∈ (First.pubSets Mg.more links ps)[k]?.getD []) (p : Place)
    (hp : ps[k]? = some p) (hst : First.standAt links p ≠ .mem) (a : A × Fr.E.Str)
    (ha : onQ N Mg links ps get k a) (hm : (get a.1).2.failed = none) :
    (get a.1).2.rows = [] := by
  obtain ⟨_, hr⟩ := ha
  obtain ⟨hB, _, _, _⟩ := hr.resolve_left (fun h => h hm)
  simp only [Bool.and_eq_true] at hB
  have hsh : First.shapeAt links ps[k]? (get a.1).2 = true := hB.1.1.1.1.1
  rw [hp] at hsh
  simp only [First.shapeAt, Bool.and_eq_true, beq_iff_eq] at hsh
  have hne : ∀ m, (get a.1).2.here ≠ .mem m := by
    intro m hh
    apply hst
    rw [← hsh.1.1]
    unfold First.standOf
    rw [hh]
  have h0 := List.all_eq_true.1 hB.1.2 .noneSent (List.mem_append_left _ hns)
  rw [hNS] at h0
  simp only [noneSentC, Bool.and_eq_true] at h0
  rw [rows_pile hne]
  exact List.isEmpty_iff.1 h0.2

end

section
variable {A Pp Xi Cells Tok : Type} {nR : ℕ} {Fr : Frame} {P : Where} {N : Numbers}
  {Mg : Meaning Pp (Desc.Wit Cells Tok MsgT)} {cs : Codes} {sh : Params.ReqShape}
  {ly : Params.ReqLayout} {rest : Pp × S → Bool} {arr : ℕ → ℕ → ℕ}
  {mat : Cells → Fin nR → (Fin P.lin.kCol → Bool) → GE} {G : FileDescription Xi}
  {smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp}
  {ms : List Mem} {decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells}
  {M : List OracleShape} {L : K12.Door.Laid}

/-- **Where the index masks' pin and the four public items are open.** -/
theorem rows_read (hF : FillsK13 P N Mg cs sh ly rest arr mat G smp ms decT M L)
    (hPl : PlanM3 L M ms cs N) (links : List ModelPart) (ps : List Place) (get : A → Pp × S) (k : ℕ)
    (hpin : Item.pinI ∈ openAt links ps k)
    (hk : ∀ q ∈ knownK13, q ∈ (First.pubSets Mg.more links ps)[k]?.getD []) (a : A × Fr.E.Str)
    (ha : onQ N Mg links ps get k a) (hm : (get a.1).2.failed = none)
    (w w' : Desc.Wit Cells Tok MsgT) (hc : w.cells = w'.cells)
    (hmsg : w.msg (arr N.index.1 N.index.2) = w'.msg (arr N.index.1 N.index.2))
    (hpad : w.pad N.index.1 N.index.2 = w'.pad N.index.1 N.index.2) :
    RowsTrue (rwBook arr mat (get a.1)) (get a.1).2 w ↔
      RowsTrue (rwBook arr mat (get a.1)) (get a.1).2 w' := by
  have hMg := mgK13_of_fills hF
  obtain ⟨hii, hit, hbk, hQ⟩ := promise_index N Mg links ps get k hpin a ha hm
  have hQ' : ∀ q ∈ knownK13, Mg.pub q (get a.1) = true := fun q hq => (hQ q (hk q hq)).1
  have hbIn : bookItem ∈ knownK13 := by simp [knownK13]
  have hsIn : seatsItem ∈ knownK13 := by simp [knownK13]
  have hmIn : shapesItem ∈ knownK13 := by simp [knownK13]
  have hpIn : pileMasksItem ∈ knownK13 := by simp [knownK13]
  have h₁ : msgShapesB M (get a.1).2.st = true := by rw [← hMg.shapes]; exact hQ' _ hmIn
  have h₂ : bookInOrderB 0 (get a.1).2.book (get a.1).2.roots = true := by
    rw [← hMg.book]; exact hQ' _ hbIn
  have h₃ : seatsCarriedB L (get a.1).2.book = true := by rw [← hMg.seats]; exact hQ' _ hsIn
  have hOn : pileMasksC (get a.1).2 = true := by rw [← hMg.masks]; exact hQ' _ hpIn
  have hI : ∀ x, Mg.pub .indexIs x = true → K1.indexIsB N.indexNo x.2 = true := fun x h => by
    rw [hMg.ours.indexIs] at h; exact h
  have hT : ∀ x, Mg.pub .indexThere x = true → K1.indexThereB x.2 = true := fun x h => by
    rw [hMg.ours.indexThere] at h; exact h
  have hseat : (get a.1).2.book.place[(get a.1).2.out.indexMasks]? = some N.index :=
    eq_of_beq (seat_in_hand N Mg (toTree L) knownK13 hsIn
      (fun z hz => by rw [hMg.seats] at hz; exact hz) hI hT hPl.hL (get a.1) ps[k]? hQ' hii hit hbk)
  have hthere : (get a.1).2.out.indexMasks < (get a.1).2.st.oracles.size := by
    have e : ((get a.1).2.st.oracles[(get a.1).2.out.indexMasks]?).isSome = true := hT _ hit
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 e
    exact (Array.getElem?_eq_some_iff.1 ho).1
  have hbk' := hbk
  unfold First.bookAt at hbk'
  simp only [Bool.and_eq_true, beq_iff_eq] at hbk'
  exact reads_rows arr mat N M L (get a.1).1 (get a.1).2 h₁ h₂ h₃ hbk'.1.2
    (below_of_plan hPl.hbelow (get a.1) ps[k]? hbk h₃) hthere hseat hOn w w' hc hmsg hpad

end

/-- **The owed statement.** -/
theorem readsK13_ok : OwedReadsK13 := by
  intro A Pp Xi Cells Tok nR Fr P N Mg cs sh ly rest arr mat G smp ms decT M L links ps get k hF hPl
    hNS hB i a w w' hi ha hm hsame hw
  have key : RowsTrue (rwBook arr mat (get a.1)) (get a.1).2 w →
      RowsTrue (rwBook arr mat (get a.1)) (get a.1).2 w' := by
    rcases hB with ⟨hpin, hk⟩ | ⟨hns, p, hp, hst⟩
    · have h3 : w.msg (arr N.index.1 N.index.2) = w'.msg (arr N.index.1 N.index.2) ∧
          w.pad N.index.1 N.index.2 = w'.pad N.index.1 N.index.2 ∧ w.cells = w'.cells := by
        rcases hi with rfl | rfl <;>
          exact ⟨hsame (.msg _) (by simp [readsK13]), hsame (.pad _ _) (by simp [readsK13]),
            hsame .cells (by simp [readsK13])⟩
      exact (rows_read hF hPl links ps get k hpin hk a ha hm w w' h3.2.2 h3.1 h3.2.1).1
    · exact fun _ => rowsTrue_nil _ (no_rows N Mg links ps get k hNS hns p hp hst a ha hm) w'
  rcases hi with rfl | rfl
  · exact (hF.pile _ _ _).2 (key ((hF.pile _ _ _).1 hw))
  · exact (hF.pileOne _ _ _).2 (key ((hF.pileOne _ _ _).1 hw))

/-- **So `ReadsOkAtQ`'s own clause holds at the two items.** -/
theorem readsOkAt_k13 {A Pp Xi Cells Tok : Type} {nR : ℕ} {Fr : Frame} (P : Where) (N : Numbers)
    (Mg : Meaning Pp (Desc.Wit Cells Tok MsgT)) (cs : Codes) (sh : Params.ReqShape)
    (ly : Params.ReqLayout) (rest : Pp × S → Bool) (arr : ℕ → ℕ → ℕ)
    (mat : Cells → Fin nR → (Fin P.lin.kCol → Bool) → GE) (G : FileDescription Xi)
    (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells)
    (M : List OracleShape) (L : K12.Door.Laid) (links : List ModelPart) (ps : List Place)
    (get : A → Pp × S) (k : ℕ)
    (hF : FillsK13 P N Mg cs sh ly rest arr mat G smp ms decT M L) (hPl : PlanM3 L M ms cs N)
    (hNS : ∀ x, Mg.pub .noneSent x = noneSentC N x.2) (hB : BorderK13 Mg.more links ps k)
    (i : Item) (hi : i = .pile ∨ i = .pileOne) (a : A × Fr.E.Str)
    (w w' : Desc.Wit Cells Tok MsgT) (ha : onQ N Mg links ps get k a)
    (hm : (get a.1).2.failed = none)
    (_ : openAfter (insQ links ps) (outsQ links ps) (· ∈ First.start links) k i)
    (_ : ¬ insQ links ps k i) (hc : ∀ c ∈ i.reads arr N links, sameQ c w w')
    (hw : meansQ N Mg get i a w) : meansQ N Mg get i a w' :=
  readsK13_ok P N Mg cs sh ly rest arr mat G smp ms decT M L links ps get k hF hPl hNS hB i a w w'
    hi ha hm (fun c h => hc c (readsK13_sub arr N links i c h)) hw

/-- **`BorderK13` as a test with code.** -/
def borderK13B (M : First.More) (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  ((openAt links ps k).contains .pinI &&
      knownK13.all fun q => ((First.pubSets M links ps)[k]?.getD []).contains q) ||
    (((First.pubSets M links ps)[k]?.getD []).contains .noneSent &&
      match ps[k]? with
      | some p => decide (First.standAt links p ≠ .mem)
      | none => false)

/-- Where the test says yes the premise holds. -/
theorem borderK13_of {M : First.More} {links : List ModelPart} {ps : List Place} {k : ℕ}
    (h : borderK13B M links ps k = true) : BorderK13 M links ps k := by
  unfold borderK13B at h
  rcases Eq.mp (Bool.or_eq_true _ _) h with h | h
  · obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) h
    exact Or.inl ⟨by simpa using h1, fun q hq => by simpa using List.all_eq_true.1 h2 q hq⟩
  · obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) h
    refine Or.inr ⟨by simpa using h1, ?_⟩
    cases hp : ps[k]? with
    | none =>
      rw [hp] at h2
      cases h2
    | some p =>
      rw [hp] at h2
      exact ⟨p, rfl, of_decide_eq_true h2⟩

/-- The test at every border of a list at which one of the two items is open. -/
def bordersK13B (M : First.More) (links : List ModelPart) (ps : List Place) : Bool :=
  (List.range (ps.length + 1)).all fun k =>
    !((openAt links ps k).contains .pile || (openAt links ps k).contains .pileOne) ||
      borderK13B M links ps k

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.borderK13_of
#print axioms VerifiableInference.Desc.K13.Law.readsK13_sub
#print axioms VerifiableInference.Desc.K13.Law.no_rows
#print axioms VerifiableInference.Desc.K13.Law.rows_read
#print axioms VerifiableInference.Desc.K13.Law.readsK13_ok
#print axioms VerifiableInference.Desc.K13.Law.readsOkAt_k13
