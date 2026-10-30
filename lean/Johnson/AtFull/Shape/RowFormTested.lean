-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/RowFormTested.lean: TEN OF THE FOURTEEN LETTERS OF RowFormLedger.lean
(`CoefLetters`) FOLLOW FROM A YES OF THE VERIFIER's OWN "TEST BY A SECOND COMPUTATION"
(`rkSelfTestP`, Johnson/Desc/First/TailClaims/SelfTests.lean), WHICH STANDS BEHIND THE STEP "THE
WEIGHTS OF EVERY VIRTUAL ROW" IN THE SAME RUN ("K8.tests": `testsP`, SelfRows.lean). SO BEHIND A YES
OF THAT RUN oneV's CLAUSE `termsV` ACCEPTS AT THE LEDGER THAT IS READ THERE, FROM THREE PREMISES ON
THE RECORD AND THE LEDGER IN FRONT OF THE RUN. General laws; no head; nothing is evaluated.

What it is for. A state in front of "the one equation" is meant to be reached through a yes of that
run, whoever plays (that join is owed: see the Limits). Then what the run's own guards say need not
be paid a second time from the plan or from the arrays' looks.

How. The library hands out what a yes of the test says, in eleven conjuncts (`rk_all`,
EquationsSelf.lean). Five are spent: what was heard; the expected pieces; the fourth (the count of
the digits' array's virtual rows, and callHeld at both calls); piecesTile; the eighth (of which
tieShapeHeld and planesShapeHeld are read). The calls are as expected (callHeld): a call's point has
as many coordinates as the call has bits n; each piece has 2^a rows, begins at a multiple of its
number of rows, and has b = a + clog2 CP ≤ n: so the piece's point, cut out of the call's, has a
coordinates. The pieces tile the digits' array (piecesTile): that array has tau rows, and each
expected piece lies in it; the expected pieces name each piece of each call (`wants_pieces`). The
planes' array has three virtual rows and 32 rows, and the two points have five coordinates and more
(planesShapeHeld). Each matrix's array has as many rows as the matrix has rows of symbols
(tieShapeHeld). The digits' array has 2 nbW + 2 virtual rows, which is not three: so the two arrays
are apart. The test is asked at the ledger behind the step, and the step turns no array's number of
rows or of virtual rows (`Fo.frame_all`).

Main names.
* `wants_pieces`; `piece_letters_tested`: a piece's four letters from callHeld and piecesTile.
* **`coefLetters_of_tested`**: a yes of rkSelfTestP tl G, at a G with F's numbers of rows and of
  virtual rows, gives CoefLetters tl g F from the four letters that it does not give: tables, reads,
  ties, mats.
* `TestsFront tl F`: the three premises: tables; Powered at the ledger's batching element (which
  gives reads, ties, mats: `powered_letters`); the ledger is clean. `testsFront_lsTail`: the writing
  of the run "K8.lsTail" keeps them. **`termsV_of_testsP`**: testsP nU tl F = .ok Fc and TestsFront
  tl F give termsV L { Fc with doorShutF := true } = true at every L.
* `FrontOfTests e`: TestsFront at the ledger and the record of a state. **`termsV_behind_tests`**:
  the same of the law's text of the run (k8Tests, Johnson/Desc/First/Batch/Law/K8Tests.lean), at the
  ledger read behind it. **`termsV_behind_whole`**: the same of the run that the kind's own block
  `whole p` states under the name "K8.tests" (by the library's k8_tests_under, K8Under.lean).

Limits. IMPLICATIONS, FROM A YES. THE THREE PREMISES (TestsFront) ARE PAID BY NOBODY HERE. THE JOIN
AT THE OTHER END IS OWED: that this run stands in a link's order behind the batching, that it stands
last there, and that nothing between it and "the one equation" writes a virtual row's weights, form
or lists, or an array's number of rows, is not shown. No example in Lean shows that the premises can
hold together. One of oneV's clauses. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.RowFormLedger
import Johnson.Desc.First.TailClaims.EquationsSelf
import Johnson.Desc.First.Batch.Law.K8CoefAll
import Johnson.Desc.First.TailClaims.EquationsTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open Fo (Frame coefAll allPieces)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims (rkSelfTestP coefBody testsP coefficientsP)
open VerifiableInference.Desc.First.TailClaims.Law (rk_all tests_ok)
open VerifiableInference.Desc.K9.Shape (termsV)
open VerifiableInference.Desc.K9L (k8Tests k8Tests_ok fork_put k8_tests_under)
open VerifiableInference.Desc.First.K8 (whole ParW)

/-! ## 1 The expected pieces -/

/-- The pieces that the test by a second computation expects name each piece of each call. -/
theorem wants_pieces (tl : HTailF2) (nbW : Nat) (Wn : List Want)
    (hw : tl.wants = some (nbW, Wn)) :
    ∀ q i, q < 2 → i < nbW → ∃ w ∈ Wn, w.call = q ∧ w.i = i := by
  unfold HTailF2.wants at hw
  simp only at hw
  split at hw
  · exact nomatch hw
  · obtain ⟨e1, e2⟩ := Prod.mk.inj (Option.some.inj hw)
    subst e1
    subst e2
    intro q i hq hi
    have hq' : q = 0 ∨ q = 1 := by omega
    by_cases hr : (tl.tau - 2 ^ Nat.log2 tl.tau != 0) = true
    · simp only [hr, if_true] at hi ⊢
      have hi' : i = 0 ∨ i = 1 := by omega
      rcases hq' with rfl | rfl <;> rcases hi' with rfl | rfl <;> simp
    · simp only [hr, Bool.false_eq_true, if_false] at hi ⊢
      obtain rfl : i = 0 := by omega
      rcases hq' with rfl | rfl <;> simp

/-! ## 2 One piece -/

/-- **A piece's four letters, from three guards of the test by a second computation**: the call is
as expected; the pieces tile the digits' array. G: the ledger at which the test is asked. -/
theorem piece_letters_tested (tl : HTailF2) (g : Forest.Heard) (G : Fork) (nbW : Nat)
    (Wn : List Want) (hw : tl.wants = some (nbW, Wn)) {q : Nat} (hq : q < 2)
    (hc : tl.callHeld g nbW q = true) (ht : tl.piecesTile G Wn = true) {p : Piece}
    (hp : p ∈ (tl.zOf q).pieces.toList) :
    p.Rp = 2 ^ (piecePoint tl g (q, p)).size ∧
      (piecePoint tl g (q, p)).size ≤ clog2 (G.trees.getD p.tree {}).R ∧
      p.r0 % 2 ^ (piecePoint tl g (q, p)).size = 0 ∧
      p.r0 < 2 ^ clog2 (G.trees.getD p.tree {}).R := by
  unfold HTailF2.callHeld at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, c6⟩, -⟩, -⟩, c9⟩, c10⟩, -⟩, -⟩, -⟩ := hc
  have hp' : p ∈ (tl.zOf q).pieces := Array.mem_toList_iff.1 hp
  have hd := Array.all_eq_true'.1 c10 p hp'
  unfold HTailF2.pieceHeld at hd
  simp only [Bool.and_eq_true] at hd
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, d4⟩, d5⟩, -⟩, -⟩, d8⟩, d9⟩, -⟩, -⟩ := hd
  have d4' : 2 ^ p.a = p.Rp := beq_iff_eq.1 d4
  have d5' : p.r0 % p.Rp = 0 := beq_iff_eq.1 d5
  have d8' : p.b = p.a + clog2 p.CP := beq_iff_eq.1 d8
  have d9' : p.b ≤ (tl.zOf q).call.n := of_decide_eq_true d9
  have c9' : (g.zk.getD q #[]).size = (tl.zOf q).call.n := beq_iff_eq.1 c9
  have hsz : (piecePoint tl g (q, p)).size = p.a := by
    show ((g.zk.getD q #[]).extract ((tl.zOf q).call.n - p.b)
      ((tl.zOf q).call.n - p.b + p.a)).size = p.a
    rw [Array.size_extract, c9']
    omega
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hp'
  have hi' : i < nbW := by
    rw [← beq_iff_eq.1 c6]
    exact hi
  obtain ⟨w, hwm, w1, w2⟩ := wants_pieces tl nbW Wn hw q i hq hi'
  unfold HTailF2.piecesTile at ht
  simp only [Bool.and_eq_true] at ht
  have hx := List.all_eq_true.1 ht.2 w hwm
  rw [w1, w2, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some] at hx
  simp only [Bool.and_eq_true] at hx
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨e1, -⟩, e3⟩, e4⟩, -⟩, -⟩, e7⟩, -⟩, -⟩, -⟩ := hx
  have e1' := beq_iff_eq.1 e1
  have e3' := beq_iff_eq.1 e3
  have e4' := beq_iff_eq.1 e4
  have e7' := of_decide_eq_true e7
  have hin : (tl.zOf q).pieces[i].r0 + (tl.zOf q).pieces[i].Rp ≤
      (G.trees.getD (tl.zOf q).pieces[i].tree {}).R := by
    rw [e1', e3', e4']
    exact e7'
  have hR : (G.trees.getD (tl.zOf q).pieces[i].tree {}).R ≤
      2 ^ clog2 (G.trees.getD (tl.zOf q).pieces[i].tree {}).R :=
    OnBytes.Slice.le_two_pow_ceilLog2 _
  have hpos : 0 < 2 ^ (tl.zOf q).pieces[i].a := Nat.two_pow_pos _
  rw [hsz]
  refine ⟨d4'.symm, ?_, by rw [d4']; exact d5', ?_⟩
  · refine (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).1 ?_
    show 2 ^ (tl.zOf q).pieces[i].a ≤ 2 ^ clog2 _
    omega
  · show (tl.zOf q).pieces[i].r0 < 2 ^ clog2 _
    omega

/-! ## 3 Ten of the fourteen letters -/

/-- **A YES OF THE TEST BY A SECOND COMPUTATION GIVES TEN OF THE FOURTEEN LETTERS.** G: the ledger
at which it is asked; F: a ledger with the same arrays, numbers of rows and of virtual rows. The
four that it does not give stay premises. -/
theorem coefLetters_of_tested {tl : HTailF2} {g : Forest.Heard} {F G : Fork} (hfr : Frame F G)
    (hg : tl.heard = some g) (h : rkSelfTestP tl G = .ok ())
    (tables : ∀ n t, tl.ix.U.getD n none = some t →
      ((F.trees.getD t {}).kind == HKind.table) = true → (F.trees.getD t {}).R = 1)
    (reads : tl.vt = powers F.theta tl.tau) (ties : tl.vp = powers F.theta tl.tau)
    (mats : ∀ mu, mu < tl.NM →
      tl.rowX.getD mu #[] = powers (powE F.theta tl.stepF) (tl.shp.getD mu {}).mS) :
    CoefLetters tl g F := by
  obtain ⟨g', jo, nbW, Wn, hg', -, hw, g1, g2, -, -, g5, -⟩ := rk_all tl G h
  obtain rfl : g = g' := Option.some.inj (hg.symm.trans hg')
  simp only [Bool.and_eq_true] at g1 g5
  have hcall : ∀ q, q < 2 → tl.callHeld g nbW q = true := fun q hq =>
    List.all_eq_true.1 g1.2 q (by
      have : q = 0 ∨ q = 1 := by omega
      rcases this with rfl | rfl <;> simp)
  have hpc : ∀ a ∈ allPieces tl, a.1 < 2 ∧ a.2 ∈ (tl.zOf a.1).pieces.toList := by
    intro a ha
    unfold allPieces at ha
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
      exact ⟨by omega, hp⟩
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
      exact ⟨by omega, hp⟩
  have four := fun a (ha : a ∈ allPieces tl) =>
    piece_letters_tested tl g G nbW Wn hw (hpc a ha).1 (hcall _ (hpc a ha).1) g2 (hpc a ha).2
  have g2' := g2
  unfold HTailF2.piecesTile at g2'
  simp only [Bool.and_eq_true] at g2'
  have hZrows : (G.trees.getD tl.ix.ZZ {}).rows.size = 2 * nbW + 2 := beq_iff_eq.1 g1.1.1
  have hZR : (G.trees.getD tl.ix.ZZ {}).R = tl.tau := beq_iff_eq.1 g2'.1.1.1.1.2
  have hp := g5.2
  unfold HTailF2.planesShapeHeld at hp
  simp only [Bool.and_eq_true] at hp
  have hBrows : (G.trees.getD tl.ix.BZ {}).rows.size = 3 := beq_iff_eq.1 hp.1.1.1.1.1.1.1.1
  have hBR : (G.trees.getD tl.ix.BZ {}).R = 32 := beq_iff_eq.1 hp.1.1.1.1.1.1.1.2
  have hz0 := beq_iff_eq.1 hp.1.2
  have hz1 := beq_iff_eq.1 hp.2
  refine
    { tables := tables
      pieceRows := fun a ha => (four a ha).1
      pieceFits := fun a ha => by rw [← (hfr.2 _).1]; exact (four a ha).2.1
      pieceAligned := fun a ha => (four a ha).2.2.1
      pieceFirst := fun a ha => by rw [← (hfr.2 _).1]; exact (four a ha).2.2.2
      reads := reads, ties := ties
      digits := by rw [← (hfr.2 _).1]; exact hZR
      planes := by rw [← (hfr.2 _).1]; exact hBR
      point0 := by
        show 5 ≤ g.zb0.size
        omega
      point1 := by
        show 5 ≤ g.zb1.size
        omega
      apart := fun he => by
        rw [he] at hBrows
        omega
      mats := mats
      matRows := fun mu hmu => ?_ }
  have hm := List.all_eq_true.1 g5.1.1.2 mu (List.mem_range.2 hmu)
  unfold HTailF2.tieShapeHeld at hm
  simp only [Bool.and_eq_true] at hm
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, c3⟩, -⟩, -⟩, c6⟩, -⟩, -⟩, c9⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩,
    -⟩, -⟩, -⟩, -⟩ := hm
  rw [← (hfr.2 _).1]
  exact (beq_iff_eq.1 c3).trans ((beq_iff_eq.1 c9).trans (beq_iff_eq.1 c6))

/-! ## 4 Behind a yes of the run of self tests -/

/-- **The three premises in front of the run**, at a record tl and a ledger F: the letter tables;
the record is Powered at the ledger's batching element; the ledger is clean. -/
def TestsFront (tl : HTailF2) (F : Fork) : Prop :=
  (∀ n t, tl.ix.U.getD n none = some t →
    ((F.trees.getD t {}).kind == HKind.table) = true → (F.trees.getD t {}).R = 1) ∧
  OnBytes.Tie.Pv.Tail.Port.Powered tl F.theta ∧ EachRow RowClean F

/-- The writing of the run "K8.lsTail", which stands in front of "K8.tests", keeps them. -/
theorem testsFront_lsTail {tl : HTailF2} {F : Fork} (h : TestsFront tl F) (x : Array E) :
    TestsFront { tl with lsTail := x } F :=
  ⟨h.1, ⟨h.2.1.vp, h.2.1.vt, h.2.1.rowX, h.2.1.loX, h.2.1.eqFirst, h.2.1.shape⟩, h.2.2⟩

/-- **BEHIND A YES OF THE THREE TESTS IN A ROW** (testsP, SelfRows.lean: the run "K8.tests" on plain
data) **THE CLAUSE OF "THE ONE EQUATION"'s TEST ON VALUES ACCEPTS AT THE LEDGER THAT THEY RETURN,
WITH THE DOOR SHUT.** -/
theorem termsV_of_testsP {nU : Array Nat} {tl : HTailF2} {F Fc : Fork}
    (h : testsP nU tl F = .ok Fc) (hf : TestsFront tl F) (L : LinkCtx) :
    termsV L { Fc with doorShutF := true } = true := by
  obtain ⟨-, h2, h3⟩ := tests_ok h
  unfold coefficientsP at h2
  split at h2
  · cases h2
  · rename_i g hg
    obtain rfl := Except.ok.inj h2
    obtain ⟨p1, p2, p3⟩ := powered_letters hf.2.1
    exact termsV_coefAll L tl g F
      (coefLetters_of_tested (G := coefBody tl g F) (Fo.frame_all tl g F) hg h3 hf.1 p1 p2
        fun mu _ => p3 mu) hf.2.2

/-- The three premises at the ledger and the record of a state. -/
def FrontOfTests (e : S) : Prop :=
  ∀ F tl, e.fork? = some F → e.tl? = some tl → TestsFront tl F

/-- **The same of the law's text of the run** (k8Tests, Johnson/Desc/First/Batch/Law/K8Tests.lean),
at the ledger that is read behind it. -/
theorem termsV_behind_tests (nU : Array Nat) (e e₁ : S) (h : k8Tests nU e = .ok e₁)
    (hrest : FrontOfTests e) :
    ∃ F₁, e₁.fork? = some F₁ ∧ ∀ L, termsV L { F₁ with doorShutF := true } = true := by
  obtain ⟨F, tl, g, h1, h2, h3, -, h5, h6⟩ := k8Tests_ok nU e e₁ h
  obtain ⟨r1, r2, r3⟩ := hrest F tl h1 h2
  obtain ⟨p1, p2, p3⟩ := powered_letters r2
  have hL : CoefLetters tl g F :=
    coefLetters_of_tested (G := coefBody tl g F) (Fo.frame_all tl g F) h3 h5 r1 p1 p2
      fun mu _ => p3 mu
  refine ⟨coefAll tl g F, ?_, fun L => termsV_coefAll L tl g F hL r3⟩
  rw [h6]
  exact fork_put e tl F _ h1

/-- **The same of the run that the kind's own block states under the name "K8.tests"**
(k8_tests_under, Johnson/Desc/First/Batch/Law/K8Under.lean). -/
theorem termsV_behind_whole (p : ParW) :
    ∃ r, (whole p).after.lookup "K8.tests" = some r ∧ ∀ e e₁, r e = .ok e₁ → FrontOfTests e →
      ∃ F₁, e₁.fork? = some F₁ ∧ ∀ L, termsV L { F₁ with doorShutF := true } = true := by
  obtain ⟨r, hr, hu⟩ := k8_tests_under p
  exact ⟨r, hr, fun e e₁ h hrest => termsV_behind_tests p.nU e e₁ (hu e e₁ h) hrest⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.wants_pieces
#print axioms Johnson.AtFull.Shape.piece_letters_tested
#print axioms Johnson.AtFull.Shape.coefLetters_of_tested
#print axioms Johnson.AtFull.Shape.testsFront_lsTail
#print axioms Johnson.AtFull.Shape.termsV_of_testsP
#print axioms Johnson.AtFull.Shape.termsV_behind_tests
#print axioms Johnson.AtFull.Shape.termsV_behind_whole
