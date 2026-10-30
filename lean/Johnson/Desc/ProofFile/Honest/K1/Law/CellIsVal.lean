-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/CellIsVal.lean:
cell_behind (Johnson/Desc/ProofFile/Honest/K1/Law/CellBehind.lean) WHERE THE JOB's DATA
ANSWERS: BEHIND THE MEMBER's STEP THE CELL OF THE THREAD's OWN WITNESS IS THE VALUE THAT THE DATA
ANSWERS, READ IN THE EXTENSION FIELD. One definition with code, four statements and their proofs.

  dataE         a value of the data as an element of the extension field, at a message's main
                degree: over the extension field (degree 3) as it stands, an element of the base
                field by the fields' map; over the base field an element of the extension field
                counts as 0, as in rowsR (Johnson/Desc/ProofFile/Honest/K1/Coins.lean)
  dataE_asE     over the extension field dataE is the frame's own asE
                (Johnson/Desc/ProofFile/Honest/RowData.lean) at "some v": A SECOND TEXT, TIED TO THE
                FIRST BY AN EQUATION WITHOUT A PREMISE; by asE_inl
                (Johnson/Desc/ProofFile/Honest/K1/AgreeTools.lean)
  dataE_inl     at an element of the base field, AT BOTH DEGREES, dataE is asE at "some v" too
  dataE_silent  THE ONE ARM AT WHICH THE TWO TEXTS PART, SAID OUT: over the base field an element of
                the extension field reads as 0 (asE hands the element itself). A default at a datum.
                WHOEVER SPENDS dataE BARS THE ARM: by the degree (three = true) or by the value (an
                element of the base field)
  cell_is_val   cell_behind's premises, and hv : the job's data at (n, rp.1, rp.2) is some v: the
                cell is dataE (the message's main degree is 3) v

hv is what data_is_val (Johnson/Desc/ProofFile/Honest/K1/Law/DataIsVal.lean) ends in, at a place's
job whose filling is laidData: this file does not import that one: whoever holds both joins them by
one rewriting.

Limits. All of CellBehind.lean's. A law under "Stepped": it has the cut from the frame, and holds of
nothing at a book that does not cover the part's count. Nothing on soundness, on completeness or on
any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.CellBehind
import Johnson.Desc.ProofFile.Honest.K1.AgreeTools

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT Mem dataQ seatTab)
open ProofFile.Honest.FirstThread (Letters)
open Johnson.Prover.Send (shapeAt)

/-- A value of the data as an element of the extension field. three: the message's main rows stand
over the extension field. -/
noncomputable def dataE (three : Bool) : GF ⊕ GE → GE
  | .inr x => if three then x else 0
  | .inl x => algebraMap GF GE x

/-- **Over the extension field it is the frame's own asE.** -/
theorem dataE_asE (v : GF ⊕ GE) : dataE true v = asE (some v) := by
  cases v with
  | inl x => exact (asE_inl x).symm
  | inr x => rfl

/-- **At an element of the base field it is asE, at both degrees.** -/
theorem dataE_inl (three : Bool) (x : GF) : dataE three (.inl x) = asE (some (.inl x)) :=
  (asE_inl x).symm

/-- **The silent arm, said out.** -/
theorem dataE_silent (x : GE) : dataE false (.inr x) = 0 := rfl

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok : Type}
variable {L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT} {b : Nat} {blk : Block S Cl}
  {wit : Local W₀ Rc Xi Tr → PlaceIn Xi} {J : SendJob (PlaceIn Xi) X} {own₀ : X} {sort : K1Sort}
  {arr : ℕ → ℕ → ℕ} {seats₀ : List (ℕ × ℕ)} {ms : List Mem} {rad : ℕ → ℕ}

/-- **Behind the member's step the cell is the
value that the job's data answers.** IT CARRIES dataE IN ITS END, AT ANY v AND EITHER DEGREE: the
silent arm (dataE_silent) is not barred here: whoever spends this law bars it. -/
theorem cell_is_val (R : K1Seated L b blk wit J own₀ sort arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) {k : Coins Bk} {s s' : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hA : ThrS L.thread Said b k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : L.thread.Stepped blk k s m E ds y cols s') (hFits : Book.BookFits s'.book)
    (hNum : ∀ (z : ℕ) (T : OnBytes.Tree), s'.book.trees[z]? = some T → T.number = z)
    (c : Cs (dueR J.P J.ride)) (hc : lentCut k 0 ⟨J.P.place, 0⟩ (dueR J.P J.ride) = some c)
    (n : ℕ) (hn : n < J.P.sent.size) (ds' : List Fmt.Drawn) (own : List (ℕ × ℕ))
    (hown : own.contains (seatAtMember L.bs b J.P n) = true) (p : K9.Part)
    (hp : K9.segAt? s' = some p) (c₀ : ℕ × String) (a : ReqArray) (i cc : ℕ) (rp : ℕ × ℕ)
    (ha : reqArray p.L.check.rows.layout c₀.1 c₀.2 = some a)
    (ho : p.L.check.frame.whereIs c₀.1 a.message = some (s.st.oracles.size + n))
    (hok : laidMatrixOk a (p.d.st.rowBits (s.st.oracles.size + n) .main)
      (p.d.st.placeBits (s.st.oracles.size + n) .main) = true)
    (hrp : laidAt a i cc = some rp) (hr : rp.1 < (shapeAt J.P n).mainRows)
    (hj : rp.2 < (J.P.codes.base.getD (shapeAt J.P n).code default).ell)
    (hans : (shapeAt J.P n).answers ≠ 0)
    (hpad : rp ∉ padInMain (J.P.codes.base.getD (shapeAt J.P n).code default).ell
      (shapeAt J.P n)) {v : GF ⊕ GE}
    (hv : J.data (wit m.st.input) { heard := m.st.heard, own := own₀, seen := .bare [] } n rp.1 rp.2 =
      some v) :
    (dataQ own p (seatTab J.P.codes arr ms
        (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds')))).cell c₀.1 c₀.2 i cc =
      dataE ((shapeAt J.P n).mainDeg == 3) v := by
  rw [cell_behind R Said hA hd hS hFits hNum c hc n hn ds' own hown p hp c₀ a i cc rp ha ho hok
    hrp hr hj hans hpad, hv]
  cases h3 : ((shapeAt J.P n).mainDeg == 3) <;> cases v <;> simp [dataE]

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.dataE
#print axioms ProofFile.Honest.K1.dataE_asE
#print axioms ProofFile.Honest.K1.dataE_inl
#print axioms ProofFile.Honest.K1.dataE_silent
#print axioms ProofFile.Honest.K1.cell_is_val
