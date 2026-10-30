-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/TieRowsCore.lean: THE CORE OF TieRowsS
(Johnson/Desc/ProofFile/Honest/K1/Law/TieShare.lean) CUT OUT AS A FORM ON A RECORD tl OF THE
SMALLNESS TEST AND A TABLE OF CELLS A, WITH NO THREAD IN IT: so that the form can be met and can
fail before any thread holds of a run. One definition, seven statements and their proofs.

  TieRowsAt          the two equations of TieRowsS, at letters tl and A: at the matrices' arrays A
                     holds the packed cells of the trace T; in row 0 of the array of reads it holds
                     the vector of reads at tl's own tables
  tieRowsS_iff       TieRowsS is: behind the pair and the member's step, at the state's record and
                     at every continuation, TieRowsAt of the thread's own witness's table
  tieRowsAt_some     IT CAN BE MET: where no two matrices share an array and none has the reads'
                     array, some table meets it (table_of_both,
                     Johnson/HonestTrace/PackedTieThird.lean)
  tieRowsAt_reads    two tables that meet it at one tl hold one vector of reads below nR
  tieRowsAt_bent     IT CAN FAIL: a table that meets it, bent at one entry of the vector below nR,
                     meets it no more
  tieRowsAt_bentM    the like at the first equation: bent at one packed cell inside the shape
  tieRowsAt_other    IT CAN FAIL AT OTHER TABLES: a table that meets it at tl does not meet it at a
                     record tl₂ with the same array of reads whose own tables read otherwise at some
                     entry below nR
  tieRowsAt_neither  WITHOUT A PREMISE, AND WITHOUT CONTENT: at the record of no matrix and no
                     table, at nR := 1, some table meets the form and some table does not: the form
                     is neither "false" nor "true"

tieRowsAt_other is the form's answer to the join that can make the item false: a witness whose
vector of reads is laid at other tables than the state's.

Limits. tieRowsAt_some IS CONDITIONAL: no record tl with a matrix is
given at which its two premises hold (tieRowsAt_neither's record has none); tieRowsAt_other IS
CONDITIONAL: no two records are given whose tables read otherwise: at tables that read alike
everywhere below nR it says nothing. SO THERE IS STILL NO MEMBER AND NO NEGATIVE TEST OF TieRowsS
ITSELF: these want a thread that holds of a run behind a reads' member. TieRowsAt is a definition:
nothing is claimed of it, and no goal file names it. Nothing on soundness, on completeness or on any
other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.TieShare
import Johnson.HonestTrace.PackedTieThird

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes VerifiableInference.Desc
open VerifiableInference.Desc.Sound (MsgT Mem cellsAt)
open OnBytes.Model (HTailF2)
open OnBytes.HonestTrace (Sz Tr parOfMats packedCells cellOf cellsC matsOf GtOne table_of_both)
open OnBytes.Tie.Pv.Tail.Port (u3Of)
open ProofFile.Honest.K8 (cellsAtOf)
open ProofFile.Honest.FirstThread (Letters)

/-- **The two equations of TieRowsS, at a record tl and a table of cells A.** It says what a table
holds; no thread, no run and no witness stands in it. A definition: a premise's form. -/
def TieRowsAt (X : OnBytes.Model.Verify.Public) (T : Tr) (m nR : ℕ) (tl : HTailF2)
    (A : ℕ → ℕ → ℕ → Cb.Gl.E) : Prop :=
  (∀ ν, ν < tl.NM → ∀ c, c < (Sz.ref.packedShape m ν).2 →
    ∀ i', i' < (Sz.ref.packedShape m ν).1 → A (tl.gtTree.getD ν 0) i' c =
      algebraMap Cb.Gl.F Cb.Gl.E (packedCells Sz.ref (cellOf X T) m ν i' c)) ∧
  (∀ j < nR, A (u3Of tl) 0 j =
    OnBytes.Model.Reading.gl.val (First.K8.Honest.readAt (parOfMats tl.mats) tl.funs.toList
      (cellsAtOf (cellsC X T) (matsOf X m)) j))

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr' X' P Cells Tok : Type}

/-- **TieRowsS is its core at the thread's own witness's table.** -/
theorem tieRowsS_iff (L : Letters Bk Cl W₀ Rc Xi Tr' X' P Cells Tok MsgT)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr') X' → Prop) (cs : OnBytes.Codes)
    (arr : ℕ → ℕ → ℕ) (ms : List Mem) (X : OnBytes.Model.Verify.Public)
    (T : Local W₀ Rc Xi Tr' → Tr) (b m nR : ℕ) :
    TieRowsS L Said cs arr ms X T b m nR ↔
      ∀ blk, L.bs[b]? = some blk → ∀ k s μ E ds y cols s', ThrS L.thread Said b k s μ E →
        drawsFit blk.rounds ds = true → L.thread.Stepped blk k s μ E ds y cols s' →
        ∀ tl, s'.tl? = some tl → ∀ ds', TieRowsAt X (T μ.st.input) m nR tl
          (cellsAt cs arr ms L.N m (L.pubOf μ.st.input.x, s')
            (L.Q.wit k μ.st.input (μ.st.heard ++ (ds ++ ds')))) :=
  ⟨fun h blk hb k s μ E ds y cols s' hA hd hS tl htl ds' =>
      h blk hb k s μ E ds y cols s' hA hd hS tl htl ds' _ rfl,
    fun h blk hb k s μ E ds y cols s' hA hd hS tl htl ds' A hAe => by
      rw [hAe]
      exact h blk hb k s μ E ds y cols s' hA hd hS tl htl ds'⟩

/-- **It can be met.** -/
theorem tieRowsAt_some (X : OnBytes.Model.Verify.Public) (T : Tr) (m nR : ℕ) {tl : HTailF2}
    (hG : GtOne tl) (hU : ∀ μ, μ < tl.NM → tl.gtTree.getD μ 0 ≠ u3Of tl) :
    ∃ A, TieRowsAt X T m nR tl A := by
  obtain ⟨A, h1, h2⟩ := table_of_both hG hU
    (fun ν i' c => algebraMap Cb.Gl.F Cb.Gl.E (packedCells Sz.ref (cellOf X T) m ν i' c))
    fun j => OnBytes.Model.Reading.gl.val (First.K8.Honest.readAt (parOfMats tl.mats)
      tl.funs.toList (cellsAtOf (cellsC X T) (matsOf X m)) j)
  exact ⟨A, fun ν hν c _ i' _ => h1 ν hν i' c, fun j _ => h2 j⟩

/-- Two tables that meet it at one record hold one vector of reads below nR. -/
theorem tieRowsAt_reads {X : OnBytes.Model.Verify.Public} {T : Tr} {m nR : ℕ} {tl : HTailF2}
    {A A' : ℕ → ℕ → ℕ → Cb.Gl.E} (h : TieRowsAt X T m nR tl A) (h' : TieRowsAt X T m nR tl A') :
    ∀ j < nR, A (u3Of tl) 0 j = A' (u3Of tl) 0 j :=
  fun j hj => (h.2 j hj).trans (h'.2 j hj).symm

/-- **It can fail**: bent at one entry of the vector below nR. -/
theorem tieRowsAt_bent {X : OnBytes.Model.Verify.Public} {T : Tr} {m nR : ℕ} {tl : HTailF2}
    {A A' : ℕ → ℕ → ℕ → Cb.Gl.E} (h : TieRowsAt X T m nR tl A) {j : ℕ} (hj : j < nR)
    (hne : A' (u3Of tl) 0 j ≠ A (u3Of tl) 0 j) : ¬ TieRowsAt X T m nR tl A' :=
  fun h' => hne (tieRowsAt_reads h' h j hj)

/-- The like at the first equation: bent at one packed cell inside the shape. -/
theorem tieRowsAt_bentM {X : OnBytes.Model.Verify.Public} {T : Tr} {m nR : ℕ} {tl : HTailF2}
    {A A' : ℕ → ℕ → ℕ → Cb.Gl.E} (h : TieRowsAt X T m nR tl A) {ν c i' : ℕ} (hν : ν < tl.NM)
    (hc : c < (Sz.ref.packedShape m ν).2) (hi : i' < (Sz.ref.packedShape m ν).1)
    (hne : A' (tl.gtTree.getD ν 0) i' c ≠ A (tl.gtTree.getD ν 0) i' c) :
    ¬ TieRowsAt X T m nR tl A' :=
  fun h' => hne ((h'.1 ν hν c hc i' hi).trans (h.1 ν hν c hc i' hi).symm)

/-- **It can fail at other tables**: a table laid at tl's tables, held against a record tl₂ whose
own tables read otherwise at some entry below nR. -/
theorem tieRowsAt_other {X : OnBytes.Model.Verify.Public} {T : Tr} {m nR : ℕ} {tl tl₂ : HTailF2}
    {A : ℕ → ℕ → ℕ → Cb.Gl.E} (h : TieRowsAt X T m nR tl A) (hu : u3Of tl₂ = u3Of tl) {j : ℕ}
    (hj : j < nR)
    (hne : OnBytes.Model.Reading.gl.val (First.K8.Honest.readAt (parOfMats tl₂.mats)
        tl₂.funs.toList (cellsAtOf (cellsC X T) (matsOf X m)) j) ≠
      OnBytes.Model.Reading.gl.val (First.K8.Honest.readAt (parOfMats tl.mats) tl.funs.toList
        (cellsAtOf (cellsC X T) (matsOf X m)) j)) : ¬ TieRowsAt X T m nR tl₂ A := by
  intro h₂
  have e₂ := h₂.2 j hj
  rw [hu, h.2 j hj] at e₂
  exact hne e₂.symm

/-- **Neither "false" nor "true"**: without a premise, and without content: the record has no matrix
and no table. -/
theorem tieRowsAt_neither (X : OnBytes.Model.Verify.Public) (T : Tr) (m : ℕ) :
    ∃ tl : HTailF2, (∃ A, TieRowsAt X T m 1 tl A) ∧ ∃ A', ¬ TieRowsAt X T m 1 tl A' := by
  have hG : GtOne ({} : HTailF2) := fun μ hμ => absurd hμ (Nat.not_lt_zero μ)
  have hU : ∀ μ, μ < ({} : HTailF2).NM → ({} : HTailF2).gtTree.getD μ 0 ≠ u3Of {} :=
    fun μ hμ => absurd hμ (Nat.not_lt_zero μ)
  obtain ⟨A, hA⟩ := tieRowsAt_some X T m 1 hG hU
  exact ⟨{}, ⟨A, hA⟩, fun t r c => A t r c + 1, tieRowsAt_bent hA Nat.one_pos
    fun h => one_ne_zero (add_left_cancel (h.trans (add_zero _).symm))⟩

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.TieRowsAt
#print axioms ProofFile.Honest.K1.tieRowsS_iff
#print axioms ProofFile.Honest.K1.tieRowsAt_some
#print axioms ProofFile.Honest.K1.tieRowsAt_reads
#print axioms ProofFile.Honest.K1.tieRowsAt_bent
#print axioms ProofFile.Honest.K1.tieRowsAt_bentM
#print axioms ProofFile.Honest.K1.tieRowsAt_other
#print axioms ProofFile.Honest.K1.tieRowsAt_neither
