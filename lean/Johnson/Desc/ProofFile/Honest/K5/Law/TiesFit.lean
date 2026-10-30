-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/TiesFit.lean: the ties of an attention segment's own rounds
(kind K5): K5Script's fields maskTie and cellsTie, and PlanesTie (Honest/K5/Law/Script.lean): HELD
AGAINST THE COMMON FORMS MaskTie AND CellsTie (Honest/Law/Rule/Ties.lean). FORMS AGAINST FORMS: NO
TIE IS SHOWN HERE. Definitions of letters, and statements with their proofs.

  runs_same, spent_same   the two texts of "the coins that a row's parts spend" (this kind's, in
                 Script.lean; the frame's, in Honest/Law/Rule/Spent.lean) yield one list. By
                 induction: at a variable row the equation does not hold by unfolding alone
  entry5, mine5, seen5, in5, inPlanes5   the common forms' letters at K5
  mask_iff       the field maskTie's text, at this kind's own function for the coins, IS MaskTie
  mask_frame     K5Script gives MaskTie at the frame's function for the coins
  mask_of_book   what is asked of the sender of the mask row (MaskTieBook) gives that
  cells_iff      the field cellsTie's text against CellsTie: three premises against one conjunction
  planes_iff     PlanesTie against CellsTie at the matrix of the lookup's planes
  script_of      MaskTie, CellsTie and the third field's text make K5Script

No statement has a premise but the forms that it names. One of the letters, seen5, is marked
noncomputable: it is made of the library's matsOfData, which is so; no code is wanted of it.

Limits. Nothing shows that any of these forms can be met. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Script
import Johnson.Desc.ProofFile.Honest.Law.Rule.Ties

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open OnBytes.Model (Reading)
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Block Claim First.S)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.Sound (MsgQ dataQ matsOfData)
open VerifiableInference.Desc.First.Att.P (K3Pts)

/-! ## 1 One list -/

/-- The two texts of the runs' coins yield one list. -/
theorem runs_same : ∀ (ds : List (String × Due)) (c : CsAll ds),
    K5.runsE ds c = ProofFile.Honest.runsE ds c
  | [], _ => rfl
  | d :: ds, c => by
    show coinsE _ ++ K5.runsE ds _ = coinsE _ ++ ProofFile.Honest.runsE ds _
    rw [runs_same ds]

/-- The two texts of the coins that a row's parts spend yield one list. -/
theorem spent_same {V W X : Type} : ∀ (ps : List (Part V W X)) (c : RowCoins ps),
    K5.spentOf ps c = ProofFile.Honest.spentOf ps c
  | [], _ => rfl
  | p :: ps, c => by
    show K5.runsE _ _ ++ K5.spentOf ps _ = ProofFile.Honest.runsE _ _ ++ ProofFile.Honest.spentOf ps _
    rw [runs_same, spent_same ps]

/-! ## 2 The letters at K5 -/

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}

/-- The reader of the member's mask entry number j off the witness. -/
def entry5 (own : List (Nat × Nat)) (rdOf : T.Wt → Nat × Nat → MsgQ) :
    VerifiableInference.Desc.K9.Part → First.S → Local W₀ Rc Xi Tr → T.Wt → Nat → GE :=
  fun a _ _ v j => (dataQ own a (rdOf v)).mask (a.F.next + j)

/-- The honest side's cell, of the input. -/
def mine5 (cells : Tr → Cells) (Z : Seat5) :
    Local W₀ Rc Xi Tr → Nat → Nat → Nat → GE :=
  fun w i r c => Reading.gl.val (cellAt Z.P.S Z.link (cells w.trace) i r c)

/-- The cell that the item's sentence reads off the witness. -/
noncomputable def seen5 (A : OnBytes.Attention.Plan) (own : List (Nat × Nat))
    (rdOf : T.Wt → Nat × Nat → MsgQ) :
    VerifiableInference.Desc.K9.Part → First.S → Local W₀ Rc Xi Tr → T.Wt → Nat → Nat → Nat → GE :=
  fun a s _ v => matsOfData A.seam.tl ((s.link?.map (·.arrayOf)).getD #[]) (dataQ own a (rdOf v))

/-- Inside every matrix of the list but the lookup's planes'. -/
def in5 (Z : Seat5) (A : OnBytes.Attention.Plan) : Nat → Nat → Nat → Prop :=
  fun i r c => i ≠ Z.P.S.cf.NAs + 2 ∧ r < (A.seam.tl.mats.getD i {}).m ∧
    c < (A.seam.tl.mats.getD i {}).k

/-- Inside the matrix of the lookup's planes. -/
def inPlanes5 (Z : Seat5) (A : OnBytes.Attention.Plan) : Nat → Nat → Nat → Prop :=
  fun i r c => i = Z.P.S.cf.NAs + 2 ∧ r < (A.seam.tl.mats.getD i {}).m ∧
    c < (A.seam.tl.mats.getD i {}).k

/-! ## 3 The forms against each other -/

variable {b : Nat} {cells : Tr → Cells} {Z : Seat5} {A : OnBytes.Attention.Plan}
  {blk : Block First.S Claim} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}

/-- **The field maskTie's text IS MaskTie**, the letter for the coins laid as this kind's own
function: by unfolding alone. -/
theorem mask_iff :
    (∀ k s m E, Thr T b k s m E → ∀ a c, segAt? s = some a →
      lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) Z.place
        (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).parts 0 = .ok c →
      ∀ ds j, j < (K5.spentOf _ c).length →
        (dataQ own a (rdOf (T.wit k m.st.input (m.st.heard ++ ds)))).mask (a.F.next + j) =
          Reading.gl.val ((K5.spentOf _ c).getD j zeroE)) ↔
      MaskTie T b Z.place (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).parts segAt?
        (entry5 own rdOf) Reading.gl.val (K5.spentOf _) (fun n j => j < n) := Iff.rfl

/-- The two functions for the coins, as functions. -/
theorem spent_fun (cells : Tr → Cells) (Z : Seat5) :
    K5.spentOf (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).parts =
      ProofFile.Honest.spentOf _ := funext (spent_same _)

/-- **K5Script gives MaskTie at the frame's function for the coins.** -/
theorem mask_frame (H : K5Script T b cells Z A blk own rdOf) :
    MaskTie T b Z.place (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).parts segAt?
      (entry5 own rdOf) Reading.gl.val (ProofFile.Honest.spentOf _) (fun n j => j < n) := by
  rw [← spent_fun]
  exact H.maskTie

/-- **What is asked of the sender of the mask row gives MaskTie.** By the frame's own lemma. -/
theorem mask_of_book (h : MaskTieBook T b Z.place
      (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).parts.length segAt?
      (entry5 own rdOf) Reading.gl.val (fun n j => j < n)) :
    MaskTie T b Z.place (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).parts segAt?
      (entry5 own rdOf) Reading.gl.val (ProofFile.Honest.spentOf _) (fun n j => j < n) :=
  maskTie_of_book h

/-- **The field cellsTie's text against CellsTie.** -/
theorem cells_iff :
    (∀ k s m E, Thr T b k s m E → ∀ a, segAt? s = some a → ∀ ds i r c,
      i ≠ Z.P.S.cf.NAs + 2 →
      r < (A.seam.tl.mats.getD i {}).m → c < (A.seam.tl.mats.getD i {}).k →
        Reading.gl.val (cellAt Z.P.S Z.link (cells m.st.input.trace) i r c) =
          matsOfData A.seam.tl ((s.link?.map (·.arrayOf)).getD #[])
            (dataQ own a (rdOf (T.wit k m.st.input (m.st.heard ++ ds)))) i r c) ↔
      CellsTie T b segAt? (mine5 cells Z) (seen5 A own rdOf) (in5 Z A) :=
  ⟨fun H k s m E hT a ha ds i r c h => H k s m E hT a ha ds i r c h.1 h.2.1 h.2.2,
    fun H k s m E hT a ha ds i r c h1 h2 h3 => H k s m E hT a ha ds i r c ⟨h1, h2, h3⟩⟩

/-- **PlanesTie against CellsTie at the matrix of the lookup's planes.** -/
theorem planes_iff : PlanesTie T b cells Z A own rdOf ↔
    CellsTie T b segAt? (mine5 cells Z) (seen5 A own rdOf) (inPlanes5 Z A) :=
  ⟨fun H k s m E hT a ha ds i r c h => by
      obtain ⟨rfl, h2, h3⟩ := h
      exact H k s m E hT a ha ds r c h2 h3,
    fun H k s m E hT a ha ds r c h2 h3 => H k s m E hT a ha ds _ r c ⟨rfl, h2, h3⟩⟩

/-- **MaskTie, CellsTie and the third field's text make K5Script.** hK: the field keyTie's text. -/
theorem script_of (hM : MaskTie T b Z.place
      (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).parts segAt?
      (entry5 own rdOf) Reading.gl.val (ProofFile.Honest.spentOf _) (fun n j => j < n))
    (hC : CellsTie T b segAt? (mine5 cells Z) (seen5 A own rdOf) (in5 Z A))
    (hK : ∀ k s m E, Thr T b k s m E → ∀ att, s.here = .att att →
      ∃ g, att.g = some g ∧ K3Pts A.fs g.zx g.zy g.zk (OnBytes.Slice.readV (g.zx ++ g.zy)) ∧
        ∀ ds n, drawsFit blk.rounds ds = true → Z.keyAt (m.st.heard ++ ds.take n) = g.zk) :
    K5Script T b cells Z A blk own rdOf := by
  rw [← spent_fun] at hM
  exact ⟨hM, cells_iff.2 hC, hK⟩

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.runs_same
#print axioms ProofFile.Honest.K5.spent_same
#print axioms ProofFile.Honest.K5.mask_iff
#print axioms ProofFile.Honest.K5.spent_fun
#print axioms ProofFile.Honest.K5.mask_frame
#print axioms ProofFile.Honest.K5.mask_of_book
#print axioms ProofFile.Honest.K5.cells_iff
#print axioms ProofFile.Honest.K5.planes_iff
#print axioms ProofFile.Honest.K5.script_of
