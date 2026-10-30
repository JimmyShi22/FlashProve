-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/TiesOn.lean: THE TIES OF Law/Rule/Ties.lean WITH THE
BORDER's SENTENCE A LETTER. There each tie is asked wherever `Thr T b` holds. Here "At" stands in
its stead: a sentence on a run's coins, the verifier's state, where the prover's run stands, and
the tables at hand. So a tie can be asked from MORE than the thread: from the thread and what is
said (`ThrS T Said b`, Honest/Thread/Said.lean), or at reached states alone: A WEAKER DEBT.
DEFINITIONS: PREMISES' FORMS; and small lemmas.

  1  `MaskTieOn`, `MaskTieBookOn`, `CellsTieOn`   the three forms
  2  `maskTie_on`, `maskTieBook_on`, `cellsTie_on`   at At := `Thr T b` they are
     Law/Rule/Ties.lean's, by unfolding
  3  `MaskTieOn.mono`, `MaskTieBookOn.mono`, `CellsTieOn.mono`   a tie from a weaker sentence
     gives the tie from a stronger one: so the elder gives every twin
  4  `maskTieOn_of_book`   as `maskTie_of_book`

Limits. As Law/Rule/Ties.lean's. With At empty each holds for nothing. This file proves nothing
about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.Ties

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open OnBytes (E zeroE)
open VerifiableInference.Desc (Place)

variable {Bk : ProverCoinCounts} {S Cl V W X Pb : Type}

def MaskTieOn (T : Thread Bk S Cl V W X Pb) (At : Coins Bk → S → Mid W X → Env → Prop) (p : Place)
    (ps : List (Part V W X)) {A G : Type} (opn : S → Option A)
    (entry : A → S → W → T.Wt → Nat → G) (val : E → G) (coins : RowCoins ps → List E)
    (J : Nat → Nat → Prop) : Prop :=
  ∀ k s m En, At k s m En → ∀ a c, opn s = some a →
    lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) p ps 0 = .ok c →
    ∀ ds j, J (coins c).length j →
      entry a s m.st.input (T.wit k m.st.input (m.st.heard ++ ds)) j =
        val ((coins c).getD j zeroE)

def MaskTieBookOn (T : Thread Bk S Cl V W X Pb) (At : Coins Bk → S → Mid W X → Env → Prop)
    (p : Place) (n : Nat) {A G : Type} (opn : S → Option A)
    (entry : A → S → W → T.Wt → Nat → G) (val : E → G) (J : Nat → Nat → Prop) : Prop :=
  ∀ k s m En, At k s m En → ∀ a, opn s = some a → ∀ ds j,
    J (rowSpent Bk (k.look T.chain) p n 0).length j →
      entry a s m.st.input (T.wit k m.st.input (m.st.heard ++ ds)) j =
        val ((rowSpent Bk (k.look T.chain) p n 0).getD j zeroE)

def CellsTieOn (T : Thread Bk S Cl V W X Pb) (At : Coins Bk → S → Mid W X → Env → Prop)
    {A G : Type} (opn : S → Option A) (mine : W → Nat → Nat → Nat → G)
    (seen : A → S → W → T.Wt → Nat → Nat → Nat → G) (In : Nat → Nat → Nat → Prop) : Prop :=
  ∀ k s m En, At k s m En → ∀ a, opn s = some a → ∀ ds i r c, In i r c →
    mine m.st.input i r c = seen a s m.st.input (T.wit k m.st.input (m.st.heard ++ ds)) i r c

section
variable {T : Thread Bk S Cl V W X Pb} {At At' : Coins Bk → S → Mid W X → Env → Prop} {b : Nat}
  {p : Place} {ps : List (Part V W X)} {n : Nat} {A G : Type} {opn : S → Option A}
  {entry : A → S → W → T.Wt → Nat → G} {val : E → G} {coins : RowCoins ps → List E}
  {J : Nat → Nat → Prop} {mine : W → Nat → Nat → Nat → G}
  {seen : A → S → W → T.Wt → Nat → Nat → Nat → G} {In : Nat → Nat → Nat → Prop}

theorem maskTie_on :
    MaskTie T b p ps opn entry val coins J ↔ MaskTieOn T (Thr T b) p ps opn entry val coins J :=
  Iff.rfl

theorem maskTieBook_on :
    MaskTieBook T b p n opn entry val J ↔ MaskTieBookOn T (Thr T b) p n opn entry val J := Iff.rfl

theorem cellsTie_on : CellsTie T b opn mine seen In ↔ CellsTieOn T (Thr T b) opn mine seen In :=
  Iff.rfl

theorem MaskTieOn.mono (hA : ∀ k s m En, At' k s m En → At k s m En)
    (h : MaskTieOn T At p ps opn entry val coins J) :
    MaskTieOn T At' p ps opn entry val coins J :=
  fun k s m En hT => h k s m En (hA k s m En hT)

theorem MaskTieBookOn.mono (hA : ∀ k s m En, At' k s m En → At k s m En)
    (h : MaskTieBookOn T At p n opn entry val J) : MaskTieBookOn T At' p n opn entry val J :=
  fun k s m En hT => h k s m En (hA k s m En hT)

theorem CellsTieOn.mono (hA : ∀ k s m En, At' k s m En → At k s m En)
    (h : CellsTieOn T At opn mine seen In) : CellsTieOn T At' opn mine seen In :=
  fun k s m En hT => h k s m En (hA k s m En hT)

theorem maskTieOn_of_book (h : MaskTieBookOn T At p ps.length opn entry val J) :
    MaskTieOn T At p ps opn entry val (spentOf ps) J := by
  intro k s m En hT a c ha hc ds j hj
  rw [spentOf_row Bk _ _ p ps 0 c hc] at hj ⊢
  exact h k s m En hT a ha ds j hj

end

end ProofFile.Honest

#print axioms ProofFile.Honest.maskTie_on
#print axioms ProofFile.Honest.maskTieBook_on
#print axioms ProofFile.Honest.cellsTie_on
#print axioms ProofFile.Honest.MaskTieOn.mono
#print axioms ProofFile.Honest.MaskTieBookOn.mono
#print axioms ProofFile.Honest.CellsTieOn.mono
#print axioms ProofFile.Honest.maskTieOn_of_book
