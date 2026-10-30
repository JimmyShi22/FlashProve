-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/WtFwdReads.lean: THE SENTENCE "weights" OF THE OUTPUT HEAD's
SEGMENT GOES FORWARD OVER AN ACCEPT OF A SEGMENT's READS, UNDER FOUR PREMISES. One statement and its
proof, over files of the library alone. No definition.

  wt_fwd_reads   the library's hwtR_of (Johnson/Desc/K1/Law/WtBackAtReads.lean) with its last arrow
                 turned. Its four premises (hidle, hmono, hheard, hquiet) stand to the letter. Its
                 antecedent KeptBelow, and with it the letters c aN R₁ R₂ R₃, are left out: its
                 proof does not spend them.

WHY IT GOES. The library's law on the head's claim on the weights over that step is an "if and only
if" (weightAt_kept, Johnson/Desc/Kinds/Law/WeightAtSame.lean); hmono is asked at every two states.

IN A FILE OF ITS OWN: seatAt is here Kinds.Head.seatAt; in
Johnson/Desc/ProofFile/Honest/K1/Law/FormsFwd.lean it is K9.seatAt.

N and Mg are letters: the promise InAt is asked at whatever meaning the caller has.

Limits. The four premises are proved here at no letters. At every link but 24 the end is hidle's.
That the sub-protocol accepts anywhere is not said. Nothing on soundness, on completeness or on any
other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K1.Law.WtBackAtReads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Model VerifiableInference.Desc
open VerifiableInference.Desc.Sound (CellsQ MsgT linksFull)
open VerifiableInference.Desc.First (S Meaning Numbers flatPlacesOf)
open VerifiableInference.Desc.Kinds.Head (seatAt)
open VerifiableInference.Desc.Kinds.Head.Law (WeightAt weightAt_kept keptW_reads_laid readsOf)
open VerifiableInference.Desc.K8 (ReadsQuiet.head)
open VerifiableInference.Desc.K1 (InAt YesOf blkL noL hhead_342)
open IM (k1Reads k1Quiet)

/-- **"weights" goes forward over the reads' accept**, under hidle, hmono, hheard and hquiet, at l <
25, from the promise InAt in front. wt: a letter: nothing here ties it to the library's sentence. -/
theorem wt_fwd_reads {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {Tok : Type} {rows cols : ℕ} (N : Numbers)
    (Mg : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))
    (wt : ℕ → ProofFile.InstPub × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop)
    (Wp : OnBytes.Model.Verify.Public) (hidle : ∀ l, l ≠ 24 → ∀ a y w, wt l a y w)
    (hmono : ∀ (a a' : ProofFile.InstPub × S) y y' w,
      (∀ cc mm, WeightAt Wp a'.2 cc mm → WeightAt Wp a.2 cc mm) → wt 24 a' y' w → wt 24 a y w)
    (hheard : ∀ x y, InAt N Mg linksFull (flatPlacesOf linksFull true) (noL 24 false) x y →
      ∃ H, (seatAt Wp.hS (readsOf Wp)).heard x.2 = some H)
    (hquiet : ∀ X, Bs.G₀.built[24]? = some X → ∃ P, k1Quiet Bs.G₀ 24 X = ReadsQuiet.head P) :
    ∀ l, l < 25 → ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ (x x' : ProofFile.InstPub × S) y y' w,
      YesOf (blkL Z Bs.G₀ l false X arrs) x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l false) x y →
      wt l x y w → wt l x' y' w := by
  intro l _ X arrs hX x x' y y' w hy hIn h0
  by_cases hl : l = 24
  · subst hl
    obtain ⟨o, ho⟩ := hhead_342 N Mg x y hIn
    obtain ⟨_, rs, gs, _, hd⟩ := hy
    obtain ⟨P, hP⟩ := hquiet X hX
    unfold blkL k1Reads at hd
    dsimp only at hd
    rw [hP] at hd
    exact hmono x' x y' y w
      (fun cc mm => (weightAt_kept Wp (keptW_reads_laid ho hd) (hheard x y hIn) cc mm).2) h0
  · exact hidle l hl x' y' w

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.wt_fwd_reads
