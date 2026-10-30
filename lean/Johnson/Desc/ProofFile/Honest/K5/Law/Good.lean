-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Good.lean: Good (Honest/Side.lean) AT THE ROW OF AN ATTENTION
SEGMENT's OWN ROUNDS (kind K5: the label of that sub-protocol in the description), AS ONE TERM, OVER
THREE SENTENCES ON THE FRAME's OWN PARTS THAT ARE PREMISES HERE. Two statements with their proofs.

  k5_good        CONDITIONAL: Good at K5's side, at every pre, face, book, order of places, chain's
                 number and first tree; at the letters A := B := False, On := True, bud := k5Bud
  k5_goodAt      the same at the row with its letters (k5Lettered, Honest/K5/Law/Bud.lean)

WHAT IS SHOWN HERE, AND WHAT IS NOT. Of Good's five fields: fits is shown (k5_fits,
Honest/K5/Law/RowIs.lean). plays AND acc ARE MET FOR NOTHING, AT A := False: nothing is said here on
the playing or on the verifier's yes. fresh is shown, under hk, AND IS EMPTY: the row has no coin of
its own (by the frame's own two lemmas: fresh_u, Honest/K5/Law/GoodForms.lean). exact, AN EQUATION
OF TWO DISTRIBUTIONS AT EACH MEMBER, IS NOT SHOWN HERE: each member of the side is written out
(member_at), what its rounds state and draw is shown (stretch_like), and THE EQUATION ITSELF IS
TAKEN FROM A PREMISE: MSForm, LoneForm or QuietForm (GoodForms.lean), WHICH ARE NOT SHOWN IN THIS
FILE (Honest/K5/Law/GoodPaid.lean has each from a theorem on that part). The three premises lack the
field's hypothesis on the opened columns (m.opened = front.opened (readsBefore pre front)): they ask
the same equation at more states than the field does, so as premises they are the stronger. pre is
not read.

The other premises. K5Block: four facts on the description's member at the place · the side's row
is K5's · hx: the verifier's test on a call's shape says yes at every call of the row: a test with
code on public numbers, which follows from the verifier's own test on the plan (shapes_plan,
Honest/K5/Law/RowIs.lean) · hk: no entry of the book names a part of this place as owner.

Every part of K5's row has takes = ⟨0, 0⟩; that no entry of the book names one as owner is the
premise hk. exact speaks, AT EACH MEMBER BY ITSELF, of the runs that it spends AS UNIFORM AND
INDEPENDENT of each other and of all that is fixed in the equation. That they are so in a run is not
stated here: it needs AT THE LEAST fresh at the part that owns them, the book's lending of just
these runs, and that no two of them share a coin. Of what stands in front the row's jobs read the
challenges alone.

Limits. No property is claimed. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Bud

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.Part.MaskedSum (shapeOk)
open VerifiableInference.Desc.First.Att
open H2K5.Honest (shapes K5In)

variable {W₀ Rc Xi Tr X Pb S Cl : Type}
  {σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {cells : Tr → Cells} {Z : Seat5}
  {p : P.Par}

/-- **Good at K5's row, as one term, AT A := B := THE EMPTY SENTENCE (False): SO ITS FIELDS plays
AND acc ARE MET FOR NOTHING: IT SAYS fits, exact AND AN EMPTY fresh, AND NOTHING ON THE PLAYING OR
ON THE VERIFIER's YES.** CONDITIONAL: see the head: exact comes out of the three premises hMS,
hLone, hQuiet, which are not shown in this file. pre is tied to no description; at each pre this
says of exact no more than its premises hMS, hLone and hQuiet give. -/
theorem k5_good (hMS : MSForm k5Bud) (hLone : LoneForm k5Bud) (hQuiet : QuietForm k5Bud)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (φ : Face (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Pb) (Bk : ProverCoinCounts) (ord : List Place)
    (chain firstTree : Nat) (hB : K5Block σ.block Z p) (hr : σ.row = k5Pairs cells Z)
    (hx : ((shapes Z.P.x).all fun s =>
      match s with
      | .sum k => shapeOk k
      | .one _ => true) = true)
    (hk : ∀ e ∈ Bk.ahead, e.owner.place ≠ Z.place) :
    Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False)
      (fun _ _ _ _ => True) k5Bud := by
  have hown : ∀ j, OwnsNothing Bk ⟨σ.block.place, j⟩ := fun j e he h =>
    hk e he (by rw [h]; exact hB.place)
  have hex : ∀ u ∈ σ.members, ExactU φ σ chain firstTree (fun _ _ _ _ => True) k5Bud u := by
    intro u hu
    obtain ⟨j, s, hq, rfl⟩ := member_at hr hu
    have hS := stretch_like hB hq
    match s, hq, hS with
    | .sum k, hq, hS =>
      have h := hMS S Cl _ _ X Pb Unit K5In φ σ chain firstTree
        (fun _ => ()) (fun t => inOf Z.P.S Z.link (cells t.trace)) (nameOf Z.place j "sum")
        (nameOf Z.place j "ends")
        (jobOf k (fun w fr => (jobs Z.P).alone j w (chalOf Z fr.heard)) fun w fr =>
          (jobs Z.P).sum j w (chalOf Z fr.heard)) j (stretchOf σ.block Z j) (shapes_ok hx hq)
        hS.1 hS.2
      rw [hB.place] at h
      exact h
    | .one 0, _, hS =>
      have h := hQuiet S Cl _ _ X Pb Unit K5In φ σ chain firstTree
        (fun _ => ()) (fun t => inOf Z.P.S Z.link (cells t.trace)) j
        (stretchOf σ.block Z j) hS
      rw [hB.place] at h
      exact h
    | .one (n + 1), _, hS =>
      have h := hLone S Cl _ _ X Pb Unit K5In φ σ chain firstTree
        (fun _ => ()) (fun t => inOf Z.P.S Z.link (cells t.trace))
        (nameOf Z.place j "scalars") (n + 1)
        (fun w fr => (jobs Z.P).alone j w (chalOf Z fr.heard)) j (stretchOf σ.block Z j) hS
      rw [hB.place] at h
      exact h
  exact
    { fits := k5_fits hB hr
      plays := fun _ _ _ _ _ h => h.elim
      acc := fun _ _ _ _ _ h => h.elim
      exact := fun u hu ca m front ds asks hOn hs _ => hex u hu ca m front ds asks hOn hs
      fresh := fun u _ => fresh_u φ σ Bk ord k5Bud u (hown u.number) }

/-- **The same at the row with its letters** (Lettered.goodAt, Honest/Rule.lean): at every list of
members of a description, every list of falls and every list of earlier chains' declared rounds.
Good's pre is made there of earlier, bs and the place (preOf, Honest/Rule.lean); it is not read.
CONDITIONAL: as k5_good; hB: whichever member of the list stands at the place meets K5Block. -/
theorem k5_goodAt (hMS : MSForm k5Bud) (hLone : LoneForm k5Bud) (hQuiet : QuietForm k5Bud)
    (earlier : List (Nat × Nat × List Fmt.DeclaredRound))
    (φ : Face (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Pb) (Bk : ProverCoinCounts) (bs : List (Block S Cl))
    (ord : List Place) (chain firstTree : Nat) (fs : List (Fall S))
    (hB : ∀ τ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb,
      (k5Lettered Bk S Cl cells Z).side bs fs = some τ → K5Block τ.block Z p)
    (hx : ((shapes Z.P.x).all fun s =>
      match s with
      | .sum k => shapeOk k
      | .one _ => true) = true)
    (hk : ∀ e ∈ Bk.ahead, e.owner.place ≠ Z.place) :
    (k5Lettered (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) (Pb := Pb) Bk S Cl cells Z).goodAt earlier
      φ bs ord chain firstTree fs :=
  fun τ hτ => k5_good hMS hLone hQuiet _ φ Bk ord chain firstTree (hB τ hτ) (side_row hτ) hx hk

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5_good
#print axioms ProofFile.Honest.K5.k5_goodAt
