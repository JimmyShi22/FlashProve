-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/Statement.lean: a law of the closing of a link (kind K10): THE TARGET
THAT IT HANDS ON IS THE PROVED BLOCK's. One definition of type Prop. Proved in Proof.lean; shown not
to be empty in NotEmpty.lean, both beside this file.

The library's proved block for these rounds is `kBatFoldRide` (Johnson/Top/H/BatFold.lean: "BAT",
"FOLD epsilon", k times "FOLD round", the fold's mask sent earlier): knowledge sound at every caller
that meets `BatFoldOK`. The library has this law for runs of two routines of
the program `verify-on-bytes` (`batFold_tied_rows`, Johnson/Top/H/BatTied.lean). `Law` is that
statement with a yes of `closing P S g mask rs` (Johnson/Desc/First/Close/Closing.lean) in the
place of the two runs, rs being the reading `ρ.V τ` of a written stretch τ.

What it says. c: a caller of the proved block, over the programs' extension field. ρ: the six
readings of Johnson/Top/H/BatFoldPlace.lean (a written round as a round of a view; an element; a
seed; a challenge). At every written stretch τ, every plan's numbers P with the caller's k, every
statement S, group g and mask: if `closing` says yes on the reading of τ, then
  1. τ has an image among the typed transcripts;
  2. the proved block's verifier puts out a statement a' on it;
  3. the target of a' is the reading of the target of the claim that `closing` hands on.
CLAUSES 1 AND 2 COST NOTHING: 1 follows from the premise `Rd.DefAt` alone, and under the premise on
the power that is left out the proved block's verifier never refuses (`batFoldRide_total`). THE
LAW's WHOLE CONTENT IS THE ONE EQUATION 3.
The premises are the library's at this place: the readings are the field's (`Rd.Scal`); the typed
round's step is the program's (`StepOK`); the power that is left out can be completed; the readings
are defined at what was drawn (`Rd.DefAt`); the typed rows can be laid in the order of `runRows`
with the powers of the drawn element (`Ordered`); the rows fit the statement (`RowFits`).

Limits. (a) THE TARGET ALONE IS TIED, on both sides: nothing on the point, the coefficients, the
forms or the words; `Ordered` reads the rows' targets alone. What `closing` hands on beside the
target stands, in the field, in HandsOn.lean; its tie to a typed statement is not made anywhere.
(b) `StepOK` is shown at two scalars a round with the linear coefficient left out; `Ordered` and
`RowFits` are shown of no rows that a verifier makes. (c) The law asks neither c ∈ L nor
`BatFoldOK`, under which alone the block is knowledge sound; L is not read. (d) One direction; a
function that always refuses would meet the law too. (e) It is about `closing`, not `closeFrame`:
the two tests of the frame have no typed counterpart here. (f) Words are read as residues; that each
is below the prime is asked elsewhere. (g) THE SIX READINGS ARE LETTERS: any functions from a
message and a challenge of any three rounds to a round of a view. Nothing ties them to the views
that a file's decision is handed; readings that ignore the challenge meet every premise. So the law
speaks at readings of written stretches, not at all views. (h) S' is tied to nothing. (i) The
premise P.k = (Yc c).k is spent by no step of the proof: the type of τ fixes the number of rounds.
Read by one other team: accepted as a statement; not accepted as all that is owed for this kind.
-/
import Johnson.Top.H.BatTied
import Johnson.Desc.First.Close.Closing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Tie.Pv.Fold Iop KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv
open OnBytes.PscRun (drawnOf)

/-- **The law of K10**, at a list of callers L, a caller c, three written rounds and six
readings. -/
def Law (L : List (BatFoldCaller GE)) (c : BatFoldCaller GE) (rB rE rR : Round)
    (ρ : Rd c rB rE rR) : Prop :=
  ρ.Scal → StepOK (Yc c).val (Yc c).n c.fx (rd2 c) →
  c.fx.2 * (HVar.plain GE (Yc c).n).mon c.fx.1 = 1 →
  ∀ (P : Plan) (S S' : Statement) (g : Nat) (mask : Option Nat) (out : SingleRows)
    (a : ((kBatFoldRide L).src c).X × ((kBatFoldRide L).src c).E.Str)
    (τ : Tr (rB :: rE :: List.replicate (Yc c).k rR)),
    P.k = (Yc c).k → ρ.DefAt (ρ.V τ) →
    closing P S g mask (ρ.V τ) = .ok (out, S') →
    (∀ G e z, S.groups[g]? = some G → (ρ.viewB τ.1 τ.2.1).drawn.elems = [e.triple] →
      ρ.rdZ (drawnOf (ρ.viewB τ.1 τ.2.1)) = some z →
      Ordered c a.1 z e ((runRows S G).toList.map fun w => readE w.target)) →
    (∀ G, S.groups[g]? = some G → ∀ w ∈ (runRows S G).toList, RowFits (begun S g G) w) →
    ∃ τ' a', ρ.carS.tr τ = some τ' ∧ ((kBatFoldRide L).block c).R.red.out a τ' = some a' ∧
      a'.1.1.1 = readE out.target

end VerifiableInference.Desc.First.Close
