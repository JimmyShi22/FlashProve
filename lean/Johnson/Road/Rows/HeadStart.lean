-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/HeadStart.lean: what stands before the first round of the output head's sub-proof,
said of the committed entries; and that it is OrdPortL in other letters.

Three statements on a tuple m of committed entries. Their bodies name no transcript, no challenge,
no hidden value and no claim; of the record R they read the shape, the layout and the border alone.

HeadRide tOf R yq m Mz: what may lie on both sides of the lookup's block and rides through the
sub-proof's own rounds:
  norm   the 17 identities of the final norm are 0 at every position, in the letters of the chain of
         the norm: normIdn (Cb/Pv/Head/Norm.lean) at the dictionary limbOf, digOf of
         Cb/Pv/Head/NormPlain.lean. It is the joint before the norm's point is drawn.
  sums   the policy's two sums over the counted positions are 0: two claims that need no draw.
  small, lift   the entries' cells are the casts of the integer matrices Mz, all below 2^18 in
         absolute value. Mz is a part of the witness. The smallness test, which is meant to give
         this, runs behind the sub-proof's own rounds, so it rides from the beginning to there.
LookIn R H yq t: in each call of the lookup every value in every column at every position is a row
of the call's table. It is in the letters of OrdPort (Johnson/Road/HeadL5Ord.lean), and is the joint
of no block yet.
LinesAll (Cb/Pv/Head/TwoLines.lean): the two clauses of the acceptance policy on a position's cost
are 0 at every position. They are tested at the lookup's point and have no round of their own.

On both sides of the lookup's block lies HeadRide alone. LookIn and LinesAll stand before it alone:
with either on both sides the block's statement would be empty. None of the three is ever a
hypothesis over all tuples m. small and lift say as much as tOf does: see what is not claimed, and
Johnson/Road/Rows/HeadBase.lean for the form that speaks of what is committed.

Left out on purpose: what the caller claims of the second and the third token sumcheck's sums. It
names the lookup's point, so it does not stand before the first round
(Cb/Pv/Head/HeadRowRide.lean [not in this library]).

head_start: HeadRide, LookIn and LinesAll are OrdPortL (Johnson/Road/HeadL5OrdL.lean) at the
library's sizes, in other letters. The one step is the padding of the features, which is
norm_start_iff of NormPlain.lean. head_start_ord: so they give HeadOrdLB (head_ord_idx,
Johnson/Road/Rows/HeadOrd.lean).

What is not claimed. That the three follow, but for an error, from a verifier's acceptance: that is
the soundness of the chain of blocks, of which the lookup's, the smallness test's and the two lines'
shares are not proved here. That tOf reads the entries as the verifier's layout does: if tOf picks
small integers by choice for whatever is committed, small and lift hold always, and a clause that
the committed symbols are the packing of Mz has to stand beside them. That the
stream of which the product layer's end value is claimed is 0 from the model's width on: limbOf is
so by definition. That lift determines the matrices; small asks every entry of Mz, also outside the
matrices' own rows, columns and list. That the premises can be met together is not shown here. All
is at the full size alone. This file is not imported by the program.


-/
import Johnson.Road.Rows.HeadOrd
import Cb.Pv.Head.NormPlain
import Cb.Pv.Head.TwoLines

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Inst.Model (ppref Instance AcceptancePolicy NormPar)
open Inst.Model.Head (Req)
open OnBytes.Model (Reading)
open OnBytes.Model.Layer (Lay)
open OnBytes.Model.Head (HL)
open OnBytes.Model.Verify (borderOf)
open OnBytes.Road.Hd

section
variable {J : Type} (tOf : (J → Cb.Gl.E) → Inst.Model.Head.Cells Cb.Gl.E)

/-- The joint before the lookup: in each call every value in every column at every position is a
row of the call's table. t: the cells. The letters are those of OrdPort
(Johnson/Road/HeadL5Ord.lean), at the library's sizes. -/
def LookIn (R : Model.Head.Run) (H : ℕ → ℕ → Cb.Gl.E) (yq : Req)
    (t : Inst.Model.Head.Cells Cb.Gl.E) : Prop :=
  ∀ q w fn, (R.L.calls.getD q default).segs.foldlM
      (fun w g => Model.Head.markColumns R w g)
      (Array.replicate (R.L.calls.getD q default).J 0) = some w →
    KeyFn (R.L.calls.getD q default).segs w (R.L.calls.getD q default).J
      (kvOf (Reading.gl.val (invE (Model.Head.pw (R.h.digSh + 15)))) HeadSizes.ref (npOf R.h) t H
        yq)
      (Reading.gl.val (ofF ((R.L.cl.getD q default).tauAt (R.L.cl.getD q default).t0))) fn →
    ∀ j, j < (R.L.calls.getD q default).J → ∀ a, a < HeadSizes.ref.T →
      ∃ u, u < 2 ^ (R.L.cl.getD q default).k ∧
        fn j a = Reading.gl.val (ofF ((R.L.cl.getD q default).tauAt u))

/-- What rides through the head's sub-proof from its first round on. A member of the first joint,
with Mz a part of the witness; never a hypothesis over all tuples. -/
structure HeadRide (R : Model.Head.Run) (yq : Req) (m : J → Cb.Gl.E) (Mz : Mats ℤ) : Prop where
  norm : ∀ k < 17, ∀ X < 2 ^ 10,
    Cb.Pv.Head.normIdn (npOf R.h) (Cb.Pv.Head.limbOf tOf 10 Inst.Model.Head.nD)
      (Cb.Pv.Head.digOf tOf) ⟨10, 13⟩ m k X = 0
  sums : Inst.Model.Head.sB2 (tOf m) yq = 0 ∧ Inst.Model.Head.sB3 (tOf m) yq = 0
  small : ∀ a r c, |Mz a r c| < 2 ^ 18
  lift : tOf m = cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)

variable {tOf}

/-- **HeadRide, LookIn and LinesAll are OrdPortL in other letters.** -/
theorem head_start {R : Model.Head.Run} {H : ℕ → ℕ → Cb.Gl.E} {yq : Req} {m : J → Cb.Gl.E}
    {Mz : Mats ℤ} (I : HeadRide tOf R yq m Mz) (Lk : LookIn R H yq (tOf m))
    (Ln : Cb.Pv.Head.LinesAll (tOf m) yq 10) : OrdPortL R HeadSizes.ref H yq Mz := by
  have hT : HeadSizes.ref.T = 2 ^ 10 := by
    show (1024 : ℕ) = 2 ^ 10
    norm_num
  unfold OrdPortL OrdPort
  rw [← I.lift]
  exact ⟨⟨I.small, Lk,
      fun a ha k hk => (Cb.Pv.Head.norm_start_iff tOf (npOf R.h) m).1 I.norm a ha k hk⟩,
    fun a ha => ⟨Ln 0 a (hT ▸ ha), Ln 1 a (hT ▸ ha)⟩, I.sums.1, I.sums.2⟩

/-- **So they give the statement on the verifier's arrays.** -/
theorem head_start_ord {R : Model.Head.Run} {hH : Model.Head.Shape} {L : HL} {y : Lay}
    {nf : NormPar} (hh : R.h = hH) (hL : R.L = L) (hb : R.b = borderOf y)
    (hnf : npOf hH = nf) (hLy : Model.Head.layout hH tauFCw = .ok L) (hF : FullH hH)
    (h24 : hH.famF = 24) (hs : hH.digSh = 8) (hTs : hH.tabS = 4) (pol : AcceptancePolicy) (i : Cm.Idx)
    (x : Instance ppref) (h3 : Inst.Model.Head3 x) {m : J → Cb.Gl.E} {Mz : Mats ℤ}
    (I : HeadRide tOf R (Req.of pol x) m Mz)
    (Lk : LookIn R (fun j v => ((i.index.val.H j v : ℤ) : Cb.Gl.E)) (Req.of pol x) (tOf m))
    (Ln : Cb.Pv.Head.LinesAll (tOf m) (Req.of pol x) 10) :
    HeadOrdLB hH L y nf pol i.mat x Mz :=
  head_ord_idx hh hL hb hnf hLy hF h24 hs hTs pol i x h3 (head_start I Lk Ln)

end

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.head_start
#print axioms OnBytes.Road.Rows.head_start_ord
