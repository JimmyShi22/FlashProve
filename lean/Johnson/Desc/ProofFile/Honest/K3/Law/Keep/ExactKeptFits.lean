-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Keep/ExactKeptFits.lean: the kind "lookup" (K3): the sentence
`ExactMember` (Honest/Small/Field.lean: the field exact of `Good` at one member) at every member of
a side that is seated, at a description's first chain, over the row that passes its tables on
(`rowPairsKeep`, Honest/K3/Law/Keep/SideKeep.lean). Two theorems; no definition.

Never to be retold as "the row that passes its tables on is simulated".

What is shown.
  `k3_exact_kept_fits`: `k3_exact_kept` (Honest/K3/Law/Keep/ExactKept.lean) with its premises hrow
    and hSt paid: hrow by `row_of_seatedKeep`, by unfolding; hSt by `rowStated_keep`
    (Honest/K3/Law/Keep/SideKeepStated.lean). At every On' and bud.
  `k3_exact_kept_fast`: the same at the letters `fastFillKeep row wit` (Honest/K3/RowKeepFill.lean),
    where row, each site's table, and wit, each site's reader of the chain's input, stay free: hK is
    paid by `fastKeeps_shaped`.

Hypotheses that remain: the description's return, opened (O); the site; the lot's sub-protocol at
the site's place; `k3Fits` at the chain's flat list, a test with code on public data; the side being
there; hK (in the first alone); the lens: hgs and hsg.

Limits. hrow is paid at this folder's own definition: that a filling of the honest side's frame lays
this side is typed by nobody: "`exact` at the filling" is not had. No instance of the premises
together is exhibited. Of `Good`'s other fields (`fits`, `plays`, `acc`, `fresh`) nothing. At jobs
right or wrong: nothing on what is sent. In `k3_exact_kept_fast` row, each site's table, stays a
free function: wherever these letters are counted as a filling, row is to be a named, closed, public
term (as `Fast.rowOfFace` at the site's face, Honest/K3/JobsFast.lean, is at that file's letters):
that is not laid in here. Nothing on any property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Keep.SideKeepStated
import Johnson.Desc.ProofFile.Honest.K3.Law.Keep.ExactKept
import Johnson.Desc.ProofFile.Honest.K3.Law.Keep.SeatKeepFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E)
open VerifiableInference.Desc (Block Chain FileDescription)
open ProofFile.Honest.Small (ExactMember)

local notation "FS" => VerifiableInference.Desc.First.S

variable {V W X Pb : Type}

/-- Never to be retold as "the row that passes its tables on is simulated". **`ExactMember` at every
member of the seated side, from "fits".** Conditional on the description's return, the site, the
lot's sub-protocol at the site's place, `k3Fits`, hK, the lens and the side. -/
theorem k3_exact_kept_fits (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A₀ : SharedSeat)
    (B₀ : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A₀ B₀) (s : Site)
    (hs : s ∈ lookSites Z) (b : Block FS ProofFile.Cl) (hb : b ∈ (K3Lot.lot Z).blocks Bs.G₀)
    (hbs : b.place = s.at_.place) (hF : k3Fits Z ch.blocksInOrder s = true) (A : FillKeep W)
    (get : X → RowOwn) (set : X → RowOwn → X) (hK : (A.keeps s).Shaped s.at_.face)
    (fs : List (Fall FS)) (σ' : Side FS ProofFile.Cl V W X Pb)
    (h : Side.seated ch.blocksInOrder s.at_.place (rowPairsKeep A get set s) fs = some σ')
    (φ : Face V W Pb) (hgs : ∀ x y, get (set x y) = y) (hsg : ∀ x, set x (get x) = x)
    (chain firstTree : Nat)
    (On' : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) :
    ∀ u' ∈ σ'.members, ExactMember φ σ' chain firstTree On' bud u' :=
  k3_exact_kept φ (A.keeps s) (A.wit s) get set s.at_ hgs hsg hK
    (row_of_seatedKeep A get set s ch.blocksInOrder fs σ' h)
    (rowStated_keep o pol lay KL Fd Z Bs base ch A₀ B₀ O s hs b hb hbs hF A get set hK fs σ' h)
    chain firstTree On' bud

/-- The same at the letters `fastFillKeep row wit`, row and wit free: without hK. That row is a
named, closed, public term is not laid in here: see the head. -/
theorem k3_exact_kept_fast (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A₀ : SharedSeat)
    (B₀ : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A₀ B₀) (s : Site)
    (hs : s ∈ lookSites Z) (b : Block FS ProofFile.Cl) (hb : b ∈ (K3Lot.lot Z).blocks Bs.G₀)
    (hbs : b.place = s.at_.place) (hF : k3Fits Z ch.blocksInOrder s = true) (row : Site → E → Nat → E)
    (wit : Site → W → Ask) (get : X → RowOwn) (set : X → RowOwn → X) (fs : List (Fall FS))
    (σ' : Side FS ProofFile.Cl V W X Pb)
    (h : Side.seated ch.blocksInOrder s.at_.place (rowPairsKeep (fastFillKeep row wit) get set s) fs =
      some σ')
    (φ : Face V W Pb) (hgs : ∀ x y, get (set x y) = y) (hsg : ∀ x, set x (get x) = x)
    (chain firstTree : Nat)
    (On' : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) :
    ∀ u' ∈ σ'.members, ExactMember φ σ' chain firstTree On' bud u' :=
  k3_exact_kept_fits o pol lay KL Fd Z Bs base ch A₀ B₀ O s hs b hb hbs hF (fastFillKeep row wit)
    get set (fastKeeps_shaped theReads (row s) s.at_) fs σ' h φ hgs hsg chain firstTree On' bud

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.k3_exact_kept_fits
#print axioms ProofFile.Honest.K3.Law.k3_exact_kept_fast
