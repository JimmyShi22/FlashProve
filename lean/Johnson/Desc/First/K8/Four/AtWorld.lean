-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/Four/AtWorld.lean: THE SMALLNESS TEST: THE EXCHANGE OF THE FIRST FOUR CLAIMS
OF ITS RUN OF EQUATIONS, AT THE BATCHING'S OWN WORLD.

`k3Out_of_equations` (Johnson/Desc/First/K8/Four/Exchange.lean) has a premise on the world:
`DigRows`: the virtual rows that the four claims read are the stated combinations of cells. The
batching's law speaks at one world: `K9L.worldAt ρ L H D`
(Johnson/Desc/First/Batch/Law/Measure.lean): under a slot what is shown less the factor times the
mask row's entry; entry i of a virtual row is THE LEDGER'S OWN WEIGHTS of that row on column i of
its array, at the data D. Here the premise is paid at that world, under four public premises:
  `cellOf L D`: the data's cells by the ledger's numbers of arrays (the link's table of arrays).
  `rowsLaw_worldAt`: **the batching's world has the library's whole law of the rows**
    (`RowsLaw`, OnBytes/Tie/Pv/Lookup/Ends/FoRowsLaw.lean) at its own ledger: by the make.
  `digRows_worldAt`: so, at the ledger in which the smallness test's weights are laid
    (`coefAll tlX g Fc`, OnBytes/Tie/Pv/Lookup/Ends/FoCoef.lean), it has `DigRows`.
  `k3Out_at_world`: **THE EXCHANGE AT THE BATCHING'S WORLD**: from a yes of the whole run, and its
    list's first four claims worth 0 THERE, IN THE BATCHING'S OWN MEASURE (`K9L.claimValue`): the
    lookup's row out `K3Out`, at the reading of places that D gives.
Definitions, statements and proofs.
Limits. Those of Exchange.lean. THE LEDGER IS `coefAll tlX g Fc`: the library's name for the state
behind the routine of the program `verify-on-bytes` that lays the weights: that the run behind the
batching of the text that runs leaves just that ledger is not said here. tlX, the record at which
the weights are laid, has the digits' lookup's numbers of tl (`SameZ`): a premise. `CoefOK`, a test
with code (`coefTest`), and "each piece's rows lie inside its array": premises on the ledger Fc. D
IS A LETTER: that it is what was committed is another law's. SO `K3Out` IS REACHED AT D'S UNKNOWNS:
AN END, NOT YET A LINK: the relation behind the lookup on the digits asks it at the witness's
messages, and no theorem here passes from the one to the other. A SILENT DEFAULT: `cellOf` reads the
link's table of arrays by `getD`: beyond the table it falls to link 0's array of the empty name:
that the numbers of the counts' and the digits' arrays lie inside the table is no premise. jLK IS A
FREE LETTER: at a number that is not the lookup's first slot no rounds stand, and the conclusion
holds idly.

-/
import Johnson.Desc.First.K8.Four.Exchange
import Johnson.Desc.First.Batch.Law.Measure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Four

open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.DgP Cb.Fo Cb.LdLkp Finset
open _root_.Fo _root_.Fo.Eq
open VerifiableInference.OnPublicFiles VerifiableInference.Desc.First.TailClaims

section
variable {K : Type} [Field K] (ρ : Reading K)

/-- The data's cells, by the ledger's numbers of arrays. -/
def cellOf (L : LinkCtx) (D : K9L.Bound K) (t r i : ℕ) : K :=
  D.cell (L.arrayOf.getD t (0, "")).1 (L.arrayOf.getD t (0, "")).2 r i

/-- **The batching's world has the whole law of the rows, at its own ledger.** -/
theorem rowsLaw_worldAt (L : LinkCtx) (H : Fork) (D : K9L.Bound K) :
    RowsLaw ρ H (K9L.worldAt ρ L H D) (cellOf L D) := by
  intro t e i hr
  obtain ⟨ht, he⟩ := hr
  have e1 : (treesFrame H.trees).getD t default = HTree.frame (H.trees.getD t {}) := by
    unfold treesFrame
    simp [Array.getD, ht]
  have e0 : ∀ X : HTree, e < X.rows.size →
      ((HTree.frame X).2.getD e default).1.coef = (X.rows.getD e {}).coef := by
    intro X hX
    unfold HTree.frame
    simp [Array.getD, hX, HRow.frame]
  have e2 : ((HTree.frame (H.trees.getD t {})).2.getD e default).1.coef =
      (rowAt H t e).coef := e0 _ he
  show K9L.entryAt ρ L.arrayOf (treesFrame H.trees) D t e i = _
  unfold K9L.entryAt cellOf
  rw [e1, e2]
  rfl

/-- The unknowns of the lookups' statements, read off the batching's data: a cell, or an entry of
the mask row. -/
def unknownOf (L : LinkCtx) (D : K9L.Bound K) : Ent3 ⊕ ℕ → K :=
  Sum.elim (fun x => cellOf L D x.1 x.2.1 x.2.2) D.mask

/-- So at the ledger in which the smallness test's weights are laid it has `DigRows`. -/
theorem digRows_worldAt (L : LinkCtx) (D : K9L.Bound K) (tl tlX : HTailF2) (hX : SameZ tl tlX)
    (g : Heard) (hP : ∀ q < 2, ∀ p ∈ piecesL tl q, PieceOK tl q (tl.zOf q).call.n p)
    (Fc : Fork) (T : CoefOK tlX Fc)
    (hRw : ∀ a ∈ allPieces tl, a.2.r0 + a.2.Rp ≤ (Fc.trees.getD a.2.tree {}).R) :
    DigRows ρ tl g (K9L.worldAt ρ L (coefAll tlX g Fc) D).entry
      fun x => unknownOf L D (Sum.inl x) :=
  digRows_of_law ρ tl tlX hX g hP Fc T hRw (K9L.worldAt ρ L (coefAll tlX g Fc) D)
    (fun x => unknownOf L D (Sum.inl x)) (rowsLaw_worldAt ρ L (coefAll tlX g Fc) D)

variable {front : ℕ}

/-- **The exchange at the batching's world.** -/
theorem k3Out_at_world (L : LinkCtx) (D : K9L.Bound K) (tl tl' tlX : HTailF2)
    (funs : Array HFun) (F F1 Fc : Fork)
    (cls : List Desc.Claim) (h : equations front tl funs F = .ok (tl', F1, cls))
    (g : Heard) (hg : tl.heard = some g) (hs : tl.f9 = g.shape) (jLK : ℕ)
    (F' : Fork) (h0 : _root_.Fo.Later F' F)
    (hok : FoNums.ok g.shape = true) (hT : TailOK tl) (hF : Sized F)
    (hfull : 2 ^ g.shape.cK = g.shape.NC) (h5 : 5 ≤ g.shape.kT + g.shape.cK)
    (hn : ∀ q < 2, (g.zk.getD q #[]).size = (tl.zOf q).call.n)
    (h63 : ∀ q < 2, (tl.zOf q).call.n ≤ 63)
    (hP : ∀ q < 2, ∀ p ∈ piecesL tl q, PieceOK tl q (tl.zOf q).call.n p)
    (hD : ∀ q < 2, (piecesL tl q).Pairwise fun p p' =>
      p.off + 2 ^ p.b ≤ p'.off ∨ p'.off + 2 ^ p'.b ≤ p.off)
    (hX : SameZ tl tlX) (T : CoefOK tlX Fc)
    (hRw : ∀ a ∈ allPieces tl, a.2.r0 + a.2.Rp ≤ (Fc.trees.getD a.2.tree {}).R)
    (hH : _root_.Fo.Later F1 (coefAll tlX g Fc))
    (clO : List Desc.Claim)
    (hO : ∀ rs : Rounds K, HeardIs ρ g F' (endsOf g.shape 5 jLK rs) →
      clO.map (K9L.claimValue ρ (K9L.worldAt ρ L (coefAll tlX g Fc) D)) =
        (endsOf g.shape 5 jLK rs).rows.map
          (rowRes fun p => zext (unknownOf L D) (NumsEq.placeOf Sum.inr (plV tl Sum.inl) p)))
    (hzO : ∀ k ∈ clO, K9L.claimValue ρ (K9L.worldAt ρ L (coefAll tlX g Fc) D) k = 0)
    (hz : ∀ k ∈ cls.take 4, K9L.claimValue ρ (K9L.worldAt ρ L (coefAll tlX g Fc) D) k = 0) :
    K3Out g.shape 5 jLK
      (fun p => zext (unknownOf L D) (NumsEq.placeOf Sum.inr (plV tl Sum.inl) p))
      (forK K (digL5 K tl Sum.inl Sum.inr jLK Unit) () (zext (unknownOf L D))) ρ g F' :=
  k3Out_of_equations ρ tl tl' funs F F1 cls h g hg hs jLK F' h0 hok hT hF hfull h5 hn h63 hP hD
    Sum.inl Sum.inr (unknownOf L D) (K9L.worldAt ρ L (coefAll tlX g Fc) D).entry
    (coefAll tlX g Fc) hH (digRows_worldAt ρ L D tl tlX hX g hP Fc T hRw) clO hO hzO hz

end

end VerifiableInference.Desc.First.K8.Four

#print axioms VerifiableInference.Desc.First.K8.Four.rowsLaw_worldAt
#print axioms VerifiableInference.Desc.First.K8.Four.digRows_worldAt
#print axioms VerifiableInference.Desc.First.K8.Four.k3Out_at_world
