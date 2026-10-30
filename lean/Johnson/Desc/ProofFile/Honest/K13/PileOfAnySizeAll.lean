-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/PileOfAnySizeAll.lean: WHAT HOLDS OF THE PILE's FILLER AT ANY
NUMBER OF SEGMENTS (PileOfAnySize.lean of this folder) AT EVERY SIZE. Seven statements with their
proofs; no definition. Six have no hypothesis on the public part; the seventh, `pileOfAnySize_none`,
starts from "`onlineFirstChainAt` rejects it": that any public part is rejected is shown nowhere: it may
speak of nothing.

Why. A filling that lays `k13LotOnce` into its list of lots needs of it what is needed of every lot
there: of which kind its halves' places are, and what its own list holds at the kind's place. And
the passage from one text of the claims to another needs that the filler reads a text at the sites'
segments alone.
Main names:
  `k13LotOnce_eq`: **the lot over a filler held as a field is `k13Lot` at that filler**: by
    definition. `k13LotOnce_at_any`: **at the closed terms: over `pileBoxAnyK3` it is `k13Lot` at
    `pileAnyK3`.** `k13LotOnce_kind`, `k13LotOnce_find`: every half of it stands at a place of the
    kind K13; its own list holds the kind's half at the kind's place: `k13Lot_kind`, `k13Lot_find`
    (LotKind.lean of this folder) at it.
  `pileRowAt_congr`, `pileBySites_congr`: **two texts of the claims that agree at the sites'
    segments give the same filler.**
  `pileOfAnySize_none`: where `onlineFirstChainAt` rejects, no row.

ON WHAT IT LEANS. PileOfAnySize.lean and LotKind.lean of this folder, and what their heads name. It
imports, directly or through another file, no file of Honest/Thread/ or Honest/K3/Law/Thread/ (the
walk along the first chain, and the laws on it).

Who calls. `pileBySites_congr`: PileOfAnySizeAt.lean of this folder; `pileRowAt_congr`: it alone.
The other five statements, `k13LotOnce` and `pileBoxAnyK3`: no file of the library yet: they are the
tie between the held form and `k13Lot` that a filling wants which lays this lot.

What is not claimed. That the lot stands in any list of lots: none in the library holds it. That the
filler yields a row at any data, or the right rows. The equations are of terms: they say nothing on
how often code runs. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K13.PileOfAnySize
import Johnson.Desc.ProofFile.Honest.K13.LotKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13
open OnBytes OnBytes.Model OnBytes.Params
open OnBytes.Desc.First.K4.Honest (K4Pub)
open VerifiableInference.Desc (Chain Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13 (whereOf)
open VerifiableInference.Desc.K13.Honest (MergeSite SiteClaims pileRowAt pileBySites)
open ProofFile (Cl)

/-- A site's row reads the claims at the site's own segment alone. -/
theorem pileRowAt_congr {Xi : Type} (lay : WsLay) (Sh : LinShape) {cl cl' : SiteClaims Xi}
    (x : Xi) (hd : List Fmt.Drawn) (m : MergeSite) (e : cl m.link = cl' m.link) :
    pileRowAt lay Sh cl x hd m = pileRowAt lay Sh cl' x hd m := by
  unfold pileRowAt
  rw [e]

/-- **Two texts of the claims that agree at the sites' segments give the same filler.** -/
theorem pileBySites_congr {Xi : Type} (lay : WsLay) (Sh : LinShape) (sites : List MergeSite)
    {cl cl' : SiteClaims Xi} (e : ∀ m ∈ sites, cl m.link = cl' m.link) :
    pileBySites lay Sh sites cl = pileBySites lay Sh sites cl' := by
  funext x hd
  unfold pileBySites
  have key : ∀ l : List MergeSite, (∀ m ∈ l, cl m.link = cl' m.link) →
      l.mapM (pileRowAt lay Sh cl x hd) = l.mapM (pileRowAt lay Sh cl' x hd) := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons a t ih =>
      intro h
      rw [List.mapM_cons, List.mapM_cons,
        pileRowAt_congr lay Sh x hd a (h a (List.mem_cons_self ..)),
        ih fun m hm => h m (List.mem_cons_of_mem _ hm)]
  rw [key sites e]

/-- **The lot over a filler held as a field is `k13Lot` at that filler.** -/
theorem k13LotOnce_eq {W₀ Rc Tr X : Type} (weights : W₀ → Weights)
    (box : ProofFile.Pub → ProofFile.Ground → PileBox) :
    k13LotOnce (Rc := Rc) (Tr := Tr) (X := X) weights box =
      k13Lot weights (fun Z G => (box Z G).run) := rfl

/-- Where `onlineFirstChainAt` rejects, the filler yields no row. -/
theorem pileOfAnySize_none
    (armOf : Chain S Cl → ProofFile.Pub → ProofFile.Ground →
      ProofFile.Inst → List Fmt.Drawn → Option (Array WsClaim))
    (Q₀ : ProofFile.Pub → Nat → K4Pub) {Z' : ProofFile.Pub} {e : String} (hn : ProofFile.onlineFirstChainAt Z' = .error e)
    (G : ProofFile.Ground) (ξ : ProofFile.Inst) (hd : List Fmt.Drawn) :
    pileOfAnySize armOf Q₀ Z' G ξ hd = [] := by
  unfold pileOfAnySize pileBoxOfAnySize
  rw [hn]

/-- **EVERY HALF THAT THE LOT OVER A FILLER HELD AS A FIELD LAYS STANDS AT A PLACE OF THE KIND
K13.** -/
theorem k13LotOnce_kind {W₀ Rc Tr X : Type} (weights : W₀ → Weights)
    (box : ProofFile.Pub → ProofFile.Ground → PileBox) (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    ∀ x ∈ (k13LotOnce (Rc := Rc) (Tr := Tr) (X := X) weights box).halves Z G,
      x.place.kind = .K13 :=
  k13Lot_kind weights (fun Z G => (box Z G).run) Z G

/-- **What that lot's own list holds at the kind's place**: the kind's half, at the filler in the
field. -/
theorem k13LotOnce_find {W₀ Rc Tr X : Type} (weights : W₀ → Weights)
    (box : ProofFile.Pub → ProofFile.Ground → PileBox) (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    ((k13LotOnce (Rc := Rc) (Tr := Tr) (X := X) weights box).halves Z G).find?
        (fun x => x.place == k13Place (whereOf Z)) =
      some (proverSideOfClaimCombination weights (box Z G).run (whereOf Z)) :=
  k13Lot_find weights (fun Z G => (box Z G).run) Z G

/-- **At the closed terms: the lot over `pileBoxAnyK3` is `k13Lot` at `pileAnyK3`.** -/
theorem k13LotOnce_at_any {W₀ Rc Tr X : Type} (weights : W₀ → Weights) :
    k13LotOnce (Rc := Rc) (Tr := Tr) (X := X) weights pileBoxAnyK3 = k13Lot weights pileAnyK3 := rfl

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.pileRowAt_congr
#print axioms ProofFile.Honest.K13.pileBySites_congr
#print axioms ProofFile.Honest.K13.pileOfAnySize_none
#print axioms ProofFile.Honest.K13.k13LotOnce_eq
#print axioms ProofFile.Honest.K13.k13LotOnce_kind
#print axioms ProofFile.Honest.K13.k13LotOnce_find
#print axioms ProofFile.Honest.K13.k13LotOnce_at_any
