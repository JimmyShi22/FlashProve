--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/- Johnson/IMR/RowsAt.lean:
OUR 101 NUMBERS, BY NUMBER: IN THE GOALS' SCOPE, AT THE OLDER HASH:
for every number k of the first chain and the sub-protocol b that stands there, if b's kind is K3,
K4, K5, K6, K8 or K11: HandsR, all six fields, at any fence Fk inside "the fold from the typed start
reaches the state" and at the join's constant EW: from the debt MadeOwed AT THAT FENCE, THAT k, THAT
b AND b's OWN PLACE, and two named premises. Two theorems, proved.



  rows_at   by the case split flat_cases, as at three_at: such
    a number is 14 l + i + 2, in front of a batching; there row_101W. THE
    SUB-PROTOCOL, ITS NUMBER AND ITS PLACE ARE TIED: b is c.blocksInOrder[k]; the place in the debt is
    b.place; that placesW[k] is that place is drawn inside (hear_placeW).
  rows_reached   the same at the fence "reached" itself: the letters of SharesRF
    (Johnson/IMR/GrownReach.lean).
  PREMISES THAT STAY: hB (the book's test at every reached state) · hFk (Fk lies inside "reached" at
    k) · alike (base has one value at all states) · M : MadeOwed at Fk.

OBJECT: c.blocksInOrder[k]. USER: none in Lean yet. LETTERS: N, D, base, z, p, Fk: free.

What is not claimed. MadeOwed at any sub-protocol. hB. No soundness.
-/
import Johnson.IMR.Row101W
import Johnson.IMR.RideAt

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName OpenedColumn)
open VerifiableInference.Desc.First (S Numbers Pub PubData bookAt kindsBeforeBatching closeKinds backKinds)
open VerifiableInference.Desc.Keeps (Decides)
open Johnson.Desc.First.Walk.Tied (Reach)
open Meaning.Tl (SameTl)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **OUR 101, BY NUMBER.** -/
theorem rows_at {Q : Type} {N : Numbers} {D : PubData} {base : Pub → Q × S → Bool} {z : Q}
    {p : ProofFile.InstPub} {Fk : ℕ → S → Prop} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B)
    (hB : ∀ k s, Reach 0 c.blocksInOrder (ProofFile.startS Z) k (p, s) → bookAt N placesW[k]? s = true)
    (alike : ∀ q s s', base q (z, s') = base q (z, s)) {k : ℕ} {b : Block S Cl}
    (hb : c.blocksInOrder[k]? = some b) (hq : quietMaker b.place.kind = true)
    (hFk : ∀ s, Fk k s → RF 0 c.blocksInOrder (ProofFile.startS Z) p k s)
    (M : MadeOwed Fk N linksW placesW D base z 0 k b b.place) :
    HandsR Fk N linksW placesW (LPFK9.HandsAt.EW D base z) 0 k b := by
  have hkind : kindW k = some b.place.kind := by
    unfold kindW
    rw [place_at hS hR O hb]
    rfl
  cases flat_cases hS hR O k b hb with
  | front b hr hd =>
    rw [kinds_ends.1] at hkind
    rw [← Option.some.inj hkind] at hq
    exact absurd hq (by decide)
  | laid l hl b hr hd =>
    rw [(kinds_at hl).1] at hkind
    rw [← Option.some.inj hkind] at hq
    exact absurd hq (by decide)
  | first l hl k0 b b' hk lot hp hj =>
    rw [joined_spot hj] at hq
    have hq' : quietMaker k0 = true := hq
    exfalso
    by_cases h24 : l < 24
    · have e := (first_kind l h24).symm.trans hk
      by_cases h0 : l = 0
      · rw [if_pos h0] at e
        rw [← Option.some.inj e] at hq'
        exact absurd hq' (by decide)
      · rw [if_neg h0] at e
        rw [← Option.some.inj e] at hq'
        exact absurd hq' (by decide)
    · obtain rfl : l = 24 := by omega
      obtain rfl : KindName.K7 = k0 := Option.some.inj hk
      exact absurd hq' (by decide)
  | hear l hl i hi k0 b b' name hk lot hp hla =>
    have ep := alone_place hla
    rw [ep] at hq M
    exact row_101W hB hl hk lot hp hq hla hb hFk alike M
  | batch l hl Lk p e1 hp hal =>
    rw [(kinds_at hl).2.1] at hkind
    rw [← Option.some.inj hkind] at hq
    exact absurd hq (by decide)
  | behind l hl Lk b e1 hr hd =>
    rw [(kinds_at hl).2.2.1] at hkind
    rw [← Option.some.inj hkind] at hq
    exact absurd hq (by decide)
  | close l hl p Q q k0 b x hp hQ hk ex hla =>
    rw [alone_place hla] at hq
    have hm := List.mem_of_getElem? hk
    have hq' : quietMaker k0 = true := hq
    exfalso
    clear hq hla hk hkind hb ex M
    revert hm hq'
    cases k0 <;> decide
  | cleared l hl fs f b hfs hf hr hd =>
    rw [(kinds_at hl).2.2.2.2.2.2] at hkind
    rw [← Option.some.inj hkind] at hq
    exact absurd hq (by decide)
  | back q k0 b b' name hk lot hp hla =>
    have hq' : quietMaker k0 = true := by
      have e : b.place = { chain := 1, link := none, piece := q + 1, kind := k0 } :=
        alone_place hla
      have hq2 : quietMaker b.place.kind = true := hq
      rw [e] at hq2
      exact hq2
    have hm := List.mem_of_getElem? hk
    exfalso
    clear hq hla hk hkind hb hp lot M
    revert hm hq'
    cases k0 <;> decide
  | last lot hla =>
    rw [kinds_ends.2.2] at hkind
    rw [← Option.some.inj hkind] at hq
    exact absurd hq (by decide)

/-- **… AT THE FENCE "REACHED" ITSELF.** -/
theorem rows_reached {Q : Type} {N : Numbers} {D : PubData} {base : Pub → Q × S → Bool} {z : Q}
    {p : ProofFile.InstPub} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B)
    (hB : ∀ k s, Reach 0 c.blocksInOrder (ProofFile.startS Z) k (p, s) → bookAt N placesW[k]? s = true)
    (alike : ∀ q s s', base q (z, s') = base q (z, s)) {k : ℕ} {b : Block S Cl}
    (hb : c.blocksInOrder[k]? = some b) (hq : quietMaker b.place.kind = true)
    (M : MadeOwed (RF 0 c.blocksInOrder (ProofFile.startS Z) p) N linksW placesW D base z 0 k b b.place) :
    HandsR (RF 0 c.blocksInOrder (ProofFile.startS Z) p) N linksW placesW (LPFK9.HandsAt.EW D base z) 0 k b :=
  rows_at hS hR O hB alike hb hq (fun _ h => h) M

end IM

#print axioms IM.rows_at
#print axioms IM.rows_reached
