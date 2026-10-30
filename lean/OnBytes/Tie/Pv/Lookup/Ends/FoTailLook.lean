-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoTailLook.lean.
The lookup's claims inside a sub-proof's one equation, as values that name neither the state nor the
element theta.

States:
  powSum x s vals: the sum of x^i times the i-th value, i counted from s. claimsValue_powSum: the
    library's claimsValue is powSum of the forms' values.
  look_powSum: behind Forest.objects and four further claims, the total has grown by powSum, from
    the number of claims before on, of: the flat function's rows, each as its form less its target
    (Fo.endsOf's rows), then the four values. Under: the run of Forest.objects returns, from a state
    with one coefficient for each slot; the record holds the end values (Fo.HeardIs) with a state
    F0; the world is that of a state later than F0; and, as a premise (h4), the total grows behind
    Forest.objects by the four values under the next four powers.
  claimsZ: the lookup's claims in the order in which Forest.objects, linJoin9 and linBits9, run in
    turn, add them: the rows, the join, the leaves' row, the bits' value, the counts' sum. It is
    Fo.claimsOf with the join moved before the planes' three (claimsZ_perm: a permutation of it).
  tail_look_dig: at the lookup on the digits the total grows by powSum of claimsZ at the digits' own
    letters. The members of that list are terms in the shape, the first slot, the rounds rsK, the
    smallness test's record tl (through plV and digKF), the caller's names en and mk of the entries,
    and the entries μ₀ of the committed messages and the mask row: no state and no theta is among
    their arguments.
Hypotheses of tail_look_dig: the run of Forest.objects returns and linJoin9 starts from what it
leaves; else those of Fo.tail_four_dig (OnBytes/Tie/Pv/Lookup/Ends/FoTailDig.lean: the two runs, the
record, the world's virtual rows, public numbers), with its premises on the state now said of the
state before Forest.objects.
Limit: that the virtual rows' weights named in these hypotheses are what the smallness test's own
claims enforce, and whether THOSE claims hang on theta, is not said here. Nor is it said that no
field of the record tl hangs on theta, or that HTailF2.objectsF (OnBytes/Model/Tail.lean) runs the
three routines in turn from one another's states: that is read off its definition. Nor is it shown
here that one world meets all the hypotheses on virtual rows together (the head of
OnBytes/Tie/Pv/Lookup/Ends/FoTailDig.lean says what that asks).
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoAddsTail
import OnBytes.Tie.Pv.Lookup.Ends.FoTailDig

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.DgP Cb.Fo Cb.LdLkp Finset
open Cb.Fo.PlaneClaims

section
variable {K : Type} [CommRing K]

/-- The sum of x^i times the i-th value, i counted from s. -/
def powSum (x : K) (s : ℕ) (vals : List K) : K := sumFrom (fun i v => x ^ i * v) s vals

theorem claimsValue_powSum (ρ : Reading K) (W : World K) (x : K) : ∀ (l : List Aff) (s : ℕ),
    claimsValue ρ W x s l = powSum x s (l.map fun a => a.value ρ W)
  | [], _ => rfl
  | a :: l, s => by
    show x ^ s * a.value ρ W + claimsValue ρ W x (s + 1) l =
      x ^ s * a.value ρ W + powSum x (s + 1) (l.map fun a => a.value ρ W)
    rw [claimsValue_powSum ρ W x l (s + 1)]

theorem powSum_append (x : K) (s : ℕ) (a b : List K) :
    powSum x s (a ++ b) = powSum x s a + powSum x (s + a.length) b := sumFrom_append _ a b s

/-- Behind Forest.objects and four further claims. -/
theorem look_powSum (ρ : Reading K) (g : Heard) (lm jLK : ℕ) (rsK : Rounds K)
    (F0 Fb F G2 H : Fork) (cb c : Ctx) (hO : Forest.objects g Fb cb = .ok (((), F), c))
    (hI : HeardIs ρ g F0 (endsOf g.shape lm jLK rsK)) (h0 : Later F0 H)
    (hLS : Fb.LS.size = Fb.ns) (ν : Pl → K) (entry : ℕ → ℕ → ℕ → K) (vJ vL vB vC : K)
    (h4 : G2.total ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) =
      F.total ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) +
        ρ.val F.theta ^ F.nClaim * vJ + ρ.val F.theta ^ (F.nClaim + 1) * vL +
        ρ.val F.theta ^ (F.nClaim + 2) * vB + ρ.val F.theta ^ (F.nClaim + 3) * vC) :
    G2.total ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) =
      Fb.total ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) +
        powSum (ρ.val Fb.theta) Fb.nClaim
          ((endsOf g.shape lm jLK rsK).rows.map (rowRes ν) ++ [vJ, vL, vB, vC]) := by
  have a0 := objects_added hO hLS
  rw [h4, a0.total, a0.theta, a0.nClaim, clsValue_forms, claimsValue_powSum,
    rows_claim ρ g lm jLK rsK F0 hI H h0 ν entry, powSum_append, List.length_map, List.length_map,
    Array.length_toList, hI.nRows]
  simp only [powSum, sumFrom]
  ring

/-- The lookup's claims in the order in which Forest.objects, linJoin9 and linBits9 add them. -/
def claimsZ (h : FoNums.Sh) (lm jLK : ℕ) (rs : Rounds K) (ν : Pl → K)
    (bit0 bit1 pin kf : ℕ → K) : List K :=
  (endsOf h lm jLK rs).rows.map (rowRes ν) ++
    [claimJoin h lm jLK rs ν kf, claimLeaves h lm jLK rs ν bit0, claimBits h lm jLK rs ν bit1,
      Pin.countK h lm pin]

/-- The same values as Fo.claimsOf, in another order. -/
theorem claimsZ_perm (h : FoNums.Sh) (lm jLK : ℕ) (rs : Rounds K) (ν : Pl → K)
    (bit0 bit1 pin kf : ℕ → K) :
    (claimsZ h lm jLK rs ν bit0 bit1 pin kf).Perm (claimsOf h lm jLK rs ν bit0 bit1 pin kf) := by
  unfold claimsZ claimsOf
  refine List.Perm.append_left _ ?_
  exact (List.perm_append_comm (l₁ := [claimJoin h lm jLK rs ν kf])
    (l₂ := [claimLeaves h lm jLK rs ν bit0, claimBits h lm jLK rs ν bit1, Pin.countK h lm pin]))

end

section
variable {K : Type} [Field K] (ρ : Reading K) {J₀ : Type}

/-- The lookup on the digits inside the one equation. -/
theorem tail_look_dig (tl tl1 tl2 : HTailF2) (Fb F G1 G2 : Fork) (cb c c1 c2 : Ctx)
    (hJ : tl.linJoin9 F c = .ok ((tl1, G1), c1)) (hB : tl1.linBits9 G1 c1 = .ok ((tl2, G2), c2))
    (g : Heard) (hO : Forest.objects g Fb cb = .ok (((), F), c)) (hg : tl.heard = some g) (hs :
        tl.f9 = g.shape) (jLK : ℕ) (rsK : Rounds K)
    (F0 : Fork) (hI : HeardIs ρ g F0 (endsOf g.shape 5 jLK rsK)) (h0 : Later F0 Fb)
    (hok : FoNums.ok g.shape = true) (hT : TailOK tl) (hF : Sized Fb) (hLS : Fb.LS.size = Fb.ns)
    (hfull : 2 ^ g.shape.cK = g.shape.NC) (h5 : 5 ≤ g.shape.kT + g.shape.cK)
    (hn : ∀ q < 2, (g.zk.getD q #[]).size = (tl.zOf q).call.n)
    (h63 : ∀ q < 2, (tl.zOf q).call.n ≤ 63)
    (hP : ∀ q < 2, ∀ p ∈ piecesL tl q, PieceOK tl q (tl.zOf q).call.n p)
    (hD : ∀ q < 2, (piecesL tl q).Pairwise fun p p' =>
      p.off + 2 ^ p.b ≤ p'.off ∨ p'.off + 2 ^ p'.b ≤ p.off)
    (en : Ent3 → J₀) (mk : ℕ → J₀) (μ₀ : J₀ → K) (entry : ℕ → ℕ → ℕ → K)
    (hV0 : VirtRow entry tl.ix.BZ 0
      (fun r => (eqTabK ((endsOf g.shape 5 jLK rsK).zb0.take 5)).getD r 0)
      (fun r i => μ₀ (en (tl.ix.BZ, r, i))) 32 tl.bzColumns)
    (hV1 : VirtRow entry tl.ix.BZ 1
      (fun r => (eqTabK ((endsOf g.shape 5 jLK rsK).zb1.take 5)).getD r 0)
      (fun r i => μ₀ (en (tl.ix.BZ, r, i))) 32 tl.bzColumns)
    (hV2 : VirtRow entry tl.ix.BZ 2 (fun _ => 1) (fun r i => μ₀ (en (tl.ix.BZ, r, i))) 32
      tl.bzColumns)
    (hVp : ∀ q < 2, ∀ p ∈ piecesL tl q, ∀ i < p.Cp, entry p.tree p.row (p.c0 + i) =
      ∑ r ∈ range p.Rp, (eqTabK (exL (rdL ρ (g.zk.getD q #[])) ((tl.zOf q).call.n - p.b)
        ((tl.zOf q).call.n - p.b + p.a))).getD r 0 * μ₀ (en (tl.ix.ZZ, p.r0 + r, p.c0 + i)))
    (H : Fork) (hH : Later G2 H) :
    G2.total ρ (H.worldOf ρ (fun j => μ₀ (mk j)) entry) =
      Fb.total ρ (H.worldOf ρ (fun j => μ₀ (mk j)) entry) +
        powSum (ρ.val Fb.theta) Fb.nClaim
          (claimsZ g.shape 5 jLK rsK (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
            (colsK g.shape 5 (endsOf g.shape 5 jLK rsK).zb0
              fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
            (colsK g.shape 5 (endsOf g.shape 5 jLK rsK).zb1
              fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
            (Pin.pinColK 5 fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
            fun c => AffK.val (digKF tl en (fun c => (endsOf g.shape 5 jLK rsK).zk.getD c []) c)
              (zext μ₀)) := by
  obtain ⟨lO, sO⟩ := Keeps.objects g Fb cb () F c hO hF
  have aO := objects_added hO hLS
  obtain ⟨lJ, sJ⟩ := keeps_Model_HTailF2_linJoin9 tl F c tl1 G1 c1 hJ sO
  obtain ⟨lB, _⟩ := keeps_Model_HTailF2_linBits9 tl1 G1 c1 tl2 G2 c2 hB sJ
  have h4 := tail_four_dig ρ tl tl1 tl2 F G1 G2 c c1 c2 hJ hB g hg hs jLK rsK F0 hI (h0.trans lO)
    hok hT sO aO.sized hfull h5 hn h63 hP hD en mk μ₀ entry hV0 hV1 hV2 hVp H hH
  exact look_powSum ρ g 5 jLK rsK F0 Fb F G2 H cb c hO hI
    ((((h0.trans lO).trans lJ).trans lB).trans hH) hLS
    (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p)) entry _ _ _ _ h4

end
end Fo
