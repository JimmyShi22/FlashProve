-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoCarry.lean.
What the block behind a sub-proof's lookup must carry.

Knowledge soundness runs backwards: the relation of the block behind the lookup must give the
lookup's out-claim at the out-statement x. This file names, in the words of the list of claims
(`Fo.claimsOf`, OnBytes/Tie/Pv/Lookup/Forest/FoClaims.lean), clauses that give it.

Main names:
  `claimsOf_congr`: the list of claims reads the caller's letters at the planes' columns and at the
    calls alone.
  `CarryAt`: x is the out-statement that the plain data rs describe (`OutAt`); the caller's letters
    are the columns' sums and the extensions of the calls' key vectors; every claim of the list is
    0.
  `carry_out`: `CarryAt` gives the lookup's out-claim at x. `carry_iff`: at an x with `OutAt` and at
    the letters' meant values it says no more than the out-claim.
  `CarryReads`: the same where the planes' letters are entries of the sub-proof's vector of reads,
    under the law of the reads (`ReadsLaw`, OnBytes/Tie/Pv/Lookup/Port/FoReads.lean).
    `carryReads_at`: it gives `CarryAt`.
  `CarryForms`: the same where, besides, the keys' letters are the values of the caller's key forms
    in a world, under `KeysAt` (OnBytes/Tie/Pv/Lookup/Ends/FoKeys.lean). `carryForms_reads`: it
    gives `CarryReads`. It is meant as the clause behind the calls' lookup of the attention
    sub-proof and of the head, whose routines hand key forms to `Forest.join`.
  `carry_rel`: from `CarryAt` alone, the first two of the out-claim's three clauses, written out:
    the masked claim on the keys holds, and all rows hold. (The third is True at these letters.)

Under: the shape is lawful (`FoNums.ok`); 5 ≤ lm ≤ kT + 5.

Not claimed: anything on completeness or hiding. Nor is it claimed that a block's relation holds
these clauses, or that the law of the reads or `KeysAt` holds of any world.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoOutOf
import OnBytes.Tie.Pv.Lookup.Ends.FoKeys
import OnBytes.Tie.Pv.Lookup.Forest.FoPlaneAt

set_option autoImplicit false

namespace Fo
open Iop IOR Cb Cb.Tw Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole TwV Tw3 Tw Cb.Fo Cb.Fo.NumsEq Cb.Fo.Pin
open Cb.Fo.PlaneClaims OnBytes OnBytes.Model Finset

section
variable {K : Type} [CommRing K]

/-- The list of claims reads the letters at the planes' columns and at the calls alone. -/
theorem claimsOf_congr (h : FoNums.Sh) (lm jLK : ℕ) (rs : Rounds K) (ν : _root_.Fo.Pl → K)
    (b0 b0' b1 b1' p p' kf kf' : ℕ → K)
    (h0 : ∀ col, col < h.NC * 2 ^ (h.kT + 5 - lm) → b0 col = b0' col)
    (h1 : ∀ col, col < h.NC * 2 ^ (h.kT + 5 - lm) → b1 col = b1' col)
    (hp : ∀ col, col < h.NC * 2 ^ (h.kT + 5 - lm) → p col = p' col)
    (hk : ∀ c, c < h.NC → kf c = kf' c) :
    claimsOf h lm jLK rs ν b0 b1 p kf = claimsOf h lm jLK rs ν b0' b1' p' kf' := by
  unfold claimsOf claimLeaves claimBits claimJoin
  rw [planesK_congr h lm _ b0 b0' h0, planesK_congr h lm _ b1 b1' h1, countK_congr h lm p p' hp,
    val_joinK, val_joinK]
  have e : ∑ c ∈ range h.NC, eK h (endsOf h lm jLK rs).zy c *
        ((endsOf h lm jLK rs).alpha - (c : K) * (endsOf h lm jLK rs).theta -
          AffK.val (AffK.ofConst (kf c) : AffK _root_.Fo.Pl K) ν) =
      ∑ c ∈ range h.NC, eK h (endsOf h lm jLK rs).zy c *
        ((endsOf h lm jLK rs).alpha - (c : K) * (endsOf h lm jLK rs).theta -
          AffK.val (AffK.ofConst (kf' c) : AffK _root_.Fo.Pl K) ν) :=
    sum_congr rfl fun c hc => by rw [hk c (mem_range.mp hc)]
  rw [e]

end

section
variable {E : Type} [Field E] [Fintype E] {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀]

/-- What gives the lookup's out-claim at x, at letters. ν: the places read through the layout. -/
structure CarryAt (h : FoNums.Sh) (L : Lay E St₀ J₀) (lm jLK : ℕ) (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀)
    (rs : Rounds E) (st : St₀) (x : TX (St₀ × E) E (Option J₀)) (μ₀ : J₀ → E)
    (bit0 bit1 pin kf : ℕ → E) : Prop where
  out : OutAt h lm jLK (placeOf mk pl) rs st x
  col0 : ∀ col, col < h.NC * 2 ^ (h.kT + 5 - lm) →
    bit0 col = colsK h lm (endsOf h lm jLK rs).zb0 (fun p => zext μ₀ (placeOf mk pl p)) col
  col1 : ∀ col, col < h.NC * 2 ^ (h.kT + 5 - lm) →
    bit1 col = colsK h lm (endsOf h lm jLK rs).zb1 (fun p => zext μ₀ (placeOf mk pl p)) col
  pinC : ∀ col, col < h.NC * 2 ^ (h.kT + 5 - lm) →
    pin col = pinColK lm (fun p => zext μ₀ (placeOf mk pl p)) col
  keys : ∀ c, c < h.NC →
    kf c = extL (forK E L st (zext μ₀) c) ((endsOf h lm jLK rs).zk.getD c [])
  claims : ∀ y ∈ claimsOf h lm jLK rs (fun p => zext μ₀ (placeOf mk pl p)) bit0 bit1 pin kf, y = 0

/-- **These clauses give the lookup's out-claim.** -/
theorem carry_out {h : FoNums.Sh} (H : FoNums.ok h = true) {L : Lay E St₀ J₀} {lm jLK : ℕ}
    (h5 : 5 ≤ lm) (hlm : lm ≤ h.kT + 5) {mk : ℕ → J₀} {pl : ℕ → ℕ → J₀} {rs : Rounds E} {st : St₀}
    {x : TX (St₀ × E) E (Option J₀)} {μ₀ : J₀ → E} {bit0 bit1 pin kf : ℕ → E}
    (C : CarryAt h L lm jLK mk pl rs st x μ₀ bit0 bit1 pin kf) :
    (forA E h L).lk.out id id x (zext μ₀) := by
  refine out_of_claims h H L lm jLK h5 hlm mk pl rs st x C.out (fun c => AffK.ofConst (kf c)) μ₀
    (fun c hc => by rw [AffK.val_ofConst]; exact C.keys c hc) ?_
  rw [← claimsOf_congr h lm jLK rs _ bit0 _ bit1 _ pin _ kf _ C.col0 C.col1 C.pinC
    fun c _ => (AffK.val_ofConst _ _).symm]
  exact C.claims

/-- At an out-statement with `OutAt` and at the letters' meant values the clauses say no more than
the out-claim. -/
theorem carry_iff {h : FoNums.Sh} (H : FoNums.ok h = true) {L : Lay E St₀ J₀} {lm jLK : ℕ}
    (h5 : 5 ≤ lm) (hlm : lm ≤ h.kT + 5) {mk : ℕ → J₀} {pl : ℕ → ℕ → J₀} {rs : Rounds E} {st : St₀}
    {x : TX (St₀ × E) E (Option J₀)} {μ₀ : J₀ → E}
    (hx : OutAt h lm jLK (placeOf mk pl) rs st x) :
    CarryAt h L lm jLK mk pl rs st x μ₀
        (colsK h lm (endsOf h lm jLK rs).zb0 fun p => zext μ₀ (placeOf mk pl p))
        (colsK h lm (endsOf h lm jLK rs).zb1 fun p => zext μ₀ (placeOf mk pl p))
        (pinColK lm fun p => zext μ₀ (placeOf mk pl p))
        (fun c => extL (forK E L st (zext μ₀) c) ((endsOf h lm jLK rs).zk.getD c [])) ↔
      (forA E h L).lk.out id id x (zext μ₀) := by
  refine ⟨carry_out H h5 hlm, fun ho => ⟨hx, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, ?_⟩⟩
  have g := (out_iff_claims h H L lm jLK h5 hlm mk pl rs st x hx (fun c => AffK.ofConst
    (extL (forK E L st (zext μ₀) c) ((endsOf h lm jLK rs).zk.getD c []))) μ₀
    (fun c _ => AffK.val_ofConst _ _)).1 ho
  simp only [AffK.val_ofConst] at g
  exact g

/-- The planes' letters are entries of the sub-proof's vector of reads. -/
structure CarryReads (h : FoNums.Sh) (L : Lay E St₀ J₀) (lm jLK : ℕ) (mk : ℕ → J₀)
    (pl : ℕ → ℕ → J₀) (rs : Rounds E) (st : St₀) (x : TX (St₀ × E) E (Option J₀)) (μ₀ : J₀ → E)
    (entry : ℕ → ℕ → ℕ → E) (iU3 K3 tB0 tB1 tP : ℕ) (kf : ℕ → E) : Prop where
  out : OutAt h lm jLK (placeOf mk pl) rs st x
  reads : ReadsLaw h lm (endsOf h lm jLK rs).zb0 (endsOf h lm jLK rs).zb1
    (fun p => zext μ₀ (placeOf mk pl p)) entry iU3 K3 tB0 tB1 tP
  keys : ∀ c, c < h.NC →
    kf c = extL (forK E L st (zext μ₀) c) ((endsOf h lm jLK rs).zk.getD c [])
  claims : ∀ y ∈ claimsOf h lm jLK rs (fun p => zext μ₀ (placeOf mk pl p))
    (fun col => u3Val entry iU3 K3 (tB0 + col)) (fun col => u3Val entry iU3 K3 (tB1 + col))
    (fun col => u3Val entry iU3 K3 (tP + col)) kf, y = 0

omit [Fintype E] [Fintype J₀] in
theorem carryReads_at {h : FoNums.Sh} {L : Lay E St₀ J₀} {lm jLK : ℕ} {mk : ℕ → J₀}
    {pl : ℕ → ℕ → J₀} {rs : Rounds E} {st : St₀} {x : TX (St₀ × E) E (Option J₀)} {μ₀ : J₀ → E}
    {entry : ℕ → ℕ → ℕ → E} {iU3 K3 tB0 tB1 tP : ℕ} {kf : ℕ → E}
    (C : CarryReads h L lm jLK mk pl rs st x μ₀ entry iU3 K3 tB0 tB1 tP kf) :
    CarryAt h L lm jLK mk pl rs st x μ₀ (fun col => u3Val entry iU3 K3 (tB0 + col))
      (fun col => u3Val entry iU3 K3 (tB1 + col)) (fun col => u3Val entry iU3 K3 (tP + col)) kf :=
  ⟨C.out, fun col hc => C.reads.bits0 col hc, fun col hc => C.reads.bits1 col hc,
    fun col hc => C.reads.count col hc, C.keys, C.claims⟩

/-- The keys' letters are the values of the caller's key forms in a world. -/
structure CarryForms (ρ : Reading E) (W : World E) (h : FoNums.Sh) (L : Lay E St₀ J₀) (lm jLK : ℕ)
    (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀) (rs : Rounds E) (st : St₀)
    (x : TX (St₀ × E) E (Option J₀)) (μ₀ : J₀ → E) (iU3 K3 tB0 tB1 tP : ℕ) (KF : Array Aff) :
    Prop where
  out : OutAt h lm jLK (placeOf mk pl) rs st x
  reads : ReadsLaw h lm (endsOf h lm jLK rs).zb0 (endsOf h lm jLK rs).zb1
    (fun p => zext μ₀ (placeOf mk pl p)) W.entry iU3 K3 tB0 tB1 tP
  keys : KeysAt ρ W h.NC KF (forK E L st (zext μ₀)) fun c => (endsOf h lm jLK rs).zk.getD c []
  claims : ∀ y ∈ claimsOf h lm jLK rs (fun p => zext μ₀ (placeOf mk pl p))
    (fun col => u3Val W.entry iU3 K3 (tB0 + col)) (fun col => u3Val W.entry iU3 K3 (tB1 + col))
    (fun col => u3Val W.entry iU3 K3 (tP + col))
    (fun c => (KF.getD c (Aff.ofConst zeroE)).value ρ W), y = 0

omit [Fintype E] [Fintype J₀] in
theorem carryForms_reads {ρ : Reading E} {W : World E} {h : FoNums.Sh} {L : Lay E St₀ J₀}
    {lm jLK : ℕ} {mk : ℕ → J₀} {pl : ℕ → ℕ → J₀} {rs : Rounds E} {st : St₀}
    {x : TX (St₀ × E) E (Option J₀)} {μ₀ : J₀ → E} {iU3 K3 tB0 tB1 tP : ℕ} {KF : Array Aff}
    (C : CarryForms ρ W h L lm jLK mk pl rs st x μ₀ iU3 K3 tB0 tB1 tP KF) :
    CarryReads h L lm jLK mk pl rs st x μ₀ W.entry iU3 K3 tB0 tB1 tP
      fun c => (KF.getD c (Aff.ofConst zeroE)).value ρ W :=
  ⟨C.out, C.reads, fun c hc => C.keys c hc, C.claims⟩

/-- From `CarryAt`: the first two clauses of the out-claim, written out. -/
theorem carry_rel {h : FoNums.Sh} (H : FoNums.ok h = true) {L : Lay E St₀ J₀} {lm jLK : ℕ}
    (h5 : 5 ≤ lm) (hlm : lm ≤ h.kT + 5) {mk : ℕ → J₀} {pl : ℕ → ℕ → J₀} {rs : Rounds E} {st : St₀}
    {x : TX (St₀ × E) E (Option J₀)} {μ₀ : J₀ → E} {bit0 bit1 pin kf : ℕ → E}
    (C : CarryAt h L lm jLK mk pl rs st x μ₀ bit0 bit1 pin kf) :
    x.2.1.Holds ((forA E h L).v' + 1) ((forA E h L).key x.1 (zext μ₀)) (zext μ₀) ∧
      RowsHold x.2.2 (zext μ₀) :=
  ⟨(carry_out H h5 hlm C).1, (carry_out H h5 hlm C).2.1⟩

end
end Fo
