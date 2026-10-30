-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoMeet.lean.
Plain data of the right sizes are the reading of a typed transcript of the sub-proofs' lookup.

Two statements speak of the flat function's end values: one at a typed transcript read as plain
data (Fo.forFl), one at the rounds that the byte-level routine took off a view. This file gives
the typed transcript for the second one's data, so that both speak of one list.

Main names:
  `flAll_un`: for every lookup A0, every shift's data P, with the shift's round and without it:
    plain data that fit the shift's round (if there is one) and then the chain's spec (Tw.spChn) are
    Fo.flAll of a typed transcript. The transcript is Tw.unChn's, with the shift's round in front.
  `specN v' d w n`: the chain's spec as a plain list, written over ranges; `spOf_eq`: it is Tw.spOf.
  `specF h`: the spec of the sub-proofs' lookup at the shape h; `spec_forA`: it is the shift's round
    and Tw.spChn at the typed lookup forA.
  `YNonZero h rs`: in every round in which the spec asks it (the round of a sumcheck's further
    variable), the element drawn is not 0.
  `rfit_of`: sizes and that premise give Tw.RFit round for round.
  `spec_sizes`: the spec's numbers of scalars sent and of elements drawn are Fo.planF h, if 1 ≤ h.v.
  `meet`: if the sizes of rs are Fo.planF h, 1 ≤ h.v and YNonZero h rs, then there is a typed
    transcript τ with forFl h L Ex τ = rs.
Limits: YNonZero is a premise. The typed challenge of a further variable is an element other than
0, so data with a 0 there are the reading of no typed transcript. The byte-level routine does not
test it: it is the strict reader's rule for that draw.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoRead
import Cb.Pv.Lookup.Out.TwLift

set_option autoImplicit false

namespace Fo
open Iop IOR Cb Cb.Tw Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole TwV Tw3 Tw

/-! ### the shift's round in front of the chain -/

section
variable {E St : Type} [Field E] [Fintype E] (Ex : ExtSpec) (A0 : LkAsmH E)
  (P : ShiftQ E St (A0.J → E))

/-- The spec of the shift's round, if there is one. -/
def spShift (several : Bool) : List RSp := if several then [⟨0, 1, false⟩] else []

theorem flAll_un (several : Bool) (rs : Rounds E)
    (h : List.Forall₂ RFit (spShift several ++ spChn (P.asmH A0)) rs) :
    ∃ τ, flAll Ex A0 P several τ = rs := by
  cases several with
  | false => exact ⟨(unChn Ex (P.asmH A0)).un rs, flChn_un Ex (P.asmH A0) rs h⟩
  | true =>
    match rs, h with
    | r0 :: rest, .cons h0 h1 =>
      refine ⟨Tr.app (s := [drawRound E]) (((), ()), r0.2.headD 0, ())
        ((unChn Ex (P.asmH A0)).un rest), ?_⟩
      show [(([] : List E), [drawn (Tr.fst (s := [drawRound E]) (Tr.app (s := [drawRound E])
          (((), ()), r0.2.headD 0, ()) ((unChn Ex (P.asmH A0)).un rest)))])] ++
        flChn Ex (P.asmH A0) (Tr.snd (s := [drawRound E]) (Tr.app (s := [drawRound E])
          (((), ()), r0.2.headD 0, ()) ((unChn Ex (P.asmH A0)).un rest))) = r0 :: rest
      rw [Tr.fst_app, Tr.snd_app, flChn_un Ex (P.asmH A0) rest h1]
      show (([] : List E), [r0.2.headD 0]) :: rest = r0 :: rest
      rw [one_of_len _ h0.2.1, ← nil_of_len r0.1 h0.1]

end

/-! ### the spec as a plain list -/

theorem chainSp_flat (sp : ℕ → List RSp) : ∀ n, chainSp sp n = (List.range (n + 1)).flatMap sp
  | 0 => by simp [chainSp]
  | n + 1 => by
    rw [chainSp, chainSp_flat sp n, List.range_succ (n := n + 1), List.flatMap_append]
    simp

theorem spForest_flat (v' w : ℕ) : ∀ d, spForest v' w d =
    (List.range (v' + 1)).flatMap (spLev 0) ++ (List.range d).flatMap (spLev w)
  | 0 => by simp [spForest, chainSp_flat]
  | d + 1 => by
    rw [spForest, spForest_flat v' w d, List.append_assoc, List.range_succ (n := d),
      List.flatMap_append]
    simp

/-- The chain's spec over ranges: alpha; the tie's n + 1 steps; the point of w; the key levels; the
table's levels; the leaves; the point of w + d; the bits. -/
def specN (v' d w n : ℕ) : List RSp :=
  [⟨0, 1, false⟩] ++ (List.range (n + 1)).flatMap spStep ++ [⟨0, w, false⟩] ++
  (List.range (v' + 1)).flatMap (spLev 0) ++ (List.range d).flatMap (spLev w) ++
  (⟨1, 1, false⟩ :: (List.replicate d 2 ++ List.replicate w 1).map fun n => ⟨n, 1, false⟩) ++
  [⟨0, w + d, false⟩] ++ spSc (w + d) 2 2 1

theorem spOf_eq (v' d w n : ℕ) :
    spOf v' d w n (List.replicate d 2 ++ List.replicate w 1) = specN v' d w n := by
  unfold spOf specN
  rw [chainSp_flat, spForest_flat]
  simp only [List.append_assoc, Nat.add_zero]

/-! ### at the sub-proofs' lookup -/

/-- The spec of the sub-proofs' lookup. -/
def specF (h : FoNums.Sh) : List RSp :=
  spShift (FoNums.several h) ++ specN (FoNums.v' h) h.d FoNums.w FoNums.n

open Cb.Fo in
theorem spec_forA {E : Type} [Field E] [Fintype E] {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀]
    (h : FoNums.Sh) (L : Lay E St₀ J₀) :
    spShift (FoNums.several h) ++ spChn ((forP E h L).asmH (forA E h L)) = specF h := by
  unfold specF
  rw [← spOf_eq, ← Cb.dgEnd_rev FoNums.w h.d]
  rfl

/-- The numbers of scalars sent and of elements drawn. -/
def sizeOf {K : Type} (r : List K × List K) : ℕ × ℕ := (r.1.length, r.2.length)

/-- In every round in which the spec asks it, the elements drawn are not 0. -/
def YNonZero {K : Type} [Zero K] (h : FoNums.Sh) (rs : Rounds K) : Prop :=
  ∀ i x, ((specF h).getD i ⟨0, 0, false⟩).nz = true → x ∈ (rs.getD i ([], [])).2 → x ≠ 0

theorem rfit_of {K : Type} [Zero K] : ∀ (sp : List RSp) (rs : Rounds K),
    rs.map sizeOf = sp.map (fun s => (s.sent, s.drawn)) →
    (∀ i x, (sp.getD i ⟨0, 0, false⟩).nz = true → x ∈ (rs.getD i ([], [])).2 → x ≠ 0) →
    List.Forall₂ RFit sp rs
  | [], [], _, _ => .nil
  | s :: sp, r :: rs, hs, hz => by
    rw [List.map_cons, List.map_cons] at hs
    have h1 := List.cons.inj hs
    refine .cons ⟨congrArg Prod.fst h1.1, congrArg Prod.snd h1.1, fun hn x hx => hz 0 x hn hx⟩
      (rfit_of sp rs h1.2 fun i x hn hx => hz (i + 1) x hn hx)
  | [], _ :: _, hs, _ => by simp at hs
  | _ :: _, [], hs, _ => by simp at hs

/-! ### the sizes are the flat function's plan -/

/-- A spec's numbers of scalars sent and of elements drawn. -/
def szs (sp : List RSp) : List (ℕ × ℕ) := sp.map fun s => (s.sent, s.drawn)

theorem szs_append (a b : List RSp) : szs (a ++ b) = szs a ++ szs b := List.map_append

theorem szs_flat (f : ℕ → List RSp) (l : List ℕ) :
    szs (l.flatMap f) = l.flatMap fun i => szs (f i) :=
  List.map_flatMap

theorem end_degs (w : ℕ) : ∀ d, ((OnBytes.Lkp.defaultOrder (w + d)).map fun t =>
    if t < w then 1 else 2) = List.replicate d 2 ++ List.replicate w 1
  | 0 => by
    refine List.eq_replicate_iff.2 ⟨by simp [OnBytes.Lkp.defaultOrder], fun b hb => ?_⟩
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hb
    have : t < w := by simpa [OnBytes.Lkp.defaultOrder] using ht
    exact if_pos this
  | d + 1 => by
    have e : OnBytes.Lkp.defaultOrder (w + (d + 1)) =
        (w + d) :: OnBytes.Lkp.defaultOrder (w + d) := by
      unfold OnBytes.Lkp.defaultOrder
      rw [← Nat.add_assoc, List.range_succ, List.reverse_append]
      rfl
    rw [e, List.map_cons, end_degs w d, if_neg (by omega)]
    rfl

theorem szs_sc (k a : ℕ) (ha : a ≠ 0) (D : ℕ) :
    szs (spSc k 2 D a) = scRounds ⟨List.replicate k 2 ++ [D], true, a⟩ := by
  simp [szs, spSc, scRounds, ha]

theorem spec_sizes (h : FoNums.Sh) (hv : 1 ≤ h.v) : szs (specF h) = planF h := by
  have hv' : FoNums.v' h + 1 = h.v := by unfold FoNums.v'; omega
  have hE : scRounds (FoNums.S h).scEnd =
      szs (⟨1, 1, false⟩ :: (List.replicate h.d 2 ++ List.replicate FoNums.w 1).map
        fun n => ⟨n, 1, false⟩) := by
    have e : (FoNums.S h).scEnd.degs = List.replicate h.d 2 ++ List.replicate FoNums.w 1 :=
      end_degs FoNums.w h.d
    unfold scRounds
    rw [e]
    simp [szs, TwNums.Sizes.scEnd]
  unfold specF specN planF
  simp only [szs_append, szs_flat]
  rw [hv', hE]
  have h1 : ∀ j, szs (spStep j) = scRounds ((FoNums.S h).scTie j) := fun j => by
    unfold spStep TwNums.Sizes.scTie
    by_cases hj : j = 0 <;> simp [hj, szs, spSc, scRounds]
  have h2 : ∀ l, szs (spLev 0 l) = scRounds ((FoNums.S h).scKey l) ++ [(0, 1)] := fun l => by
    unfold spLev TwNums.Sizes.scKey
    rw [szs_append, szs_sc _ 2 (by decide), Nat.zero_add]
    rfl
  have h3 : ∀ l, szs (spLev FoNums.w l) = scRounds ((FoNums.S h).scTab l) ++ [(0, 1)] := fun l => by
    unfold spLev
    rw [szs_append, szs_sc _ 2 (by decide)]
    rfl
  have h4 : szs (spSc (FoNums.w + h.d) 2 2 1) = scRounds (FoNums.S h).scBit :=
    szs_sc _ 1 (by decide) 2
  simp only [h1, h2, h3, h4]
  cases FoNums.several h <;> rfl

open Cb.Fo in
/-- Plain data of the plan's sizes, with no 0 drawn where a further variable's challenge stands,
are the reading of a typed transcript of the sub-proofs' lookup. -/
theorem meet {E : Type} [Field E] [Fintype E] {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀]
    (h : FoNums.Sh) (L : Lay E St₀ J₀) (Ex : ExtSpec) (rs : Rounds E) (hv : 1 ≤ h.v)
    (hs : rs.map sizeOf = planF h) (hz : YNonZero h rs) :
    ∃ τ : Tr (forB E h L V₀ V₀C (Ex := Ex)).R.shape, forFl h L Ex τ = rs :=
  flAll_un Ex (forA E h L) (forP E h L) (FoNums.several h) rs
    (by rw [spec_forA]; exact rfit_of _ _ (hs.trans (spec_sizes h hv).symm) hz)

end Fo
