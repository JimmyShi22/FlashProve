-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K10/Honest/LeftClaim.lean: after the closing of a segment, the code switch's claim on what the fold left is
true.

What is proved. **`close_claimTrue`**: assume `CloseBase P s D`, that every row that the test takes in (`runRows`: the
group's open rows and the members' sample rows) holds of words m, that m is 0 on the rows beyond the real ones, and
rounds that show the honest round polynomials. Then the block's decision returns the record whose single rows are
`old := foldOutAt (D.S1 s) (D.F s) row D.m (rE :: rR)` (row: what the batching returns at the element that "BAT" drew),
and `ClaimTrue (sizesAt (D.S1 s) old T) old (leftAt (D.S1 s) old m)` holds, for every target T of a switch. `ClaimTrue`
and `sizesAt`: Johnson/Desc/K2/Honest/Inner/Statement.lean, where `ClaimTrue` is a premise of `SwitchRowsHold`.
`leftAt`: Johnson/Desc/K2/Honest/Carry/Left.lean. The proof joins `closeBase_holds` (Holds.lean), `close_leaves`
(LeavesAt.lean), `leftFits_of_base` (LeftBase.lean) and `claimTrue_iff_tables` (LeftIs.lean).

  `stageB_k`, `stageB_z`   two of the four numbers that `closeBase_holds` asks of a stage, at `stageB`
  `getD_read`       reading a list's entries commutes with `getD`
  `point_is`        where the rounds show polynomials at the point γ, the single rows' point (`pointAt`) is γ
  `mem_switchKept`  a member that the layout marks as kept is among `switchKept`
  `rows_named`      every form on a kept member in the returned single rows names a kept member: `ClaimTrue`'s first
                   clause

What is defined. `stageB`, `freshB`: the stage and the fresh table of LeftIs.lean (`stageAt`, `freshAt`), written with
the data of `CloseBase`, so that the premises can name them before the single rows are at hand. They equal `stageAt` and
`freshAt` at `D.S1 s` and these single rows by unfolding; no theorem states it.

The premises. Those of `closeBase_holds`, at the stage `stageB`, the element that "BAT" drew and the fresh table
`freshB`: `CloseBase`; the rows hold of m (hs); the fresh table pairs with the hiding polynomial's coefficients W (hP);
"FOLD epsilon" shows that polynomial's sum (hσ); the rounds "FOLD round" show the honest round polynomials (hR). Of the
stage's four numbers three are shown (`stageB_k`, `stageB_z`, one by unfolding); the fourth stays a premise, hlen: the
main code's message length is 2 ^ logEll (`CloseBase` has the like for the mask code only). Those of `close_leaves`: 2 +
P.k rounds (hl) of the kind's shape (hsh). New: `Padded (D.S1 s) m` (hp). The fresh table is the words' own table at the
fresh mask's message, not a free variable.

Limits. All premises are assumptions: that an honest prover's run meets them is not shown here. That they can be met
together: `toy_member` (LeftClaimToy.lean [not in this library; so here read: not proved in this library]), at one made-up example. The theorem is on the block's decision at the kind's
own record, not on the block's step (Step.lean, AtS.lean). The statement is `D.S1 s`, the one after the beginning of the
test; the record that the decision returns holds `spent (D.S1 s) D.m`, and a later code switch reads a later statement:
that `sizesAt` and `leftAt` are the same there is not shown here. The Limits of LeftIs.lean hold of `leftAt` here too.
`ClaimTrue` is one of the premises of `SwitchRowsHold`; nothing is said of the others. That the words are what was
committed to is not spoken of. Nothing is said on soundness, completeness or hiding of the protocol.
-/
import Johnson.Desc.K10.Honest.LeftBase
import Johnson.Desc.K10.Honest.LeavesAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K10.LeftIs
open OnBytes OnBytes.Means OnBytes.Slice Johnson.Prover.Link H2K.ClaimSays Cb
open VerifiableInference.Desc
open VerifiableInference.Desc.K2.Honest
open VerifiableInference.Desc.First.Close (Par Rec kind)
open ProofFile.Honest.K10.YesFree (BaseData CloseBase layoutOf_same ShapedAll)
open ProofFile.Honest.K10.Values (keptLen closeBase_holds close_leaves)

/-- The stage of LeftIs.lean, written with the data of `CloseBase`: `stageAt` at `D.S1 s` and the returned single rows,
by unfolding. -/
def stageB (D : BaseData) (s : Rec) : Sg :=
  stageOf (D.S1 s).codes s.frame.shape.code s.frame.shape.maskCode (D.F s).layout

/-- The fresh table of LeftIs.lean, written with the data of `CloseBase`: `freshAt` at `D.S1 s` and the returned single
rows, by unfolding. -/
def freshB (D : BaseData) (s : Rec) (m : Words GE) : (stageB D s).cFr.J → GE :=
  fun x => m D.m .mask
    (Sz.rowNo x.1 + x.2.val * 2 ^ ceilLog2 ((D.S1 s).oracles.getD D.m default).shape.maskRows)

/-- Reading a list's entries commutes with `getD`. -/
theorem getD_read (l : List E) (n : Nat) : (l.map readE).getD n zeroG = readE (l.getD n zeroE) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases l[n]? <;> rfl

/-- A member that the layout marks as kept is among `switchKept`. -/
theorem mem_switchKept {old : SingleRows} (hk : old.layout.kept.size = old.layout.members.size)
    {o i : Nat} (hf : old.layout.find o = some i) (hkept : old.layout.kept.getD i false = true) :
    o ∈ (switchKept old).toList := by
  obtain ⟨hi, ho⟩ := find_some hf
  have hp : (o, true) ∈ pairs old := by
    have := List.mem_of_getElem? (pairs_get hk hi)
    rw [ho, hkept] at this
    exact this
  unfold switchKept
  rw [Array.toList_map, Array.toList_filter]
  exact List.mem_map.2 ⟨(o, true), List.mem_filter.2 ⟨hp, rfl⟩, rfl⟩

variable {P : Par} {s : Rec} {D : BaseData}

/-- The stage has the group's number of row variables. -/
theorem stageB_k (H : CloseBase P s D) : D.Gq.k = (stageB D s).h + (stageB D s).g := by
  obtain ⟨_, _, _, _, _, h2, _⟩ := (Own.foldShapeFits_iff _ _).1 H.shape
  have h2' : D.Gq.h ≤ D.Gq.k := h2
  show D.Gq.k = D.Gq.h + (D.Gq.k - D.Gq.h)
  omega

/-- The stage's mask code has the layout's message length. -/
theorem stageB_z (H : CloseBase P s D) :
    2 ^ (Own.layoutOf s.st D.G).logEllZk = (stageB D s).Z.l := by
  have hc : (D.S1 s).codes = s.st.codes := (extends_begun s.st s.frame.group D.G).codes
  show _ = ((D.S1 s).codes.mask.getD s.frame.shape.maskCode default).ell
  rw [hc, H.power, ← H.maskCode]
  rfl

/-- Where the rounds show polynomials at the point γ, the single rows' point is γ. -/
theorem point_is (row : GroupRow) (rE : Fmt.RoundView) (rR : List Fmt.RoundView)
    (q : RIdx (sVars GE 2 ((stageB D s).h + (stageB D s).g)) → GE)
    (γ : HPt (sVars GE 2 ((stageB D s).h + (stageB D s).g)))
    (h : Shows ((stageB D s).h + (stageB D s).g) rR q γ) :
    pointAt (D.S1 s) (foldOutAt (D.S1 s) (D.F s) row D.m (rE :: rR)) =
      sPt 2 ((stageB D s).h + (stageB D s).g) γ := by
  rw [← (claimOf_shows _ rR q γ zeroE h).2.1]
  funext i
  exact getD_read (rR.map drawnOf) i.val

/-- Every form on a kept member in the returned single rows names a kept member: `ClaimTrue`'s first clause. -/
theorem rows_named (H : CloseBase P s D) {x : E} {row : GroupRow}
    (hrow : Own.batch (D.S1 s) s.frame.group ⟨Own.layoutOf s.st D.G, runRows s.st D.G⟩ x = some row)
    (rE : Fmt.RoundView) (rR : List Fmt.RoundView) :
    ∀ f ∈ (foldOutAt (D.S1 s) (D.F s) row D.m (rE :: rR)).kept.toList,
      f.oracle ∈ (switchKept (foldOutAt (D.S1 s) (D.F s) row D.m (rE :: rR))).toList := by
  have hE := extends_begun s.st s.frame.group D.G
  have hc : (D.S1 s).codes = s.st.codes := hE.codes
  have hG' := begun_group s.st s.frame.group D.G H.there
  have hOk' : GroupOk (D.S1 s) { D.G with inRun := true, rows := #[] } :=
    H.inOrder.extends hE rfl rfl rfl rfl
  have eL := layoutOf_same H.there
  have hL' : (D.S1 s).layout s.frame.group = some (Own.layoutOf s.st D.G) := by
    show (Slice.begun s.st s.frame.group D.G).layout s.frame.group = _
    rw [layout_eq _ _ _ hG', eL,
      layoutOf_extends (G' := { D.G with inRun := true, rows := #[] }) hE H.inOrder rfl rfl rfl rfl]
  have hr' : ∀ r ∈ (runRows s.st D.G).toList,
      RowIn (D.S1 s) { D.G with inRun := true, rows := #[] } r :=
    fun r h => RowIn.extends (G := D.G) hE (fun _ c => c) (H.rowsIn r h)
  have e2 : ((D.S1 s).codes.mask.getD s.frame.shape.maskCode default).ell =
      2 ^ (Own.layoutOf s.st D.G).logEllZk := by
    rw [hc, H.power, ← H.maskCode]
    rfl
  have hfit : Own.foldRowFits (First.Close.spent (D.S1 s) D.m) (D.F s) row = true :=
    RowFit.batch_rowfits hG' hL' hOk' hr' H.termsOk hrow (First.Close.spent (D.S1 s) D.m) rfl
      (fun o ho => (First.Close.spent_extends D.m (D.S1 s)).tableBits (hOk'.there o ho) .main)
      (D.F s) rfl rfl H.kh.1.symm H.kh.2.symm
      (by
        show ceilLog2 ((D.S1 s).codes.base.getD s.frame.shape.code default).ell = _
        rw [hc, ← H.code]
        rfl) e2 H.bits
  obtain ⟨_, _, hk⟩ := (Own.foldRowFits_iff _ _ _).1 hfit
  have hsize := (leftFits_of_base H row rE rR).facts.2.1
  intro f hf
  have hf' : f ∈ (row.kept.map fun g => ({ g with
      c := g.c.scale (foldKeptFactor (drawnOf rE) (rR.map drawnOf)) } : KeptForm)).toList := hf
  rw [Array.toList_map] at hf'
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf'
  obtain ⟨⟨i, hi, hkept⟩, _⟩ := hk g (Array.mem_toList_iff.1 hg)
  exact mem_switchKept hsize hi hkept

/-- **After the closing the claim on what the fold left is true.** -/
theorem close_claimTrue {Cl : Type} (H : CloseBase P s D)
    (hlen : 2 ^ (Own.layoutOf s.st D.G).logEll =
      ((D.S1 s).codes.base.getD s.frame.shape.code default).ell)
    (m : Words GE) (hs : AllSay rdE s.st (runRows s.st D.G).toList m) (hp : Padded (D.S1 s) m)
    (rB rE : Fmt.RoundView) (rR : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hl : (rB :: rE :: rR).length = 2 + P.k) (hsh : ShapedAll (rB :: rE :: rR))
    (W : HIdx (sVars GE 2 ((stageB D s).h + (stageB D s).g)) → GE)
    (γ : HPt (sVars GE 2 ((stageB D s).h + (stageB D s).g)))
    (hP : Pairs (stageB D s) (stageB D s).Z.l W (freshB D s m))
    (hσ : readE ((sentOf rE).getD 0 zeroE) = hMu (sVars GE 2 ((stageB D s).h + (stageB D s).g)) W)
    (hR : ∀ row, Own.batch (D.S1 s) s.frame.group ⟨Own.layoutOf s.st D.G, runRows s.st D.G⟩
        (drawnOf rB) = some row →
      Shows ((stageB D s).h + (stageB D s).g) rR (foldQK (stageB D s) (vecG (stageB D s) row)
        (msgOf (stageB D s) (tablesOf (D.S1 s) (Own.layoutOf s.st D.G) m)) W (readE (drawnOf rE))
        (keptVal (keptLen (D.S1 s)) (tablesOf (D.S1 s) (Own.layoutOf s.st D.G) m).kept row.kept)
        γ) γ)
    (T : SwitchTarget) :
    ∃ row, Own.batch (D.S1 s) s.frame.group ⟨Own.layoutOf s.st D.G, runRows s.st D.G⟩
        (drawnOf rB) = some row ∧
      ((kind (Cl := Cl)) P).decide s (rB :: rE :: rR) gs = .ok ⟨none, { s.frame with
          rows := foldOutAt (D.S1 s) (D.F s) row D.m (rE :: rR), mask := none
          link := s.frame.link + 1, next := .first }, spent (D.S1 s) D.m⟩ ∧
      ClaimTrue (sizesAt (D.S1 s) (foldOutAt (D.S1 s) (D.F s) row D.m (rE :: rR)) T)
        (foldOutAt (D.S1 s) (D.F s) row D.m (rE :: rR))
        (leftAt (D.S1 s) (foldOutAt (D.S1 s) (D.F s) row D.m (rE :: rR)) m) := by
  obtain ⟨row, hrow, hdec⟩ := close_leaves (Cl := Cl) H rB rE rR gs hl hsh
  have hfits := leftFits_of_base H row rE rR
  obtain ⟨row', hrow', hall⟩ :=
    closeBase_holds H (stageB D s) (stageB_k H) rfl hlen (stageB_z H) m hs (drawnOf rB)
  obtain rfl : row' = row := Option.some.inj (hrow'.symm.trans hrow)
  have E := hall rE rR (freshB D s m) W γ hP hσ (hR _ hrow)
  refine ⟨_, hrow, hdec, (claimTrue_iff_tables _ _ _ T m hfits hp).2 ⟨rows_named H hrow rE rR, ?_⟩⟩
  have eT : tablesOf (D.S1 s) (foldOutAt (D.S1 s) (D.F s) row' D.m (rE :: rR)).layout m =
      tablesOf (D.S1 s) (Own.layoutOf s.st D.G) m := by rw [rows_layout H row' rE rR]
  have eP := point_is (D := D) (s := s) row' rE rR _ γ (hR _ hrow)
  unfold foldedAt
  rw [eT, eP]
  exact E

end ProofFile.Honest.K10.LeftIs

#print axioms ProofFile.Honest.K10.LeftIs.stageB
#print axioms ProofFile.Honest.K10.LeftIs.freshB
#print axioms ProofFile.Honest.K10.LeftIs.getD_read
#print axioms ProofFile.Honest.K10.LeftIs.mem_switchKept
#print axioms ProofFile.Honest.K10.LeftIs.stageB_k
#print axioms ProofFile.Honest.K10.LeftIs.stageB_z
#print axioms ProofFile.Honest.K10.LeftIs.point_is
#print axioms ProofFile.Honest.K10.LeftIs.rows_named
#print axioms ProofFile.Honest.K10.LeftIs.close_claimTrue
