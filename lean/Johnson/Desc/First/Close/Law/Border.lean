-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/Border.lean: THE BORDER BEHIND THE CLOSING OF A LINK (kind K10), ON
VECTORS, WITH KEPT MEMBERS: the form behind the proved fold, at the typed state that the proved
block puts out, is, entry by entry, the reading of the claim that the closing's text hands on.
Definitions, statements and proofs.

A group with kept rows is `RowsK` (Johnson/Top/H/GroupRowsKept.lean): a super-row has the slot
"none", for the rows on the cube, and a slot for each kept row.
  `SlotNames R`: for each kept slot, the number of its oracle message in the statement, and for each
    entry of a row the index of that entry in the message's own main table. Letters.
  `inVec R N row`: a row on a group (`GroupRow`), as a vector on the fold's input code: on the slot
    none and on the mask rows: the library's `vecG`; on a kept slot: what the row's forms on that
    message read as at the entry (`keptSum`), AT THE CORNER 0 .. 0, and 0 at every other corner.
  `outVec R N out`: a claim on single rows (`SingleRows`), as a vector on the folded code: the
    library's `vecS`; on a kept slot what its forms on that message read as.
  `keptSum_scale`: forms times a scalar. `prod_one_sub`: a product over a list, over its point.
  `border`: for ANY form F on the fold's input code and any state st at which `F st` is `inVec` of
    the row: the form behind the fold (`slOut`) at `stAt` of st, the reading of gamma and the
    reading of eps is `outVec` of the program's `foldOutput`.
  `law_border`: at a caller whose shape is R's, on a written stretch: if `closing` says yes, the
    proved block's verifier puts out a statement a' whose target is the reading of the target handed
    on, and at every form F that reads the batched row at the batching's state, the form behind the
    fold at the state of a' is `outVec` of the claim handed on.

Premises of `law_border` beside those of Statement.lean: three equations between the plan's numbers
and the typed shape's: hk (k), hh (h), hZ (the mask code's message length): public numbers.

Limits. THE LAST CLAUSE REACHES NO JOINT YET. F is quantified apart from the caller, whose own form
(the arranged one, `GShape.form`) stands in the relation behind the proved block. At a made-up F
(the constant `inVec N row`) the premise hF costs nothing and the clause says nothing of that
relation; at the caller's own form hF fails on a real proof, by others' reading: that form is 0 on
the rows of a member's block that the member did not send. SO WHAT IS OWED IS A CALLER WHOSE
RELATION HOLDS THE FORM "arranged plus weights on the free rows", with the law at THAT caller; the
proved block's verifier does not read the form, so the output is the same. The slots' names are
letters. Nothing on the words, on the samples or on what is carried. The limits of Whole.lean and of
Statement.lean, beside this file, hold here. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Top.H.CallerKept
import Johnson.Desc.First.Close.Law.Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Tie.Pv.Fold Iop IOR KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open OnBytes.PscRun (drawnOf)

/-- Forms on kept members, each times x, read as the forms times the reading of x. -/
theorem keptSum_scale (o idx : ℕ) (x : E) : ∀ l : List KeptForm,
    keptSum rdE o idx (l.map fun f => { f with c := f.c.scale x }) =
      keptSum rdE o idx l * readE x
  | [] => by simp [keptSum]
  | f :: l => by
    have ih := keptSum_scale o idx x l
    unfold keptSum at ih ⊢
    rw [List.map_cons, List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, add_mul]
    congr 1
    show (if f.oracle = o then rdE.val ((f.c.scale x).entry idx) else 0) = _
    by_cases h : f.oracle = o
    · rw [if_pos h, if_pos h, Form.entry_scale rdE f.c x idx]
      rfl
    · rw [if_neg h, if_neg h, zero_mul]

/-- The product over a list of n elements, as a product over the point that is read off it. -/
theorem prod_one_sub : ∀ (g : List E) (n : ℕ), g.length = n →
    (g.map fun x => 1 - readE x).prod = ∏ t : Fin n, (1 - readP n g t)
  | [], n, h => by
    subst h
    simp
  | x :: g, n, h => by
    subst h
    rw [List.map_cons, List.prod_cons, prod_one_sub g g.length rfl]
    show _ = ∏ t : Fin (g.length + 1), (1 - readP (g.length + 1) (x :: g) t)
    rw [Fin.prod_univ_succ]
    rfl

variable {S : Sig GE} (R : RowsK S)

/-- The names of the kept slots in a statement: the oracle message's number; an entry's index in
that message's own main table. -/
structure SlotNames where
  orc : R.Kp → ℕ
  idx : R.Kp → R.s.cM.J → ℕ

variable {R} (N : SlotNames R)

/-- A row on a group, as a vector on the fold's input code. -/
noncomputable def inVec (row : GroupRow) : R.Sh.Cin.J → GE := fun j =>
  match j with
  | .inl (b, (none, x)) => vecG R.s row (.inl (b, x))
  | .inl (b, (some q, x)) =>
      if b = fun _ => false then keptSum rdE (N.orc q) (N.idx q x) row.kept.toList else 0
  | .inr x => vecG R.s row (.inr x)

/-- A claim on single rows, as a vector on the folded code. -/
noncomputable def outVec (out : SingleRows) : R.Sh.Cf.J → GE := fun j =>
  match j with
  | .inl (none, x) => vecS R.s out (.inl x)
  | .inl (some q, x) => keptSum rdE (N.orc q) (N.idx q x) out.kept.toList
  | .inr x => vecS R.s out (.inr x)

/-- **THE BORDER ON VECTORS**, at any form that reads the row. -/
theorem border {St : Type} (F : Slf GE St R.Sh.Cin.J) (st : St) (S' : Statement) (Fs : FoldShape)
    (row : GroupRow) (m : ℕ) (eps : E) (gamma : List E) (claim : E)
    (hk : Fs.layout.k = R.s.h + R.s.g) (hh : Fs.layout.h = R.s.h)
    (hg : gamma.length = R.s.h + R.s.g) (hok : foldRowOk S' Fs row = true)
    (hZ : (S'.codes.mask.getD Fs.maskCode default).ell = R.s.Z.l) (hF : F st = inVec N row) :
    (R.Sh.par.reform F).slOut (stAt (R.Sh.par.reform F) st st (readP (R.s.h + R.s.g) gamma)
      (readE eps)) = outVec N (foldOutput S' Fs row m eps gamma claim) := by
  have hv := vecS_foldOutput_fits R.s S' Fs row m eps gamma claim hk hh hg hok hZ
  rw [slOut_slots]
  funext j
  rcases j with ⟨o, x⟩ | x | x
  · cases o with
    | none =>
      show (∑ b, F st (.inl (b, (none, x))) * Alg.eqk _ b) * _ = vecS R.s _ (.inl x)
      rw [hv, hF]
      rfl
    | some q =>
      show (∑ b, F st (.inl (b, (some q, x))) * Alg.eqk _ b) * _ =
        keptSum rdE (N.orc q) (N.idx q x)
          (row.kept.map fun f => { f with c := f.c.scale (foldKeptFactor eps gamma) }).toList
      rw [hF, Array.toList_map, keptSum_scale, readE_foldKeptFactor,
        prod_one_sub gamma (R.s.h + R.s.g) hg]
      show (∑ b : Fin (R.s.h + R.s.g) → Bool,
        (if b = fun _ => false then keptSum rdE (N.orc q) (N.idx q x) row.kept.toList else 0) *
          Alg.eqk (readP (R.s.h + R.s.g) gamma) b) * readE eps = _
      rw [sum_corner]
      ring
  · show (∑ b, F st (.inr (b, x)) * Alg.eqk _ b) * _ = vecS R.s _ (.inr (.inl x))
    rw [hv, hF]
    rfl
  · show _ = vecS R.s _ (.inr (.inr x))
    rw [hv]
    rfl

section Caller
variable (R) (keep : S.O → Prop) [DecidablePred keep] {B : Type} [Fintype B]
  (Sb : B → Type) (sl : ∀ b, Slf GE (Sb b) R.G.C.J) (Z : Evader GE (R.G.Row B))
  (fx : Fin ((R.Sh.fold Sb sl Z).n + 1) × GE) {Kc St₀ Wp : Type} {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub (R.sizeB keep Sb sl Z).kp).Msg × Wp)) (bC bZ : ℕ)
  (w₀ : S.Wit × Wp) (w₁ : LdBrW R.G (R.sizeB keep Sb sl Z).kp Wp)

/-- **THE LAW OF K10 WITH THE BORDER ON VECTORS**, at the caller on a group with kept rows. -/
theorem law_border (L : List (BatFoldCaller GE)) (rB rE rR : Round)
    (ρ : Rd (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁) rB rE rR) (hS : ρ.Scal)
    (hst : StepOK (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).val
      (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).n fx
      (rd2 (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)))
    (hfx : fx.2 * (HVar.plain GE (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).n).mon fx.1 = 1)
    (P : Plan) (T T' : Statement) (g : Nat) (mask : Option Nat) (out : SingleRows)
    (a : ((kBatFoldRide L).src (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).X ×
      ((kBatFoldRide L).src (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).E.Str)
    (τ : Tr (rB :: rE ::
      List.replicate (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).k rR))
    (ht : ρ.DefAt (ρ.V τ)) (h : closing P T g mask (ρ.V τ) = .ok (out, T'))
    (hO : ∀ G e z, T.groups[g]? = some G → (ρ.viewB τ.1 τ.2.1).drawn.elems = [e.triple] →
      ρ.rdZ (drawnOf (ρ.viewB τ.1 τ.2.1)) = some z →
      Ordered (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁) a.1 z e
        ((runRows T G).toList.map fun w => readE w.target))
    (hR : ∀ G, T.groups[g]? = some G → ∀ w ∈ (runRows T G).toList, RowFits (begun T g G) w)
    (hk : P.k = R.s.h + R.s.g) (hh : P.h = R.s.h)
    (hZ : (T.codes.mask.getD P.maskCode default).ell = R.s.Z.l) :
    ∃ (G : Group) (x : E) (row : GroupRow) (lay : GroupLayout) (z : Z.D)
      (τ' : Tr ((kBatFoldRide L).block (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).R.red.shape)
      (a' : ((kBatFoldRide L).dst (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).X ×
        ((kBatFoldRide L).dst (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).E.Str),
      T.groups[g]? = some G ∧ (ρ.viewB τ.1 τ.2.1).drawn.elems = [x.triple] ∧
      ρ.rdZ (drawnOf (ρ.viewB τ.1 τ.2.1)) = some z ∧
      Bat.combine (begun T g G) g ⟨lay, runRows T G⟩ x = some row ∧
      (begun T g G).layout g = some lay ∧ lay.h = R.s.h ∧ ρ.carS.tr τ = some τ' ∧
      ((kBatFoldRide L).block (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).R.red.out a τ' =
        some a' ∧
      a'.1.1.1 = readE out.target ∧
      a'.1.2 = (batX (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁) a.1 z).2 ∧
      ∀ (N : SlotNames R) (F : Slf GE (Tower.BSt Sb Z) R.Sh.Cin.J),
        F (batX (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁) a.1 z).1.2 = inVec N row →
        (R.Sh.par.reform F).slOut a'.1.1.2 = outVec N out := by
  obtain ⟨G, x, eps, row, lay, m, claim, z, τ', a', hG, -, h3, -, h5, h6, h7, -, h8, h9, h10, h11,
    h12, h13, h14, h15⟩ := law_whole L _ rB rE rR ρ hS hst hfx P T T' g mask out a τ ht h hO hR
  refine ⟨G, x, row, lay, z, τ', a', hG, h3, h5, h6, h7, h8.trans hh, h13, h14, by rw [h15],
    by rw [h15], fun N F hF => ?_⟩
  have hb := border N F _ T' (shapeAt P lay) row m eps out.gamma claim hk hh (h9.trans hk) h10
    (by rw [h11]; exact hZ) hF
  rw [← h12] at hb
  rw [h15]
  exact hb

end Caller

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.law_border
#print axioms VerifiableInference.Desc.First.Close.keptSum_scale
#print axioms VerifiableInference.Desc.First.Close.border
