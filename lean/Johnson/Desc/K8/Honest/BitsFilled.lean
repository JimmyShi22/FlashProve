-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/BitsFilled.lean: THE SMALLNESS TEST: AT A PLAIN SEGMENT THE SIZES OF THE
BITS' ARRAY AT THE LEDGER BEHIND THE RUNS (`BitsAt`, Johnson/Desc/K8/Honest/PlanesShape.lean) COME
FROM THREE NUMBERS AT THE LEDGER IN FRONT OF THE BATCHING AND FROM WHAT THE BATCHING's DRAW DOES
FIRST: it fills each virtual row of each array of the link's list with a weight 0 a column
(`t2FillL`, OnBytes/Model/Trees.lean). SO BOTH TESTS ON THE PLANES, AND THE TEST ON THE READS'
WEIGHTS, SAY YES BEHIND A YES OF THE BATCHING BLOCK: `both_at_link`
(Johnson/Desc/K8/Honest/BothAtLink.lean) with the premise that the test on the planes' shapes says
yes EXCHANGED for sizes and public facts in front. None of the library's goals.

  `fill_at`   array number t behind the filling of the first n arrays: filled if t < n, else as it
                   was
  `fillOne_full`   a filled array's virtual row has a weight a column
  `full_of_fill`   behind the filling a virtual row of an array of the list has as many weights as
                   the array has columns in front
  `drawn_fill`   behind the batching's draw the ledger's arrays are those in front, filled along the
                   link's list. ITS PROOF IS THAT OF `drawn_frame`
                   (Johnson/Desc/K8/Honest/SecondAtPlain.lean) but for its last lines
  `BitsFront tl F`   at the ledger in front the bits' array has 3 virtual rows, 32 rows and the
                   plan's number of columns
  **`bitsAt_of_fill`**   BitsFront tl F · the bits' array's number is below the list's length ⊢
                   BitsAt at a ledger whose arrays are F's, filled: the looks by the library's
                   `K9L.fill_looks` (Johnson/Desc/First/Batch/Law/FitsAtS.lean)
  **`filled_at_link`**   `open_at_link`'s premises (Johnson/Desc/K8/Honest/OpenAtLink.lean) ⊢ what
                   of its end is spent here, and: the ledger behind the runs has the arrays of the
                   ledger in front, filled along the link's list
  **`three_of_walk`**   `both_of_walk`'s premises, but for the shape, which the filling keeps
                   (`shape_fill`, Johnson/Desc/K8/Honest/FallDraw.lean) · that filling · the list
                   has a member for each array of the ledger in front · BitsFront tl F · BitsPub tl
                   g ⊢ tl'.joinObj9 = some ‹the number of the claims in front› · readWeightsHeld ·
                   planesShapeHeld · planesWeightsHeld: all three say yes
  **`three_at_link`**   the same behind a yes of the batching block at a plain segment: one call of
                   each of the two above
Limits. IMPLICATIONS. THE PREMISE ON THE PLANES' SHAPES IS MOVED, NOT PAID: the draw's filling
supplies the three rows' numbers of weights alone. PAID BY NOBODY HERE: all that `both_at_link`
leaves (RunsKeep, with two invariants as letters; PubAt; four rows' first columns; PreOk, PostOk,
the tie) · BitsFront · BitsPub · that the link's list is as long as the ledger's list of arrays. At
one challenge x. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.BothAtLink
import Johnson.Desc.K8.Honest.PlanesShape
import Johnson.Desc.K8.Honest.SecondAtPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

/-- Array number t behind the filling of the first n arrays. -/
theorem fill_at (tr : Array HTree) (t : Nat) : ∀ n : Nat,
    ((List.range n).foldl (fun trees ti => trees.modify ti K9L.fillOne) tr).getD t {} =
      if t < n then K9L.fillOne (tr.getD t {}) else tr.getD t {}
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.foldl_append]
    show (((List.range n).foldl (fun trees ti => trees.modify ti K9L.fillOne) tr).modify n
      K9L.fillOne).getD t {} = _
    rw [Fo.getD_modify, fill_at tr t n]
    by_cases h : n = t
    · subst h
      rw [if_neg (Nat.lt_irrefl n), if_pos (Nat.lt_succ_self n)]
      split
      · rfl
      · rename_i hc
        have hs : ((List.range n).foldl (fun trees ti => trees.modify ti K9L.fillOne) tr).size =
            tr.size := by
          have key : ∀ (l : List Nat) (a : Array HTree),
              (l.foldl (fun trees ti => trees.modify ti K9L.fillOne) a).size = a.size := by
            intro l
            induction l with
            | nil => exact fun _ => rfl
            | cons x l ih => exact fun a => (ih _).trans Array.size_modify
          exact key _ _
        have hn : ¬ n < tr.size := fun c => hc ⟨rfl, by rw [hs]; exact c⟩
        have e0 : tr.getD n {} = {} := by simp [Array.getD, hn]
        rw [e0]
        simp [K9L.fillOne]
    · rw [if_neg (fun c => h c.1)]
      by_cases h2 : t < n
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]

/-- A filled array's virtual row has a weight a column. -/
theorem fillOne_full (X : HTree) (r : Nat) (hr : r < X.rows.size) :
    ((K9L.fillOne X).rows.getD r {}).L.size = X.K := by
  have e : (K9L.fillOne X).rows.getD r {} =
      if X.rows[r].L.size != X.K then
        { X.rows[r] with L := Array.replicate X.K zeroE } else X.rows[r] := by
    simp only [K9L.fillOne, Array.getD_eq_getD_getElem?, Array.getElem?_map,
      Array.getElem?_eq_getElem hr, Option.map_some, Option.getD_some]
  rw [e]
  by_cases hc : X.rows[r].L.size = X.K
  · rw [if_neg (by simp [hc])]
    exact hc
  · rw [if_pos (by simp [hc])]
    exact Array.size_replicate

/-- Behind the filling a virtual row of an array of the list has a weight a column. -/
theorem full_of_fill {F Y : Fork} (T : Tail2) {t r : Nat} (ht : t < T.nt.size)
    (hr : r < (F.trees.getD t {}).rows.size) (hY : Y.trees = (t2FillL F T).trees) :
    ((Y.trees.getD t {}).rows.getD r {}).L.size = (F.trees.getD t {}).K := by
  have e : Y.trees.getD t {} = K9L.fillOne (F.trees.getD t {}) := by
    rw [hY]
    exact (fill_at F.trees t T.nt.size).trans (if_pos ht)
  rw [e]
  exact fillOne_full _ r hr

/-- Behind the batching's draw the ledger's arrays are those in front, filled along the list. -/
theorem drawn_fill (p : K9.Where) (s t : S) (d : Fmt.Drawn) (hdr : drawnAt p s d = .ok t)
    (F : Fork) (hF : s.fork? = some F) :
    ∃ a0 x, K9.atS.get? s = some a0 ∧ K9.atS.get? t = some x ∧
      x.F.trees = (t2FillL F a0.L.list).trees := by
  obtain ⟨a0, x0, o, ha0, -, hdc, htt⟩ := drawnAt_ok p s t d hdr
  obtain ⟨a', ha', hF', -, -⟩ :=
    K9L.atS_reads s { a0 with owed := o.owed, L := o.L, F := o.F } (by rw [ha0]; rfl)
  have hFa : a0.F = F := Option.some.inj ((K9.get_fork s a0 ha0).symm.trans hF)
  refine ⟨a0, a', ha0, by rw [htt]; exact ha', ?_⟩
  rw [hF']
  show o.F.trees = _
  rw [drawn_trees _ _ _ _ _ _ _ hdc, hFa]

/-- The bits' array at the ledger in front. -/
structure BitsFront (tl : HTailF2) (F : Fork) : Prop where
  rows : (F.trees.getD tl.ix.BZ {}).rows.size = 3
  R : (F.trees.getD tl.ix.BZ {}).R = 32
  K : (F.trees.getD tl.ix.BZ {}).K = tl.bzColumns

/-- **The sizes behind the filling.** -/
theorem bitsAt_of_fill {tl : HTailF2} {F Y : Fork} (T : Tail2) (B : BitsFront tl F)
    (hT : tl.ix.BZ < T.nt.size) (hY : Y.trees = (t2FillL F T).trees) : BitsAt tl Y := by
  have lk : LinkJoin.look (Y.trees.getD tl.ix.BZ {}) =
      LinkJoin.look (F.trees.getD tl.ix.BZ {}) := by
    rw [hY]
    exact look_at (K9L.fill_looks F T) _
  exact ⟨(congrArg (·.2.2.2) lk).trans B.rows, (congrArg (·.2.1) lk).trans B.R,
    (congrArg (·.2.2.1) lk).trans B.K,
    fun r hr => (full_of_fill T hT (by rw [B.rows]; exact hr) hY).trans B.K⟩

/-- **What a yes of the batching block opens at a plain segment, with the filling beside it**:
`open_at_link`'s end, and that the ledger behind the runs has the arrays of the ledger in front,
filled along the link's list. -/
theorem filled_at_link (L : Link S Claim) (i : Nat) (pre post : List (Nat × String))
    (hord : L.order = pre ++ (i, "K8.equations") :: post) (Hpre : PreOk L pre)
    (Hpost : PostOk L post)
    (tEq : ∀ run, LinkJoin.At L (i, "K8.equations") run → LinkJoin.Under run K9L.k8Run.2)
    (p : K9.Where) (batch : S → List Fmt.RoundView → Except String S) (s t' : S) (tl : HTailF2) (F : Fork)
    (funs : Array HFun)
    (hb : ∀ rs t, batch s rs = .ok t →
      (K9.batch K9.atS p (claimsInBy L.each L.hear L.order)).decide s rs [] = .ok t)
    (ht : s.tl? = some tl) (hF : s.fork? = some F) (hf : s.funs? = some funs) (x : Cb.Gl.E)
    (hbt : batch s [⟨[], chiAt x⟩] = .ok t') :
    ∃ (a0 : K9.Part) (t e e₁ e₂ : S) (cls fr k8 bk : List Claim) (tl' : HTailF2)
      (Y G F₁ F₂ : Fork), K9.atS.get? s = some a0 ∧ drawnAt p s (chiAt x) = .ok t ∧
      Walk L pre post t e cls fr k8 bk e₁ e₂ F₁ F₂ tl tl' funs ∧
      tlForkP.get? t' = some (tl', G) ∧ Added8 tl tl' funs Y G F₁ F₂ fr k8 bk fr.length ∧
      Y.trees = (t2FillL F a0.L.list).trees := by
  obtain ⟨t, e, e₁, e₂, cls, fr, k8, bk, tl', Y, G, F₁, F₂, hdr, -, W, hY, hget, A, -, -, -⟩ :=
    open_at_link L i pre post hord Hpre Hpost tEq p batch s t' tl F funs hb ht hF hf x hbt
  obtain ⟨a0, xx, ha0, hxx, hfill⟩ := drawn_fill p s t (chiAt x) hdr F hF
  exact ⟨a0, t, e, e₁, e₂, cls, fr, k8, bk, tl', Y, G, F₁, F₂, ha0, hdr, W, hget, A,
    (walk_trees Hpre Hpost W xx hxx Y hY).trans hfill⟩

/-- **THREE TESTS, ALONG THE RUNS' OWN CUT.** -/
theorem three_of_walk {L : Link S Claim} {pre post : List (Nat × String)} {t e : S}
    {cls fr k8 bk : List Claim} {e₁ e₂ : S} {F₁ F₂ Y G F : Fork} {tl tl' : HTailF2}
    {funs : Array HFun} (W : Walk L pre post t e cls fr k8 bk e₁ e₂ F₁ F₂ tl tl' funs)
    (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk fr.length) (T : Tail2)
    (hYt : Y.trees = (t2FillL F T).trees) (hT : T.nt.size = F.trees.size)
    (g : Forest.Heard) (hg : tl.heard = some g) (P : PubAt tl g)
    (hzR : ((F.trees.getD tl.ix.ZZ {}).rows.getD tl.zzRowReads {}).L0 = 0)
    (hzB : ∀ e, e ≤ 2 → ((F.trees.getD tl.ix.BZ {}).rows.getD e {}).L0 = 0)
    (B : BitsFront tl F) (Pb : BitsPub tl g)
    {Inv Inv₂ : S → Prop} (R : RunsKeep L pre post (FourRows tl) Inv Inv₂) (hI : Inv t) :
    tl'.joinObj9 = some fr.length ∧
      tl'.readWeightsHeld (coefBody tl' g G)
        (((coefBody tl' g G).trees.getD tl'.ix.ZZ {}).rows.getD (2 * tl.zzBlocks) {}).L = true ∧
      tl'.planesShapeHeld (coefBody tl' g G) g = true ∧
      tl'.planesWeightsHeld (coefBody tl' g G) g fr.length = true := by
  have hsh : shapeOf Y.trees = shapeOf F.trees := by
    rw [hYt]
    exact shape_fill F T
  obtain ⟨h2, h3, h4⟩ := both_of_walk W A hsh g hg P hzR hzB R hI
  have hBZ : tl.ix.BZ < T.nt.size := by
    rw [hT]
    exact (hasRow_of_rows B.rows (show 0 < 3 by omega)).1
  have hSh := A.planesShape g (bitsAt_of_fill T B hBZ hYt) Pb
    fun mu hmu => (((apartB_iff tl).1 P.apart).2.2.2 mu hmu).1
  exact ⟨h2, h3, hSh, h4 hSh⟩

/-- **THREE TESTS AT A PLAIN SEGMENT, BEHIND A YES OF THE BATCHING BLOCK.** -/
theorem three_at_link (L : Link S Claim) (i : Nat) (pre post : List (Nat × String))
    (hord : L.order = pre ++ (i, "K8.equations") :: post) (Hpre : PreOk L pre)
    (Hpost : PostOk L post)
    (tEq : ∀ run, LinkJoin.At L (i, "K8.equations") run → LinkJoin.Under run K9L.k8Run.2)
    (p : K9.Where) (batch : S → List Fmt.RoundView → Except String S) (s t' : S) (tl : HTailF2) (F : Fork)
    (funs : Array HFun)
    (hb : ∀ rs t, batch s rs = .ok t →
      (K9.batch K9.atS p (claimsInBy L.each L.hear L.order)).decide s rs [] = .ok t)
    (ht : s.tl? = some tl) (hF : s.fork? = some F) (hf : s.funs? = some funs)
    (g : Forest.Heard) (hg : tl.heard = some g) (P : PubAt tl g)
    (hzR : ((F.trees.getD tl.ix.ZZ {}).rows.getD tl.zzRowReads {}).L0 = 0)
    (hzB : ∀ e, e ≤ 2 → ((F.trees.getD tl.ix.BZ {}).rows.getD e {}).L0 = 0)
    (B : BitsFront tl F) (Pb : BitsPub tl g)
    (hT : ∀ a0, K9.atS.get? s = some a0 → a0.L.list.nt.size = F.trees.size)
    (Inv Inv₂ : S → Prop) (R : RunsKeep L pre post (FourRows tl) Inv Inv₂)
    (x : Cb.Gl.E) (hInv : ∀ t, drawnAt p s (chiAt x) = .ok t → Inv t)
    (hbt : batch s [⟨[], chiAt x⟩] = .ok t') :
    ∃ (tl' : HTailF2) (G : Fork) (jo : Nat), tlForkP.get? t' = some (tl', G) ∧
      tl'.joinObj9 = some jo ∧
      tl'.readWeightsHeld (coefBody tl' g G)
        (((coefBody tl' g G).trees.getD tl'.ix.ZZ {}).rows.getD (2 * tl.zzBlocks) {}).L = true ∧
      tl'.planesShapeHeld (coefBody tl' g G) g = true ∧
      tl'.planesWeightsHeld (coefBody tl' g G) g jo = true := by
  obtain ⟨a0, t, e, e₁, e₂, cls, fr, k8, bk, tl', Y, G, F₁, F₂, ha0, hdr, W, hget, A, hYt⟩ :=
    filled_at_link L i pre post hord Hpre Hpost tEq p batch s t' tl F funs hb ht hF hf x hbt
  exact ⟨tl', G, fr.length, hget, three_of_walk W A a0.L.list hYt (hT a0 ha0) g hg P hzR hzB B
    Pb R (hInv t hdr)⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.fill_at
#print axioms VerifiableInference.Desc.First.K8.Honest.fillOne_full
#print axioms VerifiableInference.Desc.First.K8.Honest.full_of_fill
#print axioms VerifiableInference.Desc.First.K8.Honest.drawn_fill
#print axioms VerifiableInference.Desc.First.K8.Honest.bitsAt_of_fill
#print axioms VerifiableInference.Desc.First.K8.Honest.filled_at_link
#print axioms VerifiableInference.Desc.First.K8.Honest.three_of_walk
#print axioms VerifiableInference.Desc.First.K8.Honest.three_at_link
