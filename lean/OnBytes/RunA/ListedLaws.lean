-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/RunA/ListedLaws.lean: what the form along the positions read and listed is. The definitions
are in OnBytes/RunA/ListedDefs.lean.

Theorems.
  `verifyPL_eq`: for any skeleton `PS`, wiring, oracle functions and typed string, `verifyPL` at a
    wiring's pieces is the library's `verifyPR` at that wiring, under three hypotheses: (h1) `ord`
    makes of a set the wiring's list `all` filtered by membership; (h2) an opening stands at listed
    positions alone; (h3) `all` holds every position.
  `order2`: h1 at `WireE.two`'s list, for `readsInOrder2`.
  `extOf_listed`: h2 at `Run.PQ.extOf`, for all tables.
  `vxl_eq`: without a hypothesis, for all D, dec, r0, r1, π, tabs: `VXL D dec r0 r1 π tabs` is the
    run of the library's `Compile.Batch.verifyOneProtocol`, its term untouched, at the string
    `{ π with ext := extOf D.a D.base.cfg tabs }`. `D.ok` is not asked: the equation holds where
    the description is nonsense too.
  `toBPrfX_ext`: what `Run.PQ.toBPrfX` returns is such a string, at `tabs := tabsX xs o`.
  `vxl_typed`: so at what `toBPrfX` returns, `VXL` is the run of `verifyOneProtocol` at that very string.
  `vxl_vxk`: there it is also the library's fast form `Run.PQ.VXK`.
  `tabsX_tabsOf`, `listedX_tabsOf`: `tabsX` is OnBytes/Tie/StoredExt.lean's `tabsOf`, and `listedX`
    at these tables is the list of which its `readOf` is the finite set.
`VXL` is the compiled verifier on a part of its domain; that part holds all that `toBPrfX` returns.

The library holds the finite list of a function's openings and its facts: Compile/Size.lean
(`EntE`, `entriesE`, `mem_entriesE`, `entriesE_injective`), Compile/Batch/Size.lean (`BT`, `encB`),
Compile/Batch/SizeO.lean (`entriesEO`, `BTO`, `encBO`).

What the equations do not say. The library's own limits hold here too (the heads of Run/PlanQX.lean
and Run/PlanQXRun.lean): the term is `verifyOneProtocol` at `(skeletonOverBothExternalStrings ..).up`, not `Compile.Batch.vLS`; the
oracle functions are `famX`, typed functions written by hand from the format, not one hash put in
through a coding with laws; `.det` sets every coin to 0; dec is any function; the protocol is made
from D; no soundness follows. Nor do the equations say that a run of `VXL` ends, or how fast it is,
or that the compiled code computes the term `VXL`: Lean's compiler is trusted in every run. The tie
is of the same kind as the library's `vx_eq` (Run/PlanQXRun.lean), no more.

-/
import OnBytes.RunA.ListedDefs
import OnBytes.Tie.StoredExt

set_option autoImplicit false

namespace OnBytes.RunA

open _root_.Run _root_.Run.PQ _root_.Run.Thin _root_.Run.Twin Iop Rom Compile Compile.Batch

/-- A wiring of the external strings, less its list of all positions. -/
def lessAll {E : ExtSpec} (we : WireE E) : WireELess E :=
  ⟨we.which, we.leaf, we.depth, we.build, we.dec, we.pr⟩

variable {I X : Type} {lam K : ℕ} (Lf : Unit → BatchProtocol I X)

/-- Walk 1: if openings stand at listed positions alone, the test at the listed positions is the
test at all. -/
theorem strictListed_eq {E : ExtSpec} (sMT : ℕ) (we : WireE E) (isRead : E.Pos → Bool)
    (f : E.Pos → Option (Opening lam E.Sym)) (listed : List E.Pos)
    (h2 : ∀ p, f p ≠ none → p ∈ listed) (h3 : ∀ p, p ∈ we.all) :
    strictListed sMT isRead f listed = strictExt sMT we isRead f := by
  unfold strictListed strictExt
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · intro h p _
    cases hf : f p with
    | none => rfl
    | some op =>
      have hp := h p (h2 p (by rw [hf]; exact Option.some_ne_none _))
      rw [hf] at hp
      exact hp
  · intro h p _
    exact h p (h3 p)

/-- Walk 2: the library's checks along a list are the checks along its read members. -/
theorem checksRead_filter {E : ExtSpec} (we : WireE E) (emb : E.Sym → Body (Lf ()))
    (cms : List (Dig lam)) (isRead : E.Pos → Bool) (f : E.Pos → Option (Opening lam E.Sym)) :
    ∀ ps : List E.Pos,
      extWP Lf we emb cms isRead f ps = checksRead Lf (lessAll we) emb cms f (ps.filter isRead)
  | [] => rfl
  | p :: ps => by
    have ih := checksRead_filter we emb cms isRead f ps
    cases h : isRead p with
    | true =>
      rw [List.filter_cons_of_pos h, extWP, if_pos h, checksRead, ih]
      rfl
    | false =>
      rw [List.filter_cons_of_neg (by rw [h]; exact Bool.false_ne_true), extWP,
        if_neg (by rw [h]; exact Bool.false_ne_true), ih]

theorem forestRead_eq {E : ExtSpec} (we : WireE E) (emb : E.Sym → Body (Lf ()))
    (cms : List (Dig lam)) (isRead : E.Pos → Bool) (f : E.Pos → Option (Opening lam E.Sym)) :
    forestRead Lf (lessAll we) emb cms f (we.all.filter isRead) =
      forestExtP Lf we emb cms isRead f := by
  unfold forestRead forestExtP
  rw [checksRead_filter]
  rfl

variable (g : Fam (spec lam K (Lf ()))) {Y : Type} {E : ExtSpec} (ord : Finset E.Pos → List E.Pos)

/-- **The form along the positions read and listed is the library's `verifyPR`**, under h1, h2
and h3. -/
theorem verifyPL_eq (early : X → X) (late : Option ℕ) (sMT sFS : ℕ) (t : Tag) (P : PS Y E)
    (wq : ProtocolQueryLayout lam K P.up) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ()))
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (xin : Y → Option X) (embE : E.Sym → Body (Lf ())) (depthReq : ℕ) (cms : List (Dig lam))
    (x : Y) (π : OneProtocolProof lam P.up) (listed : List E.Pos)
    (h1 : ∀ (R : Finset E.Pos) (isR : E.Pos → Bool), (∀ p, isR p = true ↔ p ∈ R) →
      ord R = wq.ext.all.filter isR)
    (h2 : ∀ p, π.ext p ≠ none → p ∈ listed) (h3 : ∀ p, p ∈ wq.ext.all) :
    verifyPL Lf g ord early late sMT sFS t P wq.sh wq.decO (lessAll wq.ext) wq.nOpen wq.maxDepth
        embS embP xin embE depthReq cms x π listed =
      verifyPR Lf g early late sMT sFS t P wq embS embP xin embE depthReq cms x π := by
  letI : DecidableEq E.Pos := wq.ext.dec
  have hs : ∀ ρ rts ph,
      strictPL sMT sFS P wq.sh wq.decO (lessAll wq.ext) depthReq x π listed ρ rts ph =
        strictP sMT sFS P wq depthReq x π ρ rts ph := by
    intro ρ rts ph
    unfold strictPL strictP sExtP
    dsimp only
    rw [← strictListed_eq sMT wq.ext _ π.ext listed h2 h3]
    rfl
  have hf : ∀ ρ rts,
      forestsOfL Lf ord P wq.sh (lessAll wq.ext) embS embE cms x π ρ rts =
        forestsOfR Lf P wq embS embE cms x π ρ rts := by
    intro ρ rts
    unfold forestsOfL forestsOfR
    dsimp only
    rw [h1 (P.extReads x ρ) (fun p => decide (p ∈ P.extReads x ρ)) (fun p => decide_eq_true_iff),
      forestRead_eq]
    rfl
  have ha : ∀ ρ rts ph,
      afterPL Lf g ord P wq.sh (lessAll wq.ext) wq.nOpen wq.maxDepth embS embE depthReq cms x π ρ
          rts ph =
        afterPR Lf g P wq embS embE depthReq cms x π ρ rts ph := by
    intro ρ rts ph
    unfold afterPL afterPR
    rw [hf]
    rfl
  unfold verifyPL verifyPR
  simp only [hs, ha]
  rfl

/-- The same, the wiring's pieces named one by one. -/
theorem verifyPL_pieces (early : X → X) (late : Option ℕ) (sMT sFS : ℕ) (t : Tag) (P : PS Y E)
    (wq : ProtocolQueryLayout lam K P.up) (sh : RoundsQueryLayout lam K (up P.S) P.ann)
    (decO : DecidableEq (OPos (up P.S))) (we : WireELess E) (nOpen maxDepth : ℕ)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ()))
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (xin : Y → Option X) (embE : E.Sym → Body (Lf ())) (depthReq : ℕ) (cms : List (Dig lam))
    (x : Y) (π : OneProtocolProof lam P.up) (listed : List E.Pos)
    (e1 : wq.sh = sh) (e2 : wq.decO = decO) (e3 : lessAll wq.ext = we) (e4 : wq.nOpen = nOpen)
    (e5 : wq.maxDepth = maxDepth)
    (h1 : ∀ (R : Finset E.Pos) (isR : E.Pos → Bool), (∀ p, isR p = true ↔ p ∈ R) →
      ord R = wq.ext.all.filter isR)
    (h2 : ∀ p, π.ext p ≠ none → p ∈ listed) (h3 : ∀ p, p ∈ wq.ext.all) :
    verifyPL Lf g ord early late sMT sFS t P sh decO we nOpen maxDepth
        embS embP xin embE depthReq cms x π listed =
      verifyPR Lf g early late sMT sFS t P wq embS embP xin embE depthReq cms x π := by
  subst e1 e2 e3 e4 e5
  exact verifyPL_eq Lf g ord early late sMT sFS t P wq embS embP xin embE depthReq cms x π listed
    h1 h2 h3

/-! ### The order of the positions read -/

/-- In a list that holds every member of α, strictly rising by a numbering with an inverse: the
members of a set, in the list's order, are the set's numbers, sorted, taken back. -/
theorem filter_eq_sorted {α : Type} (l : List α) (idx : α → ℕ) (back : ℕ → Option α)
    (hb : ∀ p, back (idx p) = some p) (hs : (l.map idx).Pairwise (· < ·)) (hc : ∀ p, p ∈ l)
    (R : Finset α) (isR : α → Bool) (hR : ∀ p, isR p = true ↔ p ∈ R) :
    ((R.image idx).sort (· ≤ ·)).filterMap back = l.filter isR := by
  have hsub : ((l.filter isR).map idx).Pairwise (· < ·) :=
    hs.sublist (List.filter_sublist.map idx)
  have e : (l.filter isR).map idx = (R.image idx).sort (· ≤ ·) := by
    refine List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (hsub.imp fun h => Nat.le_of_lt h)
      (Finset.pairwise_sort _ _) ?_
    refine (List.perm_ext_iff_of_nodup (hsub.imp fun h => Nat.ne_of_lt h)
      (Finset.sort_nodup _ _)).2 fun i => ?_
    rw [Finset.mem_sort, Finset.mem_image, List.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, (hR p).1 (List.mem_filter.1 hp).2, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, List.mem_filter.2 ⟨hc p, (hR p).2 hp⟩, rfl⟩
  rw [← e, List.filterMap_map]
  have : back ∘ idx = some := funext hb
  rw [this, List.filterMap_some]

theorem posOfNumber2_idx2 (n : ℕ) (p : Fin n ⊕ Fin n) : posOfNumber2 n (idx2 n p) = some p := by
  cases p with
  | inl q => simp [posOfNumber2, idx2, q.isLt]
  | inr q =>
    have h : ¬ (n + q.val < n) := by omega
    simp [posOfNumber2, idx2, h, q.isLt]

/-- The numbers of `WireE.two`'s list of all positions are 0, 1, .., 2 n - 1. -/
theorem all2_numbers (n : ℕ) (Sg : Type) (z : Sg) :
    (WireE.two n Sg z).all.map (idx2 n) = List.range (n + n) := by
  show ((List.finRange n).map Sum.inl ++ (List.finRange n).map Sum.inr).map (idx2 n) = _
  rw [List.map_append, List.map_map, List.map_map, List.range_add,
    ← List.map_coe_finRange_eq_range, List.map_map]
  rfl

theorem all2_complete (n : ℕ) (Sg : Type) (z : Sg) (p : Fin n ⊕ Fin n) :
    p ∈ (WireE.two n Sg z).all := by
  show p ∈ (List.finRange n).map Sum.inl ++ (List.finRange n).map Sum.inr
  cases p with
  | inl q => exact List.mem_append_left _ (List.mem_map.2 ⟨q, List.mem_finRange q, rfl⟩)
  | inr q => exact List.mem_append_right _ (List.mem_map.2 ⟨q, List.mem_finRange q, rfl⟩)

/-- **h1 at two strings.** -/
theorem order2 (n : ℕ) (Sg : Type) (z : Sg) (R : Finset (Fin n ⊕ Fin n)) (isR : Fin n ⊕ Fin n → Bool)
    (hR : ∀ p, isR p = true ↔ p ∈ R) :
    readsInOrder2 n R = (WireE.two n Sg z).all.filter isR :=
  filter_eq_sorted _ (idx2 n) (posOfNumber2 n) (posOfNumber2_idx2 n)
    (by rw [all2_numbers]; exact List.pairwise_lt_range) (all2_complete n Sg z) R isR hR

/-! ### The library's look-up has openings at listed positions alone -/

/-- **h2 at the library's look-up, for all tables.** -/
theorem extOf_listed (a : ℕ) (cfg : ByteArray) (tabs : List (Bool × OpenB × List (List (Dig 256))))
    (p : Fin (2 ^ a) ⊕ Fin (2 ^ a)) (h : extOf a cfg tabs p ≠ none) : p ∈ listedX a tabs := by
  obtain ⟨op, hop⟩ := Option.ne_none_iff_exists'.1 h
  rw [Tie.extOf_unfold] at hop
  obtain ⟨T, hT, hat⟩ := Option.bind_eq_some_iff.1 hop
  obtain ⟨c, s, pt, y, hm, -, -⟩ := Tie.atP_found _ _ _ _ _ _ hat
  refine List.mem_filterMap.2 ⟨(p.elim (fun _ => false) fun _ => true, p.elim (·.val) (·.val)),
    List.mem_flatMap.2 ⟨_, Tie.mem_of_lookup_some _ _ _ hT,
      List.mem_map.2 ⟨_, (List.of_mem_zip hm).1, rfl⟩⟩, Tie.xPos_back _ p⟩

/-! ### At a description with two stored tables -/

/-- **What runs is the run of the compiled verifier of one slot, at the typed string made of π and
the tables. No hypothesis.** -/
theorem vxl_eq (D : XD) (dec : View → Bool) (r0 r1 : ByteArray)
    (π : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up)
    (tabs : List (Bool × OpenB × List (List (Dig 256)))) :
    VXL D dec r0 r1 π tabs =
      (verifyOneProtocol (lam := 256) (K := D.K + 1) (L := D.L dec) (256 + 8 * D.base.plan.salt) 256 .link
          (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up
          (wqX D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec)
          (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
          (embPX D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, [])) (fun _ => some ()))
          (fun _ => none) (fun s => some (.inl s)) 0 [bytesToDig r0, bytesToDig r1] ()
          { π with ext := extOf D.a D.base.cfg tabs }).det
        (famX D dec _root_.Fmt.oracle (D.K + 1)) := by
  rw [← famXK_eq, ← thin_reads]
  unfold VXL
  exact verifyPL_pieces (fun _ => D.L dec) (famXK D dec (D.K + 1)) (readsInOrder2 (2 ^ D.a)) id none
    (256 + 8 * D.base.plan.salt) 256 .link (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec)
    (wqX D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec)
    (wire0S D.C D.K (chalP D.base.plan.field D.K), wiresSL D.C D.K (chalP D.base.plan.field D.K) D.ds)
    (decOS D.C D.ds) (weLessX D.a) (nOpen D.ds + (D.xs.map (·.count)).sum) (max (maxDepth D.ds) D.a)
    (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
    (embPX D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, [])) (fun _ => some ()))
    (fun _ => none) (fun s => some (.inl s)) 0 [bytesToDig r0, bytesToDig r1] ()
    { π with ext := extOf D.a D.base.cfg tabs } (listedX D.a tabs) rfl rfl rfl rfl rfl
    (order2 (2 ^ D.a) SgX (0, [])) (extOf_listed D.a D.base.cfg tabs)
    (all2_complete (2 ^ D.a) SgX (0, []))

/-- What the library's typing returns has the library's look-up in the tables `tabsX` as its
external openings. -/
theorem toBPrfX_ext (salt : ℕ) (cfg : ByteArray) (C : CK) (ds : List RD) (a : ℕ) (xs : List XO)
    (dec : View → Bool) (o : _root_.Fmt.ChainOut) (π : OneProtocolProof 256 (skeletonOverBothExternalStrings C ds a xs dec).up)
    (h : toBPrfX salt cfg C ds a xs dec o = some π) :
    { π with ext := extOf a cfg (tabsX xs o) } = π := by
  unfold toBPrfX at h
  split at h
  · obtain ⟨z, -, rfl⟩ := Option.map_eq_some_iff.1 h
    rfl
  · cases h

/-- **At what the library's typing returns, what runs is the run of the compiled verifier at that
very string.** -/
theorem vxl_typed (D : XD) (dec : View → Bool) (r0 r1 : ByteArray) (o : _root_.Fmt.ChainOut)
    (π : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up)
    (h : toBPrfX D.base.plan.salt D.base.cfg D.C D.ds D.a D.xs dec o = some π) :
    VXL D dec r0 r1 π (tabsX D.xs o) =
      (verifyOneProtocol (lam := 256) (K := D.K + 1) (L := D.L dec) (256 + 8 * D.base.plan.salt) 256 .link
          (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up
          (wqX D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec)
          (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
          (embPX D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, [])) (fun _ => some ()))
          (fun _ => none) (fun s => some (.inl s)) 0 [bytesToDig r0, bytesToDig r1] () π).det
        (famX D dec _root_.Fmt.oracle (D.K + 1)) := by
  rw [vxl_eq, toBPrfX_ext _ _ _ _ _ _ _ o π h]

/-- At what the library's typing returns, `VXL` is the library's fast form `VXK`. -/
theorem vxl_vxk (D : XD) (dec : View → Bool) (r0 r1 : ByteArray) (o : _root_.Fmt.ChainOut)
    (π : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up)
    (h : toBPrfX D.base.plan.salt D.base.cfg D.C D.ds D.a D.xs dec o = some π) :
    VXL D dec r0 r1 π (tabsX D.xs o) = VXK D dec r0 r1 π := by
  rw [vxl_typed D dec r0 r1 o π h, vxk_eq, vx_eq]

/-! ### The library's own names for the tables and the listed positions -/

/-- The tables are OnBytes/Tie/StoredExt.lean's. -/
theorem tabsX_tabsOf (xs : List XO) (o : _root_.Fmt.ChainOut) : tabsX xs o = Tie.tabsOf (storedB xs o) :=
  rfl

/-- At these tables the listed positions are the list of which OnBytes/Tie/StoredExt.lean's
`readOf` is the finite set. -/
theorem listedX_tabsOf (a : ℕ) (sto : List (Bool × ℕ × OpenB)) :
    listedX a (Tie.tabsOf sto) = (Tie.askedOf sto).filterMap (xPos (2 ^ a)) := by
  unfold listedX Tie.tabsOf Tie.askedOf
  rw [List.flatMap_map]

end OnBytes.RunA

#print axioms OnBytes.RunA.verifyPL_eq
#print axioms OnBytes.RunA.order2
#print axioms OnBytes.RunA.extOf_listed
#print axioms OnBytes.RunA.vxl_eq
#print axioms OnBytes.RunA.toBPrfX_ext
#print axioms OnBytes.RunA.vxl_typed
#print axioms OnBytes.RunA.vxl_vxk
#print axioms OnBytes.RunA.tabsX_tabsOf
#print axioms OnBytes.RunA.listedX_tabsOf
-- the definitions, beside the library's own fast form
#print axioms OnBytes.RunA.VXL
#print axioms OnBytes.RunA.verifyPL
#print axioms OnBytes.RunA.readsInOrder2
#print axioms Run.PQ.VXK
