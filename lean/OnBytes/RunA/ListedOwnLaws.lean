-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/RunA/ListedOwnLaws.lean: what the form along the positions read and listed in every tree
is. The definitions are in OnBytes/RunA/ListedOwnDefs.lean. The file builds on
OnBytes/RunA/ListedLaws.lean.

Theorems.
  `verifyPLO_eq`: for any skeleton `PS`, rounds' wiring, oracle functions and typed string,
    `verifyPLO` at `lessS` of a wiring is `verifyPL` (not yet `verifyOneProtocol`) at that wiring, under two
    hypotheses: `LeavesOK` (the two functions "leaves of a set" give the tree's leaves, filtered by
    "the leaf's position is in the set", in rising order) and `ListedOK` (an opening stands only at
    positions of listed leaves).
  `leaves_SL`: `LeavesOK` at a description's rounds.
  `listed_SL`: `ListedOK` at the library's look-up `atTT`, for all tables.
  `vxlo_eq`: without a hypothesis, for all D, dec, r0, r1, π, otabs, tabs:
    `VXLO D dec r0 r1 π otabs tabs` is the run of the library's `Compile.Batch.verifyOneProtocol`, its term
    untouched, at `{ π with opens := opensOfX .. otabs, ext := extOf .. tabs }`.
  `toBPrfX_both`: what `Run.PQ.toBPrfX` returns is such a string, at `otabs := otabsX xs o` and
    `tabs := tabsX xs o`.
  `vxlo_typed`: so at what `toBPrfX` returns, `VXLO` is the run of `verifyOneProtocol` at that very string.
  `vxlo_vxk`: there it is also the library's fast form `Run.PQ.VXK`.
`VXLO` is the compiled verifier on a part of its domain; that part holds all that `toBPrfX`
returns. What the equations do not say is listed in ListedLaws.lean's head, and holds of `VXLO` as
of `VXL`.

-/
import OnBytes.RunA.ListedOwnDefs
import OnBytes.RunA.ListedLaws

set_option autoImplicit false

namespace OnBytes.RunA

open _root_.Run _root_.Run.PQ _root_.Run.Thin _root_.Run.Twin Iop Rom Compile Compile.Batch

/-! ### From the library's wiring of the rounds to the lesser one -/

/-- Round by round, two functions: the leaves of a set of positions in the round's two trees. -/
def LeavesS : List RS → Type
  | [] => Unit
  | r :: S => ((Finset r.Pos → List ℕ) × (Finset r.Pos → List ℕ)) × LeavesS S

def lessR {lam K : ℕ} {r : RS} {a : RAnn r.up} (w : WireRB lam K r.up a)
    (lv : (Finset r.Pos → List ℕ) × (Finset r.Pos → List ℕ)) : WireRLess lam K r :=
  ⟨w.pt.decPos, w.pt.ofSyms, w.pt.zero, w.depth0, w.depthJ, w.has0, w.hasJ, w.posAt0, w.posAtJ,
    w.chal, w.pr0, w.prJ, lv.1, lv.2⟩

def lessS {lam K : ℕ} :
    (S : List RS) → (A : RoundSplits (up S)) → RoundsQueryLayout lam K (up S) A → LeavesS S → WireSLess lam K S
  | [], _, _, _ => ()
  | _ :: S, (_, A), (w, W), (lv, LV) => (lessR w lv, lessS S A W LV)

/-- Is the leaf j the leaf of a position that `isR` accepts? -/
def keepAt {α : Type} (posAt : ℕ → Option α) (isR : α → Bool) (j : ℕ) : Bool :=
  match posAt j with
  | some p => isR p
  | none => false

/-- Each function "leaves of a set" gives the tree's leaves whose position is in the set, in rising
order. -/
def LeavesOK {lam K : ℕ} :
    (S : List RS) → (A : RoundSplits (up S)) → RoundsQueryLayout lam K (up S) A → LeavesS S → Prop
  | [], _, _, _ => True
  | r :: S, (_, A), (w, W), (lv, LV) =>
    (∀ (R0 : Finset r.Pos) (isR : r.Pos → Bool), (∀ p, isR p = true ↔ p ∈ R0) →
      lv.1 R0 = (List.range (2 ^ w.depth0)).filter (keepAt w.posAt0 isR) ∧
      lv.2 R0 = (List.range (2 ^ w.depthJ)).filter (keepAt w.posAtJ isR)) ∧
    LeavesOK S A W LV

/-- An opening stands only at positions of listed leaves. -/
def ListedOK {lam K : ℕ} :
    (S : List RS) → (A : RoundSplits (up S)) → RoundsQueryLayout lam K (up S) A →
    ((p : OPos (up S)) → Option (Opening lam (OSym (up S) p))) → List (List ℕ × List ℕ) → Prop
  | [], _, _, _, _ => True
  | r :: S, (_, A), (w, W), f, ls =>
    (∀ (j : ℕ) (p : r.Pos), w.posAt0 j = some p → f (.inl p) ≠ none → j ∈ (ls.headD ([], [])).1) ∧
    (∀ (j : ℕ) (p : r.Pos), w.posAtJ j = some p → f (.inl p) ≠ none → j ∈ (ls.headD ([], [])).2) ∧
    ListedOK S A W (fun p => f (.inr p)) ls.tail

variable {I X : Type} {lam K : ℕ} (Lf : Unit → BatchProtocol I X)

/-! ### The strict format -/

theorem all_range_eq (n : ℕ) (B : ℕ → Bool) (js : List ℕ)
    (h : ∀ j, j < n → B j = false → j ∈ js) :
    (js.all fun j => !decide (j < n) || B j) = (List.range n).all B := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · intro H j hj
    have hlt : j < n := List.mem_range.1 hj
    cases hB : B j with
    | true => rfl
    | false =>
      have := H j (h j hlt hB)
      simp [hlt, hB] at this
  · intro H j _
    by_cases hlt : j < n
    · simp [H j (List.mem_range.2 hlt)]
    · simp [hlt]

theorem sCompL_eq (sMT : ℕ) (r : RS) (posAt : ℕ → Option r.Pos) (depth : ℕ) (hasRoot : Bool)
    (isRead : r.Pos → Bool) (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) (js : List ℕ)
    (h : ∀ j p, posAt j = some p → f p ≠ none → j ∈ js) :
    sCompL sMT r posAt depth hasRoot isRead f js =
      sCompP sMT r posAt depth hasRoot isRead f := by
  unfold sCompL sCompP
  refine all_range_eq _ _ js fun j _ hB => ?_
  split at hB
  · cases hB
  · rename_i p hp
    split at hB
    · cases hB
    · rename_i op hf
      exact h j p hp (by rw [hf]; exact Option.some_ne_none _)

theorem sSL_eq (sMT : ℕ) :
    ∀ (S : List RS) (A : RoundSplits (up S)) (W : RoundsQueryLayout lam K (up S) A) (LV : LeavesS S)
      (rts : RootsOfChain lam (up S)) (isRead : OPos (up S) → Bool)
      (f : (p : OPos (up S)) → Option (Opening lam (OSym (up S) p))) (ls : List (List ℕ × List ℕ)),
      ListedOK S A W f ls →
      sSL sMT S (lessS S A W LV) rts isRead f ls = sSP sMT S A W rts isRead f
  | [], _, _, _, _, _, _, _, _ => rfl
  | r :: S, (a, A), (w, W), (lv, LV), (rt, rts), isRead, f, ls, h => by
    have ih := sSL_eq sMT S A W LV rts (fun p => isRead (.inr p)) (fun p => f (.inr p)) ls.tail h.2.2
    have e0 := sCompL_eq sMT r w.posAt0 w.depth0 rt.1.join.isSome (fun p => isRead (.inl p))
      (fun p => f (.inl p)) (ls.headD ([], [])).1 h.1
    have eJ := sCompL_eq sMT r w.posAtJ w.depthJ rt.2.join.isSome (fun p => isRead (.inl p))
      (fun p => f (.inl p)) (ls.headD ([], [])).2 h.2.1
    show (sCompL sMT r w.posAt0 w.depth0 rt.1.join.isSome (fun p => isRead (.inl p))
          (fun p => f (.inl p)) (ls.headD ([], [])).1 &&
        sCompL sMT r w.posAtJ w.depthJ rt.2.join.isSome (fun p => isRead (.inl p))
          (fun p => f (.inl p)) (ls.headD ([], [])).2 &&
        sSL sMT S (lessS S A W LV) rts (fun p => isRead (.inr p)) (fun p => f (.inr p)) ls.tail) = _
    rw [e0, eJ, ih]
    rfl

/-! ### The checks -/

theorem compP_filter (r : RS) (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body (Lf ())) (rt : Dig lam) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ js : List ℕ, compP Lf r posAt depth emb rt isRead f (js.filter (keepAt posAt isRead)) =
      compP Lf r posAt depth emb rt isRead f js
  | [] => rfl
  | j :: js => by
    have ih := compP_filter r posAt depth emb rt isRead f js
    cases hp : posAt j with
    | none =>
      have hk : ¬ keepAt posAt isRead j = true := by simp [keepAt, hp]
      rw [List.filter_cons_of_neg hk, ih]
      simp only [compP, hp]
    | some p =>
      cases hr : isRead p with
      | true =>
        have hk : keepAt posAt isRead j = true := by simp [keepAt, hp, hr]
        rw [List.filter_cons_of_pos hk]
        simp only [compP, hp, hr, if_true, ih]
      | false =>
        have hk : ¬ keepAt posAt isRead j = true := by simp [keepAt, hp, hr]
        rw [List.filter_cons_of_neg hk, ih]
        simp [compP, hp, hr]

theorem optL_eq (r : RS) (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body (Lf ())) (rt : Option (Dig lam)) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) (js : List ℕ)
    (h : js = (List.range (2 ^ depth)).filter (keepAt posAt isRead)) :
    optL Lf r posAt depth emb rt isRead f js = optP Lf r posAt depth emb rt isRead f := by
  unfold optL optP
  cases rt with
  | none => rfl
  | some c => exact h ▸ compP_filter Lf r posAt depth emb c isRead f _

theorem forestsL_eq :
    ∀ (S : List RS) (A : RoundSplits (up S)) (W : RoundsQueryLayout lam K (up S) A) (LV : LeavesS S)
      (emb : (p : OPos (up S)) → OSym (up S) p → Body (Lf ())) (rts : RootsOfChain lam (up S))
      (R : Finset (OPos (up S))) (f : (p : OPos (up S)) → Option (Opening lam (OSym (up S) p))),
      LeavesOK S A W LV →
      forestsL Lf S (lessS S A W LV) emb rts R f = forestsR Lf S A W emb rts R f
  | [], _, _, _, _, _, _, _, _ => rfl
  | r :: S, (a, A), (w, W), (lv, LV), emb, (rt, rts), R, f, h => by
    letI : DecidableEq r.Pos := w.pt.decPos
    have ih := forestsL_eq S A W LV (fun p => emb (.inr p)) rts
      (tailR (α := r.Pos) (β := OPos (up S)) R) (fun p => f (.inr p)) h.2
    have hl := h.1 (headR (α := r.Pos) (β := OPos (up S)) R)
      (fun p => decide (p ∈ headR (α := r.Pos) (β := OPos (up S)) R)) (fun p => decide_eq_true_iff)
    have e0 := optL_eq Lf r w.posAt0 w.depth0 (fun p => emb (.inl p)) rt.1.join
      (fun p => decide (p ∈ headR (α := r.Pos) (β := OPos (up S)) R)) (fun p => f (.inl p)) _ hl.1
    have eJ := optL_eq Lf r w.posAtJ w.depthJ (fun p => emb (.inl p)) rt.2.join
      (fun p => decide (p ∈ headR (α := r.Pos) (β := OPos (up S)) R)) (fun p => f (.inl p)) _ hl.2
    simp only [forestsL, forestsR, lessS, lessR]
    rw [e0, eJ, ih]
    rfl

/-! ### The transcript and the chain -/

theorem trL_eq :
    ∀ (S : List RS) (A : RoundSplits (up S)) (W : RoundsQueryLayout lam K (up S) A) (LV : LeavesS S)
      (rts : RootsOfChain lam (up S)) (pls : Plains (up S)) (ρ : Rho (up S))
      (f : (p : OPos (up S)) → Option (Opening lam (OSym (up S) p))),
      trL S A (lessS S A W LV) rts pls ρ f = trP S A W rts pls ρ f
  | [], _, _, _, _, _, _, _ => rfl
  | r :: S, (a, A), (w, W), (lv, LV), (rt, rts), (pl, pls), (c, ρ), f => by
    have ih := trL_eq S A W LV rts pls ρ (fun p => f (.inr p))
    simp only [trL, trP, lessS, lessR, ih]
    rfl

variable (g : Fam (spec lam K (Lf ())))

theorem chainL_eq (early : X → X) (late : Option ℕ) (t : Tag) (cms : List (Dig lam)) (x : Option X)
    (salt : Bits) (rtreq : Dig lam) :
    ∀ (S : List RS) (A : RoundSplits (up S)) (W : RoundsQueryLayout lam K (up S) A) (LV : LeavesS S)
      (embP : PlainPart (up S) A → PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t)) (i : ℕ) (ph : Phase lam)
      (rts : List (Dig lam)) (pls : Plains (up S)),
      chainL Lf g early late t cms x salt rtreq S A (lessS S A W LV) embP i ph rts pls =
        _root_.Run.Thin.chainP Lf g early late t cms x salt rtreq S A W embP i ph rts pls
  | [], _, _, _, _, _, _, _, _ => rfl
  | r :: S, (a, A), (w, W), (lv, LV), embP, i, ph, rts, (pl, pls) => by
    have ih := chainL_eq early late t cms x salt rtreq S A W LV
    simp only [chainL, _root_.Run.Thin.chainP, lessS, lessR, ih]
    rfl

/-! ### The verifier -/

variable {Y : Type} {E : ExtSpec} (ord : Finset E.Pos → List E.Pos)

/-- **The form along the lists in every tree is the form along the lists in the external strings**,
under `LeavesOK` and `ListedOK`. -/
theorem verifyPLO_eq (early : X → X) (late : Option ℕ) (sMT sFS : ℕ) (t : Tag) (P : PS Y E)
    (sh : RoundsQueryLayout lam K (up P.S) P.ann) (LV : LeavesS P.S) (decO : DecidableEq (OPos (up P.S)))
    (we : WireELess E) (nOpen maxDepth : ℕ)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ()))
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (xin : Y → Option X) (embE : E.Sym → Body (Lf ())) (depthReq : ℕ) (cms : List (Dig lam))
    (x : Y) (π : OneProtocolProof lam P.up) (listed : List E.Pos) (own : List (List ℕ × List ℕ))
    (hl : LeavesOK P.S P.ann sh LV) (ho : ListedOK P.S P.ann sh π.opens own) :
    verifyPLO Lf g ord early late sMT sFS t P (lessS P.S P.ann sh LV) decO we nOpen maxDepth
        embS embP xin embE depthReq cms x π listed own =
      verifyPL Lf g ord early late sMT sFS t P sh decO we nOpen maxDepth
        embS embP xin embE depthReq cms x π listed := by
  have hs : ∀ ρ rts ph,
      strictPLO sMT sFS P (lessS P.S P.ann sh LV) decO we depthReq x π listed own ρ rts ph =
        strictPL sMT sFS P sh decO we depthReq x π listed ρ rts ph := by
    intro ρ rts ph
    unfold strictPLO strictPL
    dsimp only
    rw [sSL_eq sMT P.S P.ann sh LV rts _ π.opens own ho]
  have hf : ∀ ρ rts,
      forestsOfLO Lf ord P (lessS P.S P.ann sh LV) we embS embE cms x π ρ rts =
        forestsOfL Lf ord P sh we embS embE cms x π ρ rts := by
    intro ρ rts
    unfold forestsOfLO forestsOfL
    dsimp only
    rw [forestsL_eq Lf P.S P.ann sh LV embS rts _ π.opens hl]
    rfl
  have ha : ∀ ρ rts ph,
      afterPLO Lf g ord P (lessS P.S P.ann sh LV) we nOpen maxDepth embS embE depthReq cms x π ρ
          rts ph =
        afterPL Lf g ord P sh we nOpen maxDepth embS embE depthReq cms x π ρ rts ph := by
    intro ρ rts ph
    unfold afterPLO afterPL
    rw [hf, trL_eq]
    rfl
  unfold verifyPLO verifyPL
  rw [chainL_eq]
  simp only [hs, ha]
  rfl

/-! ### At a description's rounds -/

/-- Two lists of numbers, both rising strictly, with the same members, are one list. -/
theorem eq_of_rising {l₁ l₂ : List ℕ} (h₁ : l₁.Pairwise (· < ·)) (h₂ : l₂.Pairwise (· ≤ ·))
    (n₂ : l₂.Nodup) (h : ∀ j, j ∈ l₁ ↔ j ∈ l₂) : l₁ = l₂ :=
  List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (h₁.imp fun h => Nat.le_of_lt h) h₂
    ((List.perm_ext_iff_of_nodup (h₁.imp fun h => Nat.ne_of_lt h) n₂).2 h)

/-- The leaves of a set of positions of a round's tree. -/
def leavesOfTree (tree : Option _root_.Fmt.Shape) (R : Finset (Fin (posN tree))) : List ℕ :=
  ((R.image fun p => p.val).sort (· ≤ ·)).filter fun j => decide (j < 2 ^ depthOf tree)

theorem leavesOfTree_eq (tree : Option _root_.Fmt.Shape) (R : Finset (Fin (posN tree)))
    (isR : Fin (posN tree) → Bool) (hR : ∀ p, isR p = true ↔ p ∈ R) :
    leavesOfTree tree R = (List.range (2 ^ depthOf tree)).filter
      (keepAt (fun j => if h : j < posN tree then some (⟨j, h⟩ : Fin (posN tree)) else none) isR) := by
  symm
  refine eq_of_rising (List.pairwise_lt_range.filter _) ((Finset.pairwise_sort _ _).filter _)
    ((Finset.sort_nodup _ _).filter _) fun j => ?_
  unfold keepAt leavesOfTree
  rw [List.mem_filter, List.mem_filter, List.mem_range, Finset.mem_sort, Finset.mem_image,
    decide_eq_true_iff]
  constructor
  · rintro ⟨hj, hk⟩
    refine ⟨?_, hj⟩
    by_cases h : j < posN tree
    · have hk' : isR ⟨j, h⟩ = true := by simpa [h] using hk
      exact ⟨⟨j, h⟩, (hR _).1 hk', rfl⟩
    · simp [h] at hk
  · rintro ⟨⟨p, hp, rfl⟩, hj⟩
    refine ⟨hj, ?_⟩
    simpa [p.isLt] using (hR p).2 hp

def leavesSL (C : CK) : (ds : List RD) → LeavesS (SL C ds)
  | [] => ()
  | d :: ds => ((fun _ => [], leavesOfTree d.tree), leavesSL C ds)

theorem lessS_SL (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) :
    ∀ ds : List RD, lessS (SL C ds) (Twin.allLo (SL C ds)) (wiresSL C K chal ds) (leavesSL C ds) =
      wiresLessSL C K chal ds
  | [] => rfl
  | d :: ds => by
    show (lessR (wireS C K chal d) ((fun _ => [], leavesOfTree d.tree)),
        lessS (SL C ds) (Twin.allLo (SL C ds)) (wiresSL C K chal ds) (leavesSL C ds)) =
      (wireLessS C K chal d, wiresLessSL C K chal ds)
    rw [lessS_SL C K chal ds]
    rfl

/-- **`LeavesOK` at a description's rounds.** -/
theorem leaves_SL (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) :
    ∀ ds : List RD, LeavesOK (SL C ds) (Twin.allLo (SL C ds)) (wiresSL C K chal ds) (leavesSL C ds)
  | [] => trivial
  | d :: ds => ⟨fun R0 isR hR => ⟨rfl, leavesOfTree_eq d.tree R0 isR hR⟩, leaves_SL C K chal ds⟩

/-- A look-up in the tables of all trees finds something only at a place that the tree's first
table lists. -/
theorem atTT_listed {σ : Type} (sym : List UInt64 → Option σ) (otabs : List (Nat × List (Nat × Row3)))
    (t x : Nat) (h : atTT sym otabs t x ≠ none) :
    x ∈ ((otabs.lookup t).getD []).map Prod.fst := by
  unfold atTT atT at h
  cases ht : otabs.lookup t with
  | none => simp [ht] at h
  | some tab =>
    cases hx : tab.lookup x with
    | none => simp [ht, hx] at h
    | some v => exact List.mem_map.2 ⟨(x, v), Tie.mem_of_lookup_some _ _ _ hx, rfl⟩

/-- **`ListedOK` at the library's look-up, for all tables.** -/
theorem listed_SL (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (otabs : List (Nat × List (Nat × Row3))) :
    ∀ ds : List RD, ListedOK (SL C ds) (Twin.allLo (SL C ds)) (wiresSL C K chal ds)
      (fun q => atTT (symSL C ds q) otabs (placeSL C ds q).1 (placeSL C ds q).2)
      (ds.map fun d => ([], ((otabs.lookup (trNo d.tree)).getD []).map Prod.fst))
  | [] => trivial
  | d :: ds => by
    refine ⟨fun j p hp _ => (by cases hp), fun j p hp hf => ?_, listed_SL C K chal otabs ds⟩
    have hj : j = p.val := by
      have hp' : (if h : j < posN d.tree then some (⟨j, h⟩ : Fin (posN d.tree)) else none) = some p := hp
      by_cases h : j < posN d.tree
      · rw [dif_pos h] at hp'
        exact congrArg Fin.val (Option.some.inj hp')
      · rw [dif_neg h] at hp'
        cases hp'
    rw [hj]
    exact atTT_listed _ otabs (trNo d.tree) p.val hf

/-! ### At a description with two stored tables -/

/-- **What runs is the run of the compiled verifier of one slot, at the typed string made of π and
the tables. No hypothesis.** -/
theorem vxlo_eq (D : XD) (dec : View → Bool) (r0 r1 : ByteArray)
    (π : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up)
    (otabs : List (Nat × List (Nat × Row3)))
    (tabs : List (Bool × OpenB × List (List (Dig 256)))) :
    VXLO D dec r0 r1 π otabs tabs =
      (verifyOneProtocol (lam := 256) (K := D.K + 1) (L := D.L dec) (256 + 8 * D.base.plan.salt) 256 .link
          (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up
          (wqX D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec)
          (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
          (embPX D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, [])) (fun _ => some ()))
          (fun _ => none) (fun s => some (.inl s)) 0 [bytesToDig r0, bytesToDig r1] ()
          { π with
            opens := opensOfX D.base.plan.salt D.C D.ds D.a D.xs dec otabs
            ext := extOf D.a D.base.cfg tabs }).det
        (famX D dec _root_.Fmt.oracle (D.K + 1)) := by
  have e := vxl_eq D dec r0 r1
    { π with opens := opensOfX D.base.plan.salt D.C D.ds D.a D.xs dec otabs } tabs
  refine Eq.trans ?_ e
  unfold VXLO VXL
  have hw : ((wire0Less D.C D.K (chalP D.base.plan.field D.K),
        wiresLessSL D.C D.K (chalP D.base.plan.field D.K) D.ds) :
        WireSLess 256 (D.K + 1) (SOf D.C D.ds)) =
      lessS (SOf D.C D.ds) (Twin.allLo (SOf D.C D.ds))
        (wire0S D.C D.K (chalP D.base.plan.field D.K),
          wiresSL D.C D.K (chalP D.base.plan.field D.K) D.ds)
        (((fun _ => [], fun _ => []), leavesSL D.C D.ds) : LeavesS (SOf D.C D.ds)) := by
    show _ = (lessR (wire0S D.C D.K (chalP D.base.plan.field D.K)) ((fun _ => [], fun _ => [])),
      lessS (SL D.C D.ds) (Twin.allLo (SL D.C D.ds))
        (wiresSL D.C D.K (chalP D.base.plan.field D.K) D.ds) (leavesSL D.C D.ds))
    rw [lessS_SL]
    rfl
  rw [hw]
  exact verifyPLO_eq (fun _ => D.L dec) (famXK D dec (D.K + 1)) (readsInOrder2 (2 ^ D.a)) id none
    (256 + 8 * D.base.plan.salt) 256 .link (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec)
    (wire0S D.C D.K (chalP D.base.plan.field D.K), wiresSL D.C D.K (chalP D.base.plan.field D.K) D.ds)
    (((fun _ => [], fun _ => []), leavesSL D.C D.ds) : LeavesS (SOf D.C D.ds))
    (decOS D.C D.ds) (weLessX D.a) (nOpen D.ds + (D.xs.map (·.count)).sum) (max (maxDepth D.ds) D.a)
    (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
    (embPX D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, [])) (fun _ => some ()))
    (fun _ => none) (fun s => some (.inl s)) 0 [bytesToDig r0, bytesToDig r1] ()
    { π with
      opens := opensOfX D.base.plan.salt D.C D.ds D.a D.xs dec otabs
      ext := extOf D.a D.base.cfg tabs }
    (listedX D.a tabs) (ownListedX D.ds otabs)
    ⟨fun _ _ _ => ⟨rfl, rfl⟩, leaves_SL D.C D.K (chalP D.base.plan.field D.K) D.ds⟩
    ⟨fun _ p _ _ => p.elim, fun _ p _ _ => p.elim,
      listed_SL D.C D.K (chalP D.base.plan.field D.K) otabs D.ds⟩

/-- What the library's typing returns has the library's two look-ups, in the tables `otabsX` and
`tabsX`, as its openings. -/
theorem toBPrfX_both (salt : ℕ) (cfg : ByteArray) (C : CK) (ds : List RD) (a : ℕ) (xs : List XO)
    (dec : View → Bool) (o : _root_.Fmt.ChainOut) (π : OneProtocolProof 256 (skeletonOverBothExternalStrings C ds a xs dec).up)
    (h : toBPrfX salt cfg C ds a xs dec o = some π) :
    { π with
      opens := opensOfX salt C ds a xs dec (otabsX xs o)
      ext := extOf a cfg (tabsX xs o) } = π := by
  unfold toBPrfX at h
  split at h
  · obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 h
    unfold toBPrfP at hz
    split at hz
    · rename_i run pl hrun hpl
      split at hz
      · cases hz
        have hr : o.run = some run := hrun
        unfold otabsX
        rw [hr]
        rfl
      · cases hz
    · cases hz
  · cases h

/-- **At what the library's typing returns, what runs is the run of the compiled verifier at that
very string.** -/
theorem vxlo_typed (D : XD) (dec : View → Bool) (r0 r1 : ByteArray) (o : _root_.Fmt.ChainOut)
    (π : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up)
    (h : toBPrfX D.base.plan.salt D.base.cfg D.C D.ds D.a D.xs dec o = some π) :
    VXLO D dec r0 r1 π (otabsX D.xs o) (tabsX D.xs o) =
      (verifyOneProtocol (lam := 256) (K := D.K + 1) (L := D.L dec) (256 + 8 * D.base.plan.salt) 256 .link
          (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up
          (wqX D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec)
          (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
          (embPX D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, [])) (fun _ => some ()))
          (fun _ => none) (fun s => some (.inl s)) 0 [bytesToDig r0, bytesToDig r1] () π).det
        (famX D dec _root_.Fmt.oracle (D.K + 1)) := by
  rw [vxlo_eq, toBPrfX_both _ _ _ _ _ _ _ o π h]

/-- At what the library's typing returns, `VXLO` is the library's fast form `VXK`. -/
theorem vxlo_vxk (D : XD) (dec : View → Bool) (r0 r1 : ByteArray) (o : _root_.Fmt.ChainOut)
    (π : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up)
    (h : toBPrfX D.base.plan.salt D.base.cfg D.C D.ds D.a D.xs dec o = some π) :
    VXLO D dec r0 r1 π (otabsX D.xs o) (tabsX D.xs o) = VXK D dec r0 r1 π := by
  rw [vxlo_typed D dec r0 r1 o π h, vxk_eq, vx_eq]

end OnBytes.RunA

#print axioms OnBytes.RunA.verifyPLO_eq
#print axioms OnBytes.RunA.leaves_SL
#print axioms OnBytes.RunA.listed_SL
#print axioms OnBytes.RunA.vxlo_eq
#print axioms OnBytes.RunA.toBPrfX_both
#print axioms OnBytes.RunA.vxlo_typed
#print axioms OnBytes.RunA.vxlo_vxk
-- the definitions
#print axioms OnBytes.RunA.VXLO
#print axioms OnBytes.RunA.verifyPLO
#print axioms OnBytes.RunA.wiresLessSL
