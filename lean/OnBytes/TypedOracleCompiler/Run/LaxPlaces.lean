-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/LaxPlaces.lean: a form, for evaluation, of the lax verifier along a short list
(`verifyLXL`, OnBytes/TypedOracleCompiler/Run/LaxShort.lean): it makes each
tree's checks along the list of that tree's leaves that are read, not along all leaves.

What is not claimed. Nothing where the four laws fail: no test at run time guards the lists (unlike
`verifyLXL`'s list of external positions); at such a wire `checksRQ` may make fewer checks than
`checksR`, so `verifyLXLQ` may say yes where `verifyLXL` says no.

What this file states, assumes and does not show, its terms and its limits in full: the comment on
`verifyLXLQ_eq` (the four laws: `PlaceOK`).

-/
import OnBytes.TypedOracleCompiler.Run.LaxShort

set_option autoImplicit false

namespace TypedOracleCompiler.Run.Thin
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.Thin

variable {I X : Type} {lam K : ℕ} (Lf : Unit → BatchProtocolWithLeafBody I X)

/-! ### One component of one round -/

/-- Does a read position stand at leaf j? -/
def keepP (r : RS) (posAt : ℕ → Option r.Pos) (isRead : r.Pos → Bool) (j : ℕ) : Bool :=
  match posAt j with
  | some p => isRead p
  | none => false

/-- `compP` takes of a list of leaves those alone at which a read position stands. -/
theorem compP_filter (r : RS) (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body (Lf ())) (rt : Dig lam) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) (js : List ℕ) :
    compP Lf r posAt depth emb rt isRead f (js.filter (keepP r posAt isRead)) =
      compP Lf r posAt depth emb rt isRead f js := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    by_cases hk : keepP r posAt isRead j = true
    · rw [List.filter_cons_of_pos hk, compP, compP, ih]
    · rw [List.filter_cons_of_neg hk, ih]
      conv_rhs => rw [compP]
      unfold keepP at hk
      cases hp : posAt j with
      | none => rfl
      | some p =>
        simp only [hp] at hk
        simp only [hk]
        rfl

/-- `treesP` along a list of leaves for each tree. -/
def treesPQ (r : RS) (posAt : ℕ → ℕ → Option r.Pos)
    (emb : (p : r.Pos) → r.Sym p → Body (Lf ())) (isRead : r.Pos → Bool)
    (places : ℕ → ℕ → List ℕ) (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ℕ → List ℕ → List (Dig lam) → Option (List (ℕ × Dig lam × List (Check lam (Lf ()))))
  | k, d :: ds, c :: cs =>
      match compP Lf r (posAt k) d emb c isRead f (places k d),
        treesPQ r posAt emb isRead places f (k + 1) ds cs with
      | some a, some b => some ((d, c, a) :: b)
      | _, _ => none
  | _, _, _ => some []

/-- It is `treesP`, where each list is that of all leaves with those kept at which a read position
stands. -/
theorem treesPQ_eq (r : RS) (posAt : ℕ → ℕ → Option r.Pos)
    (emb : (p : r.Pos) → r.Sym p → Body (Lf ())) (isRead : r.Pos → Bool)
    (places : ℕ → ℕ → List ℕ) (f : (p : r.Pos) → Option (Opening lam (r.Sym p)))
    (h : ∀ k d, places k d = (List.range (2 ^ d)).filter (keepP r (posAt k) isRead))
    (ds : List ℕ) :
    ∀ (k : ℕ) (cs : List (Dig lam)),
      treesPQ Lf r posAt emb isRead places f k ds cs = treesP Lf r posAt emb isRead f k ds cs := by
  induction ds with
  | nil => intro k cs; simp only [treesPQ, treesP]
  | cons d ds ih =>
    intro k cs
    cases cs with
    | nil => simp only [treesPQ, treesP]
    | cons c cs =>
      simp only [treesPQ, treesP, h, compP_filter, ih]
      rfl

/-- `optP` along a list of leaves for each tree. -/
def optPQ (r : RS) (posAt : ℕ → ℕ → Option r.Pos) (depth : List ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body (Lf ())) (rt : List (Dig lam)) (isRead : r.Pos → Bool)
    (places : ℕ → ℕ → List ℕ) (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    Option (List (Check lam (Lf ()))) :=
  (treesPQ Lf r posAt emb isRead places f 0 depth rt).map fun l => l.flatMap fun z => z.2.2

/-- It is `optP`, under the same condition. -/
theorem optPQ_eq (r : RS) (posAt : ℕ → ℕ → Option r.Pos) (depth : List ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body (Lf ())) (rt : List (Dig lam)) (isRead : r.Pos → Bool)
    (places : ℕ → ℕ → List ℕ) (f : (p : r.Pos) → Option (Opening lam (r.Sym p)))
    (h : ∀ k d, places k d = (List.range (2 ^ d)).filter (keepP r (posAt k) isRead)) :
    optPQ Lf r posAt depth emb rt isRead places f = optP Lf r posAt depth emb rt isRead f := by
  unfold optPQ optP
  rw [treesPQ_eq Lf r posAt emb isRead places f h]

/-! ### The lists -/

/-- The places below 2 ^ d of the members of R that lie in the component b and in tree k: rising,
each once. -/
def placesAt {r : RS} {a : RAnn r.up} (w : WireRB lam K r.up a) (b : Bool) (R : Finset r.Pos)
    (k d : ℕ) : List ℕ :=
  (((R.filter fun q => (a.own q == b && w.tree q == k) = true).image w.place).sort (· ≤ ·)).filter
    fun j => decide (j < 2 ^ d)

/-- It is the list of all leaves below 2 ^ d with those kept at which a member of R stands, where
`tree` and `place` are the inverse of posAt on the component b. -/
theorem placesAt_eq {r : RS} {a : RAnn r.up} (w : WireRB lam K r.up a) (b : Bool)
    (posAt : ℕ → ℕ → Option r.Pos)
    (hat : ∀ k j p, posAt k j = some p → a.own p = b ∧ w.tree p = k ∧ w.place p = j)
    (hback : ∀ p, a.own p = b → posAt (w.tree p) (w.place p) = some p) [DecidableEq r.Pos]
    (R : Finset r.Pos) (k d : ℕ) :
    placesAt w b R k d =
      (List.range (2 ^ d)).filter (keepP r (posAt k) fun p => decide (p ∈ R)) := by
  refine eq_of_sorted_mem id _ _ ?_ (List.pairwise_lt_range.filter _) fun x => ?_
  · exact (List.Pairwise.imp₂ (fun _ _ h1 h2 => lt_of_le_of_ne h1 h2) (Finset.pairwise_sort _ _)
      (Finset.sort_nodup _ _)).filter _
  · unfold placesAt
    simp only [List.mem_filter, Finset.mem_sort, Finset.mem_image, Finset.mem_filter,
      List.mem_range, decide_eq_true_iff, Bool.and_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨⟨q, ⟨hq, ho, ht⟩, hp⟩, hx⟩
      refine ⟨hx, ?_⟩
      have hb := hback q ho
      rw [ht, hp] at hb
      unfold keepP
      rw [hb]
      exact decide_eq_true hq
    · rintro ⟨hx, hk⟩
      refine ⟨?_, hx⟩
      unfold keepP at hk
      cases hp : posAt k x with
      | none =>
        simp only [hp] at hk
        cases hk
      | some p =>
        simp only [hp] at hk
        obtain ⟨h1, h2, h3⟩ := hat k x p hp
        exact ⟨p, ⟨of_decide_eq_true hk, h1, h2⟩, h3⟩

/-- Four of the laws of a round's wire: `tree` and `place` are the inverse of `posAt0` on the shared
component and of `posAtJ` on a slot's. -/
structure PlaceOK {r : RS} {a : RAnn r.up} (w : WireRB lam K r.up a) : Prop where
  at0 : ∀ k j p, w.posAt0 k j = some p → a.own p = false ∧ w.tree p = k ∧ w.place p = j
  atJ : ∀ k j p, w.posAtJ k j = some p → a.own p = true ∧ w.tree p = k ∧ w.place p = j
  back0 : ∀ p, a.own p = false → w.posAt0 (w.tree p) (w.place p) = some p
  backJ : ∀ p, a.own p = true → w.posAtJ (w.tree p) (w.place p) = some p

/-- A wire that obeys the laws obeys these four. -/
theorem _root_.TypedOracleCompiler.Iop.WireRB.OKG.placeOK {r : RS} {a : RAnn r.up}
    {w : WireRB lam K r.up a} (h : w.OKG) : PlaceOK w :=
  ⟨h.place_posAt0, h.place_posAtJ, h.posAt0_place, h.posAtJ_place⟩

/-- The four laws at every round of a skeleton's wiring. -/
def PlaceOKS : (S : List RS) → (A : RoundSplits (up S)) → RoundsQueryLayout lam K (up S) A → Prop
  | [], _, _ => True
  | _ :: S, (_, A), (w, W) => PlaceOK w ∧ PlaceOKS S A W

/-! ### The checks -/

/-- `checksR` along the places of the positions read, round by round, tree by tree. -/
def checksRQ :
    (S : List RS) → (A : RoundSplits (up S)) → RoundsQueryLayout lam K (up S) A →
    ((p : OPos (up S)) → OSym (up S) p → Body (Lf ())) → RootsOfChain lam (up S) → Finset (OPos (up S)) →
    ((p : OPos (up S)) → Option (Opening lam (OSym (up S) p))) → Option (List (Check lam (Lf ())))
  | [], _, _, _, _, _, _ => some []
  | r :: S, (_, A), (w, W), emb, (rt, rts), R, f =>
      haveI : DecidableEq r.Pos := w.pt.decPos
      let R0 : Finset r.Pos := headR (α := r.Pos) (β := OPos (up S)) R
      match optPQ Lf r w.posAt0 w.depth0 (fun p => emb (.inl p)) (rt.1.getD [])
          (fun p => decide (p ∈ R0)) (placesAt w false R0) (fun p => f (.inl p)),
        optPQ Lf r w.posAtJ w.depthJ (fun p => emb (.inl p)) (rt.2.getD [])
          (fun p => decide (p ∈ R0)) (placesAt w true R0) (fun p => f (.inl p)),
        checksRQ S A W (fun p => emb (.inr p)) rts
          (tailR (α := r.Pos) (β := OPos (up S)) R) (fun p => f (.inr p)) with
      | some x, some y, some z => some (x ++ y ++ z)
      | _, _, _ => none

/-- It is `checksR`, where the four laws hold. -/
theorem checksRQ_eq :
    ∀ (S : List RS) (A : RoundSplits (up S)) (W : RoundsQueryLayout lam K (up S) A), PlaceOKS S A W →
      ∀ (emb : (p : OPos (up S)) → OSym (up S) p → Body (Lf ())) (rts : RootsOfChain lam (up S))
        (R : Finset (OPos (up S)))
        (f : (p : OPos (up S)) → Option (Opening lam (OSym (up S) p))),
      checksRQ Lf S A W emb rts R f = checksR Lf S A W emb rts R f
  | [], _, _, _, _, _, _, _ => rfl
  | r :: S, (a, A), (w, W), hW, emb, (rt, rts), R, f => by
      letI : DecidableEq r.Pos := w.pt.decPos
      have ih := checksRQ_eq S A W hW.2 (fun p => emb (.inr p)) rts
        (tailR (α := r.Pos) (β := OPos (up S)) R) (fun p => f (.inr p))
      have e0 := optPQ_eq Lf r w.posAt0 w.depth0 (fun p => emb (.inl p)) (rt.1.getD [])
        (fun p => decide (p ∈ headR (α := r.Pos) (β := OPos (up S)) R))
        (placesAt w false (headR (α := r.Pos) (β := OPos (up S)) R)) (fun p => f (.inl p))
        (fun k d => placesAt_eq w false w.posAt0 hW.1.at0 hW.1.back0 _ k d)
      have eJ := optPQ_eq Lf r w.posAtJ w.depthJ (fun p => emb (.inl p)) (rt.2.getD [])
        (fun p => decide (p ∈ headR (α := r.Pos) (β := OPos (up S)) R))
        (placesAt w true (headR (α := r.Pos) (β := OPos (up S)) R)) (fun p => f (.inl p))
        (fun k d => placesAt_eq w true w.posAtJ hW.1.atJ hW.1.backJ _ k d)
      simp only [checksRQ, checksR, ih, e0, eJ]
      rfl

/-! ### The verifier -/

variable (g : Fam (typedOracleFamily lam K (Lf ())))
variable {Y : Type} {E : ExtSpec} {M : Type} (mk : Finset E.Pos → M) (tst : M → E.Pos → Bool)

/-- `afterLX` over `checksRQ`. -/
def afterLXQ (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ())) (embE : E.Sym → Body (Lf ()))
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S))
    (rts : RootsOfChain lam (up P.S)) (ph : Phase lam) : Bool :=
  let R := P.reads x ρ (effsP P.S P.ann rts π.plains)
  let Re := P.extReads x ρ
  match checksRQ Lf P.S P.ann wq.sh embS rts R π.opens,
        extLP Lf wq.ext embE cms (tst (mk Re)) π.ext wq.ext.all with
  | some a, some b =>
      if (a ++ b).length ≤ wq.nOpen ∧
          (a ++ b).all (fun c => wellP Lf c && decide (c.depth ≤ wq.maxDepth)) then
        (a ++ b).all (runCheckB Lf g) && reqPartB Lf g depthReq π.rtreq π.slot π.path π.rsalt ph &&
          P.accept x (wq.ext.build fun p => (π.ext p).map Opening.sym)
            (trP P.S P.ann wq.sh rts π.plains ρ π.opens)
      else false
  | _, _ => false

/-- It is `afterLX`, where the four laws hold. -/
theorem afterLXQ_eq (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up) (hW : PlaceOKS P.S P.ann wq.sh)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ())) (embE : E.Sym → Body (Lf ()))
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S))
    (rts : RootsOfChain lam (up P.S)) (ph : Phase lam) :
    afterLXQ Lf g mk tst P wq embS embE depthReq cms x π ρ rts ph =
      afterLX Lf g mk tst P wq embS embE depthReq cms x π ρ rts ph := by
  unfold afterLXQ afterLX
  simp only [checksRQ_eq Lf P.S P.ann wq.sh hW]
  rfl

variable [DecidableEq E.Pos]

/-- `verifyLXL` over `afterLXQ`. -/
def verifyLXLQ (early : X → X) (late : Option ℕ) (t : Tag) (P : PS Y E)
    (sh : RoundsQueryLayout lam K P.up.loc.shape P.up.ann) (wqOf : List E.Pos → ProtocolQueryLayout lam K P.up)
    (key : E.Pos → ℕ) (lst : Y → Rho (up P.S) → List E.Pos)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ()))
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (xin : Y → Option X) (embE : E.Sym → Body (Lf ())) (depthReq : ℕ) (cms : List (Dig lam))
    (x : Y) (π : OneProtocolProof lam P.up) : Bool :=
  match chainP Lf g early late t cms (xin x) π.salt π.rtreq P.S P.ann sh embP 0
      .first π.roots π.plains with
  | none => false
  | some (ρ, rts, ph) =>
    decide ((lst x ρ).Pairwise (fun a b => key a < key b)) &&
      decide (∀ p ∈ P.extReads x ρ, p ∈ lst x ρ) &&
      afterLXQ Lf g mk tst P (wqOf (lst x ρ)) embS embE depthReq cms x π ρ rts ph

/-- It is `verifyLXL`, where the four laws hold of the wire at every list.

This file states: `checksR` (OnBytes/TypedOracleCompiler/Run/LaxThin.lean) goes through all 2 ^ d leaves of every
tree of depth d and asks at each whether the position there is among those that the verifier reads.
`checksRQ` calls the same function `compP` (OnBytes/TypedOracleCompiler/Run/ThinDefs.lean) on the rising list of the
read positions' leaf numbers alone (`placesAt`). `checksRQ_eq`, `afterLXQ_eq`, `verifyLXLQ_eq`: the
forms here of `checksR`, `afterLX` and `verifyLXL` (OnBytes/TypedOracleCompiler/Run/LaxShort.lean) have the same
value as these, on all arguments, where the four laws of the next paragraph hold (in
`verifyLXLQ_eq`: at the wiring `(wqOf L).sh` of every list L). General in the protocol.
OnBytes/RunA/ListedOwnLaws.lean has the like for another form of the verifier.

It assumes: in these three statements, four laws on how positions are numbered (`PlaceOK`,
`PlaceOKS`): the maps from a position to its tree and leaf are the inverse of the map from tree and
leaf to a position. They are four of the laws `WireRB.OKG`. `compP_filter` asks nothing;
`placesAt_eq` asks the like of two of the four, for one component; `treesPQ_eq` and `optPQ_eq` ask
that each list is the list of all leaves with the read ones kept. All else is a variable: the
protocol's data, the numbering, the codings, the answers to the typed queries, the instance and the
proof. OnBytes/TypedOracleCompiler/Slice/EntryVerdictPlaces.lean proves the four laws for the entry file's protocol.

It does not show: any time or memory. Nothing on soundness. Where the four laws fail nothing is
shown, no test guards the lists when the form is evaluated, and `verifyLXLQ` may say yes where
`verifyLXL` says no. Nothing more of `verifyLXL` than LaxThin.lean and LaxShort.lean show. The
limits in full, for every statement of this file: below.

Terms: lean/GLOSSARY.md. In the comments of this file a "wire" or "wiring" is the data that numbers
a round's positions and trees, a "place" is a leaf's number in its tree, a "run" is an evaluation by
Lean's evaluator or of compiled code, and the "lax verifier" is `verifyLX`
(OnBytes/TypedOracleCompiler/Run/LaxThin.lean), an evaluable form of the compiled verifier `verifyB` of the compiler
under OnBytes/TypedOracleCompiler/. Where a comment of this file names the head of a file, read with it the comment
to which that head points.

THE LIMITS.

OnBytes/TypedOracleCompiler/Run/LaxPlaces.lean: the lax verifier's evaluable form without the walk over all leaves
of the own trees: each tree's checks are made along the list of its places that are read.

Why. `checksR` (OnBytes/TypedOracleCompiler/Run/LaxThin.lean) walks all 2 ^ d leaves of every tree of depth d, and
asks at each leaf that has a position whether that position lies in the set of positions read. Here
the walk goes along the places of the read positions of that tree alone, in rising order: the same
function `compP` (OnBytes/TypedOracleCompiler/Run/ThinDefs.lean) on a list that is never longer. General in a
skeleton and its wiring. (OnBytes/RunA/ListedOwnLaws.lean has the like for another form of the
verifier.)

  `keepP`, `compP_filter`: `compP` takes of a list of leaves those alone at which a read position
    stands.
  `placesAt w b R k d`: the places below 2 ^ d of the members of R that lie in the component b
    (false: shared; true: a slot's) and in tree k, rising, each once. `placesAt_eq`: it is the list
    of all leaves below 2 ^ d with those kept at which a member of R stands, where `tree` and
    `place` are the inverse of posAt. It reads own, `tree` and `place`, which `checksR` does not
    read, and goes through all of R once for each tree.
  `PlaceOK w`, `PlaceOKS`: four of the laws of a round's wire (`WireRB.OKG`): `tree` and `place` are
    the inverse of `posAt0` | `posAtJ`. `WireRB.OKG.placeOK`.
  `treesPQ`, `optPQ`, `checksRQ`; `treesPQ_eq`, `optPQ_eq`, `checksRQ_eq`: `treesP`, `optP`,
    `checksR` along such lists; `checksRQ` is `checksR` where the four laws hold.
  `afterLXQ`, `verifyLXLQ`; `afterLXQ_eq`, `verifyLXLQ_eq`: `afterLX` (OnBytes/TypedOracleCompiler/Run/LaxThin.lean)
    and `verifyLXL` (OnBytes/TypedOracleCompiler/Run/LaxShort.lean) over `checksRQ`; they are these, on all
    arguments, where the four laws hold.
What is not claimed. Any time or memory: whether this form is cheaper is a matter of a run, and this
head reports none. Nothing on soundness. Nothing where the four laws fail: no test at run time
guards the lists (unlike `verifyLXL`'s list of external positions); at such a wire `checksRQ` may
make fewer checks than `checksR`, so `verifyLXLQ` may say yes where `verifyLXL` says no. Whoever
calls it at a wire owes `PlaceOKS` there. All that the heads of LaxThin.lean and LaxShort.lean do
not claim.
-/
theorem verifyLXLQ_eq (early : X → X) (late : Option ℕ) (t : Tag) (P : PS Y E)
    (sh : RoundsQueryLayout lam K P.up.loc.shape P.up.ann) (wqOf : List E.Pos → ProtocolQueryLayout lam K P.up)
    (hW : ∀ L, PlaceOKS P.S P.ann (wqOf L).sh)
    (key : E.Pos → ℕ) (lst : Y → Rho (up P.S) → List E.Pos)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ()))
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (xin : Y → Option X) (embE : E.Sym → Body (Lf ())) (depthReq : ℕ) (cms : List (Dig lam))
    (x : Y) (π : OneProtocolProof lam P.up) :
    verifyLXLQ Lf g mk tst early late t P sh wqOf key lst embS embP xin embE depthReq cms x π =
      verifyLXL Lf g mk tst early late t P sh wqOf key lst embS embP xin embE depthReq cms x π := by
  unfold verifyLXLQ verifyLXL
  cases chainP Lf g early late t cms (xin x) π.salt π.rtreq P.S P.ann sh embP 0
      .first π.roots π.plains with
  | none => rfl
  | some z =>
    obtain ⟨ρ, rts, ph⟩ := z
    simp only [afterLXQ_eq Lf g mk tst P (wqOf (lst x ρ)) (hW _)]

end TypedOracleCompiler.Run.Thin

#print axioms TypedOracleCompiler.Run.Thin.compP_filter
#print axioms TypedOracleCompiler.Run.Thin.placesAt_eq
#print axioms TypedOracleCompiler.Run.Thin.checksRQ_eq
#print axioms TypedOracleCompiler.Run.Thin.verifyLXLQ_eq
