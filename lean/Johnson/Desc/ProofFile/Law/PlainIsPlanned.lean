-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Law/PlainIsPlanned.lean: PlanPlain.lean's copies of the planner's functions
return what the functions that they were copied from return, except for the field `run` of the
segments' records. Theorems only; no file of the description imports this one.
Why. A law that is stated where `Verify.chainsOf` or `Verify.builtOf` returns a value does not apply
to the public part of the proof file's description, which calls the copies. These equations carry
it over.
  `blank`            a segment's record (`LinkH`) with the routine that refuses at once in `run`
  `linksOf_blank`    `(linksOf X cov).map (·.map blank) = linksPlain X`, for every `cov`
  `shapesOf_eq`      the copy returns the same shapes, and the same records after `blank`
  `chainsOf_eq`      `ProofFile.Plain.chainsOf X lay c = Verify.chainsOf X lay c`: the record `Chains`
                     holds no segment's record
  `builtOf_eq`       `ProofFile.Plain.builtOf X ch = (Verify.builtOf X ch).map blankB`
  `planned_eq`       `ProofFile.Plain.planned o pol KL lay` is `plannedAtO o pol KL lay fixedConfigurationDigest`
                     (Johnson/Desc/Ok/PlanWritten/PublicAt.lean) with `blankB` on the field `built`
  `pub_chainsOf`     where the public part `Z` is computed,
                     `Verify.chainsOf Z.p.X (some lay) fixedConfigurationDigest = .ok Z.p.chains`
The core is one kind of lemma, once for each routine that is handed the records: it does not read
`run` (`headLast_blank`, `declareLinks_blank`, `linksFit_blank`, `buildLinksH_blank`, ...).
OnBytes/Tie/PlanAtPolicy.lean has lemmas of this kind for the head's record alone, and only where
both sides return; here they are equations, so that a refusal carries over too.
Not here: `sendsOf` and `madeOf`.

-/
import Johnson.Desc.ProofFile.Law.PlainMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Law
open OnBytes OnBytes.Model OnBytes.Model.Stages OnBytes.Model.Verify
open VerifiableInference.Desc (fixedConfigurationDigest)

/-- A segment's record, with the routine that refuses at once in the field `run`. -/
def blank (X : LinkH) : LinkH := { X with run := ProofFile.Plain.notToBeRun }

/-- The same for what a sub-proof's plan gives to its segment. -/
def blankS (s : SubPlanH) : SubPlanH := { s with run := ProofFile.Plain.notToBeRun }

/-- The same for all records that `buildLinksH` returns. -/
def blankB (B : LinksH) : LinksH := { links := B.links.map blank }

/-! ### On `Except` and on loops -/

section
variable {ε α α' β β' : Type}

theorem bind_mapE {x : Except ε α} {m : α → α'} {k : α → Except ε β} {k' : α' → Except ε β'}
    {n : β → β'} (hk : ∀ a, k' (m a) = (k a).map n) : (x.map m >>= k') = (x >>= k).map n := by
  cases x with
  | error e => rfl
  | ok a => exact hk a

theorem bind_sameE {x : Except ε α} {k : α → Except ε β} {k' : α → Except ε β'} {n : β → β'}
    (hk : ∀ a, k' a = (k a).map n) : (x >>= k') = (x >>= k).map n := by
  cases x with
  | error e => rfl
  | ok a => exact hk a

theorem bind_map0 {x : Except ε α} {m : α → α'} {k : α → Except ε β} {k' : α' → Except ε β}
    (hk : ∀ a, k' (m a) = k a) : (x.map m >>= k') = (x >>= k) := by
  cases x with
  | error e => rfl
  | ok a => exact hk a

theorem bind_same0 {x : Except ε α} {k k' : α → Except ε β} (hk : ∀ a, k' a = k a) :
    (x >>= k') = (x >>= k) := by
  cases x with
  | error e => rfl
  | ok a => exact hk a

end

/-- A map on the state of a loop, on a step of the loop. -/
def stepMap {σ σ' : Type} (m : σ → σ') : ForInStep σ → ForInStep σ'
  | .done u => .done (m u)
  | .yield u => .yield (m u)

/-- Two loops, the second over the mapped list and from the mapped state: if every pass commutes
with the maps, so do the loops. -/
theorem forIn_mapE {α α' σ σ' : Type} (a2 : α → α') (m : σ → σ')
    (f : α → σ → Except String (ForInStep σ)) (f' : α' → σ' → Except String (ForInStep σ'))
    (hf : ∀ a s, f' (a2 a) (m s) = (f a s).map (stepMap m)) :
    ∀ (l : List α) (s : σ), forIn (l.map a2) (m s) f' = (forIn l s f).map m
  | [], _ => rfl
  | a :: l, s => by
    rw [List.map_cons, List.forIn_cons, List.forIn_cons, hf]
    cases f a s with
    | error e => rfl
    | ok t =>
      cases t with
      | done u => rfl
      | yield u => exact forIn_mapE a2 m f f' hf l u

/-- The same, with what follows the loop. -/
theorem loop_mapE {α α' σ σ' β β' : Type} (a2 : α → α') (m : σ → σ')
    {f : α → σ → Except String (ForInStep σ)} {f' : α' → σ' → Except String (ForInStep σ')}
    {l : List α} {s : σ} {s' : σ'} {k : σ → Except String β} {k' : σ' → Except String β'}
    {n : β → β'} (hf : ∀ a s, f' (a2 a) (m s) = (f a s).map (stepMap m)) (hs : s' = m s)
    (hk : ∀ u, k' (m u) = (k u).map n) :
    (forIn (l.map a2) s' f' >>= k') = (forIn l s f >>= k).map n := by
  subst hs
  rw [forIn_mapE a2 m f f' hf l s]
  exact bind_mapE hk

/-- A loop over a mapped list whose state is not mapped. -/
theorem forIn_mapL {α α' σ : Type} (a2 : α → α') (f' : α' → σ → Except String (ForInStep σ)) :
    ∀ (l : List α) (s : σ), forIn (l.map a2) s f' = forIn l s fun a => f' (a2 a)
  | [], _ => rfl
  | a :: l, s => by
    rw [List.map_cons, List.forIn_cons, List.forIn_cons]
    cases f' (a2 a) s with
    | error e => rfl
    | ok t =>
      cases t with
      | done u => rfl
      | yield u => exact forIn_mapL a2 f' l u

/-- The same, against a second loop whose passes agree with the first's. -/
theorem forIn_mapL2 {α α' σ : Type} (a2 : α → α') {f : α → σ → Except String (ForInStep σ)}
    {f' : α' → σ → Except String (ForInStep σ)} {l : List α} {s : σ}
    (hf : ∀ a s, f' (a2 a) s = f a s) : forIn (l.map a2) s f' = forIn l s f := by
  rw [forIn_mapL]
  have e : (fun a => f' (a2 a)) = f := funext fun a => funext fun s => hf a s
  rw [e]

/-- The same, with what follows the loop. -/
theorem loop_mapL {α α' σ β : Type} (a2 : α → α') {f : α → σ → Except String (ForInStep σ)}
    {f' : α' → σ → Except String (ForInStep σ)} {l : List α} {s : σ} {k : σ → Except String β}
    (hf : ∀ a s, f' (a2 a) s = f a s) :
    (forIn (l.map a2) s f' >>= k) = (forIn l s f >>= k) := by
  rw [forIn_mapL2 a2 hf]

/-! ### The routines that are handed the records do not read `run` -/

theorem push_blank (s : Array LinkH) (x : LinkH) :
    (s.map blank).push (blank x) = (s.push x).map blank := (Array.map_push ..).symm

theorem gids_blank (nm : Array LinkH) :
    (nm.map blank).toList.map (·.gid) = nm.toList.map (·.gid) := by
  rw [Array.toList_map, List.map_map]
  rfl

theorem onTable_blank (links : Array LinkH) : onTable (links.map blank) = onTable links := by
  unfold onTable
  rw [Array.toList_map, List.filter_map, List.length_map]
  rfl

theorem headLast_blank (links : Array LinkH) : headLast (links.map blank) = headLast links := by
  unfold headLast
  try dsimp only
  rw [Array.toList_map, List.zipIdx_map, Array.size_map]
  refine loop_mapL (Prod.map blank id) ?_
  rintro ⟨X, i⟩ r
  rfl

theorem linksCount_blank (links : Array LinkH) :
    linksCount (links.map blank) = linksCount links := by
  unfold linksCount
  rw [Array.size_map]

theorem declareOwn_blank (X : LinkH) (l : Nat) : declareOwn (blank X) l = declareOwn X l := rfl

theorem foreign_blank (links : Array LinkH) (NGr : Nat) (p4 : Bool) (l : Nat) (X : LinkH)
    (s : Array (Nat × String) × Array FrameLink) (tree : Nat) (pl : PlaceF) :
    foreign (links.map blank) NGr p4 l (blank X) s tree pl =
      foreign links NGr p4 l X s tree pl := by
  unfold foreign
  simp only [Array.getElem?_map]
  cases pl.owner with
  | none => rfl
  | some owner =>
    try dsimp only
    cases links[layersLink p4 owner]? with
    | none => rfl
    | some Y => rfl

/-- The map on the state of the loop of `declareLinks`. -/
def namedBlank (s : MProd (Array FrameLink) (Array LinkH)) :
    MProd (Array FrameLink) (Array LinkH) := ⟨s.fst, s.snd.map blank⟩

theorem declareLinks_blank (links : Array LinkH) (NGr : Nat) (p4 : Bool) :
    declareLinks (links.map blank) NGr p4 =
      (declareLinks links NGr p4).map fun x => (x.1.map blank, x.2) := by
  unfold declareLinks
  try dsimp only
  rw [Array.toList_map, List.zipIdx_map]
  refine loop_mapE (Prod.map blank id) namedBlank ?_ (by simp [namedBlank]) (fun u => rfl)
  rintro ⟨X, l⟩ ⟨dd, nn⟩
  dsimp only [Prod.map, id, namedBlank]
  simp only [foreign_blank]
  rw [declareOwn_blank]
  refine bind_sameE (fun d0 => ?_)
  refine bind_sameE (fun s0 => ?_)
  have e : (nn.map blank).push { blank X with arrayOf := s0.1 } =
      (nn.push { X with arrayOf := s0.1 }).map blank := push_blank nn { X with arrayOf := s0.1 }
  by_cases hc : (s0.1.any fun a => a.2.isEmpty) = true
  · rw [if_pos hc, if_pos hc]
    rfl
  · rw [if_neg hc, if_neg hc]
    exact congrArg (fun z => Except.ok (ForInStep.yield
      (⟨s0.2.push { name := X.name, moment := d0.moment }, z⟩ :
        MProd (Array FrameLink) (Array LinkH)))) e

theorem tableRows_blank (links : Array LinkH) (NGr : Nat) :
    tableRows (links.map blank) NGr = tableRows links NGr := by
  unfold tableRows
  rw [onTable_blank]

theorem numbersHeld_blank (links : Array LinkH) (p : Params.First) :
    numbersHeld (links.map blank) p = numbersHeld links p := by
  unfold numbersHeld
  rw [Array.size_map, onTable_blank, gids_blank]

theorem indexMaskRoom_blank (links : Array LinkH) (codes : Codes) (shape : Params.ReqShape)
    (kCol : Nat) :
    indexMaskRoom (links.map blank) codes shape kCol = indexMaskRoom links codes shape kCol := by
  unfold indexMaskRoom
  rw [onTable_blank]

theorem linksLaid_blank (links : Array LinkH) (codes : Codes) (shape : Params.ReqShape)
    (layout : Params.ReqLayout) :
    linksLaid (links.map blank) codes shape layout = linksLaid links codes shape layout := by
  unfold linksLaid
  rw [Array.toList_map, List.zipIdx_map]
  cases codes.mask[shape.maskCode]? with
  | none => rfl
  | some zk =>
    try dsimp only
    first
      | refine forIn_mapL2 (Prod.map blank id) ?_
      | refine loop_mapL (Prod.map blank id) ?_
    rintro ⟨X, l⟩ r
    rfl

theorem linksFit_blank (links : Array LinkH) (codes : Codes) (shape : Params.ReqShape)
    (layout : Params.ReqLayout) (kCol : Nat) :
    linksFit (links.map blank) codes shape layout kCol =
      linksFit links codes shape layout kCol := by
  unfold linksFit
  rw [indexMaskRoom_blank, linksLaid_blank]

theorem buildLinksH_blank (links : Array LinkH) (NGr : Nat) (p4 : Bool) (wsLay : WsLay)
    (p : Params.First) :
    buildLinksH (links.map blank) NGr p4 wsLay p =
      (buildLinksH links NGr p4 wsLay p).map blankB := by
  unfold buildLinksH
  rw [headLast_blank, linksCount_blank, declareLinks_blank]
  refine bind_sameE (fun _ => ?_)
  refine bind_sameE (fun _ => ?_)
  refine bind_mapE (fun x => ?_)
  obtain ⟨nm, dc⟩ := x
  try dsimp only
  rw [tableRows_blank, linksFit_blank, numbersHeld_blank]
  refine bind_sameE (fun _ => ?_)
  refine bind_sameE (fun _ => ?_)
  refine bind_sameE (fun _ => ?_)
  refine bind_sameE (fun _ => ?_)
  by_cases hc : (!reqOk p.codes p.shape) = true
  · rw [if_pos hc, if_pos hc]
    rfl
  · rw [if_neg hc, if_neg hc]
    refine bind_sameE (fun _ => ?_)
    refine bind_sameE (fun _ => ?_)
    refine bind_sameE (fun _ => ?_)
    refine bind_sameE (fun _ => ?_)
    rfl

/-! ### The list of the records -/

theorem listLinksH_blank (NGr : Nat) (p4 : Bool) (G A : Array SubPlanH) (H : SubPlanH) :
    listLinksH NGr p4 (G.map blankS) (A.map blankS) (blankS H) =
      (listLinksH NGr p4 G A H).map fun a => a.map blank := by
  unfold listLinksH
  try dsimp only
  rw [Array.size_map, Array.size_map, Array.toList_map, List.zipIdx_map]
  by_cases hc : (G.size != NGr || (p4 && A.size != NGr)) = true
  · rw [if_pos hc, if_pos hc]
    rfl
  · rw [if_neg hc, if_neg hc]
    refine loop_mapE (Prod.map blankS id) (fun a => a.map blank) ?_ (by simp)
      (fun u => congrArg Except.ok (push_blank u (H.link "H" (1 + NGr) 2 0 true)))
    rintro ⟨sp, g⟩ s
    dsimp only [Prod.map, id]
    rw [Array.getElem?_map]
    cases p4 with
    | false =>
      exact congrArg (fun z => Except.ok (ForInStep.yield z))
        (push_blank s (sp.link ("G" ++ toString g) (1 + g) 0 g true))
    | true =>
      cases A[g]? with
      | none =>
        exact congrArg (fun z => Except.ok (ForInStep.yield z))
          (push_blank s (sp.link ("G" ++ toString g) (1 + g) 0 g true))
      | some a =>
        exact congrArg (fun z => Except.ok (ForInStep.yield z))
          ((congrArg (fun w => w.push (blank (a.link ("A" ++ toString g) (2 + NGr + g) 1 g false)))
            (push_blank s (sp.link ("G" ++ toString g) (1 + g) 0 g true))).trans
            (push_blank _ _))

theorem linksOf_blank (X : Public) (cov : Head.Covered) :
    (linksOf X cov).map (fun a => a.map blank) = ProofFile.Plain.linksPlain X := by
  unfold linksOf ProofFile.Plain.linksPlain
  rw [← listLinksH_blank]
  have hG : (X.G.mapIdx fun g hp => layersPlanOf X cov.tokv g hp).map blankS =
      X.G.map fun hp =>
        { tl := hp.tl, Fp := hp.Fp, Tp := hp.Tp, ns := hp.ns, NCL := hp.NCL,
          run := ProofFile.Plain.notToBeRun } := by
    apply Array.ext
    · simp
    · intro i h1 h2
      simp [blankS, layersPlanOf]
  have hA : (X.A.map attentionPlanOf).map blankS =
      X.A.map fun A =>
        { tl := A.seam.tl, Fp := A.seam.Fp, Tp := A.seam.Tp, ns := A.ns,
          run := ProofFile.Plain.notToBeRun } := by
    rw [Array.map_map]
    rfl
  rw [hG, hA]
  rfl

/-! ### The copies -/

theorem shapesOf_eq (X : Public) (lay : Option ByteArray) :
    ProofFile.Plain.shapesOf X lay =
      (Verify.shapesOf X lay).map fun y => (y.1.map blank, y.2) := by
  unfold ProofFile.Plain.shapesOf Verify.shapesOf
  rw [← linksOf_blank X default]
  refine bind_mapE (fun ls => ?_)
  try dsimp only
  rw [headLast_blank, linksCount_blank, declareLinks_blank]
  refine bind_sameE (fun _ => ?_)
  refine bind_sameE (fun _ => ?_)
  refine bind_mapE (fun x => ?_)
  obtain ⟨nm, dc⟩ := x
  try dsimp only
  rw [gids_blank]
  cases lay.bind Plan.layoutRead with
  | none => rfl
  | some f =>
    try dsimp only
    refine bind_sameE (fun file => ?_)
    cases Plan.reqFrame dc file X.P.frame.answers with
    | none => rfl
    | some q =>
      try dsimp only
      refine bind_sameE (fun y => ?_)
      refine bind_sameE (fun sh => ?_)
      rfl

/-- **The seven chains.** The copy returns what `Verify.chainsOf` returns, refusals too. -/
theorem chainsOf_eq (X : Public) (lay : Option ByteArray) (c : ByteArray) :
    ProofFile.Plain.chainsOf X lay c = Verify.chainsOf X lay c := by
  unfold ProofFile.Plain.chainsOf Verify.chainsOf
  rw [shapesOf_eq]
  refine bind_map0 (fun y => ?_)
  obtain ⟨ls, sh⟩ := y
  try dsimp only
  refine bind_same0 (fun z => ?_)
  rw [linksFit_blank]
  rfl

theorem builtOf_eq (X : Public) (ch : Chains) :
    ProofFile.Plain.builtOf X ch = (Verify.builtOf X ch).map blankB := by
  unfold ProofFile.Plain.builtOf Verify.builtOf
  rw [← linksOf_blank X default]
  refine bind_mapE (fun ls => ?_)
  exact buildLinksH_blank ls X.NGr X.p4 X.layers.wsLay ch.proof.first

/-- **The planner's record.** The copy returns what `plannedAtO` returns at the constant `fixedConfigurationDigest`,
with `blankB` on the field `built`; refusals too. -/
theorem planned_eq (o : SecondHashFunctionArgument) (pol KL : ByteArray) (lay : Option ByteArray) :
    ProofFile.Plain.planned o pol KL lay =
      (VerifiableInference.PlanWritten.plannedAtO o pol KL lay fixedConfigurationDigest).map fun p =>
        { p with built := blankB p.built } := by
  unfold ProofFile.Plain.planned VerifiableInference.PlanWritten.plannedAtO
  refine bind_sameE (fun X => ?_)
  try dsimp only
  rw [chainsOf_eq]
  refine bind_sameE (fun c => ?_)
  rw [builtOf_eq]
  refine bind_mapE (fun b => ?_)
  rfl

/-- Where the public part `Z` of the proof file's description is computed, `Verify.chainsOf` itself
returns `Z.p.chains`, at the public record in `Z` and the constant `fixedConfigurationDigest`. -/
theorem pub_chainsOf {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : Pub}
    (h : pureRoad.pub o pol lay KL = .ok Z) :
    Verify.chainsOf Z.p.X (some lay) fixedConfigurationDigest = .ok Z.p.chains :=
  (chainsOf_eq _ _ _).symm.trans (planned_chains (pub_planned h)).1

/-- And `Verify.builtOf` returns records that are `Z.p.built`'s after `blankB`. -/
theorem pub_builtOf {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : Pub}
    (h : pureRoad.pub o pol lay KL = .ok Z) :
    ∃ b, Verify.builtOf Z.p.X Z.p.chains = .ok b ∧ blankB b = Z.p.built := by
  have hb := (planned_chains (pub_planned h)).2.2
  rw [builtOf_eq] at hb
  cases hx : Verify.builtOf Z.p.X Z.p.chains with
  | error e =>
    rw [hx] at hb
    exact (error_ne_ok hb).elim
  | ok b =>
    rw [hx] at hb
    exact ⟨b, rfl, Except.ok.inj hb⟩

end ProofFile.Law

#print axioms ProofFile.Law.declareLinks_blank
#print axioms ProofFile.Law.linksOf_blank
#print axioms ProofFile.Law.chainsOf_eq
#print axioms ProofFile.Law.planned_eq
#print axioms ProofFile.Law.pub_chainsOf
#print axioms ProofFile.Law.pub_builtOf
