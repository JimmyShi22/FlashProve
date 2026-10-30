-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/BookAtW.lean: no soundness is claimed.
For the field «book» of the last chain's ledger (Johnson/LLT25R/LastFive.lean: BookAt G no D j x): its first clause at all three members of the group under the last chain's own proximity test, its second at the two elder ones: lemmas on one state s of the last chain at border 2 (behind K14's second part, in front of the own test).
  BookTwo n₁ ft nΩ s       what the book-keeping at border 2 and HandedNumbers give of s.book: it has n₁ + 1 trees; the tree at place z < n₁ is the handed book's and bears the number ft + z; the tree at place n₁ bears nΩ; s.loc.firstTree = n₁ + 1 · **bookTwo_of_shape**
  **no_of_seat**           (1): seatBy (noLast t₁ t₂ s.loc.firstTree) s.book id = some q · s.book.place[id]? = some (z, u) ⇒ noAt t₁ t₂ n₁ ft nΩ z = q.1 ∧ u = q.2: the closed letter «no» of «opens» is the seat's number, at every message of the book
  elder_of_seat            q.1 < t₁ ⇒ z < n₁ (Omega's copy's tree bears t₁ + nΩ)
  tree_shape_of_seats      seatsCarriedB L B = true · B.trees[z]? = some T ⇒ L.shapes[z]? = some T.shape
  PlanShapes G L ft n₁     a test on the plan: for z < n₁ the listed shape number z is what G tells of the tree ft + z (ShapeIs, Johnson/Desc/K12/Coin/FramesTie.lean) · shapeIsB · planShapesB · planShapes_iff
  **shape_of_elder**       (2) At an elder member (q.1 < t₁): … · seatsCarriedB L f.book = true · PlanShapes G L ft n₁ ⇒ ∀ z u T, place → s.book.trees[z]? = some T → ∀ o, G.oracleAt q.1 = some o → ShapeIs T.shape o
Left. seatsCarriedB L f.book: FoldFacts' seatsCarried at the first chain's last state (one conjunct more in rcLastB, if the ledger wants it there) · PlanShapes: not evaluated here · (2) at Omega's copy: not here.
No member. Nothing on soundness.
-/
import Johnson.ToldDescR.OpensAtW
import Johnson.Desc.Sound.TabAt
import Johnson.Desc.K12.Door.DoorGives
import Johnson.Desc.K12.Coin.FramesTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound (seatBy noLast)
open VerifiableInference.Desc.Third (S₃ P₁₄ SharedOut Border)
open VerifiableInference.Desc.Third.Law (start₃E_book start₃E_border)
open VerifiableInference.Desc.Last (Handed shapeAt behindOk_of_two)
open VerifiableInference.Desc.K12.Door (seatsCarriedB)

/-- What the book-keeping at border 2 gives of the state's book. -/
structure BookTwo (n₁ ft nΩ : ℕ) (f : Handed) (s : S₃) : Prop where
  size : s.book.trees.size = n₁ + 1
  old : ∀ z, z < n₁ → s.book.trees[z]? = f.book.trees[z]?
  number : ∀ z T, z < n₁ → s.book.trees[z]? = some T → T.number = ft + z
  omega : ∀ T, s.book.trees[n₁]? = some T → T.number = nΩ
  first : s.loc.firstTree = n₁ + 1

theorem bookTwo_of_shape {p : P₁₄} {R : List Fmt.DeclaredRound} {f : Handed} {o : SharedOut} {s : S₃}
    (hs : shapeAt p R 2 f o s = true) {n₁ ft nΩ : ℕ} (hH : HandedNumbers n₁ ft nΩ f o) :
    BookTwo n₁ ft nΩ f s := by
  obtain ⟨⟨s₀, B⟩, _⟩ := behindOk_of_two hs
  obtain ⟨b, y, G, dot, L⟩ := B.laid
  obtain ⟨hbook, -, hft⟩ := start₃E_book _ _ _ _ _ _ _ _ _ _ _ B.start
  have hr := start₃E_roots _ _ _ _ _ _ _ _ _ _ _ B.start
  obtain ⟨g, hg⟩ := start₃E_border _ _ _ _ _ _ _ _ _ _ _ B.start
  obtain rfl : (⟨g, o⟩ : Border) = b := Option.some.inj (hg.symm.trans L.border)
  have hsz : s₀.book.trees.size = n₁ := by
    rw [hbook]
    exact hH.trees
  have old : ∀ z, z < n₁ → s.book.trees[z]? = f.book.trees[z]? := fun z hz => by
    rw [L.oldTrees z (by rw [hsz]; exact hz), hbook]
  refine ⟨by rw [L.trees, hsz], old, fun z T hz hT => ?_, fun T hT => ?_, ?_⟩
  · rw [old z hz] at hT
    exact hH.first z T hT
  · obtain ⟨q, T', tO, h1, h2, _, h4, h5, _⟩ := L.tree
    rw [← hsz, h4] at hT
    obtain rfl := Option.some.inj hT
    rw [h5]
    exact hH.omega q T' h1 h2
  · rw [L.loc]
    show s₀.loc.firstTree = n₁ + 1
    rw [hft, hr, hH.trees]

/-- **(1) The closed letter «no» is the seat's number.** -/
theorem no_of_seat {n₁ ft nΩ : ℕ} {f : Handed} {s : S₃} (K : BookTwo n₁ ft nΩ f s) (t₁ t₂ : ℕ)
    {id : ℕ} {q : ℕ × ℕ} (hq : seatBy (noLast t₁ t₂ s.loc.firstTree) s.book id = some q) :
    ∀ z u, s.book.place[id]? = some (z, u) → noAt t₁ t₂ n₁ ft nΩ z = q.1 ∧ u = q.2 := by
  intro z u hp
  unfold seatBy at hq
  rw [hp, Option.bind_some] at hq
  obtain ⟨T, hT, e⟩ := Option.map_eq_some_iff.1 hq
  have hz : z < n₁ + 1 := by
    rw [← K.size]
    exact (Array.getElem?_eq_some_iff.1 hT).1
  rw [← e]
  refine ⟨?_, rfl⟩
  show Three.wholeNo t₁ t₂ (if z = n₁ then (1, nΩ) else (0, ft + z)) =
    noLast t₁ t₂ s.loc.firstTree z T
  unfold noLast
  rw [K.first]
  by_cases hzn : z = n₁
  · subst hzn
    rw [if_pos rfl, if_neg (Nat.lt_irrefl _), if_pos rfl, K.omega T hT]
    rfl
  · have hlt : z < n₁ := by omega
    rw [if_neg hzn, if_pos (by omega), K.number z T hlt hT]
    show 0 + (ft + z) = ft + z
    omega

/-- A seat below the first chain's count of trees is an elder tree's. -/
theorem elder_of_seat {n₁ ft nΩ : ℕ} {f : Handed} {s : S₃} (K : BookTwo n₁ ft nΩ f s) (t₁ t₂ : ℕ)
    {id : ℕ} {q : ℕ × ℕ} (hq : seatBy (noLast t₁ t₂ s.loc.firstTree) s.book id = some q)
    (he : q.1 < t₁) : ∀ z u, s.book.place[id]? = some (z, u) → z < n₁ ∧ q.1 = ft + z := by
  intro z u hp
  have h1 := (no_of_seat K t₁ t₂ hq z u hp).1
  have hq' := hq
  unfold seatBy at hq'
  rw [hp, Option.bind_some] at hq'
  obtain ⟨T, hT, -⟩ := Option.map_eq_some_iff.1 hq'
  have hz : z < n₁ + 1 := by
    rw [← K.size]
    exact (Array.getElem?_eq_some_iff.1 hT).1
  by_cases hzn : z = n₁
  · exfalso
    subst hzn
    have e : noAt t₁ t₂ z ft nΩ z = t₁ + nΩ := by
      unfold noAt
      rw [if_pos rfl]
      rfl
    omega
  · refine ⟨by omega, ?_⟩
    have e : noAt t₁ t₂ n₁ ft nΩ z = 0 + (ft + z) := by
      unfold noAt
      rw [if_neg hzn]
      rfl
    omega

theorem tree_shape_of_seats {L : K12.Door.Laid} {B : TreeBook} (h : seatsCarriedB L B = true)
    {z : ℕ} {T : Tree} (hT : B.trees[z]? = some T) : L.shapes[z]? = some T.shape := by
  unfold seatsCarriedB at h
  simp only [Bool.and_eq_true] at h
  have e : B.trees.toList.map (·.shape) = L.shapes.take B.trees.size := eq_of_beq h.1.2
  have hz : z < B.trees.size := (Array.getElem?_eq_some_iff.1 hT).1
  have e1 : (B.trees.toList.map (·.shape))[z]? = some T.shape := by
    rw [List.getElem?_map, Array.getElem?_toList, hT]
    rfl
  rw [e, List.getElem?_take_of_lt hz] at e1
  exact e1

/-- `ShapeIs` as a test with code. -/
def shapeIsB (tsh : TreeShape) (o : VerifiableInference.Desc.Oracle) : Bool :=
  decide (tsh.mainSymbols.toList = o.tenants.map (·.main)) &&
    decide (tsh.maskSymbols.toList = o.tenants.map (·.mask)) && decide (tsh.logN = o.logLength)

theorem shapeIs_iff (tsh : TreeShape) (o : VerifiableInference.Desc.Oracle) :
    shapeIsB tsh o = true ↔ ShapeIs tsh o := by
  unfold shapeIsB
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.main, h.mask⟩, h.log⟩⟩

/-- **A test on the plan**: the listed shapes are what the description tells of the trees. -/
def PlanShapes {Xi : Type} (G : FileDescription Xi) (L : K12.Door.Laid) (ft n₁ : ℕ) : Prop :=
  ∀ z, z < n₁ → ∀ tsh o, L.shapes[z]? = some tsh → G.oracleAt (ft + z) = some o → ShapeIs tsh o

def planShapesB {Xi : Type} (G : FileDescription Xi) (L : K12.Door.Laid) (ft n₁ : ℕ) : Bool :=
  (List.range n₁).all fun z =>
    match L.shapes[z]?, G.oracleAt (ft + z) with
    | some tsh, some o => shapeIsB tsh o
    | _, _ => true

theorem planShapes_iff {Xi : Type} (G : FileDescription Xi) (L : K12.Door.Laid) (ft n₁ : ℕ) :
    planShapesB G L ft n₁ = true ↔ PlanShapes G L ft n₁ := by
  unfold planShapesB PlanShapes
  rw [List.all_eq_true]
  constructor
  · intro h z hz tsh o h1 h2
    have k := h z (List.mem_range.2 hz)
    rw [h1, h2] at k
    exact (shapeIs_iff _ _).1 k
  · intro h z hz
    have hz' := List.mem_range.1 hz
    cases h1 : L.shapes[z]? with
    | none => rfl
    | some tsh =>
      cases h2 : G.oracleAt (ft + z) with
      | none => rfl
      | some o => exact (shapeIs_iff _ _).2 (h z hz' tsh o h1 h2)

/-- **(2) At an elder member.** -/
theorem shape_of_elder {Xi : Type} (G : FileDescription Xi) {n₁ ft nΩ : ℕ} {f : Handed} {s : S₃}
    (K : BookTwo n₁ ft nΩ f s) (t₁ t₂ : ℕ) {id : ℕ} {q : ℕ × ℕ}
    (hq : seatBy (noLast t₁ t₂ s.loc.firstTree) s.book id = some q) (he : q.1 < t₁)
    {L : K12.Door.Laid} (hL : seatsCarriedB L f.book = true) (hP : PlanShapes G L ft n₁) :
    ∀ z u T, s.book.place[id]? = some (z, u) → s.book.trees[z]? = some T →
      ∀ o, G.oracleAt q.1 = some o → ShapeIs T.shape o := by
  intro z u T hp hT o ho
  obtain ⟨hz, e⟩ := elder_of_seat K t₁ t₂ hq he z u hp
  rw [K.old z hz] at hT
  rw [e] at ho
  exact hP z hz T.shape o (tree_shape_of_seats hL hT) ho

end ToldDesc

#print axioms ToldDesc.bookTwo_of_shape
#print axioms ToldDesc.no_of_seat
#print axioms ToldDesc.elder_of_seat
#print axioms ToldDesc.planShapes_iff
#print axioms ToldDesc.shape_of_elder
