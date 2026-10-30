--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeSharedChain.lean: THE LETTERS OF THE CUT STRUCTURE | VALUES
(Johnson/Desc/ProofFile/Honest/Thread/Shape.lean) FOR THE KEY FILE's SHARED CHAIN, AS ONE VALUE:
with code at the chain's front, its two proximity tests and its end; WITH LETTERS at the linear
claim's eight sub-protocols, whose guards on the shape are another hand's. (B1) is shown where there
is code, and taken as a named premise at the eight. Definitions, statements and proofs.
Sub-protocols of the verifier's: NOTHING IS SHOWN OF ANY PROVER.

THE SHAPE. `Sh₂ := Sh2 × Bool`: `Sh2` (Johnson/Desc/K14/Shape/Lin.lean: the shape of statement, book
and roots, and of what the kind K14 notes) and ONE MARK on the statement beside it (`stTidyB`,
Johnson/Desc/Ground/Shape/Marks.lean).

  `Sh₂`, `sh₂`: the type and the reader.
  `sharedOf`, **`sharedOf_eq`**: what the third chain's start reads of the shared chain's last state
    (`SharedSh`, E2E/KeyShapeDoor.lean) is a function of this shape.
  **`gTest₂`**, **`test₂_carries`**: a seated proximity test on the shape, and (B1): over
    E2E/KeyShapeShared.lean's `seat_core` and `seat_mark`.
  `gEnd₂`, `end₂_law`, `end₂_carries`, `end₂_returns`: the chain's end: two clauses on the
    statement's shape; no test on values.
  **`Z₂`**: the letters. n: how many sub-protocols stand in front of the test on G_u.
  `carries_gu`, `carries_gomega`, `carries_end₂`: (B1) at these numbers of the description's own
    flat list (cut by the library's `keyShared_cut`).
  **`eight_tidy`**: the mark is kept by a step of each of the eight: ONE CALL of the library's
    `blocksOr_steps`.
  `withMark`, `carries_withMark`: from (B1) on `Sh2` alone and "the step keeps the mark" to (B1)
    with the mark.
  **`carries_all₂`**: (B1) at every number, FROM (B1) AT THE NUMBERS IN FRONT OF THE TEST ON G_u, a
    named premise.

Limits.
- The premise is paid nowhere here: the hash build's files on the eight (Johnson/Desc/K14/Shape/)
  state their laws on `Sh2`; `carries_withMark` and `eight_tidy` are not laid together with them
  at the description's list.
- (B2) of the two tests is not here: `testCore` asks fewer guards than the test.
- The two conditions on each test's place are premises; in scope: `shared_places_in_scope`.


-/
import E2E.KeyShapeShared
import Johnson.Desc.K14.Shape.Lin
import Johnson.Desc.K14.Quiet
import Johnson.Desc.Tidy.Stay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.AtFiles
open OnBytes OnBytes.Params
open ProofFile.Honest (Shape Carries Returns CarriesR ReturnsR carries_seat returns_seat)
open ProofFile.Honest.Sh (testCore)
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts)
open _root_.Desc.K14 (St Lin)
open _root_.Desc.K14.Shape (Sh2 sh2)

/-- **The shared chain's shape**: the hash build's, and the mark on the statement beside it. -/
abbrev Sh₂ : Type := Sh2 × Bool

/-- **The reader.** -/
def sh₂ (d : St) : Sh₂ := (sh2 d, stTidyB d.st)

/-- What the third chain's start reads of it. -/
def sharedOf (a : Sh₂) : SharedSh :=
  ⟨a.2, a.1.core.st, a.1.core.book, a.1.lin.psi, a.1.lin.oOmega⟩

theorem sharedOf_eq (d : St) : sharedOf (sh₂ d) = sharedSh d := rfl

/-- **A seated proximity test on the shape.** grp, mask: which of the noted numbers the seat hands
the test. -/
def gTest₂ (p : P12) (grp : _root_.Desc.K14.Shape.LinSh → Nat)
    (mask : _root_.Desc.K14.Shape.LinSh → Option Nat) (a : Sh₂) : Except String Sh₂ :=
  if a.2 && a.1.core.st.codes.lengthsOk then
    match testCore p a.1.core (grp a.1.lin) (mask a.1.lin) with
    | some c => .ok ({ a.1 with core := c }, true)
    | none => .error "a proximity test of the shared chain: a guard on the core's shape"
  else .error "the mark on the statement, or the codes' message lengths"

/-- **(B1).** -/
theorem test₂_carries (g : Lin → Nat) (mask : Lin → Option Nat)
    (grp : _root_.Desc.K14.Shape.LinSh → Nat) (maskS : _root_.Desc.K14.Shape.LinSh → Option Nat)
    (hg : ∀ l, grp (_root_.Desc.K14.Shape.linSh l) = g l)
    (hm : ∀ l, maskS (_root_.Desc.K14.Shape.linSh l) = mask l) (p : P12) (he : p.early = true)
    (ha : p.answers = 1) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    CarriesR sh₂ (fun d => (Block.inside (VerifiableInference.Desc.K12.Seat.enter g mask)
      (proximityTestKind guardedProximityTestParts p : Block T12 Unit) VerifiableInference.Desc.K12.Seat.leave).decide d rs gs)
      (gTest₂ p grp maskS) := by
  intro d d' t hf hgt
  obtain ⟨c, hloc, -⟩ := seat_core g mask p he ha d d' rs gs hf
  unfold gTest₂ at hgt
  split at hgt
  · rename_i hmk
    rw [Bool.and_eq_true] at hmk
    have hT : stTidyB d.st = true := hmk.1
    have hl : d.st.codes.lengthsOk = true := hmk.2
    have c' : testCore p (sh₂ d).1.core (grp (sh₂ d).1.lin) (maskS (sh₂ d).1.lin) =
        some (coreSh ⟨d'.st, d'.book, d'.roots⟩) := by
      show testCore p (coreSh ⟨d.st, d.book, d.roots⟩) (grp (_root_.Desc.K14.Shape.linSh d.loc))
        (maskS (_root_.Desc.K14.Shape.linSh d.loc)) = _
      rw [hg, hm]
      exact c
    rw [c'] at hgt
    obtain rfl := Except.ok.inj hgt
    have hT' := seat_mark g mask p d d' rs gs hf hl hT
    show ((⟨coreSh ⟨d'.st, d'.book, d'.roots⟩, _root_.Desc.K14.Shape.linSh d.loc⟩ : Sh2), true) =
      ((⟨coreSh ⟨d'.st, d'.book, d'.roots⟩, _root_.Desc.K14.Shape.linSh d'.loc⟩ : Sh2),
        stTidyB d'.st)
    rw [hloc, hT']
  · cases hgt

/-- **The chain's end on the shape.** -/
def gEnd₂ (a : Sh₂) : Except String Sh₂ :=
  if untestedSh a.1.core.st then .ok a else .error "the shared chain's end: something is untested"

theorem end₂_law (front : List (Block St Unit)) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    (VerifiableInference.Desc.K12.Seat.last front).decide d rs gs = .ok d' ↔
      d' = d ∧ untestedSh (stSh d.st) = true := by
  rw [untestedSh_eq, ← refuse_iff]
  show (VerifiableInference.Desc.ChainEnd.refuse
    (VerifiableInference.Desc.ChainEnd.untestedL d.st)).map (fun _ => d) = .ok d' ↔ _
  cases VerifiableInference.Desc.ChainEnd.refuse
      (VerifiableInference.Desc.ChainEnd.untestedL d.st) with
  | error w => exact ⟨fun h => (by cases h), fun h => (by cases h.2)⟩
  | ok u => exact ⟨fun h => ⟨(Except.ok.inj h).symm, rfl⟩, fun h => by rw [h.1]; rfl⟩

theorem end₂_carries (front : List (Block St Unit)) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    CarriesR sh₂ (fun d => (VerifiableInference.Desc.K12.Seat.last front).decide d rs gs)
      gEnd₂ := by
  intro d d' t hf hg
  obtain ⟨rfl, -⟩ := (end₂_law front d d' rs gs).1 hf
  unfold gEnd₂ at hg
  split at hg
  · exact (Except.ok.inj hg).symm
  · cases hg

theorem end₂_returns (front : List (Block St Unit)) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    ReturnsR sh₂ (fun d => (VerifiableInference.Desc.K12.Seat.last front).decide d rs gs) gEnd₂
      (fun _ => true) := by
  intro d t hg _
  unfold gEnd₂ at hg
  split at hg
  · rename_i c
    exact ⟨d, (end₂_law front d d rs gs).2 ⟨rfl, c⟩⟩
  · cases hg

/-! ## The letters, and (B1) along the description's own list -/

/-- **The letters of the cut, for the shared chain.** n: how many sub-protocols stand in front of
the test on G_u; gK, v: the letters at these, and all named tests on values. -/
def Z₂ (P : VerifiableInference.Desc.Key.LaterPlaces) (n : Nat)
    (gK : Nat → Sh₂ → Except String Sh₂)
    (v : Nat → St → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) : Shape St where
  Sh := Sh₂
  sh := sh₂
  g := fun b =>
    if b < n then gK b
    else if b = n then gTest₂ (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) (·.gU) (·.firstMask)
    else match P.O with
      | some nO =>
        if b = n + 1 then gTest₂ (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) (·.gOmega) (fun _ => none)
        else gEnd₂
      | none => gEnd₂
  vals := v

section At
variable (c : OnBytes.Model.Verify.Chains) (P : VerifiableInference.Desc.Key.LaterPlaces)
  (gK : Nat → Sh₂ → Except String Sh₂)
  (v : Nat → St → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) (ft : Nat)

/-- The description's own flat list of the shared chain. -/
abbrev flat₂ : List (Block St VerifiableInference.Desc.Key.Claim) :=
  ((VerifiableInference.Desc.Key.sharedChain c P).retype
    (Cl' := VerifiableInference.Desc.Key.Claim)).blocksInOrder

theorem flat₂_cut : flat₂ c P = H2K.JointK.keySharedPre c P ++ H2K.JointK.keyGu P ::
    ((P.O.toList.map H2K.JointK.keyOmega) ++ [H2K.JointK.keySharedEnd c P]) :=
  H2K.JointK.keyShared_cut c P

/-- The letters at the description's own count. -/
abbrev Z₂At : Shape St := Z₂ P (H2K.JointK.keySharedPre c P).length gK v

theorem carries_gu (he : (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U).early = true)
    (ha : (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U).answers = 1) :
    Carries (flat₂ c P) ft (Z₂At c P gK v) (H2K.JointK.keySharedPre c P).length := by
  have e : (flat₂ c P)[(H2K.JointK.keySharedPre c P).length]? = some (H2K.JointK.keyGu P) := by
    rw [flat₂_cut, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  refine carries_seat e fun _ _ _ => ?_
  show CarriesR sh₂ _ (if _ < _ then _ else if _ = _ then _ else _)
  rw [if_neg (Nat.lt_irrefl _), if_pos rfl]
  exact test₂_carries (·.gU) (·.firstMask) (·.gU) (·.firstMask) (fun _ => rfl) (fun _ => rfl) _ he
    ha _ _

theorem carries_gomega (nO : H2U.PlaceNums) (hO : P.O = some nO)
    (he : (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).early = true)
    (ha : (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).answers = 1) :
    Carries (flat₂ c P) ft (Z₂At c P gK v) ((H2K.JointK.keySharedPre c P).length + 1) := by
  have e : (flat₂ c P)[(H2K.JointK.keySharedPre c P).length + 1]? =
      some (H2K.JointK.keyOmega nO) := by
    rw [flat₂_cut, hO, List.getElem?_append_right (by omega),
      show (H2K.JointK.keySharedPre c P).length + 1 - (H2K.JointK.keySharedPre c P).length = 1 by
        omega]
    rfl
  refine carries_seat e fun _ _ _ => ?_
  show CarriesR sh₂ _ (if _ < _ then _ else if _ = _ then _ else match P.O with
    | some nO => _
    | none => _)
  rw [if_neg (by omega), if_neg (by omega), hO]
  show CarriesR sh₂ _ (if _ = _ then _ else _)
  rw [if_pos rfl]
  exact test₂_carries (·.gOmega) (fun _ => none) (·.gOmega) (fun _ => none) (fun _ => rfl)
    (fun _ => rfl) _ he ha _ _

/-- At the chain's end, which stands behind the one or the two tests. -/
theorem carries_end₂ :
    Carries (flat₂ c P) ft (Z₂At c P gK v)
      ((H2K.JointK.keySharedPre c P).length + 1 + P.O.toList.length) := by
  have e : (flat₂ c P)[(H2K.JointK.keySharedPre c P).length + 1 + P.O.toList.length]? =
      some (H2K.JointK.keySharedEnd c P) := by
    rw [flat₂_cut]
    cases P.O with
    | none =>
      rw [List.getElem?_append_right (by show _ ≤ _ + 1 + 0; omega)]
      show (_ :: _)[(H2K.JointK.keySharedPre c P).length + 1 + 0 -
        (H2K.JointK.keySharedPre c P).length]? = _
      rw [show (H2K.JointK.keySharedPre c P).length + 1 + 0 -
        (H2K.JointK.keySharedPre c P).length = 1 by omega]
      rfl
    | some nO =>
      rw [List.getElem?_append_right (by show _ ≤ _ + 1 + 1; omega)]
      show (_ :: _)[(H2K.JointK.keySharedPre c P).length + 1 + 1 -
        (H2K.JointK.keySharedPre c P).length]? = _
      rw [show (H2K.JointK.keySharedPre c P).length + 1 + 1 -
        (H2K.JointK.keySharedPre c P).length = 2 by omega]
      rfl
  refine carries_seat e fun _ _ _ => ?_
  have hgE : (Z₂At c P gK v).g ((H2K.JointK.keySharedPre c P).length + 1 + P.O.toList.length) =
      gEnd₂ := by
    show (if _ < _ then _ else if _ = _ then _ else match P.O with
      | some nO => _
      | none => _) = _
    rw [if_neg (by omega), if_neg (by omega)]
    cases P.O with
    | none => rfl
    | some nO =>
      show (if _ = _ then _ else _) = _
      rw [if_neg (by show ¬ (_ + 1 + 1 = _ + 1); omega)]
  rw [hgE]
  exact end₂_carries (_root_.Desc.K14.blocksOr (VerifiableInference.Desc.Key.sharedPar c
    (VerifiableInference.Desc.Key.beforeSharedPoint P)) ++
      VerifiableInference.Desc.Key.sharedTests P) [] []

/-! ### The mark along the sub-protocols in front -/

/-- **The mark on the statement is kept by a step of each of the linear claim's eight
sub-protocols**, where its own test on public values passes: the library's `blocksOr_steps` at
`groundQuiet_tidy` and `admitOn_tidy`. -/
theorem eight_tidy (Q : _root_.Desc.K14.P14) (b : Block St Unit)
    (hb : b ∈ _root_.Desc.K14.blocksOr Q) (hp : b.planOk = true) (s s' : St) (rs : List Fmt.RoundView)
    (cols : List VerifiableInference.Desc.OpenedColumn) (k : Nat) (h : b.step ft s rs cols = .ok (s', k))
    (hT : stTidyB s.st = true) : stTidyB s'.st = true :=
  tidy_mark (_root_.Desc.K14.blocksOr_steps VerifiableInference.Desc.Ground.groundQuiet_tidy
    VerifiableInference.Desc.Ground.admitOn_tidy Q b hb hp ft s rs cols s' k h (tidy_of hT))

/-- A letter on `Sh2` alone, with the mark asked and laid beside it. -/
def withMark (g2 : Sh2 → Except String Sh2) (a : Sh₂) : Except String Sh₂ :=
  if a.2 then (g2 a.1).map fun t => (t, true) else .error "the mark on the statement"

/-- **From (B1) on `Sh2` alone and "the step keeps the mark" to (B1) on the shape with the mark.**
-/
theorem carries_withMark {Cl : Type} {bs : List (Block St Cl)} {b : Nat}
    (g2 : Sh2 → Except String Sh2)
    (h2 : ∀ blk, bs[b]? = some blk → ∀ s rs cols s' n t, blk.step ft s rs cols = .ok (s', n) →
      g2 (sh2 s) = .ok t → t = sh2 s')
    (hT : ∀ blk, bs[b]? = some blk → ∀ s rs cols s' n, blk.step ft s rs cols = .ok (s', n) →
      stTidyB s.st = true → stTidyB s'.st = true) :
    ∀ blk, bs[b]? = some blk → ∀ s rs cols s' n t, blk.step ft s rs cols = .ok (s', n) →
      withMark g2 (sh₂ s) = .ok t → t = sh₂ s' := by
  intro blk hblk s rs cols s' n t hs hg
  unfold withMark at hg
  split at hg
  · rename_i hm
    cases hy : g2 (sh₂ s).1 with
    | error e =>
      rw [hy] at hg
      cases hg
    | ok y =>
      rw [hy] at hg
      obtain rfl := Except.ok.inj hg
      rw [h2 blk hblk s rs cols s' n y hs hy]
      exact Prod.ext rfl (hT blk hblk s rs cols s' n hs hm).symm
  · cases hg

/-- **(B1) at every number, from (B1) at the numbers in front of the test on G_u.** -/
theorem carries_all₂
    (hK : ∀ b, b < (H2K.JointK.keySharedPre c P).length → Carries (flat₂ c P) ft (Z₂At c P gK v) b)
    (hU : (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U).early = true ∧
      (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U).answers = 1)
    (hOm : ∀ nO, P.O = some nO → (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).early = true ∧
      (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).answers = 1) (j : Nat) :
    Carries (flat₂ c P) ft (Z₂At c P gK v) j := by
  by_cases h1 : j < (H2K.JointK.keySharedPre c P).length
  · exact hK j h1
  by_cases h2 : j = (H2K.JointK.keySharedPre c P).length
  · subst h2
    exact carries_gu c P gK v ft hU.1 hU.2
  by_cases h3 : j = (H2K.JointK.keySharedPre c P).length + 1 + P.O.toList.length
  · subst h3
    exact carries_end₂ c P gK v ft
  cases hO : P.O with
  | none =>
    intro blk hb
    rw [flat₂_cut, hO] at hb
    rw [hO] at h3
    have hlen := (List.getElem?_eq_some_iff.1 hb).1
    simp only [List.length_append, List.length_cons, List.length_nil, Option.toList_none,
      List.map_nil] at hlen h3
    omega
  | some nO =>
    rw [hO] at h3
    by_cases h4 : j = (H2K.JointK.keySharedPre c P).length + 1
    · subst h4
      exact carries_gomega c P gK v ft nO hO (hOm nO hO).1 (hOm nO hO).2
    · intro blk hb
      rw [flat₂_cut, hO] at hb
      have hlen := (List.getElem?_eq_some_iff.1 hb).1
      simp only [List.length_append, List.length_cons, List.length_nil, Option.toList_some,
        List.map_cons, List.map_nil] at hlen h3
      omega

end At

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.sharedOf_eq
#print axioms AtPublicFiles.AtFiles.test₂_carries
#print axioms AtPublicFiles.AtFiles.end₂_law
#print axioms AtPublicFiles.AtFiles.end₂_carries
#print axioms AtPublicFiles.AtFiles.end₂_returns
#print axioms AtPublicFiles.AtFiles.flat₂_cut
#print axioms AtPublicFiles.AtFiles.carries_gu
#print axioms AtPublicFiles.AtFiles.carries_gomega
#print axioms AtPublicFiles.AtFiles.carries_end₂
#print axioms AtPublicFiles.AtFiles.eight_tidy
#print axioms AtPublicFiles.AtFiles.carries_withMark
#print axioms AtPublicFiles.AtFiles.carries_all₂
