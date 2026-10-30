-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Law/PassAt.lean: AT THE WRITTEN WIRES THE TESTS OF WORK ARE A FUNCTION OF THE
ANSWER's FIRST BLOCK: the premise TestsAt (OnBytes/Prover/FirstBlock.lean) is met, by one written
function passAt, at the wire record of a whole file (wqWhole, OnBytes/Maker/Wire.lean) and of the
copy's file (wqW, Johnson/RunOne/StrictLinkW.lean).

Main names.
  passAt work   A DEFINITION, with code: of a Fiat-Shamir query and a block: if the query's plain
    part is of the round whose number the query holds: are the first work t round bits of the block
    0; else yes. It names no goal's form.
  workL ds      A DEFINITION: the bits of work by the round's number over the copy's file, at the
    letters of linkSkeletonOfRoundData (none at round 0). (Over a whole file: the library's Page.workAt,
    OnBytes/Maker/Page/Fill.lean. Over an entry's description: workE, OnBytes/TypedOracleCompiler/Run/EntryFb.lean:
    of another type.)
  passAt_off    a query that holds another round's plain part is asked whole.
  passAt_zero   so is a query of a round without work.
  depth_left, depth_right   PlainPart.depth (Johnson/TypedOracleCompiler/RecCompile/SeedsApart.lean) through the two
    injections over ++.
  testIs_work   one written round's record against passAt.
  testsAt_app   TestsAt through WireSB.app.
  testsAt_wiresLo, testsAt_wiresSh, testsAt_wiresSL   a stretch of written rounds.
  workAt_J, workAt_S, workAt_1, workAt_2, workAt_3   the library's Page.workAt at the numbers that
    the walk over ++ yields (by rdAt_one, rdAt_two, rdAt_three, workAt_of).
  testsAt_file  three stretches, each behind a round without a test.
  testsAt_wqWhole, testsAt_wqW   THE STATEMENTS.

What they ask. embP keeps the round's number (PlainPart.depth (embP z) = PlainPart.depth z: at embP := id by
unfolding); work under the file's tag is the data's.

Limits. Nothing on which data stand where verify() stands. No bound on work is asked: beyond 256
bits testBits lays false, here and in the wire. Nothing on what a query's head or roots hold.
Nothing on soundness or completeness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Law.FirstBlockLaws
import Johnson.TypedOracleCompiler.RecCompile.SeedsApart
import Johnson.RunOne.StrictLinkW
import OnBytes.Maker.WorkFromHash
import OnBytes.Maker.Page.FillLaws

set_option autoImplicit false

namespace OnBytes.Prover
open _root_.Run _root_.Run.PQ Compile.Joined
open _root_.Compile (Tag)
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Joined OnBytes.Maker
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} (L : BatchProtocolWithLeafBody I X)

/-- The test by the place and by numbers of bits. work t i: the bits of work of round number i under
the tag t. A query whose plain part is not of the round whose number it holds is asked whole. -/
def passAt (work : Tag → ℕ → ℕ) : Pass 256 L := fun t q b =>
  if q.round = PlainPart.depth (shapeOf L t) (annOf L t) q.plain then
    decide (∀ i : Fin (work t q.round), testBits 256 (work t q.round) b i = false)
  else true

/-- The bits of work by the round's number over the copy's file: none at round 0; 0 beyond the
list's end (getD). -/
def workL (ds : List TypedOracleCompiler.Run.PQ.RD) (i : ℕ) : ℕ := (0 :: ds.map (·.entry.work)).getD i 0

variable (work : Tag → ℕ → ℕ) (t : Tag)

/-- A query that holds another round's plain part is asked whole. -/
theorem passAt_off (q : FbIn 256 L t) (b : Dig 256)
    (h : q.round ≠ PlainPart.depth (shapeOf L t) (annOf L t) q.plain) : passAt L work t q b = true :=
  if_neg h

/-- The test at n bits. -/
theorem passAt_on (q : FbIn 256 L t) (b : Dig 256) (n : ℕ)
    (h : q.round = PlainPart.depth (shapeOf L t) (annOf L t) q.plain) (hw : work t q.round = n) :
    passAt L work t q b = decide (∀ i : Fin n, testBits 256 n b i = false) := by
  subst hw
  exact if_pos h

/-- A query of a round without work is asked whole. -/
theorem passAt_zero (q : FbIn 256 L t) (b : Dig 256) (hw : work t q.round = 0) :
    passAt L work t q b = true := by
  by_cases h : q.round = PlainPart.depth (shapeOf L t) (annOf L t) q.plain
  · rw [passAt_on L work t q b 0 h hw]
    exact decide_eq_true fun i => i.elim0
  · exact passAt_off L work t q b h

/-! ## The round's number through ++ -/

theorem depth_left : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u} (z : PlainPart s A),
    PlainPart.depth (s ++ u) (RoundSplits.app A B) (PB.left z) = PlainPart.depth s A z
  | [], _, _, _, z => nomatch z
  | _ :: _, _, (_, _), _, .inl _ => rfl
  | _ :: s, u, (_, A), B, .inr z => congrArg (· + 1) (depth_left (s := s) (u := u) (B := B) z)

theorem depth_right : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u} (z : PlainPart u B),
    PlainPart.depth (s ++ u) (RoundSplits.app A B) (PB.right z) = s.length + PlainPart.depth u B z
  | [], _, _, _, _ => (Nat.zero_add _).symm
  | _ :: s, u, (_, A), B, z => by
    show PlainPart.depth (s ++ u) (RoundSplits.app A B) (PB.right z) + 1 = (s.length + 1) + PlainPart.depth u B z
    rw [depth_right (s := s) (A := A) z]
    omega

/-! ## One round -/

section Round
variable {K : ℕ}

/-- **One written round's record against passAt.** -/
theorem testIs_work {Cc P : Type} (ch : (Fin K → Dig 256) → Cc) (i : ℕ) :
    ∀ (b : ℕ) (plOf : GPlain ℕ b P → PlainPart (shapeOf L t) (annOf L t)),
      (∀ α, PlainPart.depth (shapeOf L t) (annOf L t) (plOf α) = i) → work t i = b →
      TestIs (Nat.succ_pos K) (passAt L work) t i (chalGrind ch b) plOf
        ((grOf Dn Cc P b).map TypedOracleCompiler.Tagged.ofGr)
  | 0, plOf, _, hw => fun h rt α b => passAt_zero L work t ⟨i, h, rt, plOf α⟩ b hw
  | b + 1, plOf, hd, hw => fun h rt α u => by
    rw [passAt_on L work t ⟨i, h, rt, plOf α⟩ _ (b + 1) (hd α).symm hw]
    show decide (testBits 256 (b + 1) (u 0) = fun _ => false) = _
    exact decide_eq_decide.2 ⟨fun e k => congrFun e k, funext⟩

/-- A round with no record of a test, at a number without work. -/
theorem testRound_none {r : Round} {a : RAnn r} (w : WireRB 256 (K + 1) r a) (hJ : w.grJ = none)
    (h0 : w.gr0 = none) (i : ℕ) (pl0 : a.P0 → PlainPart (shapeOf L t) (annOf L t))
    (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (hw : work t i = 0) :
    (match a.kind with
      | .lo => TestIs (Nat.succ_pos K) (passAt L work) t i w.chal plJ w.grJ
      | .sh => TestIs (Nat.succ_pos K) (passAt L work) t i w.chal pl0 w.gr0) := by
  rw [hJ, h0]
  cases a.kind
  · exact fun h rt α b => passAt_zero L work t ⟨i, h, rt, _⟩ b hw
  · exact fun h rt α b => passAt_zero L work t ⟨i, h, rt, _⟩ b hw

end Round

/-! ## Through ++ -/

theorem testsAt_app {lam K : ℕ} (hK : 0 < K) (pass : Pass lam L) :
    ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u} (W : RoundsQueryLayout lam K s A) (V : RoundsQueryLayout lam K u B)
      (i : ℕ) (embP : PlainPart (s ++ u) (RoundSplits.app A B) → PlainPart (shapeOf L t) (annOf L t)),
      TestsAt hK pass t i s A W (fun z => embP (PB.left z)) →
      TestsAt hK pass t (i + s.length) u B V (fun z => embP (PB.right z)) →
      TestsAt hK pass t i (s ++ u) (RoundSplits.app A B) (WireSB.app W V) embP
  | [], _, _, _, _, _, _, _, _, hV => hV
  | r :: s, _, (_, _), _, (_, W), V, i, embP, hW, hV =>
    ⟨hW.1, testsAt_app hK pass W V (i + 1) (fun z => embP (.inr z)) hW.2 (by
      have e : i + (r :: s).length = i + 1 + s.length := by
        rw [List.length_cons]
        omega
      rw [← e]
      exact hV)⟩

/-! ## Stretches of written rounds -/

section Wires
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

theorem testsAt_wiresSL : ∀ (ds : List TypedOracleCompiler.Run.PQ.RD) (i : ℕ)
    (embP : PlainPart (TypedOracleCompiler.Run.PQ.uL C ds) (Twin.allLo (TypedOracleCompiler.Run.PQ.SL C ds)) →
      PlainPart (shapeOf L t) (annOf L t)),
    (∀ z, PlainPart.depth (shapeOf L t) (annOf L t) (embP z) = i + PlainPart.depth _ _ z) →
    (∀ j (h : j < ds.length), work t (i + j) = ds[j].entry.work) →
    TestsAt (Nat.succ_pos K) (passAt L work) t i (TypedOracleCompiler.Run.PQ.uL C ds)
      (Twin.allLo (TypedOracleCompiler.Run.PQ.SL C ds)) (TypedOracleCompiler.Run.PQ.wiresSL C K chal ds) embP
  | [], _, _, _, _ => trivial
  | d :: ds, i, embP, hd, hw =>
    ⟨testIs_work L work t (chal d.entry d.kind) i d.entry.work
        (fun α => embP (.inl (.inr α))) (fun α => hd (.inl (.inr α)))
        (hw 0 (Nat.succ_pos _)),
      testsAt_wiresSL ds (i + 1) (fun z => embP (.inr z))
        (fun z => by
          rw [hd (.inr z)]
          show i + (PlainPart.depth _ _ z + 1) = i + 1 + PlainPart.depth _ _ z
          omega)
        (fun j h => by
          have e := hw (j + 1) (Nat.succ_lt_succ h)
          rw [show i + 1 + j = i + (j + 1) by omega]
          exact e)⟩

theorem testsAt_wiresLo : ∀ (ds : List RDT) (i : ℕ)
    (embP : PlainPart (uLT C ds) (RoundSplits.allLocal (uLT C ds)) → PlainPart (shapeOf L t) (annOf L t)),
    (∀ z, PlainPart.depth (shapeOf L t) (annOf L t) (embP z) = i + PlainPart.depth _ _ z) →
    (∀ j (h : j < ds.length), work t (i + j) = ds[j].entry.work) →
    TestsAt (Nat.succ_pos K) (passAt L work) t i (uLT C ds) (RoundSplits.allLocal (uLT C ds))
      (wiresLo C K chal ds) embP
  | [], _, _, _, _ => trivial
  | d :: ds, i, embP, hd, hw =>
    ⟨testIs_work L work t (chal d.entry d.kind) i d.entry.work
        (fun α => embP (.inl (.inr α))) (fun α => hd (.inl (.inr α)))
        (hw 0 (Nat.succ_pos _)),
      testsAt_wiresLo ds (i + 1) (fun z => embP (.inr z))
        (fun z => by
          rw [hd (.inr z)]
          show i + (PlainPart.depth _ _ z + 1) = i + 1 + PlainPart.depth _ _ z
          omega)
        (fun j h => by
          have e := hw (j + 1) (Nat.succ_lt_succ h)
          rw [show i + 1 + j = i + (j + 1) by omega]
          exact e)⟩

theorem testsAt_wiresSh : ∀ (ds : List RDT) (i : ℕ)
    (embP : PlainPart (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) →
      PlainPart (shapeOf L t) (annOf L t)),
    (∀ z, PlainPart.depth (shapeOf L t) (annOf L t) (embP z) = i + PlainPart.depth _ _ z) →
    (∀ j (h : j < ds.length), work t (i + j) = ds[j].entry.work) →
    TestsAt (Nat.succ_pos K) (passAt L work) t i (uLT C ds)
      (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) (wiresSh C K chal ds) embP
  | [], _, _, _, _ => trivial
  | d :: ds, i, embP, hd, hw =>
    ⟨testIs_work L work t (chal d.entry d.kind) i d.entry.work
        (fun α => embP (.inl (.inl α))) (fun α => hd (.inl (.inl α)))
        (hw 0 (Nat.succ_pos _)),
      testsAt_wiresSh ds (i + 1) (fun z => embP (.inr z))
        (fun z => by
          rw [hd (.inr z)]
          show i + (PlainPart.depth _ _ z + 1) = i + 1 + PlainPart.depth _ _ z
          omega)
        (fun j h => by
          have e := hw (j + 1) (Nat.succ_lt_succ h)
          rw [show i + 1 + j = i + (j + 1) by omega]
          exact e)⟩

end Wires

/-! ## Whole files -/

theorem getD_map_at {α : Type} (f : α → ℕ) (l : List α) (j : ℕ) (h : j < l.length) :
    (l.map f).getD j 0 = f l[j] := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact h), List.getElem_map]

theorem depth_fst {r : Round} {s u : Shape} {a : RAnn r} {A : RoundSplits s} {B : RoundSplits u} (z : PlainPart s A) :
    PlainPart.depth (r :: (s ++ u)) (a, RoundSplits.app A B) (.inr (PB.left z)) = 1 + PlainPart.depth s A z := by
  show PlainPart.depth (s ++ u) (RoundSplits.app A B) (PB.left z) + 1 = _
  rw [depth_left]
  omega

theorem depth_mid {r : Round} {s u : Shape} {a : RAnn r} {A : RoundSplits s} {B : RoundSplits u} (z : PlainPart u B) :
    PlainPart.depth (r :: (s ++ u)) (a, RoundSplits.app A B) (.inr (PB.right z)) =
      1 + s.length + PlainPart.depth u B z := by
  show PlainPart.depth (s ++ u) (RoundSplits.app A B) (PB.right z) + 1 = _
  rw [depth_right]
  omega

/-- **Three stretches, each behind a round without a test.** -/
theorem testsAt_file {K : ℕ} {rF rJ r3 : Round} {s₁ s₂ s₃ : Shape} {aF : RAnn rF} {aJ : RAnn rJ}
    {a3 : RAnn r3} {A₁ : RoundSplits s₁} {A₂ : RoundSplits s₂} {A₃ : RoundSplits s₃} (wF : WireRB 256 (K + 1) rF aF)
    (wJ : WireRB 256 (K + 1) rJ aJ) (w3 : WireRB 256 (K + 1) r3 a3)
    (W₁ : RoundsQueryLayout 256 (K + 1) s₁ A₁) (W₂ : RoundsQueryLayout 256 (K + 1) s₂ A₂) (W₃ : RoundsQueryLayout 256 (K + 1) s₃ A₃)
    (embP : PlainPart (rF :: (s₁ ++ rJ :: (s₂ ++ r3 :: s₃)))
      (aF, RoundSplits.app A₁ (aJ, RoundSplits.app A₂ (a3, A₃))) → PlainPart (shapeOf L t) (annOf L t))
    (hd : ∀ z, PlainPart.depth (shapeOf L t) (annOf L t) (embP z) = PlainPart.depth _ _ z)
    (hF : wF.grJ = none ∧ wF.gr0 = none) (hJ : wJ.grJ = none ∧ wJ.gr0 = none)
    (h3 : w3.grJ = none ∧ w3.gr0 = none) (hw0 : work t 0 = 0)
    (hwJ : work t (1 + s₁.length) = 0) (hw3 : work t (1 + s₁.length + 1 + s₂.length) = 0)
    (H₁ : ∀ e : PlainPart s₁ A₁ → PlainPart (shapeOf L t) (annOf L t),
      (∀ z, PlainPart.depth (shapeOf L t) (annOf L t) (e z) = 1 + PlainPart.depth _ _ z) →
      TestsAt (Nat.succ_pos K) (passAt L work) t 1 s₁ A₁ W₁ e)
    (H₂ : ∀ e : PlainPart s₂ A₂ → PlainPart (shapeOf L t) (annOf L t),
      (∀ z, PlainPart.depth (shapeOf L t) (annOf L t) (e z) = 1 + s₁.length + 1 + PlainPart.depth _ _ z) →
      TestsAt (Nat.succ_pos K) (passAt L work) t (1 + s₁.length + 1) s₂ A₂ W₂ e)
    (H₃ : ∀ e : PlainPart s₃ A₃ → PlainPart (shapeOf L t) (annOf L t),
      (∀ z, PlainPart.depth (shapeOf L t) (annOf L t) (e z) =
        1 + s₁.length + 1 + s₂.length + 1 + PlainPart.depth _ _ z) →
      TestsAt (Nat.succ_pos K) (passAt L work) t (1 + s₁.length + 1 + s₂.length + 1) s₃ A₃ W₃ e) :
    TestsAt (Nat.succ_pos K) (passAt L work) t 0 (rF :: (s₁ ++ rJ :: (s₂ ++ r3 :: s₃)))
      (aF, RoundSplits.app A₁ (aJ, RoundSplits.app A₂ (a3, A₃)))
      (wF, WireSB.app (u := rJ :: (s₂ ++ r3 :: s₃)) (B := (aJ, RoundSplits.app A₂ (a3, A₃))) W₁
        (wJ, WireSB.app (u := r3 :: s₃) (B := (a3, A₃)) W₂ (w3, W₃))) embP := by
  refine ⟨testRound_none L work t wF hF.1 hF.2 0 (fun α => embP (.inl (.inl α)))
      (fun α => embP (.inl (.inr α))) hw0,
    testsAt_app L t (Nat.succ_pos K) (passAt L work) (u := rJ :: (s₂ ++ r3 :: s₃))
      (B := (aJ, RoundSplits.app A₂ (a3, A₃))) W₁
      (wJ, WireSB.app (u := r3 :: s₃) (B := (a3, A₃)) W₂ (w3, W₃)) 1
      (fun z => embP (.inr z)) (H₁ _ fun z => ?_)
      ⟨testRound_none L work t wJ hJ.1 hJ.2 _
          (fun α => embP (.inr (PB.right (.inl (.inl α)))))
          (fun α => embP (.inr (PB.right (.inl (.inr α))))) hwJ,
        testsAt_app L t (Nat.succ_pos K) (passAt L work) (u := r3 :: s₃) (B := (a3, A₃)) W₂
          (w3, W₃) (1 + s₁.length + 1)
          (fun z => embP (.inr (PB.right (.inr z)))) (H₂ _ fun z => ?_)
          ⟨testRound_none L work t w3 h3.1 h3.2 _
              (fun α => embP (.inr (PB.right (.inr (PB.right (.inl (.inl α)))))))
              (fun α => embP (.inr (PB.right (.inr (PB.right (.inl (.inr α))))))) hw3,
            H₃ _ fun z => ?_⟩⟩⟩
  · rw [hd, depth_fst]
  · rw [hd, depth_mid, depth_fst]
    omega
  · rw [hd, depth_mid, depth_mid]
    show 1 + s₁.length + (1 + s₂.length + (PlainPart.depth s₃ A₃ z + 1)) = _
    omega

/-! The library's Page.workAt at the numbers that the walk over ++ yields. -/

section WorkAt
variable (D : WholeD)

theorem workAt_J : Page.workAt D (1 + D.ds₁.length) = 0 := by
  unfold Page.workAt Page.rdAt
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  rfl

theorem workAt_S : Page.workAt D (1 + D.ds₁.length + 1 + D.ds₂.length) = 0 := by
  unfold Page.workAt Page.rdAt
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega)]
  rfl

theorem workAt_1 (j : ℕ) (h : j < D.ds₁.length) :
    Page.workAt D (1 + j) = D.ds₁[j].entry.work :=
  Page.workAt_of D (by
    rw [show 1 + j = 0 + 1 + j by omega, Page.rdAt_one D j h, List.getElem?_eq_getElem h])

theorem workAt_2 (j : ℕ) (h : j < D.ds₂.length) :
    Page.workAt D (1 + D.ds₁.length + 1 + j) = D.ds₂[j].entry.work :=
  Page.workAt_of D (by
    rw [show 1 + D.ds₁.length + 1 + j = D.ds₁.length + 1 + 1 + j by omega, Page.rdAt_two D j h,
      List.getElem?_eq_getElem h])

theorem workAt_3 (j : ℕ) (h : j < D.ds₃.length) :
    Page.workAt D (1 + D.ds₁.length + 1 + D.ds₂.length + 1 + j) = D.ds₃[j].entry.work :=
  Page.workAt_of D (by
    rw [show 1 + D.ds₁.length + 1 + D.ds₂.length + 1 + j =
        D.ds₁.length + D.ds₂.length + 2 + 1 + j by omega, Page.rdAt_three D j,
      List.getElem?_eq_getElem h])

end WorkAt

section Files
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- **THE COPY's FILE.** -/
theorem testsAt_wqW (ds : List TypedOracleCompiler.Run.PQ.RD) (a : ℕ) (xs : List XO) {Y : Type}
    (dec : Y → View → Bool)
    (embP : PlainPart (OnBytes.Flat.linkSkeletonOfRoundData C ds a xs dec).up.loc.shape
      (OnBytes.Flat.linkSkeletonOfRoundData C ds a xs dec).up.ann → PlainPart (shapeOf L t) (annOf L t))
    (hd : ∀ z, PlainPart.depth (shapeOf L t) (annOf L t) (embP z) = PlainPart.depth _ _ z)
    (hw : ∀ i, work t i = workL ds i) :
    TestsAt (Nat.succ_pos K) (passAt L work) t 0 (OnBytes.Flat.linkSkeletonOfRoundData C ds a xs dec).up.loc.shape
      (OnBytes.Flat.linkSkeletonOfRoundData C ds a xs dec).up.ann
      (Johnson.RunOne.StrictW.wqW C ds a xs dec K chal).sh embP :=
  ⟨testRound_none L work t (TypedOracleCompiler.Run.PQ.wire0S C K chal) rfl rfl 0
      (fun α => embP (.inl (.inl α))) (fun α => embP (.inl (.inr α))) (by rw [hw]; rfl),
    testsAt_wiresSL L work t C K chal ds 1 (fun z => embP (.inr z))
      (fun z => by
        rw [hd (.inr z)]
        show PlainPart.depth _ _ z + 1 = 1 + PlainPart.depth _ _ z
        omega)
      (fun j h => by
        rw [hw]
        show (0 :: ds.map (·.entry.work)).getD (1 + j) 0 = _
        rw [Nat.add_comm, List.getD_cons_succ, getD_map_at _ ds j h])⟩

variable (D : WholeD) {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3)
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- **A WHOLE FILE.** -/
theorem testsAt_wqWhole
    (embP : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann →
      PlainPart (shapeOf L t) (annOf L t))
    (hd : ∀ z, PlainPart.depth (shapeOf L t) (annOf L t) (embP z) = PlainPart.depth _ _ z)
    (hw : ∀ i, work t i = Page.workAt D i) :
    TestsAt (Nat.succ_pos K) (passAt L work) t 0 (chainsOf C D tF tJ t3).sh
      (chainsOf C D tF tJ t3).ann (wqWhole C K chal D tF tJ t3 silent run).sh embP := by
  have l₁ : (uLT C D.ds₁).length = D.ds₁.length := length_uLT C D.ds₁
  have l₂ : (uLT C D.ds₂).length = D.ds₂.length := length_uLT C D.ds₂
  refine testsAt_file L work t (wireSilent (K + 1) TF tF _) (wireSilent (K + 1) TJ tJ _)
    (wireSilent (K + 1) T3 t3 _) (wiresLo C K chal D.ds₁) (wiresSh C K chal D.ds₂)
    (wiresLo C K chal D.ds₃) embP hd ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ (by rw [hw]; rfl) ?_ ?_
    (fun e he => testsAt_wiresLo L work t C K chal D.ds₁ 1 e he fun j h => ?_)
    (fun e he => testsAt_wiresSh L work t C K chal D.ds₂ _ e he fun j h => ?_)
    (fun e he => testsAt_wiresLo L work t C K chal D.ds₃ _ e he fun j h => ?_)
  · rw [hw, l₁]
    exact workAt_J D
  · rw [hw, l₁, l₂]
    exact workAt_S D
  · rw [hw]
    exact workAt_1 D j h
  · rw [hw, l₁]
    exact workAt_2 D j h
  · rw [hw, l₁, l₂]
    exact workAt_3 D j h

end Files

end OnBytes.Prover

#print axioms OnBytes.Prover.passAt_off
#print axioms OnBytes.Prover.passAt_on
#print axioms OnBytes.Prover.passAt_zero
#print axioms OnBytes.Prover.depth_left
#print axioms OnBytes.Prover.depth_right
#print axioms OnBytes.Prover.testIs_work
#print axioms OnBytes.Prover.testRound_none
#print axioms OnBytes.Prover.testsAt_app
#print axioms OnBytes.Prover.testsAt_wiresSL
#print axioms OnBytes.Prover.testsAt_wiresLo
#print axioms OnBytes.Prover.testsAt_wiresSh
#print axioms OnBytes.Prover.getD_map_at
#print axioms OnBytes.Prover.workAt_J
#print axioms OnBytes.Prover.workAt_S
#print axioms OnBytes.Prover.workAt_1
#print axioms OnBytes.Prover.workAt_2
#print axioms OnBytes.Prover.workAt_3
#print axioms OnBytes.Prover.depth_fst
#print axioms OnBytes.Prover.depth_mid
#print axioms OnBytes.Prover.testsAt_file
#print axioms OnBytes.Prover.testsAt_wqW
#print axioms OnBytes.Prover.testsAt_wqWhole
