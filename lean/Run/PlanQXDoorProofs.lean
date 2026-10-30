-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQXDoorProofs.lean: the proofs of Run/PlanQXDoor.lean. Many statements of this library are
written twice: a definition in the namespace `Spec` states a proposition, and a theorem of the same
name outside that namespace proves it (lean/GLOSSARY.md).

What this file contains. The proofs of the four statements of Run/PlanQXDoor.lean. They follow the
proofs of Run/M1Door.lean, which treat the interface whose Test is the protocol. The bound on the
reads of one string is proved like the bound on both strings in Run/PlanQXLawsProofs.lean: by
induction over the rounds, with the openings' counts split by the number of the round. `formX`: the
ten conditions of `FormX` at `Lu` and `WkX` (statement and hypotheses: Run/PlanQXDoor.lean).

Notation:
  `All`: the relation `fun _ _ => True` (Run/M1Door.lean);
  `Lu`: the interface of the run function `runEntry`, with the protocol as Link
    (Run/PlanQXDoor.lean);
  `WkX`: the whole wiring of `Lu` (Run/PlanQXDoor.lean);
  `C`: a choice of challenge types: for each round the type of the verifier's message
    (Run/PlanQS.lean);
  `ds`: a list of rounds' data (`List PQ.RD`, Run/PlanQTypes.lean);
  `a`, `xs`: a tree depth, a list of openings of the stored tables (Run/PlanQXDoor.lean);
  `dec`: a decision: a function `View → Bool`.

What is not claimed. See Run/PlanQXDoor.lean, the head: no statement on soundness follows from that
file or from this one. Of the conditions sound and low, which `lu_sound` and, under its hypotheses,
`metX` prove here, one clause has content: the last of `low`, with its event Bad
(`Compile.Batch.BcsAt`, Compile/Batch/SpecSoundG.lean; `extEnc`, `Announced`,
Compile/Batch/Events.lean). Beyond it the two are empty.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PlanQXDoor
import Run.PlanQXLawsProofs

set_option autoImplicit false

namespace Run.PQ
open Iop Rom Compile Compile.Batch
open Run.M1Door (All zErr zErr_below)

theorem wq1_okg (K a : Nat) : (wq1 K a).OKG :=
  { sh := trivial, ext := WireE.one_ok (2 ^ a) SgX (0, []),
    opens := fun _ _ _ => le_refl 0, depth := trivial }

theorem one_depth (a : Nat) : (WireE.one (2 ^ a) SgX (0, [])).depth = a :=
  Nat.clog_pow 2 a Nat.one_lt_two

theorem okgWkX : Spec.okgWkX := fun C ds a xs dec K wL h he hd =>
  { T := wq1_okg K a
    Lk := h
    B := wq1_okg K a
    fits := le_refl _
    slots := rfl
    extDepth := ⟨one_depth a, by show wL.ext.depth = a; rw [he]; rfl, one_depth a⟩
    depthT := le_refl _, depthL := hd, depthB := le_refl _
    extT := fun _ => ⟨rfl, rfl⟩
    extB := fun _ => ⟨rfl, rfl⟩
    extL := ⟨fun p => by
        show wL.ext.which (.inl p) = 0 ∧ wL.ext.leaf (.inl p) = p.val; rw [he]; exact ⟨rfl, rfl⟩,
      fun p => by
        show wL.ext.which (.inr p) = 1 ∧ wL.ext.leaf (.inr p) = p.val; rw [he]; exact ⟨rfl, rfl⟩⟩ }

/-! ## One string's count -/

/-- what xWanted keeps of a pair (key, position), for one string -/
def keepS (b : Bool) (kx : Nat × Nat) : Option (Bool × Nat) := (keepX kx).filter fun wx => wx.1 == b

theorem keepX_key (w : Bool) (x : Nat) : keepX (storedKey w, x) = some (w, x) := by
  cases w with
  | false => exact if_pos rfl
  | true =>
      unfold keepX
      rw [if_neg (show ¬ storedKey true = storedKey false by decide), if_pos rfl]

theorem keepS_other (b w : Bool) (x : Nat) (h : (w == b) = false) :
    keepS b (storedKey w, x) = none := by
  unfold keepS
  rw [keepX_key]
  simp [Option.filter, h]

theorem keepS_own (b : Bool) (kx : Nat × Nat) (h : kx.1 < 2 ^ 16) : keepS b kx = none := by
  unfold keepS
  rw [keepX_own kx h]
  rfl

theorem sideA_len (a : Nat) (D : _root_.Fmt.Drawn) (b : Bool) :
    ∀ L : List XO,
      ((L.flatMap fun o => (o.list a D).map fun x => (storedKey o.which, x)).filterMap
          (keepS b)).length ≤
        ((L.filter fun o => o.which == b).map (·.count)).sum
  | [] => Nat.le_refl 0
  | o :: L => by
      have ih := sideA_len a D b L
      rw [List.flatMap_cons, List.filterMap_append, List.length_append]
      cases hw : (o.which == b) with
      | true =>
          rw [List.filter_cons_of_pos (p := fun o : XO => o.which == b) hw,
            List.map_cons, List.sum_cons]
          refine Nat.add_le_add (le_trans (List.length_filterMap_le _ _) ?_) ih
          rw [List.length_map]
          exact list_len a o D
      | false =>
          rw [List.filter_cons_of_neg (p := fun o : XO => o.which == b)
              (by show ¬ (o.which == b) = true; rw [hw]; simp)]
          have e : (((o.list a D).map fun x => (storedKey o.which, x)).filterMap (keepS b)) =
              [] := by
            rw [List.filterMap_eq_nil_iff]
            intro kx hkx
            obtain ⟨x, _, rfl⟩ := List.mem_map.1 hkx
            exact keepS_other b o.which x hw
          rw [e]
          simpa using ih

theorem xsAt_side (b : Bool) (xs : List XO) (i : Nat) :
    (xsAt xs i).filter (fun o => o.which == b) = xsAt (xs.filter fun o => o.which == b) i := by
  unfold xsAt
  rw [List.filter_filter, List.filter_filter]
  congr 1
  funext o
  exact Bool.and_comm _ _

theorem sideXL_len (a : Nat) (all : List RD) (xs : List XO) (b : Bool) :
    ∀ (i : Nat) (ds : List RD) (Ds : List _root_.Fmt.Drawn), (∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16) →
      ((wantedXL a all xs i ds Ds).filterMap (keepS b)).length ≤
        (((xs.filter fun o => o.which == b).filter fun o => decide (i ≤ o.round)).map (·.count)).sum
  | _, [], _, _ => by simp [wantedXL]
  | _, _ :: _, [], _ => by simp [wantedXL]
  | i, d :: ds, D :: Ds, h => by
      have ih := sideXL_len a all xs b (i + 1) ds Ds fun e he => h e (List.mem_cons_of_mem _ he)
      rw [wantedXL, List.filterMap_append, List.filterMap_append, List.length_append,
        List.length_append, sum_split i (xs.filter fun o => o.which == b), ← xsAt_side]
      refine le_trans
        (Nat.add_le_add
          (Nat.add_le_add (sideA_len a D b _)
            (Nat.le_of_eq
              (congrArg List.length (List.filterMap_eq_nil_iff.2 fun kx hkx => keepS_own b kx ?_))))
          ih) (by simp)
      obtain ⟨n, hn, hm⟩ := List.mem_flatMap.1 hkx
      split at hm
      · cases hm
      · obtain ⟨x, _, rfl⟩ := List.mem_map.1 hm
        exact h d List.mem_cons_self n hn

theorem xSide_len : Spec.xSide_len := by
  intro a ds xs Ds b h
  have h1 := sideXL_len a ds xs b 0 ds Ds h
  rw [List.filter_eq_self.2 (fun o _ => decide_eq_true (Nat.zero_le _))] at h1
  have e : ((xWanted a ds xs Ds).filter fun wx => wx.1 == b) =
      (wantedX a ds xs Ds).filterMap (keepS b) :=
    List.filter_filterMap
  rw [e]
  exact h1

/-! ## The form -/

theorem filterMap_len_le {α β : Type} (g : α → Option β) (p : α → Bool)
    (h : ∀ x, (g x).isSome = true → p x = true) :
    ∀ l : List α, (l.filterMap g).length ≤ (l.filter p).length
  | [] => Nat.le_refl 0
  | x :: l => by
      have ih := filterMap_len_le g p h l
      cases hg : g x with
      | none =>
          rw [List.filterMap_cons_none hg]
          exact le_trans ih (by
            by_cases hp : p x = true
            · rw [List.filter_cons_of_pos hp]; exact Nat.le_succ _
            · rw [List.filter_cons_of_neg hp])
      | some y =>
          rw [List.filterMap_cons_some hg, List.filter_cons_of_pos (h x (by rw [hg]; rfl))]
          exact Nat.succ_le_succ ih

theorem xPos_side (n : Nat) (wx : Bool × Nat) (p : Fin n ⊕ Fin n) (h : xPos n wx = some p) :
    p.isRight = wx.1 := by
  unfold xPos at h
  split at h
  · cases hw : wx.1 with
    | false => rw [hw] at h; cases h; rfl
    | true => rw [hw] at h; cases h; rfl
  · cases h

theorem side_card (ds : List RD) (a : Nat) (xs : List XO) (Ds : List _root_.Fmt.Drawn) (b : Bool)
    (hown : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16) :
    ((((xWanted a ds xs Ds).filterMap (xPos (2 ^ a))).toFinset).filter fun p =>
        (p.isRight == b) = true).card ≤ cntOf b xs := by
  rw [← List.toFinset_filter]
  refine le_trans (List.toFinset_card_le _) ?_
  rw [List.filter_filterMap]
  refine le_trans (filterMap_len_le _ (fun wx => wx.1 == b) (fun wx hs => ?_) _)
    (xSide_len a ds xs Ds b hown)
  cases hp : xPos (2 ^ a) wx with
  | none => rw [hp] at hs; cases hs
  | some p =>
      rw [hp] at hs
      have e := xPos_side _ wx p hp
      cases hb : (p.isRight == b) with
      | true =>
          show (wx.1 == b) = true
          rw [← e]
          exact hb
      | false => simp [Option.filter, hb] at hs

theorem lu_sound (C : CK) (ds : List RD) (a : Nat) (xs : List XO) (dec : View → Bool) :
    (Lu C ds a xs dec).Sound All 0 where
  sndT :=
    ⟨(), trivial, fun _ _ h => absurd (fun e : (some () : Option Unit) = none => by cases e) h⟩
  sndL := ⟨zErr _, zErr_below _ _, fun _ _ h => absurd (Or.inr rfl) h⟩
  sndB := by
    have lang : ∀ _ : Fin (2 ^ a) → SgX,
        (some () : Option Unit) = none ∨ ∃ i, (some () : Option Unit) = some i ∧ All i () :=
      fun _ => Or.inr ⟨(), rfl, trivial⟩
    refine ⟨(), trivial, fun n h => ?_, fun _ _ _ => true, ?_, ?_, ?_, ?_, ?_⟩
    · exact absurd h (by show (none : Option ℕ) ≠ some n; exact fun e => by cases e)
    · intro y x h
      exact absurd (lang y) h
    · intro y x τ
      exact Empty.elim τ
    · intro y x τ
      exact Empty.elim τ
    · intro y x τ h
      exact absurd (lang y) h
    · intro y x
      exact trivial

theorem formX : Spec.formX := fun C ds a xs dec K wL hown h he hd =>
  { okg := okgWkX C ds a xs dec K wL h he hd
    wired := ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩
    reads :=
      { cntT := fun _ _ => le_refl 0
        cntLp := fun _ ρ => by
          have := side_card ds a xs (drawnSL C ds ρ.2) false hown
          refine le_trans
            (Nat.le_of_eq (congrArg Finset.card (Finset.filter_congr fun p _ => ?_))) this
          cases p <;> simp
        cntLc := fun _ ρ => by
          have := side_card ds a xs (drawnSL C ds ρ.2) true hown
          refine le_trans
            (Nat.le_of_eq (congrArg Finset.card (Finset.filter_congr fun p _ => ?_))) this
          cases p <;> simp
        cntB := fun x _ => by
          simp only [BatchInteractiveOracleProof.allReads]
          simp
          cases x 0 <;> rfl
        hidE := fun _ _ _ _ => rfl }
    localT := fun _ _ _ _ _ _ _ _ _ => rfl
    localL := psofX_local C ds a xs dec
    localB := fun _ _ _ _ _ _ _ _ _ => rfl
    cohB := BatchOne.BAnn.allLocal_coherent _
    pointT := ⟨()⟩
    pointL := M1Door.lts_pointT C ds dec
    pointB := ⟨()⟩ }

theorem metX : Spec.metX := fun C ds a xs dec K wL hown h he hd =>
  { form := formX C ds a xs dec K wL hown h he hd
    sound := lu_sound C ds a xs dec
    low := bcsSoundBatchG Unit Unit 256 _ (WkX K wL) All 0 (lu_sound C ds a xs dec)
      (fun _ _ _ _ _ _ _ _ _ => rfl) (psofX_local C ds a xs dec) (fun _ _ _ _ _ _ _ _ _ => rfl)
      (BatchOne.BAnn.allLocal_coherent _) (okgWkX C ds a xs dec K wL h he hd) }

end Run.PQ
