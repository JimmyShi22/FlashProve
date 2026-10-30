-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/ChainCols.lean: Block.step's second test, "the columns", AT THE VIEW OF THE
COPY's FILE's FRAME (viewOf, Johnson/Prover/Link/LinkFrame.lean): under a closed test on public data
the library's list of what is wanted is groupsOf's list in a row, and the view's opened list is
that list looked up by key. Statements and proofs.

  storedKey_item  the two texts of a stored string's key
  stored_part, opens_part   one round's two shares
  wantedXL_groups, wanted_groups   UNDER wantTie: wantedX a ds xs Ds (OnBytes/TypedOracleCompiler/Run/PlanQX.lean)
                  IS groupsOf 0 decls Ds (Johnson/Desc/Block.lean), all groups in a row, keys and
                  positions: at every list of draws
  opened_look     the view's opened list, by lookV
  colsFor_look    what is served, looked up, is the list of the columns at the wanted keys and
                  positions
  opened_colsFor  so, where all that is wanted is served, the view's opened list is colsFor's
  opened_kpw      and has, in key, position and width, just what the declared rounds read

Limits. wantTie is a premise: a closed test with code; at the copy's file's written
letters, both sizes, it is evaluated in Johnson/Prover/Link/ChainAtFull.lean (fr_wantTie,
sr_wantTie). Served is a premise. Widths are Served's, not wantTie's. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.ChainDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open VerifiableInference.Desc
open VerifiableInference.Desc.Plain.One (lookY colsFor)
open _root_.Run.PQ (XO SgX xsAt storedKey xPos)
open TypedOracleCompiler.Run.PQ (RD treeSh wantedX wantedXL)
open _root_.Iop (twoExternalStrings)

/-- The two texts of a stored string's key. -/
theorem storedKey_item (i : ℕ) (h : i < 2) : storedKey (i == 1) = Fmt.storedKey i := by
  unfold storedKey
  rcases Nat.lt_or_ge i 1 with h0 | h1
  · obtain rfl : i = 0 := by omega
    rfl
  · obtain rfl : i = 1 := by omega
    rfl

/-- One round's stored parts. -/
theorem stored_part (a : ℕ) (D : Fmt.Drawn) : ∀ (os : List XO) (ss : List Fmt.Stored),
    os.map (fun o => (o.which, o.from_, o.count)) =
      ss.map (fun s => (s.item == 1, s.lo, s.count)) →
    (∀ s ∈ ss, s.sh.a = a ∧ s.item < 2) →
    os.flatMap (fun o => (o.list a D).map fun x => (storedKey o.which, x)) =
      ((ss.map fun s => (Fmt.listOf ((Fmt.partOf s D.poss).map (· % 2 ^ s.sh.a))).map fun x =>
        (Fmt.storedKey s.item, x, s.sh.W)).flatMap id).map fun w => (w.1, w.2.1)
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | o :: os, s :: ss, h, hs => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨e1, e2, e3⟩, h'⟩ := h
    obtain ⟨ea, ei⟩ := hs s List.mem_cons_self
    have ih := stored_part a D os ss h' fun s' hs' => hs s' (List.mem_cons_of_mem _ hs')
    have hk : storedKey o.which = Fmt.storedKey s.item := by
      rw [e1]
      exact storedKey_item _ ei
    rw [List.flatMap_cons, ih, List.map_cons, List.flatMap_cons, List.map_append]
    congr 1
    show (XO.list a o D).map _ = ((Fmt.listOf _).map _).map _
    rw [List.map_map, hk]
    unfold XO.list XO.raw Fmt.partOf
    rw [e2, e3, ea]
    rfl

/-- One round's opened trees. -/
theorem opens_part {β : Type} (all : List RD) (D : Fmt.Drawn) : ∀ os : List (Fmt.Shape × β),
    (∀ o ∈ os, (treeSh all o.1.tree).map (·.a) = some o.1.a) →
    (os.map (·.1.tree)).flatMap (fun n =>
      match treeSh all n with
      | none => []
      | some s => (Fmt.listOf (D.poss.map (· % 2 ^ s.a))).map fun x => (n, x)) =
      ((os.map fun o => (Fmt.listOf (D.poss.map (· % 2 ^ o.1.a))).map fun x =>
        (o.1.tree - 0, x, o.1.W)).flatMap id).map fun w => (w.1, w.2.1)
  | [], _ => rfl
  | o :: os, h => by
    have ih := opens_part all D os fun o' ho' => h o' (List.mem_cons_of_mem _ ho')
    obtain ⟨s, hs, e⟩ := Option.map_eq_some_iff.1 (h o List.mem_cons_self)
    rw [List.map_cons, List.flatMap_cons, ih, List.map_cons, List.flatMap_cons, List.map_append]
    congr 1
    rw [hs]
    show (Fmt.listOf _).map _ = ((Fmt.listOf _).map _).map _
    rw [List.map_map, e]
    rfl

/-- From round number i on. -/
theorem wantedXL_groups (a : ℕ) (all : List RD) (xs : List XO) :
    ∀ (i : ℕ) (ds : List RD) (decls : List Fmt.DeclaredRound) (Ds : List Fmt.Drawn),
    ds.length = decls.length →
    ((ds.zip decls).zipIdx i).all (fun r => wantTie1 a all xs r.2 r.1.1 r.1.2) = true →
    wantedXL a all xs i ds Ds = ((groupsOf 0 decls Ds).flatMap id).map fun w => (w.1, w.2.1)
  | _, [], [], Ds, _, _ => by cases Ds <;> rfl
  | _, [], _ :: _, _, h, _ => by simp at h
  | _, _ :: _, [], _, h, _ => by simp at h
  | _, _ :: _, _ :: _, [], _, _ => rfl
  | i, w :: ds, d :: decls, D :: Ds, hl, h => by
    simp only [List.zip_cons_cons, List.zipIdx_cons, List.all_cons, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have ih := wantedXL_groups a all xs (i + 1) ds decls Ds (Nat.succ.inj hl) h2
    simp only [wantTie1, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h1
    obtain ⟨⟨⟨t1, t2⟩, t3⟩, t4⟩ := h1
    unfold wantedXL groupsOf
    rw [ih, List.flatMap_append, List.flatMap_append, List.map_append, List.map_append,
      ← stored_part a D _ _ t1 t2, ← opens_part all D _ t4, ← t3]
    rfl

/-- **Under the closed test the library's list of what is wanted is groupsOf's.** -/
theorem wanted_groups (a : ℕ) (ds : List RD) (xs : List XO) (decls : List Fmt.DeclaredRound)
    (h : wantTie a ds xs decls = true) (Ds : List Fmt.Drawn) :
    wantedX a ds xs Ds = ((groupsOf 0 decls Ds).flatMap id).map fun w => (w.1, w.2.1) := by
  simp only [wantTie, Bool.and_eq_true, beq_iff_eq] at h
  exact wantedXL_groups a ds xs 0 ds decls Ds h.1 h.2

/-- The view's opened list, by lookV. -/
theorem opened_look (ds : List RD) (a : ℕ) (xs : List XO) (next : ℕ → List Fmt.Drawn → MsgV)
    (y : (twoExternalStrings (2 ^ a) SgX).Str) (Ds : List Fmt.Drawn) :
    (viewOf ds a xs next y Ds).opened = (wantedX a ds xs Ds).filterMap fun kx =>
      (lookV ds a next y Ds kx.1 kx.2).map fun c => (kx.1, kx.2, c) := by
  show (wantedX a ds xs Ds).filterMap _ = _
  congr 1
  funext kx
  unfold lookV lookY
  by_cases h0 : kx.1 = storedKey false
  · rw [if_pos h0, if_pos h0, Option.map_map]
    rfl
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : kx.1 = storedKey true
    · rw [if_pos h1, if_pos h1, Option.map_map]
      rfl
    · rw [if_neg h1, if_neg h1]

/-- What is served, looked up. -/
theorem colsFor_look (L : ℕ → ℕ → Option (List UInt64)) : ∀ ws : List (ℕ × ℕ × ℕ), Served L ws →
    colsFor L ws = some ((ws.map fun w => (w.1, w.2.1)).filterMap fun kx =>
      (L kx.1 kx.2).map fun c => (kx.1, kx.2, c))
  | [], _ => rfl
  | w :: ws, h => by
    obtain ⟨c, hc, -⟩ := h w List.mem_cons_self
    have ih := colsFor_look L ws fun w' hw' => h w' (List.mem_cons_of_mem _ hw')
    show (match L w.1 w.2.1, colsFor L ws with
      | some c, some cs => some ((w.1, w.2.1, c) :: cs)
      | _, _ => none) = _
    rw [hc, ih, List.map_cons, List.filterMap_cons_some (b := (w.1, w.2.1, c)) (by rw [hc]; rfl)]

/-- **Where all that is wanted is served, the view's opened list is colsFor's.** -/
theorem opened_colsFor (ds : List RD) (a : ℕ) (xs : List XO) (decls : List Fmt.DeclaredRound)
    (next : ℕ → List Fmt.Drawn → MsgV) (y : (twoExternalStrings (2 ^ a) SgX).Str) (Ds : List Fmt.Drawn)
    (h : wantTie a ds xs decls = true)
    (hs : Served (lookV ds a next y Ds) ((groupsOf 0 decls Ds).flatMap id)) :
    colsFor (lookV ds a next y Ds) ((groupsOf 0 decls Ds).flatMap id) =
      some (viewOf ds a xs next y Ds).opened := by
  rw [opened_look, wanted_groups a ds xs decls h Ds]
  exact colsFor_look _ _ hs

/-- And it has, in key, position and width, just what the declared rounds read: Block.step's test on
the columns, whole, for whoever goes by foldBlocks and not by Walks. -/
theorem opened_kpw (ds : List RD) (a : ℕ) (xs : List XO) (decls : List Fmt.DeclaredRound)
    (next : ℕ → List Fmt.Drawn → MsgV) (y : (twoExternalStrings (2 ^ a) SgX).Str) (Ds : List Fmt.Drawn)
    (h : wantTie a ds xs decls = true)
    (hs : Served (lookV ds a next y Ds) ((groupsOf 0 decls Ds).flatMap id)) :
    ((viewOf ds a xs next y Ds).opened.map fun c => (c.1, c.2.1, c.2.2.length)) =
      (groupsOf 0 decls Ds).flatMap id := by
  rw [opened_look, wanted_groups a ds xs decls h Ds]
  generalize (groupsOf 0 decls Ds).flatMap id = ws at hs
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    obtain ⟨c, hc, hl⟩ := hs w List.mem_cons_self
    rw [List.map_cons, List.filterMap_cons_some (b := (w.1, w.2.1, c)) (by rw [hc]; rfl),
      List.map_cons, ih fun w' hw' => hs w' (List.mem_cons_of_mem _ hw')]
    show (w.1, w.2.1, c.length) :: ws = w :: ws
    rw [hl]

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.storedKey_item
#print axioms Johnson.Prover.Link.stored_part
#print axioms Johnson.Prover.Link.opens_part
#print axioms Johnson.Prover.Link.wantedXL_groups
#print axioms Johnson.Prover.Link.wanted_groups
#print axioms Johnson.Prover.Link.opened_look
#print axioms Johnson.Prover.Link.colsFor_look
#print axioms Johnson.Prover.Link.opened_colsFor
#print axioms Johnson.Prover.Link.opened_kpw
