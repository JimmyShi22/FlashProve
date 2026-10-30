-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/LinkFrameView.lean: BESIDE THE COPY's FILE's FRAME
(Johnson/Prover/Link/LinkFrame.lean): three things on the view of the frame's strategy. General in
the rounds' data, the external openings and the messages next.

1 EVERY WORD OF THE VIEW IS BELOW THE PRIME (viewWordsBelowPrime, Johnson/Desc/Block.lean), from: each sent item
  and each word of each sent column is; each word of the two stored strings' columns is. No premise
  of fitting: where an item or a column does not fit, layP and orcT lay 0.
2 NOTHING THAT IS WANTED IS DROPPED: at every own (tree, position) that the draws ask for, the
  view's column is there and is next's.
3 THE PLAY DOES NOT HANG ON THE TEST BITS: what a view shows of the run is the same at ρ and at ρ
  with all test bits set to 0.

Main names (namespace Johnson.Prover.Link).
  okGot   the test on one item: viewWordsBelowPrime's own match, under a name.
  okGot_layP, lt_orcT, lt_colOf, rvOf_drawn, rvOf_vals   the parts.
  okViewW_viewOf   THE STATEMENT of 1, at any draws whose elements pass.
  okViewW_run   the same at the draws of every verifier's randomness, under the kit of the programs'
      field (ltE_drawnSL, Johnson/Prover/Link/ViewWords.lean).
  length_drawnSL, wantedXL_own, seat_of_tree   one draw a round; an own pair that is wanted has a
      tree, a seat and a position below the tree's length.
  colOf_wanted   THE STATEMENT of 2.
  zero_lo, old_zero_grOf, drawn_zero, run_zero   THE STATEMENT of 3, at the written rounds.
  zero_tail   behind the first, empty round the whole wire's "all test bits 0" is the written
      rounds'.

By calls: okViewW_of, ltE_drawnSL (ViewWords.lean); colOf_at, treeSh_seat, run_same
(LinkFrame.lean); listOf_mem (Fmt/Rules6Laws.lean); GChal.old_mk (Iop/GrindProofs.lean).

Limits. The bounds on next's words and widths are asked at every round's number and every history,
also at histories that never occur: more than is spent. okViewW_run stands at one kit. drawn_zero
and run_zero stand at the written rounds; zero_tail ties them to the whole shape, whose first round
is empty. "Own" is said as: the tree's number is below 2 ^ 16. Nothing here says that a verifier
accepts.
Nothing on what next is. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.LinkFrame
import Johnson.Prover.Link.ViewWords

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (ckP)
open _root_.Run.PQ (CK PlainOf View RV XO SgX storedKey xPos Dn)
open TypedOracleCompiler.Run.PQ (RD roundS uL drawnSL rvSL colAtS PosT SymT colT posAtT wireS wiresSL
  wantedX wantedXL treeSh)
open VerifiableInference.Desc (fieldPrimeWord viewWordsBelowPrime)

/-! ## 1 Every word of the view is below the prime -/

/-- The test on one item that a round shows: viewWordsBelowPrime's own (Johnson/Desc/Block.lean). -/
def okGot : Fmt.ItemValue → Bool
  | .f x => decide (x < fieldPrimeWord)
  | .e x => ltE x
  | .answer x => ltE x
  | .word _ => true
  | .root _ => true

theorem zero_lt : (0 : UInt64) < fieldPrimeWord := by decide

theorem ltE_zero : ltE (0, 0, 0) = true := by decide

/-- What layP lays passes, whether the items fit or not: where one does not, 0 is laid. -/
theorem okGot_layP (l : List Fmt.Item) : ∀ g : List Fmt.ItemValue, (∀ g' ∈ g, okGot g' = true) →
    ∀ g' ∈ PlainOf.gots l (layP l g), okGot g' = true := by
  induction l with
  | nil => intro g _ g' h; cases h
  | cons it l ih =>
    intro g hg g' h
    have ht : ∀ g' ∈ g.tail, okGot g' = true := fun x hx => hg x (List.mem_of_mem_tail hx)
    cases it
    case root => exact ih g hg g' h
    all_goals
      rcases List.mem_cons.1 h with rfl | h'
      · cases g with
        | nil => first | exact decide_eq_true zero_lt | exact ltE_zero | rfl
        | cons a g =>
          have ha := hg a List.mem_cons_self
          cases a <;> first | exact ha | exact decide_eq_true zero_lt | exact ltE_zero | rfl
      · exact ih g.tail ht g' h'

/-- A column that orcT lays passes: the fill is 0. -/
theorem lt_orcT : ∀ (ts : List Fmt.Shape) (f : ℕ → ℕ → List UInt64) (p : PosT ts),
    (∀ n x, ∀ w ∈ f n x, w < fieldPrimeWord) → ∀ w ∈ colT ts p (orcT ts f p), w < fieldPrimeWord
  | s :: _, f, .inl x, hf, w, hw => by
      have hw' : w ∈ List.ofFn (fun k : Fin s.W => (f 0 x.val).getD k.val 0) := hw
      obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).1 hw'
      show (f 0 x.val).getD k.val 0 < fieldPrimeWord
      by_cases hk : k.val < (f 0 x.val).length
      · rw [List.getD_eq_getElem _ _ hk]
        exact hf 0 x.val _ (List.getElem_mem hk)
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hk)]
        exact zero_lt
  | _ :: ts, f, .inr p, hf, w, hw =>
      lt_orcT ts (fun n => f (n + 1)) p (fun n x => hf (n + 1) x) w hw

section
variable (next : ℕ → List Fmt.Drawn → MsgV)

theorem rvOf_drawn : ∀ (ds : List RD) (i : ℕ) (hist Ds : List Fmt.Drawn) (r : RV),
    r ∈ rvOf ds i hist next Ds → r.drawn ∈ Ds
  | [], _, _, _, _, h => by simp [rvOf] at h
  | _ :: _, _, _, [], _, h => by simp [rvOf] at h
  | d :: ds, i, hist, D :: Ds, r, h => by
      rcases List.mem_cons.1 h with rfl | h'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (rvOf_drawn ds _ _ Ds r h')

theorem rvOf_vals : ∀ (ds : List RD) (i : ℕ) (hist Ds : List Fmt.Drawn) (r : RV),
    r ∈ rvOf ds i hist next Ds →
    ∃ l i' h', r.vals = PlainOf.gots l (layP l (next i' h').vals)
  | [], _, _, _, _, h => by simp [rvOf] at h
  | _ :: _, _, _, [], _, h => by simp [rvOf] at h
  | d :: ds, i, hist, D :: Ds, r, h => by
      rcases List.mem_cons.1 h with rfl | h'
      · exact ⟨d.items, i, hist, rfl⟩
      · exact rvOf_vals ds _ _ Ds r h'

theorem lt_colOf (hC : ∀ i h n x, ∀ w ∈ (next i h).col n x, w < fieldPrimeWord) :
    ∀ (ds : List RD) (i : ℕ) (hist Ds : List Fmt.Drawn) (n x : ℕ) (c : List UInt64),
    colOf ds i hist next Ds n x = some c → ∀ w ∈ c, w < fieldPrimeWord
  | [], _, _, _, _, _, _, h => by simp [colOf] at h
  | _ :: _, _, _, [], _, _, _, h => by simp [colOf] at h
  | d :: ds, i, hist, D :: Ds, n, x, c, h => by
      unfold colOf at h
      split at h
      · obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 h
        exact lt_orcT d.trees _ p (hC i hist)
      · exact lt_colOf hC ds _ _ Ds _ x c h

/-- **EVERY WORD OF viewOf IS BELOW THE PRIME**, from: the draws' elements; each sent item; each
word of each sent column; each word of the two stored strings' columns. -/
theorem okViewW_viewOf (ds : List RD) (a : ℕ) (xs : List XO) (y : (twoExternalStrings (2 ^ a) SgX).Str)
    (Ds : List Fmt.Drawn) (hD : ∀ D ∈ Ds, ∀ x ∈ D.elems, ltE x = true)
    (hV : ∀ i h, ∀ g ∈ (next i h).vals, okGot g = true)
    (hC : ∀ i h n x, ∀ w ∈ (next i h).col n x, w < fieldPrimeWord)
    (hy : ∀ p, (((twoExternalStrings (2 ^ a) SgX).rd y p).2.all (· < fieldPrimeWord)) = true) :
    viewWordsBelowPrime (viewOf ds a xs next y Ds) = true := by
  refine okViewW_of _ (fun r hr => hD _ (rvOf_drawn next ds 0 [] Ds r hr)) (fun r hr g hg => ?_)
    (fun o ho => ?_)
  · obtain ⟨l, i', h', e⟩ := rvOf_vals next ds 0 [] Ds r hr
    rw [e] at hg
    have h := okGot_layP l _ (hV i' h') g hg
    cases g <;> exact h
  · obtain ⟨kx, -, he⟩ := List.mem_filterMap.1 ho
    split at he
    · obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 he
      exact hy p
    · split at he
      · obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 he
        exact hy p
      · obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 he
        exact List.all_eq_true.2 fun w hw =>
          decide_eq_true (lt_colOf next hC ds 0 [] Ds _ _ c hc w hw)

/-- **The same at the draws of every verifier's randomness**, under the kit of the programs'
field. -/
theorem okViewW_run (ds : List RD) (a : ℕ) (xs : List XO) (y : (twoExternalStrings (2 ^ a) SgX).Str)
    (hV : ∀ i h, ∀ g ∈ (next i h).vals, okGot g = true)
    (hC : ∀ i h n x, ∀ w ∈ (next i h).col n x, w < fieldPrimeWord)
    (hy : ∀ p, (((twoExternalStrings (2 ^ a) SgX).rd y p).2.all (· < fieldPrimeWord)) = true)
    (ρ : Rho (uL (ckP .two) ds)) :
    viewWordsBelowPrime (viewOf ds a xs next y (drawnSL (ckP .two) ds ρ)) = true :=
  okViewW_viewOf next ds a xs y _ (ltE_drawnSL ds ρ) hV hC hy

end

/-! ## 2 Nothing that is wanted is dropped -/

theorem length_drawnSL (C : CK) : ∀ (ds : List RD) (ρ : Rho (uL C ds)),
    (drawnSL C ds ρ).length = ds.length
  | [], _ => rfl
  | _ :: ds, (_, ρ) => congrArg (· + 1) (length_drawnSL C ds ρ)

/-- Under an own tree's number a position below that tree's length is wanted. -/
theorem wantedXL_own (a : ℕ) (all : List RD) (xs : List XO) : ∀ (i : ℕ) (ds : List RD)
    (Ds : List Fmt.Drawn), ∀ kx ∈ wantedXL a all xs i ds Ds, kx.1 < 2 ^ 16 →
    ∃ s, treeSh all kx.1 = some s ∧ kx.2 < 2 ^ s.a
  | _, [], _, _, h, _ => by simp [wantedXL] at h
  | _, _ :: _, [], _, h, _ => by simp [wantedXL] at h
  | i, d :: ds, D :: Ds, kx, h, hk => by
      unfold wantedXL at h
      rcases List.mem_append.1 h with h | h
      · rcases List.mem_append.1 h with h | h
        · obtain ⟨o, -, h⟩ := List.mem_flatMap.1 h
          obtain ⟨x, -, rfl⟩ := List.mem_map.1 h
          exact absurd hk (Nat.not_lt.2 (Nat.le_add_right _ _))
        · obtain ⟨n, -, h⟩ := List.mem_flatMap.1 h
          split at h
          · cases h
          · rename_i s hs
            obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
            obtain ⟨z, -, rfl⟩ := List.mem_map.1 ((Fmt.listOf_mem _ _).1 hx)
            exact ⟨s, hs, Nat.mod_lt _ (Nat.two_pow_pos s.a)⟩
      · exact wantedXL_own a all xs (i + 1) ds Ds kx h hk

/-- A tree that has a shape has a seat. -/
theorem seat_of_tree (ds : List RD) (n : ℕ) (s : Fmt.Shape) (h : treeSh ds n = some s) :
    ∃ j k d, seatOf ds n = some (j, k) ∧ ds[j]? = some d ∧ d.trees[k]? = some s := by
  rw [treeSh_seat] at h
  obtain ⟨⟨j, k⟩, h1, h2⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨d, h3, h4⟩ := Option.bind_eq_some_iff.1 h2
  exact ⟨j, k, d, h1, h3, h4⟩

/-- **AT EVERY WANTED OWN (TREE, POSITION) THE COLUMN IS THERE, AND IS next's.** -/
theorem colOf_wanted (next : ℕ → List Fmt.Drawn → MsgV) (ds : List RD) (a : ℕ) (xs : List XO)
    (Ds : List Fmt.Drawn) (kx : ℕ × ℕ) (hk : kx ∈ wantedX a ds xs Ds) (ho : kx.1 < 2 ^ 16)
    (hl : Ds.length = ds.length)
    (hW : ∀ j k d s, ds[j]? = some d → d.trees[k]? = some s →
      ∀ h x, ((next j h).col k x).length = s.W) :
    ∃ j k, seatOf ds kx.1 = some (j, k) ∧
      colOf ds 0 [] next Ds kx.1 kx.2 = some ((next j (Ds.take j)).col k kx.2) := by
  obtain ⟨s, hs, hx⟩ := wantedXL_own a ds xs 0 ds Ds kx hk ho
  obtain ⟨j, k, d, h1, h2, h3⟩ := seat_of_tree ds kx.1 s hs
  have hj : j < Ds.length := by
    rw [hl]
    exact (List.getElem?_eq_some_iff.1 h2).1
  have h := colOf_at next ds 0 [] Ds kx.1 kx.2 j k d s h1 h2 h3 hx hj (hW _ k d s (by
    rw [Nat.zero_add]; exact h2) h3 _ _)
  rw [Nat.zero_add, List.nil_append] at h
  exact ⟨j, k, h1, h⟩

/-! ## 3 The play does not hang on the test bits -/

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- At a local round, setting the test bits to 0 is the test of work's own setter, if the round has
one; else the challenge stays as it is. -/
theorem zero_lo {lam K' : ℕ} {r : Round} {a : RAnn r} (w : WireRB lam K' r a) (hk : a.kind = .lo)
    (c : r.Chal) : w.zero c = w.grJ.elim c fun g => g.set (fun _ => false) c := by
  unfold TypedOracleCompiler.Iop.WireRB.zero
  split
  · cases w.grJ <;> rfl
  · rename_i h
    rw [hk] at h
    cases h

theorem old_zero_grOf : ∀ (b : ℕ) (Ch P : Type) (c : GChal b Ch),
    GChal.old (((grOf Dn Ch P b).map TypedOracleCompiler.Tagged.ofGr).elim c fun g => g.set (fun _ => false) c) =
      GChal.old c
  | 0, _, _, _ => rfl
  | b + 1, _, _, c => GChal.old_mk (b + 1) (GChal.old c) _

theorem drawn_zero : ∀ (ds : List RD) (ρ : Rho (uL C ds)),
    drawnSL C ds (RoundsQueryLayout.zero _ _ (wiresSL C K chal ds) ρ) = drawnSL C ds ρ
  | [], _ => rfl
  | d :: ds, (c, ρ) => by
      show C.dr d.entry d.kind (GChal.old (b := d.entry.work) ((wireS C K chal d).zero c)) ::
          drawnSL C ds (RoundsQueryLayout.zero _ _ (wiresSL C K chal ds) ρ) =
        C.dr d.entry d.kind (GChal.old (b := d.entry.work) c) :: drawnSL C ds ρ
      rw [drawn_zero ds ρ, zero_lo (wireS C K chal d) rfl c]
      exact congrArg (fun u => C.dr d.entry d.kind u :: drawnSL C ds ρ)
        (old_zero_grOf d.entry.work (C.Ch d.entry d.kind) (PlainOf d.items) c)

/-- **What a view shows of the run is the same at ρ and at ρ with all test bits set to 0.** -/
theorem run_zero (next : ℕ → List Fmt.Drawn → MsgV) (ds : List RD) (i : ℕ)
    (hist : List Fmt.Drawn) (ρ : Rho (uL C ds)) :
    rvSL C ds ((stratSL C ds i hist next).run (RoundsQueryLayout.zero _ _ (wiresSL C K chal ds) ρ)).1 =
        rvSL C ds ((stratSL C ds i hist next).run ρ).1 ∧
      colAtS C ds ((stratSL C ds i hist next).run (RoundsQueryLayout.zero _ _ (wiresSL C K chal ds) ρ)).1 =
        colAtS C ds ((stratSL C ds i hist next).run ρ).1 :=
  run_same C next ds i hist _ ρ (drawn_zero C K chal ds ρ)

/-- Behind the first, empty round the whole wire's "all test bits 0" is the written rounds'. -/
theorem zero_tail (ds : List RD) (a : ℕ) (xs : List XO) {X : Type} (dec : X → View → Bool)
    (c0 : (_root_.Run.PQ.s0 C).up.Chal) (ρ : Rho (uL C ds)) :
    (RoundsQueryLayout.zero _ _ (Johnson.RunOne.StrictW.wqW C ds a xs dec K chal).sh
      ((c0, ρ) : Rho (_root_.Run.Twin.up (TypedOracleCompiler.Run.PQ.SOf C ds)))).2 =
      RoundsQueryLayout.zero _ _ (wiresSL C K chal ds) ρ := rfl

end

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.zero_lt
#print axioms Johnson.Prover.Link.ltE_zero
#print axioms Johnson.Prover.Link.okGot_layP
#print axioms Johnson.Prover.Link.lt_orcT
#print axioms Johnson.Prover.Link.rvOf_drawn
#print axioms Johnson.Prover.Link.rvOf_vals
#print axioms Johnson.Prover.Link.lt_colOf
#print axioms Johnson.Prover.Link.okViewW_viewOf
#print axioms Johnson.Prover.Link.okViewW_run
#print axioms Johnson.Prover.Link.length_drawnSL
#print axioms Johnson.Prover.Link.wantedXL_own
#print axioms Johnson.Prover.Link.seat_of_tree
#print axioms Johnson.Prover.Link.colOf_wanted
#print axioms Johnson.Prover.Link.zero_lo
#print axioms Johnson.Prover.Link.old_zero_grOf
#print axioms Johnson.Prover.Link.drawn_zero
#print axioms Johnson.Prover.Link.run_zero
#print axioms Johnson.Prover.Link.zero_tail
