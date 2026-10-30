-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageIsViewProofs.lean: the proof of `Spec.pi_view` (Run/PageIsView.lean), the part on the
decision in the comparison of two verifiers in Run/PageIs.lean: under the hypotheses of its
statement, on the local transcript that the compiled verifier makes from the parser's argument
string, the protocol's decision is "the test bits pass, and dec says yes on the view of what the
lenient reader handed out".

The file has `pi_view`, which proves `Spec.pi_view` (Run/PageIsView.lean's statement, as it stands
there: no hypothesis beyond its own); one statement of its own (`Spec.pi_view_of`) with its proof;
and the lemmas under them.
(The two verifiers: the compiled verifier behind the lenient reader (`laxV`) and the format's own
strict verifier (`Fmt.verifyW`).)
The compiled verifier fills a transcript (`trP`, Run/ThinDefs.lean; here `trL`) from what its chain
yields (the roots, the verifier messages) and from the argument string's plain parts and openings,
and evaluates the protocol's decision on it.
In the lemmas, tbl is a table that has, under a tree's number, the tree's width and the record Ob of
its opening (`OpenB`, Run/ParseBS.lean). A position is listed if it is in the list Ob.idx. In
`colAtS_tr`, own tree n is the n-th of the trees of the rounds ds, of the shape `treeSh ds n`
(Run/PlanQTypes.lean).

Main names:
  `Spec.pi_view_of`: `Spec.pi_want` → `Spec.pi_rowOf` → `Spec.pi_sent` → `Spec.pi_view` (the first
    three: Run/PageIsTab.lean; the last: Run/PageIsView.lean). `pi_view_of` proves it.
  `pi_view`: `pi_view_of` at `pi_want`, `pi_rowOf`, `pi_sent` of Run/PageIsTabProofs.lean.
The lemmas are each generic in the list of rounds (no description, no hash), but for `trace_okb`,
which has a hash function h and a plan P as parameters.
  `trP_head`: where a root was sent and an opening stands, the transcript's oracle message holds the
    opening's symbol.

Limits: this file says nothing on hashes, roots' values, the strict format or the walks: these are
other parts of Run/PageIs.lean.
Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Terms: lean/GLOSSARY.md.
-/
import Run.PageIsView
import Run.PageIsOp
import Run.PageIsTabProofs

set_option autoImplicit false

namespace Run.PQ
open Rom Iop Compile Compile.Batch Run.Twin Run.Thin
open _root_.Fmt (Chain RoundOut ChainOut OpenOut Plan Src Item ItemValue)

/-- Typing a message's items and reading them back gives the items without the roots: if
`PlainOf.ofGots ts l = some p`, then `PlainOf.gots ts p` is `Fmt.noRoots l`. -/
theorem gots_ofGots :
    ∀ (ts : List Item) (l : List ItemValue) (p : PlainOf ts),
      PlainOf.ofGots ts l = some p → PlainOf.gots ts p = _root_.Fmt.noRoots l
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by simp [PlainOf.ofGots] at h
  | .root :: ts, .root d :: l, p, h => gots_ofGots ts l p h
  | .f :: ts, .f x :: l, p, h => by
      rcases h1 : PlainOf.ofGots ts l with _ | y
      · simp [PlainOf.ofGots, h1] at h
      · simp only [PlainOf.ofGots, h1, Option.map_some, Option.some.injEq] at h
        subst h
        show _root_.Fmt.ItemValue.f x :: PlainOf.gots ts y = _root_.Fmt.ItemValue.f x :: _root_.Fmt.noRoots l
        rw [gots_ofGots ts l y h1]
  | .e :: ts, .e x :: l, p, h => by
      rcases h1 : PlainOf.ofGots ts l with _ | y
      · simp [PlainOf.ofGots, h1] at h
      · simp only [PlainOf.ofGots, h1, Option.map_some, Option.some.injEq] at h
        subst h
        show _root_.Fmt.ItemValue.e x :: PlainOf.gots ts y = _root_.Fmt.ItemValue.e x :: _root_.Fmt.noRoots l
        rw [gots_ofGots ts l y h1]
  | .word :: ts, .word x :: l, p, h => by
      rcases h1 : PlainOf.ofGots ts l with _ | y
      · simp [PlainOf.ofGots, h1] at h
      · simp only [PlainOf.ofGots, h1, Option.map_some, Option.some.injEq] at h
        subst h
        show _root_.Fmt.ItemValue.word x :: PlainOf.gots ts y =
          _root_.Fmt.ItemValue.word x :: _root_.Fmt.noRoots l
        rw [gots_ofGots ts l y h1]
  | .answer :: ts, .answer x :: l, p, h => by
      rcases h1 : PlainOf.ofGots ts l with _ | y
      · simp [PlainOf.ofGots, h1] at h
      · simp only [PlainOf.ofGots, h1, Option.map_some, Option.some.injEq] at h
        subst h
        show _root_.Fmt.ItemValue.answer x :: PlainOf.gots ts y =
          _root_.Fmt.ItemValue.answer x :: _root_.Fmt.noRoots l
        rw [gots_ofGots ts l y h1]
  | .root :: _, .f _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .root :: _, .e _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .root :: _, .word _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .root :: _, .answer _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .f :: _, .root _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .f :: _, .e _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .f :: _, .word _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .f :: _, .answer _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .e :: _, .root _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .e :: _, .f _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .e :: _, .word _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .e :: _, .answer _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .word :: _, .root _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .word :: _, .f _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .word :: _, .e _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .word :: _, .answer _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .answer :: _, .root _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .answer :: _, .f _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .answer :: _, .e _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .answer :: _, .word _ :: _, _, h => by simp [PlainOf.ofGots] at h

theorem pv_old_mk {W P : Type} : ∀ (b : ℕ) (p : P) (ν : W), GPlain.old (GPlain.mk b p ν) = p
  | 0, _, _ => rfl
  | _ + 1, _, _ => rfl

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- the transcript that the verifier makes of the rounds ds -/
abbrev trL (ds : List RD) (rts : RootsOfChain 256 (uL C ds)) (pl : Plains (uL C ds)) (ρ : Rho (uL C ds))
    (f : (p : OPos (uL C ds)) → Option (Opening 256 (OSym (uL C ds) p))) : Iop.Tr (uL C ds) :=
  trP (SL C ds) (allLo (SL C ds)) (wiresSL C K chal ds) rts pl ρ f

/-- the verifier messages read off the transcript are those put in -/
theorem rhoSL_tr :
    ∀ (ds : List RD) (rts : RootsOfChain 256 (uL C ds)) (pl : Plains (uL C ds)) (ρ : Rho (uL C ds))
        (f : (p : OPos (uL C ds)) → Option (Opening 256 (OSym (uL C ds) p))),
      rhoSL C ds (trL C K chal ds rts pl ρ f) = ρ
  | [], _, _, _, _ => rfl
  | d :: ds, (rt, rts), (p, pl), (c, ρ), f => by
      show (c, rhoSL C ds (trL C K chal ds rts pl ρ fun q => f (.inr q))) = (c, ρ)
      rw [rhoSL_tr ds]

/-- The rounds' values on the transcript (`rvSL`) are, round by round, the reader's items without
roots and what was drawn, given the typed plain parts and that the messages' view is what was drawn.
-/
theorem rvSL_tr :
    ∀ (ds : List RD) (ros : List RoundOut) (pl : Plains (uL C ds)) (ρ : Rho (uL C ds))
        (f : (p : OPos (uL C ds)) → Option (Opening 256 (OSym (uL C ds) p))),
      plainsSL C ds ros = some pl → drawnSL C ds ρ = ros.map (·.drawn) →
      rvSL C ds (trL C K chal ds (rtSL C ds ros) pl ρ f) =
        ros.map fun r => ⟨_root_.Fmt.noRoots r.vals, r.drawn⟩
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, h, _ => by simp [plainsSL] at h
  | _ :: _, [], _, _, _, h, _ => by simp [plainsSL] at h
  | d :: ds, ro :: ros, (p, pl), (c, ρ), f, h, hd => by
      rcases h1 : PlainOf.ofGots d.items ro.vals with _ | p0
      · simp [plainsSL, h1] at h
      rcases h2 : plainsSL C ds ros with _ | pl0
      · simp [plainsSL, h1, h2] at h
      simp only [plainsSL, h1, h2, Option.some.injEq] at h
      cases h
      have hd1 : C.dr d.entry d.kind (GChal.old (b := d.entry.work) c) = ro.drawn :=
        (List.cons.inj hd).1
      have hd2 : drawnSL C ds ρ = ros.map (·.drawn) := (List.cons.inj hd).2
      show (⟨PlainOf.gots d.items
              (GPlain.old (b := d.entry.work) (GPlain.mk d.entry.work p0 ro.nonce)),
            C.dr d.entry d.kind (GChal.old (b := d.entry.work) c)⟩ : RV) ::
          rvSL C ds (trL C K chal ds (rtSL C ds ros) pl ρ fun q => f (.inr q)) = _
      rw [pv_old_mk, gots_ofGots _ _ _ h1, hd1, rvSL_tr ds ros pl ρ _ h2 hd2]
      rfl

end

/-! ### Look-ups -/

theorem lookup_of_mem {β : Type} :
    ∀ (es : List (ℕ × β)) (a : ℕ) (b : β),
      (es.map Prod.fst).Pairwise (· < ·) → (a, b) ∈ es → es.lookup a = some b
  | [], _, _, _, h => by cases h
  | (a', b') :: es, a, b, hp, hm => by
      rw [List.map_cons, List.pairwise_cons] at hp
      rcases List.mem_cons.1 hm with e | hm'
      · cases e
        simp
      · have hlt : a' < a := hp.1 a (List.mem_map.2 ⟨(a, b), hm', rfl⟩)
        have hne : (a == a') = false := by simpa using (Nat.ne_of_gt hlt)
        rw [List.lookup_cons, hne]
        exact lookup_of_mem es a b hp.2 hm'

theorem mem_zip_ext {α β γ : Type} :
    ∀ (l1 : List α) (l2 : List β) (l3 : List γ) (a : α) (b : β),
      (a, b) ∈ l1.zip l2 → l2.length ≤ l3.length → ∃ c, (a, (b, c)) ∈ l1.zip (l2.zip l3)
  | [], _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, h, _ => by simp at h
  | _ :: _, _ :: _, [], _, _, _, hl => by simp at hl
  | x :: l1, y :: l2, z :: l3, a, b, h, hl => by
      rw [List.zip_cons_cons, List.mem_cons] at h
      rcases h with e | h
      · cases e
        exact ⟨z, by simp⟩
      · obtain ⟨c, hc⟩ := mem_zip_ext l1 l2 l3 a b h (by simpa using hl)
        exact ⟨c, by rw [List.zip_cons_cons, List.zip_cons_cons]; exact List.mem_cons_of_mem _ hc⟩

/-- Under `hok` and `hm`: the parser's opening at a listed position holds the listed column:
`Ob.at sym run y` is made from `sym c`, where that is defined, with a salt of the form
`leafSalt run s` and a path. -/
theorem at_listed {σ : Type} (sym : List UInt64 → Option σ) (run : ByteArray)
    (Ob : OpenB) (sb W : ℕ) (hok : Ob.ok sb W = true) (y : ℕ)
    (c : List UInt64) (hm : (y, c) ∈ Ob.idx.zip Ob.cols) :
    ∃ s pt, Ob.at sym run y = (sym c).map fun v => ⟨v, leafSalt run s, pt⟩ := by
  obtain ⟨h1, h2, -, -, -⟩ := TieTree.ok_spec Ob sb W hok
  have hp := (TieTree.ok_list Ob sb W hok).1
  have hl : Ob.paths.length = Ob.idx.length := Octopus.length_fill _ _ _
  obtain ⟨⟨s, pt⟩, hc⟩ :=
    mem_zip_ext Ob.idx Ob.cols (Ob.salts.zip Ob.paths) y c hm (by rw [List.length_zip]; omega)
  refine ⟨s, pt, (parseLaws_at sym run Ob y).1 c s pt (lookup_of_mem _ y _ ?_ hc)⟩
  rw [List.map_fst_zip (by rw [List.length_zip, List.length_zip]; omega)]
  exact hp

/-! ### The head of the transcript -/

theorem trP_head {lam K : ℕ} (r : RS) (S : List RS) (a : RAnn r.up) (A : RoundSplits (up S))
    (w : WireRB lam K r.up a) (W : RoundsQueryLayout lam K (up S) A) (rt : RtC lam × RtC lam)
    (rts : RootsOfChain lam (up S)) (pl : r.Plain) (pls : Plains (up S)) (c : r.Chal) (ρ : Rho (up S))
    (f : (p : OPos (up (r :: S))) → Option (Opening lam (OSym (up (r :: S)) p))) (p : r.Pos)
    (op : Opening lam (r.Sym p)) (h1 : rootP r a rt p = true) (h2 : f (.inl p) = some op) :
    r.rd (trP (r :: S) (a, A) (w, W) (rt, rts) (pl, pls) (c, ρ) f).1.1 p = op.sym := by
  simp only [trP]
  rw [show r.rd = r.up.rd from rfl, w.pt.rd_ofSyms, h1, h2]

/-! ### A column read off the transcript -/

/-- A round and what was read in it go together: a tree exactly if a root was read, and then one, of
32 bytes. This is the relation in `Spec.pi_sent` (Run/PageIsTab.lean). -/
def SentR (d : RD) (ro : RoundOut) : Prop :=
  (d.tree = none ∧ _root_.Fmt.rootsOf ro.vals = []) ∨
  (d.tree.isSome = true ∧ ∃ r : ByteArray, r.size = 32 ∧ _root_.Fmt.rootsOf ro.vals = [r])

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (tbl : List (ℕ × ℕ × OpenB))
  (run : ByteArray) (sb : ℕ)

/-- At own tree n, whose opening the table finds, the transcript's column at a listed position is
the listed column. In full: let `SentR` hold of ds and ros, round by round, `treeSh ds n = some sh`,
let the table have (sh.W, Ob) under sh.tree, with Ob.a = sh.a and `Ob.ok sb sh.W = true`, and let y
be listed in Ob with the column c. Then `colAtS`, on the transcript `trL` at the roots
`rtSL C ds ros` and the openings `opL C tbl run ds`, gives c at (n, y). -/
theorem colAtS_tr :
    ∀ (ds : List RD) (ros : List RoundOut) (pl : Plains (uL C ds)) (ρ : Rho (uL C ds)) (n : ℕ)
        (sh : _root_.Fmt.Shape) (Ob : OpenB),
      List.Forall₂ SentR ds ros → treeSh ds n = some sh → tbl.lookup sh.tree = some (sh.W, Ob) →
      Ob.a = sh.a → Ob.ok sb sh.W = true →
      ∀ (y : ℕ) (c : List UInt64), (y, c) ∈ Ob.idx.zip Ob.cols →
        colAtS C ds (trL C K chal ds (rtSL C ds ros) pl ρ (opL C tbl run ds)) n y = some c
  | [], _, _, _, _, _, _, _, ht, _, _, _, _, _, _ => by cases ht
  | ⟨e, k, items, none, opens⟩ :: ds, _, (p, pl), (c0, ρ), n, sh, Ob, hs, ht, hl, ha, hok, y, c, hm => by
      cases hs with
      | cons _ hs' => exact colAtS_tr ds _ pl ρ n sh Ob hs' ht hl ha hok y c hm
  | ⟨e, k, items, some s, opens⟩ :: ds, _, (p, pl), (c0, ρ), n, sh, Ob, hs, ht, hl, ha, hok, y, c, hm => by
      cases hs with
      | @cons _ ro _ ros h0 hs' =>
        by_cases hn : n = 0
        · subst hn
          have es : s = sh := by simpa [treeSh] using ht
          subst es
          have hy : y < 2 ^ s.a := by
            rw [← ha]
            exact (TieTree.ok_list Ob sb s.W hok).2.1 y (List.of_mem_zip hm).1
          have hw : c.length = s.W := (TieTree.ok_list Ob sb s.W hok).2.2 c (List.of_mem_zip hm).2
          obtain ⟨sl, pt, hat⟩ := at_listed
            (symSL C (⟨e, k, items, some s, opens⟩ :: ds) (.inl (⟨y, hy⟩ : Fin (2 ^ s.a))))
            run Ob sb s.W hok y c hm
          have hsym : symSL C (⟨e, k, items, some s, opens⟩ :: ds)
                (.inl (⟨y, hy⟩ : Fin (2 ^ s.a))) c =
              some (colFn s.W c) := by
            show (if h : c.length = s.W then
                  some (fun i : Fin s.W => c[i.val]'(by rw [h]; exact i.isLt))
                else none) = _
            rw [dif_pos hw]
            exact congrArg some
              (funext fun i => by
                simp [colFn,
                  List.getElem?_eq_getElem (show i.val < c.length by rw [hw]; exact i.isLt)])
          have hop : opL C tbl run (⟨e, k, items, some s, opens⟩ :: ds)
                (.inl (⟨y, hy⟩ : Fin (2 ^ s.a))) =
              some ⟨colFn s.W c, leafSalt run sl, pt⟩ := by
            unfold opL
            show (match tbl.lookup s.tree with | none => none | some x => x.2.at _ run y) = _
            rw [hl]
            show Ob.at _ run y = _
            rw [hat, hsym]
            rfl
          have hroot : rootP (roundS C ⟨e, k, items, some s, opens⟩)
                (roundS C ⟨e, k, items, some s, opens⟩).lo
                ((none, some
                    ((_root_.Fmt.rootsOf ro.vals).head?.map bytesToDig)) : RtC 256 × RtC 256)
                (⟨y, hy⟩ : Fin (2 ^ s.a)) = true := by
            rcases h0 with ⟨h, -⟩ | ⟨-, r, -, hr⟩
            · cases h
            · rw [hr]
              rfl
          have key := trP_head (roundS C ⟨e, k, items, some s, opens⟩) (SL C ds)
            (roundS C ⟨e, k, items, some s, opens⟩).lo (allLo (SL C ds))
            (wireS C K chal ⟨e, k, items, some s, opens⟩) (wiresSL C K chal ds)
            (none, some ((_root_.Fmt.rootsOf ro.vals).head?.map bytesToDig)) (rtSL C ds ros)
            p pl c0 ρ (opL C tbl run (⟨e, k, items, some s, opens⟩ :: ds))
            (⟨y, hy⟩ : Fin (2 ^ s.a)) _ hroot hop
          show (if h : y < 2 ^ s.a then
                some (List.ofFn
                    ((trL C K chal (⟨e, k, items, some s, opens⟩ :: ds)
                      (rtSL C (⟨e, k, items, some s, opens⟩ :: ds) (ro :: ros)) (p, pl) (c0, ρ)
                      (opL C tbl run (⟨e, k, items, some s, opens⟩ :: ds))).1.1 ⟨y, h⟩))
              else none) = some c
          rw [dif_pos hy]
          refine congrArg some ?_
          refine Eq.trans (congrArg List.ofFn key) ?_
          exact ofFn_colFn s.W c hw
        · have ht' : treeSh ds (n - 1) = some sh := by simpa [treeSh, hn] using ht
          have ih := colAtS_tr ds ros pl ρ (n - 1) sh Ob hs' ht' hl ha hok y c hm
          show (if n = 0 then _
              else
                colAtS C ds (trL C K chal ds (rtSL C ds ros) pl ρ (opL C tbl run ds)) (n - 1) y) =
            some c
          rw [if_neg hn]
          exact ih

end

/-! ### Lists -/

theorem filterMap_flatMap_of {α β γ : Type} (g : β → Option γ) (F : α → List β) (G : α → List γ) :
    ∀ l : List α, (∀ a ∈ l, (F a).filterMap g = G a) → (l.flatMap F).filterMap g = l.flatMap G
  | [], _ => rfl
  | a :: l, h => by
      rw [List.flatMap_cons, List.flatMap_cons, List.filterMap_append, h a List.mem_cons_self,
        filterMap_flatMap_of g F G l fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem filterMap_zip_of {β γ : Type} (g : ℕ → Option γ) (mk : ℕ → β → γ) :
    ∀ (xs : List ℕ) (cs : List β), cs.length = xs.length →
      (∀ y c, (y, c) ∈ xs.zip cs → g y = some (mk y c)) →
      xs.filterMap g = (xs.zip cs).map fun p => mk p.1 p.2
  | [], _, _, _ => by simp
  | _ :: _, [], h, _ => by simp at h
  | x :: xs, c :: cs, h, hg => by
      rw [List.zip_cons_cons, List.map_cons, List.filterMap_cons, hg x c (by simp)]
      exact congrArg _
        (filterMap_zip_of g mk xs cs (by simpa using h) fun y c' hm =>
          hg y c' (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hm))

theorem pv_right {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → ∀ b ∈ l2, ∃ a ∈ l1, R a b
  | _, _, .nil, _, h => by cases h
  | _, _, .cons h0 ht, b, hb => by
      rcases List.mem_cons.1 hb with e | hb'
      · subst e
        exact ⟨_, List.mem_cons_self, h0⟩
      · obtain ⟨a, ha, hr⟩ := pv_right ht b hb'
        exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

/-- Every opening of the lenient reader's output passes the parser's test: under
`TraceL h P rs ros c roots` (Run/PageIs.lean), every opening y of a round of ros has
`(obOf y).ok P.salt y.1.W = true`. -/
theorem trace_okb (h : HId) (P : Plan) :
    ∀ (rs : List _root_.Fmt.Round) (ros : List RoundOut) (c : Chain) (roots : Array ByteArray),
      TraceL h P rs ros c roots → ∀ ro ∈ ros, ∀ y ∈ ro.opens, (obOf y).ok P.salt y.1.W = true
  | [], [], _, _, _, _, hr, _, _ => by cases hr
  | [], _ :: _, _, _, ht, _, _, _, _ => ht.elim
  | _ :: _, [], _, _, ht, _, _, _, _ => ht.elim
  | r :: rs, ro0 :: ros, c, roots, ht, ro, hr, y, hy => by
      obtain ⟨-, -, -, -, hf, hrest⟩ := ht
      rcases List.mem_cons.1 hr with e | hr'
      · subst e
        obtain ⟨x, -, hx⟩ := pv_right hf y hy
        have := hx.okb
        rw [← hx.sh] at this
        exact this
      · exact trace_okb h P rs ros _ _ hrest ro hr' y hy

/-! ### The statement -/

def Spec.pi_view_of : Prop := Spec.pi_want → Spec.pi_rowOf → Spec.pi_sent → Spec.pi_view

theorem pi_view_of : Spec.pi_view_of := by
  intro hw hr hs h S C K chal dec hok o run pl ρ ex hL hrun hpl hd
  have hsent : List.Forall₂ SentR (rds S) o.rounds.toList := hs h S o hok hL
  show (passSL C (rds S)
        (rhoSL C (rds S)
          (trL C K chal (rds S) (rtSL C (rds S) o.rounds.toList)
            pl ρ (opL C (opensB o) run (rds S)))) &&
      dec (viewSL C (rds S)
          (trL C K chal (rds S) (rtSL C (rds S) o.rounds.toList)
            pl ρ (opL C (opensB o) run (rds S))))) = _
  rw [rhoSL_tr]
  refine congrArg (fun v => passSL C (rds S) ρ && dec v) ?_
  show (⟨rvSL C (rds S)
        (trL C K chal (rds S) (rtSL C (rds S) o.rounds.toList) pl ρ (opL C (opensB o) run (rds S))),
      (wanted (rds S)
        (drawnSL C (rds S)
          (rhoSL C (rds S)
            (trL C K chal (rds S) (rtSL C (rds S) o.rounds.toList) pl ρ
              (opL C (opensB o) run (rds S)))))).filterMap fun nx =>
                (colAtS C (rds S)
                    (trL C K chal (rds S) (rtSL C (rds S) o.rounds.toList)
                      pl ρ (opL C (opensB o) run (rds S)))
                    nx.1 nx.2).map
                  fun c => (nx.1, nx.2, c)⟩ : View) =
    ⟨o.rounds.toList.map fun r => ⟨_root_.Fmt.noRoots r.vals, r.drawn⟩,
      o.rounds.toList.flatMap (_root_.Fmt.openedOf S.firstTree)⟩
  rw [rvSL_tr C K chal (rds S) o.rounds.toList pl ρ _ hpl hd, rhoSL_tr, hd, hw h S o hok hL]
  refine congrArg _ ?_
  refine filterMap_flatMap_of _ _ _ _ fun ro hro => ?_
  refine filterMap_flatMap_of _ _ _ _ fun x hx => ?_
  obtain ⟨n, ht, row⟩ := hr h S o hok hL ro hro x hx
  have hn : x.1.tree - S.firstTree = n := by rw [row.no]; omega
  have hob := trace_okb h S.plan _ _ _ _ hL.trace ro hro x hx
  rw [List.filterMap_map, hn]
  refine filterMap_zip_of _ (fun y c => (n, y, c)) x.2.1 x.2.2.cols
    (TieTree.ok_spec (obOf x) _ _ hob).1 fun y c hm => ?_
  show (colAtS C (rds S)
        (trL C K chal (rds S) (rtSL C (rds S) o.rounds.toList) pl ρ (opL C (opensB o) run (rds S)))
        n y).map
      (fun c => (n, y, c)) = some (n, y, c)
  rw [colAtS_tr C K chal (opensB o) run S.plan.salt (rds S) o.rounds.toList pl ρ n x.1 (obOf x)
      hsent ht row.look rfl hob y c hm]
  rfl

/-- `Spec.pi_view` with no hypothesis beyond its own: `pi_view_of` at the three statements of
Run/PageIsTab.lean, which are proved in Run/PageIsTabProofs.lean. -/
theorem pi_view : Spec.pi_view := pi_view_of pi_want pi_rowOf pi_sent

end Run.PQ
