-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/TypingTLaws.lean: laws of the typing of a stretch of rounds
(OnBytes/Maker/TypingT.lean): a view that is formed from a typed transcript finds again what the
reader had read. After Run/PageIsViewProofs.lean's `rvSL_tr` and `colAtS_tr`, for rounds with a list
of trees.

The laws speak of any transcript τ of the stretch. What ties τ to the typed parts is a premise each
time: its plain parts are `plainsT`'s; its verifier's messages give the draws that were read; at the
one position in question it answers with the symbol of `opensT`'s opening. That the transcript which
a compiled verifier builds from a proof string meets these premises is not shown here.

  `posAtST_place`, `place_posAtST`
                    `placeT'` is the inverse of `posAtST`: the position at a position's tree and
                    leaf is that position, and a position found at (n, x) has the place (n, x).
  `rvT_plainsT`     the rounds of the view are, round by round, the items read without the roots,
                    and what was drawn. It asks the draws whole, the digests among them. Nothing
                    outside this file calls it: the tie of a file goes by `rvT_alike`
                    (OnBytes/Maker/ViewsAlike.lean), which asks less.
  `colAtST_opensT`  at a tree of the stretch whose table holds a column of the tree's width under a
                    leaf below the tree's number of leaves, the column that the view finds in the
                    transcript is the table's.
  `opensT_at`       at the position found at (n, x), `opensT` is the look-up under (base + n, x).
  `rootsT_eq`       `rootsT` at a chain's rounds is Run/ParseChain.lean's `rootsB`, as digests.
  `trOfT`, `trOfT_plains`, `trOfT_rho`, `trOfT_read`, `rvT_trOfT`, `colAtST_trOfT`
                    the premise on the opened symbols can be met: a transcript with given plain
                    parts and verifier's messages, the opened symbols where there are any and the
                    fixed symbol elsewhere, meets it; the premises on plain parts and draws become
                    premises on the given parts and messages; the two laws at it.
  Of one round: `treeIn_lt`, `posAtT_in`, `in_posAtT`, `posAtT_some`, `symIn_some`, `colT_symIn`. Of
  the stretch: `posAtST_some`, `symT'_some`, `colOfSym_symT'`.

Not claimed. Nothing on hashes, on paths or on salts; nothing on soundness; nothing on what a table
holds.


-/
import OnBytes.Maker.TypingT
import OnBytes.Maker.TreesLaws
import Run.PageIsViewProofs

set_option autoImplicit false

namespace OnBytes.Maker

open Iop Rom _root_.Compile _root_.Run _root_.Run.PQ

/-! ## One round -/

theorem treeIn_lt : ∀ (ts : List Fmt.Shape) (p : PosT ts), treeIn ts p < ts.length
  | _ :: _, .inl _ => Nat.succ_pos _
  | _ :: ts, .inr p => Nat.succ_lt_succ (treeIn_lt ts p)

theorem posAtT_in :
    ∀ (ts : List Fmt.Shape) (p : PosT ts), posAtT ts (treeIn ts p) (leafIn ts p) = some p
  | _ :: _, .inl x => dif_pos x.isLt
  | _ :: ts, .inr p => by
      show (posAtT ts (treeIn ts p) (leafIn ts p)).map Sum.inr = _
      rw [posAtT_in ts p]
      rfl

theorem in_posAtT :
    ∀ (ts : List Fmt.Shape) (k j : ℕ) (p : PosT ts),
      posAtT ts k j = some p → treeIn ts p = k ∧ leafIn ts p = j
  | [], _, _, _, h => by cases h
  | s :: _, 0, j, p, h => by
      have h0 : (if h : j < 2 ^ s.a then some (.inl ⟨j, h⟩) else none) = some p := h
      by_cases hj : j < 2 ^ s.a
      · rw [dif_pos hj] at h0
        cases Option.some.inj h0
        exact ⟨rfl, rfl⟩
      · rw [dif_neg hj] at h0
        cases h0
  | _ :: ts, k + 1, j, p, h => by
      obtain ⟨q, hq, rfl⟩ :=
        Option.map_eq_some_iff.1 (show (posAtT ts k j).map Sum.inr = some p from h)
      obtain ⟨h1, h2⟩ := in_posAtT ts k j q hq
      exact ⟨congrArg (· + 1) h1, h2⟩

/-- There is a position at each leaf of each tree of the round. -/
theorem posAtT_some :
    ∀ (ts : List Fmt.Shape) (k j : ℕ) (sh : Fmt.Shape),
      ts[k]? = some sh → j < 2 ^ sh.a → ∃ p, posAtT ts k j = some p
  | [], _, _, _, h, _ => by simp at h
  | s :: _, 0, j, sh, h, hj => by
      have e : s = sh := by simpa using h
      subst e
      exact ⟨.inl ⟨j, hj⟩, dif_pos hj⟩
  | _ :: ts, k + 1, j, sh, h, hj => by
      obtain ⟨p, hp⟩ := posAtT_some ts k j sh (by simpa using h) hj
      refine ⟨.inr p, ?_⟩
      show (posAtT ts k j).map Sum.inr = _
      rw [hp]
      rfl

/-- A list of the tree's width is a symbol. -/
theorem symIn_some :
    ∀ (ts : List Fmt.Shape) (p : PosT ts) (sh : Fmt.Shape) (c : List UInt64),
      ts[treeIn ts p]? = some sh → c.length = sh.W → ∃ y, symIn ts p c = some y
  | s :: _, .inl _, sh, c, h, hc => by
      have e : s = sh := by simpa [treeIn] using h
      subst e
      exact ⟨_, dif_pos hc⟩
  | _ :: ts, .inr p, sh, c, h, hc => symIn_some ts p sh c (by simpa [treeIn] using h) hc

/-- The symbol made of a list, as a list of words, is that list. -/
theorem colT_symIn :
    ∀ (ts : List Fmt.Shape) (p : PosT ts) (c : List UInt64) (y : SymT ts p),
      symIn ts p c = some y → colT ts p y = c
  | s :: _, .inl _, c, y, h => by
      have h0 : (if h : c.length = s.W then
            some (fun i : Fin s.W => c[i.val]'(by rw [h]; exact i.isLt))
          else none) = some y := h
      by_cases hw : c.length = s.W
      · rw [dif_pos hw] at h0
        have e := Option.some.inj h0
        subst e
        show List.ofFn (fun i : Fin s.W => c[i.val]'(by rw [hw]; exact i.isLt)) = c
        exact List.ext_getElem (by simp [hw]) fun i h1 h2 => by simp
      · rw [dif_neg hw] at h0
        cases h0
  | _ :: ts, .inr p, c, y, h => colT_symIn ts p c y h

/-! ## The stretch: places -/

/-- **The position at a position's tree and leaf is that position.** -/
theorem posAtST_place (C : CK) :
    ∀ (ds : List RDT) (p : OPos (uLT C ds)),
      posAtST C ds (placeT' C ds p).1 (placeT' C ds p).2 = some p
  | d :: _, .inl p => by
      show (if treeIn d.trees p < d.trees.length then
          (posAtT d.trees (treeIn d.trees p) (leafIn d.trees p)).map Sum.inl else _) = _
      rw [if_pos (treeIn_lt d.trees p), posAtT_in]
      rfl
  | d :: ds, .inr q => by
      have hn : ¬ d.trees.length + treeAt C ds q < d.trees.length := by omega
      show (if d.trees.length + treeAt C ds q < d.trees.length then _ else
          (posAtST C ds (d.trees.length + treeAt C ds q - d.trees.length)
            (leafAt C ds q)).map Sum.inr) = _
      rw [if_neg hn, Nat.add_sub_cancel_left]
      have ih : posAtST C ds (treeAt C ds q) (leafAt C ds q) = some q := posAtST_place C ds q
      rw [ih]
      rfl

/-- **A position found at (n, x) has the place (n, x).** -/
theorem place_posAtST (C : CK) :
    ∀ (ds : List RDT) (n x : ℕ) (p : OPos (uLT C ds)),
      posAtST C ds n x = some p → placeT' C ds p = (n, x)
  | [], _, _, _, h => by cases h
  | d :: ds, n, x, p, h => by
      rw [posAtST_cons] at h
      by_cases hn : n < d.trees.length
      · rw [if_pos hn] at h
        obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 h
        obtain ⟨h1, h2⟩ := in_posAtT d.trees n x q hq
        exact Prod.ext h1 h2
      · rw [if_neg hn] at h
        obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 h
        have ih := place_posAtST C ds (n - d.trees.length) x q hq
        have h1 : treeAt C ds q = n - d.trees.length := congrArg Prod.fst ih
        have h2 : leafAt C ds q = x := congrArg Prod.snd ih
        refine Prod.ext ?_ h2
        show d.trees.length + treeAt C ds q = n
        omega

/-- There is a position at each leaf of each tree of the stretch. -/
theorem posAtST_some (C : CK) :
    ∀ (ds : List RDT) (n x : ℕ) (sh : Fmt.Shape),
      treeShT ds n = some sh → x < 2 ^ sh.a → ∃ p, posAtST C ds n x = some p
  | [], _, _, _, h, _ => by cases h
  | d :: ds, n, x, sh, h, hx => by
      rw [treeShT_cons] at h
      rw [posAtST_cons]
      by_cases hn : n < d.trees.length
      · rw [if_pos hn] at h
        rw [if_pos hn]
        obtain ⟨p, hp⟩ := posAtT_some d.trees n x sh h hx
        exact ⟨.inl p, by rw [hp]; rfl⟩
      · rw [if_neg hn] at h
        rw [if_neg hn]
        obtain ⟨p, hp⟩ := posAtST_some C ds (n - d.trees.length) x sh h hx
        exact ⟨.inr p, by rw [hp]; rfl⟩

/-! ## The stretch: symbols -/

/-- A list of the tree's width is a symbol. -/
theorem symT'_some (C : CK) :
    ∀ (ds : List RDT) (p : OPos (uLT C ds)) (sh : Fmt.Shape) (c : List UInt64),
      treeShT ds (treeAt C ds p) = some sh → c.length = sh.W → ∃ y, symT' C ds p c = some y
  | d :: _, .inl p, sh, c, h, hc => by
      have h0 : (if treeIn d.trees p < d.trees.length then d.trees[treeIn d.trees p]? else _) =
          some sh := h
      rw [if_pos (treeIn_lt d.trees p)] at h0
      exact symIn_some d.trees p sh c h0 hc
  | d :: ds, .inr q, sh, c, h, hc => by
      have hn : ¬ d.trees.length + treeAt C ds q < d.trees.length := by omega
      have h0 : (if d.trees.length + treeAt C ds q < d.trees.length then _ else
          treeShT ds (d.trees.length + treeAt C ds q - d.trees.length)) = some sh := h
      rw [if_neg hn, Nat.add_sub_cancel_left] at h0
      exact symT'_some C ds q sh c h0 hc

/-- The symbol made of a list, as a list of words, is that list. -/
theorem colOfSym_symT' (C : CK) :
    ∀ (ds : List RDT) (p : OPos (uLT C ds)) (c : List UInt64) (y : OSym (uLT C ds) p),
      symT' C ds p c = some y → colOfSym C ds p y = c
  | d :: _, .inl p, c, y, h => colT_symIn d.trees p c y h
  | _ :: ds, .inr q, c, y, h => colOfSym_symT' C ds q c y h

/-! ## The rounds of a view -/

/-- **The rounds of the view.** At a transcript whose plain parts are those typed from the rounds
read, and whose verifier's messages give the draws read, the rounds of the view are the items read
without the roots, and the draws. -/
theorem rvT_plainsT (C : CK) :
    ∀ (ds : List RDT) (ros : List Fmt.RoundOut) (τ : Iop.Tr (uLT C ds)),
      plainsT C ds ros = some τ.plains → drawnT C ds τ.rho = ros.map (·.drawn) →
      rvT C ds τ = ros.map fun r => ⟨Fmt.noRoots r.vals, r.drawn⟩
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, h, _ => by simp [plainsT] at h
  | _ :: _, [], _, h, _ => by simp [plainsT] at h
  | d :: ds, ro :: ros, (m, c, τ), h, hd => by
      rcases h1 : PlainOf.ofGots d.items ro.vals with _ | p0
      · simp [plainsT, h1] at h
      rcases h2 : plainsT C ds ros with _ | pl0
      · simp [plainsT, h1, h2] at h
      simp only [plainsT, h1, h2, Option.some.injEq] at h
      have e1 : GPlain.mk d.entry.work p0 ro.nonce = m.2 := congrArg Prod.fst h
      have e2 : pl0 = τ.plains := congrArg Prod.snd h
      have hd1 : C.dr d.entry d.kind (GChal.old (b := d.entry.work) c) = ro.drawn :=
        (List.cons.inj hd).1
      have hd2 : drawnT C ds τ.rho = ros.map (·.drawn) := (List.cons.inj hd).2
      show (⟨PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2),
            C.dr d.entry d.kind (GChal.old (b := d.entry.work) c)⟩ : RV) :: rvT C ds τ = _
      rw [← e1, pv_old_mk, gots_ofGots _ _ _ h1, hd1, rvT_plainsT C ds ros τ (e2 ▸ h2) hd2]
      rfl

/-! ## The openings -/

/-- At the position found at (n, x) the opening is the look-up under (base + n, x). -/
theorem opensT_at (C : CK) (ds : List RDT) (base : ℕ) (tabs : List (ℕ × List (ℕ × Row3)))
    (n x : ℕ) (p : OPos (uLT C ds)) (hp : posAtST C ds n x = some p) :
    opensT C ds base tabs p = atTT (symT' C ds p) tabs (base + n) x := by
  unfold opensT
  rw [place_posAtST C ds n x p hp]

/-- **A column of the view.** Let n be a tree of the stretch, of the shape sh; let the tables hold,
under the tree's number over the file and the leaf x below 2 ^ sh.a, a column c of sh.W words. Let
the transcript answer, at the position of that leaf, with the symbol of `opensT`'s opening. Then the
column that a view finds there is c. -/
theorem colAtST_opensT (C : CK) (ds : List RDT) (base : ℕ) (tabs : List (ℕ × List (ℕ × Row3)))
    (τ : Iop.Tr (uLT C ds)) (n x : ℕ) (sh : Fmt.Shape) (tab : List (ℕ × Row3)) (c : List UInt64)
    (s : Bits) (pt : List (Dig 256))
    (hτ : ∀ p op, posAtST C ds n x = some p → opensT C ds base tabs p = some op →
      τ.read p = op.sym)
    (hsh : treeShT ds n = some sh) (hx : x < 2 ^ sh.a) (ht : tabs.lookup (base + n) = some tab)
    (hl : tab.lookup x = some (c, s, pt)) (hc : c.length = sh.W) :
    colAtST C ds τ n x = some c := by
  obtain ⟨p, hp⟩ := posAtST_some C ds n x sh hsh hx
  have hn : treeAt C ds p = n := congrArg Prod.fst (place_posAtST C ds n x p hp)
  obtain ⟨y, hy⟩ := symT'_some C ds p sh c (by rw [hn]; exact hsh) hc
  have hop : opensT C ds base tabs p = some ⟨y, s, pt⟩ := by
    rw [opensT_at C ds base tabs n x p hp]
    unfold atTT
    rw [ht]
    show atT (symT' C ds p) tab x = _
    unfold atT
    rw [hl]
    show (symT' C ds p c).map _ = _
    rw [hy]
    rfl
  rw [colAtST_read, hp]
  show some (colOfSym C ds p (τ.read p)) = some c
  rw [hτ p _ hp hop]
  exact congrArg some (colOfSym_symT' C ds p c y hy)

/-! ## The premise on the opened symbols can be met -/

/-- A transcript from plain parts, verifier's messages and openings: the opened symbols where there
are any, the fixed symbol elsewhere. -/
def trOfT (C : CK) : (ds : List RDT) → Plains (uLT C ds) → Rho (uLT C ds) →
    ((p : OPos (uLT C ds)) → Option (Opening 256 (OSym (uLT C ds) p))) → Iop.Tr (uLT C ds)
  | [], _, _, _ => ()
  | d :: ds, (pl, pls), (c, ρ), f =>
    ((fun p => match f (.inl p) with
        | some op => op.sym
        | none => zeroT d.trees p, pl), c, trOfT C ds pls ρ fun q => f (.inr q))

theorem trOfT_plains (C : CK) :
    ∀ (ds : List RDT) (pl : Plains (uLT C ds)) (ρ : Rho (uLT C ds))
      (f : (p : OPos (uLT C ds)) → Option (Opening 256 (OSym (uLT C ds) p))),
      (trOfT C ds pl ρ f).plains = pl
  | [], _, _, _ => rfl
  | _ :: ds, (pl, pls), (_, ρ), f =>
      congrArg (Prod.mk pl) (trOfT_plains C ds pls ρ fun q => f (.inr q))

theorem trOfT_rho (C : CK) :
    ∀ (ds : List RDT) (pl : Plains (uLT C ds)) (ρ : Rho (uLT C ds))
      (f : (p : OPos (uLT C ds)) → Option (Opening 256 (OSym (uLT C ds) p))),
      (trOfT C ds pl ρ f).rho = ρ
  | [], _, _, _ => rfl
  | _ :: ds, (_, pls), (c, ρ), f =>
      congrArg (Prod.mk c) (trOfT_rho C ds pls ρ fun q => f (.inr q))

theorem trOfT_read (C : CK) :
    ∀ (ds : List RDT) (pl : Plains (uLT C ds)) (ρ : Rho (uLT C ds))
      (f : (p : OPos (uLT C ds)) → Option (Opening 256 (OSym (uLT C ds) p)))
      (p : OPos (uLT C ds)) (op : Opening 256 (OSym (uLT C ds) p)),
      f p = some op → (trOfT C ds pl ρ f).read p = op.sym
  | d :: _, (_, _), (_, _), f, .inl p, op, h => by
      show (match f (.inl p) with
        | some op => op.sym
        | none => zeroT d.trees p) = op.sym
      rw [h]
  | _ :: ds, (_, pls), (_, ρ), f, .inr q, op, h =>
      trOfT_read C ds pls ρ (fun q => f (.inr q)) q op h

/-- The two laws at that transcript: the premise on the opened symbols is met there; those on plain
parts and draws stand on the given pl and ρ. -/
theorem rvT_trOfT (C : CK) (ds : List RDT) (ros : List Fmt.RoundOut) (pl : Plains (uLT C ds))
    (ρ : Rho (uLT C ds)) (f : (p : OPos (uLT C ds)) → Option (Opening 256 (OSym (uLT C ds) p)))
    (hpl : plainsT C ds ros = some pl) (hd : drawnT C ds ρ = ros.map (·.drawn)) :
    rvT C ds (trOfT C ds pl ρ f) = ros.map fun r => ⟨Fmt.noRoots r.vals, r.drawn⟩ :=
  rvT_plainsT C ds ros _ (by rw [trOfT_plains]; exact hpl) (by rw [trOfT_rho]; exact hd)

theorem colAtST_trOfT (C : CK) (ds : List RDT) (base : ℕ) (tabs : List (ℕ × List (ℕ × Row3)))
    (pl : Plains (uLT C ds)) (ρ : Rho (uLT C ds)) (n x : ℕ) (sh : Fmt.Shape)
    (tab : List (ℕ × Row3)) (c : List UInt64) (s : Bits) (pt : List (Dig 256))
    (hsh : treeShT ds n = some sh) (hx : x < 2 ^ sh.a) (ht : tabs.lookup (base + n) = some tab)
    (hl : tab.lookup x = some (c, s, pt)) (hc : c.length = sh.W) :
    colAtST C ds (trOfT C ds pl ρ (opensT C ds base tabs)) n x = some c :=
  colAtST_opensT C ds base tabs _ n x sh tab c s pt
    (fun p op _ h => trOfT_read C ds pl ρ _ p op h) hsh hx ht hl hc

/-- The roots are those of Run/ParseChain.lean, as digests. -/
theorem rootsT_eq (o : Fmt.ChainOut) : rootsT o.rounds.toList = (rootsB o).map bytesToDig := rfl

end OnBytes.Maker
