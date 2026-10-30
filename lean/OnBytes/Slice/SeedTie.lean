-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SeedTie.lean: the seeds that the text of the program's `recordSeeds` draws from a row
of words are `toSeed` of the value of the library's block sampler on the same words. So the bound of
OnBytes/Slice/SeedBias.lean speaks of the program's draw from a row of words, in the second field;
that the row is the one which the program reads off its blocks' bytes: OnBytes/Slice/SeedRow.lean.

Two texts say how a record's seeds are drawn. The program's (`recordSeeds`,
OnBytes/Entry/Table.lean): "a seed, s times" (`timesT`, `Fmt.drawSeed`) on the row of the round's
words, the triples then taken as elements. The library's sampler (`seedBS`,
OnBytes/Slice/SeedBias.lean), whose bias is a theorem, with `toSeed`. The library ties its sampler
to the format's list of draws (`drawTie_bs`, Run/DrawTieProofs.lean). Here both sides are read as
flat lists of drawn values.

Main definitions: `dV`, `gv`, `nzOf`, `readFlat` (s seeds off a flat list of drawn values); `flat`,
`progSeeds`.
Main theorems.
 `toSeed_eq`            `toSeed` reads the values as they are handed on (`outAll`). With `toF_toU`,
                        `toE_toU3`, `outAll_cast`, `eElems_out`, `getD_drop_cons`.
 `seedOf_flat`          `seedOf` of the program's list reads the flat list of its values, if there
                        are s seeds with points of lg coordinates: the fillers for a missing seed
                        and a missing coordinate are then not reached; the factor 1 for 0 is
                        `nzOf`'s, and the sampler's values do not reach it (`toSeed_eq`).
 `readAll_append`, `readAll_elems`, `readAll_seeds`, `times_length`, `seed_points`   the format's
                        list of the seeds' draws gives the flat list of "a seed, s times".
 `seedTie`              THE TIE, for all blocks.
 `coll_pr_prog`         the bound of `coll_pr` with the program's own expression for the seed.

WHAT IS NOT SHOWN. THE WORDS OF A BLOCK: the row here is `rowFn 0 (rowOf e64 b u)`, the words of the
blocks u as the library cuts 256 bits into four words; `recordSeeds` reads `Fmt.rowOf vb`, the words
that the format reads off arrays of 32 bytes; that the two are one row, where vb are the bytes of u,
is not shown HERE: OnBytes/Slice/SeedRow.lean. FROM UNIFORM BLOCKS TO THE ORACLE, one table, no
number evaluated: the limits (3), (4), (5) of OnBytes/Slice/SeedBias.lean stand. That `recZ` is the
programs' sample map is a reading of their text. (Of the Lean port one part is shown: the
coefficients of its row of a record's answer are `recZ`'s matrix: `coefAt_recRow`,
OnBytes/Slice/BlkRecRow.lean. Of the C++ programs nothing is shown.) Nothing on any hash function.

-/
import OnBytes.Slice.SeedBias
import Run.DrawTieProofs

set_option autoImplicit false

namespace OnBytes.Slice
open Prob Cb Cb.Ood _root_.Iop _root_.Run

/-! ## Seeds off a flat list of drawn values -/

/-- The value that stands for "no value": the element 0. -/
def dV : Fmt.Val := .ext (0, 0, 0)

/-- A drawn value, read in the extension field; 0 if it is no element. -/
noncomputable def gv : Fmt.Val → GE
  | .ext e => toE e
  | _ => 0

/-- An element as a factor; 1 for the element 0. -/
noncomputable def nzOf (x : GE) : NZ := if h : x ≠ 0 then ⟨x, h⟩ else ⟨1, one_ne_zero⟩

/-- **s seeds off a flat list of drawn values**: lg coordinates and a factor for each. -/
noncomputable def readFlat (lg : ℕ) : (s : ℕ) → List Fmt.Val → Fin s → (Fin lg → GE) × NZ
  | 0, _ => fun i => i.elim0
  | s + 1, l =>
    Fin.cons (fun c => gv (l.getD c.val dV), nzOf (gv (l.getD lg dV)))
      (readFlat lg s (l.drop (lg + 1)))

/-- Where what is left behind n members begins with x: member n is x, and t is left behind n + 1. -/
theorem getD_drop_cons {α : Type} (d : α) : ∀ (n : ℕ) (l : List α) (x : α) (t : List α),
    l.drop n = x :: t → l.getD n d = x ∧ l.drop (n + 1) = t
  | 0, [], _, _, h => by cases h
  | 0, _ :: _, _, _, h => by
    cases h
    exact ⟨rfl, rfl⟩
  | _ + 1, [], _, _, h => by cases h
  | n + 1, _ :: l, x, t, h => getD_drop_cons d n l x t h

/-! ## The sampler's values -/

/-- A number below p, made a word and read in the base field, is `eF` of it. -/
theorem toF_toU (x : FV .two) : toF (toU x) = eF x := by
  show (((toU x).toNat : ℕ) : GF) = (x.val : GF)
  rw [toU_toNat]

/-- Three numbers below p, made words and read in the extension field, are `eE` of them. -/
theorem toE_toU3 (e : EV .two) : toE (toU3 e) = eE e := by
  show (⟨toF (toU e.1), toF (toU e.2.1), toF (toU e.2.2)⟩ : GE) = ⟨eF e.1, eF e.2.1, eF e.2.2⟩
  rw [toF_toU, toF_toU, toF_toU]

/-- The values as they are handed on do not see how the list of draws is written. -/
theorem outAll_cast {ds ds' : List Fmt.Draw} (h : ds = ds') (v : Vals .two ds) :
    outAll .two ds' (cast (congrArg (Vals .two) h) v) = outAll .two ds v := by
  subst h
  rfl

/-- The values of n elements and further draws, as they are handed on: value c, read by `gv`, is
coordinate c of what `eElems` gives; what is left behind n values are the further draws' values. -/
theorem eElems_out (rest : List Fmt.Draw) : ∀ (n : ℕ)
    (w : Vals .two (List.replicate n .elem ++ rest)),
    (∀ c : Fin n, gv ((outAll .two _ w).getD c.val dV) = (eElems rest n w).1 c) ∧
      (outAll .two _ w).drop n = outAll .two rest (eElems rest n w).2
  | 0, _ => ⟨fun c => c.elim0, rfl⟩
  | n + 1, w => by
    obtain ⟨h1, h2⟩ := eElems_out rest n w.2
    refine ⟨fun c => ?_, h2⟩
    refine Fin.cases ?_ (fun j => ?_) c
    · exact toE_toU3 w.1
    · exact h1 j

/-- **`toSeed` reads the values as they are handed on.** -/
theorem toSeed_eq (lg : ℕ) : ∀ (s : ℕ) (v : Vals .two (seedDraws lg s)),
    toSeed lg s v = readFlat lg s (outAll .two (seedDraws lg s) v)
  | 0, _ => funext fun i => i.elim0
  | s + 1, v => by
    have hc : outAll .two (List.replicate lg Fmt.Draw.elem ++ Fmt.Draw.elemNZ :: seedDraws lg s)
        (cast (congrArg (Vals .two) (List.append_assoc (List.replicate lg Fmt.Draw.elem) [.elemNZ]
          (seedDraws lg s))) v) = outAll .two (seedDraws lg (s + 1)) v :=
      outAll_cast (List.append_assoc (List.replicate lg Fmt.Draw.elem) [.elemNZ]
        (seedDraws lg s)) v
    obtain ⟨p, hp⟩ : ∃ p, p = eElems (.elemNZ :: seedDraws lg s) lg
        (cast (congrArg (Vals .two) (List.append_assoc (List.replicate lg Fmt.Draw.elem) [.elemNZ]
          (seedDraws lg s))) v) := ⟨_, rfl⟩
    obtain ⟨h1, h2⟩ := eElems_out (.elemNZ :: seedDraws lg s) lg
      (cast (congrArg (Vals .two) (List.append_assoc (List.replicate lg Fmt.Draw.elem) [.elemNZ]
        (seedDraws lg s))) v)
    rw [hc, ← hp] at h1 h2
    obtain ⟨g1, g2⟩ := getD_drop_cons dV lg _ _ _ h2
    have e1 : toSeed lg (s + 1) v =
        (Fin.cons (p.1, eNZ p.2.1) (toSeed lg s p.2.2) : Fin (s + 1) → (Fin lg → GE) × NZ) := by
      rw [hp]
      rfl
    have e2 : readFlat lg (s + 1) (outAll .two (seedDraws lg (s + 1)) v) =
        (Fin.cons (fun c => gv ((outAll .two (seedDraws lg (s + 1)) v).getD c.val dV),
            nzOf (gv ((outAll .two (seedDraws lg (s + 1)) v).getD lg dV)))
          (readFlat lg s ((outAll .two (seedDraws lg (s + 1)) v).drop (lg + 1))) :
          Fin (s + 1) → (Fin lg → GE) × NZ) := rfl
    rw [e1, e2, g1, g2, ← toSeed_eq lg s]
    congr 1
    refine Prod.ext (funext fun c => (h1 c).symm) ?_
    show eNZ p.2.1 = nzOf (toE (toU3 p.2.1.1))
    rw [toE_toU3]
    unfold nzOf
    have hne : eE p.2.1.1 ≠ 0 := (eNZ p.2.1).2
    rw [dif_pos hne]
    rfl

/-! ## The program's list -/

/-- A list of seeds as the flat list of their values. -/
def flat (l : List (List Fmt.Ext × Fmt.Ext)) : List Fmt.Val :=
  l.flatMap fun y => y.1.map Fmt.Val.ext ++ [Fmt.Val.ext y.2]

/-- The program's list of seeds, from the drawn triples (`recordSeeds`). -/
def progSeeds (l : List (List Fmt.Ext × Fmt.Ext)) : List (List E × E) :=
  l.map fun y => (y.1.map E.ofTriple, E.ofTriple y.2)

/-- **`seedOf` of the program's list reads the flat list of its values**, if there are s seeds with
points of lg coordinates. -/
theorem seedOf_flat (lg : ℕ) : ∀ (s : ℕ) (l : List (List Fmt.Ext × Fmt.Ext)), l.length = s →
    (∀ y ∈ l, y.1.length = lg) → seedOf lg s (progSeeds l) = readFlat lg s (flat l)
  | 0, _, _, _ => funext fun i => i.elim0
  | s + 1, [], h, _ => by cases h
  | s + 1, y :: l, h, hp => by
    have hy : (y.1.map Fmt.Val.ext).length = lg := by
      rw [List.length_map]
      exact hp y List.mem_cons_self
    have e0 : flat (y :: l) = y.1.map Fmt.Val.ext ++ (Fmt.Val.ext y.2 :: flat l) := by
      show (y.1.map Fmt.Val.ext ++ [Fmt.Val.ext y.2]) ++ flat l = _
      rw [List.append_assoc]
      rfl
    obtain ⟨g1, g2⟩ := getD_drop_cons dV lg (flat (y :: l)) (Fmt.Val.ext y.2) (flat l)
      (by rw [e0]; exact List.drop_left' hy)
    have ih := seedOf_flat lg s l (Nat.succ.inj h) fun z hz => hp z (List.mem_cons_of_mem _ hz)
    show _ = Fin.cons _ _
    rw [g1, g2, ← ih]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · show seedOf1 lg (y.1.map E.ofTriple, E.ofTriple y.2) = _
      refine Prod.ext (funext fun c => ?_) rfl
      show readE ((y.1.map E.ofTriple).getD c.val (E.ofTriple (0, 0, 0))) =
        gv ((flat (y :: l)).getD c.val dV)
      rw [e0, List.getD_append _ _ _ _ (by rw [hy]; exact c.isLt)]
      show _ = gv ((y.1.map Fmt.Val.ext).getD c.val (Fmt.Val.ext (0, 0, 0)))
      rw [List.getD_map, List.getD_map]
      rfl
    · rfl

/-! ## The format's list of draws against "a seed, s times" -/

section
variable (f : Fmt.Fld) (row : Fmt.Row)

/-- Two lists of draws, one behind the other: the values of the first, then those of the second from
the place where the first ended. -/
theorem readAll_append : ∀ (a b : List Fmt.Draw) (c : ℕ),
    Fmt.readAll f (a ++ b) row c =
      ((Fmt.readAll f a row c).1 ++ (Fmt.readAll f b row (Fmt.readAll f a row c).2).1,
        (Fmt.readAll f b row (Fmt.readAll f a row c).2).2)
  | [], _, _ => rfl
  | d :: a, b, c => by
    show ((d.read f row c).1 :: (Fmt.readAll f (a ++ b) row (d.read f row c).2).1,
      (Fmt.readAll f (a ++ b) row (d.read f row c).2).2) = _
    rw [readAll_append a b]
    rfl

/-- The format's list of n draws of an element gives the values of "an element, n times", and ends
at the same place. -/
theorem readAll_elems : ∀ (n c : ℕ),
    Fmt.readAll f (List.replicate n .elem) row c =
      ((((Fmt.drawE f).times n) row c).1.map Fmt.Val.ext, (((Fmt.drawE f).times n) row c).2)
  | 0, _ => rfl
  | n + 1, c => by
    show (Fmt.Val.ext (Fmt.drawE f row c).1 ::
        (Fmt.readAll f (List.replicate n .elem) row (Fmt.drawE f row c).2).1,
      (Fmt.readAll f (List.replicate n .elem) row (Fmt.drawE f row c).2).2) = _
    rw [readAll_elems n]
    rfl

/-- A draw, n times, gives n values. -/
theorem times_length {α : Type} (x : Fmt.Dr α) : ∀ (n c : ℕ), ((x.times n) row c).1.length = n
  | 0, _ => rfl
  | n + 1, c => congrArg (· + 1) (times_length x n (x row c).2)

/-- **The format's list of the seeds' draws gives the flat list of "a seed, s times"**, and ends at
the same place. -/
theorem readAll_seeds (lg : ℕ) : ∀ (s c : ℕ),
    Fmt.readAll f (seedDraws lg s) row c =
      (flat (((Fmt.drawSeed f lg).times s) row c).1, (((Fmt.drawSeed f lg).times s) row c).2)
  | 0, _ => rfl
  | s + 1, c => by
    show Fmt.readAll f ((List.replicate lg .elem ++ [.elemNZ]) ++ seedDraws lg s) row c = _
    rw [readAll_append, readAll_append, readAll_elems, readAll_seeds lg s]
    rfl

/-- Each of these seeds has a point of lg coordinates. -/
theorem seed_points (lg : ℕ) : ∀ (s c : ℕ), ∀ y ∈ (((Fmt.drawSeed f lg).times s) row c).1,
    y.1.length = lg
  | 0, _, _, h => absurd h List.not_mem_nil
  | s + 1, c, y, h => by
    rcases List.mem_cons.1 h with rfl | h'
    · exact times_length row (Fmt.drawE f) lg c
    · exact seed_points lg s _ y h'

end

/-- **THE PROGRAM'S SEEDS ARE `toSeed` OF THE LIBRARY'S SAMPLER**, on the row of the blocks' words:
`seedOf` of the list that the text of `recordSeeds` draws from that row is `toSeed` of the value of
`seedBS` on the blocks. -/
theorem seedTie (lg s : ℕ) (u : Fin (seedBS lg s).b → Dig 256) :
    seedOf lg s (progSeeds
        (timesT (Fmt.drawSeed .two lg) s (rowFn 0 (rowOf e64 (seedBS lg s).b u)) 0).1) =
      toSeed lg s ((seedBS lg s).φ u) := by
  rw [toSeed_eq, timesT_eq]
  have h := drawTie_bs .two (seedDraws lg s) u
  rw [readAll_seeds] at h
  show _ = readFlat lg s (outAll .two (seedDraws lg s) ((bsOf .two (seedDraws lg s)).φ u))
  rw [h]
  exact seedOf_flat lg s _ (times_length _ _ s 0) (seed_points .two _ lg s 0)

/-- **The bound of OnBytes/Slice/SeedBias.lean with the program's own expression for the seed**: for
ONE stored table f, fixed before the blocks, within the Johnson bound: over uniform blocks, the
seeds that the text of `recordSeeds` draws from the row of the blocks' words are such that the
record does not single one table out with probability at most the bound of `coll_pr`. -/
theorem coll_pr_prog (T : Fmt.M1.Code) (v eM lg s : ℕ) (ha : T.a ≤ 32) (hk : T.r + T.l ≤ 2 ^ T.a)
    (he : eM < 2 ^ T.a - (T.r + T.l) + 1)
    (hJ : InJohnson (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM) (h3 : 3 * s ≤ T.l)
    (hl : T.l - 3 * s ≤ 2 ^ lg) (f : Fin (2 ^ T.a) → Run.PQ.SgX) :
    pr (unif (Fin (seedBS lg s).b → Dig 256))
        {u | (decRec T v eM lg s).coll f (seedOf lg s (progSeeds
          (timesT (Fmt.drawSeed .two lg) s (rowFn 0 (rowOf e64 (seedBS lg s).b u)) 0).1))} ≤
      kapSl 128 ^ (seedBS lg s).b *
        ((((listMax (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM).choose 2 * (recZ T.l lg s).err : ℕ) :
          ENNReal) / Fintype.card (recZ T.l lg s).D) := by
  have h := coll_pr_toSeed T v eM lg s ha hk he hJ h3 hl f
  simp only [← seedTie] at h
  exact h

end OnBytes.Slice
