-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/Rules6Draws.lean: a round's draws as a list, from the plan's entry and the kind; and the theorem
that the round's message is that list of draws, collected.

A draw is the reading of one value of the verifier's message (a challenge) from the next words of a
row of 64-bit words (`Row`). The plan's entry (`Entry`, Fmt/Plan.lean) has the numbers of a round's
draws; the kind (`Kind`) says what the verifier's message of the round consists of.

Fmt/Rules6.lean reads a list of draws in a given order (`readAll`). Fmt/Rules6Round.lean makes the
message of a round from the plan's entry and the kind in one go (`drawRoundD`, `drawRound`). Here
the two are connected.

Sources. Section 6 of the format page (docs/format/FORMAT.md); this file is not held against
the page as it ships, and may differ from it. The order is the one that this file reads there
(R6.2, R6.9, R6.10) at every entry that fits its kind (Fmt/Rules6Round.lean:
`Entry.fits`).
No Mathlib.


1. What the file contains.
   `dsOf e k`: the round's draws as a list, in the order of `drawRoundD`:
     the positions;
     the elements (in a round of seeds: seed after seed, each its coordinates and then its factor,
       and what is left over after them; in every other kind the plain ones, then those that must
       not be 0);
     the matrix entries (`Draw.trits`), in one portion;
     the sealed value (`Draw.sealed`) in a round of that kind.
   `collect vs`: the values of a list of draws, sorted into the record `Drawn`. Elements, positions
     and matrix entries (`trits`) keep the order of the list. Of the sealed values the first is
     kept (`digest`).

2. What is checked when the file compiles. Nine tests (#guard).

3. Theorems.
   `round_list`: `drawRoundD f e k`, from every place of every row, gives `collect` of what
     `readAll f (dsOf e k)` gives, and ends at the same place.
   `round_readAll`: the same as an equation between draws (of type `Dr Drawn`).
   `most_list`: the most words of that list (`mostAll`) is `wordsAtMost e k`.

4. What is not claimed. Nothing on laws of the draws.

Terms: lean/GLOSSARY.md.
-/
import Fmt.Rules6Round

namespace Fmt

/-- the draws of s seeds of v coordinates -/
def dsSeeds (s v : Nat) : List Draw :=
  (List.replicate s (List.replicate v Draw.elem ++ [Draw.elemNZ])).flatten

/-- the draws of a round's elements -/
def dsElems (e : Entry) (k : Kind) : List Draw :=
  if k = .seeds then
    dsSeeds e.drawNZ ((e.drawE - e.drawNZ) / e.drawNZ) ++
      List.replicate ((e.drawE - e.drawNZ) % e.drawNZ) Draw.elem
  else List.replicate (e.drawE - e.drawNZ) Draw.elem ++ List.replicate e.drawNZ Draw.elemNZ

/-- A round's draws, as a list. -/
def dsOf (e : Entry) (k : Kind) : List Draw :=
  List.replicate e.poss (Draw.pos e.logN) ++
    (dsElems e k ++ (Draw.trits e.trits :: (if k = .sealed then [Draw.sealed] else [])))

/-- The values of a list of draws, as the record of a round. -/
def collect : List Val → Drawn
  | [] => ⟨[], [], [], none⟩
  | .ext x :: l => { collect l with elems := x :: (collect l).elems }
  | .pos x :: l => { collect l with poss := x :: (collect l).poss }
  | .trits t :: l => { collect l with trits := t ++ (collect l).trits }
  | .sealed d :: l => { collect l with digest := some d }

-- the toy plan's six rounds
#guard dsOf toyE1 .elems = [.elem, .trits 0]
#guard dsOf toyE2 .nothing = [.trits 0]
#guard dsOf toyE3 .positions = [.pos 10, .pos 10, .pos 10, .pos 10, .pos 10, .elem, .trits 0]
#guard dsOf toyE4 .seeds = [.elem, .elem, .elemNZ, .trits 0]
#guard dsOf toyE5 .entries = [.trits 40]
#guard dsOf toyE6 .sealed = [.trits 0, .sealed]
#guard dsOf { name := "", drawE := 5, drawNZ := 2 } .seeds = [.elem, .elemNZ, .elem, .elemNZ, .elem, .trits 0]
#guard dsOf { name := "", drawE := 5, drawNZ := 2 } .elems = [.elem, .elem, .elem, .elemNZ, .elemNZ, .trits 0]
#guard collect [.pos 3, .ext (1, 2, 3), .pos 5, .trits [1, -1], .trits [0]] = ⟨[(1, 2, 3)], [3, 5], [1, -1, 0], none⟩


/-! ## The round's message is the list of draws, collected -/

/-- a draw n times, where each value is mapped -/
theorem times_map {α β : Type} (x : Dr α) (g : α → β) : ∀ (n : Nat) (r : Row) (c : Nat),
    ((x.bind fun a => Dr.pure (g a)).times n) r c = ((x.times n r c).1.map g, (x.times n r c).2)
  | 0, _, _ => rfl
  | n + 1, r, c => by
    show (g (x r c).1 :: (((x.bind fun a => Dr.pure (g a)).times n) r (x r c).2).1,
        (((x.bind fun a => Dr.pure (g a)).times n) r (x r c).2).2) = _
    rw [times_map x g n r (x r c).2]
    rfl

theorem readAll_append (f : Fld) :
    ∀ (a b : List Draw) (r : Row) (c : Nat), readAll f (a ++ b) r c =
      ((readAll f a r c).1 ++ (readAll f b r (readAll f a r c).2).1,
        (readAll f b r (readAll f a r c).2).2)
  | [], _, _, _ => rfl
  | d :: a, b, r, c => by
    show ((d.read f r c).1 :: (readAll f (a ++ b) r (d.read f r c).2).1,
        (readAll f (a ++ b) r (d.read f r c).2).2) = _
    rw [readAll_append f a b r (d.read f r c).2]
    rfl

theorem readAll_replicate (f : Fld) (d : Draw) :
    ∀ (n : Nat) (r : Row) (c : Nat), readAll f (List.replicate n d) r c = (d.read f).times n r c
  | 0, _, _ => rfl
  | n + 1, r, c => by
    show ((d.read f r c).1 :: (readAll f (List.replicate n d) r (d.read f r c).2).1,
        (readAll f (List.replicate n d) r (d.read f r c).2).2) = _
    rw [readAll_replicate f d n r (d.read f r c).2]
    rfl

theorem readAll_elems (f : Fld) (n : Nat) (r : Row) (c : Nat) :
    readAll f (List.replicate n Draw.elem) r c =
      (((drawE f).times n r c).1.map Val.ext, ((drawE f).times n r c).2) :=
  (readAll_replicate f .elem n r c).trans (times_map (drawE f) Val.ext n r c)

theorem readAll_elemsNZ (f : Fld) (n : Nat) (r : Row) (c : Nat) :
    readAll f (List.replicate n Draw.elemNZ) r c =
      (((drawNZ f).times n r c).1.map Val.ext, ((drawNZ f).times n r c).2) :=
  (readAll_replicate f .elemNZ n r c).trans (times_map (drawNZ f) Val.ext n r c)

theorem readAll_poss (f : Fld) (k n : Nat) (r : Row) (c : Nat) :
    readAll f (List.replicate n (Draw.pos k)) r c =
      ((drawPoss k n r c).1.map Val.pos, (drawPoss k n r c).2) :=
  (readAll_replicate f (.pos k) n r c).trans (times_map (drawPos k) Val.pos n r c)

/-- one seed -/
theorem readAll_seed (f : Fld) (v : Nat) (r : Row) (c : Nat) :
    readAll f (List.replicate v Draw.elem ++ [Draw.elemNZ]) r c =
      ((drawSeedL f v r c).1.map Val.ext, (drawSeedL f v r c).2) := by
  rw [readAll_append, readAll_elems]
  show (_ ++ [Val.ext _], _) = ((_ ++ [_]).map Val.ext, _)
  rw [List.map_append]
  rfl

/-- seeds, one after the other -/
theorem readAll_seeds (f : Fld) (v : Nat) :
    ∀ (s : Nat) (r : Row) (c : Nat), readAll f (dsSeeds s v) r c =
      ((((drawSeedL f v).times s r c).1.flatten).map Val.ext, ((drawSeedL f v).times s r c).2)
  | 0, _, _ => rfl
  | s + 1, r, c => by
    show readAll f ((List.replicate v Draw.elem ++ [Draw.elemNZ]) ++ dsSeeds s v) r c = _
    rw [readAll_append, readAll_seed, readAll_seeds f v s r (drawSeedL f v r c).2]
    show (_ ++ _, _) =
      ((((drawSeedL f v r c).1 ::
          ((drawSeedL f v).times s r (drawSeedL f v r c).2).1).flatten).map Val.ext,
        _)
    rw [List.flatten_cons, List.map_append]
    rfl

/-- the elements of a round -/
theorem readAll_dsElems (f : Fld) (e : Entry) (k : Kind) (r : Row) (c : Nat) :
    readAll f (dsElems e k) r c =
      ((drawElems f e k r c).1.map Val.ext, (drawElems f e k r c).2) := by
  unfold dsElems drawElems
  by_cases h : k = .seeds
  · rw [if_pos h, if_pos h, readAll_append, readAll_seeds, readAll_elems]
    show (_ ++ _, _) = (List.map Val.ext (_ ++ _), _)
    rw [List.map_append]
    rfl
  · rw [if_neg h, if_neg h, readAll_append, readAll_elems, readAll_elemsNZ]
    show (_ ++ _, _) = (List.map Val.ext (_ ++ _), _)
    rw [List.map_append]
    rfl

theorem collect_poss :
    ∀ (ps : List Nat) (l : List Val),
      collect (ps.map Val.pos ++ l) = { collect l with poss := ps ++ (collect l).poss }
  | [], _ => rfl
  | p :: ps, l => by
    show { collect (ps.map Val.pos ++ l) with poss := p :: (collect (ps.map Val.pos ++ l)).poss } =
      _
    rw [collect_poss ps l]
    rfl

theorem collect_exts :
    ∀ (es : List Ext) (l : List Val),
      collect (es.map Val.ext ++ l) = { collect l with elems := es ++ (collect l).elems }
  | [], _ => rfl
  | x :: es, l => by
    show { collect (es.map Val.ext ++ l) with
           elems := x :: (collect (es.map Val.ext ++ l)).elems } = _
    rw [collect_exts es l]
    rfl

/-- the end of the list: the matrix entries, and the sealed value in a round of that kind -/
theorem readAll_tail (f : Fld) (n : Nat) (k : Kind) (r : Row) (c : Nat) :
    (collect (readAll f (Draw.trits n :: (if k = .sealed then [Draw.sealed] else [])) r c).1,
        (readAll f (Draw.trits n :: (if k = .sealed then [Draw.sealed] else [])) r c).2) =
      ((⟨[], [], (drawTrits n r c).1, (drawDigest k r (drawTrits n r c).2).1⟩ : Drawn),
        (drawDigest k r (drawTrits n r c).2).2) := by
  unfold drawDigest
  by_cases h : k = .sealed
  · rw [if_pos h, if_pos h]
    show ((⟨[], [], (drawTrits n r c).1 ++ [], _⟩ : Drawn), _) = _
    rw [List.append_nil]
    rfl
  · rw [if_neg h, if_neg h]
    show ((⟨[], [], (drawTrits n r c).1 ++ [], _⟩ : Drawn), _) = _
    rw [List.append_nil]
    rfl

/-- States: the round's message is the list of draws, collected, from every place of every row. -/
def Spec.round_list : Prop :=
  ∀ (f : Fld) (e : Entry) (k : Kind) (r : Row) (c : Nat),
    drawRoundD f e k r c = (collect (readAll f (dsOf e k) r c).1, (readAll f (dsOf e k) r c).2)

/-- States the same as an equation between draws. -/
def Spec.round_readAll : Prop :=
  ∀ (f : Fld) (e : Entry) (k : Kind),
    drawRoundD f e k = (readAll f (dsOf e k)).bind fun l => Dr.pure (collect l)

/-- States: the most words of the list (`mostAll`) is `wordsAtMost e k`. -/
def Spec.most_list : Prop := ∀ (e : Entry) (k : Kind), mostAll (dsOf e k) = wordsAtMost e k

theorem round_list : Spec.round_list := by
  intro f e k r c
  unfold dsOf
  rw [readAll_append, readAll_poss, readAll_append, readAll_dsElems]
  show _ = (collect
        ((drawPoss e.logN e.poss r c).1.map Val.pos ++
          ((drawElems f e k r (drawPoss e.logN e.poss r c).2).1.map Val.ext ++ _)),
      _)
  rw [collect_poss, collect_exts]
  have h := readAll_tail f e.trits k r (drawElems f e k r (drawPoss e.logN e.poss r c).2).2
  rw [(Prod.mk.inj h).1, (Prod.mk.inj h).2]
  show _ = ((⟨_ ++ [], _ ++ [], _, _⟩ : Drawn), _)
  rw [List.append_nil, List.append_nil]
  rfl

theorem round_readAll : Spec.round_readAll := fun f e k =>
  funext fun r => funext fun c => round_list f e k r c

theorem mostAll_append : ∀ a b : List Draw, mostAll (a ++ b) = mostAll a + mostAll b
  | [], b => (Nat.zero_add _).symm
  | d :: a, b => by
    show d.most + mostAll (a ++ b) = d.most + mostAll a + mostAll b
    rw [mostAll_append a b, Nat.add_assoc]

theorem mostAll_replicate (d : Draw) : ∀ n, mostAll (List.replicate n d) = n * d.most
  | 0 => (Nat.zero_mul _).symm
  | n + 1 => by
    show d.most + mostAll (List.replicate n d) = (n + 1) * d.most
    rw [mostAll_replicate d n, Nat.succ_mul, Nat.add_comm]

theorem mostAll_seeds (v : Nat) : ∀ s, mostAll (dsSeeds s v) = s * (v * 18 + 36)
  | 0 => (Nat.zero_mul _).symm
  | s + 1 => by
    show mostAll ((List.replicate v Draw.elem ++ [Draw.elemNZ]) ++ dsSeeds s v) = _
    rw [mostAll_append, mostAll_append, mostAll_replicate, mostAll_seeds v s, Nat.succ_mul]
    show v * 18 + (36 + 0) + s * (v * 18 + 36) = _
    omega

theorem mostAll_dsElems (e : Entry) (k : Kind) :
    mostAll (dsElems e k) = 18 * (e.drawE - e.drawNZ) + 36 * e.drawNZ := by
  unfold dsElems
  by_cases h : k = .seeds
  · rw [if_pos h, mostAll_append, mostAll_seeds, mostAll_replicate]
    have hd := Nat.div_add_mod (e.drawE - e.drawNZ) e.drawNZ
    generalize (e.drawE - e.drawNZ) / e.drawNZ = q at hd ⊢
    generalize (e.drawE - e.drawNZ) % e.drawNZ = t at hd ⊢
    show e.drawNZ * (q * 18 + 36) + t * 18 = _
    rw [← hd, Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm (e.drawNZ * q) 18,
      Nat.mul_comm e.drawNZ 36, Nat.mul_comm t 18]
    omega
  · rw [if_neg h, mostAll_append, mostAll_replicate, mostAll_replicate]
    show (e.drawE - e.drawNZ) * 18 + e.drawNZ * 36 = _
    omega

theorem most_list : Spec.most_list := by
  intro e k
  unfold dsOf wordsAtMost
  rw [mostAll_append, mostAll_replicate, mostAll_append, mostAll_dsElems]
  show e.poss * 1 +
      (_ + ((e.trits + 31) / 32 + mostAll (if k = .sealed then [Draw.sealed] else []))) = _
  by_cases h : k = .sealed
  · rw [if_pos h, if_pos h]
    show e.poss * 1 + (_ + ((e.trits + 31) / 32 + (4 + 0))) = _
    omega
  · rw [if_neg h, if_neg h]
    show e.poss * 1 + (_ + ((e.trits + 31) / 32 + 0)) = _
    omega

end Fmt
