-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/VerifyShape.lean: the parameters of the chains, as a call reads them back, hold one
shape of the stored tables.

`planned` (OnBytes/Model/Verify.lean) has the parameter bytes of the seven chains spelled and reads
them back. Five of the chains hold a shape of the stored tables: the key's one-time chain and shared
chain and the proof's first chain and shared chain in the item "the test on the table", the entry's
chain in the item "the link". The checks of the three files read the tables under the shape in their
own chains. This file proves that it is one shape, for chains whose parameter bytes are fewer than
2^64.

How. The planner puts one shape of the tables into the three shapes that it makes (`sized_index`).
The items are read back as they were spelled (`Given.read_items`, OnBytes/Params/ReadBackLaws.lean).
The tables' shape that is read from such an item depends on the item's first 48 bytes alone, which
spell that one shape (OnBytes/Params/IndexLaws.lean). A file's shared chain is refused unless its
item has the bytes of the item in the chain with which the file begins.

Main theorems: `sized_index`, `configure_items`, `KeyChains.read_lin`, `ProofChains.read_lin`,
`planned_shapes`.

What is not claimed. Nothing on soundness. That the shape which the chains hold is the shape that
the planner made: a number from 2^64 on is spelled modulo 2^64. The tables' shape is `IndexShape`,
six numbers; how the matrix lies in a table (`kLo`, `matrixRows` of `LinShape`) is no part of it.
Nothing on the other fields of the shapes, but that a file's shared chain holds the whole test on
the table of the chain with which the file begins. The bound on the parameter bytes is a hypothesis
here; OnBytes/Tie/SameChains.lean takes it from a yes of the checks. For proofs only; the program
does not import this file.
-/
import OnBytes.Model.VerifyDigest
import OnBytes.Params.IndexLaws

set_option autoImplicit false

namespace OnBytes.Params

/-- The shape of the test on the table holds the tables' shape that follows from the setting and the
table's sizes. -/
theorem linSized_index {s : Setting} {L : LinLines} {T : TableSize} {codes c : Codes}
    {x : LinSized} (h : linSized s L T codes = some (x, c)) :
    x.shape.fold.index = indexShapeOf s T := by
  unfold linSized at h
  extract_lets at h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  obtain ⟨⟨x1, y1, z1⟩, _, h⟩ := opt_bind h
  replace h := opt_guard h
  obtain ⟨stU, _, h⟩ := opt_bind h
  obtain ⟨stO, h⟩ := opt_either h
  obtain ⟨stW, _, h⟩ := opt_bind h
  repeat' split at h
  all_goals first
    | (cases h; rfl)
    | cases h

/-- The same for the shape of a link. -/
theorem linkSized_index {s : Setting} {l : Lines} {T : TableSize} {codes c : Codes}
    {x : LinkSized} (h : linkSized s l T codes = some (x, c)) :
    x.shape.table = indexShapeOf s T := by
  unfold linkSized at h
  extract_lets at h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  obtain ⟨y, _, h⟩ := opt_bind h
  repeat' split at h
  all_goals first
    | (cases h; rfl)
    | cases h

/-- The sizes of a proof's chains hold the tables' shape that follows from the setting of the lines
and from the table's sizes in them; that these sizes follow from the lines is `proofSized_table`
(OnBytes/Params/ConfigureLaws.lean). -/
theorem proofSized_index {l : Lines} {sub : Subproofs} {z : ProofSized}
    (h : proofSized l sub = some z) :
    z.batch.shape.fold.index = indexShapeOf (settingOf l) z.batch.table := by
  unfold proofSized at h
  extract_lets at h
  replace h := opt_guard h
  obtain ⟨link, _, h⟩ := opt_bind h
  obtain ⟨stages, _, h⟩ := opt_bind h
  obtain ⟨T, hT, h⟩ := opt_bind h
  split at h
  replace h := opt_guard h
  obtain ⟨⟨batch, c2⟩, hb, h⟩ := opt_bind h
  cases h
  rw [linSized_table hb]
  exact linSized_index hb

/-- The sizes of a key's chains hold the tables' shape that follows from the lines. -/
theorem keySized_index {l : Lines} {shape : Plan.Shape} {z : Plan.KeySized}
    (h : Plan.keySized l shape = some z) :
    ∃ T, deriveTable (settingOf l) l = some T ∧
      z.once.shape.fold.index = indexShapeOf (settingOf l) T := by
  unfold Plan.keySized at h
  extract_lets at h
  obtain ⟨T, hT, h⟩ := opt_bind h
  obtain ⟨L, _, h⟩ := opt_bind h
  extract_lets at h
  replace h := opt_guard h
  obtain ⟨⟨once, c1⟩, ho, h⟩ := opt_bind h
  obtain ⟨⟨ranges, c2⟩, _, h⟩ := opt_bind h
  cases h
  exact ⟨T, hT, linSized_index ho⟩

/-- What `sized` returns holds one shape of the tables in the key's, the entry's and the proof's
shapes. -/
theorem sized_index {l : Lines} {x : Shapes} {z : Sized} (h : sized l x = .ok z) :
    z.key.once.shape.fold.index = z.link.shape.table ∧
      z.proof.batch.shape.fold.index = z.link.shape.table := by
  unfold sized at h
  extract_lets at h
  replace h := exc_guard h
  obtain ⟨proof, hp, h⟩ := exc_bind h
  replace h := exc_guard h
  obtain ⟨key, hk, h⟩ := exc_bind h
  replace h := exc_guard h
  obtain ⟨⟨link, codes⟩, hl, h⟩ := exc_bind h
  replace h := exc_guard h
  replace h := exc_guard h
  cases h
  have h1 := proofSized_table (orRefuse_ok hp)
  have h2 := proofSized_index (orRefuse_ok hp)
  obtain ⟨T, hT, h3⟩ := keySized_index (orRefuse_ok hk)
  have h4 := linkSized_index (orRefuse_ok hl)
  have e : T = proof.batch.table := Option.some.inj (hT.symm.trans h1)
  exact ⟨by rw [h3, e]; exact h4.symm, by rw [h2]; exact h4.symm⟩

/-- The items under which `configure` spells the parameter bytes of the key's one-time chain, of the
entry's chain and of the proof's first chain; the sizes in what it returns are those of `sized`. -/
theorem configure_items {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat}
    {made : Configured} (h : configure l x cfg bits = .ok made) :
    sized l x = .ok made.sized ∧
      (∃ P, made.keyOneTime = Fmt.paramsBytes P cfg (Plan.oneTimeItems made.sized.key)) ∧
      (∃ P, made.entryLink = Fmt.paramsBytes P cfg
        [("codes", spellCodes made.sized.entryCodes),
          ("the link", spellLink made.sized.link.shape)]) ∧
      (∃ P a b c d e, made.first = Fmt.paramsBytes P cfg
        [("codes", spellCodes made.sized.proof.codes),
          ("the test on the table", spellLin made.sized.proof.batch.shape),
          ("request's shape", a), ("layout", b), ("links' identifiers", c),
          ("pending rows", d), ("binding tree", e)]) := by
  unfold configure at h
  obtain ⟨z, hz, h⟩ := exc_bind h
  obtain ⟨proof, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨entry, _, h⟩ := exc_bind h
  split at h
  · obtain ⟨_, _, h⟩ := exc_bind h
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    cases h
    exact ⟨hz, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, _, _, _, _, _, rfl⟩⟩
  · cases h

/-- What `Link.read` returns: its items are "codes" and "the link", and its link is read from the
second. -/
theorem Link.read_link {b : ByteArray} {q : Link} (h : Link.read b = some q) :
    ∃ c l, q.given.items = [("codes", c), ("the link", l)] ∧ readLink l = some q.link := by
  unfold Link.read at h
  obtain ⟨g, _, h⟩ := opt_bind h
  split at h
  · rename_i c l hi
    obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨y, hy, h⟩ := opt_bind h
    cases h
    exact ⟨c, l, hi, hy⟩
  · cases h

/-- What `OneTime.read` returns: its five items, and its test on the table is read from the last. -/
theorem OneTime.read_lin {b : ByteArray} {q : OneTime} (h : OneTime.read b = some q) :
    ∃ m r t c l, q.given.items = [("index-mask message", m), ("ranges", r), ("binding tree", t),
      ("codes", c), ("the test on the table", l)] ∧ readLin l = some q.lin := by
  unfold OneTime.read at h
  obtain ⟨g, _, h⟩ := opt_bind h
  split at h
  · rename_i m r t c l hi
    obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨y, hy, h⟩ := opt_bind h
    cases h
    exact ⟨m, r, t, c, l, hi, hy⟩
  · cases h

/-- What `First.read` returns: its items begin with "codes" and "the test on the table", and its
test on the table is read from the second. -/
theorem First.read_lin {b : ByteArray} {q : First} (h : First.read b = some q) :
    ∃ c l rest, q.given.items = ("codes", c) :: ("the test on the table", l) :: rest ∧
      readLin l = some q.lin := by
  unfold First.read at h
  obtain ⟨g, _, h⟩ := opt_bind h
  split at h
  · rename_i c l s y i n t more hi
    obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨w, hw, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    dsimp only at h
    split at h
    · cases h
      exact ⟨c, l, _, hi, hw⟩
    · cases h
  · cases h

/-- What `Shared.read` returns: its items are "codes" and "the test on the table", and its test on
the table is read from the second. -/
theorem Shared.read_lin {b : ByteArray} {q : Shared} (h : Shared.read b = some q) :
    ∃ c l, q.given.items = [("codes", c), ("the test on the table", l)] ∧
      readLin l = some q.lin := by
  unfold Shared.read at h
  obtain ⟨g, _, h⟩ := opt_bind h
  split at h
  · rename_i c l hi
    obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨y, hy, h⟩ := opt_bind h
    cases h
    exact ⟨c, l, hi, hy⟩
  · cases h

/-- If `sameItem` says yes of two chains and a name, and each holds an item of that name, the two
items' bytes are equal. -/
theorem sameItem_eq {a b : Given} {name : String} {x y : ByteArray}
    (h : sameItem a b name = true) (ha : a.item name = some x) (hb : b.item name = some y) :
    x = y := by
  unfold sameItem at h
  rw [ha, hb] at h
  exact bytes_of_beq h

/-- The key's shared chain as read holds the test on the table of the one-time chain. -/
theorem KeyChains.read_lin {a b c : ByteArray} {k : KeyChains}
    (h : KeyChains.read a b c = some k) : k.shared.lin = k.oneTime.lin := by
  unfold KeyChains.read at h
  obtain ⟨x, hx, h⟩ := opt_bind h
  obtain ⟨y, hy, h⟩ := opt_bind h
  obtain ⟨z, _, h⟩ := opt_bind h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true] at hc
    obtain ⟨_, _, _, _, l1, q1, w1⟩ := OneTime.read_lin hx
    obtain ⟨_, l2, q2, w2⟩ := Shared.read_lin hy
    have e := sameItem_eq hc.1.1.2 (x := l1) (y := l2)
      (by unfold Given.item; rw [q1]; rfl) (by unfold Given.item; rw [q2]; rfl)
    rw [← e, w1] at w2
    exact (Option.some.inj w2).symm
  · cases h

/-- The proof's shared chain as read holds the test on the table of the first chain. -/
theorem ProofChains.read_lin {a b c : ByteArray} {k : ProofChains}
    (h : ProofChains.read a b c = some k) : k.shared.lin = k.first.lin := by
  unfold ProofChains.read at h
  obtain ⟨x, hx, h⟩ := opt_bind h
  obtain ⟨y, hy, h⟩ := opt_bind h
  obtain ⟨z, _, h⟩ := opt_bind h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true] at hc
    obtain ⟨_, l1, _, q1, w1⟩ := First.read_lin hx
    obtain ⟨_, l2, q2, w2⟩ := Shared.read_lin hy
    have e := sameItem_eq hc.1.1.2 (x := l1) (y := l2)
      (by unfold Given.item; rw [q1]; rfl) (by unfold Given.item; rw [q2]; rfl)
    rw [← e, w1] at w2
    exact (Option.some.inj w2).symm
  · cases h

end OnBytes.Params

namespace OnBytes.Model.Verify

open OnBytes.Params (exc_bind)

/-- The tables' shape that the key's one-time chain, the entry's chain and the proof's first chain
hold as read back is one shape, if the parameter bytes of each of the three are fewer than 2^64. -/
theorem planned_shapes {pol KL : ByteArray} {layout : Option ByteArray} {p : Planned}
    (h : planned pol KL layout = .ok p) (hb1 : (p.chains.bytes .keyOneTime).size < 2 ^ 64)
    (hb2 : (p.chains.bytes .link).size < 2 ^ 64)
    (hb3 : (p.chains.bytes .proofFirst).size < 2 ^ 64) :
    p.chains.key.oneTime.lin.fold.index = p.chains.link.link.table ∧
      p.chains.proof.first.lin.fold.index = p.chains.link.link.table := by
  have h32 := (planned_spelled h).1
  obtain ⟨r1, r2, r3⟩ := planned_read h
  have hm : ∃ l x bits, Params.configure l x p.cfg bits = .ok p.chains.made := by
    unfold planned at h
    obtain ⟨X, _, h⟩ := exc_bind h
    dsimp only at h
    obtain ⟨chains, hc, h⟩ := exc_bind h
    obtain ⟨_, _, h⟩ := exc_bind h
    cases h
    obtain ⟨shapes, hm⟩ := chainsOf_made hc
    exact ⟨_, _, _, hm⟩
  obtain ⟨l, x, bits, hm⟩ := hm
  obtain ⟨hz, ⟨P1, e1⟩, ⟨P2, e2⟩, ⟨P3, a, b, c, d, e, e3⟩⟩ := Params.configure_items hm
  obtain ⟨i1, i2⟩ := Params.sized_index hz
  -- the entry's chain
  have g2 := Params.Link.read_given r2
  have b2 : p.chains.bytes .link = p.chains.made.entryLink := rfl
  rw [b2, e2] at g2 hb2
  have t2 := Params.Given.read_items hb2 h32 (by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl <;> (dsimp only; decide)) g2
  obtain ⟨c2, l2, q2, w2⟩ := Params.Link.read_link r2
  rw [t2] at q2
  simp only [List.cons.injEq, Prod.mk.injEq, true_and, and_true] at q2
  rw [← q2.2] at w2
  have s2 := Params.readLink_table w2
  -- the key's one-time chain
  have k1 := (Params.KeyChains.read_parts r1).1
  have g1 := Params.OneTime.read_given k1
  have b1 : p.chains.bytes .keyOneTime = p.chains.made.keyOneTime := rfl
  rw [b1, e1] at g1 hb1
  have t1 := Params.Given.read_items hb1 h32 (by
    intro y hy
    simp only [Plan.oneTimeItems, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)) g1
  obtain ⟨_, _, _, _, l1, q1, w1⟩ := Params.OneTime.read_lin k1
  rw [t1] at q1
  simp only [Plan.oneTimeItems, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at q1
  rw [← q1.2.2.2.2] at w1
  have s1 := Params.readLin_index w1
  -- the proof's first chain
  have k3 := (Params.ProofChains.read_parts r3).1
  have g3 := Params.First.read_given k3
  have b3 : p.chains.bytes .proofFirst = p.chains.made.first := rfl
  rw [b3, e3] at g3 hb3
  have t3 := Params.Given.read_items hb3 h32 (by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)) g3
  obtain ⟨_, l3, _, q3, w3⟩ := Params.First.read_lin k3
  rw [t3] at q3
  simp only [List.cons.injEq, Prod.mk.injEq, true_and] at q3
  rw [← q3.2.1] at w3
  have s3 := Params.readLin_index w3
  rw [s1, s2, s3, i1, i2]
  exact ⟨rfl, rfl⟩

end OnBytes.Model.Verify

#print axioms OnBytes.Model.Verify.planned_shapes
