-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/RadiiFirstBlock.lean: of the rows of all seven chains' sendings (`rowsFrom`,
Johnson/Desc/First/Link/Law/RowsFrom.lean) THE FIRST PROOF CHAIN's ROWS ARE THE FIFTH BLOCK, and
their sampled shapes with their radii are what the text on one chain (`packChain`,
Johnson/HB/LLHARD/RadiiWritten.lean) returns at that chain's sendings and samples. Rules on lists
and on steps that can refuse; no evaluation.

Why. The radii of the first proof chain are to be shown to be the written ones. The written ones are
`packChain`'s value at written arguments. Here the rows' side is brought to `packChain`.

General.
  `mapM_len`: a step mapped over a list, where it returns, returns as many. `mapM7`: over seven
    members: seven returns.
  `packChain_len`: where `packChain` returns, it returns one entry a sending.
  `blockOf d q`: the rows of one chain d at its share q. `zip_blocks`: where every share has one
    entry a sending, the rows of all chains are the chains' blocks in a row.
  `firstRows_no`, `firstRows_yes`: `P5T.firstRows` (Johnson/P5T/MemberLists.lean) keeps nothing of a
    block whose chain is not ("proof", 0), and all of a block whose chain is. `sampled_block`: a
    block's column of sampled shapes is its share's second column.
  `one_tags`, `sends_tags`: where the seven chains' sendings are made, they are seven, named ("key",
    0 | 1 | 2), ("entry", 0), ("proof", 0 | 1 | 2), in this order.
**`first_block`**: where the rows are made, and under hA: the sendings are seven; `packChain`
returns at the fifth, at the planner's setting and the samples `samplesP0`; and the first proof
chain's rows' column of sampled shapes is that value's second column.

hA, A PREMISE: wherever the seven lists of calls are made, the setting is the planner's, they are
seven, and the fifth is named ("proof", 0) and says the samples `samplesP0`. Its payer: `calls_say`
(Johnson/HB/LLHARD/RadiiSays.lean).

Limits. Nothing says that the rows are made. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.RowsFrom
import Johnson.HB.LLHARD.RadiiWritten
import Johnson.P5T.MemberLists

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom
open VerifiableInference.Number (sendsFrom)

/-! ## Steps that can refuse, over lists -/

/-- A step mapped over a list, where it returns, returns as many. -/
theorem mapM_len {ε α β : Type} (f : α → Except ε β) : ∀ (l : List α) (r : List β),
    l.mapM f = .ok r → r.length = l.length
  | [], r, h => by
    rw [List.mapM_nil] at h
    cases h
    rfl
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, _, h⟩ := exc_bind h
    obtain ⟨t, ht, h⟩ := exc_bind h
    cases h
    rw [List.length_cons, List.length_cons, mapM_len f l t ht]

/-- Over seven members: seven returns. -/
theorem mapM7 {ε α β : Type} {f : α → Except ε β} {x0 x1 x2 x3 x4 x5 x6 : α} {l : List β}
    (h : [x0, x1, x2, x3, x4, x5, x6].mapM f = .ok l) :
    ∃ q0 q1 q2 q3 q4 q5 q6, f x0 = .ok q0 ∧ f x1 = .ok q1 ∧ f x2 = .ok q2 ∧ f x3 = .ok q3 ∧
      f x4 = .ok q4 ∧ f x5 = .ok q5 ∧ f x6 = .ok q6 ∧ l = [q0, q1, q2, q3, q4, q5, q6] := by
  rw [List.mapM_cons] at h
  obtain ⟨q0, h0, h⟩ := exc_bind h
  obtain ⟨t0, h, e0⟩ := exc_bind h
  rw [List.mapM_cons] at h
  obtain ⟨q1, h1, h⟩ := exc_bind h
  obtain ⟨t1, h, e1⟩ := exc_bind h
  rw [List.mapM_cons] at h
  obtain ⟨q2, h2, h⟩ := exc_bind h
  obtain ⟨t2, h, e2⟩ := exc_bind h
  rw [List.mapM_cons] at h
  obtain ⟨q3, h3, h⟩ := exc_bind h
  obtain ⟨t3, h, e3⟩ := exc_bind h
  rw [List.mapM_cons] at h
  obtain ⟨q4, h4, h⟩ := exc_bind h
  obtain ⟨t4, h, e4⟩ := exc_bind h
  rw [List.mapM_cons] at h
  obtain ⟨q5, h5, h⟩ := exc_bind h
  obtain ⟨t5, h, e5⟩ := exc_bind h
  rw [List.mapM_cons] at h
  obtain ⟨q6, h6, h⟩ := exc_bind h
  obtain ⟨t6, h, e6⟩ := exc_bind h
  rw [List.mapM_nil] at h
  cases h
  cases e6
  cases e5
  cases e4
  cases e3
  cases e2
  cases e1
  cases e0
  exact ⟨q0, q1, q2, q3, q4, q5, q6, h0, h1, h2, h3, h4, h5, h6, rfl⟩

/-- Where `packChain` returns, it returns one entry a sending. -/
theorem packChain_len {s : Setting} {file : String} {chain : Nat} {smp : List (List SampleSize)}
    {d : ChainSends} {q : List (Codes × List (OracleShape × Nat))}
    (h : packChain s file chain smp d = .ok q) : q.length = d.sends.length := by
  unfold packChain at h
  dsimp only at h
  split at h
  swap
  · obtain ⟨_, e, _⟩ := exc_bind h
    cases e
  rename_i hl
  obtain ⟨_, _, h⟩ := exc_bind h
  rw [mapM_len _ _ _ h, List.length_zip, eq_of_beq hl, Nat.min_self]

/-! ## The rows, block by block -/

/-- The rows of one chain at its share. -/
def blockOf (d : ChainSends) (q : List (Codes × List (OracleShape × Nat))) : List SendRow :=
  (d.sends.zip q).map fun x =>
    ⟨d.file, d.chain, x.1.entry, x.1.label, d.codes, x.2.2,
      (x.1.sent.filter fun m => m.shape.answers == 0).map (·.shape)⟩

/-- **Where every share has one entry a sending, the rows are the chains' blocks in a row.** -/
theorem zip_blocks : ∀ (ds : List ChainSends) (qs : List (List (Codes × List (OracleShape × Nat)))),
    List.Forall₂ (fun d q => q.length = d.sends.length) ds qs →
    (((ds.flatMap fun c => c.sends.map fun s => (c, s)).zip qs.flatten).map fun x =>
      (⟨x.1.1.file, x.1.1.chain, x.1.2.entry, x.1.2.label, x.1.1.codes, x.2.2,
        (x.1.2.sent.filter fun m => m.shape.answers == 0).map (·.shape)⟩ : SendRow)) =
      ((ds.zip qs).map fun y => blockOf y.1 y.2).flatten
  | _, _, .nil => rfl
  | _, _, .cons (a := d) (b := q) (l₁ := ds) (l₂ := qs) hq t => by
    rw [List.flatMap_cons, List.flatten_cons, List.zip_append (by rw [List.length_map, hq]),
      List.map_append, zip_blocks ds qs t, List.zip_cons_cons, List.map_cons, List.flatten_cons]
    congr 1
    unfold blockOf
    rw [List.zip_map_left, List.map_map]
    rfl

/-- Of a block whose chain is not ("proof", 0) nothing is kept. -/
theorem firstRows_no {d : ChainSends} (q : List (Codes × List (OracleShape × Nat)))
    (h : (d.file == "proof" && d.chain == 0) = false) : P5T.firstRows (blockOf d q) = [] := by
  unfold P5T.firstRows blockOf
  rw [List.filter_eq_nil_iff]
  intro r hr
  obtain ⟨x, _, rfl⟩ := List.mem_map.1 hr
  rw [h]
  exact Bool.false_ne_true

/-- Of a block whose chain is ("proof", 0) all is kept. -/
theorem firstRows_yes {d : ChainSends} (q : List (Codes × List (OracleShape × Nat)))
    (h : (d.file == "proof" && d.chain == 0) = true) :
    P5T.firstRows (blockOf d q) = blockOf d q := by
  unfold P5T.firstRows blockOf
  rw [List.filter_eq_self]
  intro r hr
  obtain ⟨x, _, rfl⟩ := List.mem_map.1 hr
  exact h

theorem firstRows_append (a b : List SendRow) :
    P5T.firstRows (a ++ b) = P5T.firstRows a ++ P5T.firstRows b := by
  unfold P5T.firstRows
  rw [List.filter_append]

/-- A block's column of sampled shapes is its share's second column. -/
theorem sampled_block {d : ChainSends} {q : List (Codes × List (OracleShape × Nat))}
    (h : q.length = d.sends.length) : (blockOf d q).map (·.sampled) = q.map (·.2) := by
  unfold blockOf
  rw [List.map_map]
  have e : (d.sends.zip q).map Prod.snd = q := List.map_snd_zip (Nat.le_of_eq h)
  conv => rhs; rw [← e]
  rw [List.map_map]
  rfl

/-! ## The seven chains' names -/

/-- What one chain's maker returns bears the name that it was handed. -/
theorem one_tags {file : String} {ch : Nat} {codes : Codes} {b : Bool}
    {g g' : Except String PUnit} {m : Except String (List Sending)} {a : ChainSends}
    (h : (if b = true then
        g >>= fun _ => m >>= fun out => pure (⟨file, ch, codes, out⟩ : ChainSends)
      else g' >>= fun _ => m >>= fun out => pure (⟨file, ch, codes, out⟩ : ChainSends)) = .ok a) :
    a.file = file ∧ a.chain = ch := by
  split at h
  · obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨out, _, h⟩ := exc_bind h
    cases h
    exact ⟨rfl, rfl⟩
  · obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨out, _, h⟩ := exc_bind h
    cases h
    exact ⟨rfl, rfl⟩

/-- **Where the sendings are made they are seven, with these names, in this order.** -/
theorem sends_tags {c : Configured} {l : List ChainSends} (h : sendsFrom c = .ok l) :
    ∃ k0 k1 k2 e p0 p1 p2, l = [k0, k1, k2, e, p0, p1, p2] ∧
      (k0.file = "key" ∧ k0.chain = 0) ∧ (k1.file = "key" ∧ k1.chain = 1) ∧
      (k2.file = "key" ∧ k2.chain = 2) ∧ (e.file = "entry" ∧ e.chain = 0) ∧
      (p0.file = "proof" ∧ p0.chain = 0) ∧ (p1.file = "proof" ∧ p1.chain = 1) ∧
      (p2.file = "proof" ∧ p2.chain = 2) := by
  unfold sendsFrom at h
  dsimp only at h
  generalize c.key = K at h
  generalize c.proof = P at h
  split at h
  · obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, h0, h1, h2, h3, h4, h5, h6, rfl⟩ := mapM7 h
    exact ⟨a0, a1, a2, a3, a4, a5, a6, rfl, one_tags h0, one_tags h1, one_tags h2, one_tags h3,
      one_tags h4, one_tags h5, one_tags h6⟩
  · cases h

/-! ## The fifth block -/

/-- **THE FIRST PROOF CHAIN's ROWS ARE THE FIFTH BLOCK.** -/
theorem first_block {c : Configured} {o : List Nat} {n : Nat} {A : Nat → Arm} {R : List SendRow}
    (h : rowsFrom c o n A = .ok R)
    (hA : ∀ s ch, callsFrom c o n A = .ok (s, ch) → s = c.sized.set ∧
      ∃ a0 a1 a2 a3 a4 a5 a6, ch = [a0, a1, a2, a3, a4, a5, a6] ∧ a4.file = "proof" ∧
        a4.chain = 0 ∧ a4.calls.flatMap Call.sendSamples = samplesP0 c.sized.proof) :
    ∃ k0 k1 k2 e p0 p1 p2 q, sendsFrom c = .ok [k0, k1, k2, e, p0, p1, p2] ∧
      packChain c.sized.set "proof" 0 (samplesP0 c.sized.proof) p0 = .ok q ∧
      (P5T.firstRows R).map (·.sampled) = q.map (·.2) := by
  unfold rowsFrom at h
  obtain ⟨sends, hs, h⟩ := exc_bind h
  obtain ⟨pack, hp, h⟩ := exc_bind h
  obtain ⟨k0, k1, k2, e, p0, p1, p2, rfl, t0, t1, t2, t3, t4, t5, t6⟩ := sends_tags hs
  unfold packFrom at hp
  obtain ⟨⟨s, ch⟩, hc, hp⟩ := exc_bind hp
  obtain ⟨rfl, a0, a1, a2, a3, a4, a5, a6, rfl, f4, c4, s4⟩ := hA s ch hc
  dsimp only at hp
  obtain ⟨sends', hs', hp⟩ := exc_bind hp
  obtain rfl : [k0, k1, k2, e, p0, p1, p2] = sends' := Except.ok.inj (hs.symm.trans hs')
  obtain ⟨per, hper, hp⟩ := exc_bind hp
  cases hp
  rw [show List.zip [a0, a1, a2, a3, a4, a5, a6] [k0, k1, k2, e, p0, p1, p2] =
    [(a0, k0), (a1, k1), (a2, k2), (a3, e), (a4, p0), (a5, p1), (a6, p2)] from rfl] at hper
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, u0, u1, u2, u3, u4, u5, u6, rfl⟩ := mapM7 hper
  have g0 : packChain c.sized.set a0.file a0.chain (a0.calls.flatMap Call.sendSamples) k0 =
    .ok q0 := u0
  have g1 : packChain c.sized.set a1.file a1.chain (a1.calls.flatMap Call.sendSamples) k1 =
    .ok q1 := u1
  have g2 : packChain c.sized.set a2.file a2.chain (a2.calls.flatMap Call.sendSamples) k2 =
    .ok q2 := u2
  have g3 : packChain c.sized.set a3.file a3.chain (a3.calls.flatMap Call.sendSamples) e =
    .ok q3 := u3
  have g4 : packChain c.sized.set a4.file a4.chain (a4.calls.flatMap Call.sendSamples) p0 =
    .ok q4 := u4
  have g5 : packChain c.sized.set a5.file a5.chain (a5.calls.flatMap Call.sendSamples) p1 =
    .ok q5 := u5
  have g6 : packChain c.sized.set a6.file a6.chain (a6.calls.flatMap Call.sendSamples) p2 =
    .ok q6 := u6
  rw [f4, c4, s4] at g4
  refine ⟨k0, k1, k2, e, p0, p1, p2, q4, hs, g4, ?_⟩
  have F2 : List.Forall₂ (fun (d : ChainSends) (q : List (Codes × List (OracleShape × Nat))) =>
      q.length = d.sends.length) [k0, k1, k2, e, p0, p1, p2] [q0, q1, q2, q3, q4, q5, q6] :=
    .cons (packChain_len g0) (.cons (packChain_len g1) (.cons (packChain_len g2)
      (.cons (packChain_len g3) (.cons (packChain_len g4) (.cons (packChain_len g5)
        (.cons (packChain_len g6) .nil))))))
  dsimp only at h
  split at h
  swap
  · obtain ⟨_, e', _⟩ := exc_bind h
    cases e'
  obtain ⟨_, _, h⟩ := exc_bind h
  have hR : R = ((([k0, k1, k2, e, p0, p1, p2].flatMap fun c => c.sends.map fun s => (c, s)).zip
      [q0, q1, q2, q3, q4, q5, q6].flatten).map fun x =>
      (⟨x.1.1.file, x.1.1.chain, x.1.2.entry, x.1.2.label, x.1.1.codes, x.2.2,
        (x.1.2.sent.filter fun m => m.shape.answers == 0).map (·.shape)⟩ : SendRow)) :=
    (Except.ok.inj h).symm
  rw [hR, zip_blocks _ _ F2]
  simp only [List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.append_nil, firstRows_append]
  rw [firstRows_no q0 (by rw [t0.1, t0.2]; rfl), firstRows_no q1 (by rw [t1.1, t1.2]; rfl),
    firstRows_no q2 (by rw [t2.1, t2.2]; rfl), firstRows_no q3 (by rw [t3.1, t3.2]; rfl),
    firstRows_yes q4 (by rw [t4.1, t4.2]; rfl), firstRows_no q5 (by rw [t5.1, t5.2]; rfl),
    firstRows_no q6 (by rw [t6.1, t6.2]; rfl)]
  simp only [List.nil_append, List.append_nil]
  exact sampled_block (packChain_len g4)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.mapM_len
#print axioms VerifiableInference.Desc.LinkJoin.mapM7
#print axioms VerifiableInference.Desc.LinkJoin.packChain_len
#print axioms VerifiableInference.Desc.LinkJoin.zip_blocks
#print axioms VerifiableInference.Desc.LinkJoin.firstRows_no
#print axioms VerifiableInference.Desc.LinkJoin.firstRows_yes
#print axioms VerifiableInference.Desc.LinkJoin.firstRows_append
#print axioms VerifiableInference.Desc.LinkJoin.sampled_block
#print axioms VerifiableInference.Desc.LinkJoin.one_tags
#print axioms VerifiableInference.Desc.LinkJoin.sends_tags
#print axioms VerifiableInference.Desc.LinkJoin.first_block
