-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Rows/TailCut.lean:
THE TAIL OF packFrom | rowsFrom (Tail.lean: tailFrom) CUT BY CHAINS. Definitions and theorems. A law
file; no running text imports it. Why. «The tail returns at the written values» is one premise of
rows_of_partsL (Twin.lean); as one closed fact it is costly for Lean's kernel (see TailHome.lean).
The tail reads the sendings (sendsFrom) and then works chain by chain; so, where the sendings are
known as seven chains, it returns if each of the seven passes.
  `sendingTail`, `chainTail`   tailFrom's lines at one sending and at one chain, by name.
                    `chainTailB`: it returns.
  `tailFrom_cut`   tailFrom with chainTail in its mapM: by rfl.
  `chainTail_len`  what a chain returns has as many entries as the chain has sendings.
  `tail_of_seven`  MAIN: sendsFrom c = .ok [d0 … d6] · chainTailB s ci di = true (seven) ⊢ the tail
                    returns at [c0 … c6].
Limits. NO CLOSED FACT IS HERE: every premise of tail_of_seven is owed. sendingTail and chainTail
will have to be turned with tailFrom; tailFrom_cut would then fail. Nothing on what a radius means.
Nothing on soundness or on hiding.

-/
import Johnson.AtFull.Rows.Tail

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom
open VerifiableInference.Number (sendsFrom)

/-- What the tail does at one sending of a chain. -/
def sendingTail (s : Setting) (file : String) (chain : Nat) (codes : Codes) (o : List SampleSize)
    (x : Sending) : Except String (Codes × List (OracleShape × Nat)) := do
  let at_ := s!"{file} {chain}, entry {x.entry} ({x.label})"
  let sampled := (x.sent.filter fun m => 0 < m.shape.answers).map (·.shape)
  let o' :=
    if o.length == sampled.length then o
    else if o.length == 1 then List.replicate sampled.length (o.headD ⟨0, []⟩) else []
  unless o'.length == sampled.length do
    throw s!"{at_}: the sampled messages and the samples are not as many"
  let l ← (sampled.zip o').mapM fun (sh, sm) => do
    pure (sh, ← radiusFor s codes at_ sh sm)
  unless x.behind.answers == l.length * s.samples do
    throw s!"{at_}: (p3) the entry behind takes in another number of answers"
  unless x.seed.drawE == s.samples * (Johnson.Pack.bMax codes l + 1) do
    throw s!"{at_}: (p4) the entry draws another number of elements"
  pure (codes, l)

/-- What the tail does at one chain. -/
def chainTail (s : Setting) (c : Johnson.G.Chain) (d : ChainSends) :
    Except String (List (Codes × List (OracleShape × Nat))) := do
  let smp := c.calls.flatMap Call.sendSamples
  unless smp.length == d.sends.length do
    throw s!"{c.file} {c.chain}: the calls and the list have not as many sendings"
  (smp.zip d.sends).mapM fun (o, x) => sendingTail s c.file c.chain d.codes o x

/-- It returns. -/
def chainTailB (s : Setting) (c : Johnson.G.Chain) (d : ChainSends) : Bool :=
  (chainTail s c d).toOption.isSome

/-- tailFrom, with chainTail in its mapM. -/
theorem tailFrom_cut (c : Configured) (s : Setting) (chains : List Johnson.G.Chain) :
    tailFrom c s chains = (do
      let sends ← sendsFrom c
      let pack ← (do
        let sends ← sendsFrom c
        let per ← (chains.zip sends).mapM fun cd => chainTail s cd.1 cd.2
        pure per.flatten : Except String (List (Codes × List (OracleShape × Nat))))
      let flat := sends.flatMap fun c => c.sends.map fun s => (c, s)
      unless flat.length == pack.length do throw "the two lists have not as many sendings"
      pure ((flat.zip pack).map fun ((c, s), p) =>
        ⟨c.file, c.chain, s.entry, s.label, c.codes, p.2,
          (s.sent.filter fun m => m.shape.answers == 0).map (·.shape)⟩)) := rfl

theorem mapM_len_ok {ε α β : Type} {f : α → Except ε β} :
    ∀ {l : List α} {r : List β}, l.mapM f = .ok r → r.length = l.length
  | [], r, h => by
    cases h
    rfl
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := exc_bind h
    obtain ⟨t, ht, h⟩ := exc_bind h
    cases h
    rw [List.length_cons, List.length_cons, mapM_len_ok ht]

/-- What a chain returns has as many entries as the chain has sendings. -/
theorem chainTail_len {s : Setting} {c : Johnson.G.Chain} {d : ChainSends}
    {l : List (Codes × List (OracleShape × Nat))} (h : chainTail s c d = .ok l) :
    l.length = d.sends.length := by
  unfold chainTail at h
  dsimp only at h
  by_cases e : ((c.calls.flatMap Call.sendSamples).length == d.sends.length) = true
  · simp only [e, bind, Except.bind, pure, Except.pure] at h
    have := mapM_len_ok h
    rw [this, List.length_zip, beq_iff_eq.1 e, Nat.min_self]
  · simp only [e, bind, Except.bind] at h
    cases h

theorem ok_of_B {s : Setting} {c : Johnson.G.Chain} {d : ChainSends} (h : chainTailB s c d = true) :
    ∃ l, chainTail s c d = .ok l ∧ l.length = d.sends.length := by
  unfold chainTailB at h
  cases e : chainTail s c d with
  | error m =>
    rw [e] at h
    cases h
  | ok l => exact ⟨l, rfl, chainTail_len e⟩

/-- **The tail returns where the sendings are seven chains and each chain passes.** -/
theorem tail_of_seven {c : Configured} {s : Setting} {c0 c1 c2 c3 c4 c5 c6 : Johnson.G.Chain}
    {d0 d1 d2 d3 d4 d5 d6 : ChainSends} (hs : sendsFrom c = .ok [d0, d1, d2, d3, d4, d5, d6])
    (t0 : chainTailB s c0 d0 = true) (t1 : chainTailB s c1 d1 = true)
    (t2 : chainTailB s c2 d2 = true) (t3 : chainTailB s c3 d3 = true)
    (t4 : chainTailB s c4 d4 = true) (t5 : chainTailB s c5 d5 = true)
    (t6 : chainTailB s c6 d6 = true) :
    (tailFrom c s [c0, c1, c2, c3, c4, c5, c6]).toOption.isSome = true := by
  obtain ⟨l0, e0, n0⟩ := ok_of_B t0
  obtain ⟨l1, e1, n1⟩ := ok_of_B t1
  obtain ⟨l2, e2, n2⟩ := ok_of_B t2
  obtain ⟨l3, e3, n3⟩ := ok_of_B t3
  obtain ⟨l4, e4, n4⟩ := ok_of_B t4
  obtain ⟨l5, e5, n5⟩ := ok_of_B t5
  obtain ⟨l6, e6, n6⟩ := ok_of_B t6
  rw [tailFrom_cut, hs]
  simp only [bind, Except.bind, List.zip_cons_cons, List.zip_nil_right, List.mapM_cons,
    List.mapM_nil, e0, e1, e2, e3, e4, e5, e6, pure, Except.pure]
  have hl : ((([d0, d1, d2, d3, d4, d5, d6] : List ChainSends).flatMap fun c =>
        c.sends.map fun s => (c, s)).length ==
      ([l0, l1, l2, l3, l4, l5, l6] : List _).flatten.length) = true := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.flatten_cons, List.flatten_nil,
      List.length_append, List.length_map, List.length_nil, n0, n1, n2, n3, n4, n5, n6,
      beq_self_eq_true]
  simp only [hl]
  rfl

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.tailFrom_cut
#print axioms VerifiableInference.Desc.LinkJoin.mapM_len_ok
#print axioms VerifiableInference.Desc.LinkJoin.chainTail_len
#print axioms VerifiableInference.Desc.LinkJoin.ok_of_B
#print axioms VerifiableInference.Desc.LinkJoin.tail_of_seven
