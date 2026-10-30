-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/LaxGround.lean: what `accepts_allRoots_once` (OnBytes/TypedOracleCompiler/Run/AllRoots.lean) asks at
each pair of roots, shown at the entry file from the exit code 0: the strict reader's equation, the
decision's yes on the view, the roots in the statement's items, and the bound on the statement.

That theorem fixes a description S0 and a function `stm` from two roots to a statement before the
roots are chosen. Under a record the statement of the entry's chain holds both tables' answers. So
here `stm` has the answers written in (`stmAt`), and S0 is the program's own description at an empty
statement (`specAt`).

Main names:
  `specAt G c`, `stmAt a0 a1`: S0 and `stm`.
  `specAt_with`: S0 with the statement at two tables put in is the program's own description at
    these tables. By unfolding.
  `specAt_xd`: S0's base and stored openings are those of `entryXD G c`. By unfolding.
  `ground`: under `PortYesAt` and `G.SaysLines`: both roots have 32 bytes; the strict reader at the
    format's own oracle reads, from some byte of the entry file, what `Entry.read` returned; the
    program's decision at the two keys says yes on its view; each stored table that S0 lists has its
    root in the statement's item 0 or 1.

  `stmAt_size`: the statement's length, from the lengths of the roots and the numbers of answers.
  `ground_bounds`: under the same hypotheses: the parameter bytes are in the domain of the call that
    hashes them; each table has fewer than 2^32 answers; and at these answers the statement at any
    two roots of 32 bytes is within the hash's bound.

Limits: values alone. Nothing on soundness; no probability. The side conditions of
`accepts_allRoots_once` that hang on the ground alone are not here.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Left.Conv
import OnBytes.TypedOracleCompiler.Slice.EntryDesc
import Run.PageXStmSize

set_option autoImplicit false

namespace OnBytes.K.Left
open OnBytes.Tie
open TypedOracleCompiler.Slice

/-- The program's own description of the entry's chain at G's parameters, with c for the digest, at
G's rounds and an empty statement. -/
def specAt (G : EntryGround) (c : ByteArray) : Fmt.SpecX :=
  Params.entrySpecOf (linkAtCfg G.q c) G.rs ByteArray.empty

/-- The statement on two tables as a function of their roots, with their answers written in. -/
def stmAt (a0 a1 : List E) (r0 r1 : ByteArray) : ByteArray :=
  Params.Link.statement ⟨r0, a0⟩ ⟨r1, a1⟩

/-- With the statement at two tables put in, it is the program's own description at these tables. -/
theorem specAt_with (G : EntryGround) (c : ByteArray) (first further : Params.TableName) :
    TypedOracleCompiler.Run.PQ.withStatement (specAt G c)
        (stmAt first.answers further.answers first.root further.root) =
      Params.entrySpecOf (linkAtCfg G.q c) G.rs (Params.Link.statement first further) := rfl

/-- Its base and stored openings are those of `entryXD G c`. -/
theorem specAt_xd (G : EntryGround) (c : ByteArray) :
    (specAt G c).base = (entryXD G c).base ∧ (specAt G c).stored = (entryXD G c).stored :=
  ⟨rfl, rfl⟩

/-- What is asked at each pair of roots, from the exit code 0. -/
theorem ground (G : EntryGround) (hA : (G.q.link.table.answers == 0) = false)
    {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) (hl : G.SaysLines F.pol) :
    ∃ (r : Entry.EntryRead) (l0 l1 : List (List E × E)) (i : ℕ),
      Entry.read (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL])) table F.ent =
        .ok r ∧ r.further = further ∧
      seedsUnder recordSeeds (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL]))
        table = some l0 ∧
      seedsUnder recordSeeds (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL]))
        further = some l1 ∧
      table.root.size = 32 ∧ further.root.size = 32 ∧
      Fmt.readChainX (m := Id) (Fmt.HO Fmt.oracle)
        (TypedOracleCompiler.Run.PQ.withStatement (specAt G (Params.configurationDigest [F.pol, F.lay, F.KL]))
          (stmAt table.answers further.answers table.root further.root))
        Session.start.seen F.ent i = some (r.chain.out, r.chain.next) ∧
      entryDecR (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL]))
        { item := 0, record := table.answers.toArray, seeds := l0.map fun x => ⟨x.1, x.2⟩ }
        { item := 1, record := further.answers.toArray, seeds := l1.map fun x => ⟨x.1, x.2⟩ }
        (Fmt.viewX
          (TypedOracleCompiler.Run.PQ.withStatement (specAt G (Params.configurationDigest [F.pol, F.lay, F.KL]))
            (stmAt table.answers further.answers table.root further.root)) r.chain.out) = true ∧
      ∀ t ∈ (specAt G (Params.configurationDigest [F.pol, F.lay, F.KL])).stored.flatten,
        Fmt.itemRoot (stmAt table.answers further.answers table.root further.root) t.item =
          some (if t.item == 1 then further.root else table.root) := by
  obtain ⟨-, -, -, -, -, h0, hb⟩ := entry_facts h
  have hc32 := Params.configurationDigest_size [F.pol, F.lay, F.KL]
  obtain ⟨r, l0, l1, hr, hf, a0, a1, hblk, hd⟩ := read_at G hA h hl
  obtain ⟨j, S, s', hS, hrd, h32⟩ := entry_read_spec _ table F.ent r hr
  obtain ⟨-, rs', hrs', eS⟩ := Params.entrySpec_eq_all hS
  obtain rfl : G.rs = rs' := Option.some.inj ((G.rounds_at _).symm.trans hrs')
  rw [hf] at hS eS h32
  have hok := readX_ok Fmt.formatHash _ _ F.ent j _ (readIn_read _ F.ent j _ s' r.chain hrd).1
  have hwi : withinX S = true := by
    rw [eS]
    exact G.within_at _ hc32 _ (by rw [← eS]; exact specX_base _ hok)
  have hsm := smallFX_of_withinX _ hok hwi F.ent hb
  obtain ⟨e2, e3⟩ := readInAt_read _ _ _ _ _ _ _ ((readInAt_oracle S F.ent j _ hsm).trans hrd)
  have hB : S.base.statement.size + 88 ≤ 2 ^ 32 - 144 := by
    have hsm' := hsm
    unfold smallFX Run.smallF Run.smallB at hsm'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hsm'
    exact hsm'.1.1.1.1.1.2
  have hroot := (entrySpec_roots _ _ _ _ _ hS).2 hwi (by omega)
  rw [hblk, e3] at hd
  subst eS
  exact ⟨r, l0, l1, j, hr, hf, a0, a1, h0, h32, e2, hd, hroot⟩

/-- The statement's length. -/
theorem stmAt_size (a0 a1 : List E) (r0 r1 : ByteArray) :
    (stmAt a0 a1 r0 r1).size = 96 + r0.size + r1.size + 24 * a0.length + 24 * a1.length := by
  have e0 : (Fmt.ascii "the first table").size = 15 := rfl
  have e1 : (Fmt.ascii "the further table").size = 17 := rfl
  unfold stmAt Params.Link.statement Fmt.tableItem Fmt.item Fmt.textS Fmt.text
  simp only [ByteArray.size_append, Fmt.size_u64n, Run.PQ.size_listExt, List.length_map, e0, e1]
  omega

/-- Parameter bytes within the hash's bound are in the domain of the call that hashes them. -/
theorem hDom_params (b : ByteArray) (h : b.size ≤ 2 ^ 32 - 144) :
    Fmt.hDom 169 0 1 Fmt.zero32 b = true := by
  unfold Fmt.hDom
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨by decide, by decide⟩, by decide⟩, by decide⟩, h⟩, by decide⟩, by decide⟩, rfl⟩

/-- The bounds, from the exit code 0. -/
theorem ground_bounds (G : EntryGround) (hA : (G.q.link.table.answers == 0) = false)
    {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) (hl : G.SaysLines F.pol) :
    Fmt.hDom 169 0 1 Fmt.zero32
        (entryXD G (Params.configurationDigest [F.pol, F.lay, F.KL])).base.params = true ∧
      table.answers.length < 2 ^ 32 ∧ further.answers.length < 2 ^ 32 ∧
      ∀ a b : ByteArray, a.size = 32 → b.size = 32 →
        (stmAt table.answers further.answers a b).size + 88 ≤ 2 ^ 32 - 144 := by
  obtain ⟨-, -, -, -, -, h0, hb⟩ := entry_facts h
  have hc32 := Params.configurationDigest_size [F.pol, F.lay, F.KL]
  obtain ⟨r, -, -, hr, hf, -, -, -, -⟩ := read_at G hA h hl
  obtain ⟨j, S, s', hS, hrd, h32⟩ := entry_read_spec _ table F.ent r hr
  obtain ⟨-, rs', hrs', eS⟩ := Params.entrySpec_eq_all hS
  obtain rfl : G.rs = rs' := Option.some.inj ((G.rounds_at _).symm.trans hrs')
  rw [hf] at eS h32
  have hok := readX_ok Fmt.formatHash _ _ F.ent j _ (readIn_read _ F.ent j _ s' r.chain hrd).1
  have hwi : withinX S = true := by
    rw [eS]
    exact G.within_at _ hc32 _ (by rw [← eS]; exact specX_base _ hok)
  have hsm := smallFX_of_withinX _ hok hwi F.ent hb
  unfold smallFX Run.smallF Run.smallB at hsm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hsm
  have hP : S.base.params.size ≤ 2 ^ 32 - 144 := hsm.1.1.1.1.1.1
  have hB : S.base.statement.size + 88 ≤ 2 ^ 32 - 144 := hsm.1.1.1.1.1.2
  subst eS
  have hB' : (stmAt table.answers further.answers table.root further.root).size + 88 ≤
      2 ^ 32 - 144 := hB
  rw [stmAt_size, h0, h32] at hB'
  refine ⟨hDom_params _ hP, by omega, by omega, fun a b ha hb' => ?_⟩
  rw [stmAt_size, ha, hb']
  exact hB'

end OnBytes.K.Left
