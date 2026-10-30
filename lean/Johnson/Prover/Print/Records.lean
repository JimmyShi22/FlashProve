-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Print/Records.lean: a typed record, written as the parsed files hold it (its answers
as triples of words: `trAns`, OnBytes/Flat/LinkSib.lean; its seeds: `seedsOf`,
Johnson/Prover/Print/Form.lean), comes back under the makers' `recOne` (OnBytes/K/ArmLetters.lean);
and the written lists are such as the readers and the judged rows take.

Main names (namespace `Johnson.Prover.Print`).
  `okE_of_okE`       the library's test "three words below the prime" on an element gives the bytes'
                     reader's condition on its triple
  `recOne_spell`, `wf_spell`   the two ends for every v, lg, s
  `recOne_seedsOf`   at the full size: recOne of the written answers and seeds is the record
  `wf_seedsOf`       at the full size, at every record: one seed, of 29 coordinates, which the
                     bytes' reader takes; 2^v * 1 answers

Limits. Equations on a record's spelling. Nothing says that a record is any committer's, nor that
the answers' words are below the prime. No file, no prover, no verifier.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Print.Form
import OnBytes.Field.ExtEq
import Fmt.ParsedReadLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Print

open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open _root_.Run
open _root_.Iop (Dig)
open TypedOracleCompiler.Slice (anT)
open OnBytes.Prover.Print (okSeed map_ofTriple_triple map_triple_ofTriple)
open OnBytes.K.IdTable (spellSeedL seedOfC_spell shaped_spell)

/-- The library's test on an element gives the bytes' reader's condition on its triple. -/
theorem okE_of_okE (x : OnBytes.E) (h : OnBytes.okE x = true) : Carrier.okE x.triple :=
  Fmt.lt_of_okE .two x.triple ((OnBytes.okE_triple x).symm.trans h)

theorem map_seed_back : ∀ l : List (List OnBytes.E × OnBytes.E),
    ((l.map fun y => (y.1.map OnBytes.E.triple, y.2.triple)).map
      fun y => (y.1.map OnBytes.E.ofTriple, OnBytes.E.ofTriple y.2)) = l
  | [] => rfl
  | y :: l => by
    show ((y.1.map OnBytes.E.triple).map OnBytes.E.ofTriple, OnBytes.E.ofTriple y.2.triple) ::
      ((l.map fun y => (y.1.map OnBytes.E.triple, y.2.triple)).map
        fun y => (y.1.map OnBytes.E.ofTriple, OnBytes.E.ofTriple y.2)) = y :: l
    rw [map_ofTriple_triple, map_seed_back l]
    rfl

/-- **The record comes back**, for every v, lg, s. -/
theorem recOne_spell (v lg s : ℕ) (root : ByteArray) (rcd : RecP NZ v lg s) :
    OnBytes.K.recOne v lg s ⟨root, (trAns rcd.2).map OnBytes.E.ofTriple⟩
      (((spellSeedL lg s rcd.1).map fun y => (y.1.map OnBytes.E.triple, y.2.triple)).map
        fun y => (y.1.map OnBytes.E.ofTriple, OnBytes.E.ofTriple y.2)) = rcd := by
  unfold OnBytes.K.recOne
  rw [map_seed_back, seedOfC_spell]
  show (rcd.1, anT v s (((trAns rcd.2).map OnBytes.E.ofTriple).map OnBytes.E.triple)) = rcd
  rw [map_triple_ofTriple, anT_trAns]

/-- **The written lists**, for every v, lg, s with lg below 2^64. -/
theorem wf_spell (v lg s : ℕ) (hlg : lg < 2 ^ 64) (rcd : RecP NZ v lg s) :
    ((spellSeedL lg s rcd.1).map fun y => (y.1.map OnBytes.E.triple, y.2.triple)).length = s ∧
    (∀ y ∈ (spellSeedL lg s rcd.1).map fun y => (y.1.map OnBytes.E.triple, y.2.triple),
      y.1.length = lg ∧ okSeed y) ∧ (trAns rcd.2).length = 2 ^ v * s := by
  have hsh := shaped_spell lg s rcd.1
  have hlen : ((spellSeedL lg s rcd.1).map
      fun y => (y.1.map OnBytes.E.triple, y.2.triple)).length = s := by
    rw [List.length_map]
    exact hsh.1
  refine ⟨hlen, ?_, List.length_ofFn⟩
  intro y hy
  obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hy
  obtain ⟨hl, hok⟩ := hsh.2 y' hy'
  have hl' : (y'.1.map OnBytes.E.triple).length = lg := by
    rw [List.length_map]
    exact hl
  have hlt : (y'.1.map OnBytes.E.triple).length < 2 ^ 64 := by
    rw [hl']
    exact hlg
  refine ⟨hl', hlt, ?_, okE_of_okE _ hok.2.1⟩
  intro e he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
  exact okE_of_okE x (hok.1 x hx)

/-- **The record comes back**, at the full size. -/
theorem recOne_seedsOf :
  ∀ (root : ByteArray) (rcd : RecFull),
    OnBytes.K.recOne frS.P.v 29 1 ⟨root, (trAns rcd.2).map OnBytes.E.ofTriple⟩
      ((seedsOf rcd).map fun y => (y.1.map OnBytes.E.ofTriple, OnBytes.E.ofTriple y.2)) = rcd :=
  fun root rcd => recOne_spell frS.P.v 29 1 root rcd

/-- **The seeds' file is well formed, at every record**, at the full size. -/
theorem wf_seedsOf :
  ∀ rcd : RecFull, (seedsOf rcd).length = 1 ∧
    (∀ y ∈ seedsOf rcd, y.1.length = 29 ∧ okSeed y) ∧ (trAns rcd.2).length = 2 ^ frS.P.v * 1 :=
  fun rcd => wf_spell frS.P.v 29 1 (by omega) rcd

end Johnson.Prover.Print
