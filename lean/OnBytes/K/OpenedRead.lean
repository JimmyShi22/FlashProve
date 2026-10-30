-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/OpenedRead.lean: what one yes of the strict reader with stored tables says of what it
hands out, as one lemma.



OnBytes/TypedOracleCompiler/Run/StoredMain.lean's `stored_core` draws these facts inside its proof and hands none of
them on. Here that first half of its proof stands as a lemma of its own, in its words, so that what
speaks of the same reading can call it. For proofs only; the program does not import this file.

Main theorem.
 `read_parts`      if `Fmt.readChainX` at the hash over any function O has read o under S, S's own
                  part is within the limits of OnBytes/TypedOracleCompiler and the chain has random bytes: S is in
                  order; o has a run value R and the digest of S's parameter bytes; there is a list
                  rc, one member a round: the round as read without the stored tables' openings, and
                  these openings; o's rounds are rc's members joined; `LaxFacts` holds of the chain
                  without the stored tables' openings and the vertices met (`ownOut`); all tests of
                  work pass; all own openings walk to their roots; each round has as many draws as
                  its entry says; and every stored opening has `StoredFact`.

What is not claimed. Nothing on soundness; no probability; nothing on any hash: O is any function on
byte strings. That the reader reads any file.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.TypedOracleCompiler.Run.StoredMain

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
  TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open OnBytes.Tie (StoOK roundWithStoredOpenings StoredFact storedB_eq readX_stages foldX_facts partsFrom_le
  fullX_true)

/-- What one yes of the strict reader says of what it hands out. -/
theorem read_parts (S : _root_.Fmt.SpecX) (O : ByteArray → ByteArray)
    (hokb : ok (inFile S.base) = true) (hn : S.base.rand.isNone = false)
    (seen : _root_.Fmt.Seen) (b : ByteArray) (i : ℕ) (o : _root_.Fmt.ChainOut) (j : ℕ)
    (e : _root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO O) S seen b i = some (o, j)) :
    S.ok = true ∧
    ∃ (R rho0 : ByteArray)
      (rc : List (_root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut))),
      o.run = some R ∧
      o.pd = _root_.Fmt.HO O 169 0 1 _root_.Fmt.zero32 S.base.params ∧
      o.rounds.toList = rc.map roundWithStoredOpenings ∧
      LaxFacts (_root_.Fmt.HO O) (inFile S.base) (ownOut o.pd R rho0 o.rho rc) ∧
      passL (_root_.Fmt.HO O) S.base.rounds (rc.map fun p => stripR p.1)
        ⟨S.base.label, rho0, 0⟩ = true ∧
      rootsAll (_root_.Fmt.HO O) S.base.cfg R (rc.map fun p => stripR p.1) = true ∧
      List.Forall₂ (fun (x : _root_.Fmt.Round × List _root_.Fmt.Stored)
          (p : _root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)) =>
        p.1.drawn.poss.length = x.1.entry.poss) (S.base.rounds.zip S.stored) rc ∧
      List.Forall₂ (fun (ts : List _root_.Fmt.Stored)
          (p : _root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)) =>
        List.Forall₂ (StoredFact (_root_.Fmt.HO O) S.base.cfg S.base.statement p.1.drawn.poss) ts
          p.2) S.stored rc := by
  obtain ⟨hSok, x, i0, hd, s, hr, hst', hf, rfl, rfl⟩ :=
    readX_stages (_root_.Fmt.HO O) S seen b i o j e
  obtain ⟨rnd, rfl⟩ := rnd_some S.base b i x i0 hn hr
  obtain ⟨hdrun, rho0⟩ := hd
  obtain ⟨h32, hrun, hrho⟩ := startChain_some (_root_.Fmt.HO O) _ _ _ _ _ hst'
  obtain ⟨R, hR⟩ : ∃ R : ByteArray, hdrun = some R := ⟨_, hrun⟩
  subst hR
  have hown : ∀ r ∈ S.base.rounds.zip S.stored, ∀ x ∈ r.1.opens, ∃ n, x.2 = .own n :=
    fun r hr' => own_of_ok (inFile S.base) hokb r.1 (List.of_mem_zip hr').1
  obtain ⟨rc, g1, g2, g3, g4, g5⟩ := foldX_facts (_root_.Fmt.HO O) S.base.cfg S.base.statement
    S.base.plan
    R b (S.base.rounds.zip S.stored) _ s hown hf
  have hlen := specX_len S hSok
  have hfst : (S.base.rounds.zip S.stored).map (·.1) = S.base.rounds :=
    List.map_fst_zip (le_of_eq hlen.symm)
  have hsnd : (S.base.rounds.zip S.stored).map (·.2) = S.stored :=
    List.map_snd_zip (le_of_eq hlen)
  rw [hfst] at g2 g3
  have g1' : s.out.toList = rc.map roundWithStoredOpenings := by simpa using g1
  have ht : ((rc.map fun p => stripR p.1).toArray).toList = rc.map fun p => stripR p.1 := by simp
  refine ⟨hSok, R, rho0, rc, rfl, rfl, g1', ?_, g3, g4, g5.imp fun _ _ hh => hh.1, ?_⟩
  · refine ⟨rfl, ⟨rnd, h32, hrun⟩, ?_, ?_⟩
    · intro r hr'
      have hr2 : some r = some _ := hr'.symm.trans hrun
      rw [Option.some.inj hr2]
      exact hrho
    · show TraceL (_root_.Fmt.HO O) S.base.plan S.base.rounds
        ((rc.map fun p => stripR p.1).toArray).toList ⟨S.base.label, rho0, 0⟩ #[]
      rw [ht]
      exact g2
  · rw [← hsnd]
    exact List.forall₂_map_left_iff.2 (g5.imp fun _ _ hh => hh.2)

end TypedOracleCompiler.Run.PQ
