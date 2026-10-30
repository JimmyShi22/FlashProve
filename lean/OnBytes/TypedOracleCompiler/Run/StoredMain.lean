-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/StoredMain.lean: what the strict reader with stored tables has read, the sibling's
compiled verifier accepts, at the family `famXPd`, if the decision does.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

After OnBytes/Tie/StoredMain.lean (16 declarations, 434 lines), up to its `stored_core`. CUT
AND TURNED BY PROGRAM. OnBytes/TypedOracleCompiler/Run/StoredTop.lean (`verifyX_true`) has the verifier's yes under
hypotheses on what was read; here these are shown of what `Fmt.readChainX` hands out.

WHAT IT IMPORTS: the sibling alone (StoredTop.lean, PageXTop.lean), and through it the seven
files of OnBytes/Tie/ that stand under StoredTop.lean. The original imports
OnBytes/Tie/Session.lean, with which the files of OnBytes/Chain/ and four of OnBytes/Hash/ come in;
up to `stored_core` it uses of them `rnd_some` and `specX_len`, which are said again in
OnBytes/TypedOracleCompiler/Run/PageXRead.lean.

AS TEXT, but for `_root_.` before `Fmt.` and some line breaks (5). `ownOut`, `forall2_and_left`,
`specX_parts`, `specX_shape`, `stoOK_of`.
TURNED (1).
 `stored_core`      at every pd: `hpd` says that O's hash gives pd as the digest of the parameter
                    bytes, where the original asks that it gives the format's; the verifier's
                    embeddings of bodies are `embS` and `B.embE`; `hi` and `hns` are asked.
SAID ELSEWHERE OVER THE SIBLING (3): `xdOf` (PageXTop.lean, with `inFile` of
OnBytes/Tie/Limits.lean); `exists_zip_left`, `specX_round` (PageXRead.lean).
NOT SAID (7): `withinX`, `within_of_withinX`, `smallFX_of_withinX`, `CompiledAcceptsX`, `stored_VX`,
`stored_compiled`, `readInX_compiled`: what stands behind `stored_core` in the original: the passage
to the format's own hash and to the library's function `VX` on files.

WHAT IS NOT SAID. ONE DIRECTION: what was read is accepted. That the reader reads any file. That any
description meets `XD.ok`, or any bodies `hi` and `hns`. That the two roots are the right ones.
Nothing on soundness; no probability; nothing on any hash: O is any function on byte strings with
answers of 32 bytes.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.StoredTop
import OnBytes.TypedOracleCompiler.Run.PageXTop

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
  TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open OnBytes.Tie (StoOK roundWithStoredOpenings StoredFact storedB_eq readX_stages foldX_facts partsFrom_le
  fullX_true)

/-- A chain as read, without the stored tables' openings and without the vertices met. -/
def ownOut (pd R rho0 rho : ByteArray)
    (rc : List (_root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut))) :
    _root_.Fmt.ChainOut :=
  ⟨pd, some R, rho0, rho, [], (rc.map fun p => stripR p.1).toArray⟩


/-- If R relates two lists and P holds on the first, "R and P" relates them. -/
theorem forall2_and_left {α β : Type} {R : α → β → Prop} {P : α → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → (∀ x ∈ l1, P x) →
      List.Forall₂ (fun x y => R x y ∧ P x) l1 l2
  | _, _, .nil, _ => .nil
  | _, _, .cons h t, hp =>
    .cons ⟨h, hp _ List.mem_cons_self⟩
      (forall2_and_left t fun x hx => hp x (List.mem_cons_of_mem _ hx))


section
variable (S : _root_.Fmt.SpecX) (hS : S.ok = true)

include hS in
/-- The parts of a round's draws end within the round's number of draws. -/
theorem specX_parts : ∀ x ∈ S.base.rounds.zip S.stored, ∀ t ∈ x.2,
    t.lo + t.count ≤ x.1.entry.poss := by
  intro x hx t ht
  have h := specX_round S hS x hx
  unfold _root_.Fmt.storedOk at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · rw [List.isEmpty_iff.1 h] at ht
    cases ht
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact partsFrom_le x.2 0 _ h.1.2 t ht

include hS in
/-- A stored table's tree is a stored tree with the number 0. -/
theorem specX_shape : ∀ t ∈ S.stored.flatten, t.sh.stored = true ∧ t.sh.tree = 0 := by
  intro t ht
  obtain ⟨ts, hts, htt⟩ := List.mem_flatten.1 ht
  obtain ⟨r, hr⟩ := exists_zip_left S.base.rounds S.stored ts hts (le_of_eq (specX_len S hS))
  have h := specX_round S hS (r, ts) hr
  unfold _root_.Fmt.storedOk at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · have hE : ts = [] := List.isEmpty_iff.1 h
    rw [hE] at htt
    cases htt
  · simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
    have := h.2 t htt
    exact ⟨this.1.1.1.1.1.1.1.1, this.1.1.1.2⟩


end

section
variable (S : _root_.Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray) (dec : View → Bool)
  (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32)

/-- `StoredFact` of each table's opening in rc gives `StoOK` of o's stored openings, if o is rc with
these joined in, S is in order, hD holds (one depth, the plan's salts), each table is opened at most
once and the items hold the roots. -/
theorem stoOK_of (r0 r1 : ByteArray) (hS : S.ok = true) (o : _root_.Fmt.ChainOut)
    (rc : List (_root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)))
    (ho : o.rounds.toList = rc.map roundWithStoredOpenings)
    (hF : List.Forall₂ (fun (ts : List _root_.Fmt.Stored)
        (p : _root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)) =>
      List.Forall₂ (StoredFact (_root_.Fmt.HO O) S.base.cfg S.base.statement p.1.drawn.poss) ts p.2)
      S.stored rc)
    (hD : ∀ s ∈ S.stored.flatten, s.sh.a = (xdOf S stm).a ∧ s.salt = S.base.plan.salt)
    (honce : (S.stored.flatten.map (·.item == 1)).Nodup)
    (hroot : ∀ t ∈ S.stored.flatten,
      _root_.Fmt.itemRoot S.base.statement t.item = some (if t.item == 1 then r1 else r0)) :
    StoOK O S.base.cfg (xdOf S stm).a S.base.plan.salt r0 r1 (storedB (xdOf S stm).xs o) := by
  have hl : List.Forall₂ (fun (ts : List _root_.Fmt.Stored)
      (p : _root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)) =>
        ts.length = p.2.length)
      S.stored rc := hF.imp fun _ _ hh => hh.length_eq
  have key : ∀ e ∈ storedB (xdOf S stm).xs o, ∃ (t : _root_.Fmt.Stored)
      (z : _root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut) (poss : List ℕ), t ∈ S.stored.flatten ∧
      StoredFact (_root_.Fmt.HO O) S.base.cfg S.base.statement poss t z ∧
      e = (t.item == 1, z.1.W, obOf z) := by
    intro e he
    rw [xs_eq, show (xdOf S stm).stored = S.stored from rfl, storedB_eq S.stored o rc ho hl] at he
    obtain ⟨tp, htp, he'⟩ := List.mem_flatMap.1 he
    obtain ⟨tz, htz, rfl⟩ := List.mem_map.1 he'
    have h1 := (List.forall₂_iff_zip.1 hF).2 (show (tp.1, tp.2) ∈ _ from htp)
    have h2 := (List.forall₂_iff_zip.1 h1).2 (show (tz.1, tz.2) ∈ _ from htz)
    exact ⟨tz.1, tz.2, _, List.mem_flatten.2 ⟨tp.1, (List.of_mem_zip htp).1,
      (List.of_mem_zip htz).1⟩, h2, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [sto_keys (_root_.Fmt.HO O) (xdOf S stm) o rc ho hF]
    exact honce
  · intro e he
    obtain ⟨t, z, poss, ht, F, rfl⟩ := key e he
    have := F.okb
    rw [(hD t ht).2] at this
    show (⟨z.1.a, z.2.1, z.2.2.cols, z.2.2.salts, z.2.2.given⟩ : OpenB).ok S.base.plan.salt z.1.W
      = true
    rw [F.sh]
    exact this
  · intro e he
    obtain ⟨t, z, poss, ht, F, rfl⟩ := key e he
    show z.1.a = _
    rw [F.sh]
    exact (hD t ht).1
  · intro e he
    obtain ⟨t, z, poss, ht, F, rfl⟩ := key e he
    exact (WalkTie.listOK_spec _ _ F.okl).1
  · intro e he
    obtain ⟨t, z, poss, ht, F, rfl⟩ := key e he
    have hw := F.walk
    have hr := (F.root.symm.trans (hroot t ht))
    obtain ⟨hs1, hs2⟩ := specX_shape S hS t ht
    have hsh : t.sh = ⟨(xdOf S stm).a, z.1.W, true, 0⟩ := by
      rw [F.sh, ← (hD t ht).1, ← hs1, ← hs2]
    rw [hsh] at hw
    exact hw.trans (Option.some.inj hr)

variable {Bd : Type} (B : BodyD Bd) (pd : ByteArray)
  (embS : (p : OPos (Twin.up (SOf (xdOf S stm).C (xdOf S stm).ds))) →
    OSym (Twin.up (SOf (xdOf S stm).C (xdOf S stm).ds)) p → Bd)

include hO in
/-- If the strict reader, at the hash that O induces, has read a chain that opens stored tables
and the decision is yes, the sibling's typing gives a typed string and the evaluable form of the
sibling's compiled verifier accepts it, at `famXPd`. O is any function on byte strings with
answers of 32 bytes; pd is what its hash gives as the digest of the parameter bytes (`hpd`). The
other hypotheses: r0 and r1 have 32 bytes; the description is within the sibling's limits (`XD.ok`,
the random bytes counted as standing in the file); the chain has random bytes; each table is opened
at most once; the statement is `stm r0 r1` and its items hold the roots; the body of every own
symbol is spelled as the format spells its leaf (hi) and is no stored symbol (hns). One direction.
Nothing on soundness. -/
theorem stored_core (r0 r1 : ByteArray) (h0 : r0.size = 32) (h1 : r1.size = 32)
    (hok : (xdOf S stm).ok = true) (hn : S.base.rand.isNone = false)
    (honce : (S.stored.flatten.map (·.item == 1)).Nodup)
    (hst : S.base.statement = stm r0 r1)
    (hroot : ∀ t ∈ S.stored.flatten,
      _root_.Fmt.itemRoot S.base.statement t.item = some (if t.item == 1 then r1 else r0))
    (hpd : _root_.Fmt.HO O 169 0 1 _root_.Fmt.zero32 S.base.params = pd)
    (hi : ∀ p a, B.own (embS (.inr p) a) =
      some (leafSL (xdOf S stm).C S.base.plan.salt (xdOf S stm).ds ⟨p, a⟩))
    (hns : ∀ p a, B.getE (embS (.inr p) a) = none)
    (seen : _root_.Fmt.Seen) (b : ByteArray) (i : ℕ) (o : _root_.Fmt.ChainOut) (j : ℕ)
    (e : _root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO O) S seen b i = some (o, j))
    (hdec : dec (_root_.Fmt.viewX S o) = true) :
    ∃ π, toBPrfX S.base.plan.salt S.base.cfg (xdOf S stm).C (xdOf S stm).ds (xdOf S stm).a
        (xdOf S stm).xs dec o = some π ∧
      verifyP (fun _ => (xdOf S stm).L Bd dec)
        (famXPd B (xdOf S stm) dec pd O ((xdOf S stm).K + 1)) id none
        (256 + 8 * S.base.plan.salt) 256 .link
        (skeletonOverBothExternalStrings (xdOf S stm).C (xdOf S stm).ds (xdOf S stm).a (xdOf S stm).xs dec)
        (wqX (xdOf S stm).C (xdOf S stm).K (chalP S.base.plan.field (xdOf S stm).K)
          (xdOf S stm).ds (xdOf S stm).a (xdOf S stm).xs dec)
        embS
        (embPX Bd (xdOf S stm).C (xdOf S stm).ds (xdOf S stm).a (xdOf S stm).xs dec
          (fun _ _ p => (p.val, [])) (fun _ => some ()))
        (fun _ => none) B.embE 0 [bytesToDig r0, bytesToDig r1] () π = true := by
  have hok' := hok
  unfold XD.ok at hok'
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at hok'
  obtain ⟨⟨hokb, -⟩, hall⟩ := hok'
  have hbok : (inFile S.base).ok = true := base_ok _ hokb
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
  have hF : List.Forall₂ (fun (ts : List _root_.Fmt.Stored)
        (p : _root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)) =>
      List.Forall₂ (StoredFact (_root_.Fmt.HO O) S.base.cfg S.base.statement p.1.drawn.poss) ts p.2)
      S.stored rc := by
    rw [← hsnd]
    exact List.forall₂_map_left_iff.2 (g5.imp fun _ _ hh => hh.2)
  have hfull : everyOpeningHasItsDraws (xdOf S stm).xs ((rc.map fun p => stripR p.1).map (·.drawn)) = true := by
    refine fullX_true S.stored _ ?_
    rw [← hsnd, List.map_map]
    refine List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 ?_)
    refine (forall2_and_left g5 (specX_parts S hSok)).imp fun x p hh t ht' => ?_
    show t.lo + t.count ≤ p.1.drawn.poss.length
    rw [hh.1.1]
    exact hh.2 t ht'
  have hL : LaxFacts (_root_.Fmt.HO O) (inFile S.base)
      (ownOut (_root_.Fmt.HO O 169 0 1 _root_.Fmt.zero32 S.base.params) R rho0 s.chain.rho rc) := by
    refine ⟨rfl, ⟨rnd, h32, hrun⟩, ?_, ?_⟩
    · intro r hr'
      have hr2 : some r = some _ := hr'.symm.trans hrun
      rw [Option.some.inj hr2]
      exact hrho
    · show TraceL (_root_.Fmt.HO O) S.base.plan S.base.rounds
        ((rc.map fun p => stripR p.1).toArray).toList ⟨S.base.label, rho0, 0⟩ #[]
      rw [ht]
      exact g2
  exact verifyX_true (xdOf S stm) dec O hO B pd embS r0 r1 h0 h1 hokb hst
    (beq_iff_eq.1 (_root_.Fmt.ok_cfg hbok)) hi hns
    _ (ownOut (_root_.Fmt.HO O 169 0 1 _root_.Fmt.zero32 S.base.params) R rho0 s.chain.rho rc) R rc
    ht g1' rfl rfl
    hL hpd
    (by
      show passL (_root_.Fmt.HO O) S.base.rounds ((rc.map fun p => stripR p.1).toArray).toList
        ⟨S.base.label, rho0, 0⟩ = true
      rw [ht]
      exact g3)
    (by
      show rootsAll (_root_.Fmt.HO O) S.base.cfg R ((rc.map fun p => stripR p.1).toArray).toList =
        true
      rw [ht]
      exact g4)
    hF (fun t ht' => ⟨(hall t ht').1.1, (hall t ht').2⟩)
    (stoOK_of S stm O r0 r1 hSok _ rc g1' hF (fun t ht' => ⟨(hall t ht').1.1, (hall t ht').1.2⟩)
      honce hroot)
    (by
      show everyOpeningHasItsDraws (xdOf S stm).xs (((rc.map fun p => stripR p.1).toArray).toList.map (·.drawn))
        = true
      rw [ht]
      exact hfull)
    hdec


end

end TypedOracleCompiler.Run.PQ
