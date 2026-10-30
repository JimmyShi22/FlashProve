-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ToyFit.lean: this file is about a small toy of this library's own (`Run.Toy1`; on bytes:
Fmt.Toy1). There, for all queries that the partial codes write, the encoding of the queries and the
functions "typed query ↦ call of the format's hash" give the same string. This is proved. So the run
over the single oracle is the run at the typed oracle functions, on every input on which the
verifier asks nothing off the plan.

Theorems; one test.
Run/ToyCode.lean has the encoding's data at the toy (`pageT`). Run/ToyQ.lean has the spellings for
the functions of Run/CodingFn.lean (`PD`). They were written apart. Here they are tied.

Main names:
  `pE3_put`: three words: the bits of the format's spelling of an element of the large field.
  `chainT_fit`: `ChainFit chainT PD` (Run/CodingPut.lean): label, kinds, work agree; what `rc1`,
    `rc2` write is the bits of `PD`'s message and then of `PD`'s nonce's word.
  `leafPT_fit`: what `leafPT` writes is the bits of the label (leaves' number, `PD`'s tree, `PD`'s
    index) and then of `PD`'s column.
  `firstT_fit`: what `firstT` writes is the string of the call that Run/CodingFn.lean makes of a
    query of round 0 at the block of the chain value.
  `toy_fit : PageFit (pageT cfgT cfgT_size) PD`: (Run/CodingAgree.lean) whatever string a partial
    code of the toy writes for a leaf, node or chain query is the string of the call that the
    functions make of that query.
  `toy_run_agree`: for every computation c over the typed oracles: if all queries of its run fit (a
    test that can be run: `OComp.askedOK` at `fitsC`), then (c.overOneN mOne (needC ..)).det oBits =
    c.det (famOf Fmt.oracle PD 2).
  `runOneC`, and a test. `toy_run_agree` speaks of the run that asks the blocks which the format
    writes (`needC`). Run/ToyOne.lean runs with fewer (`needT`: in round 2 the chain value alone).
    On all 21 files of this library's own small toy (its files: `Fmt.Toy1.files`) the two give the
    same verdicts.
    That is one test (a test when the file is compiled; no theorem).

Notation:
  `164`: the number under which the leaves of a run's tree are hashed (`Fmt.leafNo`,
    Fmt/Rules7.lean);
  `c.overOneN ..`: c over the single oracle, asking only for the needed blocks (Rom/OverOneN.lean);
  `mOne`: the encoding of the queries at the toy's configuration (Run/ToyOne.lean);
  `det g`: the run's result under oracle functions g, every coin toss yielding 0 (Rom/Cache.lean);
  `oBits`: the single oracle on bits (Run/OracleBits.lean).

Limits: this file does not say that the verifier asks only fitting queries on every input: on a
given file that is one evaluation. It says nothing on soundness.
Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Terms: lean/GLOSSARY.md.
-/
import Run.ToyOne
import Run.CodingAgree

set_option autoImplicit false

namespace Run.Toy1
open Iop Rom Compile Compile.Batch

theorem pE3_put (e : E3) : pE3.put e = some (bytesToBits (_root_.Fmt.ext e)) := by
  show (pU64.put e.1).bind
      (fun u => ((pU64.put e.2.1).bind fun u' => (pU64.put e.2.2).map (u' ++ ·)).map (u ++ ·)) = _
  rw [pU64_put, pU64_put, pU64_put]
  show some (bytesToBits (_root_.Fmt.u64 e.1) ++
        (bytesToBits (_root_.Fmt.u64 e.2.1) ++ bytesToBits (_root_.Fmt.u64 e.2.2))) = _
  unfold _root_.Fmt.ext
  rw [bytesToBits_append, bytesToBits_append, List.append_assoc]

theorem rc1_fit (rt : Option (Dig 256)) (pl : PBt) (s : List Bool) (h : rc1.put (rt, pl) = some s) :
    s = bytesToBits (PD.msg 1 (rt.map digToBytes) pl) ++
        bytesToBits (_root_.Fmt.u64n (PD.nonce 1 pl)) := by
  obtain ⟨a, ha, hs⟩ := PCode.via_put' _ _ _ _ _ (rt, pl) s h
  have hb := mk1_sel1 (rt, pl) a ha
  obtain ⟨u, v, hu, hv, rfl⟩ := PCode.cons_put _ _ _ _ a s hs
  have e1 : rt = some a.1 := (congrArg Prod.fst hb).symm
  have e2 : pl = .inr (.inl (.inr ((), a.2))) := (congrArg Prod.snd hb).symm
  subst e1 e2
  have hu' : u = List.ofFn a.1 := by
    obtain ⟨l, hl, hp⟩ := PCode.pull_put _ _ _ _ _ a.1 u hu
    have hl' : l = List.ofFn a.1 := (Option.some.inj hl).symm
    subst hl'
    have h0 : (if (List.ofFn a.1).length = 256 then some (List.ofFn a.1) else none) = some u := hp
    rw [if_pos (List.length_ofFn)] at h0
    exact (Option.some.inj h0).symm
  have hv' : v = bytesToBits (_root_.Fmt.u64n a.2) := by
    have h0 : (if a.2 < 2 ^ 64 then some (bytesToBits (_root_.Fmt.u64n a.2)) else none) = some v :=
      hv
    by_cases hn : a.2 < 2 ^ 64
    · rw [if_pos hn] at h0
      exact (Option.some.inj h0).symm
    · rw [if_neg hn] at h0
      cases h0
  rw [hu', hv']
  show _ = bytesToBits (digToBytes a.1) ++ bytesToBits (_root_.Fmt.u64n a.2)
  rw [bits_digToBytes]

theorem rc2_fit (rt : Option (Dig 256)) (pl : PBt) (s : List Bool) (h : rc2.put (rt, pl) = some s) :
    s = bytesToBits (PD.msg 2 (rt.map digToBytes) pl) ++
        bytesToBits (_root_.Fmt.u64n (PD.nonce 2 pl)) := by
  obtain ⟨a, ha, hs⟩ := PCode.via_put' _ _ _ _ _ (rt, pl) s h
  have hb := mk2_sel2 (rt, pl) a ha
  obtain ⟨u, v, hu, hv, rfl⟩ := PCode.cons_put _ _ _ _ a s hs
  have e1 : rt = none := (congrArg Prod.fst hb).symm
  have e2 : pl = .inr (.inr (.inl (.inr a.1))) := (congrArg Prod.snd hb).symm
  subst e1 e2
  rw [pE3_put] at hu
  rw [← Option.some.inj hu, ← Option.some.inj hv]
  rfl

theorem chainT_fit : ChainFit chainT PD where
  label := rfl
  kind := fun _ => rfl
  work := fun _ => rfl
  rc := fun i rt pl s h => by
    match i, h with
    | 0, h => cases h
    | 1, h => exact rc1_fit rt pl s h
    | 2, h => exact rc2_fit rt pl s h
    | _ + 3, h => cases h

theorem leafPT_fit (y : SymAny (shapeOf Lt .test)) (m : List Bool) (h : leafPT.put y = some m) :
    m = bytesToBits (_root_.Fmt.label 164 (PD.leaf y).1 (PD.leaf y).2.1) ++
        bytesToBits (PD.leaf y).2.2 := by
  obtain ⟨a, ha, hs⟩ := PCode.via_put' _ _ _ _ _ y m h
  have hb := mkL_selL y a ha
  subst hb
  obtain ⟨u, hu, rfl⟩ := PCode.pre_put' _ _ _ m hs
  obtain ⟨u1, v1, hu1, hv1, rfl⟩ := PCode.cons_put _ _ _ _ a u hu
  rw [pE3_put] at hv1
  have hx : u1 = bytesToBits (_root_.Fmt.u64n (16 + a.1.val)) := by
    obtain ⟨n, hn, hp⟩ := PCode.pull_put _ _ _ _ _ a.1 u1 hu1
    have hn' : n = 16 + a.1.val := (Option.some.inj hn).symm
    subst hn'
    rw [pWord_put _ (by have := a.1.isLt; omega)] at hp
    exact (Option.some.inj hp).symm
  rw [hx, ← Option.some.inj hv1]
  show word164 ++
      (bytesToBits (_root_.Fmt.u64n (16 + a.1.val)) ++ bytesToBits (_root_.Fmt.ext a.2)) =
    bytesToBits (_root_.Fmt.u64n (164 + 65536 * _root_.Fmt.leafPlace 0 3 5) ++
          _root_.Fmt.u64n (16 + a.1.val)) ++
      bytesToBits (_root_.Fmt.ext a.2)
  rw [bytesToBits_append, List.append_assoc]
  rfl

theorem size_ext (e : E3) : (_root_.Fmt.ext e).size = 24 := by
  unfold _root_.Fmt.ext
  rw [ByteArray.size_append, ByteArray.size_append, _root_.Fmt.size_u64,
    _root_.Fmt.size_u64, _root_.Fmt.size_u64]

/-- The statement's bytes are those of the functions' spelling. -/
theorem stmT_eq (x : Option E3) (st : ByteArray) (h : stmT x = some st) : st = PD.stm x := by
  cases x with
  | none => cases h
  | some c =>
      have h0 : (((pE3.put c).map (hdrSt ++ ·)).map bitsToBytes) = some st := h
      rw [pE3_put] at h0
      rw [← Option.some.inj h0]
      show bitsToBytes (hdrSt ++ bytesToBits (_root_.Fmt.ext c)) =
        _root_.Fmt.textS "toy: claim" ++ _root_.Fmt.u64n (_root_.Fmt.ext c).size ++ _root_.Fmt.ext c
      unfold hdrSt
      rw [← bytesToBits_append, bitsToBytes_bytesToBits, size_ext]

theorem bits_first (pd st : ByteArray) (salt : List Bool) :
    bytesToBits (_root_.Fmt.firstBytes pd st ByteArray.empty (runOf salt)) =
      bytesToBits (Run.firstBytes pd st salt) := by
  unfold _root_.Fmt.firstBytes Run.firstBytes runOf
  cases hs : salt.isEmpty with
  | true =>
      simp only [if_true, bytesToBits_append, List.append_assoc]
      rfl
  | false =>
      simp only [Bool.false_eq_true, if_false, bytesToBits_append, List.append_assoc]
      rfl

theorem firstT_fit (q : FbIn 256 Lt .test) (s : List Bool) (h : firstT.put q = some s) :
    q.round = 0 ∧ ∃ c, fbCall PD 2 q (Fin.last 2) = some c ∧ s = bytesToBits (strOf c) := by
  obtain ⟨a, ha, hs⟩ := PCode.via_put' (pFirst0 7 stmT unstmT unstm_stm stm_unstm) (fbSel0 isP0T)
    (fbMk0 p0T) (fbSel0_mk p0T isP0T isP0T_iff) (fbMk0_sel p0T isP0T isP0T_iff) q s h
  have hq := fbMk0_sel p0T isP0T isP0T_iff q a ha
  subst hq
  refine ⟨rfl,
    ⟨0, 160, 0, 7, _root_.Fmt.zero32, Run.firstBytes (digToBytes a.1) (PD.stm a.2.1) a.2.2⟩,
    rfl, ?_⟩
  have h0 : (stmT a.2.1).bind (fun st =>
        if st.size < 2 ^ 64 ∧ (a.2.2 = [] ∨ a.2.2.length = 256) then
          some (hdr160 7 ++
              bytesToBits (_root_.Fmt.firstBytes (digToBytes a.1) st ByteArray.empty (runOf a.2.2)))
        else none) = some s := hs
  cases hst : stmT a.2.1 with
  | none => rw [hst] at h0; cases h0
  | some st =>
      rw [hst] at h0
      have h1 : (if st.size < 2 ^ 64 ∧ (a.2.2 = [] ∨ a.2.2.length = 256) then
              some (hdr160 7 ++
                  bytesToBits
                    (_root_.Fmt.firstBytes (digToBytes a.1) st ByteArray.empty (runOf a.2.2)))
            else none) = some s := h0
      by_cases hc : st.size < 2 ^ 64 ∧ (a.2.2 = [] ∨ a.2.2.length = 256)
      · rw [if_pos hc] at h1
        rw [← Option.some.inj h1, bits_first, stmT_eq _ st hst]
        exact (oStr_bits 0 160 0 7 _root_.Fmt.zero32 _).symm
      · rw [if_neg hc] at h1
        cases h1

/-- What the partial codes of the encoding of the queries write are the bits of the functions'
strings, at the toy. -/
theorem toy_fit : PageFit (pageT cfgT cfgT_size) PD :=
  PageFit.of (pageT cfgT cfgT_size) PD (by decide) chainT_fit rfl 40 rfl leafPT_fit firstT_fit

/-- The run over the single oracle is the run at the typed oracle functions, wherever nothing off
the plan is asked (`h`). -/
theorem toy_run_agree {α : Type} (c : OComp (spec 256 2 Lt) α)
    (h : c.askedOK (famOf _root_.Fmt.oracle PD 2) (fitsC (pageT cfgT cfgT_size)) = true) :
    (c.overOneN mOne (needC (pageT cfgT cfgT_size))).det oBits =
      c.det (famOf _root_.Fmt.oracle PD 2) :=
  run_agree toy_fit c h

/-- The run over the single oracle at the blocks that the format writes (the form of
`toy_run_agree`). -/
def runOnC (c : E3) (x : Option (List (Dig 256) × OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto QT))) : Who :=
  match x with
  | none => .reader
  | some (cms, π) =>
    if ((V cms c π).overOneN mOne (needC (pageT cfgT cfgT_size))).detB oB then .accepted
    else .verifier

def runOneC (c : E3) (file : ByteArray) : Who :=
  runOnC c (parseLaxW (m := Id) _root_.Fmt.formatHash (specOf c) T file)

end Run.Toy1

-- on all 21 files of the toy (Fmt.Toy1.files): the verdicts at needC are those at needT
open Run Run.Toy1 in
#guard (_root_.Fmt.Toy1.files.map fun f => runOneC (1, 2, 3) f.2.1) == (_root_.Fmt.Toy1.files.map fun f => runOne (1, 2, 3) f.2.1)
