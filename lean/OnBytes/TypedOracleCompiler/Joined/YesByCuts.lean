-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/YesByCuts.lean: the yes of the verifier of a file, cut by cut: from facts that
each speak of one hash chain's rounds to a yes of the whole.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

The verifier of a file (`verifyFile`, OnBytes/TypedOracleCompiler/Joined/Verifier.lean) walks three chains, tests
the strict format, and then checks the openings, the request tree and the decision. This file
gives the direction "pieces, so yes": `Cuts` lists what is asked, and `yes_of_cuts` concludes that
the verifier runs to yes in the trace.

Main names:
  `readS`, `readE`: which positions of the prover's oracles, of the external strings, are read,
    given the verifier messages and the roots of all three chains.
  `runForests_app`: the walks of two lists of forests, one after the other.
  `Cuts`: the list of premises. Said of ONE chain's rounds each: the three runs; the strict format
    of the openings; the forests; that each check is well formed and within the depth; the walks.
  `yes_of_cuts`: `Cuts` gives a yes of `verifyFile`; `FileW.yes_of_cuts`: of `FileW.verify`.

What cannot be cut, and stays one premise over the whole:
  `count`: the number of all openings, of the three chains and the external strings together, is at
    most `nOpen`;
  `roots`: the string holds no root beyond those that the three chains have taken;
  `readS`, `readE`: which positions are read is a function of the verifier messages and plain
    parts of all three chains: each chain's premises take their share of the one function;
  `accept`: the decision sees the whole transcript; it is given as the three chains' transcripts
    in a row.
A tree that a later chain opens and an earlier chain sent has no premise of its own here. By the
definition of `forestsB` an opening stands at a position of the round that sent the oracle, and is
checked in that round's forests under that round's roots: so it falls under the sender's premises.

Limits: one direction only. Nothing on soundness.
That the conditions of `Cuts` hold together is shown of no real file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.ForestFacts
import OnBytes.TypedOracleCompiler.Joined.After
import OnBytes.TypedOracleCompiler.Joined.CutAfter
import OnBytes.TypedOracleCompiler.Joined.Verifier

noncomputable section

namespace TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} {Y : Type} {E : ExtSpec}

/-! ## The walks of two lists of forests -/

/-- The walks of the forests Fs, with the sibling digests read off their own paths, and then the
walks of the forests Gs with the digests s. -/
theorem runForests_app {tr : Trace (typedOracleFamily lam K L)} :
    ∀ (Fs Gs : List (Forest lam L)) (s : List (Dig lam)),
      RunsIn tr (runForests (K := K) Fs (readsF Fs)) true →
      RunsIn tr (runForests (K := K) Gs s) true →
      RunsIn tr (runForests (K := K) (Fs ++ Gs) (readsF Fs ++ s)) true
  | [], _, _, _, h => h
  | F :: Fs, Gs, s, h, h' => by
    have e1 : (F.reads ++ readsF Fs).take F.need = F.reads := List.take_left' F.length_reads
    have e2 : (F.reads ++ readsF Fs).drop F.need = readsF Fs := List.drop_left' F.length_reads
    have e3 : (F.reads ++ (readsF Fs ++ s)).take F.need = F.reads := List.take_left' F.length_reads
    have e4 : (F.reads ++ (readsF Fs ++ s)).drop F.need = readsF Fs ++ s :=
      List.drop_left' F.length_reads
    have h0 : RunsIn tr ((runForest (K := K) F ((F.reads ++ readsF Fs).take F.need)).bind fun a =>
        (runForests Fs ((F.reads ++ readsF Fs).drop F.need)).bind fun b =>
          OComp.pure (a && b)) true := h
    rw [e1, e2] at h0
    obtain ⟨a, ha, h1⟩ := (runsIn_bind_iff _ _ _).1 h0
    obtain ⟨b, hb, h2⟩ := (runsIn_bind_iff _ _ _).1 h1
    obtain ⟨rfl, rfl⟩ := Bool.and_eq_true_iff.1 (runsIn_pure_iff.1 h2)
    show RunsIn tr ((runForest (K := K) F ((F.reads ++ readsF Fs ++ s).take F.need)).bind fun a =>
        (runForests (Fs ++ Gs) ((F.reads ++ readsF Fs ++ s).drop F.need)).bind fun b =>
          OComp.pure (a && b)) true
    rw [List.append_assoc, e3, e4]
    exact (runsIn_bind_iff _ _ _).2 ⟨true, ha, (runsIn_bind_iff _ _ _).2
      ⟨true, runForests_app Fs Gs s hb h', runsIn_pure_iff.2 rfl⟩⟩

theorem readsF_append (Fs Gs : List (Forest lam L)) : readsF (Fs ++ Gs) = readsF Fs ++ readsF Gs :=
  List.flatMap_append

/-! ## What is read -/

section File
variable (sMT sFS : ℕ) (t : Tag) {G : Chains} (D : Desc G Y E) (wq : ProtocolQueryLayout lam K D.batch)
  (embS : (p : OPos G.sh) → OSym G.sh p → Body L)
  (embP : PlainPart G.sh G.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam D.batch)

/-- is this position of the prover's oracles read, given the verifier messages ρ and the roots R of
all three chains -/
def readS (ρ : Rho G.sh) (R : RootsOfChain lam G.sh) : OPos G.sh → Bool :=
  haveI := wq.decO
  fun p => decide (p ∈ D.reads x ρ (effPlains G.sh G.ann R π.plains))

/-- is this position of the external strings read -/
def readE (ρ : Rho G.sh) : E.Pos → Bool :=
  haveI := wq.ext.dec
  fun p => decide (p ∈ D.extReads x ρ)

theorem strictBB_eq (ρ : Rho G.sh) (R : RootsOfChain lam G.sh) (ph : Phase lam) :
    proofHasStrictFormat sMT sFS D.batch wq depthReq x π ρ R ph =
      (decide (π.salt.length = sFS) && decide (π.roots.length ≤ RootsOfChain.count G.sh R) &&
        strictSB sMT G.sh G.ann wq.sh R (readS D wq x π ρ R) π.opens &&
        strictExt sMT wq.ext (readE D wq x ρ) π.ext &&
        decide (π.slot < 2 ^ depthReq) && (ph.slotVal.isSome || π.path.isEmpty) &&
        (ph.slotVal.isSome || π.rsalt.isEmpty)) := rfl

theorem forestsOf_eq (ρ : Rho G.sh) (R : RootsOfChain lam G.sh) :
    forestsOf D.batch wq embS embE cms x π ρ R =
      appO (forestsB G.sh G.ann wq.sh embS R (readS D wq x π ρ R) π.opens)
        (forestExt wq.ext embE cms (readE D wq x ρ) π.ext) := by
  unfold forestsOf appO
  show (match forestsB G.sh G.ann wq.sh embS R (readS D wq x π ρ R) π.opens,
      forestExt wq.ext embE cms (readE D wq x ρ) π.ext with
    | some a, some b => some (a ++ b)
    | _, _ => none) = _
  cases forestsB G.sh G.ann wq.sh embS R (readS D wq x π ρ R) π.opens <;>
    cases forestExt wq.ext embE cms (readE D wq x ρ) π.ext <;> rfl

/-! ## The premises, chain by chain -/

section Cuts
variable (a : Out lam G.c₁) (b : Out lam G.c₂) (e : Out lam G.c₃)

/-- which positions of the prover's oracles are read, given what the three chains have yielded -/
def rd : OPos G.sh → Bool := readS D wq x π (glue a b e).1 (glue a b e).2.1

/-- chain 1's share of `rd` -/
def rd₁ : OPos G.c₁ → Bool := fun p =>
  rd D wq x π a b e (OPos.left (s := G.c₁) (t := G.c₂ ++ G.c₃) p)
/-- chain 2's share -/
def rd₂ : OPos G.c₂ → Bool := fun p =>
  rd D wq x π a b e
    (OPos.right (s := G.c₁) (t := G.c₂ ++ G.c₃) (OPos.left (s := G.c₂) (t := G.c₃) p))
/-- chain 3's share -/
def rd₃ : OPos G.c₃ → Bool := fun p =>
  rd D wq x π a b e
    (OPos.right (s := G.c₁) (t := G.c₂ ++ G.c₃) (OPos.right (s := G.c₂) (t := G.c₃) p))

/-- how the symbols of chain 1's rounds are written into a leaf -/
def symb₁ : (p : OPos G.c₁) → OSym G.c₁ p → Body L := embL (s := G.c₁) (u := G.c₂ ++ G.c₃) embS
/-- of chain 2's rounds -/
def symb₂ : (p : OPos G.c₂) → OSym G.c₂ p → Body L :=
  embL (s := G.c₂) (u := G.c₃) (embR (s := G.c₁) (u := G.c₂ ++ G.c₃) embS)
/-- of chain 3's rounds -/
def symb₃ : (p : OPos G.c₃) → OSym G.c₃ p → Body L :=
  embR (s := G.c₂) (u := G.c₃) (embR (s := G.c₁) (u := G.c₂ ++ G.c₃) embS)

/-- the openings at the positions of chain 1's rounds -/
def op₁ : (p : OPos G.c₁) → Option (Opening lam (OSym G.c₁ p)) :=
  opensL (s := G.c₁) (u := G.c₂ ++ G.c₃) π.opens
/-- of chain 2's rounds -/
def op₂ : (p : OPos G.c₂) → Option (Opening lam (OSym G.c₂ p)) :=
  opensL (s := G.c₂) (u := G.c₃) (opensR (s := G.c₁) (u := G.c₂ ++ G.c₃) π.opens)
/-- of chain 3's rounds -/
def op₃ : (p : OPos G.c₃) → Option (Opening lam (OSym G.c₃ p)) :=
  opensR (s := G.c₂) (u := G.c₃) (opensR (s := G.c₁) (u := G.c₂ ++ G.c₃) π.opens)

/-- the transcript of chain 1's rounds that the verifier builds -/
def tr₁ : Tr G.c₁ :=
  mkTr G.c₁ G.A₁ (wire₁ wq) a.2.1 (Plains.fst (s := G.c₁) (t := G.c₂ ++ G.c₃) π.plains) a.1
    (op₁ D π)
/-- of chain 2's rounds -/
def tr₂ : Tr G.c₂ :=
  mkTr G.c₂ G.A₂ (wire₂ wq) b.2.1
    (Plains.fst (s := G.c₂) (t := G.c₃) (Plains.snd (s := G.c₁) (t := G.c₂ ++ G.c₃) π.plains)) b.1
    (op₂ D π)
/-- of chain 3's rounds -/
def tr₃ : Tr G.c₃ :=
  mkTr G.c₃ G.A₃ (wire₃ wq) e.2.1
    (Plains.snd (s := G.c₂) (t := G.c₃) (Plains.snd (s := G.c₁) (t := G.c₂ ++ G.c₃) π.plains)) e.1
    (op₃ D π)

/-- a check is well formed, in a tree within the depth that the wire record allows -/
def fits (c : Check lam L) : Bool := c.wellFormed && decide (c.depth ≤ wq.maxDepth)

/-- **What is asked for a yes, cut by cut.** a, b, e: what the three chains yield. F₁, F₂, F₃: the
forests of the three chains' rounds; Fe: those of the external strings. c: the slot value. -/
structure Cuts (tr : Trace (typedOracleFamily lam K L)) (F₁ F₂ F₃ Fe : List (Forest lam L)) (c : Dig lam) :
    Prop where
  /-- chain 1 runs in the trace, from the start -/
  run₁ : RunsIn tr (run₁ t D wq embP xin cms x π) (some a)
  /-- chain 2 runs on from where chain 1 ended -/
  run₂ : RunsIn tr (run₂ t D wq embP xin cms x π a) (some b)
  /-- chain 3 runs on from where chain 2 ended -/
  run₃ : RunsIn tr (run₃ t D wq embP xin cms x π a b) (some e)
  /-- chain 3 ends with the slot value c -/
  joined : e.2.2.slotVal = some c
  /-- the format: chain 1's salt has sFS bits -/
  salt : π.salt.length = sFS
  /-- the format, over the whole: no root beyond those that the three chains have taken -/
  roots : π.roots.length ≤ RootsOfChain.count G.c₁ a.2.1 + (RootsOfChain.count G.c₂ b.2.1 + RootsOfChain.count G.c₃ e.2.1)
  /-- the format: the slot's number is the number of a slot -/
  slot : π.slot < 2 ^ depthReq
  /-- the format of the openings at chain 1's rounds -/
  strict₁ : strictSB sMT G.c₁ G.A₁ (wire₁ wq) a.2.1 (rd₁ D wq x π a b e) (op₁ D π) = true
  /-- at chain 2's rounds -/
  strict₂ : strictSB sMT G.c₂ G.A₂ (wire₂ wq) b.2.1 (rd₂ D wq x π a b e) (op₂ D π) = true
  /-- at chain 3's rounds -/
  strict₃ : strictSB sMT G.c₃ G.A₃ (wire₃ wq) e.2.1 (rd₃ D wq x π a b e) (op₃ D π) = true
  /-- of the openings of the external strings -/
  strictE : strictExt sMT wq.ext (readE D wq x (glue a b e).1) π.ext = true
  /-- no opening that is read is missing at chain 1's rounds: its forests -/
  forests₁ : forestsB G.c₁ G.A₁ (wire₁ wq) (symb₁ embS) a.2.1 (rd₁ D wq x π a b e) (op₁ D π) =
    some F₁
  /-- chain 2's forests -/
  forests₂ : forestsB G.c₂ G.A₂ (wire₂ wq) (symb₂ embS) b.2.1 (rd₂ D wq x π a b e) (op₂ D π) =
    some F₂
  /-- chain 3's forests -/
  forests₃ : forestsB G.c₃ G.A₃ (wire₃ wq) (symb₃ embS) e.2.1 (rd₃ D wq x π a b e) (op₃ D π) =
    some F₃
  /-- the forests of the external strings -/
  forestsE : forestExt wq.ext embE cms (readE D wq x (glue a b e).1) π.ext = some Fe
  /-- over the whole: at most nOpen openings in all -/
  count : (flatF F₁).length + (flatF F₂).length + (flatF F₃).length + (flatF Fe).length ≤ wq.nOpen
  /-- chain 1's checks are well formed and within the depth -/
  fit₁ : (flatF F₁).all (fits D wq) = true
  fit₂ : (flatF F₂).all (fits D wq) = true
  fit₃ : (flatF F₃).all (fits D wq) = true
  fitE : (flatF Fe).all (fits D wq) = true
  /-- the walks of chain 1's forests run to yes in the trace -/
  walk₁ : RunsIn tr (runForests (K := K) F₁ (readsF F₁)) true
  walk₂ : RunsIn tr (runForests (K := K) F₂ (readsF F₂)) true
  walk₃ : RunsIn tr (runForests (K := K) F₃ (readsF F₃)) true
  walkE : RunsIn tr (runForests (K := K) Fe (readsF Fe)) true
  /-- the check in the request tree at the slot value runs to yes -/
  request : RunsIn tr (reqCheck (K := K) (L := L) depthReq π.rtreq π.slot π.path c π.rsalt) true
  /-- over the whole: the decision, at the three chains' transcripts in a row -/
  accept : D.accept x (wq.ext.build fun p => (π.ext p).map Opening.sym)
    (Tr.app (s := G.c₁) (t := G.c₂ ++ G.c₃) (tr₁ D wq π a)
      (Tr.app (s := G.c₂) (t := G.c₃) (tr₂ D wq π b) (tr₃ D wq π e))) = true

variable {sMT sFS t D wq embS embP xin embE depthReq cms x π a b e}

/-- **Pieces, so yes.** If what `Cuts` lists holds, the verifier of a file runs to yes in the
trace. -/
theorem yes_of_cuts {tr : Trace (typedOracleFamily lam K L)} {F₁ F₂ F₃ Fe : List (Forest lam L)} {c : Dig lam}
    (C : Cuts sMT sFS t D wq embS embP xin embE depthReq cms x π a b e tr F₁ F₂ F₃ Fe c) :
    RunsIn tr (verifyFile sMT sFS t D wq embS embP xin embE depthReq cms x π) true := by
  have hj : (glue a b e).2.2.slotVal = some c := C.joined
  refine (runsIn_verifyFile_iff sMT sFS t D wq embS embP xin embE depthReq cms x π).2
    ⟨a, b, e, C.run₁, C.run₂, C.run₃, ?_, ?_⟩
  · -- the strict format
    have hc : RootsOfChain.count G.sh (glue a b e).2.1 =
        RootsOfChain.count G.c₁ a.2.1 + (RootsOfChain.count G.c₂ b.2.1 + RootsOfChain.count G.c₃ e.2.1) := by
      show RootsOfChain.count (G.c₁ ++ (G.c₂ ++ G.c₃)) (RT.app a.2.1 (RT.app b.2.1 e.2.1)) = _
      rw [RT.count_app, RT.count_app]
    have hs :
        strictSB sMT G.sh G.ann wq.sh (glue a b e).2.1 (rd D wq x π a b e) π.opens = true := by
      show strictSB sMT (G.c₁ ++ (G.c₂ ++ G.c₃)) (RoundSplits.app G.A₁ (RoundSplits.app G.A₂ G.A₃)) wq.sh
        (RT.app a.2.1 (RT.app b.2.1 e.2.1)) (rd D wq x π a b e) π.opens = true
      rw [strictSB_app, strictSB_app, RT.fst_app, RT.snd_app, RT.fst_app, RT.snd_app]
      exact Bool.and_eq_true_iff.2 ⟨C.strict₁, Bool.and_eq_true_iff.2 ⟨C.strict₂, C.strict₃⟩⟩
    rw [strictBB_eq, hc, decide_eq_true C.salt, decide_eq_true C.roots, decide_eq_true C.slot, hj]
    show (true && true && strictSB sMT G.sh G.ann wq.sh (glue a b e).2.1 (rd D wq x π a b e) π.opens
      && strictExt sMT wq.ext (readE D wq x (glue a b e).1) π.ext && true && _ && _) = true
    rw [hs, C.strictE]
    rfl
  · -- behind the chains
    refine (runsIn_afterBO_iff wq embS embE depthReq cms x π _ _ _).2
      ⟨(F₁ ++ (F₂ ++ F₃)) ++ Fe, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [forestsOf_eq]
      refine appO_eq_some.2 ⟨_, _, ?_, C.forestsE, rfl⟩
      show forestsB (G.c₁ ++ (G.c₂ ++ G.c₃)) (RoundSplits.app G.A₁ (RoundSplits.app G.A₂ G.A₃)) wq.sh embS
        (RT.app a.2.1 (RT.app b.2.1 e.2.1)) (rd D wq x π a b e) π.opens = _
      rw [forestsB_app, forestsB_app, RT.fst_app, RT.snd_app, RT.fst_app, RT.snd_app]
      exact appO_eq_some.2 ⟨_, _, C.forests₁,
        appO_eq_some.2 ⟨_, _, C.forests₂, C.forests₃, rfl⟩, rfl⟩
    · rw [flatF_append, flatF_append, flatF_append, List.length_append, List.length_append,
        List.length_append]
      have := C.count
      omega
    · rw [flatF_append, flatF_append, flatF_append, List.all_append, List.all_append,
        List.all_append]
      exact Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2 ⟨C.fit₁,
        Bool.and_eq_true_iff.2 ⟨C.fit₂, C.fit₃⟩⟩, C.fitE⟩
    · rw [readsF_append]
      refine runForests_app _ _ _ ?_ C.walkE
      rw [readsF_append]
      refine runForests_app _ _ _ C.walk₁ ?_
      rw [readsF_append]
      exact runForests_app _ _ _ C.walk₂ C.walk₃
    · refine (runsIn_reqPart_iff depthReq π _).2 fun c' hc' => ?_
      obtain rfl : c = c' := Option.some.inj (hj.symm.trans hc')
      exact C.request
    · show D.accept x _ (mkTr (G.c₁ ++ (G.c₂ ++ G.c₃)) (RoundSplits.app G.A₁ (RoundSplits.app G.A₂ G.A₃)) wq.sh
        (RT.app a.2.1 (RT.app b.2.1 e.2.1)) π.plains
        (Rho.app (s := G.c₁) (t := G.c₂ ++ G.c₃) a.1 (Rho.app (s := G.c₂) (t := G.c₃) b.1 e.1))
        π.opens) = true
      rw [mkTr_app, mkTr_app, RT.fst_app, RT.snd_app, RT.fst_app, RT.snd_app, Rho.fst_app,
        Rho.snd_app, Rho.fst_app, Rho.snd_app]
      exact C.accept

end Cuts

end File

/-- The same at a written file: its verifier runs to yes in the trace. -/
theorem FileW.yes_of_cuts {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {W : QueryLayout lam L} {G : Chains}
    (F : FileW W G Y E) {sMT sFS : ℕ} {cms : List (Dig lam)} {x : Y} {π : F.Prf}
    {a : Out lam G.c₁} {b : Out lam G.c₂} {e : Out lam G.c₃} {tr : Tc W}
    {F₁ F₂ F₃ Fe : List (Forest lam L)} {c : Dig lam}
    (C : Cuts sMT sFS F.t F.D F.wq F.embS F.embP F.xin F.embE (W.dReq F.t) cms x π a b e tr
      F₁ F₂ F₃ Fe c) :
    RunsIn tr (F.verify sMT sFS cms x π) true :=
  Joined.yes_of_cuts C

end TypedOracleCompiler.Joined
