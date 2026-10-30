-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/YesByCutsMore.lean: the yes of the verifier of a file, cut by cut, under fixed
oracle functions; and helpers for single premises.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

OnBytes/TypedOracleCompiler/Joined/YesByCuts.lean says "pieces, so yes" of runs in a trace (`RunsIn`). A tie
between a program on bytes and the compiled verifier speaks of the verifier's value under fixed
oracle functions g (`OComp.det`, Rom/Cache.lean). This file carries the statement over.

Main names:
  `Agrees g tr`: every entry of the trace holds the answer that g gives.
  `det_of_runsIn`: a run in such a trace ends in the value under g.
  `runsIn_log`: an algorithm without coins runs, in some such trace, to its value under g.
  `noCoin_chainB`, `noCoin_runForests`, `noCoin_reqCheck`: the verifier's parts have no coins.
  `CutsAt g`: the fields of `Cuts`, with values under g in the place of runs in a trace.
  `CutsAt.cuts`, `yes_at`, `FileW.yes_at`: `CutsAt g` gives `Cuts` in a trace that agrees with g; so
    the verifier of a file has the value yes under g.
  `joined_of_runs`, `joined_at`: the premise `joined` follows from the three runs and the law of the
    joining round's kind.
    The first chain's run (h₁) is asked in both; the proof of `joined_of_runs` does not use it.
  `climbP`, `det_climbReq`, `det_reqCheck`: the check in the request tree under g, as a function
    without queries: the premise `request` is one equation between digests.
  `roots_of_lengths`: the premise `roots` from the lengths of three lists of roots.

Limits: one direction only, as in YesByCuts.lean. Nothing on soundness. Nothing says how g comes
from a hash on strings.

Terms: lean/GLOSSARY.md.

-/
import Rom.Cache
import OnBytes.TypedOracleCompiler.Compile.Batch.GlueTools
import OnBytes.TypedOracleCompiler.Joined.SealFile
import OnBytes.TypedOracleCompiler.Joined.YesByCuts

noncomputable section

namespace TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)

/-! ## Runs in a trace, and values under fixed oracle functions -/

section Bridge
variable {S : OSpec} {α : Type}

/-- every entry of the trace holds the answer that g gives to its query -/
def Agrees (g : Fam S) (tr : Trace S) : Prop := ∀ e ∈ tr, g e.1 e.2.1 = e.2.2

theorem Agrees.append {g : Fam S} {tr tr' : Trace S} (h : Agrees g tr) (h' : Agrees g tr') :
    Agrees g (tr ++ tr') := fun e he =>
  (List.mem_append.1 he).elim (h e) (h' e)

/-- A run in a trace that agrees with g ends in the value under g. -/
theorem det_of_runsIn {g : Fam S} {tr : Trace S} (hg : Agrees g tr) {c : OComp S α} {a : α}
    (h : RunsIn tr c a) : c.det g = a := by
  induction h with
  | pure a => rfl
  | query o q k r a hm _ ih =>
    show (k (g o q)).det g = a
    rw [show g o q = r from hg _ hm]
    exact ih

/-- An algorithm without coins runs, in some trace that agrees with g, to its value under g. -/
theorem runsIn_log (g : Fam S) {c : OComp S α} (hc : c.NoCoin) :
    ∃ tr, Agrees g tr ∧ RunsIn tr c (c.det g) := by
  induction c with
  | pure a => exact ⟨[], fun _ h => (by cases h), RunsIn.pure a⟩
  | query o q k ih =>
    obtain ⟨tr, ha, hr⟩ := ih (g o q) (hc (g o q))
    refine ⟨⟨o, q, g o q⟩ :: tr, fun e he => ?_,
      RunsIn.query o q k (g o q) _ List.mem_cons_self (hr.mono (List.subset_cons_self _ _))⟩
    rcases List.mem_cons.1 he with rfl | he
    · rfl
    · exact ha e he
  | sample n k _ => exact hc.elim

/-- the same, with the value named -/
theorem runsIn_log' (g : Fam S) {c : OComp S α} (hc : c.NoCoin) {a : α} (h : c.det g = a) :
    ∃ tr, Agrees g tr ∧ RunsIn tr c a := h ▸ runsIn_log g hc

theorem noCoin_of_detBound {c : OComp S α} : ∀ {t : ℕ}, DetBound c t → c.NoCoin := by
  induction c with
  | pure a => exact fun _ => trivial
  | query o q k ih =>
    intro t h r
    cases t with
    | zero => exact h.elim
    | succ t => exact ih r (h r)
  | sample n k _ => exact fun h => h.elim

/-- "has no coins" is kept by pure and bind -/
theorem counts_noCoin (S : OSpec) : Counts S (fun {_} c _ => c.NoCoin) where
  pure := fun _ _ => trivial
  bind := fun h hg => h.bind hg
  mono := fun h _ => h

end Bridge

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} {Y : Type} {E : ExtSpec}

/-! ## The verifier's parts have no coins -/

theorem noCoin_askV (o : OracleName) (q : domOf lam L o) : (askTypedOracle (L := L) (K := K) o q).NoCoin :=
  fun _ => trivial

theorem noCoin_chainB (t : Tag) (cms : List (Dig lam)) (x : Option X) (salt : Bits)
    (rtreq : Dig lam) (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : Phase lam) (rts : List (Dig lam))
    (pls : Plains s) : (recomputeChain (L := L) t cms x salt rtreq s A W embP i ph rts pls).NoCoin :=
  noCoin_of_detBound (detBound_chainB t cms x salt rtreq s A W embP i ph rts pls)

theorem noCoin_reqCheck (d : ℕ) (rtreq : Dig lam) (slot : ℕ) (path : List (Dig lam)) (c : Dig lam)
    (rs : Bits) : (reqCheck (L := L) (K := K) d rtreq slot path c rs).NoCoin :=
  noCoin_of_detBound (detBound_reqCheck d rtreq slot path c rs)

theorem noCoin_runForests : ∀ (Fs : List (Forest lam L)) (s : List (Dig lam)),
    (runForests (K := K) Fs s).NoCoin
  | [], _ => trivial
  | F :: Fs, _ =>
    OComp.NoCoin.bind
      (Counts.runForest (counts_noCoin (typedOracleFamily lam K L)) (noCoin_askV _) (noCoin_askV _) F _)
      fun _ => OComp.NoCoin.bind (noCoin_runForests Fs _) fun _ => trivial

/-! ## The premises under fixed oracle functions -/

section File
variable (sMT sFS : ℕ) (t : Tag) {G : Chains} (D : Desc G Y E) (wq : ProtocolQueryLayout lam K D.batch)
  (embS : (p : OPos G.sh) → OSym G.sh p → Body L)
  (embP : PlainPart G.sh G.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam D.batch)
  (a : Out lam G.c₁) (b : Out lam G.c₂) (e : Out lam G.c₃)

/-- **What is asked for a yes under fixed oracle functions g, cut by cut.** The fields of `Cuts`
(OnBytes/TypedOracleCompiler/Joined/YesByCuts.lean), with "runs in the trace to v" replaced by "has the value v
under g". a, b, e: what the three chains yield. F₁, F₂, F₃: the forests of the three chains' rounds;
Fe: those of the external strings. c: the slot value. -/
structure CutsAt (g : Fam (typedOracleFamily lam K L)) (F₁ F₂ F₃ Fe : List (Forest lam L)) (c : Dig lam) :
    Prop where
  /-- chain 1 has a value, from the start -/
  run₁ : (run₁ t D wq embP xin cms x π).det g = some a
  /-- chain 2 runs on from where chain 1 ended -/
  run₂ : (run₂ t D wq embP xin cms x π a).det g = some b
  /-- chain 3 runs on from where chain 2 ended -/
  run₃ : (run₃ t D wq embP xin cms x π a b).det g = some e
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
  /-- the walks of chain 1's forests say yes -/
  walk₁ : (runForests (K := K) F₁ (readsF F₁)).det g = true
  walk₂ : (runForests (K := K) F₂ (readsF F₂)).det g = true
  walk₃ : (runForests (K := K) F₃ (readsF F₃)).det g = true
  walkE : (runForests (K := K) Fe (readsF Fe)).det g = true
  /-- the check in the request tree at the slot value says yes -/
  request : (reqCheck (K := K) (L := L) depthReq π.rtreq π.slot π.path c π.rsalt).det g = true
  /-- over the whole: the decision, at the three chains' transcripts in a row -/
  accept : D.accept x (wq.ext.build fun p => (π.ext p).map Opening.sym)
    (Tr.app (s := G.c₁) (t := G.c₂ ++ G.c₃) (tr₁ D wq π a)
      (Tr.app (s := G.c₂) (t := G.c₃) (tr₂ D wq π b) (tr₃ D wq π e))) = true

variable {sMT sFS t D wq embS embP xin embE depthReq cms x π a b e}

/-- `CutsAt g` gives `Cuts` in a trace that agrees with g. -/
theorem CutsAt.cuts {g : Fam (typedOracleFamily lam K L)} {F₁ F₂ F₃ Fe : List (Forest lam L)} {c : Dig lam}
    (C : CutsAt sMT sFS t D wq embS embP xin embE depthReq cms x π a b e g F₁ F₂ F₃ Fe c) :
    ∃ tr, Agrees g tr ∧
      Cuts sMT sFS t D wq embS embP xin embE depthReq cms x π a b e tr F₁ F₂ F₃ Fe c := by
  obtain ⟨t1, a1, r1⟩ := runsIn_log' g (noCoin_chainB _ _ _ _ _ _ _ _ _ _ _ _ _) C.run₁
  obtain ⟨t2, a2, r2⟩ := runsIn_log' g (noCoin_chainB _ _ _ _ _ _ _ _ _ _ _ _ _) C.run₂
  obtain ⟨t3, a3, r3⟩ := runsIn_log' g (noCoin_chainB _ _ _ _ _ _ _ _ _ _ _ _ _) C.run₃
  obtain ⟨t4, a4, r4⟩ := runsIn_log' g (noCoin_runForests _ _) C.walk₁
  obtain ⟨t5, a5, r5⟩ := runsIn_log' g (noCoin_runForests _ _) C.walk₂
  obtain ⟨t6, a6, r6⟩ := runsIn_log' g (noCoin_runForests _ _) C.walk₃
  obtain ⟨t7, a7, r7⟩ := runsIn_log' g (noCoin_runForests _ _) C.walkE
  obtain ⟨t8, a8, r8⟩ := runsIn_log' g (noCoin_reqCheck _ _ _ _ _ _) C.request
  refine ⟨t1 ++ (t2 ++ (t3 ++ (t4 ++ (t5 ++ (t6 ++ (t7 ++ t8)))))),
    a1.append (a2.append (a3.append (a4.append (a5.append (a6.append (a7.append a8)))))), ?_⟩
  exact
    { run₁ := r1.mono (by intro z hz; simp [hz])
      run₂ := r2.mono (by intro z hz; simp [hz])
      run₃ := r3.mono (by intro z hz; simp [hz])
      joined := C.joined
      salt := C.salt
      roots := C.roots
      slot := C.slot
      strict₁ := C.strict₁
      strict₂ := C.strict₂
      strict₃ := C.strict₃
      strictE := C.strictE
      forests₁ := C.forests₁
      forests₂ := C.forests₂
      forests₃ := C.forests₃
      forestsE := C.forestsE
      count := C.count
      fit₁ := C.fit₁
      fit₂ := C.fit₂
      fit₃ := C.fit₃
      fitE := C.fitE
      walk₁ := r4.mono (by intro z hz; simp [hz])
      walk₂ := r5.mono (by intro z hz; simp [hz])
      walk₃ := r6.mono (by intro z hz; simp [hz])
      walkE := r7.mono (by intro z hz; simp [hz])
      request := r8.mono (by intro z hz; simp [hz])
      accept := C.accept }

/-- **Pieces, so yes, under fixed oracle functions.** -/
theorem yes_at {g : Fam (typedOracleFamily lam K L)} {F₁ F₂ F₃ Fe : List (Forest lam L)} {c : Dig lam}
    (C : CutsAt sMT sFS t D wq embS embP xin embE depthReq cms x π a b e g F₁ F₂ F₃ Fe c) :
    (verifyFile sMT sFS t D wq embS embP xin embE depthReq cms x π).det g = true := by
  obtain ⟨tr, hg, hC⟩ := C.cuts
  exact det_of_runsIn hg (yes_of_cuts hC)

/-! ## The premise `joined` -/

/-- The premise `joined` follows from the three runs and the law of the joining round's kind. -/
theorem joined_of_runs (hG : G.Laws) {tr : Trace (typedOracleFamily lam K L)}
    (h₁ : RunsIn tr (run₁ t D wq embP xin cms x π) (some a))
    (h₂ : RunsIn tr (run₂ t D wq embP xin cms x π a) (some b))
    (h₃ : RunsIn tr (run₃ t D wq embP xin cms x π a b) (some e)) :
    ∃ c, e.2.2.slotVal = some c := by
  obtain ⟨⟨c₁, ρ₁⟩, ⟨rt₁, R₁⟩, p₁⟩ := a
  obtain ⟨⟨c₂, ρ₂⟩, ⟨rt₂, R₂⟩, p₂⟩ := b
  obtain ⟨⟨c₃, ρ₃⟩, ⟨rt₃, R₃⟩, p₃⟩ := e
  have k₂ : IsShr p₂ := by
    obtain ⟨cur, ans, ph, rts', hv, -, -, hr⟩ := runsIn_chainB_cons h₂
    exact shr_of_sh _ _ _ _ _ ph p₂ _ _ _ _ (RoundSplits.allKind_const .sh _ (fun _ => rfl) G.s₂)
      (vstep_sh hv hG.kindJ) hr
  have k₃ : IsAft p₃ := by
    obtain ⟨cur, ans, ph, rts', hv, -, -, hr⟩ := runsIn_chainB_cons h₃
    exact aft_of_lo _ _ _ _ _ ph p₃ _ _ _ _ (RoundSplits.allKind_const .lo _ (fun _ => rfl) G.s₃)
      ((vstep_lo hv rfl).2 (Or.inl k₂)) hr
  cases p₃ with
  | first => exact k₃.elim
  | loc _ => exact k₃.elim
  | shr _ _ => exact k₃.elim
  | aft v c => exact ⟨c, rfl⟩

/-- the same under fixed oracle functions -/
theorem joined_at (hG : G.Laws) {g : Fam (typedOracleFamily lam K L)}
    (h₁ : (run₁ t D wq embP xin cms x π).det g = some a)
    (h₂ : (run₂ t D wq embP xin cms x π a).det g = some b)
    (h₃ : (run₃ t D wq embP xin cms x π a b).det g = some e) : ∃ c, e.2.2.slotVal = some c := by
  obtain ⟨t₁, -, r₁⟩ := runsIn_log' g (noCoin_chainB _ _ _ _ _ _ _ _ _ _ _ _ _) h₁
  obtain ⟨t₂, -, r₂⟩ := runsIn_log' g (noCoin_chainB _ _ _ _ _ _ _ _ _ _ _ _ _) h₂
  obtain ⟨t₃, -, r₃⟩ := runsIn_log' g (noCoin_chainB _ _ _ _ _ _ _ _ _ _ _ _ _) h₃
  exact joined_of_runs hG (tr := t₁ ++ (t₂ ++ t₃)) (r₁.mono (by intro z hz; simp [hz]))
    (r₂.mono (by intro z hz; simp [hz])) (r₃.mono (by intro z hz; simp [hz]))

/-! ## The premise `roots` -/

/-- The premise `roots`, if the string's roots are three lists in a row, each as long as the number
of roots that its chain has taken. -/
theorem roots_of_lengths {l₁ l₂ l₃ : List (Dig lam)} (hπ : π.roots = l₁ ++ (l₂ ++ l₃))
    (h₁ : l₁.length = RootsOfChain.count G.c₁ a.2.1) (h₂ : l₂.length = RootsOfChain.count G.c₂ b.2.1)
    (h₃ : l₃.length = RootsOfChain.count G.c₃ e.2.1) :
    π.roots.length ≤ RootsOfChain.count G.c₁ a.2.1 + (RootsOfChain.count G.c₂ b.2.1 + RootsOfChain.count G.c₃ e.2.1) := by
  rw [hπ, List.length_append, List.length_append, h₁, h₂, h₃]

end File

/-! ## The premise `request` -/

/-- The climb from the digest c at leaf number j along a path, with nd for the hash of a node: the
digest so far is the left child where the number is even. -/
def climbP (nd : Dig lam → Dig lam → Dig lam) : List (Dig lam) → ℕ → Dig lam → Dig lam
  | [], _, c => c
  | s :: ss, j, c => climbP nd ss (j / 2) (if j % 2 = 0 then nd c s else nd s c)

/-- the request tree's node hash under g -/
def rnodeAt (g : Fam (typedOracleFamily lam K L)) (u v : Dig lam) : Dig lam :=
  g OracleName.rnode (List.ofFn u, List.ofFn v)

/-- Under g the verifier's climb in the request tree is `climbP`. -/
theorem det_climbReq (g : Fam (typedOracleFamily lam K L)) : ∀ (path : List (Dig lam)) (j : ℕ) (c : Dig lam),
    (climbM (rnodeV (K := K) (L := L)) path j c).det g = climbP (rnodeAt g) path j c
  | [], _, _ => rfl
  | s :: ss, j, c => by
    by_cases hb : j % 2 = 0
    · have e : climbM (rnodeV (K := K) (L := L)) (s :: ss) j c
          = (rnodeV c s).bind fun u => climbM rnodeV ss (j / 2) u := by
        simp only [climbM, if_pos hb]; rfl
      rw [e, OComp.det_bind, det_climbReq g ss]
      show _ = climbP (rnodeAt g) ss (j / 2) (if j % 2 = 0 then _ else _)
      rw [if_pos hb]
      rfl
    · have e : climbM (rnodeV (K := K) (L := L)) (s :: ss) j c
          = (rnodeV s c).bind fun u => climbM rnodeV ss (j / 2) u := by
        simp only [climbM, if_neg hb]; rfl
      rw [e, OComp.det_bind, det_climbReq g ss]
      show _ = climbP (rnodeAt g) ss (j / 2) (if j % 2 = 0 then _ else _)
      rw [if_neg hb]
      rfl

/-- **The check in the request tree under g says yes**, if the path has d digests, the slot's number
is below 2^d, and the climb from the digest of the leaf, whose input is the slot value c and behind
it rs, ends in the request root. -/
theorem det_reqCheck (g : Fam (typedOracleFamily lam K L)) {d : ℕ} {rtreq : Dig lam} {slot : ℕ}
    {path : List (Dig lam)} {c : Dig lam} {rs : Bits} (hl : path.length = d) (hs : slot < 2 ^ d)
    (hr : climbP (rnodeAt g) path slot (g OracleName.rleaf (List.ofFn c ++ rs)) = rtreq) :
    (reqCheck (K := K) (L := L) d rtreq slot path c rs).det g = true := by
  unfold reqCheck
  rw [if_pos ⟨hl, hs⟩]
  show ((askTypedOracle (K := K) (L := L) OracleName.rleaf (List.ofFn c ++ rs)).bind fun dg =>
    (climbM rnodeV path slot dg).bind fun r => OComp.pure (decide (r = rtreq))).det g = true
  rw [OComp.det_bind, OComp.det_bind, det_climbReq]
  exact decide_eq_true hr

/-! ## At a written file -/

/-- The verifier of a written file has the value yes under g. -/
theorem FileW.yes_at {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {W : QueryLayout lam L} {G : Chains} (F : FileW W G Y E)
    {sMT sFS : ℕ} {cms : List (Dig lam)} {x : Y} {π : F.Prf} {a : Out lam G.c₁}
    {b : Out lam G.c₂} {e : Out lam G.c₃} {g : Fam (typedOracleFamily lam W.K L)}
    {F₁ F₂ F₃ Fe : List (Forest lam L)} {c : Dig lam}
    (C : CutsAt sMT sFS F.t F.D F.wq F.embS F.embP F.xin F.embE (W.dReq F.t) cms x π a b e g
      F₁ F₂ F₃ Fe c) :
    (F.verify sMT sFS cms x π).det g = true :=
  Joined.yes_at C

end TypedOracleCompiler.Joined
