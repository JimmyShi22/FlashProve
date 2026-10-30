-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/K/Left.lean: what is left to show for a yes of the verifier of a file, at a proof
string that is assembled from three chains as read.

A part of the tie between a reader of a file's bytes and the second form of the compiler's verifier
side (lean/OnBytes/TypedOracleCompiler/Joined/): it brings that verifier's yes, under fixed oracle functions, down
to conditions on what was read and on how these functions answer. That the reading of a real file,
and oracle functions made from the programs' hash, meet these conditions is not shown in this
folder.


"Yes, cut by cut" under fixed oracle functions g (`CutsAt`,
OnBytes/TypedOracleCompiler/Joined/YesByCutsMore.lean) has 26 premises. At an assembled string five of them are
proved (`FileW.runs_at`, OnBytes/TypedOracleCompiler/Joined/K/RunsAt.lean): the three runs, `roots`, `joined`.
Twelve follow from three conditions at each position (`Opened`, `OpenedE`,
OnBytes/TypedOracleCompiler/Joined/K/YesRead.lean): the strict format of the openings, the forests, and that each
check fits. `count` follows from the laws of the wire record (`count_of_forests`,
OnBytes/TypedOracleCompiler/Joined/K/Count.lean). Five have a form without queries: the four walks (`walk_at`,
OnBytes/TypedOracleCompiler/Joined/WalkAt.lean) and `request` (`det_reqCheck`). This file lists what is then left,
and concludes the yes.

Main names:
  `AfterRuns`: what is asked at values a, b, e of the three chains: g answers the query to g behind
    the first chain with that chain's seal as read; the openings at each chain's rounds and of the
    external strings; each forest's walk, as a Boolean equation; the decision.
  `Left`: the law of the joining round's kind; the laws of the wire record; `Fits`; the lengths of
    the salt and of the request path; the slot's number; the climb in the request tree from the
    leaf that holds the seal, as an equation between digests; and `AfterRuns` at whatever values
    the three chains have under g.
  `yes_of_left`: `Left` gives the value yes of the verifier of the file under g.

Who can give what. `climb`, `slotLt`, `pathLen`: they follow from the program's reading of the
place in the request tree and two hypotheses on how g answers at that tree's leaves and vertices.
`accept`: `Row.accept_app` (OnBytes/TypedOracleCompiler/Joined/K/RunsAt.lean), stage by stage.

Limits: one direction only. Nothing on soundness. `AfterRuns` is asked at all values that the runs
can have under g; under g they have one value each, so that is one instance. Nothing here says what
these values are. That g answers the query to g with the seal (`sealAt`: it speaks of the chaining
value in which the first chain ends), and that the verifier messages are the program's draws (they
decide which positions are read, and the decision), is owed by whoever shows `AfterRuns`: it rests
on how g answers the chains' queries.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.TypedOracleCompiler.Joined.JoinsAt
import OnBytes.TypedOracleCompiler.Joined.WalkAt
import OnBytes.TypedOracleCompiler.Joined.K.Count
import OnBytes.TypedOracleCompiler.Joined.K.RunsAt
import OnBytes.TypedOracleCompiler.Joined.K.YesRead

noncomputable section

namespace TypedOracleCompiler.Joined.K
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {W : QueryLayout lam L} {G : Chains} {Y : Type}
  {E : ExtSpec}

/-- What is asked at a proof string π and values a, b, e of the three chains. sl: the first chain's
seal as read. -/
structure AfterRuns (F : FileW W G Y E) (g : Fam (typedOracleFamily lam W.K L)) (sMT : ℕ)
    (cms : List (Dig lam)) (x : Y) (π : F.Prf) (sl : Dig lam) (a : Out lam G.c₁)
    (b : Out lam G.c₂) (e : Out lam G.c₃) : Prop where
  /-- g answers the query to g that holds the chaining value in which the first chain ends with that
  chain's seal as read -/
  sealAt : ∀ ρ₁, a.2.2 = .loc ρ₁ →
    g (OracleName.g F.t) (qSeal₁ F.t F.D F.embP π ρ₁ (rtJ F.D F.wq π a)) = sl
  /-- the openings at chain 1's rounds -/
  opened₁ : Opened sMT G.c₁ G.A₁ (wire₁ F.wq) a.2.1 (rd₁ F.D F.wq x π a b e) (op₁ F.D π)
  /-- at chain 2's rounds -/
  opened₂ : Opened sMT G.c₂ G.A₂ (wire₂ F.wq) b.2.1 (rd₂ F.D F.wq x π a b e) (op₂ F.D π)
  /-- at chain 3's rounds -/
  opened₃ : Opened sMT G.c₃ G.A₃ (wire₃ F.wq) e.2.1 (rd₃ F.D F.wq x π a b e) (op₃ F.D π)
  /-- the openings of the external strings -/
  openedE : OpenedE sMT F.wq.maxDepth F.wq.ext (readE F.D F.wq x (glue a b e).1) π.ext
  /-- the walk of each forest of chain 1's rounds ends, under g, in its trees' roots -/
  walk₁ : ∀ F₁,
    forestsB G.c₁ G.A₁ (wire₁ F.wq) (symb₁ F.embS) a.2.1 (rd₁ F.D F.wq x π a b e) (op₁ F.D π) =
      some F₁ → ∀ T ∈ F₁, walkP g T T.reads = true
  /-- of chain 2's rounds -/
  walk₂ : ∀ F₂,
    forestsB G.c₂ G.A₂ (wire₂ F.wq) (symb₂ F.embS) b.2.1 (rd₂ F.D F.wq x π a b e) (op₂ F.D π) =
      some F₂ → ∀ T ∈ F₂, walkP g T T.reads = true
  /-- of chain 3's rounds -/
  walk₃ : ∀ F₃,
    forestsB G.c₃ G.A₃ (wire₃ F.wq) (symb₃ F.embS) e.2.1 (rd₃ F.D F.wq x π a b e) (op₃ F.D π) =
      some F₃ → ∀ T ∈ F₃, walkP g T T.reads = true
  /-- of the external strings -/
  walkE : ∀ Fe,
    forestExt F.wq.ext F.embE cms (readE F.D F.wq x (glue a b e).1) π.ext = some Fe →
    ∀ T ∈ Fe, walkP g T T.reads = true
  /-- over the whole: the decision, at the three chains' transcripts in a row -/
  accept : F.D.accept x (F.wq.ext.build fun p => (π.ext p).map Opening.sym)
    (Tr.app (s := G.c₁) (t := G.c₂ ++ G.c₃) (tr₁ F.D F.wq π a)
      (Tr.app (s := G.c₂) (t := G.c₃) (tr₂ F.D F.wq π b) (tr₃ F.D F.wq π e))) = true

/-- **What is left to show for a yes**, at the proof string that is assembled from the three chains
as read k₁, k₂, k₃ and what belongs to no chain. sl: the first chain's seal as read. -/
structure Left (F : FileW W G Y E) (g : Fam (typedOracleFamily lam W.K L)) (sMT sFS : ℕ)
    (cms : List (Dig lam)) (x : Y) (sl : Dig lam) (salt : Bits) (k₁ : ChainStr lam G.c₁)
    (k₂ : ChainStr lam G.c₂) (k₃ : ChainStr lam G.c₃) (ext : E.Pos → Option (Opening lam E.Sym))
    (rtreq : Dig lam) (slot : ℕ) (path : List (Dig lam)) (rsalt : Bits) : Prop where
  /-- the joining round is a shared round, and its annotation is coherent -/
  laws : G.Laws
  /-- the laws of the wire record -/
  wire : F.wq.OKG
  /-- few trees a component, and as many roots read for each chain as its rounds have trees -/
  fits : Fits F k₁ k₂ k₃
  /-- chain 1's salt has sFS bits -/
  saltLen : salt.length = sFS
  /-- the slot's number is the number of a slot -/
  slotLt : slot < 2 ^ W.dReq F.t
  /-- the request path has one digest for each level -/
  pathLen : path.length = W.dReq F.t
  /-- the climb in the request tree, from the digest of the leaf that holds the seal and the string
  behind it, ends in the request root -/
  climb : climbP (rnodeAt g) path slot (g OracleName.rleaf (List.ofFn sl ++ rsalt)) = rtreq
  /-- what is asked at whatever values the three chains have under g -/
  after : ∀ a b e,
    (run₁ F.t F.D F.wq F.embP F.xin cms x
      (F.assemble salt k₁ k₂ k₃ ext rtreq slot path rsalt)).det g = some a →
    (run₂ F.t F.D F.wq F.embP F.xin cms x
      (F.assemble salt k₁ k₂ k₃ ext rtreq slot path rsalt) a).det g = some b →
    (run₃ F.t F.D F.wq F.embP F.xin cms x
      (F.assemble salt k₁ k₂ k₃ ext rtreq slot path rsalt) a b).det g = some e →
    AfterRuns F g sMT cms x (F.assemble salt k₁ k₂ k₃ ext rtreq slot path rsalt) sl a b e

/-- **`Left` gives the value yes of the verifier of the file under g.** -/
theorem yes_of_left {F : FileW W G Y E} {g : Fam (typedOracleFamily lam W.K L)} {sMT sFS : ℕ}
    {cms : List (Dig lam)} {x : Y} {sl : Dig lam} {salt : Bits} {k₁ : ChainStr lam G.c₁}
    {k₂ : ChainStr lam G.c₂} {k₃ : ChainStr lam G.c₃}
    {ext : E.Pos → Option (Opening lam E.Sym)} {rtreq : Dig lam} {slot : ℕ}
    {path : List (Dig lam)} {rsalt : Bits}
    (H : Left F g sMT sFS cms x sl salt k₁ k₂ k₃ ext rtreq slot path rsalt) :
    (F.verify sMT sFS cms x (F.assemble salt k₁ k₂ k₃ ext rtreq slot path rsalt)).det g =
      true := by
  obtain ⟨a, b, e, c, h₁, h₂, h₃, hr, hc⟩ :=
    F.runs_at H.laws g salt H.fits ext rtreq slot path rsalt cms x
  have A := H.after a b e h₁ h₂ h₃
  obtain ⟨ρ₁, e1, hg⟩ := slot_at H.laws h₁ h₂ h₃ hc
  have hsl : c = sl := hg.symm.trans (A.sealAt ρ₁ e1)
  obtain ⟨s₁, F₁, f₁, t₁⟩ :=
    A.opened₁.cuts (wire₁_okg H.wire) (wire₁_depthLe H.wire) (symb₁ F.embS)
  obtain ⟨s₂, F₂, f₂, t₂⟩ :=
    A.opened₂.cuts (wire₂_okg H.wire) (wire₂_depthLe H.wire) (symb₂ F.embS)
  obtain ⟨s₃, F₃, f₃, t₃⟩ :=
    A.opened₃.cuts (wire₃_okg H.wire) (wire₃_depthLe H.wire) (symb₃ F.embS)
  obtain ⟨sE, Fe, fE, tE⟩ := A.openedE.cuts F.embE cms
  exact F.yes_at (F₁ := F₁) (F₂ := F₂) (F₃ := F₃) (Fe := Fe) (c := c)
    { run₁ := h₁
      run₂ := h₂
      run₃ := h₃
      joined := hc
      salt := H.saltLen
      roots := hr
      slot := H.slotLt
      strict₁ := s₁
      strict₂ := s₂
      strict₃ := s₃
      strictE := sE
      forests₁ := f₁
      forests₂ := f₂
      forests₃ := f₃
      forestsE := fE
      count := count_of_forests H.wire f₁ f₂ f₃ fE
      fit₁ := t₁
      fit₂ := t₂
      fit₃ := t₃
      fitE := tE
      walk₁ := walk_at g (A.walk₁ F₁ f₁)
      walk₂ := walk_at g (A.walk₂ F₂ f₂)
      walk₃ := walk_at g (A.walk₃ F₃ f₃)
      walkE := walk_at g (A.walkE Fe fE)
      request := det_reqCheck g H.pathLen H.slotLt (by rw [hsl]; exact H.climb)
      accept := A.accept }

end TypedOracleCompiler.Joined.K
