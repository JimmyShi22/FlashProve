-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/K/RunsLineRead.lean: the three chains of a file's verifier, and its whole chain,
under fixed oracle functions, from three yeses of the strict reader of chains.

A part of the tie between a reader of a file's bytes and the second form of the compiler's verifier
side (lean/OnBytes/TypedOracleCompiler/Joined/): it brings that verifier's yes, under fixed oracle functions, down
to conditions on what was read and on how these functions answer. That the reading of a real file,
and oracle functions made from the programs' hash, meet these conditions is not shown in this
folder.


`whole_line` (OnBytes/TypedOracleCompiler/Joined/K/RunsLine.lean) takes the reader's side as facts on stretches
(`StretchFacts`) and the two seals as letters. Here both are paid as
OnBytes/TypedOracleCompiler/Run/ChainFRead.lean pays them for `chain_whole`: the facts by `stretch_of_read`
(OnBytes/TypedOracleCompiler/Run/StretchRead.lean), the seals by OnBytes/TypedOracleCompiler/Run/SealDigest.lean. All is said at the
reader's own outputs o₁, o₂, o₃.

Main names:
  `ReadL`: what is asked, in one record: three yeses of `Fmt.readChainX` at the hash O, each chain
    under its own plan (read₁ to read₃); the descriptions: the first chain's rounds are rs₁ and one
    sealed round rS (rounds₁, sKind), which has no item, draws no position, trit or element and asks
    no work (sItems, sPoss, sTrits, sDrawE, sDrawNZ, sWork); the lists ds₁, ds₂, ds₃ fit (fit₁ to
    fit₃); K blocks are enough for the verifier message of every round but rS (room₁ to room₃); the
    shared chain ends in a sealed round (seal₂); rs₁ and the last chain's rounds are not empty
    (some₁, some₃); the file's wire records are the written rounds' (wire₁ to wire₃); the joining
    round is shared and its wire has no tree (joinSh, joinJ, join0); the front's and the seam's own
    roots are as many as the trees over a slot's component in their wires (`depthJ`), and at most
    `maxRt` (front, front2, seam, seam2); the proof string's roots and plain parts are those of the
    rounds read (roots, plains₁ to plains₃); the laws on g, each at the reader's own values (row₁ to
    row₃, s0, sG, s4, s3); the condition on the round "late" for the first and the last chain
    (late₁, late₃).
  `whole_line_read`: under `ReadL`, O's answers having 32 bytes (hO) and the kit fitting each
    chain's field (hkit₁ to hkit₃): the three chains have values under g; so has the whole chain,
    and its last phase holds the first chain's seal as read (`sealRead o₁`) as the slot value; the
    stretches' verifier messages draw what the reader drew (the shared chain's up to its seal's
    digest); all typed tests of work pass.

Limits: those of RunsLine.lean. One kit (C, K, chal) serves all three chains: it must fit the field
of each chain's plan. That any g has the laws, and that any file's wire records are the
written rounds', is not shown here. That a program's reader is `Fmt.readChainX` at O is not said.
The three yeses are three separate facts: nothing in `ReadL` says that the three chains were read
off one file, one behind the other. There is a condition on the round "late" for the first and the
last chain and none for the shared one: a shared round's query never holds an instance.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.TypedOracleCompiler.Run.ChainFRead
import OnBytes.TypedOracleCompiler.Joined.K.RunsLine

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Joined.K
open Rom TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin TypedOracleCompiler.Run.Thin
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ
open _root_.Run.PQ (CK)
open _root_.Run (bytesToDig bitsToBytes)
open _root_.Run.Twin (RS up allLo allLo_eq)
open _root_.Fmt (Chain RoundOut ChainOut)
open _root_.Compile.Joined (Chains Desc)

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {Y : Type} {E : ExtSpec} {C : CK} {K : ℕ} {rF rJ r3 : RS}
  {aJ : RAnn rJ.up} {ds₁ ds₂ ds₃ : List RD} {t : Tag}
  {D : Desc (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃) Y E}

/-- **What is asked.** -/
structure ReadL (wq : ProtocolQueryLayout 256 (K + 1) D.batch)
    (embP : PlainPart (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).sh (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).ann →
      PlainPart (shapeOf L t) (annOf L t))
    (xin : Y → Option X) (cms : List (Dig 256)) (x : Y) (π : OneProtocolProof 256 D.batch)
    (g : Fam (typedOracleFamily 256 (K + 1) L)) (O : ByteArray → ByteArray)
    (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (wF : WireRB 256 (K + 1) rF.up rF.lo)
    (wJ : WireRB 256 (K + 1) rJ.up aJ) (w3 : WireRB 256 (K + 1) r3.up r3.lo)
    (rtF rt3 rest : List (Dig 256)) (S₁ S₂ S₃ : _root_.Fmt.SpecX) (o₁ o₂ o₃ : ChainOut)
    (rs₁ : List _root_.Fmt.Round) (rS : _root_.Fmt.Round) : Prop where
  /-- three yeses of the strict reader -/
  read₁ : ∃ seen b i j,
    _root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO O) S₁ seen b i = some (o₁, j)
  read₂ : ∃ seen b i j,
    _root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO O) S₂ seen b i = some (o₂, j)
  read₃ : ∃ seen b i j,
    _root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO O) S₃ seen b i = some (o₃, j)
  /-- the descriptions -/
  rounds₁ : S₁.base.rounds = rs₁ ++ [rS]
  sKind : rS.kind = .sealed
  sItems : rS.items = []
  sPoss : rS.entry.poss = 0
  sTrits : rS.entry.trits = 0
  sDrawE : rS.entry.drawE = 0
  sDrawNZ : rS.entry.drawNZ = 0
  sWork : rS.entry.work = 0
  fit₁ : FitL ds₁ rs₁
  fit₂ : FitL ds₂ S₂.base.rounds
  fit₃ : FitL ds₃ S₃.base.rounds
  room₁ : ∀ r ∈ rs₁, _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost r.entry r.kind) ≤ K
  room₂ : ∀ r ∈ S₂.base.rounds, _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost r.entry r.kind) ≤ K
  room₃ : ∀ r ∈ S₃.base.rounds, _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost r.entry r.kind) ≤ K
  seal₂ : SealLast ds₂
  some₁ : rs₁ ≠ []
  some₃ : S₃.base.rounds ≠ []
  /-- the file's wire records are the front's, the joining round's, the seam's, and the written
  rounds' -/
  wire₁ : wire₁ wq = wTo (allLo_eq (rF :: SL C ds₁)) (wF, wiresSL C K chal ds₁)
  wire₂ : wire₂ wq = wTo (annL₂ C rF rJ r3 aJ ds₁ ds₂ ds₃) (wireW₂ C K chal rJ aJ wJ ds₂)
  wire₃ : wire₃ wq = wTo (allLo_eq (r3 :: SL C ds₃)) (w3, wiresSL C K chal ds₃)
  /-- the joining round is shared and has no tree -/
  joinSh : aJ.kind = Kind.sh
  joinJ : wJ.depthJ = []
  join0 : wJ.depth0 = []
  /-- the front's roots, and the seam's -/
  front : wF.depthJ.length = rtF.length
  front2 : rtF.length ≤ TypedOracleCompiler.Iop.maxRt
  seam : w3.depthJ.length = rt3.length
  seam2 : rt3.length ≤ TypedOracleCompiler.Iop.maxRt
  /-- the proof string's roots are the front's, those of the rounds read, with the seam's before
  the last chain's, and a rest -/
  roots : π.roots = rtF ++ (rootsD (o₁.rounds.toList.take rs₁.length) ++
    (rootsD o₂.rounds.toList ++ (rt3 ++ (rootsD o₃.rounds.toList ++ rest))))
  /-- the typed plain parts are those of the rounds read -/
  plains₁ : plainsSL C ds₁ (o₁.rounds.toList.take rs₁.length) = some (pls₁ D π).2
  plains₂ : plainsSL C ds₂ o₂.rounds.toList = some (pls₂ D π).2
  plains₃ : plainsSL C ds₃ o₃.rounds.toList = some (pls₃ D π).2
  /-- the laws on g -/
  row₁ : RowEnd (fun _ => L) C K g t O S₁.base.label ds₁ (fun z => embL₁ embP (Sum.inr z)) (0 + 1)
    (0 + 1)
  row₂ : RowShE (fun _ => L) C K g t O S₂.base.label ds₂ (fun z => embL₂ embP (Sum.inr z))
    (0 + (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁.length + 1) (0 + 1)
  row₃ : RowEnd (fun _ => L) C K g t O S₃.base.label ds₃ (fun z => embL₃ embP (Sum.inr z))
    (0 + (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁.length +
      (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₂.length + 1) (0 + 1)
  s0 : (g (OracleName.fb t) (⟨0, .f1 cms ((xin x).map L.early) π.salt, rtF,
              embL₁ embP (Sum.inl (Sum.inr (pls₁ D π).1))⟩ : FbIn 256 L t) :
    (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig o₁.rho0
  sG : GAt (fun _ => L) K g t O S₁.base.label
    (embL₂ embP (Sum.inl (Sum.inr (aJ.plain (pls₂ D π).1).2)))
    (0 + (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁.length) (0 + rs₁.length + 1)
  s4 : (g (OracleName.fb t) (⟨0 + (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁.length,
              .f4 cms (List.ofFn π.rtreq), [], embL₂ embP (Sum.inl (Sum.inl (aJ.plain (pls₂ D π).1).1))⟩ :
            FbIn 256 L t) : (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig o₂.rho0
  s3 : (g (OracleName.fb t) (⟨0 + (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁.length +
              (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₂.length,
              .f3 (List.ofFn (bytesToDig (sealRead o₂))) (List.ofFn (bytesToDig (sealRead o₁))), rt3,
              embL₃ embP (Sum.inl (Sum.inr (pls₃ D π).1))⟩ : FbIn 256 L t) :
    (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig o₃.rho0
  /-- no instance is written into a query, or the round "late" is none of the stretch's -/
  late₁ : xin x = none ∨ ∀ k, k < ds₁.length → L.late ≠ some (0 + 1 + k)
  late₃ : xin x = none ∨ ∀ k, k < ds₃.length →
    L.late ≠ some (0 + (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁.length +
      (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₂.length + 1 + k)

variable {wq : ProtocolQueryLayout 256 (K + 1) D.batch}
  {embP : PlainPart (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).sh (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).ann →
    PlainPart (shapeOf L t) (annOf L t)}
  {xin : Y → Option X} {cms : List (Dig 256)} {x : Y} {π : OneProtocolProof 256 D.batch}
  {g : Fam (typedOracleFamily 256 (K + 1) L)} {O : ByteArray → ByteArray}
  {chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k} {wF : WireRB 256 (K + 1) rF.up rF.lo}
  {wJ : WireRB 256 (K + 1) rJ.up aJ} {w3 : WireRB 256 (K + 1) r3.up r3.lo}
  {rtF rt3 rest : List (Dig 256)} {S₁ S₂ S₃ : _root_.Fmt.SpecX} {o₁ o₂ o₃ : ChainOut}
  {rs₁ : List _root_.Fmt.Round} {rS : _root_.Fmt.Round}

/-- **THE THREE CHAINS' VALUES, AND THE WHOLE CHAIN'S, UNDER g, FROM THREE YESES OF THE STRICT
READER.** -/
theorem whole_line_read (hO : ∀ s, (O s).size = 32)
    (hkit₁ : KitFits S₁.base.plan.field C K chal) (hkit₂ : KitFits S₂.base.plan.field C K chal)
    (hkit₃ : KitFits S₃.base.plan.field C K chal)
    (A : ReadL wq embP xin cms x π g O chal wF wJ w3 rtF rt3 rest S₁ S₂ S₃ o₁ o₂ o₃ rs₁ rS) :
    ∃ (a : Out 256 (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁)
      (b : Out 256 (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₂)
      (e : Out 256 (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₃) (v' : Bits),
      (run₁ t D wq embP xin cms x π).det g = some a ∧
      (run₂ t D wq embP xin cms x π a).det g = some b ∧
      (run₃ t D wq embP xin cms x π a b).det g = some e ∧
      (recomputeChainOfProof t D.batch wq embP xin cms x π).det g = some (glue a b e) ∧
      (glue a b e).2.2 = .aft v' (bytesToDig (sealRead o₁)) ∧
      a.2.1 = ((none, some rtF), rtSL C ds₁ (o₁.rounds.toList.take rs₁.length)) ∧
      b.2.1 = ((some [], some []), rtShL C ds₂ o₂.rounds.toList) ∧
      e.2.1 = ((none, some rt3), rtSL C ds₃ o₃.rounds.toList) ∧
      drawnSL C ds₁ a.1.2 = (o₁.rounds.toList.take rs₁.length).map (·.drawn) ∧
      SameButSeal (drawnSL C ds₂ b.1.2) (o₂.rounds.toList.map (·.drawn)) ∧
      drawnSL C ds₃ e.1.2 = o₃.rounds.toList.map (·.drawn) ∧
      passSL C ds₁ a.1.2 = true ∧ passSL C ds₂ b.1.2 = true ∧ passSL C ds₃ e.1.2 = true := by
  obtain ⟨sn₁, b₁, i₁, j₁, e₁⟩ := A.read₁
  obtain ⟨sn₂, b₂, i₂, j₂, e₂⟩ := A.read₂
  obtain ⟨sn₃, b₃, i₃, j₃, e₃⟩ := A.read₃
  -- the three readers' sides
  obtain ⟨ros₁, rosS, pl₁, rt₁', F₁, w₁, tS, -, m₁, mS⟩ :=
    stretch_of_read O S₁ sn₁ b₁ i₁ o₁ j₁ e₁ C K ds₁ rs₁ [rS] A.rounds₁ A.fit₁ A.room₁
  obtain ⟨ros₂, n₂, pl₂, rt₂', F₂, w₂, t₂', -, m₂, m₂'⟩ :=
    stretch_of_read O S₂ sn₂ b₂ i₂ o₂ j₂ e₂ C K ds₂ S₂.base.rounds [] (List.append_nil _).symm
      A.fit₂ A.room₂
  obtain ⟨ros₃, n₃, pl₃, rt₃', F₃, w₃, t₃', -, m₃, m₃'⟩ :=
    stretch_of_read O S₃ sn₃ b₃ i₃ o₃ j₃ e₃ C K ds₃ S₃.base.rounds [] (List.append_nil _).symm
      A.fit₃ A.room₃
  -- whole chains
  have z₂ : n₂ = [] := by cases n₂ with | nil => rfl | cons _ _ => exact t₂'.elim
  have z₃ : n₃ = [] := by cases n₃ with | nil => rfl | cons _ _ => exact t₃'.elim
  subst z₂
  subst z₃
  have a₂ : o₂.rounds.toList.take S₂.base.rounds.length = o₂.rounds.toList :=
    take_all _ _ (List.forall₂_nil_left_iff.1 m₂')
  have a₃ : o₃.rounds.toList.take S₃.base.rounds.length = o₃.rounds.toList :=
    take_all _ _ (List.forall₂_nil_left_iff.1 m₃')
  rw [a₂] at m₂
  rw [a₃] at m₃
  -- the typed plain parts are the string's
  have hp₁ : pl₁ = (pls₁ D π).2 :=
    Option.some.inj ((F₁.plains.symm.trans (plainsSL_same C ds₁ _ _ m₁)).trans A.plains₁)
  have hp₂ : pl₂ = (pls₂ D π).2 :=
    Option.some.inj ((F₂.plains.symm.trans (plainsSL_same C ds₂ _ _ m₂)).trans A.plains₂)
  have hp₃ : pl₃ = (pls₃ D π).2 :=
    Option.some.inj ((F₃.plains.symm.trans (plainsSL_same C ds₃ _ _ m₃)).trans A.plains₃)
  subst hp₁
  subst hp₂
  subst hp₃
  -- the first seal
  obtain ⟨y₁, l₁, hy₁, hl₁, ed₁⟩ : ∃ y l, Same5 (rosS.headD y) y ∧ rosS = [rosS.headD y] ∧
      o₁.rounds.toList.drop rs₁.length = y :: l ∧ l = [] := by
    cases rosS with
    | nil => exact tS.elim
    | cons ro l =>
      cases l with
      | cons _ _ => exact tS.2.2.2.2.2.elim
      | nil =>
        obtain ⟨y, l', hy, hl', e⟩ := List.forall₂_cons_left_iff.1 mS
        exact ⟨y, l', hy, rfl, e, List.forall₂_nil_left_iff.1 hl'⟩
  obtain ⟨ed₁, rfl⟩ := ed₁
  rw [hl₁] at tS
  have dS := sealG_digest O hO S₁.base.plan rS _ _ _ A.sKind A.sItems A.sPoss A.sTrits A.sDrawE
    A.sDrawNZ A.sWork tS
  have sr₁ : sealRead o₁ =
      sealG O (endOf (_root_.Fmt.HO O) rs₁ ros₁ ⟨S₁.base.label, o₁.rho0, 0⟩) := by
    have hl : o₁.rounds.toList.getLast? = some y₁ := by
      rw [← List.take_append_drop rs₁.length o₁.rounds.toList, ed₁]
      simp
    unfold sealRead
    rw [hl]
    show (y₁.drawn.digest).getD ByteArray.empty = _
    rw [← hy₁.2.2.2.1, dS]
    rfl
  -- the second seal
  obtain ⟨x₂, hx₂, dx₂⟩ := sealOf_digest O hO S₂.base.plan ds₂ S₂.base.rounds ros₂ _ _ A.seal₂
    A.fit₂ F₂.trace
  obtain ⟨y₂, hy₂, hs₂⟩ := forall₂_getLast m₂ x₂ hx₂
  have sr₂ : sealRead o₂ =
      sealOf (_root_.Fmt.HO O) S₂.base.rounds ros₂ ⟨S₂.base.label, o₂.rho0, 0⟩ := by
    unfold sealRead
    rw [hy₂]
    show (y₂.drawn.digest).getD ByteArray.empty = _
    rw [← hs₂.2.2.2.1, dx₂]
    rfl
  -- the first values have 32 bytes
  have ne₂ : S₂.base.rounds ≠ [] := by
    intro h
    have hf := A.fit₂
    rw [h] at hf
    have hs := A.seal₂
    rw [fitL_nil _ hf] at hs
    exact hs.elim
  have z₁ := trace_rho32' (_root_.Fmt.HO O) S₁.base.plan rs₁ ros₁ _ _ A.some₁ F₁.trace
  have z₂ := trace_rho32' (_root_.Fmt.HO O) S₂.base.plan _ ros₂ _ _ ne₂ F₂.trace
  have z₃ := trace_rho32' (_root_.Fmt.HO O) S₃.base.plan _ ros₃ _ _ A.some₃ F₃.trace
  -- the law of the query to g, at the chain behind the first stretch
  obtain ⟨lE, rE⟩ := endOf_trace (_root_.Fmt.HO O) S₁.base.plan rs₁ ros₁ _ _ F₁.trace
  have hG : GAt (fun _ => L) K g t O
      (endOf (_root_.Fmt.HO O) rs₁ ros₁ ⟨S₁.base.label, o₁.rho0, 0⟩).label
      (embL₂ embP (Sum.inl (Sum.inr (aJ.plain (pls₂ D π).1).2)))
      (0 + (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁.length)
      ((endOf (_root_.Fmt.HO O) rs₁ ros₁ ⟨S₁.base.label, o₁.rho0, 0⟩).round + 1) := by
    rw [lE, rE]
    exact A.sG
  have s3 := A.s3
  rw [sr₁, sr₂] at s3
  have hroots := A.roots
  rw [← rootsD_same _ _ m₁, ← rootsD_same _ _ m₂, ← rootsD_same _ _ m₃] at hroots
  obtain ⟨a, b, e, v', E1, E2, E3, EW, hph, ra, rb, re, d1, d2, d3, p1, p2, p3⟩ :=
    whole_line g O hO S₁.base.plan S₂.base.plan S₃.base.plan chal hkit₁ hkit₂ hkit₃ wF wJ w3
      A.joinSh A.joinJ A.join0 A.wire₁ A.wire₂ A.wire₃ rtF rt3 rest rs₁ S₂.base.rounds
      S₃.base.rounds ros₁ ros₂ ros₃ ⟨S₁.base.label, o₁.rho0, 0⟩ ⟨S₂.base.label, o₂.rho0, 0⟩
      ⟨S₃.base.label, o₃.rho0, 0⟩ #[] #[] #[] hroots A.front A.front2 A.seam A.seam2 F₁ F₂ F₃
      A.seal₂ A.row₁ A.row₂ A.row₃ z₁ z₂ z₃
      (bytesToDig (sealG O (endOf (_root_.Fmt.HO O) rs₁ ros₁ ⟨S₁.base.label, o₁.rho0, 0⟩))) A.s0
      hG.sG A.s4 s3 A.late₁ A.late₃
  refine ⟨a, b, e, v', E1, E2, E3, EW, ?_, ?_, ?_, ?_, ?_, ?_, ?_, p1.trans w₁, p2.trans w₂,
    p3.trans w₃⟩
  · rw [sr₁]
    exact hph
  · rw [← rtSL_same C ds₁ _ _ m₁]
    exact ra
  · rw [← rtShL_same C ds₂ _ _ m₂]
    exact rb
  · rw [← rtSL_same C ds₃ _ _ m₃]
    exact re
  · rw [← drawn_same _ _ m₁]
    exact d1
  · rw [← drawn_same _ _ m₂]
    exact d2
  · rw [← drawn_same _ _ m₃]
    exact d3

end TypedOracleCompiler.Joined.K
