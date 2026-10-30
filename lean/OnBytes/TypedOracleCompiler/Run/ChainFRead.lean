-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/ChainFRead.lean: THE WHOLE CHAIN OF THE TYPED VERIFIER FROM THREE YESES OF THE
STRICT READER: Run/ChainF.lean's chain_whole with its reader's side paid by Run/StretchRead.lean and
its two seals by Run/SealDigest.lean; READ AT THE READER's OWN o₁ | o₂ | o₃. A piece of "the tie at
H_b" for a proof file (LinkF). The compiler under OnBytes/TypedOracleCompiler/ is the one that
`innerCompiledVerifier` is made with; it builds on definitions of Compile/.
  endOf_trace        behind a trace the reader's chain has its label and as many rounds more as were
                     read
  forall₂_getLast    two lists that agree round by round agree in their last rounds
  sealRead o         the digest that the LAST round read draws (empty bytes if there is none)
  take_all           a list whose rest behind n is empty is its first n
  rtAll_same         rtAll hangs on the five fields alone
  ReadF          WHAT IS ASKED, IN ONE RECORD: three yeses of Fmt.readChainX at HO O, EACH CHAIN
                 UNDER ITS OWN PLAN S_k.base.plan (nothing is asked between the three plans); THE
                 DESCRIPTIONS: chain 1's rounds are rs₁ and one sealed round without items behind
                 them; FitL and room for ds₁ | ds₂ | ds₃; ds₂ ends in a sealed round; each chain has
                 a round; THE TYPED PLAIN PARTS are those of the rounds
                     read (chain 1: its first |rs₁|): what assemble3 lays; THE LAWS ON g: RowLo |
                     RowShS | RowEnd, s0, GAt, s4, s3, EACH AT THE READER's OWN VALUES (o_k.rho0;
                     sealRead o₁ | o₂)
  chain_whole_read    under ReadF, the kit fitting each chain's own field: the chain says some (ρ,
                      rtAll …, .aft v' (sealRead o₁ as a digest)); D.r₁ ρ | D.r₃ ρ draw what o₁'s
                      first rounds | o₃'s rounds drew; D.r₂ ρ what o₂'s drew up to SEAL 2's digest;
                      ALL TYPED TESTS OF WORK PASS
WHAT IS NOT SAID. THAT ANY g HAS THE LAWS (F's page). "fit", "room", the sealed rounds' clauses: the
description's (that the port's three descriptions are D's lists). That the twin's reader is
Fmt.readChainX at HO O. THAT THE PORT's ChainRead.seal IS sealRead. That o_k.rho0 is the format's
first value.
What follows the chain. A table with a record.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.StretchRead

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
    TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open _root_.Run.Twin (allLo)
open _root_.Fmt (RoundOut ChainOut Item ItemValue)
open TypedOracleCompiler.Slice (shA annLoS annShS wLoS wShS plF plS shdS wireSh ofR BD)

theorem endOf_trace (h : HId) (P : _root_.Fmt.Plan) :
    ∀ (rs : List _root_.Fmt.Round) (ros : List RoundOut) (c : _root_.Fmt.Chain)
        (roots : Array ByteArray),
      TraceL h P rs ros c roots →
      (endOf h rs ros c).label = c.label ∧ (endOf h rs ros c).round = c.round + rs.length
  | [], [], _, _, _ => ⟨rfl, rfl⟩
  | [], _ :: _, _, _, t => t.elim
  | _ :: _, [], _, _, t => t.elim
  | r :: rs, ro :: ros, c, roots, t => by
      obtain ⟨a, b⟩ := endOf_trace h P rs ros (nextOf h c r ro) _ t.2.2.2.2.2
      refine ⟨a, b.trans ?_⟩
      show c.round + 1 + rs.length = c.round + (rs.length + 1)
      omega

theorem forall₂_getLast {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ a, l.getLast? = some a → ∃ b,
        l'.getLast? = some b ∧ R a b
  | _, _, .nil, _, e => by cases e
  | [_], [y], .cons h .nil, _, e => by
      cases Option.some.inj e
      exact ⟨y, rfl, h⟩
  | _ :: x' :: l, _ :: y' :: l', .cons _ (.cons h' t), a, e => by
      rw [List.getLast?_cons_cons] at e
      obtain ⟨b, hb, hr⟩ := forall₂_getLast (.cons h' t) a e
      exact ⟨b, by rw [List.getLast?_cons_cons]; exact hb, hr⟩

theorem fitL_nil : ∀ ds : List RD, FitL ds [] → ds = []
  | [], _ => rfl
  | _ :: _, h => h.elim

theorem trace_rho32' (h : HId) (P : _root_.Fmt.Plan) (rs : List _root_.Fmt.Round)
    (ros : List RoundOut)
    (c : _root_.Fmt.Chain) (roots : Array ByteArray) (hne : rs ≠ [])
        (t : TraceL h P rs ros c roots) : c.rho.size = 32 := by
  obtain ⟨r, rs', rfl⟩ := List.exists_cons_of_ne_nil hne
  exact trace_rho32 h P r rs' ros c roots t

/-- the digest that the last round read draws -/
def sealRead (o : ChainOut) : ByteArray := ((o.rounds.toList.getLast?).bind (·.drawn.digest)).getD
    ByteArray.empty

theorem take_all {α : Type} (l : List α) (n : ℕ) (h : l.drop n = []) : l.take n = l :=
  List.take_of_length_le (List.drop_eq_nil_iff.1 h)

theorem rtAll_same (D : BD) (rtF : List (Dig 256)) {a a' b b' c c' : List RoundOut}
    (ha : List.Forall₂ Same5 a a')
    (hb : List.Forall₂ Same5 b b') (hc : List.Forall₂ Same5 c c') :
        rtAll D rtF a b c = rtAll D rtF a' b' c' := by
  unfold rtAll
  rw [rtSL_same D.G.C D.G.ds₁ a a' ha, rtShL_same D.G.C D.G.ds₂ b b' hb,
      rtSL_same D.G.C D.G.ds₃ c c' hc]

section
variable {I X : Type} {Lf : Unit → BatchProtocolWithLeafBody I X} {t : Tag} (D : BD)
  (embP : PlainPart D.shS D.annS → PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t))
  (K : ℕ) (g : Fam (typedOracleFamily 256 (K + 1) (Lf ()))) (early : X → X) (late : Option ℕ)
  (cms : List (Dig 256)) (x : Option X) (salt : Bits) (rtreq : Dig 256)
  (O : ByteArray → ByteArray)

/-- What is asked. -/
structure ReadF (pls : Plains D.shS) (rtF : List (Dig 256)) (S₁ S₂ S₃ : _root_.Fmt.SpecX)
    (o₁ o₂ o₃ : ChainOut)
    (rs₁ : List _root_.Fmt.Round) (rS : _root_.Fmt.Round) : Prop where
  /-- three yeses of the strict reader -/
  read₁ : ∃ seen b i j, _root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO O) S₁ seen b i = some (o₁, j)
  read₂ : ∃ seen b i j, _root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO O) S₂ seen b i = some (o₂, j)
  read₃ : ∃ seen b i j, _root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO O) S₃ seen b i = some (o₃, j)
  /-- the descriptions -/
  rounds₁ : S₁.base.rounds = rs₁ ++ [rS]
  sKind : rS.kind = .sealed
  sItems : rS.items = []
  sPoss : rS.entry.poss = 0
  sTrits : rS.entry.trits = 0
  sDrawE : rS.entry.drawE = 0
  sDrawNZ : rS.entry.drawNZ = 0
  sWork : rS.entry.work = 0
  fit₁ : FitL D.G.ds₁ rs₁
  fit₂ : FitL D.G.ds₂ S₂.base.rounds
  fit₃ : FitL D.G.ds₃ S₃.base.rounds
  room₁ : ∀ r ∈ rs₁, _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost r.entry r.kind) ≤ K
  room₂ : ∀ r ∈ S₂.base.rounds, _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost r.entry r.kind) ≤ K
  room₃ : ∀ r ∈ S₃.base.rounds, _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost r.entry r.kind) ≤ K
  seal₂ : SealLast D.G.ds₂
  some₁ : rs₁ ≠ []
  some₃ : S₃.base.rounds ≠ []
  /-- the front's roots -/
  front : D.F.depths.length = rtF.length
  front2 : rtF.length ≤ TypedOracleCompiler.Iop.maxRt
  /-- the typed plain parts are those of the rounds read -/
  plains₁ : plainsSL D.G.C D.G.ds₁ (o₁.rounds.toList.take rs₁.length) = some
      (plF D.G.C D.SJ D.G.ds₁ pls.2)
  plains₂ : plainsSL D.G.C D.G.ds₂ o₂.rounds.toList = some (plF D.G.C D.S₃ D.G.ds₂ (qJ D pls).2)
  plains₃ : plainsSL D.G.C D.G.ds₃ o₃.rounds.toList = some (q3 D pls).2
  /-- the laws on g -/
  row₁ : RowLo Lf D.G.C K g t O S₁.base.label D.SJ D.annSJ D.G.ds₁
      (fun z => embP (Sum.inr z)) 1 (0 + 1)
  row₂ : RowShS Lf D.G.C K g t O S₂.base.label D.S₃ D.annS₃ D.G.ds₂ (fun z => eJ D embP (Sum.inr z))
    (1 + D.G.ds₁.length + 1) (0 + 1)
  row₃ : RowEnd Lf D.G.C K g t O S₃.base.label D.G.ds₃ (fun z => e3 D embP (Sum.inr z))
    (1 + D.G.ds₁.length + 1 + D.G.ds₂.length + 1) (0 + 1)
  s0 : (g (OracleName.fb t) (⟨0, .f1 cms (x.map early) salt, rtF, embP (Sum.inl (Sum.inr pls.1))⟩ :
              FbIn 256 (Lf ()) t) :
    (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig o₁.rho0
  sG : GAt Lf K g t O S₁.base.label (eJ D embP (Sum.inl (Sum.inr (D.aJ.plain (qJ D pls).1).2)))
      (1 + D.G.ds₁.length)
    (0 + rs₁.length + 1)
  s4 : (g (OracleName.fb t) (⟨1 + D.G.ds₁.length, .f4 cms (List.ofFn rtreq), [],
              eJ D embP (Sum.inl (Sum.inl (D.aJ.plain (qJ D pls).1).1))⟩ : FbIn 256 (Lf ()) t) :
    (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig o₂.rho0
  s3 : (g (OracleName.fb t) (⟨1 + D.G.ds₁.length + 1 + D.G.ds₂.length,
              .f3 (List.ofFn (bytesToDig (sealRead o₂))) (List.ofFn (bytesToDig (sealRead o₁))), [],
              e3 D embP (Sum.inl (Sum.inr (q3 D pls).1))⟩ : FbIn 256 (Lf ()) t) :
    (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig o₃.rho0
  late₁ : ∀ k, k < D.G.ds₁.length → late ≠ some (1 + k)
  late₃ : ∀ k, k < D.G.ds₃.length → late ≠ some (1 + D.G.ds₁.length + 1 + D.G.ds₂.length + 1 + k)

variable (chal : ∀ e k, (Fin K → Dig 256) → D.G.C.Ch e k) (o : D.G.Ones)
  (hO : ∀ s, (O s).size = 32)

include hO in
/-- THE WHOLE CHAIN FROM THREE YESES OF THE STRICT READER. -/
theorem chain_whole_read (pls : Plains D.shS) (rtF rest : List (Dig 256))
    (S₁ S₂ S₃ : _root_.Fmt.SpecX) (o₁ o₂ o₃ : ChainOut)
    (rs₁ : List _root_.Fmt.Round) (rS : _root_.Fmt.Round)
    (hkit₁ : KitFits S₁.base.plan.field D.G.C K chal)
        (hkit₂ : KitFits S₂.base.plan.field D.G.C K chal)
    (hkit₃ : KitFits S₃.base.plan.field D.G.C K chal)
    (A : ReadF D embP K g early late cms x salt rtreq O pls rtF S₁ S₂ S₃ o₁ o₂ o₃ rs₁ rS) :
    ∃ (ρ : Rho D.shS) (v' : Bits),
      chainP Lf g early late t cms x salt rtreq D.S D.annS (D.wiresS K chal o) embP 0 .first
          (rtF ++ (rootsD (o₁.rounds.toList.take rs₁.length) ++ (rootsD o₂.rounds.toList ++
            (rootsD o₃.rounds.toList ++ rest)))) pls =
        some (ρ, rtAll D rtF (o₁.rounds.toList.take rs₁.length) o₂.rounds.toList o₃.rounds.toList,
          .aft v' (bytesToDig (sealRead o₁))) ∧
      drawnSL D.G.C D.G.ds₁ (D.r₁ ρ) = (o₁.rounds.toList.take rs₁.length).map (·.drawn) ∧
      SameButSeal (drawnSL D.G.C D.G.ds₂ (D.r₂ ρ)) (o₂.rounds.toList.map (·.drawn)) ∧
      drawnSL D.G.C D.G.ds₃ (D.r₃ ρ) = o₃.rounds.toList.map (·.drawn) ∧
      passSL D.G.C D.G.ds₁ (D.r₁ ρ) = true ∧ passSL D.G.C D.G.ds₂ (D.r₂ ρ) = true ∧
      passSL D.G.C D.G.ds₃ (D.r₃ ρ) = true := by
  obtain ⟨sn₁, b₁, i₁, j₁, e₁⟩ := A.read₁
  obtain ⟨sn₂, b₂, i₂, j₂, e₂⟩ := A.read₂
  obtain ⟨sn₃, b₃, i₃, j₃, e₃⟩ := A.read₃
  -- the three readers' sides
  obtain ⟨ros₁, rosS, pl₁, rt₁', F₁, w₁, tS, -, m₁, mS⟩ :=
    stretch_of_read O S₁ sn₁ b₁ i₁ o₁ j₁ e₁ D.G.C K D.G.ds₁ rs₁ [rS] A.rounds₁ A.fit₁ A.room₁
  obtain ⟨ros₂, n₂, pl₂, rt₂', F₂, w₂, t₂', -, m₂, m₂'⟩ :=
    stretch_of_read O S₂ sn₂ b₂ i₂ o₂ j₂ e₂ D.G.C K D.G.ds₂ S₂.base.rounds []
        (List.append_nil _).symm A.fit₂ A.room₂
  obtain ⟨ros₃, n₃, pl₃, rt₃', F₃, w₃, t₃', -, m₃, m₃'⟩ :=
    stretch_of_read O S₃ sn₃ b₃ i₃ o₃ j₃ e₃ D.G.C K D.G.ds₃ S₃.base.rounds []
        (List.append_nil _).symm A.fit₃ A.room₃
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
  have hp₁ : pl₁ = plF D.G.C D.SJ D.G.ds₁ pls.2 :=
    Option.some.inj ((F₁.plains.symm.trans (plainsSL_same D.G.C D.G.ds₁ _ _ m₁)).trans A.plains₁)
  have hp₂ : pl₂ = plF D.G.C D.S₃ D.G.ds₂ (qJ D pls).2 :=
    Option.some.inj ((F₂.plains.symm.trans (plainsSL_same D.G.C D.G.ds₂ _ _ m₂)).trans A.plains₂)
  have hp₃ : pl₃ = (q3 D pls).2 :=
    Option.some.inj ((F₃.plains.symm.trans (plainsSL_same D.G.C D.G.ds₃ _ _ m₃)).trans A.plains₃)
  subst hp₁
  subst hp₂
  subst hp₃
  -- SEAL 1
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
  have sr₁ : sealRead o₁ = sealG O (endOf (_root_.Fmt.HO O) rs₁ ros₁ ⟨S₁.base.label, o₁.rho0, 0⟩) :=
      by
    have hl : o₁.rounds.toList.getLast? = some y₁ := by
      rw [← List.take_append_drop rs₁.length o₁.rounds.toList, ed₁]
      simp
    unfold sealRead
    rw [hl]
    show (y₁.drawn.digest).getD ByteArray.empty = _
    rw [← hy₁.2.2.2.1, dS]
    rfl
  -- SEAL 2
  obtain ⟨x₂, hx₂, dx₂⟩ := sealOf_digest O hO S₂.base.plan D.G.ds₂ S₂.base.rounds ros₂ _ _ A.seal₂
      A.fit₂ F₂.trace
  obtain ⟨y₂, hy₂, hs₂⟩ := forall₂_getLast m₂ x₂ hx₂
  have sr₂ : sealRead o₂ = sealOf (_root_.Fmt.HO O) S₂.base.rounds ros₂
      ⟨S₂.base.label, o₂.rho0, 0⟩ := by
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
  -- (G)'s law at the chain behind the first stretch
  obtain ⟨lE, rE⟩ := endOf_trace (_root_.Fmt.HO O) S₁.base.plan rs₁ ros₁ _ _ F₁.trace
  have hG : GAt Lf K g t O (endOf (_root_.Fmt.HO O) rs₁ ros₁ ⟨S₁.base.label, o₁.rho0, 0⟩).label
      (eJ D embP (Sum.inl (Sum.inr (D.aJ.plain (qJ D pls).1).2))) (1 + D.G.ds₁.length)
      ((endOf (_root_.Fmt.HO O) rs₁ ros₁ ⟨S₁.base.label, o₁.rho0, 0⟩).round + 1) := by
    rw [lE, rE]
    exact A.sG
  have s3 := A.s3
  rw [sr₁, sr₂] at s3
  obtain ⟨ρ, v', E, d1, d2, d3, p1, p2, p3⟩ := chain_whole D embP K chal o g early late cms x salt
      rtreq O hO S₁.base.plan S₂.base.plan
    S₃.base.plan hkit₁ hkit₂ hkit₃ pls rtF
    rest A.front A.front2 rs₁ S₂.base.rounds S₃.base.rounds ros₁ ros₂ ros₃
        ⟨S₁.base.label, o₁.rho0, 0⟩
    ⟨S₂.base.label, o₂.rho0, 0⟩ ⟨S₃.base.label, o₃.rho0, 0⟩ #[] #[] #[] F₁ F₂ F₃ A.seal₂ A.row₁
        A.row₂ A.row₃ z₁ z₂ z₃
    (sealG O (endOf (_root_.Fmt.HO O) rs₁ ros₁ ⟨S₁.base.label, o₁.rho0, 0⟩)) A.s0 hG.sG A.s4 s3
        A.late₁ A.late₃
  refine ⟨ρ, v', ?_, ?_, ?_, ?_, p1.trans w₁, p2.trans w₂, p3.trans w₃⟩
  · rw [← rootsD_same _ _ m₁, ← rootsD_same _ _ m₂, ← rootsD_same _ _ m₃,
      ← rtAll_same D rtF m₁ m₂ m₃, sr₁]
    exact E
  · rw [← drawn_same _ _ m₁]
    exact d1
  · rw [← drawn_same _ _ m₂]
    exact d2
  · rw [← drawn_same _ _ m₃]
    exact d3

end

end TypedOracleCompiler.Run.PQ
