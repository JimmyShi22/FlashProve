-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryVerdict.lean: a verifier of an entry file on plain data, and that its yes is
a yes of the checker of the entry file, on the user's own commitment ID, whatever a converter has
handed over.

A call has a statement (`EntryStmt`: the user's commitment ID and the digest of the three public
files) and a value that an untrusted converter has made of the key file and the entry file
(`OnBytes.Tie.AskedE`: plain data). `verifyE` tests, on these two alone: that the pins fit the
description at the digest; that the chain as read gives a typed string; that the run's function
(`whyOutE`, OnBytes/TypedOracleCompiler/Slice/EntryRunMain.lean) says "YES" on the typed value, under the family
that a run evaluates; and that the commitment ID which the format makes of the digest, the shape and
the value's first root, first seeds and first answers is the user's.

Main names:
  `EntryStmt`, `verifyE`. `valueOf`: the typed value that is made of what a converter hands over.
  `verifyE_facts`: what the verifier's yes says, unfolded. `verdict_of_facts`: from these facts to
    the checker.
  `verifyE_yes`: for every value a: if the verifier says yes, there is a typed value o with two
    roots, the user's ID is the commitment ID of o's first root, first seeds and first answers, and
    the checker at every converter returns o, under the oracle made from the format's hash, on all
    files of which that converter makes o.
  `verifyE_roots`: the roots of `valueOf`'s value are the two tables' roots in what the converter
    has handed over. `verifyE_yes_roots`: `verifyE_yes` with these two roots named.
  `playFull`: a play at the full size.

Not claimed. All of this is at one fixed oracle, the one made from the format's hash: no probability
stands here. The bound on the checker (OnBytes/TypedOracleCompiler/Slice/EntryFullTop.lean, EntrySmallTop.lean) is
over a uniformly random oracle; what joins the two is the usual step of an argument in the random
oracle model, and no theorem. That the verifier says yes on any value. Nothing on a program, on
bytes read from a disk, or on an exit code. One file of three. Nothing on an honest prover.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryRunAny
import OnBytes.TypedOracleCompiler.Slice.EntryRunTieX

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD bodyS)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open OnBytes.Tie (EntryGround linkAtCfg keyAt AskedE)
open OnBytes.Slice (Tab s0Of)
open OnBytes.Slice.Shapes (Files FileSpec Size Cfg dgOf dgOf_size pubS₀ pubS₁)
open OnBytes.Slice.Shapes.FileSpec (own₀ own₁)
open scoped ENNReal

/-- The statement of a call: what the user gave. -/
structure EntryStmt where
  /-- the commitment ID, in hexadecimal signs -/
  id : String
  /-- the digest of the three public files -/
  c : ByteArray
  /-- it has 32 bytes -/
  hc : c.size = 32

variable (G : EntryGround)
  (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)

/-- The typed value that is made of what a converter hands over, at a digest c; nothing where the
chain as read gives no typed string. -/
noncomputable def valueOf (eM : ℕ) (a : AskedE) : (homeOf G hok eM).ConvC :=
  fun c _ _ =>
    (assembleS (entryXD G c)
      (decRun (linkAtCfg G.q c) G.q.link.table.v G.q.link.table.cubeBits G.q.link.table.answers)
      a.out).map fun π =>
      ([_root_.Run.bytesToDig a.first.root, _root_.Run.bytesToDig a.further.root],
        xOfAskedC _ _ a, ofPS _ _ π)

/-- The verifier of a call: on the statement x and on what a converter has handed over: the pins
fit the description at x's digest; the chain as read gives a typed string; the run's function says
"YES" on the typed value, under the family that a run evaluates; and the commitment ID that the
format makes of the digest, the shape, the first table's root, its seeds and its answers in that
value is the user's. -/
def verifyE (x : EntryStmt) (a : AskedE) : Bool :=
  pinsFit (entryXD G x.c) G.q.link.table &&
    match assembleS (entryXD G x.c)
      (decRun (linkAtCfg G.q x.c) G.q.link.table.v G.q.link.table.cubeBits G.q.link.table.answers)
      a.out with
    | none => false
    | some π =>
      (whyOutE (entryXD G x.c) (hok x.c x.hc) (d1Run _ _) _
        (EntryRunTop.famOf (entryXD G x.c) x.hc (d1Run _ _) G.q.link.table)
        [_root_.Run.bytesToDig a.first.root, _root_.Run.bytesToDig a.further.root]
        (xOfAskedC _ _ a) π == "YES") &&
      (stmtId G.q.link.table x.c (_root_.Run.bytesToDig a.first.root)
        (xOfAskedC G.q.link.table.cubeBits G.q.link.table.answers a).2.1
        (xOfAskedC G.q.link.table.cubeBits G.q.link.table.answers a).1.1 == x.id)

/-- What the verifier's yes says, unfolded. -/
theorem verifyE_facts (eM : ℕ) (x : EntryStmt) (a : AskedE) (h : verifyE G hok x a = true) :
    pinsFit (entryXD G x.c) G.q.link.table = true ∧
      ∃ o : (homeOf G hok eM).OutC x.c x.hc, ∀ d, valueOf G hok eM a x.c x.hc d = some o ∧
        whyOutE (entryXD G x.c) (hok x.c x.hc) (d1Run _ _)
          (decRun (linkAtCfg G.q x.c) G.q.link.table.v G.q.link.table.cubeBits
            G.q.link.table.answers)
          (EntryRunTop.famOf (entryXD G x.c) x.hc (d1Run _ _) G.q.link.table) o.1 o.2.1
          (toPS _ _ o.2.2) = "YES" ∧
        x.id = stmtId G.q.link.table x.c (o.1.getD 0 default) o.2.1.2.1 o.2.1.1.1 := by
  unfold verifyE at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hp, h⟩ := h
  refine ⟨hp, ?_⟩
  cases has : assembleS (entryXD G x.c)
      (decRun (linkAtCfg G.q x.c) G.q.link.table.v G.q.link.table.cubeBits G.q.link.table.answers)
      a.out with
  | none =>
    rw [has] at h
    exact absurd h Bool.false_ne_true
  | some π =>
    rw [has] at h
    dsimp only at h
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
    refine ⟨⟨[_root_.Run.bytesToDig a.first.root, _root_.Run.bytesToDig a.further.root],
      xOfAskedC _ _ a, ofPS _ _ π⟩, fun d => ⟨?_, h.1, h.2.symm⟩⟩
    unfold valueOf
    exact congrArg (Option.map fun π =>
      ([_root_.Run.bytesToDig a.first.root, _root_.Run.bytesToDig a.further.root],
        xOfAskedC _ _ a, ofPS _ _ π)) has

/-- From these facts to the checker, at a digest c that the oracle's own first table holds. -/
theorem verdict_of_facts (eM : ℕ) (cfg : Cfg) (a : AskedE) (εs : ℝ≥0∞) (Bk : ℕ) (id : String)
    (c : ByteArray) (h32 : c.size = 32)
    (hc : c = dgOf cfg (own₀ (pubS₀ cfg) _root_.Run.oBits))
    (hpd : own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) _root_.Run.oBits
      (s0Of ((homeOf G hok eM).prm c)) = EntryRunTop.pdOf ((homeOf G hok eM).DX c))
    (hp : pinsFit (entryXD G c) G.q.link.table = true) (o : (homeOf G hok eM).OutC c h32)
    (ho : ∀ d, valueOf G hok eM a c h32 d = some o)
    (hy : whyOutE (entryXD G c) (hok c h32) (d1Run _ _)
      (decRun (linkAtCfg G.q c) G.q.link.table.v G.q.link.table.cubeBits G.q.link.table.answers)
      (EntryRunTop.famOf (entryXD G c) h32 (d1Run _ _) G.q.link.table) o.1 o.2.1
      (toPS _ _ o.2.2) = "YES")
    (hid : id = stmtId G.q.link.table c (o.1.getD 0 default) o.2.1.2.1 o.2.1.1.1) :
    ∃ o' : (homeOf G hok eM).Out cfg (own₀ (pubS₀ cfg) _root_.Run.oBits)
        (own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) _root_.Run.oBits),
      o'.1.length = 2 ∧ id = stmtId G.q.link.table c (o'.1.getD 0 default) o'.2.1.2.1 o'.2.1.1.1 ∧
      ∀ (conv' : (homeOf G hok eM).Conv cfg) (d' : Files),
        conv' (own₀ (pubS₀ cfg) _root_.Run.oBits)
          (own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) _root_.Run.oBits) d' = some o' →
        ((((homeOf G hok eM).spec cfg conv' εs Bk).toO (pubS₀ cfg)
          (pubS₁ [(homeOf G hok eM).prm] cfg) (own₀ (pubS₀ cfg) _root_.Run.oBits)
          (own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) _root_.Run.oBits)).chk d').det
            _root_.Run.oBits = some o' := by
  have d₀ : Files := ⟨ByteArray.empty, ByteArray.empty, ByteArray.empty, ByteArray.empty,
    ByteArray.empty⟩
  have h := (homeOf G hok eM).yes_of_runX cfg (valueOf G hok eM a) G.q.link.table εs Bk d₀ c h32 hc
    ⟨rfl, hpd, rfl, salt_of_pinsFit _ _ hp, rfl⟩ h32 o (ho d₀) hy
  obtain ⟨o', ho', hs⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨hl, ha⟩ := (homeOf G hok eM).any_conv cfg _ εs Bk _root_.Run.oBits d₀ o' ho'
  have h1 : o'.1 = o.1 := congrArg Prod.fst hs
  have h2 : o'.2.1 = o.2.1 := congrArg Prod.snd hs
  refine ⟨o', hl, ?_, ha⟩
  rw [h1, h2]
  exact hid

/-- The verifier's yes is a yes of the entry file's checker, on the user's own commitment ID,
whatever the converter has handed over. cfg: three public files within the bound of the format's
hash; x: a statement whose digest is theirs. For every a: if the verifier says yes on x and a, then
there is a typed value o with two roots, the user's ID is the commitment ID that the format makes of
o's first root, first seeds and first answers, and the checker at every converter returns o, under
the oracle made from the format's hash, on all files of which that converter makes o. At that one
fixed oracle: no probability stands here. -/
theorem verifyE_yes (eM : ℕ) (cfg : Cfg)
    (hb : (_root_.Fmt.configBytes [cfg.pol, cfg.lay, cfg.KL]).size ≤ 2 ^ 32 - 144) (x : EntryStmt)
    (hx : x.c = OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]) (a : AskedE)
    (εs : ℝ≥0∞) (Bk : ℕ) (h : verifyE G hok x a = true) :
    ∃ o : (homeOf G hok eM).Out cfg (own₀ (pubS₀ cfg) _root_.Run.oBits)
        (own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) _root_.Run.oBits),
      o.1.length = 2 ∧ x.id = stmtId G.q.link.table x.c (o.1.getD 0 default) o.2.1.2.1 o.2.1.1.1 ∧
      ∀ (conv' : (homeOf G hok eM).Conv cfg) (d' : Files),
        conv' (own₀ (pubS₀ cfg) _root_.Run.oBits)
          (own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) _root_.Run.oBits) d' = some o →
        ((((homeOf G hok eM).spec cfg conv' εs Bk).toO (pubS₀ cfg)
          (pubS₁ [(homeOf G hok eM).prm] cfg) (own₀ (pubS₀ cfg) _root_.Run.oBits)
          (own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) _root_.Run.oBits)).chk d').det
            _root_.Run.oBits = some o := by
  obtain ⟨hp, o, ho⟩ := verifyE_facts G hok eM x a h
  have d₀ : Files := ⟨ByteArray.empty, ByteArray.empty, ByteArray.empty, ByteArray.empty,
    ByteArray.empty⟩
  have hpd := (homeOf G hok eM).pd_own₁ cfg hb
    (params_le_of_ok _ (hok _ (OnBytes.Params.configurationDigest_size _)))
    (homeOf_prm G hok eM _)
  rw [← hx] at hpd
  exact verdict_of_facts G hok eM cfg a εs Bk x.id x.c x.hc
    (hx.trans (OnBytes.Slice.Shapes.dgOf_own₀ cfg hb).symm) hpd hp o (fun d => (ho d).1)
    (ho d₀).2.1 (ho d₀).2.2

/-- The roots of the typed value that is made of what a converter hands over (`valueOf`): they are
the two tables' roots in it. No yes of the verifier is asked. -/
theorem verifyE_roots (eM : ℕ) (x : EntryStmt) (a : AskedE)
    (o : (homeOf G hok eM).OutC x.c x.hc) (d : Files)
    (ho : valueOf G hok eM a x.c x.hc d = some o) :
    o.1 = [_root_.Run.bytesToDig a.first.root, _root_.Run.bytesToDig a.further.root] := by
  unfold valueOf at ho
  obtain ⟨π, -, rfl⟩ := Option.map_eq_some_iff.1 ho
  rfl

/-- The same as `verifyE_yes`, with the two roots named: the typed value's roots are the roots
of the two tables in what the converter has handed over, in that order. -/
theorem verifyE_yes_roots (eM : ℕ) (cfg : Cfg)
    (hb : (_root_.Fmt.configBytes [cfg.pol, cfg.lay, cfg.KL]).size ≤ 2 ^ 32 - 144) (x : EntryStmt)
    (hx : x.c = OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]) (a : AskedE)
    (εs : ℝ≥0∞) (Bk : ℕ) (h : verifyE G hok x a = true) :
    ∃ o : (homeOf G hok eM).Out cfg (own₀ (pubS₀ cfg) _root_.Run.oBits)
        (own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) _root_.Run.oBits),
      o.1 = [_root_.Run.bytesToDig a.first.root, _root_.Run.bytesToDig a.further.root] ∧
      x.id = stmtId G.q.link.table x.c (_root_.Run.bytesToDig a.first.root) o.2.1.2.1 o.2.1.1.1 ∧
      ∀ (conv' : (homeOf G hok eM).Conv cfg) (d' : Files),
        conv' (own₀ (pubS₀ cfg) _root_.Run.oBits)
          (own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) _root_.Run.oBits) d' = some o →
        ((((homeOf G hok eM).spec cfg conv' εs Bk).toO (pubS₀ cfg)
          (pubS₁ [(homeOf G hok eM).prm] cfg) (own₀ (pubS₀ cfg) _root_.Run.oBits)
          (own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) _root_.Run.oBits)).chk d').det
            _root_.Run.oBits = some o := by
  obtain ⟨hp, o, ho⟩ := verifyE_facts G hok eM x a h
  have d₀ : Files := ⟨ByteArray.empty, ByteArray.empty, ByteArray.empty, ByteArray.empty,
    ByteArray.empty⟩
  have hr := verifyE_roots G hok eM x a o d₀ (ho d₀).1
  have hpd := (homeOf G hok eM).pd_own₁ cfg hb
    (params_le_of_ok _ (hok _ (OnBytes.Params.configurationDigest_size _)))
    (homeOf_prm G hok eM _)
  rw [← hx] at hpd
  have hc := hx.trans (OnBytes.Slice.Shapes.dgOf_own₀ cfg hb).symm
  have hy := (homeOf G hok eM).yes_of_runX cfg (valueOf G hok eM a) G.q.link.table εs Bk d₀ x.c
    x.hc hc ⟨rfl, hpd, rfl, salt_of_pinsFit _ _ hp, rfl⟩ x.hc o (ho d₀).1 (ho d₀).2.1
  obtain ⟨o', ho', hs⟩ := Option.map_eq_some_iff.1 hy
  obtain ⟨-, ha⟩ := (homeOf G hok eM).any_conv cfg _ εs Bk _root_.Run.oBits d₀ o' ho'
  have h1 : o'.1 = o.1 := congrArg Prod.fst hs
  have h2 : o'.2.1 = o.2.1 := congrArg Prod.snd hs
  refine ⟨o', h1.trans hr, ?_, ha⟩
  have hid := (ho d₀).2.2
  rw [hr] at hid
  rw [h2]
  exact hid

/-- A play at the full size. -/
def playFull (safe lax : Bool) (dm : Dmg) (pol lay kl key ent : ByteArray) : String × String :=
  playE OnBytes.Tie.recordGround record_ok OnBytes.Params.stdFull safe lax dm pol lay kl key ent

end TypedOracleCompiler.Slice
