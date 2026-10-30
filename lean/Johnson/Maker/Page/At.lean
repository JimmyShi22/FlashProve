-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Maker/Page/At.lean: the page (OnBytes/Maker/Page/Frame.lean, `PageJ`) at the typed interface
of the two makers' values and an entry's part (Johnson/Maker/Page/Type.lean, `LM`), and what of the
premises of OnBytes/Maker/Page/RowsAt.lean is met there.

At that interface the plain parts under the key file's and the proof file's tag are the plain parts
of the files' own rounds, by unfolding (`pb_test`, `pb_onl`): so the read-back of
OnBytes/Maker/Page/Fill.lean is `some`, and it undoes the embedding `id`.

  `rdK`, `rdP`: the two read-backs. `hrdK`, `hrdP`: they undo `id`.
  `keyM`, `proofM`: the two files' data: `fillJ` at the makers' data and at
    OnBytes/Maker/Page/Silent.lean's `silentKey`, `silentProof`.
  `p1M`: the plain part that the page's code of the seeds bears at its second query
    (OnBytes/TypedOracleCompiler/Run/SeedVals.lean, `plainFirst`). `p1M_front`: it is read as the front round's.
  `baseM`, `pageM`: the page: without, and with, the three spellings that are taken from elsewhere
    (OnBytes/Maker/Page/Holes.lean, `withHoles`: the entry file's, the seeds', the leaves'; the
    spare oracle's stays the one that writes nothing).
  `speaksK`, `speaksP`: the page's family answers by the two files' calls: under the key file's tag
    at the queries at which the seeds' code is silent; under the proof file's at all.
  `quietK`, `quietP`: the files' own chain queries are such queries.

h: the format's hash, from which the parameters' digests are made; at use `Fmt.HO O` for the same O
as in `gJ (pageM ..) O`: here the two are two letters. req: from an instance, two strings: the value
of the statement's item "request", then the request file's bytes.

To be minded. All letters of `pageM` are free. Lk, V (the entry file's code; a code of leaves), p0,
cfgL, sh, rest are letters too: no value is laid in for them, and the code that writes nothing is a
value of Lk and of V: at such a page every chain query of the entry file is answered by zeros.
`speaksK` and `speaksP` hold of every page, by unfolding `gJ`; what is particular to `pageM` is
`p1M_front` and `quietK`. late is a free letter, and a query of the format f2 that holds an instance
has no string: so for a proof file it is owed that late names no written round of the first and the
third chain (OnBytes/Maker/Page/RowsAt.lean: `late₁`, `late₃`). `pageM` is a term for statements,
not one that runs.

What is not claimed. That the verifiers at these values pass the identity as their embedding. That
the verifier's second query for the seeds bears `p1M`: no wire of the record is given at these
values. Nothing on a file as read: the premises of RowsAt.lean on readings, heads, statements and
run values stay premises. Nothing on leaves, vertices and the request tree. Nothing on the entry
file's tag.


-/
import Johnson.Maker.Page.Type
import OnBytes.Maker.Page.QuietPays
import OnBytes.Maker.Page.Silent

set_option autoImplicit false

namespace OnBytes.Maker.Page

open _root_.Run _root_.Run.PQ Iop Hiop OnBytes.Maker OnBytes.Flat OnBytes.RunA
open TypedOracleCompiler.Compile.Batch (PlainPart FbIn typedOracleFamily)
open TypedOracleCompiler.Run (SeedVals.plainFirst)
open TypedOracleCompiler.Run.SeedPage (LinkCode)
open TypedOracleCompiler.Run.PageG (Leaves)
open _root_.Compile.Joined (JoinMsg)

attribute [local instance] ConfLetters.finRnd ConfLetters.neRnd ConfLetters.finPad
  ConfLetters.nePad ConfLetters.finSeed ConfLetters.neSeed

variable {a : ℕ} (Kc : ConfLetters a) (f : _root_.Fmt.Fld)
  (tFk : FrontMsg (List E)) (tJk : JoinMsg (List E) ByteArray) (t3k : ByteArray)
  (tFp : FrontMsg (List E)) (tJp : JoinMsg (List E) ByteArray) (t3p : ByteArray)
  (silK : Kc.conf.Rec → FrontMsg (List E) → JoinMsg (List E) ByteArray → ByteArray → Bool)
  (silP : Kc.conf.X × Kc.conf.Rec → FrontMsg (List E) → JoinMsg (List E) ByteArray → ByteArray →
    Bool) (key : Kc.conf.Rec → TableKey)
  (k : Params.KeyChains) (rec₀ : Kc.conf.Rec) (c : Params.ProofChains)
  (block : Kc.conf.X → Blk Proof.FirstEnd) (z₀ : Kc.conf.X × Kc.conf.Rec) (p : LinkProtocolWithLeafCodingAndQueryLayout Kc.conf.Rec a
    (kM Kc f key k rec₀ c block z₀)) (N : ℕ) (early : Kc.conf.X → Kc.conf.X) (late : Option ℕ)
  (P : (filesM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early
    late).Provers)

/-- The read-back under the key file's tag. -/
def rdK (z : PBt (LM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late
    P) .test) :
    Option (PlainPart (chainsOf (ckP f) (dataK Kc key k rec₀) tFk tJk t3k).sh
      (chainsOf (ckP f) (dataK Kc key k rec₀) tFk tJk t3k).ann) := some z

/-- The read-back under the proof file's tag. -/
def rdP (z : PBt (LM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late
    P) .onl) :
    Option (PlainPart (chainsOf (ckP f) (dataP Kc key c block z₀) tFp tJp t3p).sh
      (chainsOf (ckP f) (dataP Kc key c block z₀) tFp tJp t3p).ann) := some z

theorem hrdK (w : PlainPart (chainsOf (ckP f) (dataK Kc key k rec₀) tFk tJk t3k).sh
    (chainsOf (ckP f) (dataK Kc key k rec₀) tFk tJk t3k).ann) : rdK Kc f tFk tJk t3k tFp tJp t3p
        silK silP key k rec₀ c block z₀ p N early late P w = some w := rfl

theorem hrdP (w : PlainPart (chainsOf (ckP f) (dataP Kc key c block z₀) tFp tJp t3p).sh
    (chainsOf (ckP f) (dataP Kc key c block z₀) tFp tJp t3p).ann) : rdP Kc f tFk tJk t3k tFp tJp t3p
        silK silP key k rec₀ c block z₀ p N early late P w = some w := rfl

/-- **The key file's data.** -/
noncomputable def keyM (h : HId) : FileJ (LM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c
    block z₀ p N early late P) .test :=
  fillJ (ckP f) (dataK Kc key k rec₀) tFk tJk t3k (rdK Kc f tFk tJk t3k tFp tJp t3p silK silP key k
      rec₀ c block z₀ p N early late P) (silentKey h k _)

/-- **The proof file's data.** -/
noncomputable def proofM (h : HId)
    (req : ((filesM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early
      late).withProvers P).XC → ByteArray × ByteArray) : FileJ (LM Kc f tFk tJk t3k tFp tJp t3p silK silP
                  key k rec₀ c
                  block z₀ p N early late P) .onl :=
  fillJ (ckP f) (dataP Kc key c block z₀) tFp tJp t3p (rdP Kc f tFk tJk t3k tFp tJp t3p silK silP
      key k rec₀ c block z₀ p N early late P) (silentProof h c req)

/-- The plain part that the page's code of the seeds bears at its second query. -/
def p1M : PBt (LM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P)
    .test :=
  SeedVals.plainFirst _ _ (chainsOf (ckP f) (dataK Kc key k rec₀) tFk tJk t3k).ann.1
    (chainsOf (ckP f) (dataK Kc key k rec₀) tFk tJk t3k).ann.2

/-- **It is read as the front round's message.** -/
theorem p1M_front :
    partAt (ckP f) (dataK Kc key k rec₀) tFk tJk t3k (rdK Kc f tFk tJk t3k tFp tJp t3p silK silP key
        k rec₀ c block z₀ p N early late P) (p1M Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀
        c block z₀ p N early late P) = .front tFk :=
  partOf_plainFirst (ckP f) (dataK Kc key k rec₀) tFk tJk t3k

/-- The page without the four spellings that are taken from elsewhere. -/
noncomputable def baseM (cfg : ByteArray) (sR : ℕ) (h : HId) (req : ((filesM Kc f tFk tJk t3k tFp
    tJp t3p silK silP key k rec₀ c block z₀ p N early
      late).withProvers P).XC → ByteArray × ByteArray) :
    PageJ (LM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P) (p.K +
      1) where
  cfg := cfg
  key := keyM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P h
  proof := proofM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P h
      req
  sR := sR
  leaf := leafOf fun b => b
  link := fun _ => none
  seeds := fun _ => none
  leafX := fun _ => none
  other := fun _ => none

section
variable (cfg : ByteArray) (sR : ℕ) (h : HId) (req : ((filesM Kc f tFk tJk t3k tFp tJp t3p silK silP
    key k rec₀ c block z₀ p N early
      late).withProvers P).XC → ByteArray × ByteArray)
  (p0 : PBt (LM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P)
      .test) (isP0 isP1 : PBt (LM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N
      early late P) .test → Bool) (cfgL : List (Dig 256))
  (sh : Rom.Bits) (hp0 : ∀ q, isP0 q = true ↔ q = p0) (hp1 : ∀ q, isP1 q = true ↔ q = p1M Kc f tFk
      tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P)
  (rest : ByteArray) (Lk : LinkCode (LM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀
    p N early late P) (p.K + 1)) (V : Leaves (LM Kc f tFk tJk t3k
      tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P))

/-- **The page.** -/
noncomputable def pageM : PageJ (LM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p
    N early late P) (p.K + 1) :=
  withHoles (LM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P) p0
      (p1M Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P) isP0
      isP1 cfgL sh hp0 hp1 rest (p.K + 1) (baseM Kc f tFk tJk t3k tFp
      tJp t3p silK silP key k rec₀ c block z₀ p N early late P cfg sR h req) Lk V

/-- **Under the key file's tag the page's family answers by the key file's calls**, at the queries
at which the seeds' code is silent. -/
theorem speaksK (O : ByteArray → ByteArray) :
    Speaks (gJ (pageM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late
        P cfg sR h req p0 isP0 isP1 cfgL sh hp0 hp1 rest Lk V) O) .test (keyM Kc f tFk tJk t3k tFp
        tJp t3p silK silP key k rec₀ c block z₀ p N early late P h) O
      (Quiet (LM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P) p0
          (p1M Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P) isP0
          isP1 cfgL sh hp0 hp1 rest (p.K + 1)) :=
  speaks_test (pageM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P
      cfg sR h req p0 isP0 isP1 cfgL sh hp0 hp1 rest Lk V) O

/-- **Under the proof file's tag it answers by the proof file's calls**, at every query. -/
theorem speaksP (O : ByteArray → ByteArray) :
    Speaks (gJ (pageM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late
        P cfg sR h req p0 isP0 isP1 cfgL sh hp0 hp1 rest Lk V) O) .onl
      (proofM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P h req)
          O (fun _ => True) :=
  speaks_onl (pageM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P
      cfg sR h req p0 isP0 isP1 cfgL sh hp0 hp1 rest Lk V) O _

/-- **The key file's own chain queries are queries at which the seeds' code is silent.** -/
theorem quietK (cms : List (Dig 256)) (x : Option ((filesM Kc f tFk tJk t3k tFp tJp t3p silK silP
    key k rec₀ c block z₀ p N early
      late).withProvers P).XC) (salt rtreq ρ0 c' : Rom.Bits)
    (pF : FrontMsg (List E)) (pJ : JoinMsg (List E) ByteArray) (p3 : ByteArray) :
    QuietAt (ckP f) (dataK Kc key k rec₀) tFk tJk t3k (rdK Kc f tFk tJk t3k tFp tJp t3p silK silP
        key k rec₀ c block z₀ p N early late P) (silentKey h k _)
      (Quiet (LM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P) p0
          (p1M Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P) isP0
          isP1 cfgL sh hp0 hp1 rest (p.K + 1)) (fun w => w) cms x salt
      rtreq ρ0 c' pF pJ p3 :=
  quietAt_test (ckP f) (dataK Kc key k rec₀) tFk tJk t3k (rdK Kc f tFk tJk t3k tFp tJp t3p silK silP
      key k rec₀ c block z₀ p N early late P) (silentKey h k _) (fun w => w)
    (hrdK Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P) (p1M Kc f
        tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P) tFk (p1M_front
        Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P) p0 isP0
        isP1 cfgL sh hp0 hp1 rest (p.K + 1) cms x salt rtreq
    ρ0 c' pF pJ p3

end

/-- The proof file's, at the condition that is always true. -/
theorem quietP (h : HId) (req : ((filesM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block
    z₀ p N early
      late).withProvers P).XC → ByteArray × ByteArray) (cms : List (Dig 256)) (x : Option ((filesM Kc f tFk
                  tJk t3k tFp
                  tJp t3p silK silP key k rec₀ c block z₀ p N early
              late).withProvers P).XC)
    (salt rtreq ρ0 c' : Rom.Bits) (pF : FrontMsg (List E)) (pJ : JoinMsg (List E) ByteArray)
    (p3 : ByteArray) :
    QuietAt (ckP f) (dataP Kc key c block z₀) tFp tJp t3p (rdP Kc f tFk tJk t3k tFp tJp t3p silK
        silP key k rec₀ c block z₀ p N early late P) (silentProof h c req)
      (fun _ => True) (fun w => w) cms x salt rtreq ρ0 c' pF pJ p3 :=
  quietAt_true (ckP f) (dataP Kc key c block z₀) tFp tJp t3p (rdP Kc f tFk tJk t3k tFp tJp t3p silK
      silP key k rec₀ c block z₀ p N early late P) (silentProof h c req)
    (fun w => w) cms x salt rtreq ρ0 c' pF pJ p3

end OnBytes.Maker.Page
