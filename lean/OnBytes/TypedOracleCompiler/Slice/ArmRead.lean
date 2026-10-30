-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/ArmRead.lean: what `chain_one_read` (OnBytes/TypedOracleCompiler/Run/ChainERead.lean) asks for one
chain (`PQ.ReadE`), over a second interface L2 and at the typed oracle functions that the encoding
`ArmRounds.implAt` reads out of an oracle g: from one reading of an entry's chain at the hash over g
(`EntryRead`, OnBytes/TypedOracleCompiler/Slice/EntryChain.lean).

Over L2 the link's first query holds both tables' roots and, behind them, both tables' typed answers
as digests; its field for the instance is empty:
  ⟨0, f1 (c₀ :: c₁ :: (cA an ++ cA an')) none salt, [], pbF.symm (p0E …)⟩.
It is written directly by `lf0` (OnBytes/TypedOracleCompiler/Run/LinkFirstAns.lean) as the string of the hash under
160 on the program's own statement of a link's chain. The later rounds' queries are those of the
entry's page, with the plain part carried by `pbF.symm`.

Main theorems.
 `first_arm`     THE FIRST QUERY's LAW: the chain value of the answer at that query is the first
                 value o.rho0 of the chain as read.
 `readE_arm`     `PQ.ReadE` over L2: its row law by `ArmRows.rowEnd_arm`, its first query's law by
                 `first_arm`, the rest from `EntryRead`.
 `chainP_arm`    the typed chain over L2 (`chain_one_read` at `readE_arm`), with K digests in a
                 verifier's message, for ANY K from D.K on and any wire that fits the field.
 `chain_arm`     THE CHAIN's HALF OF THE COMPILED LAX VERIFIER OVER L2 (`ArmChain.chain_at_none`
                 at `readE_arm`): at a typed string whose salt is the run value's bits, whose roots
                 begin with the roots that were read and whose plain parts are those of the rounds
                 read, the chain returns; it draws what the reader drew; all tests of work pass.

Asked beside `EntryRead`: tr writes the typed answers an, an' as the two tables' answers' triples;
cA and tr are one to one, cA with one number of digests; `FitsE D`; D.K ≤ K; K + 1 below 2 ^ 48.
Nothing is asked of the late round of L2: no instance is handed to the chain, so the chain does not
look at it (`chainP_late_none`, OnBytes/TypedOracleCompiler/Run/ArmChainNone.lean). K, the number of digests in a
verifier's message, is a letter: a wire over L2 may have more than the description needs.

Not claimed. That any reading has `EntryRead`. That L2, pbF, bd, cA, tr exist as asked. pbF is a
letter here, but whoever joins this chain with a verifier over L2 has no choice of it: the way of
the plain parts here is `wayE`, then `pbF.symm`, and it must be that verifier's own way. Nothing on
soundness.


-/
import OnBytes.TypedOracleCompiler.Run.ArmRows
import OnBytes.TypedOracleCompiler.Run.ArmCodes
import OnBytes.TypedOracleCompiler.Run.ArmChainNone
import OnBytes.TypedOracleCompiler.Run.LinkFirstAns
import OnBytes.TypedOracleCompiler.Slice.EntryChain

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice.ArmRead
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.Apart TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.RowsG TypedOracleCompiler.Run.RowsE2
open TypedOracleCompiler.Run.EntryFb TypedOracleCompiler.Run.EntryPage TypedOracleCompiler.Slice.EntryFill
open TypedOracleCompiler.Slice.EntryChain
open TypedOracleCompiler.Run.LinkFirstAns TypedOracleCompiler.Run.ArmRounds TypedOracleCompiler.Run.ArmRows
open TypedOracleCompiler.Run.ArmDirect
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD)
open OnBytes.Slice (seedEntry)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {lg s : ℕ} (D : XD) (d₁ : Sd1 lg s) (cfg : ByteArray) (hcfg : cfg.size = 32)
  (pd : Dig 256) (rest1 : ByteArray) (V : Leaves (Ls D d₁)) (K : ℕ)
  {I2 X2 : Type} (L2 : BatchProtocolWithLeafBody I2 X2)
  (pbF : PlainPart (shapeOf L2 .link) (annOf L2 .link) ≃
    PlainPart (shapeOf (Ls D d₁) .link) (annOf (Ls D d₁) .link))
  (bd : L2.Bd ≃ (Ls D d₁).Bd)
  (p0 p1 : PlainPart (shapeOf L2 .test) (annOf L2 .test))
  (isP0 isP1 : PlainPart (shapeOf L2 .test) (annOf L2 .test) → Bool) (cfgL : List (Dig 256)) (sh : Bits)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1) (rest : ByteArray)
  (isPL : PlainPart (shapeOf L2 .link) (annOf L2 .link) → Bool)
  (hpL : ∀ p, isPL p = true ↔
    p = pbF.symm (p0E D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s)))
  {An : Type} (cA : An → List (Dig 256)) (tr : An → List T3) (hinj : Function.Injective cA)
  (hlen : ∀ a a', (cA a).length = (cA a').length) (htr : Function.Injective tr)
  (back : StrCode (AllPts 256 (K + 1) L2)) (g : Fam (rom 256))

/-- The encoding over L2, with Kb digests in a verifier's message: the link's first query by `lf0`;
the later rounds and the leaves by the codes of the entry's page at the pins `pinsE`, carried. -/
abbrev implL2 (Kb : ℕ) (back : StrCode (AllPts 256 Kb L2)) : OracleCoding (typedOracleFamily 256 Kb L2) 256 :=
  implAt (pinsE D d₁ cfg hcfg pd rest1) Kb V L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest
    (lf0 L2 .link (pbF.symm (p0E D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s))) isPL pd
      cA tr hpL hinj hlen htr OnBytes.Params.labelLink)
    (lf0_is L2 .link _ isPL pd cA tr hpL hinj hlen htr OnBytes.Params.labelLink) back

/-- **The first query's law over L2**: the chain value is the first value of the chain as read. -/
theorem first_arm (first further : OnBytes.Params.TableName) (c₀ c₁ : Dig 256)
    (S : _root_.Fmt.SpecX) (o : _root_.Fmt.ChainOut) (run : ByteArray)
    (pls : Plains (PQ.uL D.C D.ds)) (A : EntryRead D pd g first further c₀ c₁ S o run pls)
    (an an' : An) (a₀ : tr an = first.answers.map OnBytes.E.triple)
    (a₁ : tr an' = further.answers.map OnBytes.E.triple) :
    (readBlocks (implL2 D d₁ cfg hcfg pd rest1 V L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest isPL
        hpL cA tr hinj hlen htr (K + 1) back) g (.fb .link)
        ⟨0, .f1 (c₀ :: c₁ :: (cA an ++ cA an')) none (bytesToBits run), [],
          pbF.symm (p0E D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s))⟩ :
        (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig o.rho0 := by
  obtain ⟨seen, b, i, j, e⟩ := A.read
  obtain ⟨x, i0, hd, -, hst, hrun, hrho⟩ := OnBytes.Tie.readX_head _ S seen b i o j e
  have hl : (bytesToBits run).length = 256 := by rw [length_bytesToBits, A.run32]
  have hv : runOf (bytesToBits run) = some run :=
    runOf_saltOf (some run) fun r e0 => by rw [← Option.some.inj e0]; exact A.run32
  have hs := lf0_link L2 .link
    (pbF.symm (p0E D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s))) isPL pd cA tr hpL
    hinj hlen htr OnBytes.Params.labelLink first further c₀ c₁ an an' (bytesToBits run) A.root₀
    A.root₁ a₀ a₁ A.few₀ A.few₁ (Or.inr hl)
  rw [hv] at hs
  have hf := head_first _ _ _ _ _ hd hst
  rw [hrun, A.runIs, hrho, A.label, A.pdIs, A.stm] at hf
  rw [hf]
  exact first_of_code _ g .link _ OnBytes.Params.labelLink (digToBytes pd)
    (OnBytes.Params.Link.statement first further) ByteArray.empty (some run)
    (armD_code_first L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest (K + 1) OnBytes.Params.labelLink _ _
      _ _ _ _ _ _ V cfg hcfg back _ rfl _ hs)

/-- **What `chain_one_read` asks, over L2**, where no instance is handed to the chain, at no late
round. early2: how the chain over L2 would name an instance early: not used. -/
theorem readE_arm (F : FitsE D) (hDK : D.K ≤ K) (hK : K + 1 < 2 ^ 48) (early2 : X2 → X2)
    (first further : OnBytes.Params.TableName) (c₀ c₁ : Dig 256)
    (S : _root_.Fmt.SpecX) (o : _root_.Fmt.ChainOut) (run : ByteArray)
    (pls : Plains (PQ.uL D.C D.ds)) (A : EntryRead D pd g first further c₀ c₁ S o run pls)
    (an an' : An) (a₀ : tr an = first.answers.map OnBytes.E.triple)
    (a₁ : tr an' = further.answers.map OnBytes.E.triple) :
    PQ.ReadE (fun _ : Unit => L2) D.C K
      (readBlocks (implL2 D d₁ cfg hcfg pd rest1 V L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest
        isPL hpL cA tr hinj hlen htr (K + 1) back) g)
      early2 none .link (c₀ :: c₁ :: (cA an ++ cA an')) none (bytesToBits run) (oB (g ())) D.ds
      (fun z => pbF.symm (wayE D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s) z)) pls S
      o where
  read := A.read
  fit := A.fit
  room := fun r hr => Nat.le_trans (A.room r hr) hDK
  hasRound := A.hasRound
  plains := A.plains
  row := by
    rw [A.label]
    exact rowEnd_arm (pinsE D d₁ cfg hcfg pd rest1) K V L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1
      rest _ _ back g F hK
  first := first_arm D d₁ cfg hcfg pd rest1 V K L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest isPL
    hpL cA tr hinj hlen htr back g first further c₀ c₁ S o run pls A an an' a₀ a₁
  noLate := fun _ _ h => by cases h

/-- **The typed chain over L2, with K digests in a verifier's message**, for any K from D.K on, at
any wire `chal` that fits the description's field: `chain_one_read` at `readE_arm`. -/
theorem chainP_arm (F : FitsE D) (hDK : D.K ≤ K) (hK : K + 1 < 2 ^ 48) (early2 : X2 → X2)
    (late2 : Option ℕ) (first further : OnBytes.Params.TableName) (c₀ c₁ : Dig 256)
    (S : _root_.Fmt.SpecX) (o : _root_.Fmt.ChainOut) (run : ByteArray)
    (pls : Plains (PQ.uL D.C D.ds)) (A : EntryRead D pd g first further c₀ c₁ S o run pls)
    (an an' : An) (a₀ : tr an = first.answers.map OnBytes.E.triple)
    (a₁ : tr an' = further.answers.map OnBytes.E.triple)
    (chal : ∀ e k, (Fin K → Dig 256) → D.C.Ch e k)
    (hkit : _root_.Run.PQ.KitFits S.base.plan.field D.C K chal) (rtreq : Dig 256)
    (more : List (Dig 256)) :
    ∃ (ρ : Rho (_root_.Run.Twin.up (PQ.SOf D.C D.ds))) (v' : Bits),
      TypedOracleCompiler.Run.Thin.chainP (fun _ : Unit => L2)
          (readBlocks (implL2 D d₁ cfg hcfg pd rest1 V L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1
            rest isPL hpL cA tr hinj hlen htr (K + 1) back) g)
          early2 late2 .link (c₀ :: c₁ :: (cA an ++ cA an')) none (bytesToBits run) rtreq
          (PQ.SOf D.C D.ds) (_root_.Run.Twin.allLo (PQ.SOf D.C D.ds))
          (PQ.wire0S D.C K chal, PQ.wiresSL D.C K chal D.ds)
          (fun z => pbF.symm (wayE D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s) z))
          0 .first ((_root_.Run.rootsB o).map bytesToDig ++ more) ((), pls) =
        some (ρ, ((none, some []), PQ.rtSL D.C D.ds o.rounds.toList),
          TypedOracleCompiler.Compile.Batch.Phase.loc v') ∧
      PQ.drawnSL D.C D.ds ρ.2 = o.rounds.toList.map (·.drawn) ∧
      PQ.passSL D.C D.ds ρ.2 = true := by
  rw [TypedOracleCompiler.Run.ArmChain.chainP_late_none (fun _ : Unit => L2) _ early2 late2 none]
  exact PQ.chain_one_read (fun _ : Unit => L2) D.C K _ early2 none .link _ none (bytesToBits run)
    (oB (g ())) D.ds _ rtreq (fun _ => size_digToBytes _) chal pls S o more hkit
    (readE_arm D d₁ cfg hcfg pd rest1 V K L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest isPL hpL
      cA tr hinj hlen htr back g F hDK hK early2 first further c₀ c₁ S o run pls A an an' a₀ a₁)

/-- **The chain's half over L2**, at D.K digests and the wiring `wqXE`. xin: how the verifier hands
the instance to the chain: at x, nothing. -/
theorem chain_arm (backD : StrCode (AllPts 256 (D.K + 1) L2)) {X : Type}
    (dec : X → _root_.Run.PQ.View → Bool) (xin : X → Option X2) (x : X)
    (hx : xin x = none) (F : FitsE D) (hK : D.K + 1 < 2 ^ 48)
    (first further : OnBytes.Params.TableName) (c₀ c₁ : Dig 256)
    (S : _root_.Fmt.SpecX) (o : _root_.Fmt.ChainOut) (run : ByteArray)
    (pls : Plains (PQ.uL D.C D.ds)) (A : EntryRead D pd g first further c₀ c₁ S o run pls)
    (an an' : An) (a₀ : tr an = first.answers.map OnBytes.E.triple)
    (a₁ : tr an' = further.answers.map OnBytes.E.triple)
    (π : OneProtocolProof 256 (PSXE D dec).up) (more : List (Dig 256)) (hsalt : π.salt = bytesToBits run)
    (hroots : π.roots = (_root_.Run.rootsB o).map bytesToDig ++ more)
    (hpl : π.plains = ((), pls)) :
    ∃ (ρ : Rho (_root_.Run.Twin.up (PQ.SOf D.C D.ds))) (v' : Bits),
      (recomputeChainOfProof (L := L2) .link (PSXE D dec).up (wqXE D dec)
          (fun z => pbF.symm (wayE D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s) z))
          xin (c₀ :: c₁ :: (cA an ++ cA an')) x π).det
          (readBlocks (implL2 D d₁ cfg hcfg pd rest1 V L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1
            rest isPL hpL cA tr hinj hlen htr (D.K + 1) backD) g) =
        some (ρ, ((none, some []), PQ.rtSL D.C D.ds o.rounds.toList),
          TypedOracleCompiler.Compile.Batch.Phase.loc v') ∧
      PQ.drawnSL D.C D.ds ρ.2 = o.rounds.toList.map (·.drawn) ∧
      PQ.passSL D.C D.ds ρ.2 = true :=
  TypedOracleCompiler.Run.ArmChain.chain_at_none L2 D dec _ (oB (g ())) (fun _ => size_digToBytes _) _ xin
    _ x hx S o (bytesToBits run) pls A.kit
    (readE_arm D d₁ cfg hcfg pd rest1 V D.K L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest isPL hpL
      cA tr hinj hlen htr backD g F (Nat.le_refl _) hK L2.early first further c₀ c₁ S o run pls A
      an an' a₀ a₁)
    π more hsalt hroots hpl

end TypedOracleCompiler.Slice.ArmRead
