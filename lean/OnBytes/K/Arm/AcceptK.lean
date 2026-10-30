-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/AcceptK.lean: the decision's clause and the chain's half of the lax verifier's yes at
an entry's typed string, at the skeleton's wiring with any number K of blocks in a verifier's
message.

A verifier of three files has one number of blocks for all, which need not be the entry file's own
`D.K`. `wqXK D dec K chal` (OnBytes/K/Arm/WireK.lean) is the skeleton's wiring at K blocks. The
number of blocks sits in one field of a round's wire: how a verifier's message is made of the
blocks. The transcript that the compiled verifier builds of a typed string does not read that field.
So the decision's clause at K blocks is the decision's clause at `D.K` blocks, which
OnBytes/K/Left/LaxView.lean and LaxAccept.lean have. The chain does read the field;
OnBytes/TypedOracleCompiler/Slice/ArmRead.lean (`chainP_arm`) has its evaluable form at K blocks. For proofs only;
the program does not import this file.

Main theorems.
 `mkTr_chal`      the transcript is the same at any two numbers of blocks and any two ways of making
                 a message of them.
 `accept_K`       so the decision's clause at `wqXK D dec K chal` is, as a truth value, the one at
                 `wqXE D dec`.
 `accept_viewK`, `accept_readK`   `accept_view` and `accept_read` at `wqXK D dec K chal`, under
                 their own premises: nothing is asked of K or of chal.
 `chain_armK`     the chain's half over a second interface at `wqXK D dec K chal`, under the
                 encoding `implL2` with K + 1 blocks: it returns, draws what the reader drew, and
                 all tests of work pass. Asked of K and chal: `D.K ≤ K`; K + 1 is below 2^48; chal
                 fits the description's field (`KitFits`; the library's `kit_pull` has that for
                 `chalP` at every K).

Not claimed. What the premises of `accept_view`, `accept_read` and `chainP_arm` ask is shown at no
file and no description here. Nothing on the checks of openings (WireK.lean). Nothing on soundness.


-/
import OnBytes.K.Arm.WireK
import OnBytes.K.Left.LaxAccept
import OnBytes.TypedOracleCompiler.Slice.ArmRead
import OnBytes.TypedOracleCompiler.Run.LaxThin

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Arm
open OnBytes.K.Left
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.RowsE2 TypedOracleCompiler.Run.EntryFb
open TypedOracleCompiler.Slice.EntryFill TypedOracleCompiler.Slice.EntryChain TypedOracleCompiler.Slice.ArmRead
open TypedOracleCompiler.Run.Thin
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD SOf inFile)
open OnBytes.Slice (seedEntry)
open OnBytes.Tie (roundWithStoredOpenings StoredFact)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run
open _root_.Run.PQ (View SgX)

/-! ## The transcript -/

section
variable (C : PQ.CK) (K K' : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
  (chal' : ∀ e k, (Fin K' → Dig 256) → C.Ch e k)

/-- On the written rounds. -/
theorem mkTrL_chal : ∀ (ds : List TypedOracleCompiler.Run.PQ.RD) (rts : RootsOfChain 256 (PQ.uL C ds))
    (pls : Plains (PQ.uL C ds)) (ρ : Rho (PQ.uL C ds))
    (f : (p : OPos (PQ.uL C ds)) → Option (Opening 256 (OSym (PQ.uL C ds) p))),
    mkTr (PQ.uL C ds) (_root_.Run.Twin.allLo (PQ.SL C ds)) (PQ.wiresSL C K chal ds) rts pls ρ f =
      mkTr (PQ.uL C ds) (_root_.Run.Twin.allLo (PQ.SL C ds)) (PQ.wiresSL C K' chal' ds) rts pls ρ f
  | [], _, _, _, _ => rfl
  | d :: ds, (rt, rts), (pl, pls), (c, ρ), f => by
      have ih := mkTrL_chal ds rts pls ρ fun p => f (.inr p)
      show (_, c, mkTr (PQ.uL C ds) _ (PQ.wiresSL C K chal ds) rts pls ρ fun p => f (.inr p)) =
        (_, c, mkTr (PQ.uL C ds) _ (PQ.wiresSL C K' chal' ds) rts pls ρ fun p => f (.inr p))
      rw [ih]
      rfl

/-- **The transcript does not look at how a verifier's message is made of blocks.** -/
theorem mkTr_chal (ds : List TypedOracleCompiler.Run.PQ.RD) (rts : RootsOfChain 256 (_root_.Run.Twin.up (PQ.SOf C ds)))
    (pls : Plains (_root_.Run.Twin.up (PQ.SOf C ds))) (ρ : Rho (_root_.Run.Twin.up (PQ.SOf C ds)))
    (f : (p : OPos (_root_.Run.Twin.up (PQ.SOf C ds))) →
      Option (Opening 256 (OSym (_root_.Run.Twin.up (PQ.SOf C ds)) p))) :
    mkTr (_root_.Run.Twin.up (PQ.SOf C ds)) (_root_.Run.Twin.allLo (PQ.SOf C ds))
        (PQ.wire0S C K chal, PQ.wiresSL C K chal ds) rts pls ρ f =
      mkTr (_root_.Run.Twin.up (PQ.SOf C ds)) (_root_.Run.Twin.allLo (PQ.SOf C ds))
        (PQ.wire0S C K' chal', PQ.wiresSL C K' chal' ds) rts pls ρ f := by
  obtain ⟨rt, rts⟩ := rts
  obtain ⟨pl, pls⟩ := pls
  obtain ⟨c, ρ⟩ := ρ
  have ih := mkTrL_chal C K K' chal chal' ds rts pls ρ fun p => f (.inr p)
  show (_, c, mkTr (PQ.uL C ds) _ (PQ.wiresSL C K chal ds) rts pls ρ fun p => f (.inr p)) =
    (_, c, mkTr (PQ.uL C ds) _ (PQ.wiresSL C K' chal' ds) rts pls ρ fun p => f (.inr p))
  rw [ih]

end

/-! ## The decision's clause -/

section
variable {X : Type} (D : XD) (dec : X → View → Bool) (K : ℕ)
  (chal : ∀ e k, (Fin K → Dig 256) → D.C.Ch e k)

/-- **The decision's clause at K blocks is the one at the description's own number.** -/
theorem accept_K (x : X) (π : OneProtocolProof 256 (PSXE D dec).up)
    (rts : RootsOfChain 256 (_root_.Run.Twin.up (SOf D.C D.ds)))
    (ρ : Rho (_root_.Run.Twin.up (SOf D.C D.ds))) :
    (PSXE D dec).up.loc.accept x
        ((wqXK D dec K chal).ext.build fun p => (π.ext p).map Opening.sym)
        (mkTr (PSXE D dec).up.loc.shape (PSXE D dec).up.ann (wqXK D dec K chal).sh rts π.plains ρ
          π.opens) =
      (PSXE D dec).up.loc.accept x
        ((wqXE D dec).ext.build fun p => (π.ext p).map Opening.sym)
        (mkTr (PSXE D dec).up.loc.shape (PSXE D dec).up.ann (wqXE D dec).sh rts π.plains ρ
          π.opens) :=
  congrArg (fun τ => (PSXE D dec).up.loc.accept x
      ((wqXE D dec).ext.build fun p => (π.ext p).map Opening.sym) τ)
    (mkTr_chal D.C K D.K chal (chalP D.base.plan.field D.K) D.ds rts π.plains ρ π.opens)

/-- **`accept_view` at K blocks.** -/
theorem accept_viewK (h : HId) (hok : TypedOracleCompiler.Run.PQ.ok D.base = true) (st : ByteArray) (x : X)
    (o : _root_.Fmt.ChainOut) (π : OneProtocolProof 256 (PSXE D dec).up) (hπ : assembleS D dec o = some π)
    (ρ : Rho (_root_.Run.Twin.up (SOf D.C D.ds)))
    (hd : PQ.drawnSL D.C D.ds ρ.2 = o.rounds.toList.map (·.drawn))
    (hpass : PQ.passSL D.C D.ds ρ.2 = true) (c : _root_.Fmt.Chain)
    (rc : List (_root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)))
    (ho : o.rounds.toList = rc.map roundWithStoredOpenings)
    (htr : PQ.TraceL h D.base.plan D.base.rounds (rc.map fun p => PQ.stripR p.1) c #[])
    (hsent : List.Forall₂ TypedOracleCompiler.Run.PQ.SentR D.ds (rc.map fun p => PQ.stripR p.1))
    (hS : List.Forall₂ (fun (ts : List _root_.Fmt.Stored)
        (p : _root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)) =>
      List.Forall₂ (StoredFact h D.base.cfg st p.1.drawn.poss) ts p.2) D.stored rc)
    (hlen : List.Forall₂ (fun (z : _root_.Fmt.Round × List _root_.Fmt.Stored)
        (p : _root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)) =>
      p.1.drawn.poss.length = z.1.entry.poss) (D.base.rounds.zip D.stored) rc)
    (hSok : (⟨{ D.base with statement := st }, D.stored⟩ : _root_.Fmt.SpecX).ok = true)
    (hD : ∀ s ∈ D.stored.flatten, s.sh.a = D.a ∧ s.item ≤ 1)
    (honce : (D.stored.flatten.map (·.item == 1)).Nodup)
    (okx : PQ.okX D.ds D.a D.xs = true)
    (listed : ListedX D D.a ((opsOf 1 o).filter fun op => op.sh.stored) fun p =>
      (haveI := (wqXK D dec K chal).ext.dec
       decide (p ∈ (PSXE D dec).up.loc.extReads x ρ)))
    (hA : ∀ tab, tabOf (fun op => op.sh.tree) ((opsOf 1 o).filter fun op => !op.sh.stored) =
      some tab → PQ.Agree tab)
    (hbase : ({ D.base with statement := st } : _root_.Fmt.Spec).ok = true)
    (S : _root_.Fmt.SpecX) (hsto : S.stored = D.stored)
    (hft : S.base.firstTree = D.base.firstTree) (hdec : dec x (_root_.Fmt.viewX S o) = true) :
    (PSXE D dec).up.loc.accept x
      ((wqXK D dec K chal).ext.build fun p => (π.ext p).map Opening.sym)
      (mkTr (PSXE D dec).up.loc.shape (PSXE D dec).up.ann (wqXK D dec K chal).sh
        ((none, some []), PQ.rtSL D.C D.ds o.rounds.toList) π.plains ρ π.opens) = true :=
  (accept_K D dec K chal x π _ ρ).trans
    (accept_view h D hok st dec x o π hπ ρ hd hpass c rc ho htr hsent hS hlen hSok hD honce okx
      listed hA hbase S hsto hft hdec)

/-- **`accept_read` at K blocks.** -/
theorem accept_readK (hok : TypedOracleCompiler.Run.PQ.ok D.base = true) (st : ByteArray)
    (O : ByteArray → ByteArray)
    (hokb : TypedOracleCompiler.Run.PQ.ok (inFile ({ D.base with statement := st } : _root_.Fmt.Spec)) = true)
    (hn : D.base.rand.isNone = false) (seen : _root_.Fmt.Seen) (b : ByteArray) (i : ℕ)
    (o : _root_.Fmt.ChainOut) (j : ℕ)
    (e : _root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO O)
      ⟨{ D.base with statement := st }, D.stored⟩ seen b i = some (o, j))
    (x : X) (π : OneProtocolProof 256 (PSXE D dec).up)
    (hπ : assembleS D dec o = some π) (ρ : Rho (_root_.Run.Twin.up (SOf D.C D.ds)))
    (hd : PQ.drawnSL D.C D.ds ρ.2 = o.rounds.toList.map (·.drawn))
    (hpass : PQ.passSL D.C D.ds ρ.2 = true)
    (hD : ∀ s ∈ D.stored.flatten, s.sh.a = D.a ∧ s.item ≤ 1)
    (honce : (D.stored.flatten.map (·.item == 1)).Nodup)
    (okx : PQ.okX D.ds D.a D.xs = true)
    (listed : ListedX D D.a ((opsOf 1 o).filter fun op => op.sh.stored) fun p =>
      (haveI := (wqXK D dec K chal).ext.dec
       decide (p ∈ (PSXE D dec).up.loc.extReads x ρ)))
    (S : _root_.Fmt.SpecX) (hsto : S.stored = D.stored)
    (hft : S.base.firstTree = D.base.firstTree) (hdec : dec x (_root_.Fmt.viewX S o) = true) :
    (PSXE D dec).up.loc.accept x
      ((wqXK D dec K chal).ext.build fun p => (π.ext p).map Opening.sym)
      (mkTr (PSXE D dec).up.loc.shape (PSXE D dec).up.ann (wqXK D dec K chal).sh
        ((none, some []), PQ.rtSL D.C D.ds o.rounds.toList) π.plains ρ π.opens) = true :=
  (accept_K D dec K chal x π _ ρ).trans
    (accept_read D hok st O hokb hn seen b i o j e dec x π hπ ρ hd hpass hD honce okx listed S hsto
      hft hdec)

end

/-! ## The chain's half -/

section
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

/-- **The chain's half over L2, at K blocks.** xin: how the verifier hands the instance to the
chain: at x, nothing. -/
theorem chain_armK {X : Type} (dec : X → View → Bool) (xin : X → Option X2) (x : X)
    (hx : xin x = none) (F : FitsE D) (hDK : D.K ≤ K) (hK : K + 1 < 2 ^ 48)
    (first further : OnBytes.Params.TableName) (c₀ c₁ : Dig 256)
    (S : _root_.Fmt.SpecX) (o : _root_.Fmt.ChainOut) (run : ByteArray)
    (pls : Plains (PQ.uL D.C D.ds)) (A : EntryRead D pd g first further c₀ c₁ S o run pls)
    (an an' : An) (a₀ : tr an = first.answers.map E.triple)
    (a₁ : tr an' = further.answers.map E.triple)
    (chal : ∀ e k, (Fin K → Dig 256) → D.C.Ch e k)
    (hkit : _root_.Run.PQ.KitFits S.base.plan.field D.C K chal)
    (π : OneProtocolProof 256 (PSXE D dec).up) (more : List (Dig 256)) (hsalt : π.salt = bytesToBits run)
    (hroots : π.roots = (_root_.Run.rootsB o).map bytesToDig ++ more)
    (hpl : π.plains = ((), pls)) :
    ∃ (ρ : Rho (_root_.Run.Twin.up (SOf D.C D.ds))) (v' : Bits),
      (recomputeChainOfProof (L := L2) .link (PSXE D dec).up (wqXK D dec K chal)
          (fun z => pbF.symm (wayE D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s) z))
          xin (c₀ :: c₁ :: (cA an ++ cA an')) x π).det
          (readBlocks (implL2 D d₁ cfg hcfg pd rest1 V L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1
            rest isPL hpL cA tr hinj hlen htr (K + 1) back) g) =
        some (ρ, ((none, some []), PQ.rtSL D.C D.ds o.rounds.toList),
          TypedOracleCompiler.Compile.Batch.Phase.loc v') ∧
      PQ.drawnSL D.C D.ds ρ.2 = o.rounds.toList.map (·.drawn) ∧
      PQ.passSL D.C D.ds ρ.2 = true := by
  obtain ⟨ρ, v', e, hd, hp⟩ := chainP_arm D d₁ cfg hcfg pd rest1 V K L2 pbF bd p0 p1 isP0 isP1 cfgL
    sh hp0 hp1 rest isPL hpL cA tr hinj hlen htr back g F hDK hK L2.early L2.late first further c₀
    c₁ S o run pls A an an' a₀ a₁ chal hkit π.rtreq more
  refine ⟨ρ, v', ?_, hd, hp⟩
  rw [chainP_det, hx, hsalt, hroots, hpl]
  exact e

end

end OnBytes.K.Arm
