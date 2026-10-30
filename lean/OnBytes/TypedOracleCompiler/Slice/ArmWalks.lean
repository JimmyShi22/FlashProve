-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/ArmWalks.lean: what the lax verifier's clause on the walks asks at an entry's
typed string, put together for any interface, any number of blocks in a verifier's message and any
family of oracle functions.

`assembleS_walks` (OnBytes/TypedOracleCompiler/Slice/EntryWhole.lean) asks: a law of the family at vertices; that
the bodies of the chain's own symbols are one way e1, lifted; the trees' forms and roots under two
predicates; and one record for each opening of the file (`OwnOkE`, `StoOkE`). Of these only the law
at vertices, the equations at leaves and the bodies look at the family or at the interface. Here all
are joined into one statement, with the family's laws as hypotheses in the letters of
`ownOkE_of_read` and `stoOkE_of_read`. For proofs only; the program does not import this file.

Main names.
 `aw_which`: `whichOf` is 0 or 1.
 `stoOkE_longer`: the record of a stored table's opening at the list of two outer roots holds at
   every list that begins with these two.
 `Walks`: the statement: there are a function at vertices, a way e1 and two predicates with all that
   `assembleS_walks` asks.
 `walks_at`: `Walks` at any interface, family, bodies and list of outer roots, from the family's
   three laws and, opening by opening, what the format's reader of an opening has said.
 `Walks.longer`: `Walks` at two outer roots gives `Walks` at every list that begins with them.
 `Walks.run`: what `Walks` is for, at `D.K + 1` blocks: at the string that the typing makes, all
   checks that the lax verifier forms walk to their roots under the family, and are well formed.

What is not claimed. The family's laws at any family. That the reader of each opening said yes
(`ReadAs`); the forms, roots, widths and the salts' lengths: they are hypotheses of `walks_at`.
Nothing on soundness.


-/
import OnBytes.TypedOracleCompiler.Slice.EntryWhole
import OnBytes.TypedOracleCompiler.Run.PageIs

set_option autoImplicit false

namespace TypedOracleCompiler.Slice.ArmWalks
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD SOf)
open _root_.Run.PQ (SgX View)
open _root_.Run (bytesToDig leafSalt)

/-! ## The list of outer roots -/

/-- Which of the two tables: 0 or 1. -/
theorem aw_which (D : XD) (op : OpAt) : whichOf D op = 0 ∨ whichOf D op = 1 := by
  unfold whichOf
  split
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl
  · exact Or.inl rfl

section
variable {I X' : Type} {K : ℕ} {L : BatchProtocolWithLeafBody I X'} {g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 K L)}
  {vert : ByteArray → ByteArray → ByteArray}

/-- A longer list of outer roots that begins with the two tables' roots. -/
theorem stoOkE_longer {embE : SgX → Body L} {a : ℕ} {cfg : ByteArray} {c₀ c₁ : Dig 256} {D : XD}
    {op : OpAt} (h : StoOkE g vert embE a cfg [c₀, c₁] D op) (rest : List (Dig 256)) :
    StoOkE g vert embE a cfg (c₀ :: c₁ :: rest) D op := by
  refine ⟨h.depth, ?_, h.rows⟩
  rw [← h.root]
  rcases aw_which D op with e | e <;> rw [e] <;> rfl

end

/-! ## The clause, at any interface and family -/

section
variable {I X' : Type} {L : BatchProtocolWithLeafBody I X'} (D : XD) {K : ℕ}
  (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 K L))

/-- What `assembleS_walks` asks beside the typed string, as one statement. -/
def Walks (embS : (p : OPos (_root_.Run.Twin.up (SOf D.C D.ds))) →
      OSym (_root_.Run.Twin.up (SOf D.C D.ds)) p → Body L)
    (embE : SgX → Body L) (cms : List (Dig 256)) (o : _root_.Fmt.ChainOut) : Prop :=
  ∃ (vert : ByteArray → ByteArray → ByteArray) (e1 : Enc1 (Body L))
      (Fm : ℕ → _root_.Fmt.Shape → Prop) (Rt : ℕ → Dig 256 → Prop),
    NodeLaw g vert ∧ (∀ q a, embS (.inr q) a = embLS D.C (liftT e1) D.ds q a) ∧
    FormsOn Fm 0 D.ds ∧
    (∀ run, o.run = some run → ∀ op ∈ (opsOf 1 o).filter (fun op => !op.sh.stored),
      OwnOkE g vert e1 run Fm Rt op) ∧
    (∀ op ∈ (opsOf 1 o).filter (fun op => op.sh.stored),
      StoOkE g vert embE D.a D.base.cfg cms D op) ∧
    RtsL Rt D.C 0 D.ds (PQ.rtSL D.C D.ds o.rounds.toList)

variable {D g}

/-- The clause from the family's three laws and the reader's yes, opening by opening. h: the hash;
sB: the bytes of a file's salt. -/
theorem walks_at {h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray}
    (hz : ∀ n t i s b, ByteArray.size (h n t i s b) = _root_.Fmt.dlen n)
    (N : NodeLaw g fun l r => h 166 0 0 D.base.cfg (l ++ r))
    {embS : (p : OPos (_root_.Run.Twin.up (SOf D.C D.ds))) →
      OSym (_root_.Run.Twin.up (SOf D.C D.ds)) p → Body L}
    {e1 : Enc1 (Body L)} (hemb : ∀ q a, embS (.inr q) a = embLS D.C (liftT e1) D.ds q a)
    {Fm : ℕ → _root_.Fmt.Shape → Prop} {Rt : ℕ → Dig 256 → Prop} (hF : FormsOn Fm 0 D.ds)
    {o : _root_.Fmt.ChainOut} (hR : RtsL Rt D.C 0 D.ds (PQ.rtSL D.C D.ds o.rounds.toList))
    {embE : SgX → Body L} {cms : List (Dig 256)} (sB : ℕ)
    (rdO : ∀ run, o.run = some run → ∀ op ∈ (opsOf 1 o).filter (fun op => !op.sh.stored),
      ReadAs h D.base.cfg run op)
    (hform : ∀ op ∈ (opsOf 1 o).filter (fun op => !op.sh.stored),
      ∀ n s, Fm n s → s.tree = op.sh.tree → s = op.sh)
    (hroot : ∀ op ∈ (opsOf 1 o).filter (fun op => !op.sh.stored),
      ∀ n s c, Fm n s → s.tree = op.sh.tree → Rt n c → c = bytesToDig op.out.root)
    (hsO : ∀ op ∈ (opsOf 1 o).filter (fun op => !op.sh.stored), ∀ sl ∈ op.out.salts, sl.size = sB)
    (leafO : ∀ run, o.run = some run → ∀ op ∈ (opsOf 1 o).filter (fun op => !op.sh.stored),
      ∀ (x : Fin (2 ^ op.sh.a)) (sym : Fin op.sh.W → UInt64) (salt : ByteArray), salt.size = sB →
        (g TypedOracleCompiler.Compile.Batch.OracleName.leaf (⟨e1 op.sh x sym, leafSalt run salt⟩ : LeafIn L) :
          Dig 256) = bytesToDig (leafAtH h op.sh run x.val (List.ofFn sym) salt))
    (rdS : ∀ op ∈ (opsOf 1 o).filter (fun op => op.sh.stored),
      ReadAs h D.base.cfg D.base.cfg op)
    (hd : ∀ op ∈ (opsOf 1 o).filter (fun op => op.sh.stored), op.sh.a = D.a)
    (hr : ∀ op ∈ (opsOf 1 o).filter (fun op => op.sh.stored),
      cms.getD (whichOf D op) default = bytesToDig op.out.root)
    (hcS : ∀ op ∈ (opsOf 1 o).filter (fun op => op.sh.stored),
      ∀ c ∈ op.out.cols, c.length = op.sh.W)
    (hsS : ∀ op ∈ (opsOf 1 o).filter (fun op => op.sh.stored), ∀ sl ∈ op.out.salts, sl.size = sB)
    (leafS : ∀ op ∈ (opsOf 1 o).filter (fun op => op.sh.stored),
      ∀ (x : ℕ) (col : List UInt64) (salt : ByteArray), x < 2 ^ op.sh.a → col.length = op.sh.W →
        salt.size = sB →
        (g TypedOracleCompiler.Compile.Batch.OracleName.leaf
          (⟨embE (x, col), leafSalt D.base.cfg salt⟩ : LeafIn L) : Dig 256) =
          bytesToDig (leafAtH h op.sh D.base.cfg x col salt)) :
    Walks D g embS embE cms o :=
  ⟨_, e1, Fm, Rt, N, hemb, hF,
    fun run hrun op hop => ownOkE_of_read hz sB (rdO run hrun op hop) (hform op hop) (hroot op hop)
      (hsO op hop) (leafO run hrun op hop),
    fun op hop => stoOkE_of_read hz sB (rdS op hop) (hd op hop) (hr op hop) (hcS op hop)
      (hsS op hop) (leafS op hop), hR⟩

/-- A longer list of outer roots. -/
theorem Walks.longer {embS : (p : OPos (_root_.Run.Twin.up (SOf D.C D.ds))) →
      OSym (_root_.Run.Twin.up (SOf D.C D.ds)) p → Body L}
    {embE : SgX → Body L} {c₀ c₁ : Dig 256} {o : _root_.Fmt.ChainOut}
    (W : Walks D g embS embE [c₀, c₁] o) (rest : List (Dig 256)) :
    Walks D g embS embE (c₀ :: c₁ :: rest) o := by
  obtain ⟨vert, e1, Fm, Rt, N, hemb, hF, hO, hS, hR⟩ := W
  exact ⟨vert, e1, Fm, Rt, N, hemb, hF, hO, fun op hop => stoOkE_longer (hS op hop) rest, hR⟩

/-- What it is for, at the number of blocks of the skeleton's own wiring: at the typing's string all
checks walk to their roots and are well formed. -/
theorem Walks.run {g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (D.K + 1) L)} {X : Type}
    (dec : X → View → Bool)
    {embS : (p : OPos (_root_.Run.Twin.up (SOf D.C D.ds))) →
      OSym (_root_.Run.Twin.up (SOf D.C D.ds)) p → Body L}
    {embE : SgX → Body L} {cms : List (Dig 256)} {o : _root_.Fmt.ChainOut}
    (W : Walks D g embS embE cms o) {π : OneProtocolProof 256 (PSXE D dec).up}
    (hπ : assembleS D dec o = some π)
    (isRead : OPos (_root_.Run.Twin.up (SOf D.C D.ds)) → Bool)
    (isReadE : Fin (2 ^ D.a) ⊕ Fin (2 ^ D.a) → Bool) (a b : List (Check 256 L))
    (ha : checksB (_root_.Run.Twin.up (SOf D.C D.ds)) (_root_.Run.Twin.allLo (SOf D.C D.ds))
      (wqXE D dec).sh embS ((none, some []), PQ.rtSL D.C D.ds o.rounds.toList) isRead
      π.opens = some a)
    (hb : TypedOracleCompiler.Compile.Batch.checksExt (wqXE D dec).ext embE cms isReadE π.ext
      (wqXE D dec).ext.all = some b) :
    (runChecks (K := D.K + 1) (a ++ b)).det g = true ∧ (a ++ b).all (runCheckF g) = true ∧
      (a ++ b).all (fun c => c.wellFormed) = true := by
  obtain ⟨vert, e1, Fm, Rt, N, hemb, hF, hO, hS, hR⟩ := W
  exact assembleS_walks D dec N hπ embS hemb hF hO hS
    ((none, some []), PQ.rtSL D.C D.ds o.rounds.toList) hR isRead isReadE a b ha hb

end

end TypedOracleCompiler.Slice.ArmWalks
