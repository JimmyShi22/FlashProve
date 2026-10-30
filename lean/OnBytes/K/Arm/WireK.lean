-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/WireK.lean: the skeleton of an entry's written link, wired with any number K of blocks
in a verifier's message that is at least the description's own; and the lax verifier's clauses on
the checks of openings at that wiring.

The wiring `wqXE D dec` (OnBytes/TypedOracleCompiler/Slice/EntryPS.lean) has `D.K` blocks, the description's own
number. A verifier of three files has one number of blocks for all, which need not be the entry
file's own. The number sits in one field of a round's wire: how a verifier's
message is made of the blocks. The checks of openings do not read that field. So the clauses "own",
"ext", "few", "formed" and "walks" (OnBytes/TypedOracleCompiler/Slice/EntryOpened.lean, EntryWhole.lean) hold at K
blocks by their old proofs. For proofs only; the program does not import this file.

Main names.
 `wqXK D dec K chal`: the rounds' wires at K blocks and a way chal of making a message of K blocks;
   the four other fields are `wqXE D dec`'s.
 `wqXK_self`: at `D.K` and the library's way `chalP` it is `wqXE D dec`. `wqXK_sib`: it is `sibW`
   (OnBytes/K/Arm/SameSib.lean) at D's letters. Both by unfolding.
 `wqXK_okg`: it obeys the sibling's laws of a wiring, if the wiring of the rounds alone does and
   the stored openings are in order. `wqS_okgP`: the former holds at `chalP`, if `D.K ≤ K` and no
   round asks more than 64 bits of work. `wqXK_depth`.
 `assembleS_ownK`, `assembleS_extK`, `entry_fewK`, `entry_formedK`, `assembleS_walksK`: the five
   clauses at the typing's string.
 `walks_runK`: `Walks` (OnBytes/TypedOracleCompiler/Slice/ArmWalks.lean) at a family with K + 1 blocks gives the
   fifth.

What is not claimed. The chain at K blocks (OnBytes/TypedOracleCompiler/Slice/ArmRead.lean has it); the decision's
clause. Nothing on soundness.


-/
import OnBytes.TypedOracleCompiler.Slice.EntryOpened
import OnBytes.TypedOracleCompiler.Slice.EntryWhole
import OnBytes.TypedOracleCompiler.Slice.ArmWalks
import OnBytes.K.Arm.SameSib

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Arm
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Slice TypedOracleCompiler.Slice.ArmWalks
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD SOf wqX RowsL)
open _root_.Run.PQ (View SgX weX)
open _root_.Run (chalP)

variable {X : Type} (D : XD) (dec : X → View → Bool) (K : ℕ)
  (chal : ∀ e k, (Fin K → Dig 256) → D.C.Ch e k)

/-- The skeleton's wiring with K blocks in a verifier's message, made into a message by chal. -/
def wqXK : ProtocolQueryLayout 256 (K + 1) (PSXE D dec).up :=
  ⟨(PQ.wire0S D.C K chal, PQ.wiresSL D.C K chal D.ds), (wqXE D dec).ext, (wqXE D dec).decO,
    (wqXE D dec).nOpen, (wqXE D dec).maxDepth⟩

/-- At the description's own number of blocks and the library's way it is the skeleton's own
wiring. -/
theorem wqXK_self : wqXK D dec D.K (chalP D.base.plan.field D.K) = wqXE D dec := rfl

/-- It is the wire record over letters, at D's letters. -/
theorem wqXK_sib : wqXK D dec K chal = sibW D.C D.ds D.a D.xs K chal dec := rfl

/-- The wiring is lawful, if the wiring of the rounds alone is. -/
theorem wqXK_okg (hS : (PQ.wqS D.C K chal D.ds fun _ => true).OKG)
    (hokx : TypedOracleCompiler.Run.PQ.okX D.ds D.a D.xs = true) : (wqXK D dec K chal).OKG :=
  have h : (wqX D.C K chal D.ds D.a D.xs fun _ => true).OKG :=
    TypedOracleCompiler.Run.PQ.wqX_okg D.C K chal D.ds D.a D.xs (fun _ => true) (fun _ => true)
      (TypedOracleCompiler.Run.PQ.okX_own D.ds D.a D.xs hokx) hS
  ⟨h.sh, h.ext, fun _ ρ pl => h.opens () ρ pl, h.depth⟩

/-- The wiring of the rounds alone is lawful at the library's way of making a message of K blocks,
for K at least the description's own number. -/
theorem wqS_okgP (hDK : D.K ≤ K) (hwork : ∀ r ∈ D.ds, r.entry.work ≤ 64) :
    (PQ.wqS D.C K (chalP D.base.plan.field K) D.ds fun _ => true).OKG :=
  TypedOracleCompiler.Run.planPull_okg D.base.plan.field K D.ds (fun _ => true)
    (fun d hd => le_trans (TypedOracleCompiler.Run.PQ.blocks_le_kOf D.base d hd) hDK) hwork

/-- The stored tables' depth is within the wiring's greatest depth. -/
theorem wqXK_depth : (wqXK D dec K chal).ext.depth ≤ (wqXK D dec K chal).maxDepth :=
  le_max_right (TypedOracleCompiler.Run.PQ.maxDepth D.ds) D.a

variable {I X' : Type} {L : BatchProtocolWithLeafBody I X'}

/-- "own": every read position of the chain's own trees has an opening. -/
theorem assembleS_ownK {o : _root_.Fmt.ChainOut} {π : OneProtocolProof 256 (PSXE D dec).up}
    (hπ : assembleS D dec o = some π)
    (embS : (p : OPos (_root_.Run.Twin.up (SOf D.C D.ds))) →
      OSym (_root_.Run.Twin.up (SOf D.C D.ds)) p → Body L)
    (rts : RootsOfChain 256 (_root_.Run.Twin.up (SOf D.C D.ds)))
    (isRead : OPos (_root_.Run.Twin.up (SOf D.C D.ds)) → Bool) (sb : ℕ)
    (ros : List _root_.Fmt.RoundOut)
    (hrows : RowsL D.C (tblOf ((opsOf 1 o).filter fun op => !op.sh.stored)) sb D.ds ros
      fun q => isRead (.inr q))
    (hc : ColsFit ((opsOf 1 o).filter fun op => !op.sh.stored)) :
    ∃ a : List (Check 256 L), checksB (_root_.Run.Twin.up (SOf D.C D.ds))
      (_root_.Run.Twin.allLo (SOf D.C D.ds)) (wqXK D dec K chal).sh embS rts isRead π.opens =
        some a := by
  obtain ⟨run, pl, tab, tx, -, -, e3, -, -, -, -, hop, -⟩ := assembleS_some D dec hπ
  refine Option.isSome_iff_exists.1 (checksB_isSome _ _ _ embS rts isRead π.opens fun p hp => ?_)
  cases p with
  | inl e => exact e.elim
  | inr q =>
    rw [hop q]
    exact own_opened e3 hc run sb D.C D.ds ros (fun q => isRead (.inr q)) hrows 0 q hp

/-- "ext": every read position of a stored table has an opening. -/
theorem assembleS_extK {o : _root_.Fmt.ChainOut} {π : OneProtocolProof 256 (PSXE D dec).up}
    (hπ : assembleS D dec o = some π) (embE : SgX → Body L) (cms : List (Dig 256))
    (isReadE : Fin (2 ^ D.a) ⊕ Fin (2 ^ D.a) → Bool)
    (h : ListedX D D.a ((opsOf 1 o).filter fun op => op.sh.stored) isReadE) :
    ∃ b : List (Check 256 L), TypedOracleCompiler.Compile.Batch.checksExt (wqXK D dec K chal).ext embE cms
      isReadE π.ext (wqXK D dec K chal).ext.all = some b :=
  assembleS_ext D dec hπ embE cms isReadE h

/-- "few". -/
theorem entry_fewK (hS : (PQ.wqS D.C K chal D.ds fun _ => true).OKG)
    (hokx : TypedOracleCompiler.Run.PQ.okX D.ds D.a D.xs = true)
    (embS : (p : OPos (_root_.Run.Twin.up (SOf D.C D.ds))) →
      OSym (_root_.Run.Twin.up (SOf D.C D.ds)) p → Body L)
    (embE : SgX → Body L) (cms : List (Dig 256)) (x : X) (π : OneProtocolProof 256 (PSXE D dec).up)
    (ρ : Rho (_root_.Run.Twin.up (SOf D.C D.ds))) (rts : RootsOfChain 256 (_root_.Run.Twin.up (SOf D.C D.ds)))
    (a b : List (Check 256 L))
    (own : (haveI := (wqXK D dec K chal).decO; checksB (PSXE D dec).up.loc.shape (PSXE D dec).up.ann
      (wqXK D dec K chal).sh embS rts
      (fun p => decide (p ∈ (PSXE D dec).up.loc.reads x ρ
        (effPlains (PSXE D dec).up.loc.shape (PSXE D dec).up.ann rts π.plains))) π.opens) = some a)
    (ext : (haveI := (wqXK D dec K chal).ext.dec; TypedOracleCompiler.Compile.Batch.checksExt
      (wqXK D dec K chal).ext embE cms (fun p => decide (p ∈ (PSXE D dec).up.loc.extReads x ρ))
      π.ext (wqXK D dec K chal).ext.all) = some b) :
    (a ++ b).length ≤ (wqXK D dec K chal).nOpen :=
  few_of_okg (PSXE D dec).up (wqXK D dec K chal) (wqXK_okg D dec K chal hS hokx) embS embE cms x π ρ
    rts a b own ext

/-- "formed". -/
theorem entry_formedK (hS : (PQ.wqS D.C K chal D.ds fun _ => true).OKG)
    (hokx : TypedOracleCompiler.Run.PQ.okX D.ds D.a D.xs = true)
    (embS : (p : OPos (_root_.Run.Twin.up (SOf D.C D.ds))) →
      OSym (_root_.Run.Twin.up (SOf D.C D.ds)) p → Body L)
    (embE : SgX → Body L) (cms : List (Dig 256)) (rts : RootsOfChain 256 (_root_.Run.Twin.up (SOf D.C D.ds)))
    (isRead : OPos (_root_.Run.Twin.up (SOf D.C D.ds)) → Bool)
    (isReadE : Fin (2 ^ D.a) ⊕ Fin (2 ^ D.a) → Bool) (π : OneProtocolProof 256 (PSXE D dec).up)
    (a b : List (Check 256 L))
    (own : checksB (PSXE D dec).up.loc.shape (PSXE D dec).up.ann (wqXK D dec K chal).sh embS rts
      isRead π.opens = some a)
    (ext : TypedOracleCompiler.Compile.Batch.checksExt (wqXK D dec K chal).ext embE cms isReadE π.ext
      (wqXK D dec K chal).ext.all = some b)
    (wf : (a ++ b).all (fun c => c.wellFormed) = true) :
    (a ++ b).all (fun c => c.wellFormed && decide (c.depth ≤ (wqXK D dec K chal).maxDepth)) =
      true :=
  formed_of_okg (PSXE D dec).up (wqXK D dec K chal) (wqXK_okg D dec K chal hS hokx)
    (wqXK_depth D dec K chal) embS embE cms rts isRead isReadE π a b own ext wf

/-- "walks", and the first half of "formed". -/
theorem assembleS_walksK {g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (K + 1) L)}
    {vert : ByteArray → ByteArray → ByteArray} (N : NodeLaw g vert) {o : _root_.Fmt.ChainOut}
    {π : OneProtocolProof 256 (PSXE D dec).up} (hπ : assembleS D dec o = some π) {e1 : Enc1 (Body L)}
    (embS : (p : OPos (_root_.Run.Twin.up (SOf D.C D.ds))) →
      OSym (_root_.Run.Twin.up (SOf D.C D.ds)) p → Body L)
    (hemb : ∀ q a, embS (.inr q) a = embLS D.C (liftT e1) D.ds q a)
    {Fm : ℕ → _root_.Fmt.Shape → Prop} {Rt : ℕ → Dig 256 → Prop} (hF : FormsOn Fm 0 D.ds)
    (hOwn : ∀ run, o.run = some run → ∀ op ∈ (opsOf 1 o).filter (fun op => !op.sh.stored),
      OwnOkE g vert e1 run Fm Rt op)
    {embE : SgX → Body L} {cms : List (Dig 256)}
    (hSto : ∀ op ∈ (opsOf 1 o).filter (fun op => op.sh.stored),
      StoOkE g vert embE D.a D.base.cfg cms D op)
    (rts : RootsOfChain 256 (_root_.Run.Twin.up (SOf D.C D.ds))) (hR : RtsL Rt D.C 0 D.ds rts.2)
    (isRead : OPos (_root_.Run.Twin.up (SOf D.C D.ds)) → Bool)
    (isReadE : Fin (2 ^ D.a) ⊕ Fin (2 ^ D.a) → Bool) (a b : List (Check 256 L))
    (ha : checksB (_root_.Run.Twin.up (SOf D.C D.ds)) (_root_.Run.Twin.allLo (SOf D.C D.ds))
      (wqXK D dec K chal).sh embS rts isRead π.opens = some a)
    (hb : TypedOracleCompiler.Compile.Batch.checksExt (wqXK D dec K chal).ext embE cms isReadE π.ext
      (wqXK D dec K chal).ext.all = some b) :
    (runChecks (K := K + 1) (a ++ b)).det g = true ∧ (a ++ b).all (runCheckF g) = true ∧
      (a ++ b).all (fun c => c.wellFormed) = true := by
  obtain ⟨run, pl, tab, tx, h1, -, e3, e4, -, -, -, hop, hext, -⟩ := assembleS_some D dec hπ
  have H := lookGood_E N (hOwn run h1) e3
  have e5 : (fun q => embS (.inr q)) = embLS D.C (liftT e1) D.ds :=
    funext fun q => funext fun a => hemb q a
  have e6 : (fun q => π.opens (.inr q)) = opLS D.C (lookE run tab) 0 D.ds := funext hop
  have G : GoodAt (Yes g) (_root_.Run.Twin.up (SOf D.C D.ds)) (_root_.Run.Twin.allLo (SOf D.C D.ds))
      (wqXK D dec K chal).sh embS rts isRead π.opens := by
    refine ⟨comp_none _ _ _ _ _, comp_none _ _ _ _ _, ?_⟩
    show GoodAt (Yes g) (PQ.uL D.C D.ds) (_root_.Run.Twin.allLo (PQ.SL D.C D.ds))
      (PQ.wiresSL D.C K chal D.ds) (fun q => embS (.inr q)) rts.2
      (fun q => isRead (.inr q)) (fun q => π.opens (.inr q))
    rw [e5, e6]
    exact goodAt_L H D.C K chal D.ds 0 rts.2 _ hF hR
  rw [hext] at hb
  have Y := checks_yes g _ _ (wqXK D dec K chal).sh embS rts isRead π.opens
    (wqXK D dec K chal).ext embE cms isReadE _ G (fun p op _ ho => extE_yes N hSto e4 p op ho) a b
    ha hb
  exact ⟨Y.1, by rw [← runChecks_detF]; exact Y.1, Y.2⟩

/-- What `Walks` is for, at K + 1 blocks. -/
theorem walks_runK {g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (K + 1) L)}
    {embS : (p : OPos (_root_.Run.Twin.up (SOf D.C D.ds))) →
      OSym (_root_.Run.Twin.up (SOf D.C D.ds)) p → Body L}
    {embE : SgX → Body L} {cms : List (Dig 256)} {o : _root_.Fmt.ChainOut}
    (W : Walks D g embS embE cms o) {π : OneProtocolProof 256 (PSXE D dec).up}
    (hπ : assembleS D dec o = some π) (isRead : OPos (_root_.Run.Twin.up (SOf D.C D.ds)) → Bool)
    (isReadE : Fin (2 ^ D.a) ⊕ Fin (2 ^ D.a) → Bool) (a b : List (Check 256 L))
    (ha : checksB (_root_.Run.Twin.up (SOf D.C D.ds)) (_root_.Run.Twin.allLo (SOf D.C D.ds))
      (wqXK D dec K chal).sh embS ((none, some []), PQ.rtSL D.C D.ds o.rounds.toList) isRead
      π.opens = some a)
    (hb : TypedOracleCompiler.Compile.Batch.checksExt (wqXK D dec K chal).ext embE cms isReadE π.ext
      (wqXK D dec K chal).ext.all = some b) :
    (runChecks (K := K + 1) (a ++ b)).det g = true ∧ (a ++ b).all (runCheckF g) = true ∧
      (a ++ b).all (fun c => c.wellFormed) = true := by
  obtain ⟨vert, e1, Fm, Rt, N, hemb, hF, hO, hS, hR⟩ := W
  exact assembleS_walksK D dec K chal N hπ embS hemb hF hO hS
    ((none, some []), PQ.rtSL D.C D.ds o.rounds.toList) hR isRead isReadE a b ha hb

end OnBytes.K.Arm
